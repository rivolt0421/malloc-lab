/*
 * mm-explicit.c - explicit free-list, w/ address order, immediate boundary-tag coalescing.
 * 
 * 경계 태그 연결(boundary-tag coalescing)을 사용하는 명시적 가용 리스트 (explicit free-list)에 기초한 할당기.
 * 모든 블록은 header와 footer을 가지며, 가용 블록은 추가로 prev free block pointer와 next free block pointer를 가진다.
 * 더블워드 정렬 기준이다. 블록의 최소 크기(바이트) 는 16 bytes 이다.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "JUNGLE_W06_TEAM_7",
    /* First member's full name */
    "LEE_KANG_WOOK",
    /* First member's email address */
    "dlrkddnr0421@daum.net",
    /* Second member’s full name (leave blank if none) */
    "",
    /* Second member’s email address (leave blank if none) */
    ""
};

/* Basic constants and macros*/

#define WSIZE       4       /* Word and header/footer size (bytes) */  
#define DSIZE       8       /* Double word size (bytes) */
#define MINBLKSIZE  16      /* minimum block size with header and footer */  
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amout (bytes) */
#define ALIGNMENT   8       /* single word (4) or double word (8) alignment */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*((unsigned int *)(p)))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p. (p would be an address of header or footer of block)*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define UINT_CAST(p) ((size_t)p)

/* bp(block pointer) : payload의 시작 주소를 가리키는 포인터이다. 헤더를 가리키지 않는다. */
/* Given block ptr bp(), compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given free block ptr bp, compute address of previous and next free blocks */
#define NEXT_FREE(bp)   ((void *)((char *)bp))                
#define PREV_FREE(bp)   ((void *)((char *)bp + WSIZE))
// bp로부터 4바이트는 next free block의 주소값을 담고있다.
// *(short **)bp
// short라는 자료형에 대한 포인터이므로, bp주소에서 부터 short 자료형의 크기 2바이트를 읽는다.
// *(void **)bp
// 포인터(void*)라는 자료형에 대한 포인터(void**)이므로, bp주소에서 부터 포인터 자료형의 크기 4바이트(32bit mode)를 읽는다.
// *(void **)(bp + WSIZE))
// 포인터(void*)라는 자료형에 대한 포인터(void**)이므로, bp주소에서 부터 포인터 자료형의 크기 4바이트(32bit mode)를 읽는다.

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)       // 7을 더해주고 하위 3개의 비트는 0으로 바꿔줌.
                                                            // 그러면 나보다 높으면서 가장 가까운 8의 배수가 될 수 있다.

/* heap checker */
#ifdef DEBUG
# define CHECKHEAP() printf("\n%s : %d\n", __func__,__LINE__); mm_checkheap(__LINE__);
#endif

/* private variables */
static char *heap_listp;
static void *root;

/* private function declarations */
int mm_init(void);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void update_pointer(void *bp, void *prev, void *next);
static void *insert_free(void *bp);
static void mm_checkheap(int lineno);

/* 
 * mm_init - Initializes the heap like that shown below.
 -------------------------------------------------------------------------------------------------------------
 * <initialized heap image>
 * @                          @                           @  - double word alignment
 *  _____________ ____________ _____________ _____________
 * |   PROLOGUE  |  PROLOGUE  |   PROLOGUE  |             |
 * |     next    |    prev    |    footer   |   EPILOGUE  |
 * |-------------|------------|-------------|-------------|
 * |      0      |      0     |    4 / 1    |    0 / 1    |
 * |-------------|------------|-------------|-------------|
 *                                          ^
 *                                      heap_listp
 -------------------------------------------------------------------------------------------------------------
 * <generalized heap image>
 * @                          @                           @                           @                           @  - double word alignment
 *  _____________ ____________ _____________                                                         _____________ 
 * |   PROLOGUE  |  PROLOGUE  |   PROLOGUE  |                                                       |             |
 * |     next    |    prev    |    footer   |                                                       |   EPILOGUE  |
 * |-------------|------------|-------------|-------------|-------------|-------------|-------------|-------------|
 * |      0      |      0     |    4 / 1    |    HEADER   |    PREV     |    NEXT     |    FOOTER   |    0 / 1    |
 * |-------------|------------|-------------|-------------|-------------|-------------|-------------|-------------|
 * ^                                        ^
 * root                                 heap_listp
 * 
 * 
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)     // 시스템에 요청한 heap공간 할당이 실패했을 때.
        return -1;
    PUT(heap_listp + 0*WSIZE, 0);                /* PROLOGUE next */
    PUT(heap_listp + 1*WSIZE, 0);                /* PROLOGUE prev */
    PUT(heap_listp + 2*WSIZE, PACK(4, 1));       /* PROLOGUE footer */
    PUT(heap_listp + 3*WSIZE, PACK(0, 1));       /* EPILOGUE */
    root = heap_listp;
    heap_listp += 3*WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)   // 필요한 워드의 개수를 인자로 넘긴다.
        return -1;

    return 0;
}

/*
 * extend_heap은
 * 1. 힙이 초기화 될 때, 또는
 * 2.mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때 호출된다.
 */
static void *extend_heap(size_t words) // size_t a.k.a. {long, unsigned int} (stddef.h)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;     // 요청 크기를 2워드의 배수로 다시 맞춘다.
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */     // 위에서 extend한 size가 encode 됨에 유의하자.
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));    /* New epilogue header */

    /* Coalesce if the previous block was free block */
    return coalesce(bp);
}

/* 
 * mm_malloc - size 바이트의 메모리를 할당하고, 해당 블록의 포인터(bp)를 반환.
 *           - 적절한 크기의 free 블록을 찾지 못한 경우, extend_heap 을 통해 힙을 확장 후 할당.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size for alignment */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* 불필요한 요청 무시 */
    if (size == 0) {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs (double word). */
    if (size <= MINBLKSIZE - DSIZE)     // 요청된 size가 minimum block size에서 header와 footer의 크기 뺀, 최소 payload크기보다도 작으면
        asize = MINBLKSIZE;             // 그냥 minimum block을 할당해주면 됨.
    else
        asize = ALIGN(size) + DSIZE;    // size는 사용자가 요구한 공간. 거기에 헤더와 푸터의 8바이트를 더해줘야 한다.

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);

        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    place(bp, asize);

    return bp;
}

/*
 * find_fit - find available free block for request.
*/
static void *find_fit(size_t asize)
{   
    // First-fit search
    for (void *bp = (void *)GET(NEXT_FREE(root)); bp != NULL; bp = (void *)GET(NEXT_FREE(bp))) {
        if (GET_SIZE(HDRP(bp)) >= asize)
            return bp;
    }
    return NULL;
}

/*
 * update_pointer - update pointers of bp, prev, next
*/
static void update_pointer(void *bp, void *prev, void *next) {
    // 내 꺼
    PUT(PREV_FREE(bp), prev);
    PUT(NEXT_FREE(bp), next);
    // 남의 꺼  
    PUT(NEXT_FREE(prev), bp);
    if (next)
        PUT(PREV_FREE(next), bp);
}

/*
 * place - place allocated block and divide if possible.
 */
static void place(void *bp, size_t asize)
{
    size_t original_size = GET_SIZE(HDRP(bp));  // 원래 블록의 사이즈
    size_t diff = original_size - asize;
    
    if (diff >= MINBLKSIZE) {   // 원래 블록의 사이즈와 할당하려는 블록 사이즈의 차이가 블록의 최소크기 보다 커야 분할할 수 있다.

        // 할당 처리
        PUT(HDRP(bp) , PACK(asize, 1));             // header (asize / 1)
        PUT(FTRP(bp) , PACK(asize, 1));             // footer (asize / 1)
        void * leftover_bp = NEXT_BLKP(bp);
        
        // 남은 부분 가용 처리
        PUT(HDRP(leftover_bp), PACK(diff, 0));      // header (diff / 1)
        PUT(FTRP(leftover_bp), PACK(diff, 0));      // footer (diff / 1)

        /* 포인터 조정 */
        update_pointer(leftover_bp, (void *)GET(PREV_FREE(bp)), (void *)GET(NEXT_FREE(bp)));
    }
    else {  // 분할 못하는 경우.

        // 원래 블록을 전부 할당 처리.
        PUT(FTRP(bp), PACK(original_size, 1));
        PUT(HDRP(bp), PACK(original_size, 1));

        /* 포인터 조정 */
        // 남의 꺼만 하면 됨. 어떠한 포인터도 날 가리키지 않게되면 나는 리스트에서 삭제된 것임.
        PUT(NEXT_FREE(GET(PREV_FREE(bp))), GET(NEXT_FREE(bp)));
        if (GET(NEXT_FREE(bp)))
            PUT(PREV_FREE(GET(NEXT_FREE(bp))), GET(PREV_FREE(bp)));
    }
}

/*
 * mm_free - 일단 현재 블록을 free해주고, coalese 를 통해 경우에 따라 인접한 블록들을 연결을 해준다.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));       // size 그대로인 free 블록으로 지정.
    PUT(FTRP(bp), PACK(size, 0));       // size 그대로인 free 블록으로 지정.
    coalesce(bp);


}

/*
 * insert_free - free된 블럭을 리스트 안에 삽입해야할 때 사용한다.
*/
static void *insert_free(void *bp) {
    void * prev_free = root;
    void * next_free = (void *)GET(NEXT_FREE(root));
    while (next_free != NULL) {
        if (bp < next_free)  // 찾았다!
            break;
        prev_free = next_free;
        next_free = (void *)GET(NEXT_FREE(next_free));
    }
    update_pointer(bp, (void *)prev_free, (void *)next_free);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(bp - DSIZE);              // 앞 블록의 할당 여부  // prologue에는 header가 없어서 이런 방식으로 계산.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));     // 뒤 블록의 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                       // 현재 블록의 사이즈

    /* case 1 : 앞, 뒤 블록 모두 allocated 인 경우. */
    if (prev_alloc && next_alloc) {
        insert_free(bp);
    }
    /* case 3 : 앞 블록만 free 인 경우. */
    else if (next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // prev free block은 이미 free list에 있던 블록이기 때문에,
        // update_pointer 불필요.
    }
    /* case 2 : 뒤 블록만 free 인 경우. */
    else if (prev_alloc) {
        void * next_bp = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(next_bp));
        PUT(HDRP(bp), PACK(size, 0));           // 현재 블록의 크기와 뒤 블록의 크기가 합쳐진 size가 현재 블록의 header에 인코딩됨.
        PUT(FTRP(bp), PACK(size, 0));           // 위 라인 덕분에 FTRP(bp) 는 다음 블록의 footer를 가리키게 된다.

        update_pointer(bp, (void *)GET(PREV_FREE(next_bp)), (void *)GET(NEXT_FREE(next_bp)));
    }

    /* case 4 : 앞, 뒤 블록 모두 free 인 경우. */
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        void *nnext_bp = NEXT_BLKP(bp); 
        bp = PREV_BLKP(bp);

        update_pointer(bp, (void *)GET(PREV_FREE(bp)), (void *)GET(NEXT_FREE(nnext_bp)));
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);       // size : 사용자 요청 크기
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);

    mm_free(oldptr);
    return newptr;

    // size_t block_size = GET_SIZE(HDRP(bp));
    // // 1. 재요청된 size가 원래 payload size보다 작거나 같을 때.
    // if (size <= (block_size - DSIZE)) {
    //     size_t al_blk_size;
    //     if (size <= MINBLKSIZE - DSIZE)
    //         { al_blk_size = MINBLKSIZE; }
    //     else
    //         { al_blk_size = ALIGN(size) + DSIZE; }

    //     // 1-1. 원래 블록이 분할 가능할 때.
    //     if (block_size - al_blk_size >= MINBLKSIZE) {
    //         // 할당 처리
    //         PUT(HDRP(bp) , PACK(al_blk_size, 1));             // header (al_blk_size / 1)
    //         PUT(FTRP(bp) , PACK(al_blk_size, 1));             // footer (al_blk_size / 1)
            
    //         // 남은 부분 가용 처리
    //         void * leftover_bp = NEXT_BLKP(bp);
    //         PUT(HDRP(leftover_bp), PACK(block_size - al_blk_size, 0));     // header (diff / 1)
    //         PUT(FTRP(leftover_bp), PACK(block_size - al_blk_size, 0));     // footer (diff / 1)
            
    //         coalesce(leftover_bp);
    //     }
    //     // 1-2. 원래 블록이 분할 불가능할 때.
    //     // -> 아무 것도 할 수 있는게 없다. 그냥 그대로 돌려주면 됨.
    // }
    // // 2. 재요청된 size가 원래 size보다 클 때.
    // else {
    //     void *new_bp = mm_malloc(size);
    //     memcpy(new_bp, bp, block_size);
    //     mm_free(bp);
    //     bp = new_bp;
    // }
    
    // return bp;
}

/*
 * mm_checkheap - check heap invariants for this implementation.
 *
 * #ifdef DEBUG
 *   CHECKHEAP();
 * #endif
*/
void mm_checkheap(int lineno)
{
    char *heap_lo = mem_heap_lo();                      // pointing first word of the heap
    char *heap_hi = heap_lo + (mem_heapsize()-WSIZE);   // pointing last word of the heap
    char *bp;

    /* heap level check*/
    //assert(GET(heap_lo) == 0);                          // check PROLOGUE next
    //assert(GET(heap_lo + 1*WSIZE) == 0);                // check PROLOGUE prev
    assert(GET(heap_lo + 2*WSIZE) == PACK(WSIZE,1));    // check PROLOGUE footer
    assert(GET(heap_hi) == PACK(0,1));                  // check epilogue block

    /* block level */
    for(bp = heap_listp ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp)) {
        assert(GET(HDRP(bp)) == GET(FTRP(bp)));     // check header and footer match
        assert(!(UINT_CAST(bp) & 0x7));             // check if payload area aligned
        assert(GET_ALLOC(HDRP(bp)) | GET_ALLOC(HDRP(NEXT_BLKP(bp))));   // check contiguous free blocks
        assert(heap_lo < HDRP(bp) && FTRP(bp) < heap_hi);               // check heap bound

        // check all free blocks are in the free list
        if (!GET_ALLOC(HDRP(bp))) {
            void *next_free;
            for (next_free = (void *)GET(NEXT_FREE(root)); next_free != NULL; next_free = (void *)GET(NEXT_FREE(next_free))) {
                if (next_free == bp)
                    break;
            }
            assert(next_free);
        }
    }
    // detect cycle
    char * hare; char *tortoise;
    hare = tortoise = root;
    printf("hare : %16p, tortoise: %16p\n", hare, tortoise);
    while(1) {
        if (!hare || !GET(NEXT_FREE(hare)))
            break;
        hare = (void *)GET(NEXT_FREE(GET(NEXT_FREE(hare))));
        tortoise = (void *)GET(NEXT_FREE(tortoise));
        printf("hare : %16p, tortoise: %16p\n", hare, tortoise);
        assert(hare != tortoise);
    }
    /* list level check */
    printf("<<free block list>>\n");
    void * free = root;
    void * next_free = (void *)GET(NEXT_FREE(root));
    while (next_free != NULL) {
        printf("free : %p, next free : %p\n", free, next_free);
        assert(!GET_ALLOC(HDRP(next_free)));
        assert(free < next_free);

        free = next_free;
        next_free = (void *)GET(NEXT_FREE(next_free));
    }
}