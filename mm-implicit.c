/*
 * mm-implicit.c - implicit free-list, immediate boundary-tag coalescing.
 * 
 * 경계 태그 연결(boundary-tag coalescing)을 사용하는 묵시적 가용 리스트 (implicit free-list)에 기초한 할당기.
 * 각 블록은 헤더(header)와 푸터(footer)를 가지며, 더블워드 정렬 기준이다.
 * 블록의 최소 크기(바이트) 는 16 bytes 이다.
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
    "Team_7",
    /* First member's full name */
    "LEE_KANG_WOOK",
    /* First member's email address */
    "dlrkddnr0421@daum.net"
};

/* Basic constants and macros*/

#define WSIZE       4       /* Word and header/footer size (bytes) */  
#define DSIZE       8       /* Double word size (bytes) */  
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

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)       // 7을 더해주고 하위 3개의 비트는 0으로 바꿔줌.
                                                            // 그러면 나보다 높으면서 가장 가까운 8의 배수가 될 수 있다.
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* heap checker */
#ifdef DEBUG
# define CHECKHEAP() printf("%s : %d\n", __func__,__LINE__); mm_checkheap(__LINE__);
#endif

/* private variables */
static char *heap_listp;

/* private function declarations */
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);

/*
 * mm_checkheap - check heap invariants for this implementation.
*/
void mm_checkheap(int lineno)
{
    char *heap_lo = mem_heap_lo();                      // pointing first word of the heap
    char *heap_hi = heap_lo + (mem_heapsize()-WSIZE);   // pointing last word of the heap
    char *bp;

    /* heap level check*/
    assert(GET(heap_lo) == 0);                          // check unused block
    assert(GET(heap_lo + 1*WSIZE) == PACK(DSIZE,1));    // check prologue block
    assert(GET(heap_lo + 2*WSIZE) == PACK(DSIZE,1));
    assert(GET(heap_hi) == PACK(0,1));                  // check epilogue block

    /* block level, list level check */
    for(bp = heap_listp ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp)) {
        // block level
        char * ftr = FTRP(bp);
        assert(GET(HDRP(bp)) == GET(FTRP(bp)));     // check header and footer match
        assert(!(UINT_CAST(bp) & 0x7));             // check if payload area aligned

        // list level
        assert(GET_ALLOC(HDRP(bp)) | GET_ALLOC(HDRP(NEXT_BLKP(bp))));   // check contiguous free blocks
                                                                        // alloc 여부가 (1,0), (0,1), (1,1) 이면 연속된 free블록이 없는 것이지만,
                                                                        // (0,0) 이면 연속된 free블록이 존재한다는 뜻.
    }
}

/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)     // 시스템에 요청한 heap공간 할당이 실패했을 때.
        return -1;
    PUT(heap_listp, 0);                                 /* Alignment padding*/
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));        /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));        /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));            /* Epilogue header */
    heap_listp += (2*WSIZE);
    /*                   unused   pro.hdr.   pro.ftr.   epl.hdr.
     * start of heap : | unused |    8/1   |    8/1   |   0/1   |
     *                                     |
     *                                 heap_listp           
     */
        #ifdef DEBUG
        CHECKHEAP(); 
        #endif
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)   // 필요한 워드의 개수를 인자로 넘긴다.
        return -1;

        #ifdef DEBUG
        CHECKHEAP();
        #endif

    return 0;
}

/*
 * extend_heap은 1. 힙이 초기화 될 때, 2.mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때 호출된다.
 */
static void *extend_heap(size_t words) // size_t a.k.a. {long, unsigned int} (stddef.h)
{
    char * origin = heap_listp - 8;
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;     // 요청 크기를 2워드의 배수로 다시 맞춘다.
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    size_t *hdr = HDRP(bp);
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */     // 위에서 extend한 size가 encode 됨에 유의하자.
    size_t *ftr = FTRP(bp);
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
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = ALIGN(size) + DSIZE;    // size는 사용자가 요구한 공간. 거기에 헤더와 푸터의 8바이트를 더해줘야 한다.

    // if (size <= DSIZE)
    //     asize = 2*DSIZE;
    // else
    //     asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);

        #ifdef DEBUG
        CHECKHEAP();
        #endif

        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

        #ifdef DEBUG
        CHECKHEAP();
        #endif

    place(bp, asize);

        #ifdef DEBUG
        CHECKHEAP();
        #endif
        
    return bp;
}

/*
 * find_fit - find available free block for request.
*/
static void *find_fit(size_t asize)
{   // First-fit search
    char *bp = heap_listp;
    while (GET_SIZE(HDRP(bp = NEXT_BLKP(bp)))) { // 다음 블록이 epilogue 블록이 아니라면,
        // 블록이 free이고, size가 asize보다 크다면 할당 가능하다.
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize))
            return bp;
    }
    return NULL;
}

/*
 * place - place allocated block and divide if possible.
*/
static void place(void *bp, size_t asize)
{
    size_t total = mem_heapsize();
    size_t original_size = GET_SIZE(HDRP(bp));  // 원래 블록의 사이즈
    size_t diff = original_size - asize;
    
    if (diff >= DSIZE*2) {   // 원래 블록의 사이즈와 할당하려는 블록 사이즈의 차이가 블록의 최소크기 보다 커야 분할할 수 있다.
        size_t *hdrp = HDRP(bp); size_t *ftrp = FTRP(bp);
        PUT(HDRP(bp) , PACK(asize, 1));              // asize 만큼 할당.
        ftrp = FTRP(bp);
        PUT(FTRP(bp) , PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        hdrp = HDRP(bp);
        PUT(HDRP(bp), PACK(diff, 0));     // 할당 후 남은 부분 diff 크기를 가진 free 블록으로 지정
        ftrp = FTRP(bp);
        PUT(FTRP(bp), PACK(diff, 0));     
    }
    else {  // 분할 못하는 경우.
        PUT(FTRP(bp), PACK(original_size, 1));
        PUT(HDRP(bp), PACK(original_size, 1));           // 원래 블록을 전부 allocate 한다.
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
        #ifdef DEBUG
        CHECKHEAP();
        #endif
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));     // 앞 블록의 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));     // 뒤 블록의 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                       // 현재 블록의 사이즈

    /* case 1 : 앞, 뒤 블록 모두 allocated 인 경우. */
    if (prev_alloc && next_alloc) {
        return bp;
    }
    /* case 2 : 뒤 블록만 free 인 경우. */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));           // 현재 블록의 크기와 뒤 블록의 크기가 합쳐진 size가 현재 블록의 header에 인코딩됨.
        PUT(FTRP(bp), PACK(size, 0));           // 위 라인 덕분에 FTRP(bp) 는 다음 블록의 footer를 가리키게 된다.
    }
    /* case 3 : 앞 블록만 free 인 경우. */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* case 4 : 앞, 뒤 블록 모두 free 인 경우. */
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - WSIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}