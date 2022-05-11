// implicit 방법

/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
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
    "week6-02",
    /* First member's full name */
    "ktkdgh",
    /* First member's email address */
    "ktkdgh@skku.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define WSIZE     4         // 워드, 헤더, 푸터 4byte 크기로
#define DSIZE     8         // 더블 워드, 8byte 크기로
#define CHUNKSIZE (1 << 12) // heap을 늘릴 때 얼만큼 늘릴거냐? 4kb 분량

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // x > y가 참이면 x, 거짓이면 y

#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값 리턴

#define GET(p)      (*(unsigned int *)(p))         // 인자 p가 참조하는 워드를 읽어서 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 인자 p가 가리키는 워드에 val을 저장한다.

#define GET_SIZE(p)  (GET(p) & ~0x7)  // 주소 p에 있는 헤더 또는 풋터의 size를 리턴
#define GET_ALLOC(p) (GET(p) & 0x1)   // 주소 p에 있는 헤더 또는 풋터의 할당 비트를 리턴

#define HDRP(bp) ((char *)(bp) - WSIZE)                      // bp(현재 블록의 포인터)가 주어지면, 현재 블록의 header 위치 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp(현재 블록의 포인터)가 주어지면, 현재 블록의 footer 위치 반환
 
#define NEXT_BLKP(bp) (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))) // 다음 블록 bp 위치 반환(bp + 현재 블록의 크기)
#define PREV_BLKP(bp) (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))) // 이전 블록 bp 위치 반환(bp - 이전 블록의 크기)

static void *extend_heap(size_t words);     // 새 가용 블록으로 힙 확장
static void *coalesce(void *bp);            // 인접 가용 블록들과 통합
static void *find_fit(size_t asize);        // 가용 리스트를 처음부터 검색해서 크기가 맞는 첫 번째 가용 블록을 선택
static void place(void *bp, size_t asize);  // 가용 공간과 할당할 사이즈가 들어갈 수 있는 공간에 header와 footer에 
                                            // 정보를 넣어주고 공간 할당을 하고 남은 부분이 있으면
                                            // (넣어줄 가용 블록 크기 - 할당할 크기) 만큼을 가용공간으로 만듬 
static void *heap_listp; // find_fit에서 사용하기 위한 정적 전역 변수

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    /* 최소 16바이트(header, footer, payload)을 할당해야되는데 
       전체로 봤을 때 16바이트를 할당할 수 없으면 return -1 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) { 
        return -1;
    }
    
    PUT(heap_listp, 0); // 블록 생성시 넣는 padding을 1워드 크기만큼 생성, heap_listp 위치는 맨 처음
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  // prologue block header 생성 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  // prologue block footer 생성
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));      // epilogue block header 생성
    heap_listp += (2*WSIZE); // heap_listp 포인터를 prologue header와 footer 사이에 위치 시킨다.
    
    // CHUNKSIZE: (1<<12) = 4096, 빈 힙을 CHUNKSIZE 바이트의 사용 가능한 블록으로 확장
    // 공간이 없다면 return -1;
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}
/*
    extend_heap이 사용되는 경우 2가지
        1. 힙이 초기화될 때,
        2. mm_malloc이 적당한 fit을 찾지 못했을 때
*/
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // 64bit 운영체제는 주소 단위를 8바이트로 읽기 때문에 최소 8바이트가 필요 
    // 짝수 * 4는 무조건 8의 배수이기 때문에 홀수일 때 짝수로 만들어서 *4를 함 
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // size 크기 만큼 heap을 확장 시킨다. 확장할 공간이 없다면 return NULL
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));          // free block header 생성, regular block의 첫번째 부분
    PUT(FTRP(bp), PACK(size, 0));          // free block footer 생성, regular block의 마지막 부분
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // free block footer 뒤에 epilogue 위치 설정

    // 새 가용 블록으로 힙을 확장하고 이전 블록이 가용블록이면 합침 
    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 푸터의 할당여부를 체크
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더의 할당여부를 체크
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 헤더의 사이즈 확인

    /* case 1 : 이전, 다음 블록 모두 할당되어있다면 */
    if (prev_alloc && next_alloc) {  
        return bp;
    /* case 2 : 이전 블록은 할당되어있고, 다음 블록은 가용상태라면 */    
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록 사이즈에 다음 블록 사이즈를 더해준다.
        PUT(HDRP(bp), PACK(size, 0));          // 현재 블록 header에 size를 넣고 가용상태로 변경
        PUT(FTRP(bp), PACK(size, 0));          // 다음 블록 footer에 size를 넣고 가용상태로 변경
    /* case 3 : 이전 블록은 가용상태이고, 다음 블록이 할당상태라면 */
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 현재 블록 사이즈에 이전 블록 사이즈를 더해준다.
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 footer에 size를 넣고 가용상태로 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 header에 size를 넣고 가용상태로 변경
        bp = PREV_BLKP(bp);                      // bp를 이전 블록 payload 시작 위치로 변경
    /* case 4 : 이전, 다음 블록 모두 가용 상태라면 */
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  // size에 이전, 다음 블록의 사이즈를 더해준다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                                // 이전 블록 header에 size를 넣고 가용상태로 변경
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                                // 다음 블록 footer에 size를 넣고 가용상태로 변경
        bp = PREV_BLKP(bp);                                                     // bp를 이전 블록 payload 시작 위치로 변경
    }
    return bp; // bp 반환
}

/*
 * mm_free - 공간 할당 해제.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));  // free 시킬 블록의 사이즈를 size에 담아준다.
    // header와 footer를 가용상태로 변경
    PUT(HDRP(bp), PACK(size, 0));      
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);  // 이전, 다음 블록을 체크해 공간을 합쳐준다.
}

static void *find_fit(size_t asize) {
    /* First-fit search */
    void *bp;

    // GET_SIZE(HDRP(bp)) > 0 : 블록의 크기가 0 보다 작을 때, 즉 apilogue를 만날 때까지 반복
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        // 현재 블록이 가용 상태이고, 할당하고 싶은 사이즈(asize)가 현재 블록보다 작을때 bp 반환
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    // for문이 종료됬다면, 알맞는 크기가 없으니 NULL 반환
    return NULL;
}

/*
* place - 할당할 크기를 담을 수 있는 블록을 분할 해줌
*         할당할 크기를 담을 수 있는 블록 - 할당할 블록이 16바이트보다 크면
*         나중에 16바이트 크기만큼 할당하고 싶을 때 사용할 수 있기 때문에
*         분할 해서 뒤에 공간은 가용 공간으로 만들어줌
*         내부 단편화를 줄여줌       
*/
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));       // 현재 블록의 사이즈

    if ((csize - asize) >= (2*DSIZE)) {      // 분할 후에 이 블록의 나머지가 최소 블록 크기(16 bytes)와 같거나 크다면
        PUT(HDRP(bp), PACK(asize, 1));       // header 위치에 asize 만큼 넣고 할당 상태로 변경
        PUT(FTRP(bp), PACK(asize, 1));       // footer 위치에 asize 만큼 넣고 할당 상태로 변경
        bp = NEXT_BLKP(bp);                  // bp 위치를 다음 블록 위치로 갱신
        // asize 할당 후 남은 공간 분할 후 가용 상태로 변경
        PUT(HDRP(bp), PACK(csize-asize, 0)); 
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else {
        // 아니라면, 그냥 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;       // 블록 사이즈 조정
    size_t extendsize;  // heap에 맞는 fit이 없다면 확장하기 위한 사이즈
    char *bp;

    /* Ignore spurious requests */
    if (size == 0) {
        return NULL;
    }

    /* 할당할 크기가 8바이트보다 작으면 asize에 16바이트를 담음 
       할당할 크기가 8바이트보다 크면 8의 배수로 맞춰줘야되기 때문에
       (header/footer의 크기 8바이트 + 7바이트 + 할당할 크기) / 8을 하면 
       나머지는 버려지고 몫만 남는데 그 몫 * 8을 하면 할당할 크기를 담을 수 있는
       최소한의 크기의 8의 배수를 구할 수 있음 */
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    // find_fit으로 asize의 크기를 넣을 수 있는 공간이 있다면
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize); 
        return bp;  // place를 마친 블록의 위치를 리턴
    }

    // find_fit에 넣을 수 있는 공간이 없다면, 새 가용블록으로 힙을 확장.
    extendsize = MAX(asize, CHUNKSIZE);
    // 확장할 공간이 더 남아있지 않다면 NULL 반환
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    // 확장이 됬다면, asize 만큼 공간을 할당하고 잘라준다.
    place(bp, asize);
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL) {
      return NULL;
    }

    copySize = GET_SIZE(HDRP(oldptr));  // 현재 크기를 copysize에 담는다.
    // size가 copySize보다 작다면, copySize의 값을 size의 값으로 바꾼다.
    if (size < copySize) {
      copySize = size;
    }
    
    // newptr : 복사받을 메모리를 가리키는 포인터, oldptr : 복사할 메모리를 가리키는 포인터, copySize : 크기
    memcpy(newptr, oldptr, copySize); 
    mm_free(oldptr); // 기존의 메모리 free
    return newptr;
}