#include "kernel/types.h"  // Include kernel-specific type definitions
#include "kernel/stat.h"   // Include kernel-specific status definitions
#include "user/user.h"     // Include user-specific definitions
#include "kernel/param.h"  // Include kernel-specific parameters

// Memory allocator by Kernighan and Ritchie,
// The C programming Language, 2nd ed. Section 8.7.

typedef long Align;  // Ensure alignment of memory blocks

// Define a union for the memory header
union header {
  struct {
    union header *ptr;  // Pointer to the next block in the free list
    uint size;          // Size of the block
  } s;
  Align x;  // Alignment
};

typedef union header Header;  // Define Header as a type alias for the union

static Header base;        // Base block for the free list
static Header *freep;      // Pointer to the current free block

// Free the allocated memory block
void free(void *ap)
{
  Header *bp, *p;

  bp = (Header*)ap - 1;  // Convert the pointer to a Header pointer and adjust to the header
  for(p = freep; !(bp > p && bp < p->s.ptr); p = p->s.ptr)  // Traverse the free list to find the correct position
    if(p >= p->s.ptr && (bp > p || bp < p->s.ptr))  // Check for wrap-around at the end of the list
      break;
  if(bp + bp->s.size == p->s.ptr){  // Coalesce with the next block if adjacent
    bp->s.size += p->s.ptr->s.size;
    bp->s.ptr = p->s.ptr->s.ptr;
  } else
    bp->s.ptr = p->s.ptr;
  if(p + p->s.size == bp){  // Coalesce with the previous block if adjacent
    p->s.size += bp->s.size;
    p->s.ptr = bp->s.ptr;
  } else
    p->s.ptr = bp;
  freep = p;  // Update the free list pointer
}

// Request more memory from the system
static Header* morecore(uint nu)
{
  char *p;
  Header *hp;

  if(nu < 4096)  // Ensure a minimum allocation size
    nu = 4096;
  p = sbrk(nu * sizeof(Header));  // Request memory from the system
  if(p == (char*)-1)  // Check for allocation failure
    return 0;
  hp = (Header*)p;  // Convert the allocated memory to a Header pointer
  hp->s.size = nu;  // Set the size of the new block
  free((void*)(hp + 1));  // Free the new block to add it to the free list
  return freep;  // Return the updated free list pointer
}

// Allocate memory
void*
malloc(uint nbytes)
{
  Header *p, *prevp;
  uint nunits;

  nunits = (nbytes + sizeof(Header) - 1)/sizeof(Header) + 1;  // Calculate the number of units needed
  if((prevp = freep) == 0){  // Initialize the free list if it is empty
    base.s.ptr = freep = prevp = &base;
    base.s.size = 0;
  }
  for(p = prevp->s.ptr; ; prevp = p, p = p->s.ptr){  // Traverse the free list to find a suitable block
    if(p->s.size >= nunits){  // Check if the current block is large enough
      if(p->s.size == nunits)  // If the block is exactly the right size
        prevp->s.ptr = p->s.ptr;
      else {  // If the block is larger, split it
        p->s.size -= nunits;
        p += p->s.size;
        p->s.size = nunits;
      }
      freep = prevp;  // Update the free list pointer
      return (void*)(p + 1);  // Return a pointer to the allocated memory
    }
    if(p == freep)  // If the end of the free list is reached
      if((p = morecore(nunits)) == 0)  // Request more memory
        return 0;  // Return NULL if allocation fails
  }
}