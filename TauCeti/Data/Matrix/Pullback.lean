/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Matrices over a fibre product of rings

For ring homomorphisms `f : R →+* T` and `g : S →+* T`, Mathlib's `RingHom.pullback f g` is the
fibre product `R ×_T S`, the subring of pairs `(r, s)` of `R × S` with `f r = g s`. A square
matrix over `R ×_T S` is the same as a pair of square matrices `(M₁, M₂)` over `R` and `S` whose
images over `T` agree. This file makes that identification a ring isomorphism

```text
Mₙ(R ×_T S) ≃+* Mₙ(R) ×_{Mₙ(T)} Mₙ(S),   M ↦ (p₁(M), p₂(M)),
```

where `p₁` and `p₂` are the two projections applied entrywise, and the fibre product on the right
is again `RingHom.pullback`, now of the entrywise homomorphisms `f.mapMatrix` and `g.mapMatrix`.
No surjectivity of `f` or `g` is needed.

The identification is the matrix compatibility of a Milnor square: it lets a pair of matrices
over the two corners of the square, which agree over the common quotient, be glued into a matrix
over the fibre product.

## Main definitions

* `RingHom.pullbackMatrixEquiv f g`: the ring isomorphism
  `Matrix n n (f.pullback g) ≃+* f.mapMatrix.pullback g.mapMatrix`.

## Main results

* `RingHom.coe_pullbackMatrixEquiv_apply`: the isomorphism sends `M` to the pair of its two
  entrywise projections.
* `RingHom.pullbackMatrixEquiv_symm_apply_apply`: the entries of the inverse image of a pair of
  matrices are the pairs of their entries.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §2.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, §2.6.
-/

public section

namespace RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T] (f : R →+* T) (g : S →+* T)
  {n : Type*} [Fintype n] [DecidableEq n]

/-- Square matrices over the fibre product `R ×_T S` are the fibre product of the matrix rings
`Mₙ(R)` and `Mₙ(S)` over `Mₙ(T)`: a matrix `M` corresponds to the pair of its entrywise
projections to `R` and to `S`, and a pair of matrices whose images over `T` agree glues
entrywise. -/
def pullbackMatrixEquiv :
    Matrix n n (f.pullback g) ≃+* (f.mapMatrix (m := n)).pullback (g.mapMatrix (m := n)) where
  toFun M := ⟨((f.pullbackFst g).mapMatrix M, (f.pullbackSnd g).mapMatrix M), by
    ext i j
    exact (M i j).property⟩
  invFun X := Matrix.of fun i j ↦
    ⟨((X : Matrix n n R × Matrix n n S).1 i j, (X : Matrix n n R × Matrix n n S).2 i j),
      congrFun (congrFun X.property i) j⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' M N := Subtype.ext (Prod.ext (map_mul _ M N) (map_mul _ M N))
  map_add' M N := Subtype.ext (Prod.ext (map_add _ M N) (map_add _ M N))

/-- The isomorphism `pullbackMatrixEquiv` sends a matrix over `R ×_T S` to the pair of its
entrywise projections to `R` and to `S`. -/
@[simp]
theorem coe_pullbackMatrixEquiv_apply (M : Matrix n n (f.pullback g)) :
    (pullbackMatrixEquiv f g M : Matrix n n R × Matrix n n S) =
      ((f.pullbackFst g).mapMatrix M, (f.pullbackSnd g).mapMatrix M) :=
  (rfl)

/-- The entries of the matrix over `R ×_T S` glued from a pair of matrices are the pairs of their
entries. -/
@[simp]
theorem pullbackMatrixEquiv_symm_apply_apply
    (X : (f.mapMatrix (m := n)).pullback (g.mapMatrix (m := n))) (i j : n) :
    ((pullbackMatrixEquiv f g).symm X i j : R × S) =
      ((X : Matrix n n R × Matrix n n S).1 i j, (X : Matrix n n R × Matrix n n S).2 i j) :=
  (rfl)

end RingHom
