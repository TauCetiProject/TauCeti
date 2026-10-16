/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.BlockSucc
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.RepresentationTheory.ClassicalGroups.Orthogonal

/-!
# Branching of the orthogonal standard representation along the block inclusion

The orthogonal block inclusion `TauCeti.orthogonalBlockSucc : O(n, k) →* O(n + 1, k)` puts an
orthogonal matrix in the upper-left block and fixes the last basis vector, so restricting the
standard representation of `O(n + 1, k)` along it leaves the last coordinate alone.  This file
proves that, in the form

`Res (stdOrthogonalRep k (n + 1)) ≅ stdOrthogonalRep k n ⊕ 1`,

as `TauCeti.stdOrthogonalRepBlockSuccEquiv`, records that the splitting is **orthogonal** for the
invariant dot product (`TauCeti.dotProduct_eq_stdOrthogonalRepBlockSuccEquiv`), and derives the
character identity `TauCeti.char_stdOrthogonalRep_orthogonalBlockSucc`.

This is the branching problem `O(n + 1) ↓ O(n)` for the standard representation, the orthogonal
counterpart of `TauCeti.stdRepBlockSuccEquiv` in
`TauCeti/RepresentationTheory/ClassicalGroups/Branching/Basic.lean`.  The decomposition of the
other irreducible representations along this chain is type-specific — the orthogonal interlacing is
not the general linear one — and needs the orthogonal highest-weight classification, so it is not
proved here; what is proved here is the restriction formula
`TauCeti.stdOrthogonalRep_orthogonalBlockSucc_apply` that any such computation starts from, the one
splitting, and the compatibility
`TauCeti.orthogonalGroupToGL_orthogonalBlockSucc` of the two chains of groups, which says that the
orthogonal chain sits inside the general linear one.

The splitting is `LinearEquiv.piFinSnoc`, exactly as for the general linear group: a vector of
`Fin (n + 1) → k` is its first `n` coordinates together with its last, and that linear isomorphism
carries the restricted representation onto `Representation.prod`.  Because the dot product of two
vectors is the dot product of their initial segments plus the product of their last coordinates,
the same isomorphism identifies the invariant form with the orthogonal direct sum of the invariant
form of the smaller group and the square on the line, which is the sense in which the summand `1`
is the orthogonal complement of the smaller standard module.

## Main definitions

* `TauCeti.stdOrthogonalRepBlockSuccEquiv`: the branching isomorphism, an equivalence of
  representations of `Matrix.orthogonalGroup (Fin n) k`.

## Main results

* `TauCeti.orthogonalGroupToGL_orthogonalBlockSucc`: the orthogonal and the general linear block
  inclusions agree under the inclusion of the orthogonal group in the general linear group.
* `TauCeti.stdOrthogonalRep_orthogonalBlockSucc_apply`: the restricted standard action multiplies
  the first `n` coordinates and fixes the last.
* `TauCeti.dotProduct_eq_stdOrthogonalRepBlockSuccEquiv`: the branching splits the invariant dot
  product as an orthogonal direct sum.
* `TauCeti.stdOrthogonalRep_comp_orthogonalBlockSucc_injective`: the restriction is still faithful.
* `TauCeti.char_stdOrthogonalRep_orthogonalBlockSucc`: the character of the restriction is the
  character of the standard representation plus one.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

attribute [local instance] starRingOfComm

/-- **The two block inclusions agree**: extending an orthogonal matrix and then viewing it as an
invertible matrix is the same as viewing it as an invertible matrix and then extending it.  So the
chain `O(1, k) ⊂ O(2, k) ⊂ ⋯` sits inside the chain `GL 1 ⊂ GL 2 ⊂ ⋯`, and the restrictions along
the two chains are compatible. -/
@[simp]
theorem orthogonalGroupToGL_orthogonalBlockSucc (g : Matrix.orthogonalGroup (Fin n) k) :
    orthogonalGroupToGL k (n + 1) (orthogonalBlockSucc k n g) =
      glBlockSucc k n (orthogonalGroupToGL k n g) :=
  Units.ext <| by
    rw [orthogonalGroupToGL_coe, coe_glBlockSucc, coe_orthogonalBlockSucc,
      orthogonalGroupToGL_coe]

/-- **The standard orthogonal action, restricted along the block inclusion**: `g` multiplies the
first `n` coordinates and the last one is fixed. -/
theorem stdOrthogonalRep_orthogonalBlockSucc_apply (g : Matrix.orthogonalGroup (Fin n) k)
    (v : Fin (n + 1) → k) :
    stdOrthogonalRep k (n + 1) (orthogonalBlockSucc k n g) v =
      Fin.snoc ((g : Matrix (Fin n) (Fin n) k) *ᵥ Fin.init v) (v (Fin.last n)) := by
  rw [stdOrthogonalRep_apply_apply, coe_orthogonalBlockSucc, blockSucc_mulVec]

/-- **Branching of the standard representation of `O(n + 1, k)` to `O(n, k)`.**  The restriction
along the orthogonal block inclusion is the standard representation of the smaller orthogonal group
plus a trivial summand, carried by the splitting of a vector into its first `n` coordinates and its
last one. -/
noncomputable def stdOrthogonalRepBlockSuccEquiv :
    Representation.Equiv
      ((stdOrthogonalRep k (n + 1)).comp (orthogonalBlockSucc k n) :
        Representation k (Matrix.orthogonalGroup (Fin n) k) (Fin (n + 1) → k))
      ((stdOrthogonalRep k n).prod
        (Representation.trivial k (Matrix.orthogonalGroup (Fin n) k) k)) :=
  Representation.Equiv.mk (LinearEquiv.piFinSnoc k fun _ => k) fun g => LinearMap.ext fun v =>
    Prod.ext (by simp [blockSucc_mulVec]) (by simp [blockSucc_mulVec])

@[simp]
theorem stdOrthogonalRepBlockSuccEquiv_apply (v : Fin (n + 1) → k) :
    stdOrthogonalRepBlockSuccEquiv k n v = (Fin.init v, v (Fin.last n)) :=
  LinearEquiv.piFinSnoc_apply k (fun _ => k) v

@[simp]
theorem stdOrthogonalRepBlockSuccEquiv_symm_apply (p : (Fin n → k) × k) :
    (stdOrthogonalRepBlockSuccEquiv k n).symm p = Fin.snoc p.1 p.2 :=
  LinearEquiv.piFinSnoc_symm_apply k (fun _ => k) p

/-- **The branching splitting is orthogonal for the invariant form**: the dot product of two
vectors is the dot product of their images in the standard module of the smaller group plus the
product of their images in the trivial summand.  So the two summands are orthogonal to each other:
the invariant form of `O(n + 1, k)` restricts to the invariant form of `O(n, k)` on the smaller
standard summand and to multiplication on the trivial summand, and the trivial summand is the
orthogonal complement of the smaller standard module. -/
theorem dotProduct_eq_stdOrthogonalRepBlockSuccEquiv (v w : Fin (n + 1) → k) :
    v ⬝ᵥ w =
      (stdOrthogonalRepBlockSuccEquiv k n v).1 ⬝ᵥ (stdOrthogonalRepBlockSuccEquiv k n w).1 +
        (stdOrthogonalRepBlockSuccEquiv k n v).2 * (stdOrthogonalRepBlockSuccEquiv k n w).2 := by
  simp [dotProduct, Fin.sum_univ_castSucc, Fin.init]

/-- The standard representation of the orthogonal group stays faithful after restriction along the
block inclusion, both maps being injective. -/
theorem stdOrthogonalRep_comp_orthogonalBlockSucc_injective :
    Function.Injective ((stdOrthogonalRep k (n + 1)).comp (orthogonalBlockSucc k n)) :=
  (stdOrthogonalRep_injective k (n + 1)).comp (orthogonalBlockSucc_injective k n)

end CommRing

section Field

variable [Field k]

attribute [local instance] starRingOfComm

/-- The character of the restricted standard orthogonal representation is the character of the
standard representation of the smaller orthogonal group plus one, the dimension of the trivial
summand. -/
theorem char_stdOrthogonalRep_orthogonalBlockSucc (g : Matrix.orthogonalGroup (Fin n) k) :
    (stdOrthogonalRep k (n + 1)).character (orthogonalBlockSucc k n g) =
      (stdOrthogonalRep k n).character g + 1 := by
  rw [char_stdOrthogonalRep, char_stdOrthogonalRep, coe_orthogonalBlockSucc, trace_blockSucc]

/-- The character identity for the bundled standard representation of the orthogonal group. -/
theorem char_stdOrthogonalFDRep_orthogonalBlockSucc (g : Matrix.orthogonalGroup (Fin n) k) :
    (stdOrthogonalFDRep k (n + 1)).character (orthogonalBlockSucc k n g) =
      (stdOrthogonalFDRep k n).character g + 1 := by
  rw [char_stdOrthogonalFDRep, char_stdOrthogonalFDRep, coe_orthogonalBlockSucc, trace_blockSucc]

end Field

end TauCeti
