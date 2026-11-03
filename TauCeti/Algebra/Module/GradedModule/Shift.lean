/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Shifting an internal grading

An internal grading may be regraded by a fixed shift `c`, so that the degree-`p` piece of the
shifted grading is the degree-`(p + c)` piece of the original one. The underlying module is
unchanged, and the shifted family is again an internal direct sum: reindexing the homogeneous
pieces along an equivalence of degrees only permutes the summands of `⨁ p, G.piece p`.
The degrees may form any additive group. Simultaneous shifts preserve the degree of a homogeneous
map when the degree group is commutative.

For integer degrees, shifting by one is the suspension `sA` in the `A∞` conventions. The
suspension leaves the underlying module unchanged and reindexes its homogeneous pieces.

## Main definitions

* `TauCeti.InternalGrading.shift`: the shift of an internal grading.

## Main results

* `TauCeti.LinearMap.isHomogeneous_shift_piece_iff`: shifting both gradings preserves degrees.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

namespace TauCeti

universe u v

namespace InternalGrading

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type} [DecidableEq ι] [AddGroup ι]

/-- The shift of an internal grading by `c`: its degree-`p` piece is the degree-`(p + c)` piece of
the original grading. The underlying module is unchanged. -/
def shift (G : InternalGrading R M ι) (c : ι) : InternalGrading R M ι where
  piece := fun p ↦ G.piece (Equiv.addRight c p)
  isInternal := by
    refine TauCeti.DirectSum.isInternal_of_lof
      (e := fun p ↦ LinearEquiv.refl R (G.piece (Equiv.addRight c p)))
      (E := (DirectSum.lequivCongrLeft R (Equiv.addRight c).symm).symm.trans
        (DirectSum.decomposeLinearEquiv G.piece).symm) ?_
    intro p x
    -- Express the generator family using the inverse reindexing, so the generator formula
    -- matches without unfolding the semireducible Equiv.addRight permutation.
    change (DirectSum.decomposeLinearEquiv G.piece).symm
      ((DirectSum.lequivCongrLeft R (Equiv.addRight c).symm).symm
        (DirectSum.lof R ι (fun p ↦ G.piece ((Equiv.addRight c).symm.symm p)) p x)) =
          (x : M)
    rw [DirectSum.lequivCongrLeft_symm_lof, DirectSum.decomposeLinearEquiv_symm_lof]

@[simp]
theorem shift_piece (G : InternalGrading R M ι) (c p : ι) :
    (G.shift c).piece p = G.piece (p + c) :=
  (rfl)

@[simp]
theorem shift_zero (G : InternalGrading R M ι) : G.shift 0 = G := by
  ext p
  simp

/-- Shifting twice shifts by the sum of the two amounts. -/
@[simp]
theorem shift_shift (G : InternalGrading R M ι) (c d : ι) :
    (G.shift c).shift d = G.shift (d + c) := by
  ext p
  simp [add_assoc]

/-- A Koszul twist preserves the original degree, expressed in any shifted grading. -/
theorem koszulTwist_mem_shift_piece {R : Type u} {M : Type v}
    [CommRing R] [AddCommMonoid M] [Module R M] (G : InternalGrading R M)
    {x : M} {e : ℤ} (hx : x ∈ G.piece e) (q c : ℤ) :
    G.koszulTwist q x ∈ (G.shift c).piece (e - c) := by
  rw [shift_piece, sub_add_cancel]
  exact G.koszulTwist_mem_piece hx q

/-- The Koszul twist of parameter `q` for a grading shifted by `c` differs from the unshifted
twist by the constant sign `(-1)^(q * c)`: a homogeneous element of degree `p` has degree `p - c`
after the shift. -/
theorem koszulTwist_shift {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]
    (G : InternalGrading R M) (c q : ℤ) :
    (G.shift c).koszulTwist q = (((q * c).negOnePow : ℤ) : R) • G.koszulTwist q := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  have hshift : x ∈ (G.shift c).piece (p - c) := by rwa [shift_piece, sub_add_cancel]
  rw [koszulTwist_apply_of_mem _ hshift, LinearMap.smul_apply, G.koszulTwist_apply_of_mem hx,
    smul_smul, ← Int.cast_mul, ← Units.val_mul, mul_sub, Int.negOnePow_sub]
  congr 3
  exact mul_comm _ _

/-- The degree-one Koszul twist of the suspended grading is the negative of the unsuspended one. -/
theorem koszulTwist_one_shift_one {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (G : InternalGrading R M) :
    (G.shift 1).koszulTwist 1 = -G.koszulTwist 1 := by
  rw [koszulTwist_shift]
  simp

end InternalGrading

/-- Shifting the source and the target internal grading by the same amount leaves the degree of a
homogeneous linear map unchanged. -/
theorem LinearMap.isHomogeneous_shift_piece_iff {R : Type u} {M N : Type*} [Semiring R]
    {ι : Type} [DecidableEq ι] [AddCommGroup ι]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {G : InternalGrading R M ι}
    {H : InternalGrading R N ι} {f : M →ₗ[R] N} {c q : ι} :
    LinearMap.IsHomogeneous f (G.shift c).piece (H.shift c).piece q ↔
      LinearMap.IsHomogeneous f G.piece H.piece q := by
  simp only [LinearMap.isHomogeneous_def, InternalGrading.shift_piece]
  constructor
  · intro hf p x hx
    simpa only [sub_add_cancel, sub_add_eq_add_sub] using hf (p - c) x (by rwa [sub_add_cancel])
  · intro hf p x hx
    rw [add_right_comm]
    exact hf _ x hx

end TauCeti
