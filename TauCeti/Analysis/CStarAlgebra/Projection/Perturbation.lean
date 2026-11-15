/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Algebra.Star.PartialIsometry
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Tactic.NoncommRing
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# Perturbation, unitary conjugacy, and paths of star projections

Two star projections `p` and `q` in a unital C⋆-algebra satisfying `‖p - q‖ < 1` are unitarily
conjugate by a unitary close to `1` and hence in the identity path component of the unitary group.
Explicitly, Sz.-Nagy's intertwiner

`projectionIntertwiner p q = q * p + (1 - q) * (1 - p)`

satisfies `z * p = q * z` and `star z * z = z * star z = 1 - (p - q) ^ 2`. When `‖p - q‖ < 1`,
`1 - (p - q) ^ 2` is invertible by the Neumann series, so `z` is a unit whose polar unitary factor
`u = hp.closeUnitary hq h` conjugates `p` to `q` (`u * p * star u = q`). Because
`z + star z = 2 * (1 - (p - q) ^ 2)`, the polar relation gives `u + star u = 2 * √(1 - (p - q) ^ 2)`
and therefore `star (u - 1) * (u - 1) = 2 * (1 - √(1 - (p - q) ^ 2)) ≤ 2 * (p - q) ^ 2`, yielding
the sharp norm estimate `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ < 2` and `Joined (1 : unitary A) u`.

Subdividing a norm-continuous path of star projections on the compact unit interval shows that any
two path-connected projections in a unital C⋆-algebra are conjugate by a unitary in the path
component of `1`. Passing to the minimal unitization `Unitization ℂ B` transfers both the
nearby-projection theorem and the path-lifting theorem to possibly non-unital C⋆-algebras `B`: if a
unitary `u` of `Unitization ℂ B` conjugates `p` to `q`, the ideal product
`unitizationConjElem u p = u.fst • p + u.snd * p` lies in `B` itself and is a partial isometry with
initial projection `p` and final projection `q`.

We also compute the exponential of any scalar multiple of a star projection `p`: since the spectrum
of `p` is contained in `{0, 1}`, `exp (z • p) = 1 + (exp z - 1) • p`, and in particular
`expUnitary (π • p) = 1 - 2 • p` is the self-adjoint symmetry associated to `p`.

## Main definitions

* `TauCeti.projectionIntertwiner p q`: the intertwiner `q * p + (1 - q) * (1 - p)`.
* `IsStarProjection.closeUnitary`: the polar unitary of `projectionIntertwiner p q` when
  `‖p - q‖ < 1`.
* `TauCeti.unitizationConjElem u p`: the element `u.fst • p + u.snd * p` in `B` lifting `u * p`
  from `Unitization R B` into the ideal `B`.

## Main results

* `IsStarProjection.exp_smul`, `IsStarProjection.coe_expUnitary_pi_smul`: exponential formulas
  `exp (z • p) = 1 + (exp z - 1) • p` and `expUnitary (π • p) = 1 - 2 • p`.
* `IsStarProjection.closeUnitary_mul_self_mul_star`: `(hp.closeUnitary hq h : A) * p * star u = q`.
* `IsStarProjection.norm_closeUnitary_sub_one_le`:
  `‖(hp.closeUnitary hq h : A) - 1‖ ≤ √2 * ‖p - q‖`.
* `IsStarProjection.joined_one_closeUnitary`: `Joined (1 : unitary A) (hp.closeUnitary hq h)`.
* `IsStarProjection.exists_joined_one_unitary_conj_of_path`: endpoints of a norm-continuous path of
  star projections in a unital C⋆-algebra are conjugate by a unitary joined to `1`.
* `IsStarProjection.exists_isPartialIsometry_of_path`: endpoints of a norm-continuous path of star
  projections in a possibly non-unital C⋆-algebra are linked by a partial isometry in the algebra.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Proposition 4.6.6.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, London
  Mathematical Society Student Texts 49, Cambridge University Press (2000), Proposition 2.2.4 and
  Proposition 2.2.6.
-/

public section

noncomputable section

open NormedSpace
open scoped Real unitInterval

namespace TauCeti

section IntertwinerAlgebra

variable {R : Type*} [Ring R]

/-- Sz.-Nagy's intertwiner `q * p + (1 - q) * (1 - p)` between idempotents `p` and `q`. -/
def projectionIntertwiner (p q : R) : R :=
  q * p + (1 - q) * (1 - p)

/-- Unfold `TauCeti.projectionIntertwiner`. -/
theorem projectionIntertwiner_def (p q : R) :
    projectionIntertwiner p q = q * p + (1 - q) * (1 - p) :=
  (rfl)

/-- At equal idempotents `p = q`, the intertwiner is `1`. -/
@[simp]
theorem projectionIntertwiner_self {p : R} (hp : IsIdempotentElem p) :
    projectionIntertwiner p p = 1 := by
  rw [projectionIntertwiner_def]
  noncomm_ring [hp.eq]

/-- Right multiplication by an idempotent `p` collapses `projectionIntertwiner p q * p` to
`q * p`. -/
theorem projectionIntertwiner_mul_right {p q : R} (hp : IsIdempotentElem p) :
    projectionIntertwiner p q * p = q * p := by
  rw [projectionIntertwiner_def]
  noncomm_ring [hp.eq]

/-- Left multiplication by an idempotent `q` collapses `q * projectionIntertwiner p q` to
`q * p`. -/
theorem mul_projectionIntertwiner_left {p q : R} (hq : IsIdempotentElem q) :
    q * projectionIntertwiner p q = q * p := by
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq.eq]
  rw [projectionIntertwiner_def]
  noncomm_ring [hq.eq, hqqp]

/-- The element `projectionIntertwiner p q` intertwines idempotents `p` and `q`:
`z * p = q * z`. -/
theorem projectionIntertwiner_mul_eq_mul {p q : R} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) :
    projectionIntertwiner p q * p = q * projectionIntertwiner p q := by
  rw [projectionIntertwiner_mul_right hp, mul_projectionIntertwiner_left hq]

/-- For idempotents `p` and `q`, `1 - (p - q) ^ 2` commutes with `p`. -/
theorem commute_one_sub_sub_mul_self_left {p q : R} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) : Commute (1 - (p - q) * (p - q)) p := by
  have hppq : p * (p * q) = p * q := by rw [← mul_assoc, hp.eq]
  rw [commute_iff_eq]
  noncomm_ring [hp.eq, hq.eq, hppq]

/-- For idempotents `p` and `q`, `1 - (p - q) ^ 2` commutes with `q`. -/
theorem commute_one_sub_sub_mul_self_right {p q : R} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) : Commute (1 - (p - q) * (p - q)) q := by
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq.eq]
  rw [commute_iff_eq]
  noncomm_ring [hp.eq, hq.eq, hqqp]

section Star

variable [StarRing R]

/-- Taking the star of `projectionIntertwiner p q` for self-adjoint `p`, `q` swaps `p` and `q`. -/
theorem star_projectionIntertwiner {p q : R} (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) :
    star (projectionIntertwiner p q) = projectionIntertwiner q p := by
  rw [projectionIntertwiner_def, projectionIntertwiner_def, star_add, star_mul, star_mul,
    star_sub, star_sub, star_one, hp.star_eq, hq.star_eq]

/-- For star projections `p` and `q`, `star z * z = 1 - (p - q) ^ 2`. -/
theorem star_projectionIntertwiner_mul_self {p q : R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    star (projectionIntertwiner p q) * projectionIntertwiner p q = 1 - (p - q) * (p - q) := by
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq.isIdempotentElem.eq]
  have hpqqp : p * (q * (q * p)) = p * (q * p) := by rw [hqqp]
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint, projectionIntertwiner_def,
    projectionIntertwiner_def]
  noncomm_ring [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hqqp, hpqqp]

/-- For star projections `p` and `q`, `z * star z = 1 - (p - q) ^ 2`; in particular `z` is
normal. -/
theorem projectionIntertwiner_mul_star_self {p q : R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    projectionIntertwiner p q * star (projectionIntertwiner p q) = 1 - (p - q) * (p - q) := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint]
  have h := star_projectionIntertwiner_mul_self hq hp
  rw [star_projectionIntertwiner hq.isSelfAdjoint hp.isSelfAdjoint] at h
  rw [h]
  noncomm_ring

/-- Twice `1 - (p - q) ^ 2` equals `z + star z` for `z = projectionIntertwiner p q`. -/
theorem projectionIntertwiner_add_star {p q : R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    projectionIntertwiner p q + star (projectionIntertwiner p q) =
      2 * (1 - (p - q) * (p - q)) := by
  rw [star_projectionIntertwiner hp.isSelfAdjoint hq.isSelfAdjoint, projectionIntertwiner_def,
    projectionIntertwiner_def]
  noncomm_ring [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]

end Star

end IntertwinerAlgebra

section UnitizationConj

variable {R B : Type*} [CommSemiring R] [NonUnitalSemiring B] [Module R B]

/-- For an element `u` of the unitization `Unitization R B` and `p : B`, `unitizationConjElem u p`
is the unique element `u.fst • p + u.snd * p` of `B` whose image in `Unitization R B` is
`u * p`. -/
def unitizationConjElem (u : Unitization R B) (p : B) : B :=
  u.fst • p + u.snd * p

/-- Coercing `unitizationConjElem u p` into `Unitization R B` recovers `u * p`. -/
@[simp]
theorem inr_unitizationConjElem (u : Unitization R B) (p : B) :
    ((unitizationConjElem u p : B) : Unitization R B) = u * (p : Unitization R B) := by
  ext
  · simp [unitizationConjElem]
  · simp [unitizationConjElem]

variable [StarRing R] [IsScalarTower R B B] [SMulCommClass R B B] [StarRing B] [StarModule R B]

/-- If `u` is unitary in `Unitization R B` and `p` is a star projection in `B`, the initial
projection `star v * v` of `v = unitizationConjElem u p` in `B` is `p`. -/
theorem star_unitizationConjElem_mul_self {u : Unitization R B}
    (hu : u ∈ unitary (Unitization R B)) {p : B} (hp : IsStarProjection p) :
    star (unitizationConjElem u p) * unitizationConjElem u p = p := by
  apply Unitization.inr_injective (R := R)
  rw [Unitization.inr_mul, Unitization.inr_star, inr_unitizationConjElem, star_mul,
    ← Unitization.inr_star, hp.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star u),
    Unitary.star_mul_self_of_mem hu, one_mul, ← Unitization.inr_mul, hp.isIdempotentElem.eq]

/-- If `u` in `Unitization R B` conjugates a star projection `p : B` to `q : B`, the final
projection `v * star v` of `v = unitizationConjElem u p` in `B` is `q`. -/
theorem unitizationConjElem_mul_star_self {u : Unitization R B} {p q : B}
    (hp : IsStarProjection p)
    (hconj : u * (p : Unitization R B) * star u = (q : Unitization R B)) :
    unitizationConjElem u p * star (unitizationConjElem u p) = q := by
  apply Unitization.inr_injective (R := R)
  rw [Unitization.inr_mul, Unitization.inr_star, inr_unitizationConjElem, star_mul,
    ← Unitization.inr_star, hp.isSelfAdjoint.star_eq, mul_assoc,
    ← mul_assoc (p : Unitization R B), ← Unitization.inr_mul, hp.isIdempotentElem.eq,
    ← mul_assoc, hconj]

/-- Under the hypotheses of `star_unitizationConjElem_mul_self`, `unitizationConjElem u p` is a
partial isometry in `B`. -/
theorem isPartialIsometry_unitizationConjElem {u : Unitization R B}
    (hu : u ∈ unitary (Unitization R B)) {p : B} (hp : IsStarProjection p) :
    IsPartialIsometry (unitizationConjElem u p) := by
  rw [isPartialIsometry_iff, mul_assoc, star_unitizationConjElem_mul_self hu hp,
    unitizationConjElem, add_mul, smul_mul_assoc, mul_assoc, hp.isIdempotentElem.eq]

end UnitizationConj

end TauCeti

namespace IsStarProjection

open TauCeti

section Exponential

variable {A : Type*} [CStarAlgebra A]

/-- Exponential of a complex scalar multiple of a star projection:
`exp (z • p) = 1 + (Complex.exp z - 1) • p`. -/
theorem exp_smul {p : A} (hp : IsStarProjection p) (z : ℂ) :
    NormedSpace.exp (z • p) = 1 + (Complex.exp z - 1) • p := by
  have hp_spec : spectrum ℂ p ⊆ {0, 1} :=
    (isStarProjection_iff_spectrum_subset_and_isStarNormal.mp hp).1
  have hp_norm : IsStarNormal p :=
    (isStarProjection_iff_spectrum_subset_and_isStarNormal.mp hp).2
  have hzp_norm : IsStarNormal (z • p) :=
    ⟨by rw [star_smul]; exact (hp_norm.star_comm_self.smul_left (star z)).smul_right z⟩
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) hzp_norm,
    ← cfc_comp_smul z (NormedSpace.exp : ℂ → ℂ) p]
  have hlin : cfc (fun w : ℂ ↦ 1 + (Complex.exp z - 1) * w) p =
      1 + (Complex.exp z - 1) • p := by
    rw [cfc_const_add (1 : ℂ) ((Complex.exp z - 1) * ·) p, map_one,
      cfc_const_mul_id (Complex.exp z - 1) p]
  rw [← hlin]
  refine cfc_congr fun w hw ↦ ?_
  rw [← Complex.exp_eq_exp_ℂ]
  rcases hp_spec hw with hw0 | hw1
  · simp [Set.mem_singleton_iff.mp hw0]
  · simp [Set.mem_singleton_iff.mp hw1]

/-- For a star projection `p` and `t : ℝ`, the exponential unitary `expUnitary (t • p)` has
underlying element `1 + (Complex.exp (Complex.I * t) - 1) • p`. -/
theorem coe_expUnitary_smul {p : A} (hp : IsStarProjection p) (t : ℝ) :
    (selfAdjoint.expUnitary (t • ⟨p, hp.isSelfAdjoint⟩) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • p := by
  rw [selfAdjoint.expUnitary_coe]
  change NormedSpace.exp (Complex.I • (t • p)) = _
  rw [← Complex.coe_smul t p, smul_smul, hp.exp_smul]

/-- At angle `π`, `expUnitary (π • p)` equals the self-adjoint reflection `1 - 2 • p`. -/
theorem coe_expUnitary_pi_smul {p : A} (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary (π • ⟨p, hp.isSelfAdjoint⟩) : A) = 1 - (2 : ℝ) • p := by
  rw [hp.coe_expUnitary_smul π, mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I]
  have htwo : (-1 - 1 : ℂ) • p = -((2 : ℝ) • p) := by
    rw [show (-1 - 1 : ℂ) = -((2 : ℝ) : ℂ) by push_cast; ring, neg_smul, Complex.coe_smul]
  rw [htwo, sub_eq_add_neg]

end Exponential

section Perturbation

variable {A : Type*} [CStarAlgebra A]

private theorem isUnit_one_sub_sub_mul_self {p q : A} (h : ‖p - q‖ < 1) :
    IsUnit (1 - (p - q) * (p - q)) := by
  have hsq : ‖(p - q) * (p - q)‖ < 1 := by
    calc ‖(p - q) * (p - q)‖ ≤ ‖p - q‖ * ‖p - q‖ := norm_mul_le _ _
      _ < 1 * 1 := mul_lt_mul'' h h (norm_nonneg _) (norm_nonneg _)
      _ = 1 := mul_one 1
  exact (Units.oneSub ((p - q) * (p - q)) hsq).isUnit

/-- When star projections `p` and `q` satisfy `‖p - q‖ < 1`, Sz.-Nagy's intertwiner
`projectionIntertwiner p q` is a unit in `A`. -/
theorem isUnit_projectionIntertwiner {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    IsUnit (projectionIntertwiner p q) := by
  obtain ⟨w, hw⟩ := isUnit_one_sub_sub_mul_self h
  have hmul₁ : projectionIntertwiner p q * (star (projectionIntertwiner p q) * ↑w⁻¹) = 1 := by
    rw [← mul_assoc, projectionIntertwiner_mul_star_self hp hq, ← hw, Units.mul_inv]
  have hmul₂ : (↑w⁻¹ * star (projectionIntertwiner p q)) * projectionIntertwiner p q = 1 := by
    rw [mul_assoc, star_projectionIntertwiner_mul_self hp hq, ← hw, Units.inv_mul]
  have heq := left_inv_eq_right_inv hmul₂ hmul₁
  exact ⟨⟨projectionIntertwiner p q, star (projectionIntertwiner p q) * ↑w⁻¹, hmul₁,
    heq ▸ hmul₂⟩, rfl⟩

/-- The canonical unitary conjugating a star projection `p` to a nearby star projection `q`
(`‖p - q‖ < 1`), defined as the polar unitary factor of `projectionIntertwiner p q`. -/
def closeUnitary {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : unitary A :=
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  (hp.isUnit_projectionIntertwiner hq h).unit.polarUnitary

/-- The unitary `hp.closeUnitary hq h` intertwines `p` and `q`: `u * p = q * u`. -/
theorem closeUnitary_mul_self {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    (hp.closeUnitary hq h : A) * p = q * (hp.closeUnitary hq h : A) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set z := (hp.isUnit_projectionIntertwiner hq h).unit
  have hz_coe : (z : A) = projectionIntertwiner p q := IsUnit.unit_spec _
  set s := CFC.sqrt ((z : A) * star (z : A))
  have hs_unit : IsUnit s := z.isStrictlyPositive_sqrt_mul_star.isUnit
  have hs_mul_u : s * (hp.closeUnitary hq h : A) = projectionIntertwiner p q :=
    (z.sqrt_mul_star_mul_polarUnitary).trans hz_coe
  have hs_eq : (z : A) * star (z : A) = 1 - (p - q) * (p - q) := by
    rw [hz_coe, projectionIntertwiner_mul_star_self hp hq]
  have hcomm_sq : Commute s q := by
    rw [show s = CFC.sqrt (1 - (p - q) * (p - q)) from congrArg CFC.sqrt hs_eq]
    exact Commute.cfcₙ_nnreal
      (commute_one_sub_sub_mul_self_right hp.isIdempotentElem hq.isIdempotentElem) NNReal.sqrt
  apply hs_unit.mul_left_cancel
  calc s * ((hp.closeUnitary hq h : A) * p)
      = (s * (hp.closeUnitary hq h : A)) * p := (mul_assoc _ _ _).symm
    _ = projectionIntertwiner p q * p := by rw [hs_mul_u]
    _ = q * projectionIntertwiner p q :=
        projectionIntertwiner_mul_eq_mul hp.isIdempotentElem hq.isIdempotentElem
    _ = q * (s * (hp.closeUnitary hq h : A)) := by rw [hs_mul_u]
    _ = (q * s) * (hp.closeUnitary hq h : A) := (mul_assoc _ _ _).symm
    _ = (s * q) * (hp.closeUnitary hq h : A) := by rw [hcomm_sq.eq]
    _ = s * (q * (hp.closeUnitary hq h : A)) := mul_assoc _ _ _

/-- Conjugating `p` by `hp.closeUnitary hq h` yields `q`: `u * p * star u = q`. -/
@[simp]
theorem closeUnitary_mul_self_mul_star {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    (hp.closeUnitary hq h : A) * p * star (hp.closeUnitary hq h : A) = q := by
  rw [hp.closeUnitary_mul_self hq h, mul_assoc,
    Unitary.mul_star_self_of_mem (hp.closeUnitary hq h).property, mul_one]

/-- Sharp Sz.-Nagy norm bound: `‖(hp.closeUnitary hq h : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem norm_closeUnitary_sub_one_le {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ‖(hp.closeUnitary hq h : A) - 1‖ ≤ √2 * ‖p - q‖ := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set u := hp.closeUnitary hq h
  set z := (hp.isUnit_projectionIntertwiner hq h).unit
  have hz_coe : (z : A) = projectionIntertwiner p q := IsUnit.unit_spec _
  set d := p - q
  have hd_sa : IsSelfAdjoint d := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hdd_nonneg : 0 ≤ d * d := by simpa only [hd_sa.star_eq] using star_mul_self_nonneg d
  have hzz : (z : A) * star (z : A) = 1 - d * d := by
    rw [hz_coe, projectionIntertwiner_mul_star_self hp hq]
  have hz_normal : star (z : A) * (z : A) = (z : A) * star (z : A) := by
    rw [hz_coe, star_projectionIntertwiner_mul_self hp hq,
      projectionIntertwiner_mul_star_self hp hq]
  set s := CFC.sqrt ((z : A) * star (z : A))
  have hs_nonneg : 0 ≤ s := CFC.sqrt_nonneg _
  have hs_sa : IsSelfAdjoint s := hs_nonneg.isSelfAdjoint
  have hs_unit : IsUnit s := z.isStrictlyPositive_sqrt_mul_star.isUnit
  have hs_sq : s * s = 1 - d * d := by
    rw [CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg (z : A)), hzz]
  have hs_le_one : s ≤ 1 := by
    rw [← CFC.sqrt_one (A := A)]
    exact CFC.sqrt_le_sqrt _ _ (hzz.symm ▸ sub_le_self 1 hdd_nonneg)
  -- Left and right polar decompositions coincide since `z` is normal, giving `u + star u = 2 s`.
  have hsu : s * (u : A) = (z : A) := z.sqrt_mul_star_mul_polarUnitary
  have hus : (u : A) * s = (z : A) := by
    have hr := z.polarUnitary_mul_sqrt_star_mul
    rwa [hz_normal] at hr
  have hsu_star : s * star (u : A) = star (z : A) := by
    simpa only [star_mul, hs_sa.star_eq] using congrArg star hus
  have hu_add_star : (u : A) + star (u : A) = 2 * s := by
    apply hs_unit.mul_left_cancel
    calc s * ((u : A) + star (u : A))
        = s * (u : A) + s * star (u : A) := mul_add _ _ _
      _ = (z : A) + star (z : A) := by rw [hsu, hsu_star]
      _ = 2 * (1 - d * d) := by rw [hz_coe, projectionIntertwiner_add_star hp hq]
      _ = 2 * (s * s) := by rw [hs_sq]
      _ = s * (2 * s) := by noncomm_ring
  -- Hence `star (u - 1) * (u - 1) = (2 : ℝ) • (1 - s) ≤ (2 : ℝ) • (d * d)`.
  have hu_sub_sq : star ((u : A) - 1) * ((u : A) - 1) = (2 : ℝ) • (1 - s) := by
    have h1 : star ((u : A) - 1) * ((u : A) - 1) = 1 + 1 - ((u : A) + star (u : A)) := by
      rw [star_sub, star_one, sub_mul, mul_sub, mul_sub,
        Unitary.star_mul_self_of_mem u.property, mul_one, one_mul, one_mul]
      abel
    rw [h1, hu_add_star, two_mul, two_smul]
    abel
  have h_one_sub_s_nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs_le_one
  have h_one_sub_s_le : 1 - s ≤ d * d := by
    have hdiff : d * d - (1 - s) = (1 - s) * s := by
      have : 1 - s * s = d * d := by rw [hs_sq, sub_sub_cancel]
      rw [← this]
      noncomm_ring
    rw [← sub_nonneg, hdiff]
    exact Commute.mul_nonneg h_one_sub_s_nonneg hs_nonneg ((Commute.one_left s).sub_left rfl)
  have h2_nonneg : 0 ≤ (2 : ℝ) • (1 - s) := smul_nonneg zero_le_two h_one_sub_s_nonneg
  have h2_le : (2 : ℝ) • (1 - s) ≤ (2 : ℝ) • (d * d) :=
    smul_le_smul_of_nonneg_left h_one_sub_s_le zero_le_two
  have hnorm_sq : ‖(u : A) - 1‖ ^ 2 ≤ (√2 * ‖d‖) ^ 2 := by
    calc ‖(u : A) - 1‖ ^ 2
        = ‖star ((u : A) - 1) * ((u : A) - 1)‖ := by
          rw [CStarRing.norm_star_mul_self, sq]
      _ = ‖(2 : ℝ) • (1 - s)‖ := by rw [hu_sub_sq]
      _ ≤ ‖(2 : ℝ) • (d * d)‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg h2_le h2_nonneg
      _ = 2 * ‖d‖ ^ 2 := by
          rw [norm_smul, Real.norm_ofNat]
          nth_rw 1 [← hd_sa.star_eq]
          rw [CStarRing.norm_star_mul_self, ← sq]
      _ = (√2 * ‖d‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt zero_le_two]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hnorm_sq

/-- Since `‖p - q‖ < 1` and `√2 < 2`, `hp.closeUnitary hq h` has distance strictly less than `2`
from `1`. -/
theorem norm_closeUnitary_sub_one_lt_two {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ‖(hp.closeUnitary hq h : A) - 1‖ < 2 := by
  have hsqrt2 : √2 < 2 := by
    rw [Real.sqrt_lt' zero_lt_two]
    norm_num
  calc ‖(hp.closeUnitary hq h : A) - 1‖
      ≤ √2 * ‖p - q‖ := hp.norm_closeUnitary_sub_one_le hq h
    _ < √2 * 1 := mul_lt_mul_of_pos_left h (by positivity)
    _ = √2 := mul_one _
    _ < 2 := hsqrt2

/-- Nearby star projections (`‖p - q‖ < 1`) are conjugate by a unitary in the path component of `1`,
namely `hp.closeUnitary hq h`. -/
theorem joined_one_closeUnitary {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    Joined (1 : unitary A) (hp.closeUnitary hq h) :=
  Unitary.joined 1 (hp.closeUnitary hq h) (hp.norm_closeUnitary_sub_one_lt_two hq h)

/-- Existential form of Sz.-Nagy's perturbation theorem: star projections `p`, `q` with
`‖p - q‖ < 1` are conjugate by a unitary `u` joined to `1` with `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitary_conj_of_norm_sub_lt_one {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined (1 : unitary A) u ∧
      (u : A) * p * star (u : A) = q ∧ ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ :=
  ⟨hp.closeUnitary hq h, hp.joined_one_closeUnitary hq h,
    hp.closeUnitary_mul_self_mul_star hq h, hp.norm_closeUnitary_sub_one_le hq h⟩

/-- Any norm-continuous path of star projections in a unital C⋆-algebra has endpoints conjugate by
a unitary in the identity path component of `unitary A`. -/
theorem exists_joined_one_unitary_conj_of_path {p q : A} (γ : Path p q)
    (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A, Joined (1 : unitary A) u ∧ (u : A) * p * star (u : A) = q := by
  have huc : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuous_iff.mp huc 1 zero_lt_one
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ_pos
  have hN_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- Partition `[0, 1]` into `N + 1` equal subintervals of length `< δ`.
  let pt (k : ℕ) (hk : k ≤ N + 1) : I :=
    ⟨(k : ℝ) / ((N : ℝ) + 1), ⟨div_nonneg (Nat.cast_nonneg k) hN_pos.le,
      (div_le_one hN_pos).mpr (by exact_mod_cast hk)⟩⟩
  have step : ∀ (k : ℕ) (hk : k ≤ N + 1),
      ∃ u : unitary A, Joined (1 : unitary A) u ∧ (u : A) * p * star (u : A) = γ (pt k hk) := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨1, Joined.refl 1, ?_⟩
      have hpt0 : pt 0 hk = 0 := by ext; simp [pt]
      simp [hpt0]
    | succ k ih =>
      intro hk
      obtain ⟨u, hu_join, hu_conj⟩ := ih (Nat.le_of_succ_le hk)
      have hdist_pt : dist (pt k (Nat.le_of_succ_le hk)) (pt (k + 1) hk) < δ := by
        rw [Subtype.dist_eq, Real.dist_eq]
        have hsub : (k : ℝ) / ((N : ℝ) + 1) - ((k + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) =
            -(1 / ((N : ℝ) + 1)) := by push_cast; ring
        rw [hsub, abs_neg, abs_of_pos (one_div_pos.mpr hN_pos)]
        exact hN
      have hnorm : ‖γ (pt k (Nat.le_of_succ_le hk)) - γ (pt (k + 1) hk)‖ < 1 := by
        rw [← dist_eq_norm]
        exact hδ hdist_pt
      set w := (hγ (pt k (Nat.le_of_succ_le hk))).closeUnitary (hγ (pt (k + 1) hk)) hnorm
      refine ⟨w * u, by simpa only [mul_one] using
        ((hγ _).joined_one_closeUnitary (hγ _) hnorm).mul hu_join, ?_⟩
      simp only [Submonoid.coe_mul, star_mul, mul_assoc]
      rw [← mul_assoc (u : A), ← mul_assoc ((u : A) * p), hu_conj, ← mul_assoc,
        (hγ _).closeUnitary_mul_self_mul_star (hγ _) hnorm]
  obtain ⟨u, hu_join, hu_conj⟩ := step (N + 1) le_rfl
  have hpt1 : pt (N + 1) le_rfl = 1 := by
    ext
    simp [pt, div_self hN_pos.ne']
  rw [hpt1, γ.target] at hu_conj
  exact ⟨u, hu_join, hu_conj⟩

end Perturbation

section NonUnitalPerturbation

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- In a possibly non-unital C⋆-algebra `B`, star projections `p` and `q` with `‖p - q‖ < 1` are
conjugate inside `Unitization ℂ B` by a unitary joined to `1` satisfying
`‖(u : Unitization ℂ B) - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_unitization_unitary_conj_of_norm_sub_lt_one {p q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ u : unitary (Unitization ℂ B), Joined (1 : unitary (Unitization ℂ B)) u ∧
      (u : Unitization ℂ B) * (p : Unitization ℂ B) * star (u : Unitization ℂ B) =
        (q : Unitization ℂ B) ∧
      ‖(u : Unitization ℂ B) - 1‖ ≤ √2 * ‖p - q‖ := by
  have hp' : IsStarProjection (p : Unitization ℂ B) :=
    hp.map (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hq' : IsStarProjection (q : Unitization ℂ B) :=
    hq.map (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hnorm_eq : ‖(p : Unitization ℂ B) - (q : Unitization ℂ B)‖ = ‖p - q‖ := by
    rw [← Unitization.inr_sub, Unitization.norm_inr]
  obtain ⟨u, hu_join, hu_conj, hu_norm⟩ :=
    hp'.exists_unitary_conj_of_norm_sub_lt_one hq' (hnorm_eq.trans_lt h)
  exact ⟨u, hu_join, hu_conj, hnorm_eq ▸ hu_norm⟩

/-- Nearby star projections (`‖p - q‖ < 1`) in a possibly non-unital C⋆-algebra `B` are linked by
a partial isometry `v : B` with `star v * v = p` and `v * star v = q`. -/
theorem exists_isPartialIsometry_of_norm_sub_lt_one {p q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    ∃ v : B, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  obtain ⟨u, -, hu_conj, -⟩ := hp.exists_unitization_unitary_conj_of_norm_sub_lt_one hq h
  exact ⟨unitizationConjElem (u : Unitization ℂ B) p,
    isPartialIsometry_unitizationConjElem u.property hp,
    star_unitizationConjElem_mul_self u.property hp,
    unitizationConjElem_mul_star_self hp hu_conj⟩

/-- Any norm-continuous path of star projections in a possibly non-unital C⋆-algebra `B` yields a
partial isometry `v : B` with `star v * v = p` and `v * star v = q`. -/
theorem exists_isPartialIsometry_of_path {p q : B} (γ : Path p q)
    (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ v : B, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  let inrCont : C(B, Unitization ℂ B) :=
    ⟨Unitization.inr, Unitization.isometry_inr.continuous⟩
  let γ' : Path (p : Unitization ℂ B) (q : Unitization ℂ B) := γ.map inrCont.continuous
  have hγ' : ∀ t : I, IsStarProjection (γ' t) := fun t ↦
    (hγ t).map (Unitization.inrNonUnitalStarAlgHom ℂ B)
  obtain ⟨u, -, hu_conj⟩ := exists_joined_one_unitary_conj_of_path γ' hγ'
  have hp : IsStarProjection p := γ.source ▸ hγ 0
  exact ⟨unitizationConjElem (u : Unitization ℂ B) p,
    isPartialIsometry_unitizationConjElem u.property hp,
    star_unitizationConjElem_mul_self u.property hp,
    unitizationConjElem_mul_star_self hp hu_conj⟩

end NonUnitalPerturbation

end IsStarProjection
