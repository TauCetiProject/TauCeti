/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.Projection.Equivalence
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Connected.Clopen
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Algebra.Star.Projection.Pair

/-!
# Nearby and homotopic projections, exponential formulas, and stabilized rotation paths

Two star projections `p` and `q` in a unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a
unitary `u` with `‖u - 1‖ ≤ √2 * ‖p - q‖`. The unitary is the unitary part of the polar
decomposition of the intertwiner `z = q * p + (1 - q) * (1 - p)`: since
`star z * z = z * star z = 1 - (p - q) ^ 2` commutes with `p` and `q`, the element
`u = z * (1 - (p - q) ^ 2) ^ (-1 / 2)` is a unitary with `u * p * star u = q`, and its real part
`(1 - (p - q) ^ 2) ^ (1 / 2)` gives the norm estimate. Since `‖u - 1‖ < 2`, the unitary lies in
the path component of the identity of the unitary group.

Consequently the values of a norm-continuous family of projections over a preconnected space are
mutually unitarily equivalent, through unitaries joined to `1`. In a C⋆-algebra without unit,
applying this in the unitization shows that nearby projections, and the values of a continuous
family of projections, are Murray–von Neumann equivalent. For matrices over a C⋆-algebra this says
that matrix projections joined by a path of matrix projections are Murray–von Neumann equivalent,
so they have the same class in the projection monoid `V(A)`.

Conversely, over any (possibly non-unital) C⋆-algebra `A`, equivalent matrix projections `p` and
`q` are joined by an explicit rotation path `CStarMatrix.stabilizedPath p q v` from `p ⊕ 0` to
`0 ⊕ q`. Using the projection exponential formula `exp (z • r) = 1 + (exp z - 1) • r`, this path
equals unitary conjugation by `expUnitary ((t * π) • r)` in the unitization for
`r = CStarMatrix.stabilizedProjection p q v` while remaining inside `CStarMatrix (m ⊕ n) (m ⊕ n) A`
even when `A` has no unit, characterizing `CStarMatrix.MurrayVonNeumannEquiv` by stabilized
projection homotopy (`CStarMatrix.murrayVonNeumannEquiv_iff_exists_stabilized_path`) and extending
`Matrix.IsMurrayVonNeumannEquivalent.exists_path_fromBlocks` to non-unital C⋆-algebras.

## Main statements

* `IsStarProjection.exp_smul`, `IsStarProjection.coe_expUnitary_smul`,
  `IsStarProjection.coe_expUnitary_pi_smul`: exponential of scalar multiples of a star projection,
  with `expUnitary (π • p) = 1 - 2 • p`.
* `IsStarProjection.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one`: projections `p` and
  `q` of a unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a unitary `u` with
  `‖u - 1‖ ≤ √2 * ‖p - q‖`.
* `IsStarProjection.exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one`: the conjugating
  unitary can be chosen in the path component of `1`.
* `IsStarProjection.exists_star_mul_self_eq_of_norm_sub_lt_one`,
  `IsStarProjection.murrayVonNeumannEquiv_of_norm_sub_lt_one`: in a C⋆-algebra, possibly without
  unit, projections with `‖p - q‖ < 1` are Murray–von Neumann equivalent.
* `Continuous.exists_joined_one_mul_mul_star_eq`, `Continuous.exists_star_mul_self_eq`,
  `Continuous.isMurrayVonNeumannEquivalent`, `Continuous.murrayVonNeumannEquiv`,
  `Path.murrayVonNeumannEquiv_of_isStarProjection`: homotopy invariance of unitary and Murray–von
  Neumann equivalence over preconnected spaces and paths.
* `CStarMatrix.stabilizedProjection`, `CStarMatrix.stabilizedRotation`,
  `CStarMatrix.stabilizedPath`, `CStarMatrix.inr_stabilizedRotation_eq_expUnitary_conj`: explicit
  stabilized rotation path from `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` and its unitization
  exponential-conjugacy identity.
* `CStarMatrix.MurrayVonNeumannEquiv.exists_stabilized_path`,
  `CStarMatrix.murrayVonNeumannEquiv_iff_exists_stabilized_path`,
  `Matrix.IsMurrayVonNeumannEquivalent.exists_path_fromBlocks`: equivalence of matrix projections
  over any (possibly non-unital) C⋆-algebra implies, and is characterized by, stabilized homotopy.

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Chapter 2.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Section 4.6.
-/

public section

open scoped Real unitInterval

/-- For `|t| ≤ s < 1`, the defect `2 - 2 * √(1 - t)` is at most `2 * s` in absolute value. -/
private theorem abs_two_sub_two_mul_sqrt_one_sub_le {t s : ℝ} (hts : |t| ≤ s) (hs : s < 1) :
    |2 - 2 * √(1 - t)| ≤ 2 * s := by
  have ht : 0 ≤ 1 - t := by linarith [le_abs_self t]
  have hsq := Real.sq_sqrt ht
  have hnn := Real.sqrt_nonneg (1 - t)
  rw [abs_le] at hts ⊢
  constructor <;> nlinarith

namespace IsStarProjection

section Exponential

variable {A : Type*} [CStarAlgebra A]

/-- Exponential of a complex scalar multiple of a star projection:
`exp (z • p) = 1 + (Complex.exp z - 1) • p`. -/
theorem exp_smul {p : A} (hp : IsStarProjection p) (z : ℂ) :
    NormedSpace.exp (z • p) = 1 + (Complex.exp z - 1) • p := by
  obtain ⟨hp_spec, hp_norm⟩ := isStarProjection_iff_spectrum_subset_and_isStarNormal.mp hp
  have hzp_norm : IsStarNormal (z • p) :=
    ⟨by rw [star_smul]; exact (hp_norm.star_comm_self.smul_left (star z)).smul_right z⟩
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) hzp_norm,
    ← cfc_comp_smul z (NormedSpace.exp : ℂ → ℂ) p]
  have hlin : cfc (fun w : ℂ ↦ 1 + (Complex.exp z - 1) * w) p = 1 + (Complex.exp z - 1) • p := by
    rw [cfc_const_add (1 : ℂ) ((Complex.exp z - 1) * ·) p, map_one,
      cfc_const_mul_id (Complex.exp z - 1) p]
  rw [← hlin]
  refine cfc_congr fun w hw ↦ ?_
  rw [← Complex.exp_eq_exp_ℂ]
  rcases hp_spec hw with hw0 | hw1 <;> simp [Set.mem_singleton_iff.mp ‹_›]

/-- For a star projection `p` and `t : ℝ`, `expUnitary (t • p)` has underlying element
`1 + (Complex.exp (Complex.I * t) - 1) • p`. -/
theorem coe_expUnitary_smul {p : A} (hp : IsStarProjection p) (t : ℝ) :
    (selfAdjoint.expUnitary (t • ⟨p, hp.isSelfAdjoint⟩) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • p := by
  rw [selfAdjoint.expUnitary_coe, selfAdjoint.val_smul, ← Complex.coe_smul t p, smul_smul,
    hp.exp_smul]

/-- At angle `π`, `expUnitary (π • p)` equals the self-adjoint reflection `1 - 2 • p`. -/
theorem coe_expUnitary_pi_smul {p : A} (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary (π • ⟨p, hp.isSelfAdjoint⟩) : A) = 1 - (2 : ℝ) • p := by
  rw [hp.coe_expUnitary_smul π, mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I]
  have hscalar : (-1 - 1 : ℂ) = -((2 : ℝ) : ℂ) := by push_cast; ring
  rw [hscalar, neg_smul, Complex.coe_smul, sub_eq_add_neg]

end Exponential

section Unital

variable {A : Type*} [CStarAlgebra A] {p q : A}

section Defect

/-! In this section `h` is a self-adjoint element with `‖h‖ < 1`, so that `1 - h` has the
inverse square root `cfc (fun t ↦ (√(1 - t))⁻¹) h`. -/

variable {h : A}

private theorem one_sub_eq_cfc (hh : IsSelfAdjoint h) : 1 - h = cfc (fun t : ℝ ↦ 1 - t) h := by
  rw [cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) (fun t : ℝ ↦ t) h, cfc_const_one ℝ h, cfc_id' ℝ h]

variable (hh : IsSelfAdjoint h) (h₁ : ‖h‖ < 1)
include h₁

private theorem one_sub_pos_of_mem_spectrum {t : ℝ} (ht : t ∈ spectrum ℝ h) : 0 < 1 - t := by
  have := spectrum.norm_le_norm_of_mem ht
  rw [Real.norm_eq_abs] at this
  linarith [le_abs_self t]

private theorem continuousOn_inv_sqrt_one_sub :
    ContinuousOn (fun t : ℝ ↦ (√(1 - t))⁻¹) (spectrum ℝ h) :=
  ContinuousOn.inv₀ (by fun_prop) fun _ ht ↦
    (Real.sqrt_pos.2 (one_sub_pos_of_mem_spectrum h₁ ht)).ne'

include hh

/-- `(1 - h) ^ (-1 / 2) * (1 - h) = (1 - h) ^ (1 / 2)`. -/
private theorem cfc_inv_sqrt_one_sub_mul_one_sub :
    cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * (1 - h) = cfc (fun t : ℝ ↦ √(1 - t)) h := by
  rw [one_sub_eq_cfc hh, ← cfc_mul _ _ h (continuousOn_inv_sqrt_one_sub h₁) (by fun_prop)]
  refine cfc_congr fun t ht ↦ ?_
  have h₀ := one_sub_pos_of_mem_spectrum h₁ ht
  have := Real.sq_sqrt h₀.le
  have := (Real.sqrt_pos.2 h₀).ne'
  field_simp
  linarith

/-- `(1 - h) ^ (-1 / 2) * (1 - h) ^ (-1 / 2) * (1 - h) = 1`. -/
private theorem cfc_inv_sqrt_one_sub_mul_self_mul_one_sub :
    cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * (1 - h) = 1 := by
  have hc := continuousOn_inv_sqrt_one_sub h₁
  rw [mul_assoc, cfc_inv_sqrt_one_sub_mul_one_sub hh h₁, ← cfc_mul _ _ h hc (by fun_prop),
    ← cfc_const_one ℝ h]
  refine cfc_congr fun t ht ↦ ?_
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (one_sub_pos_of_mem_spectrum h₁ ht)).ne'

/-- `‖2 - 2 * (1 - h) ^ (1 / 2)‖ ≤ 2 * ‖h‖`. -/
private theorem norm_two_sub_two_mul_cfc_sqrt_one_sub_le :
    ‖2 - 2 * cfc (fun t : ℝ ↦ √(1 - t)) h‖ ≤ 2 * ‖h‖ := by
  have hcfc : 2 - 2 * cfc (fun t : ℝ ↦ √(1 - t)) h = cfc (fun t : ℝ ↦ 2 - 2 * √(1 - t)) h := by
    rw [cfc_sub (fun _ : ℝ ↦ (2 : ℝ)) (fun t : ℝ ↦ 2 * √(1 - t)) h, cfc_const_mul 2 _ h,
      cfc_const (2 : ℝ) h, map_ofNat, two_smul, two_mul]
  rw [hcfc]
  refine norm_cfc_le (by positivity) fun t ht ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_two_sub_two_mul_sqrt_one_sub_le (spectrum.norm_le_norm_of_mem ht) h₁

end Defect

/-- **Nearby projections are unitarily equivalent.** Star projections `p` and `q` of a unital
C⋆-algebra with `‖p - q‖ < 1` are conjugate, `u * p * star u = q`, by a unitary `u` with
`‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ u ∈ unitary A, u * p * star u = q ∧ ‖u - 1‖ ≤ √2 * ‖p - q‖ := by
  -- `h = (p - q) ^ 2` commutes with `p` and `q`, and `z` intertwines `p` with `q`.
  set h := (p - q) ^ 2
  set z := TauCeti.intertwiner p q with hz
  have hp' := hp.isIdempotentElem
  have hq' := hq.isIdempotentElem
  have hh : IsSelfAdjoint h := (hp.isSelfAdjoint.sub hq.isSelfAdjoint).pow 2
  have hnorm : ‖h‖ ≤ ‖p - q‖ ^ 2 := norm_pow_le' _ two_pos
  have h₁ : ‖h‖ < 1 := hnorm.trans_lt (by nlinarith [norm_nonneg (p - q)])
  have hzz : star z * z = 1 - h := hp.star_intertwiner_mul_intertwiner hq
  have hzz' : z * star z = 1 - h := hp.intertwiner_mul_star_intertwiner hq
  have hzp : z * p = q * z := hp'.intertwiner_mul hq'
  -- `c = (1 - h) ^ (-1 / 2)` commutes with `p`, `q`, `h`, `z` and `star z`.
  set c := cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h
  have hc : star c = c := IsSelfAdjoint.cfc.star_eq
  have hcc : c * c * (1 - h) = 1 := cfc_inv_sqrt_one_sub_mul_self_mul_one_sub hh h₁
  have hcp : Commute c p := Commute.cfc_real (hp'.commute_sub_sq_left hq').symm _
  have hcq : Commute c q := Commute.cfc_real (hp'.commute_sub_sq_right hq').symm _
  have hc₁ : Commute c (1 - h) := (Commute.one_right c).sub_right (Commute.cfc_real (.refl h) _)
  have hcz : Commute c z := by
    rw [hz, TauCeti.intertwiner_def]
    exact (hcq.mul_right hcp).add_right
      (((Commute.one_right c).sub_right hcq).mul_right ((Commute.one_right c).sub_right hcp))
  have hcz' : Commute c (star z) := hc ▸ hcz.star_star
  -- The unitary `u = z * c`, the unitary part of the polar decomposition of `z`.
  have hu₁ : star (z * c) * (z * c) = 1 := by
    calc star (z * c) * (z * c) = c * (star z * z) * c := by simp only [star_mul, hc, mul_assoc]
      _ = c * c * (1 - h) := by rw [hzz, mul_assoc, ← hc₁.eq, ← mul_assoc]
      _ = 1 := hcc
  have hu₂ : z * c * star (z * c) = 1 := by
    calc z * c * star (z * c) = z * ((c * c) * star z) := by simp only [star_mul, hc, mul_assoc]
      _ = (1 - h) * (c * c) := by rw [(hcz'.mul_left hcz').eq, ← mul_assoc, hzz']
      _ = 1 := by rw [← (hc₁.mul_left hc₁).eq, hcc]
  have hconj : z * c * p * star (z * c) = q := by
    calc z * c * p * star (z * c) = z * p * (c * star (z * c)) := by
          rw [mul_assoc z c p, hcp.eq, ← mul_assoc z p c, mul_assoc]
      _ = q * (z * c * star (z * c)) := by rw [hzp, mul_assoc, mul_assoc, ← mul_assoc z c]
      _ = q := by rw [hu₂, mul_one]
  -- Its real part is `(1 - h) ^ (1 / 2)`, which gives the norm estimate.
  have hdefect : star (z * c - 1) * (z * c - 1) = 2 - 2 * cfc (fun t : ℝ ↦ √(1 - t)) h := by
    have hzs : z + star z = 2 * (1 - h) := hp.intertwiner_add_star_intertwiner hq
    have hre : z * c + star (z * c) = 2 * cfc (fun t : ℝ ↦ √(1 - t)) h := by
      rw [star_mul, hc, ← hcz.eq, ← mul_add, hzs, two_mul, mul_add, ← two_mul,
        cfc_inv_sqrt_one_sub_mul_one_sub hh h₁]
    rw [← hre, star_sub, star_one, sub_mul, mul_sub, mul_sub, hu₁, mul_one, one_mul, one_mul,
      ← one_add_one_eq_two]
    abel
  have hbound : ‖z * c - 1‖ ^ 2 ≤ 2 * ‖p - q‖ ^ 2 := by
    rw [sq, ← CStarRing.norm_star_mul_self, hdefect]
    exact (norm_two_sub_two_mul_cfc_sqrt_one_sub_le hh h₁).trans (by gcongr)
  refine ⟨z * c, ⟨hu₁, hu₂⟩, hconj, ?_⟩
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt zero_le_two]

/-- **Nearby projections are homotopic through unitaries.** Star projections `p` and `q` of a
unital C⋆-algebra with `‖p - q‖ < 1` are conjugate by a unitary in the path component of `1`. -/
theorem exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * p * star (u : A) = q := by
  obtain ⟨u, hu, hupq, hnorm⟩ := hp.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one hq hpq
  refine ⟨⟨u, hu⟩, Unitary.joined 1 ⟨u, hu⟩ ?_, hupq⟩
  have hsqrt : √2 < 2 := by
    rw [Real.sqrt_lt' two_pos]
    norm_num
  calc ‖u - ((1 : unitary A) : A)‖ = ‖u - 1‖ := by rw [OneMemClass.coe_one]
    _ ≤ √2 * ‖p - q‖ := hnorm
    _ ≤ √2 * 1 := by gcongr
    _ < 2 := by rwa [mul_one]

end Unital

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {p q : A}

/-- **Nearby projections are Murray–von Neumann equivalent.** Star projections `p` and `q` of a
C⋆-algebra, possibly without unit, with `‖p - q‖ < 1` satisfy `star v * v = p` and
`v * star v = q` for some `v`. -/
theorem exists_star_mul_self_eq_of_norm_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) : ∃ v : A, star v * v = p ∧ v * star v = q := by
  have hp' := hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hq' := hq.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  rw [Unitization.inrNonUnitalStarAlgHom_apply] at hp' hq'
  obtain ⟨u, hu, hupq, -⟩ := hp'.exists_mem_unitary_mul_mul_star_eq_of_norm_sub_lt_one hq'
    (by rwa [← Unitization.inr_sub, Unitization.norm_inr])
  exact hp.exists_star_mul_self_eq_of_mem_unitary_unitization hu hupq

/-- Nearby matrix projections (`‖p - q‖ < 1`) in `CStarMatrix n n A` are Murray–von Neumann
equivalent, even when `A` is non-unital. -/
theorem murrayVonNeumannEquiv_of_norm_sub_lt_one {n : Type*} [Fintype n]
    [PartialOrder A] [StarOrderedRing A] {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    CStarMatrix.MurrayVonNeumannEquiv p q := by
  rw [CStarMatrix.murrayVonNeumannEquiv_iff hp hq]
  obtain ⟨v, hv₁, hv₂⟩ := hp.exists_star_mul_self_eq_of_norm_sub_lt_one hq h
  exact ⟨v, by simpa only [← CStarMatrix.star_eq_conjTranspose] using hv₁,
    by simpa only [← CStarMatrix.star_eq_conjTranspose] using hv₂⟩

end NonUnital

end IsStarProjection

section Continuous

/-! The statements below write `Star.star`: in a declaration named `Continuous.foo`, plain `star`
resolves to `Continuous.star`. -/

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

/-- **Homotopic projections are unitarily equivalent.** For a continuous family `f` of star
projections of a unital C⋆-algebra over a preconnected space, any two values `f x` and `f y` are
conjugate by a unitary in the path component of `1`. For a path of projections this compares its
endpoints. -/
theorem Continuous.exists_joined_one_mul_mul_star_eq {A : Type*} [CStarAlgebra A] {f : X → A}
    (hf : Continuous f) (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    ∃ u : unitary A, Joined 1 u ∧ (u : A) * f x * Star.star (u : A) = f y := by
  refine PreconnectedSpace.induction₂'
    (fun x y ↦ ∃ u : unitary A, Joined 1 u ∧ (u : A) * f x * Star.star (u : A) = f y)
    (fun x ↦ ?_) ⟨fun a b c ⟨u, hu, hab⟩ ⟨v, hv, hbc⟩ ↦ ⟨v * u, ?_, ?_⟩⟩ x y
  · filter_upwards [hf.continuousAt.eventually (Metric.ball_mem_nhds (f x) one_pos)] with y hy
    rw [dist_eq_norm] at hy
    exact ⟨(hfp x).exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one (hfp y)
      (by rwa [norm_sub_rev]), (hfp y).exists_joined_one_mul_mul_star_eq_of_norm_sub_lt_one
      (hfp x) hy⟩
  · simpa using hv.mul hu
  · rw [Submonoid.coe_mul, star_mul, ← hbc, ← hab]
    simp only [mul_assoc]

/-- **Homotopic projections are Murray–von Neumann equivalent.** For a continuous family `f` of
star projections of a C⋆-algebra, possibly without unit, over a preconnected space, any two values
satisfy `star v * v = f x` and `v * star v = f y` for some `v`. -/
theorem Continuous.exists_star_mul_self_eq {A : Type*} [NonUnitalCStarAlgebra A] {f : X → A}
    (hf : Continuous f) (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    ∃ v : A, Star.star v * v = f x ∧ v * Star.star v = f y := by
  have hfp' (x : X) : IsStarProjection ((f x : A) : Unitization ℂ A) := by
    simpa using (hfp x).map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  obtain ⟨u, -, hu⟩ :=
    ((Unitization.continuous_inr (𝕜 := ℂ)).comp hf).exists_joined_one_mul_mul_star_eq hfp' x y
  exact (hfp x).exists_star_mul_self_eq_of_mem_unitary_unitization u.property hu

/-- **Homotopic matrix projections are Murray–von Neumann equivalent.** For a continuous family `f`
of matrix projections over a C⋆-algebra, possibly without unit, over a preconnected space, any two
values `f x` and `f y` are Murray–von Neumann equivalent. The topology on matrices is the entrywise
one, which is the norm topology of `CStarMatrix n n A`. -/
theorem Continuous.isMurrayVonNeumannEquivalent {A : Type*} [NonUnitalCStarAlgebra A]
    {n : Type*} [Fintype n] {f : X → Matrix n n A} (hf : Continuous f)
    (hfp : ∀ x, IsStarProjection (f x)) (x y : X) :
    Matrix.IsMurrayVonNeumannEquivalent (f x) (f y) := by
  -- `CStarMatrix n n A` is a C⋆-algebra for the spectral order on `A`.
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  have hfp' (x : X) : IsStarProjection (CStarMatrix.ofMatrix (f x)) :=
    CStarMatrix.isStarProjection_ofMatrix_iff.2 (hfp x)
  have hg : Continuous fun x ↦ CStarMatrix.ofMatrix (f x) := by
    rw [CStarMatrix.ofMatrix_eq_ofMatrixL]
    exact CStarMatrix.ofMatrixL.continuous.comp hf
  obtain ⟨v, hv₁, hv₂⟩ := hg.exists_star_mul_self_eq hfp' x y
  refine ⟨hfp x, hfp y, CStarMatrix.ofMatrix.symm v, ?_, ?_⟩
  · rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul, hv₁,
      Equiv.symm_apply_apply]
  · rw [← CStarMatrix.ofMatrix_symm_star, ← CStarMatrix.ofMatrix_symm_mul, hv₂,
      Equiv.symm_apply_apply]

/-- For a continuous family `f` of `CStarMatrix` projections over a preconnected space, any two
values `f x` and `f y` satisfy `CStarMatrix.MurrayVonNeumannEquiv (f x) (f y)`. -/
theorem Continuous.murrayVonNeumannEquiv {A n : Type*} [NonUnitalCStarAlgebra A] [Fintype n]
    {f : X → CStarMatrix n n A} (hf : Continuous f) (hfp : ∀ x, IsStarProjection (f x))
    (x y : X) : CStarMatrix.MurrayVonNeumannEquiv (f x) (f y) := by
  rw [CStarMatrix.murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  exact (CStarMatrix.ofMatrixL.symm.continuous.comp hf).isMurrayVonNeumannEquivalent
    (fun z ↦ CStarMatrix.isStarProjection_ofMatrix_symm_iff.2 (hfp z)) x y

end Continuous

/-- Endpoints of any norm-continuous path of star projections in `CStarMatrix n n A` are
Murray–von Neumann equivalent. -/
theorem Path.murrayVonNeumannEquiv_of_isStarProjection {A n : Type*} [NonUnitalCStarAlgebra A]
    [Fintype n] {p q : CStarMatrix n n A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    CStarMatrix.MurrayVonNeumannEquiv p q := by
  simpa only [γ.source, γ.target] using γ.continuous.murrayVonNeumannEquiv hγ 0 1

noncomputable section

namespace CStarMatrix

section StabilizedHomotopy

variable {m n A : Type*}

/-- The block matrix `r = (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q` in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`, which is a star projection when `v` implements a Murray–von
Neumann equivalence over a C⋆-algebra, without requiring a unit in `A` or `DecidableEq` on the
index types. -/
def stabilizedProjection [Neg A] [SMul ℝ A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q

/-- Unfold `CStarMatrix.stabilizedProjection`. -/
theorem stabilizedProjection_def [Neg A] [SMul ℝ A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    stabilizedProjection p q v = (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := (rfl)

section RotationPath

variable [NonUnitalCStarAlgebra A]

/-- Explicit rotation family `stabilizedRotation p q v t` in `CStarMatrix (m ⊕ n) (m ⊕ n) A` joining
`fromBlocks p 0 0 0` (at `t = 0`) to `fromBlocks 0 0 0 q` (at `t = 1`). When `p` and `q` are star
projections with `v.conjTranspose * v = p` and `v * v.conjTranspose = q`, this equals the unitary
conjugate `expUnitary ((t * π) • r) * fromBlocks p 0 0 0 * star (expUnitary ((t * π) • r))` in the
unitization (`r = stabilizedProjection p q v`) while remaining inside
`CStarMatrix (m ⊕ n) (m ⊕ n) A` even for non-unital `A`. -/
def stabilizedRotation (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) (t : ℝ) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fromBlocks ((Real.cos (π * t / 2) ^ 2 : ℝ) • p)
    (((Complex.I / 2) * Real.sin (π * t)) • v.conjTranspose)
    ((-(Complex.I / 2) * Real.sin (π * t)) • v)
    ((Real.sin (π * t / 2) ^ 2 : ℝ) • q)

/-- Unfold `CStarMatrix.stabilizedRotation`. -/
theorem stabilizedRotation_def (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) (t : ℝ) :
    stabilizedRotation p q v t =
      fromBlocks ((Real.cos (π * t / 2) ^ 2 : ℝ) • p)
        (((Complex.I / 2) * Real.sin (π * t)) • v.conjTranspose)
        ((-(Complex.I / 2) * Real.sin (π * t)) • v)
        ((Real.sin (π * t / 2) ^ 2 : ℝ) • q) := (rfl)

/-- At `t = 0`, `stabilizedRotation p q v 0` is the top-left corner `fromBlocks p 0 0 0`. -/
@[simp]
theorem stabilizedRotation_zero (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v 0 = fromBlocks p 0 0 0 := by simp [stabilizedRotation_def]

/-- At `t = 1`, `stabilizedRotation p q v 1` is the bottom-right corner `fromBlocks 0 0 0 q`. -/
@[simp]
theorem stabilizedRotation_one (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v 1 = fromBlocks 0 0 0 q := by simp [stabilizedRotation_def]

/-- At the midpoint `t = 1 / 2`, `stabilizedRotation p q v (1 / 2)` equals the block matrix
`fromBlocks ((1 / 2 : ℝ) • p) ((I / 2) • v.conjTranspose) (-(I / 2) • v) ((1 / 2 : ℝ) • q)`
(which is a star projection under the hypotheses of `isStarProjection_stabilizedRotation`). -/
theorem stabilizedRotation_half (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v (1 / 2) =
      fromBlocks ((1 / 2 : ℝ) • p) ((Complex.I / 2) • v.conjTranspose)
        (-(Complex.I / 2) • v) ((1 / 2 : ℝ) • q) := by
  have hangle : π * (1 / 2 : ℝ) / 2 = π / 4 := by ring
  have hangle2 : π * (1 / 2 : ℝ) = π / 2 := by ring
  have hcos : Real.cos (π / 4) ^ 2 = (1 / 2 : ℝ) := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt zero_le_two]; norm_num
  have hsin : Real.sin (π / 4) ^ 2 = (1 / 2 : ℝ) := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt zero_le_two]; norm_num
  rw [stabilizedRotation_def, hangle, hangle2, hcos, hsin, Real.sin_pi_div_two]
  simp

/-- Continuity of `t ↦ stabilizedRotation p q v t` in operator norm. -/
theorem continuous_stabilizedRotation (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : Continuous (stabilizedRotation p q v) := by
  have hdecomp : stabilizedRotation p q v = fun t : ℝ ↦
      (Real.cos (π * t / 2) ^ 2 : ℝ) • fromBlocks p (0 : CStarMatrix m n A) 0 0 +
      (((Complex.I / 2) * Real.sin (π * t)) •
        fromBlocks (0 : CStarMatrix m m A) v.conjTranspose 0 0 +
      (((-(Complex.I / 2) * Real.sin (π * t)) •
        fromBlocks (0 : CStarMatrix m m A) (0 : CStarMatrix m n A) v 0) +
      (Real.sin (π * t / 2) ^ 2 : ℝ) • fromBlocks (0 : CStarMatrix m m A) 0 0 q)) :=
    funext fun t ↦ by simp [stabilizedRotation_def]
  rw [hdecomp]
  fun_prop

/-- Bundled norm-continuous `Path` in `CStarMatrix (m ⊕ n) (m ⊕ n) A` from `fromBlocks p 0 0 0` to
`fromBlocks 0 0 0 q` defined by `stabilizedRotation p q v`. When `p` and `q` are star projections
satisfying `v.conjTranspose * v = p` and `v * v.conjTranspose = q`, every point on this path is a
star projection (`isStarProjection_stabilizedPath`). -/
def stabilizedPath (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    Path (fromBlocks p (0 : CStarMatrix m n A) 0 0)
      (fromBlocks (0 : CStarMatrix m m A) 0 0 q) where
  toFun t := stabilizedRotation p q v t
  continuous_toFun := (continuous_stabilizedRotation p q v).comp continuous_subtypeVal
  source' := stabilizedRotation_zero p q v
  target' := stabilizedRotation_one p q v

/-- Evaluation of `stabilizedPath` at `t : I` gives `stabilizedRotation` at `(t : ℝ)`. -/
@[simp]
theorem stabilizedPath_apply (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) (t : I) :
    stabilizedPath p q v t = stabilizedRotation p q v t := (rfl)

private theorem exp_I_mul_pi_identities {ζ : ℂ} (t : ℝ)
    (hζ_def : ζ = Complex.exp (Complex.I * (t * π))) :
    1 + (ζ - 1) * (1 / 2 : ℂ) + (star ζ - 1) * (1 / 2 : ℂ) +
        (ζ - 1) * (star ζ - 1) * (1 / 4 : ℂ) = ((Real.cos (π * t / 2) ^ 2 : ℝ) : ℂ) ∧
      -((star ζ - 1) * (1 / 2 : ℂ)) - (ζ - 1) * (star ζ - 1) * (1 / 4 : ℂ) =
        (Complex.I / 2) * (Real.sin (π * t) : ℂ) ∧
      -((ζ - 1) * (1 / 2 : ℂ)) - (ζ - 1) * (star ζ - 1) * (1 / 4 : ℂ) =
        -(Complex.I / 2) * (Real.sin (π * t) : ℂ) ∧
      (ζ - 1) * (star ζ - 1) * (1 / 4 : ℂ) =
        ((Real.sin (π * t / 2) ^ 2 : ℝ) : ℂ) := by
  have hζ : ζ = (Real.cos (π * t) : ℂ) + (Real.sin (π * t) : ℂ) * Complex.I := by
    have harg : Complex.I * (t * π : ℂ) = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hζ_def, harg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hζ_star : star ζ = (Real.cos (π * t) : ℂ) - (Real.sin (π * t) : ℂ) * Complex.I := by
    rw [hζ, star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]; ring
  have hcos_sq : ((Real.cos (π * t / 2) ^ 2 : ℝ) : ℂ) = (1 + (Real.cos (π * t) : ℂ)) / 2 := by
    have h := Real.cos_sq (π * t / 2)
    have htwo_angle : 2 * (π * t / 2) = π * t := by ring
    rw [htwo_angle] at h
    rw [h]; push_cast; ring
  have hsin_sq : ((Real.sin (π * t / 2) ^ 2 : ℝ) : ℂ) = (1 - (Real.cos (π * t) : ℂ)) / 2 := by
    rw [Real.sin_sq, Complex.ofReal_sub, Complex.ofReal_one, hcos_sq]; ring
  have hpyth : (Real.cos (π * t) : ℂ) ^ 2 + (Real.sin (π * t) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (π * t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcos_sq, hζ_star, hζ]
    linear_combination (1 / 4 : ℂ) * hpyth - (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  · rw [hζ_star, hζ]
    linear_combination -(1 / 4 : ℂ) * hpyth +
      (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  · rw [hζ_star, hζ]
    linear_combination -(1 / 4 : ℂ) * hpyth +
      (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  · rw [hsin_sq, hζ_star, hζ]
    linear_combination (1 / 4 : ℂ) * hpyth - (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq

private theorem real_smul_cstarMatrix {m' n' : Type*} (c : ℝ) (M : CStarMatrix m' n' A) :
    c • M = (c : ℂ) • M := by
  rw [← algebraMap_smul ℂ c M, Complex.coe_algebraMap]

section Fintype

variable [Fintype m] [Fintype n] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
  {v : CStarMatrix n m A}

private theorem mul_eq_of_conjTranspose_mul_self
    (hp : IsStarProjection p) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    v * p = v ∧ p * v.conjTranspose = v.conjTranspose ∧
      q * v = v ∧ v.conjTranspose * q = v.conjTranspose := by
  have hvvv : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)
  have hvvv' : v.conjTranspose * v * v.conjTranspose = v.conjTranspose :=
    conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)
  exact ⟨by rw [← hv₁, ← mul_assoc_rectangular, hvvv], by rw [← hv₁, hvvv'],
    by rw [← hv₂, hvvv], by rw [← hv₂, ← mul_assoc_rectangular, hvvv']⟩

/-- When `v` implements a Murray–von Neumann equivalence between `p` and `q`,
`stabilizedProjection p q v` is a star projection in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem isStarProjection_stabilizedProjection (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    IsStarProjection (stabilizedProjection p q v) := by
  obtain ⟨hvp, hpv, hqv, hvq⟩ := mul_eq_of_conjTranspose_mul_self hp hv₁ hv₂
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, stabilizedProjection_def, smul_mul, mul_smul, smul_smul, fromBlocks_mul]
    simp only [CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, hp.isIdempotentElem.eq,
      hq.isIdempotentElem.eq, hv₁, hv₂, hvp, hpv, hqv, hvq, ← two_smul ℝ,
      fromBlocks_smul, smul_neg, smul_smul]
    norm_num
  · rw [isSelfAdjoint_iff, stabilizedProjection_def, star_smul, star_trivial, star_fromBlocks,
      hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, conjTranspose_neg, conjTranspose_neg,
      conjTranspose_conjTranspose]

/-- Left product of `stabilizedProjection p q v` with `fromBlocks p 0 0 0`. -/
theorem stabilizedProjection_mul_fromBlocks
    (hp : IsStarProjection p) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    stabilizedProjection p q v * fromBlocks p 0 0 0 = (1 / 2 : ℝ) • fromBlocks p 0 (-v) 0 := by
  obtain ⟨hvp, -, -, -⟩ := mul_eq_of_conjTranspose_mul_self hp hv₁ hv₂
  rw [stabilizedProjection_def, smul_mul, fromBlocks_mul]; simp [hp.isIdempotentElem.eq, hvp]

/-- Right product of `fromBlocks p 0 0 0` with `stabilizedProjection p q v`. -/
theorem fromBlocks_mul_stabilizedProjection
    (hp : IsStarProjection p) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    fromBlocks p 0 0 0 * stabilizedProjection p q v =
      (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) 0 0 := by
  obtain ⟨-, hpv, -, -⟩ := mul_eq_of_conjTranspose_mul_self hp hv₁ hv₂
  rw [stabilizedProjection_def, mul_smul, fromBlocks_mul]; simp [hp.isIdempotentElem.eq, hpv]

/-- Two-sided compression of `fromBlocks p 0 0 0` by `stabilizedProjection p q v`. -/
theorem stabilizedProjection_mul_fromBlocks_mul
    (hp : IsStarProjection p) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    stabilizedProjection p q v * fromBlocks p 0 0 0 * stabilizedProjection p q v =
      (1 / 4 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := by
  obtain ⟨hvp, hpv, -, -⟩ := mul_eq_of_conjTranspose_mul_self hp hv₁ hv₂
  rw [stabilizedProjection_mul_fromBlocks hp hv₁ hv₂, stabilizedProjection_def, smul_mul, mul_smul,
    smul_smul, fromBlocks_mul]
  simp only [CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, CStarMatrix.zero_mul, add_zero,
    hp.isIdempotentElem.eq, hpv, hvp, hv₂]
  norm_num

/-- In `Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)`, `stabilizedRotation p q v t` is the
unitary conjugate of `fromBlocks p 0 0 0` by `expUnitary ((t * π) • r)` for
`r = stabilizedProjection p q v`. -/
theorem inr_stabilizedRotation_eq_expUnitary_conj [PartialOrder A] [StarOrderedRing A]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (t : ℝ) :
    let u := selfAdjoint.expUnitary ((t * π) •
      ⟨((stabilizedProjection p q v : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)),
        selfAdjoint.mem_iff.mpr (((isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
          (Unitization.inrNonUnitalStarAlgHom ℂ _)).isSelfAdjoint)⟩)
    ((stabilizedRotation p q v t : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (u : Unitization ℂ _) *
        ((fromBlocks p (0 : CStarMatrix m n A) 0 0 : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) * star (u : Unitization ℂ _) := by
  set B := CStarMatrix (m ⊕ n) (m ⊕ n) A
  set r : B := stabilizedProjection p q v
  set x : B := fromBlocks p (0 : CStarMatrix m n A) 0 0
  have hr_inr : IsStarProjection (r : Unitization ℂ B) :=
    (isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
      (Unitization.inrNonUnitalStarAlgHom ℂ B)
  set ζ : ℂ := Complex.exp (Complex.I * (t * π))
  have h_exp : (selfAdjoint.expUnitary ((t * π) •
      ⟨(r : Unitization ℂ B), selfAdjoint.mem_iff.mpr hr_inr.isSelfAdjoint⟩) :
      Unitization ℂ B) = 1 + (ζ - 1) • (r : Unitization ℂ B) := by
    simpa [ζ] using hr_inr.coe_expUnitary_smul (t * π)
  dsimp only
  rw [h_exp, star_add, star_one, star_smul, star_sub, star_one, hr_inr.isSelfAdjoint.star_eq]
  have hexpand :
      (1 + (ζ - 1) • (r : Unitization ℂ B)) * (x : Unitization ℂ B) *
          (1 + (star ζ - 1) • (r : Unitization ℂ B)) =
        ((x + (ζ - 1) • (r * x) + (star ζ - 1) • (x * r) +
          ((ζ - 1) * (star ζ - 1)) • (r * x * r) : B) : Unitization ℂ B) := by
    push_cast
    simp only [add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_assoc, mul_comm (star ζ - 1) (ζ - 1)]; abel
  rw [hexpand]; congr 1
  obtain ⟨hc11, hc12, hc21, hc22⟩ := exp_I_mul_pi_identities (ζ := ζ) t rfl
  dsimp only [B, r, x]
  rw [stabilizedRotation_def, stabilizedProjection_mul_fromBlocks_mul hp hv₁ hv₂,
    stabilizedProjection_mul_fromBlocks hp hv₁ hv₂,
    fromBlocks_mul_stabilizedProjection hp hv₁ hv₂]
  simp only [fromBlocks_smul, fromBlocks_add, smul_zero, smul_neg, add_zero, zero_add,
    fromBlocks_inj, real_smul_cstarMatrix, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, smul_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nth_rw 2 [← one_smul ℂ p]; rw [← add_smul, ← add_smul, ← add_smul, hc11]
  · rw [← neg_smul, ← neg_smul, ← add_smul, ← sub_eq_add_neg, hc12]
  · rw [← neg_smul, ← neg_smul, ← add_smul, ← sub_eq_add_neg, hc21]
  · rw [hc22]

/-- For every `t : ℝ`, `stabilizedRotation p q v t` is a star projection when `p` and `q` are star
projections with `v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
theorem isStarProjection_stabilizedRotation (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (t : ℝ) :
    IsStarProjection (stabilizedRotation p q v t) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set B := CStarMatrix (m ⊕ n) (m ⊕ n) A
  let u := selfAdjoint.expUnitary ((t * π) •
    ⟨((stabilizedProjection p q v : B) : Unitization ℂ B),
      selfAdjoint.mem_iff.mpr (((isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
        (Unitization.inrNonUnitalStarAlgHom ℂ B)).isSelfAdjoint)⟩)
  set x0 : Unitization ℂ B := ((fromBlocks p (0 : CStarMatrix m n A) 0 0 : B) : Unitization ℂ B)
  have hx : IsStarProjection x0 :=
    (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩).map
      (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hconj_proj : IsStarProjection ((u : Unitization ℂ B) * x0 * star (u : Unitization ℂ B)) := by
    simpa using hx.map (Unitary.conjStarAlgAut ℂ (Unitization ℂ B) u)
  rw [← inr_stabilizedRotation_eq_expUnitary_conj hp hq hv₁ hv₂ t] at hconj_proj
  exact ⟨Unitization.inr_injective (R := ℂ)
      (by simpa only [Unitization.inr_mul] using hconj_proj.isIdempotentElem.eq),
    Unitization.inr_injective (R := ℂ)
      (by simpa only [Unitization.inr_star] using hconj_proj.isSelfAdjoint.star_eq)⟩

/-- Every point on `stabilizedPath p q v` is a star projection when `v` implements `p ∼ q`. -/
theorem isStarProjection_stabilizedPath (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (t : I) :
    IsStarProjection (stabilizedPath p q v t) :=
  isStarProjection_stabilizedRotation hp hq hv₁ hv₂ t

/-- **Stabilized homotopy of Murray–von Neumann equivalent projections**: if `p` and `q` are
Murray–von Neumann equivalent over a possibly non-unital C⋆-algebra `A`, then `fromBlocks p 0 0 0`
and `fromBlocks 0 0 0 q` are joined by a norm-continuous path of star projections. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_path (h : MurrayVonNeumannEquiv p q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p (0 : CStarMatrix m n A) 0 0)
        (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q),
      ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨v, hv₁, hv₂⟩ := h.exists_matrix
  exact ⟨stabilizedPath p q v,
    isStarProjection_stabilizedPath h.isStarProjection_left h.isStarProjection_right hv₁ hv₂⟩

/-- **Characterization of Murray–von Neumann equivalence via stabilized homotopy**: star projections
`p : CStarMatrix m m A` and `q : CStarMatrix n n A` over a C⋆-algebra `A` are Murray–von Neumann
equivalent iff `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are joined by a norm-continuous path of
star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_stabilized_path
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv p q ↔
      ∃ γ : Path (fromBlocks p (0 : CStarMatrix m n A) 0 0)
          (fromBlocks (0 : CStarMatrix m m A) 0 0 q),
        ∀ t : I, IsStarProjection (γ t) :=
  ⟨MurrayVonNeumannEquiv.exists_stabilized_path, fun ⟨γ, hγ⟩ ↦
    (MurrayVonNeumannEquiv.pad_zero hp).trans
      ((γ.murrayVonNeumannEquiv_of_isStarProjection hγ).trans
        (hq.murrayVonNeumannEquiv_inrCorner (m := m)).symm)⟩

end Fintype

end RotationPath

end StabilizedHomotopy

end CStarMatrix

end

/-- **Equivalent projections are homotopic after stabilization.** Murray–von Neumann equivalent
matrix projections `p` and `q` over any (possibly non-unital) C⋆-algebra are joined by a continuous
path of projections from `p ⊕ 0` to `0 ⊕ q`. -/
theorem Matrix.IsMurrayVonNeumannEquivalent.exists_path_fromBlocks {A : Type*}
    [NonUnitalCStarAlgebra A] {m n : Type*} [Fintype m] [Fintype n] {p : Matrix m m A}
    {q : Matrix n n A} (h : Matrix.IsMurrayVonNeumannEquivalent p q) :
    ∃ γ : Path (Matrix.fromBlocks p 0 0 0) (Matrix.fromBlocks 0 0 0 q),
      ∀ t, IsStarProjection (γ t) := by
  have h' : CStarMatrix.MurrayVonNeumannEquiv
      (CStarMatrix.ofMatrix p) (CStarMatrix.ofMatrix q) := by
    simpa [CStarMatrix.murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent] using h
  obtain ⟨γ, hγ⟩ := h'.exists_stabilized_path
  have hsymm (M : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
      CStarMatrix.ofMatrixL.symm M = CStarMatrix.ofMatrix.symm M := rfl
  refine ⟨(γ.map CStarMatrix.ofMatrixL.symm.continuous).cast ?_ ?_, fun t ↦
    CStarMatrix.isStarProjection_ofMatrix_symm_iff.2 (hγ t)⟩
  · simp [hsymm]
  · simp [hsymm]
