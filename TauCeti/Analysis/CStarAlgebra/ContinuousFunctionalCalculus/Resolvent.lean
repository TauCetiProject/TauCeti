/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Algebra.Algebra.StrictPositivity
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Algebra.Algebra.Spectrum

/-!
# The resolvent in the continuous functional calculus

For an element `a` satisfying the predicate of a continuous functional calculus and a point `z` of
its resolvent set, the function `w ↦ (z - w)⁻¹` is continuous on the spectrum of `a`, and its
functional calculus is the resolvent `(z - a)⁻¹`. Likewise, for a self-adjoint `a` and a real `k`
with `1 + k a` invertible, `a (1 + k a)⁻¹` is the image of `a` under the fractional linear function
`x ↦ x / (1 + k x)`.

For an element `h` of a nonunital C⋆-algebra `A` and a real scale `c`, the resolvent cutoff
`TauCeti.CStarAlgebra.resolventApproxAt h c` is `cfcₙ (fun t : ℝ => t * (t + c)⁻¹) h`, with
sequential specialization
`TauCeti.CStarAlgebra.resolventApprox h n = resolventApproxAt h ((n : ℝ) + 1)⁻¹`. When `0 ≤ h` and
`0 < c`, it embeds into the unitization `A⁺¹` as `(h : A⁺¹) * Ring.inverse ((h : A⁺¹) + c • 1)`
(`TauCeti.CStarAlgebra.inr_resolventApproxAt`) and agrees with
`cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹) (c⁻¹ • h)`
(`TauCeti.CStarAlgebra.resolventApproxAt_eq_cfcₙ_one_sub`).

## Main results

* `TauCeti.continuousOn_inv_sub_of_mem_resolventSet`: `w ↦ (z - w)⁻¹` is continuous on the
  spectrum of `a` for `z` in the resolvent set of `a`.
* `TauCeti.continuousOn_add_inv_quasispectrum`: `t ↦ (t + c)⁻¹` is continuous on the
  quasispectrum of a nonnegative element `h` for `0 < c`.
* `TauCeti.cfc_inv_sub_eq_resolvent`: `cfc (fun w ↦ (z - w)⁻¹) a = resolvent a z` for `z` in the
  resolvent set of `a`.
* `IsSelfAdjoint.cfc_div_one_add_mul`: `cfc (fun x ↦ x / (1 + k x)) a = a (1 + k a)⁻¹` when
  `1 + k a` is invertible.
* `TauCeti.CStarAlgebra.resolventApproxAt` and `TauCeti.CStarAlgebra.resolventApprox`: resolvent
  cutoffs at scale `c : ℝ` and `((n : ℝ) + 1)⁻¹` (`resolventApproxAt_def`, `resolventApprox_def`,
  `resolventApprox_eq_cfcₙ`), together with self-adjointness (`isSelfAdjoint_resolventApproxAt`),
  homomorphism transport (`map_resolventApproxAt`), positivity (`resolventApproxAt_nonneg`), strict
  contractive norm bound (`norm_resolventApproxAt_lt_one`), antitone dependence on `c`
  (`antitoneOn_resolventApproxAt`) and monotonicity in `n` (`monotone_resolventApprox`), algebraic
  identity (`resolventApproxAt_mul_self_add_smul`), unitization embedding
  (`inr_resolventApproxAt`, `inr_resolventApprox`), and norm bound
  `‖resolventApproxAt h c * h - h‖ ≤ c` (`norm_resolventApproxAt_mul_self_sub_le`,
  `norm_resolventApprox_mul_self_sub_le`).

## References

* B. Blackadar, *Operator Algebras*, II.4.2.4.
* G. K. Pedersen, *C⋆-Algebras and Their Automorphism Groups*, §3.10.
-/

public section

namespace TauCeti

/-- For `z` in the resolvent set of `a`, the function `w ↦ (z - w)⁻¹` is continuous on the
spectrum of `a`, since `z - w` does not vanish there. -/
theorem continuousOn_inv_sub_of_mem_resolventSet {R A : Type*} [Field R] [TopologicalSpace R]
    [IsTopologicalRing R] [ContinuousInv₀ R] [Ring A] [Algebra R A] {a : A} {z : R}
    (hz : z ∈ resolventSet R a) : ContinuousOn (fun w ↦ (z - w)⁻¹) (spectrum R a) :=
  (continuousOn_const.sub continuousOn_id).inv₀ fun w hw h0 =>
    hw ((sub_eq_zero.mp h0 : z = w) ▸ hz)

/-- For `0 ≤ h` and `0 < c`, the shifted inverse `t ↦ (t + c)⁻¹` is continuous on
`quasispectrum R h`. -/
theorem continuousOn_add_inv_quasispectrum {R A : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [TopologicalSpace R] [ContinuousAdd R] [ContinuousInv₀ R]
    [NonUnitalRing A] [PartialOrder A] [Module R A] [NonnegSpectrumClass R A]
    {h : A} (hh : 0 ≤ h) {c : R} (hc : 0 < c) :
    ContinuousOn (fun t : R => (t + c)⁻¹) (quasispectrum R h) :=
  (continuousOn_id.add continuousOn_const).inv₀ fun t ht =>
    (add_pos_of_nonneg_of_pos (quasispectrum_nonneg_of_nonneg h hh t ht) hc).ne'

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalRing R] [ContinuousStar R] [ContinuousInv₀ R] [TopologicalSpace A] [Ring A]
  [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- **The resolvent through the functional calculus.** For `z` in the resolvent set of
`a`, the functional calculus of `w ↦ (z - w)⁻¹` at `a` is the resolvent `(z - a)⁻¹`. -/
theorem cfc_inv_sub_eq_resolvent {a : A} {z : R} (hz : z ∈ resolventSet R a)
    (ha : p a := by cfc_tac) : cfc (fun w ↦ (z - w)⁻¹) a = resolvent a z := by
  have hne : ∀ w ∈ spectrum R a, z - w ≠ 0 := fun w hw h0 =>
    hw ((sub_eq_zero.mp h0 : z = w) ▸ hz)
  rw [cfc_inv (fun w ↦ z - w) a hne, cfc_sub (fun _ ↦ z) (fun w ↦ w) a, cfc_const z a,
    cfc_id' R a, resolvent]

end TauCeti

namespace IsSelfAdjoint

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A}

/-- For a self-adjoint `a` with `1 + k a` invertible, `a (1 + k a)⁻¹` is the image of `a` under the
fractional linear function `x ↦ x / (1 + k x)`. -/
theorem cfc_div_one_add_mul (ha : IsSelfAdjoint a) {k : ℝ} (hk : IsUnit (1 + k • a)) :
    cfc (fun x : ℝ ↦ x / (1 + k * x)) a = a * Ring.inverse (1 + k • a) := by
  have hne := spectrum.isUnit_one_add_smul_iff.1 hk
  simp_rw [div_eq_mul_inv]
  rw [cfc_mul (fun x : ℝ ↦ x) (fun x ↦ (1 + k * x)⁻¹) a,
    cfc_inv (fun x : ℝ ↦ 1 + k * x) a hne]
  simp [cfc_id' ℝ a, cfc_const_add 1 (fun x : ℝ ↦ k * x) a, cfc_const_mul_id k a]

end IsSelfAdjoint

section Resolvent

open Unitization
open scoped ComplexOrder NNReal CStarAlgebra

namespace TauCeti.CStarAlgebra

/-- The resolvent cutoff `h * (h + c)⁻¹` at real scale `c` attached to an element `h` of a
nonunital C⋆-algebra, defined for general `h` via the real nonunital continuous functional calculus
as `cfcₙ (fun t : ℝ => t * (t + c)⁻¹) h`. When `0 ≤ h` and `0 < c`, it embeds in the unitization
`A⁺¹` as `(h : A⁺¹) * Ring.inverse ((h : A⁺¹) + c • 1)` (`inr_resolventApproxAt`). -/
noncomputable def resolventApproxAt {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (c : ℝ) : A :=
  cfcₙ (fun t : ℝ => t * (t + c)⁻¹) h

/-- Unfolding formula for `resolventApproxAt`. -/
theorem resolventApproxAt_def {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (c : ℝ) :
    resolventApproxAt h c = cfcₙ (fun t : ℝ => t * (t + c)⁻¹) h :=
  (rfl)

@[simp, grind =]
theorem resolventApproxAt_zero {A : Type*} [NonUnitalCStarAlgebra A] (c : ℝ) :
    resolventApproxAt (0 : A) c = 0 :=
  cfcₙ_apply_zero

@[simp, grind .]
theorem isSelfAdjoint_resolventApproxAt {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (c : ℝ) :
    IsSelfAdjoint (resolventApproxAt h c) :=
  IsSelfAdjoint.cfcₙ

@[simp]
instance instIsStarNormalResolventApproxAt {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (c : ℝ) :
    IsStarNormal (resolventApproxAt h c) :=
  (isSelfAdjoint_resolventApproxAt h c).isStarNormal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem continuousOn_mul_add_inv_quasispectrum {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (fun t : ℝ => t * (t + c)⁻¹) (quasispectrum ℝ h) :=
  continuousOn_id.mul (TauCeti.continuousOn_add_inv_quasispectrum hh hc)

/-- Nonunital star-algebra homomorphisms commute with `resolventApproxAt` on nonnegative
elements for positive scales. -/
@[simp]
theorem map_resolventApproxAt {B F : Type*} [NonUnitalCStarAlgebra B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    f (resolventApproxAt h c) = resolventApproxAt (f h) c :=
  NonUnitalStarAlgHomClass.map_cfcₙ f (fun t : ℝ => t * (t + c)⁻¹) h
    (continuousOn_mul_add_inv_quasispectrum hh hc) (by simp) (map_continuous f)
    hh.isSelfAdjoint (hh.isSelfAdjoint.map f)

/-- For `0 ≤ h` and `0 < c`, `resolventApproxAt h c` agrees with
`cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹)` at `c⁻¹ • h`, connecting the resolvent formula to Mathlib's
operator-monotone contraction. -/
theorem resolventApproxAt_eq_cfcₙ_one_sub {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    resolventApproxAt h c = cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹) (c⁻¹ • h) := by
  have hc_inv : 0 < c⁻¹ := inv_pos.mpr hc
  have hsh : 0 ≤ c⁻¹ • h := smul_nonneg hc_inv.le hh
  rw [cfcₙ_nnreal_eq_real _ _ hsh]
  have hcongr1 : cfcₙ (fun x : ℝ => ((1 - (1 + x.toNNReal)⁻¹ : ℝ≥0) : ℝ)) (c⁻¹ • h) =
      cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) (c⁻¹ • h) := by
    refine cfcₙ_congr fun x hx => ?_
    have hx₀ : 0 ≤ x := quasispectrum_nonneg_of_nonneg _ hsh x hx
    have hle : (1 + x.toNNReal)⁻¹ ≤ (1 : ℝ≥0) := inv_le_one_of_one_le₀ (by simp)
    simp [NNReal.coe_sub hle, Real.coe_toNNReal x hx₀]
  rw [hcongr1, ← cfcₙ_comp_smul c⁻¹ (fun x : ℝ => 1 - (1 + x)⁻¹) h ?_ (by simp) hh.isSelfAdjoint]
  · refine cfcₙ_congr fun t ht => ?_
    have ht₀ : 0 ≤ t := quasispectrum_nonneg_of_nonneg h hh t ht
    have : t + c ≠ 0 := by positivity
    have : 1 + c⁻¹ * t ≠ 0 := by positivity
    dsimp only [smul_eq_mul]
    field_simp
    ring
  · refine continuousOn_const.sub (ContinuousOn.inv₀ (by fun_prop) ?_)
    rintro _ ⟨t, ht, rfl⟩
    have ht₀ : 0 ≤ t := quasispectrum_nonneg_of_nonneg h hh t ht
    have hmul : 0 ≤ c⁻¹ * t := mul_nonneg hc_inv.le ht₀
    dsimp only [smul_eq_mul]
    linarith

theorem resolventApproxAt_nonneg {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    0 ≤ resolventApproxAt h c := by
  rw [resolventApproxAt_eq_cfcₙ_one_sub hh hc]
  exact cfcₙ_nonneg_of_predicate

theorem norm_resolventApproxAt_lt_one {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    ‖resolventApproxAt h c‖ < 1 := by
  rw [resolventApproxAt_eq_cfcₙ_one_sub hh hc]
  exact norm_cfcₙ_one_sub_one_add_inv_lt_one _

/-- For `0 ≤ h`, `resolventApproxAt h` is antitone on `(0, ∞)`. -/
theorem antitoneOn_resolventApproxAt {h : A} (hh : 0 ≤ h) :
    AntitoneOn (resolventApproxAt h) (Set.Ioi 0) := by
  intro c₁ hc₁ c₂ hc₂ hle
  rw [resolventApproxAt_eq_cfcₙ_one_sub hh hc₂, resolventApproxAt_eq_cfcₙ_one_sub hh hc₁]
  have h1 : 0 ≤ c₁⁻¹ • h := smul_nonneg (inv_pos.mpr hc₁).le hh
  have h2 : 0 ≤ c₂⁻¹ • h := smul_nonneg (inv_pos.mpr hc₂).le hh
  have hsmul : c₂⁻¹ • h ≤ c₁⁻¹ • h := by
    rw [← sub_nonneg, ← sub_smul]
    exact smul_nonneg (sub_nonneg.mpr (inv_anti₀ hc₁ hle)) hh
  exact CFC.monotoneOn_one_sub_one_add_inv h2 h1 hsmul

theorem resolventApproxAt_le_inv_smul {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    resolventApproxAt h c ≤ c⁻¹ • h := by
  have hcont := continuousOn_mul_add_inv_quasispectrum hh hc
  rw [resolventApproxAt, ← cfcₙ_const_mul_id c⁻¹ h hh.isSelfAdjoint]
  refine cfcₙ_mono (fun t ht => ?_) hcont (by fun_prop) (by simp) (by simp)
  have ht₀ : 0 ≤ t := quasispectrum_nonneg_of_nonneg h hh t ht
  have hpos : 0 < t + c := by positivity
  have hmul : c⁻¹ * t * (t + c) = c⁻¹ * t ^ 2 + t := by field_simp
  rw [← div_eq_mul_inv, div_le_iff₀ hpos, hmul]
  linarith [mul_nonneg (inv_pos.mpr hc).le (sq_nonneg t)]

/-- Algebraic resolvent identity in `A`: `(h (h + c)⁻¹) h + c • (h (h + c)⁻¹) = h` for
`0 ≤ h` and `0 < c`. -/
theorem resolventApproxAt_mul_self_add_smul {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    resolventApproxAt h c * h + c • resolventApproxAt h c = h := by
  let g : ℝ → ℝ := fun t => t * (t + c)⁻¹
  have hg : ContinuousOn g (quasispectrum ℝ h) := continuousOn_mul_add_inv_quasispectrum hh hc
  rw [resolventApproxAt]
  nth_rw 2 [← cfcₙ_id' ℝ h hh.isSelfAdjoint]
  rw [← cfcₙ_mul g (fun t : ℝ => t) h hg (by simp [g]) (by fun_prop) (by simp),
    ← cfcₙ_smul c g h hg (by simp [g]),
    ← cfcₙ_add (fun x => g x * x) (fun x => c • g x) h
      (hg.mul continuousOn_id) (by simp [g]) (by fun_prop) (by simp [g])]
  conv_rhs => rw [← cfcₙ_id' ℝ h hh.isSelfAdjoint]
  refine cfcₙ_congr fun t ht => ?_
  have ht₀ : 0 ≤ t := quasispectrum_nonneg_of_nonneg h hh t ht
  have : t + c ≠ 0 := by positivity
  dsimp only [g, smul_eq_mul]
  field_simp

omit [PartialOrder A] [StarOrderedRing A] in
theorem commute_resolventApproxAt_self (h : A) (c : ℝ) :
    Commute (resolventApproxAt h c) h := by
  by_cases hh : IsSelfAdjoint h
  · simpa only [resolventApproxAt, cfcₙ_id' ℝ h hh] using
      cfcₙ_commute_cfcₙ (fun t : ℝ => t * (t + c)⁻¹) (fun t : ℝ => t) h
  · simp [resolventApproxAt, cfcₙ_apply_of_not_predicate h hh]

/-- Resolvent approximation bound: `‖resolventApproxAt h c * h - h‖ ≤ c`. -/
theorem norm_resolventApproxAt_mul_self_sub_le {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    ‖resolventApproxAt h c * h - h‖ ≤ c := by
  have heq : resolventApproxAt h c * h - h = -(c • resolventApproxAt h c) := by
    rw [eq_sub_iff_add_eq.mpr (resolventApproxAt_mul_self_add_smul hh hc)]
    abel
  rw [heq, norm_neg, norm_smul, Real.norm_of_nonneg hc.le]
  exact mul_le_of_le_one_right hc.le (norm_resolventApproxAt_lt_one hh hc).le

private theorem add_ne_zero_of_mem_spectrum_inr {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c)
    {t : ℝ} (ht : t ∈ spectrum ℝ (h : A⁺¹)) : t + c ≠ 0 := by
  have : 0 ≤ t := spectrum_nonneg_of_nonneg (Unitization.inr_nonneg ℂ h hh) ht
  positivity

/-- In the unitization `A⁺¹`, `resolventApproxAt h c` embeds as
`(h : A⁺¹) * Ring.inverse ((h : A⁺¹) + c • 1)` for `0 ≤ h` and `0 < c`. -/
theorem inr_resolventApproxAt {h : A} (hh : 0 ≤ h) {c : ℝ} (hc : 0 < c) :
    ((resolventApproxAt h c : A) : A⁺¹) =
      (h : A⁺¹) * Ring.inverse ((h : A⁺¹) + c • (1 : A⁺¹)) := by
  have hh' : 0 ≤ (h : A⁺¹) := Unitization.inr_nonneg ℂ h hh
  have hne : ∀ t ∈ spectrum ℝ (h : A⁺¹), t + c ≠ 0 :=
    fun _ ht => add_ne_zero_of_mem_spectrum_inr hh hc ht
  have hcont : ContinuousOn (fun t : ℝ => (t + c)⁻¹) (spectrum ℝ (h : A⁺¹)) :=
    ContinuousOn.inv₀ (by fun_prop) hne
  rw [resolventApproxAt, Unitization.real_cfcₙ_eq_cfc_inr h _,
    cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + c)⁻¹) (h : A⁺¹) (by fun_prop) hcont,
    cfc_id' ℝ (h : A⁺¹) hh'.isSelfAdjoint,
    cfc_inv (fun t : ℝ => t + c) (h : A⁺¹) hne (by fun_prop) hh'.isSelfAdjoint,
    cfc_add_const c (fun t : ℝ => t) (h : A⁺¹) (by fun_prop) hh'.isSelfAdjoint,
    cfc_id' ℝ (h : A⁺¹) hh'.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

/-- The resolvent sequence `resolventApproxAt h ((n : ℝ) + 1)⁻¹` attached to an element `h` of a
nonunital C⋆-algebra, defined for general `h` as
`cfcₙ (fun t : ℝ => t * (t + ((n : ℝ) + 1)⁻¹)⁻¹) h`. When `0 ≤ h`, it embeds in `A⁺¹` as
`(h : A⁺¹) * Ring.inverse ((h : A⁺¹) + ((n : ℝ) + 1)⁻¹ • 1)` (`inr_resolventApprox`), and when `h`
is strictly positive it is a monotone sequential increasing approximate unit of `A`. -/
noncomputable def resolventApprox {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (n : ℕ) : A :=
  resolventApproxAt h ((n : ℝ) + 1)⁻¹

/-- Unfolding formula for `resolventApprox` in terms of `resolventApproxAt`. -/
theorem resolventApprox_def {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (n : ℕ) :
    resolventApprox h n = resolventApproxAt h ((n : ℝ) + 1)⁻¹ :=
  (rfl)

/-- Nonunital continuous functional calculus formula for `resolventApprox`. -/
theorem resolventApprox_eq_cfcₙ {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (n : ℕ) :
    resolventApprox h n = cfcₙ (fun t : ℝ => t * (t + ((n : ℝ) + 1)⁻¹)⁻¹) h :=
  (rfl)

@[simp, grind =]
theorem resolventApprox_zero {A : Type*} [NonUnitalCStarAlgebra A] (n : ℕ) :
    resolventApprox (0 : A) n = 0 :=
  resolventApproxAt_zero _

@[simp, grind .]
theorem isSelfAdjoint_resolventApprox {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (n : ℕ) :
    IsSelfAdjoint (resolventApprox h n) :=
  isSelfAdjoint_resolventApproxAt h _

@[simp]
instance instIsStarNormalResolventApprox {A : Type*} [NonUnitalCStarAlgebra A] (h : A) (n : ℕ) :
    IsStarNormal (resolventApprox h n) :=
  instIsStarNormalResolventApproxAt h _

/-- Nonunital star-algebra homomorphisms commute with `resolventApprox` on nonnegative elements. -/
@[simp]
theorem map_resolventApprox {B F : Type*} [NonUnitalCStarAlgebra B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) {h : A} (hh : 0 ≤ h) (n : ℕ) :
    f (resolventApprox h n) = resolventApprox (f h) n :=
  map_resolventApproxAt f hh (by positivity)

/-- For `0 ≤ h`, `resolventApprox h n` agrees with `cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹)` at
`((n : ℝ) + 1) • h`, connecting the resolvent formula to Mathlib's operator-monotone contraction. -/
theorem resolventApprox_eq_cfcₙ_one_sub {h : A} (hh : 0 ≤ h) (n : ℕ) :
    resolventApprox h n = cfcₙ (fun x : ℝ≥0 => 1 - (1 + x)⁻¹) (((n : ℝ) + 1) • h) := by
  rw [resolventApprox_def]
  simpa using resolventApproxAt_eq_cfcₙ_one_sub hh (c := ((n : ℝ) + 1)⁻¹) (by positivity)

theorem resolventApprox_nonneg {h : A} (hh : 0 ≤ h) (n : ℕ) : 0 ≤ resolventApprox h n :=
  resolventApproxAt_nonneg hh (by positivity)

theorem norm_resolventApprox_lt_one {h : A} (hh : 0 ≤ h) (n : ℕ) :
    ‖resolventApprox h n‖ < 1 :=
  norm_resolventApproxAt_lt_one hh (by positivity)

/-- For `0 ≤ h`, `resolventApprox h` is monotone in `n`. -/
theorem monotone_resolventApprox {h : A} (hh : 0 ≤ h) : Monotone (resolventApprox h) :=
  fun _ _ hmn => antitoneOn_resolventApproxAt hh (Set.mem_Ioi.mpr (by positivity))
    (Set.mem_Ioi.mpr (by positivity)) (inv_anti₀ (by positivity) (by gcongr))

theorem resolventApprox_le_smul {h : A} (hh : 0 ≤ h) (n : ℕ) :
    resolventApprox h n ≤ ((n : ℝ) + 1) • h := by
  rw [resolventApprox_def]
  simpa using resolventApproxAt_le_inv_smul hh (c := ((n : ℝ) + 1)⁻¹) (by positivity)

/-- Algebraic resolvent identity in `A`: `(h (h + c)⁻¹) h + c • (h (h + c)⁻¹) = h` for
`c = ((n : ℝ) + 1)⁻¹`. -/
theorem resolventApprox_mul_self_add_smul {h : A} (hh : 0 ≤ h) (n : ℕ) :
    resolventApprox h n * h + ((n : ℝ) + 1)⁻¹ • resolventApprox h n = h :=
  resolventApproxAt_mul_self_add_smul hh (by positivity)

omit [PartialOrder A] [StarOrderedRing A] in
theorem commute_resolventApprox_self (h : A) (n : ℕ) :
    Commute (resolventApprox h n) h :=
  commute_resolventApproxAt_self h _

/-- Resolvent approximation bound: `‖resolventApprox h n * h - h‖ ≤ ((n : ℝ) + 1)⁻¹`. -/
theorem norm_resolventApprox_mul_self_sub_le {h : A} (hh : 0 ≤ h) (n : ℕ) :
    ‖resolventApprox h n * h - h‖ ≤ ((n : ℝ) + 1)⁻¹ :=
  norm_resolventApproxAt_mul_self_sub_le hh (by positivity)

/-- In the unitization `A⁺¹`, `resolventApprox h n` embeds as
`(h : A⁺¹) * Ring.inverse ((h : A⁺¹) + ((n : ℝ) + 1)⁻¹ • 1)` for `0 ≤ h`. -/
theorem inr_resolventApprox {h : A} (hh : 0 ≤ h) (n : ℕ) :
    ((resolventApprox h n : A) : A⁺¹) =
      (h : A⁺¹) * Ring.inverse ((h : A⁺¹) + ((n : ℝ) + 1)⁻¹ • (1 : A⁺¹)) :=
  inr_resolventApproxAt hh (by positivity)

end TauCeti.CStarAlgebra

end Resolvent
