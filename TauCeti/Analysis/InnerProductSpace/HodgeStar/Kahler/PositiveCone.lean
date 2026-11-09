/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian
-- Private: the negative-part inequality is used only in proofs.
import TauCeti.Algebra.Order.Group.MinMax

/-!
# The cone of positive `(1,1)`-forms and the distance to it

Let `V` be a finite-dimensional real inner product space with an almost complex structure `J`.
A two-vector `F ∈ ⋀² V` represents the two-form `F(v, w) = ⟪F, v ∧ w⟫`. It is of type `(1,1)`
when this form is `J`-invariant, `F(J v, J w) = F(v, w)`; it is **positive** when in addition
`F(v, J v) ≥ 0` for every `v`. For an orthogonal `J` the invariance is the vanishing of the
derivation action `D_J F` of `J` on two-vectors (`exteriorPower.lieMap 2 J`,
`TauCeti.AlmostComplexStructure.forall_inner_ιMulti_apply_eq_iff`); without
orthogonality the two conditions differ, since the form transforms by the adjoint of `J`. The
positive `(1,1)`-forms form a closed pointed cone `TauCeti.AlmostComplexStructure.positiveCone J`,
which contains the Kähler form `ω` when `J` is orthogonal. Every positive form pairs
nonnegatively with `ω`.

Positivity of currents is tested against this cone. In Taubes's passage from Seiberg–Witten
solutions to pseudoholomorphic curves the normalized curvature `iF_a / 2π` of a solution is a
closed two-form that is only approximately positive: its anti-`J`-invariant part and the negative
part of its Hermitian form `F(v, J v)` are small in an integrated sense. The quantity that
measures this is the pointwise distance of the form to the positive cone, and the mass of the
form is controlled by its pairing with a taming form together with this distance. This file
computes that distance and proves the mass control, pointwise in dimension four.

In dimension four, for the complex orientation (witnessed, as in
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic`, by a positively oriented orthonormal
basis `e` with `J e₀ = e₁` and `J e₂ = e₃`), write `c = ⟪ω, F⟫ / 2` and let `F⁻` be the
anti-self-dual part of `F`. The anti-self-dual forms are of type `(1,1)`, and the self-dual
`(1,1)`-forms are the multiples of `ω`. So `F` is of type `(1,1)` exactly when its
*anti-`J`-invariant part* `F - F⁻ - c ω` vanishes
(`TauCeti.AlmostComplexStructure.lieMap_eq_zero_iff`), and positive exactly when moreover
`‖F⁻‖ ≤ √2 c`, that is when the least eigenvalue `λ₋ = c - ‖F⁻‖ / √2` of the Hermitian form of
`F` (`TauCeti.AlmostComplexStructure.isLeast_hermitianForm_apply_self`) is nonnegative. In
these coordinates the positive cone is a circular cone of half-angle `π / 4` around `ω` in
`ℝ ω ⊕ Λ⁻`, and positive forms pair nonnegatively with each other. The distance of an
arbitrary `F` to it is

`dist(F, P)² = ‖F - F⁻ - c ω‖² + min(0, λ₋)² + min(0, λ₊)²`,

where `λ₊ = c + ‖F⁻‖ / √2` is the largest eigenvalue of the Hermitian form. It is the norm of the
anti-`J`-invariant part together with the negative parts of the eigenvalues. Consequently a
lower bound `F(v, J v) ≥ -K ‖v‖²` gives `dist(F, P) ≤ ‖F - F⁻ - c ω‖ + √2 K`.

If a two-form `Ω` tames `J` with constant `ε`, `Ω(v, J v) ≥ ε ‖v‖²`, then `ε ⟪ω, P⟫ ≤ ⟪Ω, P⟫`
on the positive cone, and `‖P‖ ≤ ⟪ω, P⟫` there. Hence every two-form satisfies the mass bound
`ε ‖F‖ ≤ ⟪Ω, F⟫ + (ε + ‖Ω‖) dist(F, P)`.

## Main definitions

* `TauCeti.AlmostComplexStructure.positiveCone J`: the closed cone of positive `(1,1)`-forms.

## Main results

In the namespace `TauCeti.AlmostComplexStructure`:

* `kahlerForm_mem_positiveCone`: `ω` is a positive `(1,1)`-form.
* `inner_kahlerForm_nonneg_of_mem_positiveCone`: positive forms pair nonnegatively with `ω`.
* `mem_positiveCone_iff`: the description of the positive cone in `ℝ ω ⊕ Λ⁻`.
* `norm_le_inner_kahlerForm_of_mem_positiveCone`: `‖P‖ ≤ ⟪ω, P⟫` on the positive cone.
* `inner_nonneg_of_mem_positiveCone`: positive forms pair nonnegatively with each other.
* `mul_inner_kahlerForm_le_inner_of_mem_positiveCone`: a taming form `Ω` with constant `ε`
  satisfies `ε ⟪ω, P⟫ ≤ ⟪Ω, P⟫` on the positive cone.
* `infDist_positiveCone`: the distance to the positive cone.
* `infDist_positiveCone_le`: the distance bound from a lower bound on the Hermitian form.
* `mul_norm_le_inner_add_mul_infDist`: mass control by a taming form and the distance.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter III, §1.
-/

public section

noncomputable section

open Module exteriorPower Metric
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

/-! ### The positive cone -/

/-- The **cone of positive `(1,1)`-forms** of an almost complex structure `J`: the two-vectors
`F` whose form is `J`-invariant, `F(J v, J w) = F(v, w)`, and satisfies
`F(v, J v) = ⟪F, v ∧ J v⟫ ≥ 0` for every `v`. It is a closed pointed cone. -/
def positiveCone (J : AlmostComplexStructure V) : ProperCone ℝ (⋀[ℝ]^2 V) where
  carrier := {F | (∀ v w, ⟪F, ιMulti ℝ 2 ![J v, J w]⟫ = ⟪F, ιMulti ℝ 2 ![v, w]⟫) ∧
    ∀ v, 0 ≤ ⟪F, ιMulti ℝ 2 ![v, J v]⟫}
  add_mem' {F G} hF hG := ⟨fun v w ↦ by rw [inner_add_left, inner_add_left, hF.1, hG.1],
    fun v ↦ by rw [inner_add_left]; exact add_nonneg (hF.2 v) (hG.2 v)⟩
  zero_mem' := ⟨fun v w ↦ by simp, fun v ↦ by simp⟩
  smul_mem' c F hF := ⟨fun v w ↦ by rw [← Nonneg.coe_smul, real_inner_smul_left,
    real_inner_smul_left, hF.1], fun v ↦ by
    rw [← Nonneg.coe_smul, real_inner_smul_left]; exact mul_nonneg c.2 (hF.2 v)⟩
  isClosed' := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun v ↦ isClosed_iInter fun w ↦ isClosed_eq
      (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)).inter
      (isClosed_iInter fun v ↦ isClosed_le continuous_const
        (continuous_id.inner continuous_const))

/-- Membership in the positive cone: the form of `F` is `J`-invariant and `F(v, J v) ≥ 0` for
every `v`. -/
@[simp]
theorem mem_positiveCone {J : AlmostComplexStructure V} {F : ⋀[ℝ]^2 V} :
    F ∈ J.positiveCone ↔ (∀ v w, ⟪F, ιMulti ℝ 2 ![J v, J w]⟫ = ⟪F, ιMulti ℝ 2 ![v, w]⟫) ∧
      ∀ v, 0 ≤ ⟪F, ιMulti ℝ 2 ![v, J v]⟫ :=
  Iff.rfl

/-- **The Kähler form is a positive `(1,1)`-form**, since `ω(v, J v) = ‖J v‖²`. -/
theorem kahlerForm_mem_positiveCone {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) : J.kahlerForm ∈ J.positiveCone :=
  ⟨(forall_inner_ιMulti_apply_eq_iff hJ).2 (lieMap_kahlerForm hJ), fun v ↦ by
    rw [inner_kahlerForm_ιMulti hJ]; exact real_inner_self_nonneg⟩

/-- **Positive forms pair nonnegatively with the Kähler form**: `⟪ω, F⟫ ≥ 0` for `F` in the
positive cone, since `ω` is half the sum of `bᵢ ∧ J bᵢ` over an orthonormal basis `b`. -/
theorem inner_kahlerForm_nonneg_of_mem_positiveCone {J : AlmostComplexStructure V}
    {F : ⋀[ℝ]^2 V} (hF : F ∈ J.positiveCone) : 0 ≤ ⟪J.kahlerForm, F⟫ := by
  rw [kahlerForm_def, real_inner_smul_left, sum_inner]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ ↦ by
    rw [real_inner_comm]; exact hF.2 _)

/-! ### Dimension four -/

/-- In dimension four the Kähler form of an orthogonal `J` has `⟪ω, ω⟫ = 2`. -/
private theorem inner_kahlerForm_self_eq_two [Fact (finrank ℝ V = 4)]
    {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) :
    ⟪J.kahlerForm, J.kahlerForm⟫ = 2 := by
  rw [inner_kahlerForm_self hJ, (Fact.out : finrank ℝ V = 4)]; norm_num

/-- Rotating the coordinates `(c, r)` of `c ω + μ`, with `r = ‖μ‖`, to the eigenvalues `c ∓ r / √2`
of its Hermitian form preserves the squared distance `2 (c - d)² + (r - s)²`. -/
private theorem two_mul_sub_sq_add_sub_sq (c d r s : ℝ) : 2 * (c - d) ^ 2 + (r - s) ^ 2 =
    (c - r / √2 - (d - s / √2)) ^ 2 + (c + r / √2 - (d + s / √2)) ^ 2 := by
  have h : 2 * ((r - s) / √2) ^ 2 = (r - s) ^ 2 := by
    rw [div_pow, Real.sq_sqrt zero_le_two]; ring
  rw [← h]; ring

section Frame

variable [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  {e : OrthonormalBasis (Fin 4) ℝ V} (he : e.toBasis.orientation = o)

include hkl he

variable {J : AlmostComplexStructure V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

include h₀ h₂

/-- **The positive cone in dimension four**: with `F⁻ = μ` the anti-self-dual part of `F`, the
form `F` is a positive `(1,1)`-form iff `F - F⁻ = c ω` and `‖F⁻‖ ≤ √2 c`, where
`c = ⟪ω, F⟫ / 2`, that is iff `F` is `J`-invariant and the least eigenvalue `c - ‖F⁻‖ / √2` of its
Hermitian form is nonnegative. So the positive cone is the circular cone `{c ω + μ | ‖μ‖ ≤ √2 c}` in
`ℝ ω ⊕ Λ⁻`. -/
theorem mem_positiveCone_iff {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) :
    F ∈ J.positiveCone ↔ F - μ = (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm ∧
      ‖μ‖ ≤ √2 * (⟪J.kahlerForm, F⟫ / 2) := by
  have h := forall_le_hermitianForm_apply_self_iff h₀ h₂ hkl he F (C := 0)
  simp only [neg_zero, zero_mul, add_zero, hermitianForm_apply_self,
    o.smul_sub_hodgeStar_eq hkl hμ hF] at h
  rw [mem_positiveCone,
    forall_inner_ιMulti_apply_eq_iff (inner_apply_apply_of_orthonormalBasis h₀ h₂),
    lieMap_eq_zero_iff h₀ h₂ hkl he hμ hF, h]

/-- A positive `(1,1)`-form `F` is `⟪ω, F⟫ / 2 · ω` plus its anti-self-dual part `μ`. -/
private theorem eq_smul_kahlerForm_add_of_mem_positiveCone {F μ : ⋀[ℝ]^2 V}
    (hμ : o.hodgeStar hkl μ = -μ) (hF : o.hodgeStar hkl (F - μ) = F - μ)
    (hP : F ∈ J.positiveCone) : F = (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm + μ := by
  rw [← ((mem_positiveCone_iff hkl he h₀ h₂ hμ hF).1 hP).1]; abel

/-- For anti-self-dual `ν` with `‖ν‖ ≤ √2 c`, the form `c ω + ν` is a positive `(1,1)`-form. -/
private theorem smul_kahlerForm_add_mem_positiveCone {ν : ⋀[ℝ]^2 V}
    (hν : o.hodgeStar hkl ν = -ν) {c : ℝ} (h : ‖ν‖ ≤ √2 * c) :
    c • J.kahlerForm + ν ∈ J.positiveCone := by
  have hinner : ⟪J.kahlerForm, c • J.kahlerForm + ν⟫ / 2 = c := by
    rw [inner_add_right, real_inner_smul_right,
      inner_kahlerForm_self_eq_two (inner_apply_apply_of_orthonormalBasis h₀ h₂),
      inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hν]
    ring
  refine (mem_positiveCone_iff hkl he h₀ h₂ hν ?_).2 ⟨?_, ?_⟩
  · rw [add_sub_cancel_right, map_smul, hodgeStar_kahlerForm h₀ h₂ hkl he]
  · rw [add_sub_cancel_right, hinner]
  · rwa [hinner]

/-- The squared norm of a form split along the orthogonal summands `(ℝ ω)ᗮ ∩ Λ⁺`, `ℝ ω` and
`Λ⁻`. -/
private theorem norm_add_smul_kahlerForm_add_sq {A μ : ⋀[ℝ]^2 V} (hA : o.hodgeStar hkl A = A)
    (hAω : ⟪J.kahlerForm, A⟫ = 0) (hμ : o.hodgeStar hkl μ = -μ) (c : ℝ) :
    ‖A + c • J.kahlerForm + μ‖ ^ 2 = ‖A‖ ^ 2 + 2 * c ^ 2 + ‖μ‖ ^ 2 := by
  have hω : ‖J.kahlerForm‖ ^ 2 = 2 := by
    rw [← real_inner_self_eq_norm_sq,
      inner_kahlerForm_self_eq_two (inner_apply_apply_of_orthonormalBasis h₀ h₂)]
  have hAμ := o.inner_eq_zero_of_hodgeStar_eq_self_of_hodgeStar_eq_neg even_two hkl hA hμ
  have hωμ := inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hμ
  rw [norm_add_sq_real, norm_add_sq_real, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm, hAω, hAμ, hωμ, norm_smul, mul_pow, hω,
    Real.norm_eq_abs, sq_abs]
  ring

/-- The anti-`J`-invariant part `A = F - F⁻ - ⟪ω, F⟫ / 2 · ω` of `F` is self-dual and orthogonal
to `ω`. -/
private theorem hodgeStar_antiInvariantPart {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) :
    o.hodgeStar hkl (F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm) =
        F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm ∧
      ⟪J.kahlerForm, F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm⟫ = 0 := by
  refine ⟨by rw [map_sub, hF, map_smul, hodgeStar_kahlerForm h₀ h₂ hkl he], ?_⟩
  rw [inner_sub_right, inner_sub_right, real_inner_smul_right,
    inner_kahlerForm_self_eq_two (inner_apply_apply_of_orthonormalBasis h₀ h₂),
    inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hμ]
  ring

omit hkl he in
/-- **Positive forms have norm at most their pairing with `ω`**: `‖F‖ ≤ ⟪ω, F⟫` for `F` in the
positive cone. -/
theorem norm_le_inner_kahlerForm_of_mem_positiveCone {F : ⋀[ℝ]^2 V} (hF : F ∈ J.positiveCone) :
    ‖F‖ ≤ ⟪J.kahlerForm, F⟫ := by
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  obtain ⟨o, he⟩ : ∃ o, e.toBasis.orientation = o := ⟨_, rfl⟩
  obtain ⟨μ, hμ, hFμ⟩ := o.exists_hodgeStar_eq_neg_and_hodgeStar_sub_eq even_two hkl F
  have h2 := ((mem_positiveCone_iff hkl he h₀ h₂ hμ hFμ).1 hF).2
  have hn := norm_add_smul_kahlerForm_add_sq hkl he h₀ h₂ (A := 0) (by simp) (by simp) hμ
    (⟪J.kahlerForm, F⟫ / 2)
  rw [zero_add, ← eq_smul_kahlerForm_add_of_mem_positiveCone hkl he h₀ h₂ hμ hFμ hF,
    norm_zero] at hn
  set c := ⟪J.kahlerForm, F⟫ / 2
  have hc : 0 ≤ c := (mul_nonneg_iff_of_pos_left (by positivity)).1 ((norm_nonneg μ).trans h2)
  have hsq : ‖μ‖ ^ 2 ≤ 2 * c ^ 2 := by
    calc ‖μ‖ ^ 2 ≤ (√2 * c) ^ 2 := pow_le_pow_left₀ (norm_nonneg μ) h2 2
      _ = 2 * c ^ 2 := by rw [mul_pow, Real.sq_sqrt zero_le_two]
  have : ‖F‖ ^ 2 ≤ (2 * c) ^ 2 := by nlinarith
  calc ‖F‖ ≤ 2 * c := (pow_le_pow_iff_left₀ (norm_nonneg F) (by linarith) two_ne_zero).1 this
    _ = ⟪J.kahlerForm, F⟫ := by ring

omit hkl he in
/-- **Positive forms pair nonnegatively**: `⟪F, G⟫ ≥ 0` for positive `(1,1)`-forms `F` and `G`.
For `F = a ω + μ` and `G = b ω + ν` this is `2 a b + ⟪μ, ν⟫ ≥ 0`, as `‖μ‖ ≤ √2 a` and
`‖ν‖ ≤ √2 b`. -/
theorem inner_nonneg_of_mem_positiveCone {F G : ⋀[ℝ]^2 V} (hF : F ∈ J.positiveCone)
    (hG : G ∈ J.positiveCone) : 0 ≤ ⟪F, G⟫ := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hω := inner_kahlerForm_self_eq_two hJ
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  obtain ⟨o, he⟩ : ∃ o, e.toBasis.orientation = o := ⟨_, rfl⟩
  obtain ⟨μ, hμ, hFμ⟩ := o.exists_hodgeStar_eq_neg_and_hodgeStar_sub_eq even_two hkl F
  obtain ⟨ν, hν, hGν⟩ := o.exists_hodgeStar_eq_neg_and_hodgeStar_sub_eq even_two hkl G
  have hF2 := ((mem_positiveCone_iff hkl he h₀ h₂ hμ hFμ).1 hF).2
  have hG2 := ((mem_positiveCone_iff hkl he h₀ h₂ hν hGν).1 hG).2
  have hωμ := inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hμ
  have hων := inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hν
  have hFG : ⟪F, G⟫ =
      2 * (⟪J.kahlerForm, F⟫ / 2) * (⟪J.kahlerForm, G⟫ / 2) + ⟪μ, ν⟫ := by
    conv_lhs => rw [eq_smul_kahlerForm_add_of_mem_positiveCone hkl he h₀ h₂ hμ hFμ hF,
      eq_smul_kahlerForm_add_of_mem_positiveCone hkl he h₀ h₂ hν hGν hG]
    have hμω : ⟪μ, J.kahlerForm⟫ = 0 := by rw [real_inner_comm]; exact hωμ
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hω,
      hων, hμω]
    ring
  set a := ⟪J.kahlerForm, F⟫ / 2
  set b := ⟪J.kahlerForm, G⟫ / 2
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hprod : ‖μ‖ * ‖ν‖ ≤ 2 * a * b := by
    calc ‖μ‖ * ‖ν‖ ≤ (√2 * a) * (√2 * b) :=
          mul_le_mul hF2 hG2 (norm_nonneg ν) ((norm_nonneg μ).trans hF2)
      _ = 2 * a * b := by rw [mul_mul_mul_comm, hss, mul_assoc]
  rw [hFG]
  linarith [neg_abs_le ⟪μ, ν⟫, abs_real_inner_le_norm μ ν]

omit hkl he in
/-- **A taming form controls the pairing with `ω` on the positive cone**: if
`Ω(v, J v) ≥ ε ‖v‖²` for every `v`, then `ε ⟪ω, F⟫ ≤ ⟪Ω, F⟫` for every positive `(1,1)`-form
`F`. -/
theorem mul_inner_kahlerForm_le_inner_of_mem_positiveCone {Ω F : ⋀[ℝ]^2 V} {ε : ℝ}
    (hΩ : ∀ v, ε * ‖v‖ ^ 2 ≤ ⟪Ω, ιMulti ℝ 2 ![v, J v]⟫) (hF : F ∈ J.positiveCone) :
    ε * ⟪J.kahlerForm, F⟫ ≤ ⟪Ω, F⟫ := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  obtain ⟨o, he⟩ : ∃ o, e.toBasis.orientation = o := ⟨_, rfl⟩
  obtain ⟨ν, hν, hΩν⟩ := o.exists_hodgeStar_eq_neg_and_hodgeStar_sub_eq even_two hkl Ω
  obtain ⟨μ, hμ, hFμ⟩ := o.exists_hodgeStar_eq_neg_and_hodgeStar_sub_eq even_two hkl F
  set c := ⟪J.kahlerForm, Ω⟫ / 2 with hc
  -- The `(1,1)`-part of `Ω - ε ω` is positive.
  set G := ν + (c - ε) • J.kahlerForm
  have hG : G ∈ J.positiveCone := by
    refine ⟨(forall_inner_ιMulti_apply_eq_iff hJ).2 (by
      rw [map_add, map_smul, lieMap_of_hodgeStar_eq_neg h₀ h₂ hkl he hν,
        lieMap_kahlerForm hJ, smul_zero, add_zero]), fun v ↦ ?_⟩
    have h := hΩ v
    rw [← hermitianForm_apply_self, hermitianForm_apply_eq h₀ h₂ hkl he,
      o.smul_sub_hodgeStar_eq hkl hν hΩν, real_inner_self_eq_norm_sq, ← hc] at h
    rw [inner_add_left, real_inner_smul_left, inner_kahlerForm_ιMulti hJ,
      inner_apply_apply_of_orthonormalBasis h₀ h₂, real_inner_self_eq_norm_sq]
    linarith
  -- The anti-`J`-invariant part of `Ω` is orthogonal to `F`.
  obtain ⟨hA, hAω⟩ := hodgeStar_antiInvariantPart hkl he h₀ h₂ hν hΩν
  rw [← hc] at hA hAω
  have hAF : ⟪Ω - ν - c • J.kahlerForm, F⟫ = 0 := by
    rw [eq_smul_kahlerForm_add_of_mem_positiveCone hkl he h₀ h₂ hμ hFμ hF, inner_add_right,
      real_inner_smul_right, real_inner_comm J.kahlerForm, hAω, mul_zero, zero_add]
    exact o.inner_eq_zero_of_hodgeStar_eq_self_of_hodgeStar_eq_neg even_two hkl hA hμ
  have hGF := inner_nonneg_of_mem_positiveCone h₀ h₂ hG hF
  have hΩF : ⟪Ω, F⟫ = ⟪Ω - ν - c • J.kahlerForm, F⟫ + ⟪G, F⟫ + ε * ⟪J.kahlerForm, F⟫ := by
    simp only [G, inner_sub_left, inner_add_left, real_inner_smul_left]
    ring
  linarith

omit hkl he in
/-- **A taming form controls the norm on the positive cone**: if `Ω(v, J v) ≥ ε ‖v‖²` for every
`v`, with `ε ≥ 0`, then `ε ‖F‖ ≤ ⟪Ω, F⟫` for every positive `(1,1)`-form `F`. -/
theorem mul_norm_le_inner_of_mem_positiveCone {Ω F : ⋀[ℝ]^2 V} {ε : ℝ} (hε : 0 ≤ ε)
    (hΩ : ∀ v, ε * ‖v‖ ^ 2 ≤ ⟪Ω, ιMulti ℝ 2 ![v, J v]⟫) (hF : F ∈ J.positiveCone) :
    ε * ‖F‖ ≤ ⟪Ω, F⟫ :=
  (mul_le_mul_of_nonneg_left (norm_le_inner_kahlerForm_of_mem_positiveCone h₀ h₂ hF)
    hε).trans (mul_inner_kahlerForm_le_inner_of_mem_positiveCone h₀ h₂ hΩ hF)

/-- For `G = c' ω + ν` with anti-self-dual `ν`, the squared distance from `F` splits along
`(ℝ ω)ᗮ ∩ Λ⁺`, `ℝ ω` and `Λ⁻`: it is `‖A‖² + 2 (c - c')² + ‖F⁻ - ν‖²`, where `c = ⟪ω, F⟫ / 2` and
`A = F - F⁻ - c ω` is the anti-`J`-invariant part of `F`. -/
private theorem dist_smul_kahlerForm_add_sq {F μ ν : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) (hν : o.hodgeStar hkl ν = -ν) (c' : ℝ) :
    dist F (c' • J.kahlerForm + ν) ^ 2 =
      ‖F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm‖ ^ 2 +
        2 * (⟪J.kahlerForm, F⟫ / 2 - c') ^ 2 + ‖μ - ν‖ ^ 2 := by
  obtain ⟨hA, hAω⟩ := hodgeStar_antiInvariantPart hkl he h₀ h₂ hμ hF
  have hμν : o.hodgeStar hkl (μ - ν) = -(μ - ν) := by rw [map_sub, hμ, hν]; abel
  rw [dist_eq_norm, show F - (c' • J.kahlerForm + ν) =
      (F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm) +
        (⟪J.kahlerForm, F⟫ / 2 - c') • J.kahlerForm + (μ - ν) by rw [sub_smul]; abel]
  exact norm_add_smul_kahlerForm_add_sq hkl he h₀ h₂ hA hAω hμν _

/-- The upper bound for `infDist_positiveCone`: the positive form `c' ω + (r' / r) F⁻` whose
Hermitian form has the eigenvalues `max(0, c ∓ ‖F⁻‖ / √2)` realizes the distance. -/
private theorem infDist_positiveCone_le_sqrt {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) :
    infDist F (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      √(‖F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm‖ ^ 2 +
        min 0 (⟪J.kahlerForm, F⟫ / 2 - ‖μ‖ / √2) ^ 2 +
        min 0 (⟪J.kahlerForm, F⟫ / 2 + ‖μ‖ / √2) ^ 2) := by
  have hs : (0 : ℝ) < √2 := by positivity
  set c := ⟪J.kahlerForm, F⟫ / 2
  set r := ‖μ‖
  -- The nearest point `c' ω + (r' / r) μ` has eigenvalues `u = max(0, c - r / √2)` and
  -- `w = max(0, c + r / √2)`, that is `c' = (u + w) / 2` and `r' / √2 = (w - u) / 2`.
  set u := max (c - r / √2) 0
  set w := max (c + r / √2) 0
  have hrs : 0 ≤ r / √2 := div_nonneg (norm_nonneg μ) hs.le
  have hu : 0 ≤ u := le_max_right _ _
  have huw : u ≤ w := max_le_max (by linarith) le_rfl
  have hwu : w - u ≤ 2 * (r / √2) := by
    have h := abs_max_sub_max_le_abs (c + r / √2) (c - r / √2) 0
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - u),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ c + r / √2 - (c - r / √2))] at h
    linarith
  set c' := (u + w) / 2
  set r' := √2 * ((w - u) / 2)
  have hr's : r' / √2 = (w - u) / 2 := by simp only [r']; field_simp
  have hr' : 0 ≤ r' := mul_nonneg hs.le (by linarith)
  have hr'r : r' ≤ r := by
    calc r' ≤ √2 * (r / √2) := mul_le_mul_of_nonneg_left (by linarith) hs.le
      _ = r := by field_simp
  have hr'0 : r = 0 → r' = 0 := fun h ↦ le_antisymm (h ▸ hr'r) hr'
  have hνG : o.hodgeStar hkl ((r' / r) • μ) = -((r' / r) • μ) := by rw [map_smul, hμ, smul_neg]
  have hnormG : ‖(r' / r) • μ‖ = r' := by
    rcases eq_or_ne r 0 with h | h
    · rw [hr'0 h, zero_div, zero_smul, norm_zero]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr' (norm_nonneg μ)),
        div_mul_cancel₀ _ h]
  have hnorm : ‖μ - (r' / r) • μ‖ = r - r' := by
    rcases eq_or_ne r 0 with h | h
    · rw [hr'0 h, h, norm_eq_zero.1 h, smul_zero, sub_zero, norm_zero, sub_zero]
    · rw [show μ - (r' / r) • μ = (1 - r' / r) • μ by rw [sub_smul, one_smul], norm_smul,
        Real.norm_eq_abs, abs_of_nonneg, sub_mul, one_mul, div_mul_cancel₀ _ h]
      rw [sub_nonneg, div_le_one (lt_of_le_of_ne (norm_nonneg μ) (Ne.symm h))]
      exact hr'r
  have hG : c' • J.kahlerForm + (r' / r) • μ ∈ J.positiveCone :=
    smul_kahlerForm_add_mem_positiveCone hkl he h₀ h₂ hνG (by
      rw [hnormG]
      exact mul_le_mul_of_nonneg_left (by linarith [show c' = (u + w) / 2 from rfl]) hs.le)
  have hdist : dist F (c' • J.kahlerForm + (r' / r) • μ) ^ 2 =
      ‖F - μ - c • J.kahlerForm‖ ^ 2 + 2 * (c - c') ^ 2 + ‖μ - (r' / r) • μ‖ ^ 2 :=
    dist_smul_kahlerForm_add_sq hkl he h₀ h₂ hμ hF hνG c'
  refine (infDist_le_dist_of_mem hG).trans_eq ?_
  rw [← Real.sqrt_sq dist_nonneg, hdist, hnorm, add_assoc, two_mul_sub_sq_add_sub_sq c c' r r',
    ← add_assoc]
  have hu' : c - r / √2 - (c' - r' / √2) = min 0 (c - r / √2) := by
    rw [hr's, show c' - (w - u) / 2 = u by ring]
    rcases le_total 0 (c - r / √2) with h | h <;> simp [u, h]
  have hw' : c + r / √2 - (c' + r' / √2) = min 0 (c + r / √2) := by
    rw [hr's, show c' + (w - u) / 2 = w by ring]
    rcases le_total 0 (c + r / √2) with h | h <;> simp [w, h]
  rw [hu', hw']

/-- The lower bound for `infDist_positiveCone`: every positive `(1,1)`-form `G` lies at distance at
least `√(‖F - F⁻ - c ω‖² + min(0, c - ‖F⁻‖ / √2)² + min(0, c + ‖F⁻‖ / √2)²)` from `F`. -/
private theorem sqrt_le_dist_of_mem_positiveCone {F μ G : ⋀[ℝ]^2 V}
    (hμ : o.hodgeStar hkl μ = -μ) (hF : o.hodgeStar hkl (F - μ) = F - μ)
    (hG : G ∈ J.positiveCone) :
    √(‖F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm‖ ^ 2 +
        min 0 (⟪J.kahlerForm, F⟫ / 2 - ‖μ‖ / √2) ^ 2 +
        min 0 (⟪J.kahlerForm, F⟫ / 2 + ‖μ‖ / √2) ^ 2) ≤ dist F G := by
  have hs : (0 : ℝ) < √2 := by positivity
  obtain ⟨ν, hν, hGν⟩ := o.exists_hodgeStar_eq_neg_and_hodgeStar_sub_eq even_two hkl G
  have h2 := ((mem_positiveCone_iff hkl he h₀ h₂ hν hGν).1 hG).2
  have hd := dist_smul_kahlerForm_add_sq hkl he h₀ h₂ hμ hF hν (⟪J.kahlerForm, G⟫ / 2)
  rw [← eq_smul_kahlerForm_add_of_mem_positiveCone hkl he h₀ h₂ hν hGν hG] at hd
  rw [← Real.sqrt_sq dist_nonneg, hd]
  refine Real.sqrt_le_sqrt ?_
  set c := ⟪J.kahlerForm, F⟫ / 2
  set d := ⟪J.kahlerForm, G⟫ / 2
  have hμν : (‖μ‖ - ‖ν‖) ^ 2 ≤ ‖μ - ν‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_norm_sub_norm_le μ ν) 2
  have key := two_mul_sub_sq_add_sub_sq c d ‖μ‖ ‖ν‖
  have hu : 0 ≤ d - ‖ν‖ / √2 := by rw [sub_nonneg, div_le_iff₀' hs]; exact h2
  have hw : 0 ≤ d + ‖ν‖ / √2 := by linarith [div_nonneg (norm_nonneg ν) hs.le]
  linarith [sq_le_sq.2 (abs_min_zero_le_abs_sub (a := c - ‖μ‖ / √2) hu),
    sq_le_sq.2 (abs_min_zero_le_abs_sub (a := c + ‖μ‖ / √2) hw)]

/-- **The distance to the positive cone**: with `F⁻ = μ` the anti-self-dual part of `F` and
`c = ⟪ω, F⟫ / 2`, the distance from `F` to the cone of positive `(1,1)`-forms is
`√(‖F - F⁻ - c ω‖² + min(0, c - ‖F⁻‖ / √2)² + min(0, c + ‖F⁻‖ / √2)²)`. Here `F - F⁻ - c ω` is the
anti-`J`-invariant part of `F`, and `c ∓ ‖F⁻‖ / √2` are the extreme eigenvalues of its Hermitian
form. -/
theorem infDist_positiveCone {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) :
    infDist F (J.positiveCone : Set (⋀[ℝ]^2 V)) =
      √(‖F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm‖ ^ 2 +
        min 0 (⟪J.kahlerForm, F⟫ / 2 - ‖μ‖ / √2) ^ 2 +
        min 0 (⟪J.kahlerForm, F⟫ / 2 + ‖μ‖ / √2) ^ 2) :=
  le_antisymm (infDist_positiveCone_le_sqrt hkl he h₀ h₂ hμ hF)
    ((le_infDist J.positiveCone.nonempty).2 fun _ hG ↦
      sqrt_le_dist_of_mem_positiveCone hkl he h₀ h₂ hμ hF hG)

/-- **The distance to the positive cone is controlled by the negative part of the Hermitian
form**: with `F⁻ = μ` the anti-self-dual part of `F`, if `F(v, J v) ≥ -K ‖v‖²` for every `v`, with
`K ≥ 0`, then the distance from `F` to the positive cone is at most
`‖F - F⁻ - ⟪ω, F⟫ / 2 · ω‖ + √2 K`, the norm of the anti-`J`-invariant part plus `√2 K`. -/
theorem infDist_positiveCone_le {F μ : ⋀[ℝ]^2 V} (hμ : o.hodgeStar hkl μ = -μ)
    (hF : o.hodgeStar hkl (F - μ) = F - μ) {K : ℝ} (hK₀ : 0 ≤ K)
    (hK : ∀ v, -K * ‖v‖ ^ 2 ≤ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) :
    infDist F (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      ‖F - μ - (⟪J.kahlerForm, F⟫ / 2) • J.kahlerForm‖ + √2 * K := by
  rw [infDist_positiveCone hkl he h₀ h₂ hμ hF]
  set c := ⟪J.kahlerForm, F⟫ / 2 with hc
  set a := ‖F - μ - c • J.kahlerForm‖
  -- The least eigenvalue `c - ‖μ‖ / √2` is at least `-K`, hence so is the largest.
  have hs : (0 : ℝ) < √2 := by positivity
  have hle := norm_smul_sub_hodgeStar_le_of_forall_le_hermitianForm_apply_self h₀ h₂ hkl he F
    (C := K) (by simpa only [hermitianForm_apply_self] using hK)
  rw [o.smul_sub_hodgeStar_eq hkl hμ hF] at hle
  rw [← hc] at hle
  have h₁ : -K ≤ c - ‖μ‖ / √2 := by
    have : ‖μ‖ / √2 ≤ c + K := by rw [div_le_iff₀ hs]; linarith [mul_comm (√2) (c + K)]
    linarith
  have h₂' : -K ≤ c + ‖μ‖ / √2 := by linarith [div_nonneg (norm_nonneg μ) hs.le]
  have hm (l : ℝ) (hl : -K ≤ l) : min 0 l ^ 2 ≤ K ^ 2 :=
    (sq_le_sq.2 (abs_min_zero_le_abs_sub (b := l + K) (by linarith))).trans_eq (by ring)
  have hss : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [hm _ h₁, hm _ h₂', norm_nonneg (F - μ - c • J.kahlerForm),
    mul_nonneg (mul_nonneg hs.le hK₀) (norm_nonneg (F - μ - c • J.kahlerForm))]

omit hkl he in
/-- **Mass control by a taming form and the distance to the positive cone**: if
`Ω(v, J v) ≥ ε ‖v‖²` for every `v`, with `ε ≥ 0`, then every two-form `F` satisfies
`ε ‖F‖ ≤ ⟪Ω, F⟫ + (ε + ‖Ω‖) · dist(F, P)`, where `P` is the cone of positive `(1,1)`-forms. -/
theorem mul_norm_le_inner_add_mul_infDist {Ω : ⋀[ℝ]^2 V} {ε : ℝ} (hε : 0 ≤ ε)
    (hΩ : ∀ v, ε * ‖v‖ ^ 2 ≤ ⟪Ω, ιMulti ℝ 2 ![v, J v]⟫) (F : ⋀[ℝ]^2 V) :
    ε * ‖F‖ ≤ ⟪Ω, F⟫ + (ε + ‖Ω‖) * infDist F (J.positiveCone : Set (⋀[ℝ]^2 V)) := by
  obtain ⟨G, hG, hd⟩ := J.positiveCone.isClosed.exists_infDist_eq_dist J.positiveCone.nonempty F
  have hGn := mul_norm_le_inner_of_mem_positiveCone h₀ h₂ hε hΩ hG
  rw [hd, dist_eq_norm]
  have h1 : ‖F‖ ≤ ‖G‖ + ‖F - G‖ := norm_le_norm_add_norm_sub' F G
  have h2 : ⟪Ω, G⟫ ≤ ⟪Ω, F⟫ + ‖Ω‖ * ‖F - G‖ := by
    have := real_inner_le_norm Ω (G - F)
    rw [inner_sub_right, norm_sub_rev] at this
    linarith
  nlinarith

end Frame

end TauCeti.AlmostComplexStructure
