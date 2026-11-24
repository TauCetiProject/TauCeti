/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian
-- Private: the spectral theorem and the distance to a cone are used only in proofs.
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Convex.Cone.InfDist

/-!
# The cone of positive `(1,1)`-forms

Let `V` be a finite-dimensional real inner product space with an orthogonal almost complex
structure `J`, and represent a two-form by `η ∈ ⋀² V`, `η(u, w) = ⟪η, u ∧ w⟫`. The endomorphism
`J` acts on two-forms as the derivation `D_J (u ∧ w) = J u ∧ w + u ∧ J w`
(`exteriorPower.lieMap 2 J`), and `η` is `J`-invariant, `η(J u, J w) = η(u, w)`, exactly when
`D_J η = 0`. A `J`-invariant two-form is a real `(1,1)`-form, and it is **positive** when
`η(v, J v) ≥ 0` for every `v`. The positive `(1,1)`-forms form a closed pointed convex cone
(`TauCeti.AlmostComplexStructure.positiveCone`) containing the Kähler form `ω` and the complex
lines `v ∧ J v`.

A smooth two-form `Θ` on an almost complex four-manifold defines the current `ζ ↦ ∫ Θ ∧ ζ`, which
is a positive `(1,1)`-current exactly when `Θ` takes values in this cone at every point. In
Taubes's passage from Seiberg–Witten solutions to pseudoholomorphic curves, the normalized
curvature currents are only approximately positive: their pointwise distance to the cone is
controlled by two quantities, the anti-`J`-invariant part of the form and the negative part of its
Hermitian form `B(v, v) = η(v, J v)`. This file proves that distance estimate and writes positive
`(1,1)`-forms as nonnegative combinations of complex lines. The converse estimate, the control of
the norm of a form by its pairing with a two-form `Ω` taming `J` and its distance to the cone, is
in `TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.ComplexLineCone`.

**Distance to the cone.** `D_J` satisfies `D_J³ = -4 D_J` (`lieMap_lieMap_lieMap`), so
`η + D_J² η / 4` is `J`-invariant; it is the `(1,1)`-part of `η`, and `-D_J² η / 4` is its
anti-`J`-invariant part, determined by `⟪D_J² η, u ∧ w⟫ = 2 (η(J u, J w) - η(u, w))`
(`inner_lieMap_lieMap_ιMulti`). Since `D_J` is skew-adjoint and kills `v ∧ J v`, the
anti-`J`-invariant part does not contribute to the Hermitian form (`hermitianForm_lieMap`).
These facts about `D_J` live in `TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic` and
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian`.
Adding `s ω` to the `(1,1)`-part raises the Hermitian form by `s g`. Hence, if
`η(v, J v) ≥ -s ‖v‖²` with `s ≥ 0`, then

`dist(η, positiveCone) ≤ ‖D_J² η‖ / 4 + s ‖ω‖`

(`infDist_positiveCone_le`), in every dimension.

**Positive forms as combinations of complex lines.** For a positive `(1,1)`-form `κ`, the
symmetric operator `T` with `⟪T u, w⟫ = κ(u, J w)` is positive semidefinite, and an orthonormal
eigenbasis `b` of `T` writes `κ = (1 / 2) ∑ᵢ μᵢ bᵢ ∧ J bᵢ` with eigenvalues `μᵢ ≥ 0`: a
nonnegative combination of unit complex lines (`exists_eq_smul_sum_of_mem_positiveCone`). The
norm control of positive `(1,1)`-forms by a taming form `Ω`, and of every two-form `η` by
`c₀ ‖η‖ ≤ ⟪Ω, η⟫ + (‖Ω‖ + c₀) dist(η, positiveCone)`, follows from this decomposition and lives in
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.ComplexLineCone`, where it is derived from
the corresponding statements for the cone of complex lines of an arbitrary almost complex
structure.

**The two-form of a complex-valued covector.** For a real-linear `P : V → ℂ`, the two-form
`Y(u, w) = Im (conj (P u) P w)` is `p₁ ∧ p₂` for the gradients `p₁`, `p₂` of `Re P` and `Im P`
(`ContinuousLinearMap.inner_gradientWedge_ιMulti`). When `P` is `J`-linear, `p₂ = J p₁` and `Y`
is positive; in general `Y` is at distance at most `‖Q‖ (‖P‖ + ‖P - Q‖)` from the cone, where `Q`
is the `J`-antilinear part of `P` (`infDist_positiveCone_le_of_inner_ιMulti_eq_im`). Since the
distance to the cone is subadditive and positively homogeneous, a nonnegative combination
`a F + c Y` is then at distance at most `a dist(F, positiveCone) + c ‖Q‖ (‖P‖ + ‖P - Q‖)`
(`infDist_positiveCone_le_of_inner_ιMulti_eq`). For a section `α` of a Hermitian line with
`P = ∇_a α`, `Y` is the derivative term of the curvature of the cutoff current of Taubes's
analysis.

**Dimension four.** For the complex orientation, a `J`-invariant two-form is `κ = c ω + κ⁻` with
`c = ⟪ω, κ⟫ / 2` and `κ⁻ = (κ - ⋆κ) / 2` anti-self-dual
(`eq_smul_kahlerForm_add_of_lieMap_eq_zero`), and it is positive exactly when `‖κ⁻‖ ≤ √2 c`
(`mem_positiveCone_iff_norm_smul_sub_hodgeStar_le`), by the eigenvalue formula
`TauCeti.AlmostComplexStructure.isLeast_hermitianForm_apply_self`: the positive cone is a round
cone about `ω`.

The Hodge star preserves the cone
(`hodgeStar_mem_positiveCone_iff`), so the positivity of the current `ζ ↦ ∫ Θ ∧ ζ`, whose
representing two-vector is `⋆Θ`, is the positivity of `Θ`, and both have the same distance to the
cone (`infDist_hodgeStar_positiveCone`).

Norms are Hilbert norms on `⋀² V`; they are comparable to the mass norm up to constants depending
only on the dimension.

As in `TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian`, the four-dimensional results
take a positively oriented orthonormal basis `e` with `J e₀ = e₁` and `J e₂ = e₃` as a witness that
the orientation is the complex one.

## Main definitions

* `TauCeti.AlmostComplexStructure.positiveCone J`: the cone of positive `(1,1)`-forms.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter III, §1 (positive forms
  and currents).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Module exteriorPower Metric
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

/-! ### The cone of positive `(1,1)`-forms -/

/-- The **cone of positive `(1,1)`-forms** of `J`: the two-forms `η` that are `J`-invariant,
`D_J η = 0`, and nonnegative on complex lines, `η(v, J v) ≥ 0` for every `v`. -/
def positiveCone (J : AlmostComplexStructure V) : PointedCone ℝ (⋀[ℝ]^2 V) where
  carrier := {η | lieMap 2 J.toLinearMap η = 0 ∧ ∀ v, 0 ≤ ⟪η, ιMulti ℝ 2 ![v, J v]⟫}
  add_mem' := by
    rintro η κ ⟨hη, hη'⟩ ⟨hκ, hκ'⟩
    exact ⟨by rw [map_add, hη, hκ, add_zero], fun v ↦ by
      rw [inner_add_left]; exact add_nonneg (hη' v) (hκ' v)⟩
  zero_mem' := ⟨map_zero _, fun v ↦ by rw [inner_zero_left]⟩
  smul_mem' := by
    rintro ⟨c, hc⟩ η ⟨hη, hη'⟩
    exact ⟨by rw [Nonneg.mk_smul, map_smul, hη, smul_zero], fun v ↦ by
      rw [Nonneg.mk_smul, real_inner_smul_left]; exact mul_nonneg hc (hη' v)⟩

/-- Membership in the cone of positive `(1,1)`-forms. -/
@[simp]
theorem mem_positiveCone {J : AlmostComplexStructure V} {η : ⋀[ℝ]^2 V} :
    η ∈ J.positiveCone ↔
      lieMap 2 J.toLinearMap η = 0 ∧ ∀ v, 0 ≤ ⟪η, ιMulti ℝ 2 ![v, J v]⟫ :=
  Iff.rfl

/-- A `J`-invariant two-form is a positive `(1,1)`-form exactly when its Hermitian part is
positive semidefinite. -/
theorem mem_positiveCone_iff_hermitianForm {J : AlmostComplexStructure V} {η : ⋀[ℝ]^2 V} :
    η ∈ J.positiveCone ↔
      lieMap 2 J.toLinearMap η = 0 ∧ ∀ v, 0 ≤ J.hermitianForm η v v := by
  simp only [mem_positiveCone, hermitianForm_apply_self]

/-- The cone of positive `(1,1)`-forms is closed. -/
theorem isClosed_positiveCone (J : AlmostComplexStructure V) :
    IsClosed (J.positiveCone : Set (⋀[ℝ]^2 V)) := by
  have hD : Continuous (lieMap 2 J.toLinearMap) := LinearMap.continuous_of_finiteDimensional _
  have : (J.positiveCone : Set (⋀[ℝ]^2 V)) = lieMap 2 J.toLinearMap ⁻¹' {0} ∩
      ⋂ v, {η | 0 ≤ ⟪η, ιMulti ℝ 2 ![v, J v]⟫} := by
    ext η
    simp only [SetLike.mem_coe, mem_positiveCone, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_singleton.preimage hD).inter
    (isClosed_iInter fun v ↦ isClosed_le continuous_const (continuous_id.inner continuous_const))

/-- The Kähler form of an orthogonal `J` is a positive `(1,1)`-form. -/
theorem kahlerForm_mem_positiveCone {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) : J.kahlerForm ∈ J.positiveCone :=
  ⟨lieMap_kahlerForm J, fun v ↦ by
    rw [inner_kahlerForm_ιMulti hJ]; exact real_inner_self_nonneg⟩

/-- A complex line `v ∧ J v` is a positive `(1,1)`-form, for an orthogonal `J`. -/
theorem ιMulti_mem_positiveCone {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (v : V) : ιMulti ℝ 2 ![v, J v] ∈ J.positiveCone := by
  refine ⟨lieMap_ιMulti_apply J v, fun w ↦ ?_⟩
  rw [inner_ιMulti_two, hJ, inner_apply_left hJ]
  nlinarith [sq_nonneg ⟪v, w⟫, sq_nonneg ⟪v, J w⟫]

/-- **Distance to the cone of positive `(1,1)`-forms.** For an orthogonal `J`, if
`η(v, J v) ≥ -s ‖v‖²` for every `v`, with `s ≥ 0`, then the distance from `η` to the cone is at
most `‖D_J² η‖ / 4 + s ‖ω‖`: the norm of the anti-`J`-invariant part of `η` plus `‖ω‖` times the
negative part of its Hermitian form. The form `η + D_J² η / 4 + s ω` is positive. -/
theorem infDist_positiveCone_le {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {η : ⋀[ℝ]^2 V} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ v, -(s * ‖v‖ ^ 2) ≤ ⟪η, ιMulti ℝ 2 ![v, J v]⟫) :
    infDist η (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      ‖lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η)‖ / 4 + s * ‖J.kahlerForm‖ := by
  set D := lieMap 2 J.toLinearMap
  set κ := η + (4⁻¹ : ℝ) • D (D η) + s • J.kahlerForm
  have hκ : κ ∈ J.positiveCone := by
    refine ⟨?_, fun v ↦ ?_⟩
    · rw [map_add, lieMap_add_smul_lieMap_lieMap, map_smul, lieMap_kahlerForm J, smul_zero,
        add_zero]
    · have hB := LinearMap.congr_fun₂ (hermitianForm_lieMap hJ (D η)) v v
      rw [hermitianForm_apply_self, LinearMap.zero_apply, LinearMap.zero_apply] at hB
      simp only [κ, inner_add_left, real_inner_smul_left, inner_kahlerForm_ιMulti hJ, hJ,
        real_inner_self_eq_norm_sq]
      linarith [h v]
  calc infDist η (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤ dist η κ := infDist_le_dist_of_mem hκ
    _ = ‖(4⁻¹ : ℝ) • D (D η) + s • J.kahlerForm‖ := by
        rw [dist_eq_norm, ← norm_neg]
        congr 1
        simp only [κ]
        abel
    _ ≤ ‖D (D η)‖ / 4 + s * ‖J.kahlerForm‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num), Real.norm_of_nonneg hs]
        ring

/-! ### Positive `(1,1)`-forms as combinations of complex lines -/

section Orthogonal

variable {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- **A positive `(1,1)`-form is a nonnegative combination of complex lines**:
`κ = (1 / 2) ∑ᵢ μᵢ bᵢ ∧ J bᵢ` with `μᵢ ≥ 0`, for an orthonormal eigenbasis `b` of the symmetric
operator `T` with `⟪T u, w⟫ = κ(u, J w)`. -/
theorem exists_eq_smul_sum_of_mem_positiveCone {κ : ⋀[ℝ]^2 V}
    (hκ : κ ∈ J.positiveCone) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V) (μ : Fin (finrank ℝ V) → ℝ),
      (∀ i, 0 ≤ μ i) ∧ κ = (2⁻¹ : ℝ) • ∑ i, μ i • ιMulti ℝ 2 ![b i, J (b i)] := by
  set T : V →ₗ[ℝ] V := -(J.toLinearMap ∘ₗ twoVectorContraction κ)
  have hT (u w : V) : ⟪T u, w⟫ = ⟪κ, ιMulti ℝ 2 ![u, J w]⟫ := by
    simp only [T, LinearMap.neg_apply, LinearMap.comp_apply, inner_neg_left, inner_apply_left hJ,
      neg_neg, inner_twoVectorContraction_apply]
  have hTs : T.IsSymmetric := fun u w ↦ by
    rw [real_inner_comm (T w) u, hT, hT, ← hermitianForm_apply_of_lieMap_eq_zero hJ hκ.1,
      ← hermitianForm_apply_of_lieMap_eq_zero hJ hκ.1]
    exact (isSymm_hermitianForm J κ).eq u w
  set b := hTs.eigenvectorBasis rfl
  set μ := hTs.eigenvalues rfl
  have hTb (i) : T (b i) = μ i • b i := hTs.apply_eigenvectorBasis rfl i
  -- `κ(a, c) = ∑ᵢ μᵢ ⟪bᵢ, a⟫ ⟪J bᵢ, c⟫`, expanding `⟪T a, -J c⟫` in the eigenbasis.
  have hS (a c : V) : ⟪κ, ιMulti ℝ 2 ![a, c]⟫ = ∑ i, μ i * (⟪b i, a⟫ * ⟪J (b i), c⟫) := by
    calc ⟪κ, ιMulti ℝ 2 ![a, c]⟫ = ⟪T a, -J c⟫ := by rw [hT, map_neg, apply_apply, neg_neg]
      _ = ∑ i, ⟪T a, b i⟫ * ⟪b i, -J c⟫ := (b.sum_inner_mul_inner _ _).symm
      _ = _ := Finset.sum_congr rfl fun i _ ↦ by
        rw [hTs, hTb, real_inner_smul_right, inner_neg_right, ← inner_apply_left hJ,
          real_inner_comm a]
        ring
  refine ⟨b, μ, fun i ↦ ?_, ext_inner_ιMulti_two fun a c ↦ ?_⟩
  · have h := hκ.2 (b i)
    rwa [← hT, hTb, real_inner_smul_left, real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow,
      mul_one] at h
  · have hanti : ⟪κ, ιMulti ℝ 2 ![c, a]⟫ = -⟪κ, ιMulti ℝ 2 ![a, c]⟫ := by
      rw [← inner_twoVectorContraction_apply, ← inner_twoVectorContraction_apply,
        inner_twoVectorContraction_apply_left, real_inner_comm]
    simp only [real_inner_smul_left, sum_inner, inner_ιMulti_two]
    have h1 := hS a c
    have h2 := hS c a
    rw [hanti] at h2
    simp only [mul_sub, Finset.sum_sub_distrib]
    linear_combination (2⁻¹ : ℝ) * h1 - (2⁻¹ : ℝ) * h2

/-! ### The two-form of a complex-valued covector -/

/-- **The two-form `Im (conj (P u) P w)` is nearly a positive `(1,1)`-form.** Let `P` be a
real-linear map `V → ℂ` and `Q` its `J`-antilinear part, in the sense that `P - Q` is `J`-linear
(`TauCeti.IsComplexLinear`), `(P - Q)(J v) = i (P - Q)(v)`. The two-form
`Y(u, w) = Im (conj (P u) P w)` is then at distance at most `‖Q‖ (‖P‖ + ‖P - Q‖)` from the
positive cone. For `Q = 0`, `Y` is the positive form
`p ∧ J p` with `p` the gradient of `Re P`. For a section `α` of a Hermitian line, with `P = ∇_a α`
and `Q = ∂bar_a α`, this is the term `Im (conj ∇_a α ∧ ∇_a α)` of the curvature of the cutoff
current. -/
theorem infDist_positiveCone_le_of_inner_ιMulti_eq_im {P Q : V →L[ℝ] ℂ}
    (hPQ : IsComplexLinear J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ Complex.I)
      ((P - Q : V →L[ℝ] ℂ) : V →ₗ[ℝ] ℂ)) {Y : ⋀[ℝ]^2 V}
    (hY : ∀ u w, ⟪Y, ιMulti ℝ 2 ![u, w]⟫ = (starRingEnd ℂ (P u) * P w).im) :
    infDist Y (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤ ‖Q‖ * (‖P‖ + ‖P - Q‖) := by
  set R := P - Q
  -- The two-vector of the `J`-linear part `R` is `a ∧ J a` with `a` the gradient of `Re R`.
  have hJR : R.imGradient = J R.reGradient := by
    refine ext_inner_right ℝ fun v ↦ ?_
    have hRv : R (J v) = Complex.I * R v := by
      simpa only [ContinuousLinearMap.coe_coe, DistribSMul.toLinearMap_apply, smul_eq_mul]
        using hPQ.apply v
    rw [ContinuousLinearMap.inner_imGradient, inner_apply_left hJ,
      ContinuousLinearMap.inner_reGradient, hRv, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    ring
  have hmem : ιMulti ℝ 2 ![R.reGradient, R.imGradient] ∈ J.positiveCone := by
    rw [hJR]
    exact ιMulti_mem_positiveCone hJ _
  -- `Y - a ∧ J a = p₁ ∧ q₂ + q₁ ∧ r₂`, with `pᵢ`, `qᵢ`, `rᵢ` the gradients of the real and
  -- imaginary parts of `P`, `Q` and `R`.
  have hdiff : Y - ιMulti ℝ 2 ![R.reGradient, R.imGradient] =
      ιMulti ℝ 2 ![P.reGradient, Q.imGradient] + ιMulti ℝ 2 ![Q.reGradient, R.imGradient] := by
    refine ext_inner_ιMulti_two fun u w ↦ ?_
    simp only [R, inner_sub_left, inner_add_left, hY, inner_ιMulti_two,
      ContinuousLinearMap.inner_reGradient, ContinuousLinearMap.inner_imGradient, sub_apply,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
    ring
  calc infDist Y (J.positiveCone : Set (⋀[ℝ]^2 V))
      ≤ dist Y (ιMulti ℝ 2 ![R.reGradient, R.imGradient]) := infDist_le_dist_of_mem hmem
    _ ≤ ‖ιMulti ℝ 2 ![P.reGradient, Q.imGradient]‖ +
          ‖ιMulti ℝ 2 ![Q.reGradient, R.imGradient]‖ := by
        rw [dist_eq_norm, hdiff]
        exact norm_add_le _ _
    _ ≤ ‖P‖ * ‖Q‖ + ‖Q‖ * ‖R‖ := by
        gcongr
        · exact (norm_ιMulti_two_le _ _).trans
            (mul_le_mul P.norm_reGradient_le Q.norm_imGradient_le (norm_nonneg _)
              (norm_nonneg _))
        · exact (norm_ιMulti_two_le _ _).trans
            (mul_le_mul Q.norm_reGradient_le R.norm_imGradient_le (norm_nonneg _)
              (norm_nonneg _))
    _ = ‖Q‖ * (‖P‖ + ‖P - Q‖) := by ring

/-- **The distance to the positive cone of a combination with the two-form of a covector.** Let
`P : V → ℂ` be real-linear and `Q` its `J`-antilinear part, so that `P - Q` is `J`-linear. If a
two-form `Θ` is `a F + c Im (conj (P u) P w)` with `a, c ≥ 0`, then

`dist(Θ, positiveCone) ≤ a dist(F, positiveCone) + c ‖Q‖ (‖P‖ + ‖P - Q‖)`.

For the cutoff current of Taubes's analysis, `a = 1 - χ(|α|²)`, `F = i F_a`, `c = 2 χ'(|α|²)`,
`P = ∇_a α` and `Q = ∂bar_a α`. -/
theorem infDist_positiveCone_le_of_inner_ιMulti_eq {Θ F : ⋀[ℝ]^2 V} {P Q : V →L[ℝ] ℂ} {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hPQ : IsComplexLinear J.toLinearMap (DistribSMul.toLinearMap ℝ ℂ Complex.I)
      ((P - Q : V →L[ℝ] ℂ) : V →ₗ[ℝ] ℂ))
    (hΘ : ∀ u w, ⟪Θ, ιMulti ℝ 2 ![u, w]⟫ =
      a * ⟪F, ιMulti ℝ 2 ![u, w]⟫ + c * (starRingEnd ℂ (P u) * P w).im) :
    infDist Θ (J.positiveCone : Set (⋀[ℝ]^2 V)) ≤
      a * infDist F (J.positiveCone : Set (⋀[ℝ]^2 V)) + c * (‖Q‖ * (‖P‖ + ‖P - Q‖)) := by
  have hΘ' : Θ = a • F + c • P.gradientWedge := ext_inner_ιMulti_two fun u w ↦ by
    rw [hΘ, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      P.inner_gradientWedge_ιMulti]
  rw [hΘ']
  refine (AddSubmonoidClass.infDist_add_le J.positiveCone _ _).trans ?_
  rw [J.positiveCone.infDist_smul ha, J.positiveCone.infDist_smul hc]
  gcongr
  exact infDist_positiveCone_le_of_inner_ιMulti_eq_im hJ hPQ P.inner_gradientWedge_ιMulti

end Orthogonal

/-! ### Dimension four -/

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)
include h₀ h₂ he

/-- **The positive cone in dimension four is a round cone**: a two-form `η` is a positive
`(1,1)`-form exactly when it is `J`-invariant and its anti-self-dual part is bounded by its
`ω`-component, `‖(η - ⋆η) / 2‖ ≤ √2 ⟪ω, η⟫ / 2`. -/
theorem mem_positiveCone_iff_norm_smul_sub_hodgeStar_le {η : ⋀[ℝ]^2 V} :
    η ∈ J.positiveCone ↔ lieMap 2 J.toLinearMap η = 0 ∧
      ‖(2⁻¹ : ℝ) • (η - o.hodgeStar hkl η)‖ ≤ √2 * (⟪J.kahlerForm, η⟫ / 2) := by
  rw [mem_positiveCone, ← add_zero (⟪J.kahlerForm, η⟫ / 2),
    ← forall_le_hermitianForm_apply_self_iff h₀ h₂ hkl he]
  simp only [hermitianForm_apply_self, neg_zero, zero_mul]

/-- **The Hodge star preserves the cone of positive `(1,1)`-forms.** A positive `(1,1)`-form is
`c ω + κ⁻` with `κ⁻` anti-self-dual and `‖κ⁻‖ ≤ √2 c`, and the star only changes the sign of
`κ⁻`. -/
theorem hodgeStar_mem_positiveCone_iff {η : ⋀[ℝ]^2 V} :
    o.hodgeStar hkl η ∈ J.positiveCone ↔ η ∈ J.positiveCone := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hasd (F : ⋀[ℝ]^2 V) :
      (2⁻¹ : ℝ) • (o.hodgeStar hkl F - o.hodgeStar hkl (o.hodgeStar hkl F)) =
        -((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)) := by
    rw [o.hodgeStar_hodgeStar_of_even even_two, ← smul_neg, neg_sub]
  -- The star commutes with `D_J`, since `J` is skew-adjoint, so it preserves `J`-invariance.
  have hD (F : ⋀[ℝ]^2 V) (hF : lieMap 2 J.toLinearMap F = 0) :
      lieMap 2 J.toLinearMap (o.hodgeStar hkl F) = 0 := by
    rw [← o.hodgeStar_lieMap hkl (inner_apply_left hJ), hF, map_zero]
  have hdir (F : ⋀[ℝ]^2 V) (hF : F ∈ J.positiveCone) : o.hodgeStar hkl F ∈ J.positiveCone := by
    rw [mem_positiveCone_iff_norm_smul_sub_hodgeStar_le h₀ h₂ hkl he] at hF ⊢
    refine ⟨hD F hF.1, ?_⟩
    rw [hasd, norm_neg, inner_kahlerForm_hodgeStar h₀ h₂ hkl he]
    exact hF.2
  refine ⟨fun h ↦ ?_, hdir η⟩
  simpa only [o.hodgeStar_hodgeStar_of_even even_two] using hdir _ h

/-- A two-form and its Hodge star have the same distance to the cone of positive `(1,1)`-forms. -/
theorem infDist_hodgeStar_positiveCone (η : ⋀[ℝ]^2 V) :
    infDist (o.hodgeStar hkl η) (J.positiveCone : Set (⋀[ℝ]^2 V)) =
      infDist η (J.positiveCone : Set (⋀[ℝ]^2 V)) := by
  have himage : o.hodgeStar hkl '' (J.positiveCone : Set (⋀[ℝ]^2 V)) = J.positiveCone := by
    ext F
    refine ⟨?_, fun hF ↦ ⟨o.hodgeStar hkl F, ?_, o.hodgeStar_hodgeStar_of_even even_two hkl F⟩⟩
    · rintro ⟨G, hG, rfl⟩
      exact (hodgeStar_mem_positiveCone_iff h₀ h₂ hkl he).2 hG
    · rw [SetLike.mem_coe, hodgeStar_mem_positiveCone_iff h₀ h₂ hkl he]
      exact hF
  have hiso : ⇑(o.hodgeStarIsometry hkl) = o.hodgeStar hkl := funext (o.hodgeStarIsometry_apply hkl)
  conv_lhs => rw [← himage, ← hiso]
  exact infDist_image (o.hodgeStarIsometry hkl).isometry

end Frame


end TauCeti.AlmostComplexStructure
