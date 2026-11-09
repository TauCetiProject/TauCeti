/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian
-- Private: the existence of a unitary frame is used only in proofs.
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

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
Hermitian form `B(v, v) = η(v, J v)`. Conversely, a two-form `Ω` taming `J` controls the norm of
a form by its pairing with `Ω` and its distance to the cone. These are the two pointwise
estimates of this file.

**Distance to the cone.** `D_J` satisfies `D_J³ = -4 D_J` (`lieMap_lieMap_lieMap`), so
`η + D_J² η / 4` is `J`-invariant; it is the `(1,1)`-part of `η`, and `-D_J² η / 4` is its
anti-`J`-invariant part, determined by `⟪D_J² η, u ∧ w⟫ = 2 (η(J u, J w) - η(u, w))`
(`inner_lieMap_lieMap_ιMulti`). Since `D_J` is skew-adjoint and kills `v ∧ J v`, the
anti-`J`-invariant part does not contribute to the Hermitian form (`hermitianForm_lieMap`).
Adding `s ω` to the `(1,1)`-part raises the Hermitian form by `s g`. Hence, if
`η(v, J v) ≥ -s ‖v‖²` with `s ≥ 0`, then

`dist(η, positiveCone) ≤ ‖D_J² η‖ / 4 + s ‖ω‖`

(`infDist_positiveCone_le`), in every dimension.

**Norm control by a taming form.** In dimension four, for the complex orientation, a
`J`-invariant two-form is `κ = c ω + κ⁻` with `c = ⟪ω, κ⟫ / 2` and `κ⁻ = (κ - ⋆κ) / 2`
anti-self-dual (`eq_smul_kahlerForm_add_of_lieMap_eq_zero`), and it is positive exactly when
`‖κ⁻‖ ≤ √2 c` (`mem_positiveCone_iff_norm_smul_sub_hodgeStar_le`), by the eigenvalue formula
`TauCeti.AlmostComplexStructure.isLeast_hermitianForm_apply_self`: the positive cone is a round
cone about `ω`. Consequently:

* a positive `(1,1)`-form has norm at most its pairing with `ω`, `‖κ‖ ≤ ⟪ω, κ⟫`
  (`norm_le_inner_kahlerForm_of_mem_positiveCone`);
* positive `(1,1)`-forms pair nonnegatively with every two-form `Ω` that is nonnegative on complex
  lines, `Ω(v, J v) ≥ 0` (`inner_nonneg_of_mem_positiveCone`); if `Ω(v, J v) ≥ c₀ ‖v‖²` then
  `c₀ ‖κ‖ ≤ ⟪Ω, κ⟫` for `c₀ ≥ 0` (`mul_norm_le_inner_of_mem_positiveCone`);
* for every two-form `η`,
  `c₀ ‖η‖ ≤ ⟪Ω, η⟫ + (‖Ω‖ + c₀) dist(η, positiveCone)`
  (`mul_norm_le_inner_add_mul_infDist_positiveCone`).

Integrated over a tube, the last inequality bounds the mass of an approximately positive closed
current by its pairing with a closed taming form, which is a topological quantity, plus its
integrated distance to the positive cone. The Hodge star preserves the cone
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

/-! ### The derivation action of `J` on two-vectors -/

/-- `D_J² (u ∧ w) = 2 (J u ∧ J w) - 2 (u ∧ w)`. -/
theorem lieMap_lieMap_ιMulti (J : AlmostComplexStructure V) (u w : V) :
    lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap (ιMulti ℝ 2 ![u, w])) =
      (2 : ℝ) • ιMulti ℝ 2 ![J u, J w] - (2 : ℝ) • ιMulti ℝ 2 ![u, w] := by
  refine ext_inner_ιMulti_two fun a b ↦ ?_
  simp only [lieMap_two_apply_ιMulti, map_add, inner_add_left, inner_sub_left,
    real_inner_smul_left, inner_ιMulti_two, apply_apply, inner_neg_left]
  ring

/-- **`D_J³ = -4 D_J` on two-vectors.** Hence `D_J² / 4` is minus the projection onto the
anti-`J`-invariant two-vectors, the `-4`-eigenspace of `D_J²`, and `η + D_J² η / 4` is the
`J`-invariant part of `η`. -/
theorem lieMap_lieMap_lieMap (J : AlmostComplexStructure V) (η : ⋀[ℝ]^2 V) :
    lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η)) =
      -(4 : ℝ) • lieMap 2 J.toLinearMap η := by
  set D := lieMap 2 J.toLinearMap
  have key : D ∘ₗ D ∘ₗ D = -(4 : ℝ) • D := by
    refine linearMap_ext_inner_ιMulti_two fun a b u w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, D]
    rw [lieMap_lieMap_ιMulti]
    simp only [map_sub, map_smul, lieMap_two_apply_ιMulti, inner_add_left, inner_sub_left,
      real_inner_smul_left, inner_ιMulti_two, apply_apply, inner_neg_left]
    ring
  exact LinearMap.congr_fun key η

/-- The two-form `η + D_J² η / 4` is `J`-invariant. -/
theorem lieMap_add_smul_lieMap_lieMap (J : AlmostComplexStructure V) (η : ⋀[ℝ]^2 V) :
    lieMap 2 J.toLinearMap
        (η + (4⁻¹ : ℝ) • lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η)) = 0 := by
  rw [map_add, map_smul, lieMap_lieMap_lieMap, smul_smul]
  norm_num

/-- The anti-`J`-invariant part of a two-form, read on pairs of vectors:
`⟪D_J² η, u ∧ w⟫ = 2 (η(J u, J w) - η(u, w))` for an orthogonal `J`. -/
theorem inner_lieMap_lieMap_ιMulti {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (η : ⋀[ℝ]^2 V) (u w : V) :
    ⟪lieMap 2 J.toLinearMap (lieMap 2 J.toLinearMap η), ιMulti ℝ 2 ![u, w]⟫ =
      2 * (⟪η, ιMulti ℝ 2 ![J u, J w]⟫ - ⟪η, ιMulti ℝ 2 ![u, w]⟫) := by
  rw [inner_lieMap_left (inner_apply_left hJ), inner_lieMap_left (inner_apply_left hJ), neg_neg,
    lieMap_lieMap_ιMulti, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  ring

/-- `D_J (v ∧ J w) + D_J (w ∧ J v) = 0`. -/
private theorem lieMap_ιMulti_add_lieMap_ιMulti (J : AlmostComplexStructure V) (v w : V) :
    lieMap 2 J.toLinearMap (ιMulti ℝ 2 ![v, J w]) +
      lieMap 2 J.toLinearMap (ιMulti ℝ 2 ![w, J v]) = 0 := by
  refine ext_inner_ιMulti_two fun a b ↦ ?_
  simp only [lieMap_two_apply_ιMulti, inner_add_left, inner_ιMulti_two, inner_zero_left,
    apply_apply, inner_neg_left]
  ring

/-- **The anti-`J`-invariant part of a two-form has zero Hermitian part**: `B(D_J ξ) = 0` for an
orthogonal `J`, because `D_J` is skew-adjoint. -/
theorem hermitianForm_lieMap {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (ξ : ⋀[ℝ]^2 V) : J.hermitianForm (lieMap 2 J.toLinearMap ξ) = 0 := by
  ext v w
  rw [hermitianForm_apply, inner_lieMap_left (inner_apply_left hJ),
    inner_lieMap_left (inner_apply_left hJ), ← neg_add, ← inner_add_right,
    lieMap_ιMulti_add_lieMap_ιMulti, inner_zero_right, neg_zero, zero_div, LinearMap.zero_apply,
    LinearMap.zero_apply]

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
  ⟨lieMap_kahlerForm hJ, fun v ↦ by
    rw [inner_kahlerForm_ιMulti hJ]; exact real_inner_self_nonneg⟩

/-- A complex line `v ∧ J v` is a positive `(1,1)`-form, for an orthogonal `J`. -/
theorem ιMulti_mem_positiveCone {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (v : V) : ιMulti ℝ 2 ![v, J v] ∈ J.positiveCone := by
  refine ⟨?_, fun w ↦ ?_⟩
  · rw [lieMap_two_apply_ιMulti]
    refine ext_inner_ιMulti_two fun a b ↦ ?_
    simp only [inner_add_left, inner_ιMulti_two, inner_zero_left, apply_apply, inner_neg_left]
    ring
  · rw [inner_ιMulti_two, hJ, inner_apply_left hJ]
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
    · rw [map_add, lieMap_add_smul_lieMap_lieMap, map_smul, lieMap_kahlerForm hJ, smul_zero,
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

/-! ### Dimension four -/

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)
include h₀ h₂ he

/-- **A `J`-invariant two-form is a multiple of `ω` plus an anti-self-dual form**: for
`D_J η = 0`, `η = (⟪ω, η⟫ / 2) ω + (η - ⋆η) / 2`. -/
theorem eq_smul_kahlerForm_add_of_lieMap_eq_zero {η : ⋀[ℝ]^2 V}
    (hη : lieMap 2 J.toLinearMap η = 0) :
    η = (⟪J.kahlerForm, η⟫ / 2) • J.kahlerForm + (2⁻¹ : ℝ) • (η - o.hodgeStar hkl η) := by
  set p := (2⁻¹ : ℝ) • (η + o.hodgeStar hkl η)
  set m := (2⁻¹ : ℝ) • (η - o.hodgeStar hkl η)
  have hp : o.hodgeStar hkl p = p := o.hodgeStar_smul_add_hodgeStar even_two hkl η
  have hm : o.hodgeStar hkl m = -m := o.hodgeStar_smul_sub_hodgeStar even_two hkl η
  have hpm : p + m = η := by simp only [p, m]; module
  -- The self-dual part `p` is `J`-invariant, as `η` and its anti-self-dual part are.
  have hDp : lieMap 2 J.toLinearMap p = 0 := by
    have h := congrArg (lieMap 2 J.toLinearMap) hpm
    rwa [map_add, lieMap_of_hodgeStar_eq_neg h₀ h₂ hkl he hm, add_zero, hη] at h
  have h2 := lieMap_lieMap_of_hodgeStar_eq_self h₀ h₂ hkl he hp
  rw [hDp, map_zero] at h2
  have hω : ⟪J.kahlerForm, p⟫ = ⟪J.kahlerForm, η⟫ := by
    rw [← hpm, inner_add_right, inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he hm,
      add_zero]
  rw [hω] at h2
  calc η = p + m := hpm.symm
    _ = _ := by
      congr 1
      linear_combination (norm := module) (4⁻¹ : ℝ) • h2

/-- A two-form `F` is nonnegative on complex lines exactly when `‖(F - ⋆F) / 2‖ ≤ √2 ⟪ω, F⟫ / 2`:
the case `C = 0` of `forall_le_hermitianForm_apply_self_iff`. -/
private theorem forall_inner_ιMulti_nonneg_iff (F : ⋀[ℝ]^2 V) :
    (∀ v, 0 ≤ ⟪F, ιMulti ℝ 2 ![v, J v]⟫) ↔
      ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤ √2 * (⟪J.kahlerForm, F⟫ / 2) := by
  rw [← add_zero (⟪J.kahlerForm, F⟫ / 2), ← forall_le_hermitianForm_apply_self_iff h₀ h₂ hkl he]
  simp only [hermitianForm_apply_self, neg_zero, zero_mul]

/-- **The positive cone in dimension four is a round cone**: a two-form `η` is a positive
`(1,1)`-form exactly when it is `J`-invariant and its anti-self-dual part is bounded by its
`ω`-component, `‖(η - ⋆η) / 2‖ ≤ √2 ⟪ω, η⟫ / 2`. -/
theorem mem_positiveCone_iff_norm_smul_sub_hodgeStar_le {η : ⋀[ℝ]^2 V} :
    η ∈ J.positiveCone ↔ lieMap 2 J.toLinearMap η = 0 ∧
      ‖(2⁻¹ : ℝ) • (η - o.hodgeStar hkl η)‖ ≤ √2 * (⟪J.kahlerForm, η⟫ / 2) := by
  rw [mem_positiveCone, forall_inner_ιMulti_nonneg_iff h₀ h₂ hkl he]

/-- **The Hodge star preserves the cone of positive `(1,1)`-forms.** A positive `(1,1)`-form is
`c ω + κ⁻` with `κ⁻` anti-self-dual and `‖κ⁻‖ ≤ √2 c`, and the star only changes the sign of
`κ⁻`. -/
theorem hodgeStar_mem_positiveCone_iff {η : ⋀[ℝ]^2 V} :
    o.hodgeStar hkl η ∈ J.positiveCone ↔ η ∈ J.positiveCone := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hω (F : ⋀[ℝ]^2 V) : ⟪J.kahlerForm, o.hodgeStar hkl F⟫ = ⟪J.kahlerForm, F⟫ :=
    o.inner_hodgeStar_right_of_hodgeStar_eq_self even_two hkl (hodgeStar_kahlerForm h₀ h₂ hkl he) F
  have hasd (F : ⋀[ℝ]^2 V) :
      (2⁻¹ : ℝ) • (o.hodgeStar hkl F - o.hodgeStar hkl (o.hodgeStar hkl F)) =
        -((2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)) := by
    rw [o.hodgeStar_hodgeStar_of_even even_two, ← smul_neg, neg_sub]
  -- The star of a `J`-invariant form `c ω + κ⁻` is `c ω - κ⁻`, again `J`-invariant.
  have hD (F : ⋀[ℝ]^2 V) (hF : lieMap 2 J.toLinearMap F = 0) :
      lieMap 2 J.toLinearMap (o.hodgeStar hkl F) = 0 := by
    have hm := o.hodgeStar_smul_sub_hodgeStar even_two hkl F
    rw [eq_smul_kahlerForm_add_of_lieMap_eq_zero h₀ h₂ hkl he hF, map_add, map_smul,
      hodgeStar_kahlerForm h₀ h₂ hkl he, hm, map_add, map_smul, map_neg, lieMap_kahlerForm hJ,
      lieMap_of_hodgeStar_eq_neg h₀ h₂ hkl he hm, neg_zero, smul_zero, add_zero]
  have hdir (F : ⋀[ℝ]^2 V) (hF : F ∈ J.positiveCone) : o.hodgeStar hkl F ∈ J.positiveCone := by
    rw [mem_positiveCone_iff_norm_smul_sub_hodgeStar_le h₀ h₂ hkl he] at hF ⊢
    refine ⟨hD F hF.1, ?_⟩
    rw [hasd, norm_neg, hω]
    exact hF.2
  refine ⟨fun h ↦ ?_, hdir η⟩
  simpa only [o.hodgeStar_hodgeStar_of_even even_two] using hdir _ h

/-- A two-form and its Hodge star have the same distance to the cone of positive `(1,1)`-forms. -/
theorem infDist_hodgeStar_positiveCone (η : ⋀[ℝ]^2 V) :
    infDist (o.hodgeStar hkl η) (J.positiveCone : Set (⋀[ℝ]^2 V)) =
      infDist η (J.positiveCone : Set (⋀[ℝ]^2 V)) := by
  have hiso : Isometry (o.hodgeStar hkl) :=
    AddMonoidHomClass.isometry_of_norm _ (o.norm_hodgeStar hkl)
  have himage : o.hodgeStar hkl '' (J.positiveCone : Set (⋀[ℝ]^2 V)) = J.positiveCone := by
    ext F
    refine ⟨?_, fun hF ↦ ⟨o.hodgeStar hkl F, ?_, o.hodgeStar_hodgeStar_of_even even_two hkl F⟩⟩
    · rintro ⟨G, hG, rfl⟩
      exact (hodgeStar_mem_positiveCone_iff h₀ h₂ hkl he).2 hG
    · rw [SetLike.mem_coe, hodgeStar_mem_positiveCone_iff h₀ h₂ hkl he]
      exact hF
  conv_lhs => rw [← himage]
  exact infDist_image hiso

include hkl in
/-- `‖κ‖ ≤ ⟪ω, κ⟫` for a positive `(1,1)`-form, given a unitary frame. -/
private theorem norm_le_inner_kahlerForm_of_frame {κ : ⋀[ℝ]^2 V} (hκ : κ ∈ J.positiveCone) :
    ‖κ‖ ≤ ⟪J.kahlerForm, κ⟫ := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  set c := ⟪J.kahlerForm, κ⟫ / 2
  set m := (2⁻¹ : ℝ) • (κ - o.hodgeStar hkl κ)
  have hdec : κ = c • J.kahlerForm + m :=
    eq_smul_kahlerForm_add_of_lieMap_eq_zero h₀ h₂ hkl he hκ.1
  have hm : ‖m‖ ≤ √2 * c := (forall_inner_ιMulti_nonneg_iff h₀ h₂ hkl he κ).1 hκ.2
  have hωm : ⟪J.kahlerForm, m⟫ = 0 := inner_kahlerForm_eq_zero_of_hodgeStar_eq_neg h₀ h₂ hkl he
    (o.hodgeStar_smul_sub_hodgeStar even_two hkl κ)
  have hω : ‖J.kahlerForm‖ ^ 2 = 2 := by
    rw [norm_kahlerForm_sq hJ, (Fact.out : finrank ℝ V = 4)]
    norm_num
  have hc : 0 ≤ c := nonneg_of_mul_nonneg_right ((norm_nonneg m).trans hm) (by positivity)
  -- `‖κ‖² = 2 c² + ‖m‖² ≤ 4 c²`.
  have hsq : ‖κ‖ ^ 2 ≤ (2 * c) ^ 2 := by
    have hm2 : ‖m‖ ^ 2 ≤ 2 * c ^ 2 := by
      calc ‖m‖ ^ 2 ≤ (√2 * c) ^ 2 := pow_le_pow_left₀ (norm_nonneg m) hm 2
        _ = 2 * c ^ 2 := by rw [mul_pow, Real.sq_sqrt zero_le_two]
    rw [hdec, norm_add_sq_real, real_inner_smul_left, hωm, norm_smul, Real.norm_of_nonneg hc,
      mul_pow, hω]
    nlinarith
  have h2c : 2 * c = ⟪J.kahlerForm, κ⟫ := by ring
  rw [← h2c]
  exact (pow_le_pow_iff_left₀ (norm_nonneg κ) (by positivity) two_ne_zero).1 hsq

include hkl in
/-- `⟪Ω, κ⟫ ≥ 0` for a positive `(1,1)`-form `κ` and a form `Ω` nonnegative on complex lines,
given a unitary frame. -/
private theorem inner_nonneg_of_frame {Ω κ : ⋀[ℝ]^2 V}
    (hΩ : ∀ v, 0 ≤ ⟪Ω, ιMulti ℝ 2 ![v, J v]⟫) (hκ : κ ∈ J.positiveCone) : 0 ≤ ⟪Ω, κ⟫ := by
  set c := ⟪J.kahlerForm, κ⟫ / 2
  set m := (2⁻¹ : ℝ) • (κ - o.hodgeStar hkl κ)
  set cΩ := ⟪J.kahlerForm, Ω⟫ / 2
  set p := (2⁻¹ : ℝ) • (Ω + o.hodgeStar hkl Ω)
  set mΩ := (2⁻¹ : ℝ) • (Ω - o.hodgeStar hkl Ω)
  have hdec : κ = c • J.kahlerForm + m :=
    eq_smul_kahlerForm_add_of_lieMap_eq_zero h₀ h₂ hkl he hκ.1
  have hm : ‖m‖ ≤ √2 * c := (forall_inner_ιMulti_nonneg_iff h₀ h₂ hkl he κ).1 hκ.2
  have hmΩ : ‖mΩ‖ ≤ √2 * cΩ := (forall_inner_ιMulti_nonneg_iff h₀ h₂ hkl he Ω).1 hΩ
  have hmm : o.hodgeStar hkl m = -m := o.hodgeStar_smul_sub_hodgeStar even_two hkl κ
  -- The self-dual part `p` of `Ω` is orthogonal to the anti-self-dual `m`.
  have hpm : ⟪p, m⟫ = 0 := by
    have h : ⟪p, o.hodgeStar hkl m⟫ = ⟪p, m⟫ := o.inner_hodgeStar_right_of_hodgeStar_eq_self
      even_two hkl (o.hodgeStar_smul_add_hodgeStar even_two hkl Ω) m
    rw [hmm, inner_neg_right] at h
    linarith
  have hΩm : ⟪Ω, m⟫ = ⟪mΩ, m⟫ := by
    have hΩpm : Ω = p + mΩ := by simp only [p, mΩ]; module
    rw [hΩpm, inner_add_left, hpm, zero_add]
  have hΩω : ⟪Ω, J.kahlerForm⟫ = 2 * cΩ := by rw [real_inner_comm]; ring
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hc : 0 ≤ c := nonneg_of_mul_nonneg_right ((norm_nonneg m).trans hm) (by positivity)
  have hcΩ : 0 ≤ cΩ := nonneg_of_mul_nonneg_right ((norm_nonneg mΩ).trans hmΩ) (by positivity)
  -- `⟪Ω, κ⟫ = 2 c cΩ + ⟪mΩ, m⟫ ≥ 2 c cΩ - ‖mΩ‖ ‖m‖ ≥ 0`.
  have hprod : ‖mΩ‖ * ‖m‖ ≤ (√2 * cΩ) * (√2 * c) :=
    mul_le_mul hmΩ hm (norm_nonneg m) ((norm_nonneg mΩ).trans hmΩ)
  have h2 : √2 * cΩ * (√2 * c) = 2 * cΩ * c := by linear_combination (cΩ * c) * hs
  rw [hdec, inner_add_right, real_inner_smul_right, hΩm, hΩω]
  linarith [neg_abs_le ⟪mΩ, m⟫, abs_real_inner_le_norm mΩ m]

end Frame

section Orthogonal

variable [Fact (finrank ℝ V = 4)] {J : AlmostComplexStructure V}
  (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- An orthogonal complex structure on a four-dimensional space has a unitary frame
`e₀, e₁ = J e₀, e₂, e₃ = J e₂`. -/
private theorem exists_unitaryFrame :
    ∃ e : OrthonormalBasis (Fin 4) ℝ V, J (e 0) = e 1 ∧ J (e 2) = e 3 := by
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (norm_apply hJ) 2
    (by rw [(Fact.out : finrank ℝ V = 4)])
  exact ⟨b, (hb 0).symm, (hb 1).symm⟩

/-- **The norm of a positive `(1,1)`-form is at most its pairing with `ω`**: `‖κ‖ ≤ ⟪ω, κ⟫`, for
an orthogonal complex structure on a four-dimensional space. -/
theorem norm_le_inner_kahlerForm_of_mem_positiveCone {κ : ⋀[ℝ]^2 V}
    (hκ : κ ∈ J.positiveCone) : ‖κ‖ ≤ ⟪J.kahlerForm, κ⟫ := by
  obtain ⟨e, h₀, h₂⟩ := exists_unitaryFrame hJ
  exact norm_le_inner_kahlerForm_of_frame h₀ h₂ (by rw [(Fact.out : finrank ℝ V = 4)]) rfl hκ

/-- **Positive `(1,1)`-forms pair nonnegatively with forms that are nonnegative on complex
lines**: if `Ω(v, J v) ≥ 0` for every `v`, then `⟪Ω, κ⟫ ≥ 0` for every positive `(1,1)`-form
`κ`. The form `Ω` need not be `J`-invariant. -/
theorem inner_nonneg_of_mem_positiveCone {Ω κ : ⋀[ℝ]^2 V}
    (hΩ : ∀ v, 0 ≤ ⟪Ω, ιMulti ℝ 2 ![v, J v]⟫) (hκ : κ ∈ J.positiveCone) : 0 ≤ ⟪Ω, κ⟫ := by
  obtain ⟨e, h₀, h₂⟩ := exists_unitaryFrame hJ
  exact inner_nonneg_of_frame h₀ h₂ (by rw [(Fact.out : finrank ℝ V = 4)]) rfl hΩ hκ

/-- If `Ω(v, J v) ≥ c₀ ‖v‖²` for every `v`, then `c₀ ⟪ω, κ⟫ ≤ ⟪Ω, κ⟫` for every positive
`(1,1)`-form `κ`. -/
theorem mul_inner_kahlerForm_le_inner_of_mem_positiveCone {Ω κ : ⋀[ℝ]^2 V} {c₀ : ℝ}
    (hΩ : ∀ v, c₀ * ‖v‖ ^ 2 ≤ ⟪Ω, ιMulti ℝ 2 ![v, J v]⟫) (hκ : κ ∈ J.positiveCone) :
    c₀ * ⟪J.kahlerForm, κ⟫ ≤ ⟪Ω, κ⟫ := by
  have h := inner_nonneg_of_mem_positiveCone hJ (Ω := Ω - c₀ • J.kahlerForm)
    (fun v ↦ by
      rw [inner_sub_left, real_inner_smul_left, inner_kahlerForm_ιMulti hJ, hJ,
        real_inner_self_eq_norm_sq]
      linarith [hΩ v]) hκ
  rw [inner_sub_left, real_inner_smul_left] at h
  linarith

/-- **A taming form controls the norm of positive `(1,1)`-forms**: if `Ω(v, J v) ≥ c₀ ‖v‖²` for
every `v`, with `c₀ ≥ 0`, then `c₀ ‖κ‖ ≤ ⟪Ω, κ⟫` for every positive `(1,1)`-form `κ`. -/
theorem mul_norm_le_inner_of_mem_positiveCone {Ω κ : ⋀[ℝ]^2 V} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hΩ : ∀ v, c₀ * ‖v‖ ^ 2 ≤ ⟪Ω, ιMulti ℝ 2 ![v, J v]⟫) (hκ : κ ∈ J.positiveCone) :
    c₀ * ‖κ‖ ≤ ⟪Ω, κ⟫ :=
  (mul_le_mul_of_nonneg_left (norm_le_inner_kahlerForm_of_mem_positiveCone hJ hκ) hc₀).trans
    (mul_inner_kahlerForm_le_inner_of_mem_positiveCone hJ hΩ hκ)

/-- **Norm control by a taming form and the distance to the positive cone**: if
`Ω(v, J v) ≥ c₀ ‖v‖²` for every `v`, with `c₀ ≥ 0`, then every two-form `η` satisfies
`c₀ ‖η‖ ≤ ⟪Ω, η⟫ + (‖Ω‖ + c₀) dist(η, positiveCone)`. -/
theorem mul_norm_le_inner_add_mul_infDist_positiveCone {Ω : ⋀[ℝ]^2 V} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hΩ : ∀ v, c₀ * ‖v‖ ^ 2 ≤ ⟪Ω, ιMulti ℝ 2 ![v, J v]⟫) (η : ⋀[ℝ]^2 V) :
    c₀ * ‖η‖ ≤ ⟪Ω, η⟫ + (‖Ω‖ + c₀) * infDist η (J.positiveCone : Set (⋀[ℝ]^2 V)) := by
  obtain ⟨κ, hκ, hd⟩ := (isClosed_positiveCone J).exists_infDist_eq_dist
    ⟨0, zero_mem J.positiveCone⟩ η
  rw [hd, dist_eq_norm]
  have hκη := mul_norm_le_inner_of_mem_positiveCone hJ hc₀ hΩ hκ
  have htri : ‖η‖ ≤ ‖κ‖ + ‖η - κ‖ := norm_le_norm_add_norm_sub' η κ
  have hpair : ⟪Ω, κ - η⟫ ≤ ‖Ω‖ * ‖η - κ‖ := by
    rw [← norm_neg (η - κ), neg_sub]
    exact real_inner_le_norm Ω (κ - η)
  rw [inner_sub_right] at hpair
  nlinarith [norm_nonneg (η - κ)]

end Orthogonal

end TauCeti.AlmostComplexStructure
