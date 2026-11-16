/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Logarithmic twists and representative changes on torus families

Over the complement `{φ ≠ 0}` of the zero locus of a `C^n` (or holomorphic) complex function `φ`
on a base manifold `Y`, a period section `μ : Λ` determines the logarithmic twist automorphism
`[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` of the punctured torus family `Y* → {φ ≠ 0}`.
Although `log (φ y)` is only locally single-valued, shifting the branch of the logarithm by
`2πi k` (`k ∈ ℤ`) shifts the fibre coordinate by `k • P y μ ∈ P y (Λ)`, so the automorphism is
globally well-defined and locally given by any `C^n` (or holomorphic) branch of `log ∘ φ`.

Specializing to a disc `Metric.ball 0 (r ^ m)` with coordinate `φ = Subtype.val`, the logarithmic
twists form the gauge-transition group governing representative changes `l ↦ l + m • μ` of the
normalized pure translation action `TauCeti.logTranslationMulAction`: replacing `l` by `l + m • μ`
leaves the cyclic action unchanged (`TauCeti.logTranslationMulAction_add_nsmul`), identifies the
quotient manifolds canonically, and postcomposes the downstairs logarithmic gauge diffeomorphism
`Q* ≃ₘ^n Y*` with the logarithmic twist for `-μ`.

## Main definitions and results

* `TauCeti.torusFamilyLogTwistMap`: the fibrewise equivalence
  `[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` on `(Y × E) / Λ`.
* `TauCeti.torusFamilyLogTwistMap_mk_of_exp_eq`: branch-independence of `torusFamilyLogTwistMap`
  whenever `exp L = φ y`.
* `TauCeti.torusFamilyLogTwistEquiv`: restriction of `torusFamilyLogTwistMap` to the punctured
  family `{φ ∘ p ≠ 0}`.
* `TauCeti.torusFamilyLogTwistDiffeomorph`: the logarithmic twist as a `C^n` diffeomorphism (and
  biholomorphism for `n = ω`) of the punctured open submanifold `{φ ∘ p ≠ 0}` over `Y`, together
  with its group-homomorphism laws (`_zero`, `_trans`, `_symm`).
* `TauCeti.logTranslationSection_add_nsmul`, `TauCeti.logTranslationMulAction_add_nsmul`: the
  normalized pure translation action depends only on `l` modulo `mΛ`.
* `TauCeti.torusFamilyLogGauge_add_nsmul`, `TauCeti.torusFamilyLogGaugeEquiv_add_nsmul`, and
  `TauCeti.torusFamilyLogGaugeDiffeomorph_add_nsmul`: changing the representative `l` by `m • μ`
  postcomposes the logarithmic gauge with the logarithmic twist for `-μ`.
* `TauCeti.logTranslationQuotientAddNsmulEquiv` and
  `TauCeti.logTranslationQuotientAddNsmulDiffeomorph`: canonical identification of the cyclic
  quotient manifolds for `l + m • μ` and `l`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, and A. Van de Ven, *Compact Complex Surfaces*, 2nd ed.,
  Springer, 2004, Ch. V, §13 (logarithmic transformations of torus families).
* K. Kodaira, *On compact analytic surfaces III*, Ann. of Math. **78** (1963), 1–40, §11.
-/

public section

open Complex Real MulAction
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Logarithmic twists on torus families -/

section LogTwist

variable {Y Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E] [Module ℂ E]
  (φ : Y → ℂ) (P : Y → Λ →ₗ[ℤ] E)

/-- The fibrewise logarithmic twist `[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` on the torus
family `(Y × E) / Λ`. On the locus `{φ ≠ 0}` it is independent of the branch of the logarithm
(`torusFamilyLogTwistMap_mk_of_exp_eq`). -/
noncomputable def torusFamilyLogTwistMap (μ : Λ) :
    (letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) ≃
      (letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :=
  torusFamilyGauge P fun y ↦ (log (φ y) / (2 * π * I)) • P y μ

/-- On representatives, the logarithmic twist adds `(log (φ y) / 2πi) • P y μ` to the fibre
coordinate. -/
@[simp] theorem torusFamilyLogTwistMap_mk (μ : Λ) (y : Y) (e : E) :
    letI := periodAddAction P
    torusFamilyLogTwistMap φ P μ (Quotient.mk _ (y, e)) =
      Quotient.mk _ (y, e + (log (φ y) / (2 * π * I)) • P y μ) :=
  torusFamilyGauge_mk P _ y e

/-- The logarithmic twist preserves the family projection to `Y`. -/
@[simp] theorem torusFamilyProjection_torusFamilyLogTwistMap (μ : Λ)
    (y : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    torusFamilyProjection P (torusFamilyLogTwistMap φ P μ y) = torusFamilyProjection P y :=
  torusFamilyProjection_gauge P _ y

/-- **Branch independence of the logarithmic twist.** Any logarithm `L` of `φ y` computes the
logarithmic twist on the fibre over `y`, because integer multiples of `2πi` shift the fibre by
periods in `P y (Λ)`. -/
theorem torusFamilyLogTwistMap_mk_of_exp_eq (μ : Λ) {y : Y} {L : ℂ} (hL : exp L = φ y) (e : E) :
    letI := periodAddAction P
    torusFamilyLogTwistMap φ P μ (Quotient.mk _ (y, e)) =
      Quotient.mk _ (y, e + (L / (2 * π * I)) • P y μ) := by
  let _ := periodAddAction P
  have hφ : φ y ≠ 0 := hL ▸ Complex.exp_ne_zero L
  have hexp : exp (L - log (φ y)) = 1 := by
    rw [Complex.exp_sub, hL, Complex.exp_log hφ, div_self hφ]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hexp
  have hdiv : L / (2 * π * I) - log (φ y) / (2 * π * I) = (k : ℂ) := by
    rw [← sub_div, hk, mul_div_cancel_right₀ _ two_pi_I_ne_zero]
  rw [torusFamilyLogTwistMap_mk, Quotient.eq, AddAction.orbitRel_apply,
    mem_orbit_periodAddAction_iff]
  refine ⟨rfl, -(k • μ), ?_⟩
  rw [map_neg, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, ← hdiv]
  simp only [sub_smul]
  abel

/-- The logarithmic twist for `0 : Λ` is the identity. -/
@[simp] theorem torusFamilyLogTwistMap_zero :
    torusFamilyLogTwistMap φ P 0 = Equiv.refl _ := by
  have h : (fun y ↦ (log (φ y) / (2 * π * I)) • P y 0) = 0 := by
    ext y
    simp
  rw [torusFamilyLogTwistMap, h, torusFamilyGauge_zero]

/-- Composing logarithmic twists adds their period parameters. -/
@[simp] theorem torusFamilyLogTwistMap_trans (μ₁ μ₂ : Λ) :
    (torusFamilyLogTwistMap φ P μ₁).trans (torusFamilyLogTwistMap φ P μ₂) =
      torusFamilyLogTwistMap φ P (μ₁ + μ₂) := by
  rw [torusFamilyLogTwistMap, torusFamilyLogTwistMap, torusFamilyGauge_trans,
    torusFamilyLogTwistMap]
  congr 1
  ext y
  simp [smul_add]

/-- The inverse of a logarithmic twist negates its period parameter. -/
@[simp] theorem torusFamilyLogTwistMap_symm (μ : Λ) :
    (torusFamilyLogTwistMap φ P μ).symm = torusFamilyLogTwistMap φ P (-μ) := by
  rw [torusFamilyLogTwistMap, torusFamilyGauge_symm, torusFamilyLogTwistMap]
  congr 1
  ext y
  simp

/-- The logarithmic twist restricted to the punctured torus family `{φ ∘ p ≠ 0}`. -/
noncomputable def torusFamilyLogTwistEquiv (μ : Λ) :
    (letI := periodAddAction P;
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}) ≃
    (letI := periodAddAction P;
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}) :=
  (torusFamilyLogTwistMap φ P μ).subtypeEquiv fun y ↦ by simp

/-- Coercion of `torusFamilyLogTwistEquiv` to the ambient torus family is
`torusFamilyLogTwistMap`. -/
@[simp] theorem coe_torusFamilyLogTwistEquiv (μ : Λ)
    (y : letI := periodAddAction P
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}) :
    (torusFamilyLogTwistEquiv φ P μ y :
        letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyLogTwistMap φ P μ y.1 := (rfl)

/-- The punctured logarithmic twist for `0 : Λ` is the identity. -/
@[simp] theorem torusFamilyLogTwistEquiv_zero :
    torusFamilyLogTwistEquiv φ P 0 = Equiv.refl _ := by
  ext y
  simp [torusFamilyLogTwistMap_zero]

/-- Composing punctured logarithmic twists adds their period parameters. -/
@[simp] theorem torusFamilyLogTwistEquiv_trans (μ₁ μ₂ : Λ) :
    (torusFamilyLogTwistEquiv φ P μ₁).trans (torusFamilyLogTwistEquiv φ P μ₂) =
      torusFamilyLogTwistEquiv φ P (μ₁ + μ₂) := by
  ext y
  simp only [Equiv.trans_apply, coe_torusFamilyLogTwistEquiv]
  exact congrFun (congrArg DFunLike.coe (torusFamilyLogTwistMap_trans φ P μ₁ μ₂)) y.1

/-- The inverse of a punctured logarithmic twist negates its period parameter. -/
@[simp] theorem torusFamilyLogTwistEquiv_symm (μ : Λ) :
    (torusFamilyLogTwistEquiv φ P μ).symm = torusFamilyLogTwistEquiv φ P (-μ) := by
  ext y
  simp only [torusFamilyLogTwistEquiv, Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply,
    torusFamilyLogTwistMap_symm]

/-- The punctured logarithmic twist preserves the family projection to `Y`. -/
theorem torusFamilyProjection_torusFamilyLogTwistEquiv (μ : Λ)
    (y : letI := periodAddAction P
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}) :
    torusFamilyProjection P (torusFamilyLogTwistEquiv φ P μ y).1 =
      torusFamilyProjection P y.1 :=
  torusFamilyProjection_torusFamilyLogTwistMap φ P μ y.1

end LogTwist

/-! ### `C^n` and holomorphic logarithmic twist diffeomorphisms -/

section LogTwistDiffeomorph

variable {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℂ EY]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ EY H}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [T2Space Y] [LocallyCompactSpace Y]
  {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (φ : Y → ℂ) (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Function.Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hφ : ContMDiff I 𝓘(ℂ) n φ) (hP : ∀ l, ContMDiff I 𝓘(ℂ, E) n fun y ↦ P y l)

include hφ in
/-- The logarithmic twist is `C^n` at every point of the torus family where `φ ∘ p ≠ 0`: locally
near `y₀`, it is given by the `C^n` branch `log (φ y₀) + log (φ y / φ y₀)`. -/
theorem contMDiffAt_torusFamilyLogTwistMap (μ : Λ)
    {x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)}
    (hx : φ (torusFamilyProjection P x) ≠ 0) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiffAt (I.prod 𝓘(ℂ, E)) (I.prod 𝓘(ℂ, E)) n (torusFamilyLogTwistMap φ P μ) x := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  obtain ⟨⟨y₀, e₀⟩, rfl⟩ := Quotient.exists_rep x
  have hy₀ : φ y₀ ≠ 0 := by rwa [torusFamilyProjection_mk] at hx
  rw [← (isLocalDiffeomorph_torusFamily_mk P hinj hP (y₀, e₀)).contMDiffAt_comp_iff le_rfl]
  let L : Y → ℂ := fun y ↦ log (φ y₀) + log (φ y / φ y₀)
  have hLc : ContMDiffAt (I.prod 𝓘(ℂ, E)) 𝓘(ℂ) n (fun p : Y × E ↦ L p.1) (y₀, e₀) :=
    contMDiffAt_const.add
      ((Complex.contDiffAt_log (x := 1) one_mem_slitPlane).contMDiffAt.comp_of_eq
        ((contDiff_id.div_const (φ y₀)).contMDiff.comp
          (hφ.comp contMDiff_fst)).contMDiffAt (by simp [hy₀]))
  have hs : ContMDiffAt (I.prod 𝓘(ℂ, E)) (I.prod 𝓘(ℂ, E)) n
      (fun p : Y × E ↦ (Quotient.mk _ (p.1, p.2 + (L p.1 / (2 * π * Complex.I)) • P p.1 μ) :
        AddAction.orbitRel.Quotient Λ (Y × E))) (y₀, e₀) :=
    (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff.contMDiffAt.comp (y₀, e₀)
      (contMDiffAt_fst.prodMk (contMDiffAt_snd.add
        ((hLc.div_const (2 * π * Complex.I)).smul ((hP μ).comp contMDiff_fst).contMDiffAt)))
  refine hs.congr_of_eventuallyEq ?_
  have hopen : IsOpen {p : Y × E | φ p.1 ≠ 0} :=
    isOpen_ne_fun (hφ.continuous.comp continuous_fst) continuous_const
  filter_upwards [hopen.mem_nhds hy₀] with p hp
  have hexp : exp (L p.1) = φ p.1 := by
    rw [Complex.exp_add, Complex.exp_log hy₀, Complex.exp_log (div_ne_zero hp hy₀),
      mul_div_cancel₀ _ hy₀]
  exact torusFamilyLogTwistMap_mk_of_exp_eq φ P μ hexp p.2

/-- The punctured logarithmic twist is `C^n` on the open submanifold `{φ ∘ p ≠ 0}`. -/
private theorem contMDiff_torusFamilyLogTwistEquiv (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
      (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
        isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
        TopologicalSpace.Opens _)
    ContMDiff (I.prod 𝓘(ℂ, E)) (I.prod 𝓘(ℂ, E)) n (torusFamilyLogTwistEquiv φ P μ) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let U : TopologicalSpace.Opens _ :=
    ⟨{y | φ (torusFamilyProjection P y) ≠ 0},
      isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E) U
  refine (ContMDiff.subtypeVal_comp_iff U _).1 fun y ↦ ?_
  have hcomp : (Subtype.val : U → _) ∘ torusFamilyLogTwistEquiv φ P μ =
      torusFamilyLogTwistMap φ P μ ∘ (Subtype.val : U → _) :=
    funext fun z ↦ coe_torusFamilyLogTwistEquiv φ P μ z
  rw [hcomp]
  exact (contMDiffAt_subtype_iff (U := U) (x := y)).2
    (contMDiffAt_torusFamilyLogTwistMap φ P hinj hφ hP μ y.2)

/-- **The logarithmic twist diffeomorphism.** For a `C^n` period family `P` over `Y` and a `C^n`
function `φ : Y → ℂ`, each lattice element `μ : Λ` defines a `C^n` automorphism
`[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` of the punctured open submanifold `{φ ∘ p ≠ 0}` over
`Y`. For holomorphic input (`n = ω`), this is a biholomorphism over `{φ ≠ 0}`. -/
noncomputable def torusFamilyLogTwistDiffeomorph (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
      (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
        isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
        TopologicalSpace.Opens _)
    Diffeomorph (I.prod 𝓘(ℂ, E)) (I.prod 𝓘(ℂ, E))
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0} n :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
    (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
      isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
      TopologicalSpace.Opens _)
  { toEquiv := torusFamilyLogTwistEquiv φ P μ
    contMDiff_toFun := contMDiff_torusFamilyLogTwistEquiv φ P hinj hφ hP μ
    contMDiff_invFun := by
      rw [torusFamilyLogTwistEquiv_symm]
      exact contMDiff_torusFamilyLogTwistEquiv φ P hinj hφ hP (-μ) }

/-- The logarithmic twist diffeomorphism has underlying equivalence `torusFamilyLogTwistEquiv`. -/
@[simp] theorem torusFamilyLogTwistDiffeomorph_toEquiv (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
      (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
        isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
        TopologicalSpace.Opens _)
    (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ).toEquiv =
      torusFamilyLogTwistEquiv φ P μ := (rfl)

/-- Coercing `torusFamilyLogTwistDiffeomorph` to a function gives `torusFamilyLogTwistEquiv`. -/
@[simp] theorem coe_torusFamilyLogTwistDiffeomorph (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
      (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
        isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
        TopologicalSpace.Opens _)
    ⇑(torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ) =
      torusFamilyLogTwistEquiv φ P μ := (rfl)

/-- The logarithmic twist diffeomorphism for `0 : Λ` is the identity. -/
@[simp] theorem torusFamilyLogTwistDiffeomorph_zero :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
      (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
        isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
        TopologicalSpace.Opens _)
    torusFamilyLogTwistDiffeomorph φ P hinj hφ hP 0 = Diffeomorph.refl _ _ _ := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
    (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
      isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
      TopologicalSpace.Opens _)
  exact Diffeomorph.toEquiv_injective (torusFamilyLogTwistEquiv_zero φ P)

/-- Composing logarithmic twist diffeomorphisms adds their period parameters. -/
@[simp] theorem torusFamilyLogTwistDiffeomorph_trans (μ₁ μ₂ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
      (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
        isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
        TopologicalSpace.Opens _)
    (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ₁).trans
        (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ₂) =
      torusFamilyLogTwistDiffeomorph φ P hinj hφ hP (μ₁ + μ₂) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
    (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
      isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
      TopologicalSpace.Opens _)
  exact Diffeomorph.toEquiv_injective (torusFamilyLogTwistEquiv_trans φ P μ₁ μ₂)

/-- The inverse of a logarithmic twist diffeomorphism negates its period parameter. -/
@[simp] theorem torusFamilyLogTwistDiffeomorph_symm (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
      (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
        isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
        TopologicalSpace.Opens _)
    (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ).symm =
      torusFamilyLogTwistDiffeomorph φ P hinj hφ hP (-μ) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd H E)
    (⟨{y | φ (torusFamilyProjection P y) ≠ 0},
      isOpen_ne_fun (hφ.continuous.comp (continuous_torusFamilyProjection P)) continuous_const⟩ :
      TopologicalSpace.Opens _)
  exact Diffeomorph.toEquiv_injective (torusFamilyLogTwistEquiv_symm φ P μ)

/-- The logarithmic twist diffeomorphism preserves the family projection to `Y`. -/
theorem torusFamilyProjection_torusFamilyLogTwistDiffeomorph (μ : Λ)
    (y : letI := periodAddAction P
      {y : AddAction.orbitRel.Quotient Λ (Y × E) // φ (torusFamilyProjection P y) ≠ 0}) :
    torusFamilyProjection P (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ y).1 =
      torusFamilyProjection P y.1 :=
  torusFamilyProjection_torusFamilyLogTwistEquiv φ P μ y

end LogTwistDiffeomorph

/-! ### Changing the period representative `l ↦ l + m • μ` -/

section AddNsmulComparison

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E] [Module ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)

/-- Adding an element of `mΛ` to `l` does not change the normalized translation section:
`m * log ζ` is an integer multiple of `2πi`, so `(log ζ / 2πi) • P (z ^ m) (m • μ)` is a period. -/
theorem logTranslationSection_add_nsmul (l μ : Λ) (ζ : rootsOfUnity m ℂ)
    (z : rootsOfUnityBall m r) :
    logTranslationSection P (l + m • μ) ζ z = logTranslationSection P l ζ z := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  have hexp : Complex.exp ((m : ℂ) * log ((ζ : ℂˣ) : ℂ)) = Complex.exp 0 := by
    rw [Complex.exp_nat_mul, Complex.exp_log (ζ : ℂˣ).ne_zero, Complex.exp_zero]
    have hpow : (ζ : ℂˣ) ^ m = 1 := (_root_.mem_rootsOfUnity m (ζ : ℂˣ)).1 ζ.2
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hpow
  obtain ⟨k, hk⟩ := exists_div_two_pi_I_smul_eq_add_zsmul hexp (powPullbackPeriod m r P z μ)
  rw [zero_div, zero_smul, zero_add] at hk
  rw [logTranslationSection_eq_mk_of_exp_eq P (l + m • μ) (Complex.exp_log (ζ : ℂˣ).ne_zero),
    logTranslationSection_eq_mk_of_exp_eq P l (Complex.exp_log (ζ : ℂˣ).ne_zero),
    Quotient.eq, AddAction.orbitRel_apply, mem_orbit_periodAddAction_iff]
  refine ⟨rfl, k • μ, ?_⟩
  rw [map_add, map_nsmul, smul_add, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_comm _ (m : ℂ), ← mul_div_assoc, hk, map_zsmul, powPullbackPeriod_apply,
    powPullbackPeriod_apply, rootsOfUnityBall.powMap_smul]

/-- The normalized translation action depends only on the class of `l` modulo `mΛ`. -/
theorem logTranslationMulAction_add_nsmul (l μ : Λ) :
    logTranslationMulAction P (l + m • μ) = logTranslationMulAction P l := by
  have hsec : logTranslationSection P (l + m • μ) = logTranslationSection P l :=
    funext fun ζ ↦ funext fun z ↦ logTranslationSection_add_nsmul P l μ ζ z
  simp only [logTranslationMulAction, hsec]

/-- Upstairs, replacing the period representative `l` by `l + m • μ` postcomposes the logarithmic
gauge with the logarithmic twist for `-μ` over `z ≠ 0`. -/
theorem torusFamilyLogGauge_add_nsmul (l μ : Λ)
    {x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)}
    (hx : ((torusFamilyProjection (powPullbackPeriod m r P) x : rootsOfUnityBall m r) : ℂ) ≠ 0) :
    torusFamilyLogGauge P (l + m • μ) x =
      torusFamilyLogTwistMap Subtype.val P (-μ) (torusFamilyLogGauge P l x) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  obtain ⟨⟨z, e⟩, rfl⟩ := Quotient.exists_rep x
  have hz : (z : ℂ) ≠ 0 := by rwa [torusFamilyProjection_mk] at hx
  have hexp : exp ((m : ℂ) * log (z : ℂ)) = (rootsOfUnityBall.powMap m r z : ℂ) := by
    rw [Complex.exp_nat_mul, Complex.exp_log hz, rootsOfUnityBall.coe_powMap]
  rw [torusFamilyLogGauge_mk, torusFamilyLogGauge_mk,
    torusFamilyLogTwistMap_mk_of_exp_eq Subtype.val P (-μ) hexp]
  congr 2
  rw [map_add, map_nsmul, map_neg, smul_add, smul_neg, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_div_assoc, mul_comm (m : ℂ), ← sub_eq_add_neg, sub_sub]

/-- Freeness of the normalized pure translation action is invariant under replacing `l` by
`l + m • μ`. -/
theorem isCancelSMul_logTranslationMulAction_add_nsmul (l μ : Λ)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI := logTranslationMulAction P (l + m • μ)
    IsCancelSMul (rootsOfUnity m ℂ)
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  rw [logTranslationMulAction_add_nsmul P l μ]
  exact hfree

/-- Canonical identification of the cyclic quotients for `l + m • μ` and `l`, induced by the
identity upstairs (the two `μ_m`-actions coincide by `logTranslationMulAction_add_nsmul`). -/
noncomputable def logTranslationQuotientAddNsmulEquiv (l μ : Λ) :
    (letI := periodAddAction (powPullbackPeriod m r P);
      letI := logTranslationMulAction P (l + m • μ);
      orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) ≃
    (letI := periodAddAction (powPullbackPeriod m r P);
      letI := logTranslationMulAction P l;
      orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
  letI := periodAddAction (powPullbackPeriod m r P)
  Quotient.congr (Equiv.refl _) fun _ _ ↦ by
    rw [logTranslationMulAction_add_nsmul P l μ]
    rfl

/-- On representatives, `logTranslationQuotientAddNsmulEquiv` sends the orbit class of `x` to the
orbit class of `x`. -/
@[simp] theorem logTranslationQuotientAddNsmulEquiv_mk (l μ : Λ)
    (x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :
    letI := periodAddAction (powPullbackPeriod m r P)
    logTranslationQuotientAddNsmulEquiv P l μ
        (letI := logTranslationMulAction P (l + m • μ); Quotient.mk _ x) =
      (letI := logTranslationMulAction P l; Quotient.mk _ x) := (rfl)

/-- On representatives, the inverse of `logTranslationQuotientAddNsmulEquiv` sends the orbit class
of `x` to the orbit class of `x`. -/
@[simp] theorem logTranslationQuotientAddNsmulEquiv_symm_mk (l μ : Λ)
    (x : letI := periodAddAction (powPullbackPeriod m r P)
      AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :
    letI := periodAddAction (powPullbackPeriod m r P)
    (logTranslationQuotientAddNsmulEquiv P l μ).symm
        (letI := logTranslationMulAction P l; Quotient.mk _ x) =
      (letI := logTranslationMulAction P (l + m • μ); Quotient.mk _ x) := (rfl)

/-- The canonical identification between the cyclic quotients for `l + m • μ` and `l` preserves the
descended base coordinate `t = z ^ m`. -/
@[simp] theorem torusFamilyCyclicQuotientProjection_logTranslationQuotientAddNsmulEquiv
    (l μ : Λ)
    (q : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P (l + m • μ)
      orbitRel.Quotient (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction (powPullbackPeriod m r P)
    (letI := logTranslationMulAction P l;
      torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
        (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
        (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
        (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
        (logTranslationSection_mul P l) (logTranslationQuotientAddNsmulEquiv P l μ q)) =
      (letI := logTranslationMulAction P (l + m • μ);
        torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P (l + m • μ))
          (torusFamilyProjection_logTranslationSection P (l + m • μ))
          (logTranslationSection_mul P (l + m • μ)) q) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [logTranslationQuotientAddNsmulEquiv_mk, torusFamilyCyclicQuotientProjection_mk,
    torusFamilyCyclicQuotientProjection_mk]

/-- Downstairs, replacing `l` by `l + m • μ` changes the logarithmic gauge equivalence `Q* ≃ Y*` by
postcomposing with the logarithmic twist for `-μ`. -/
theorem torusFamilyLogGaugeEquiv_add_nsmul (l μ : Λ) (hr : 0 ≤ r) :
    letI := periodAddAction (powPullbackPeriod m r P)
    torusFamilyLogGaugeEquiv P (l + m • μ) hr =
      ((logTranslationQuotientAddNsmulEquiv P l μ).subtypeEquiv fun q ↦ by
          rw [torusFamilyCyclicQuotientProjection_logTranslationQuotientAddNsmulEquiv]).trans
        ((torusFamilyLogGaugeEquiv P l hr).trans
          (torusFamilyLogTwistEquiv Subtype.val P (-μ))) := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  ext ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hx : ((torusFamilyProjection (powPullbackPeriod m r P) x :
      rootsOfUnityBall m r) : ℂ) ≠ 0 := fun h ↦
    hq (by rw [torusFamilyCyclicQuotientProjection_mk, h, zero_pow (NeZero.ne m)])
  simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply, coe_torusFamilyLogTwistEquiv,
    logTranslationQuotientAddNsmulEquiv_mk]
  rw [torusFamilyLogGaugeEquiv_mk P (l + m • μ) hr x, torusFamilyLogGaugeEquiv_mk P l hr x]
  exact torusFamilyLogGauge_add_nsmul P l μ hx

end AddNsmulComparison

section AddNsmulDiffeomorph

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ : Type*} [AddCommGroup Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : Metric.ball (0 : ℂ) (r ^ m) → Λ →ₗ[ℤ] E)
  [∀ t, DiscreteTopology (LinearMap.range (P t))]
  [∀ t, IsZLattice ℝ (LinearMap.range (P t))]
  (hinj : ∀ t, Function.Injective (P t)) {n : ℕ∞ω}
  (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun t ↦ P t l)

/-- The canonical identification between the cyclic quotient manifolds for `l + m • μ` and `l` is a
`C^n` diffeomorphism (biholomorphism for `n = ω`). -/
noncomputable def logTranslationQuotientAddNsmulDiffeomorph (l μ : Λ)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P (l + m • μ);
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
        (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P l;
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    Diffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E))
      (letI := logTranslationMulAction P (l + m • μ);
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
      (letI := logTranslationMulAction P l;
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) n := by
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ := torusFamilyChartedSpace (H := ℂ) (powPullbackPeriod m r P)
    (fun l' ↦ (contMDiff_powPullbackPeriod P (hP l')).continuous)
    (fun z ↦ powPullbackPeriod_injective P z (hinj _))
  let _ : ChartedSpace (ModelProd ℂ E)
      (letI := logTranslationMulAction P (l + m • μ);
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
      (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
  let _ : ChartedSpace (ModelProd ℂ E)
      (letI := logTranslationMulAction P l;
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  have hmk₁ : IsLocalDiffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (letI := logTranslationMulAction P (l + m • μ);
        Quotient.mk (orbitRel (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) := by
    let _ := logTranslationMulAction P (l + m • μ)
    exact isLocalDiffeomorph_torusFamilyAffineQuotient_mk (H := ℂ) (I := 𝓘(ℂ))
      (powPullbackPeriod m r P) (fun z ↦ powPullbackPeriod_injective P z (hinj _))
      (fun l' ↦ contMDiff_powPullbackPeriod P (hP l')) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P (l + m • μ))
      (torusFamilyProjection_logTranslationSection P (l + m • μ))
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P (l + m • μ))
      (fun _ ↦ contMDiff_snd)
      (fun ζ ↦ contMDiff_logTranslationSection P hinj hP (l + m • μ) ζ)
      (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
  have hmk₂ : IsLocalDiffeomorph (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (letI := logTranslationMulAction P l;
        Quotient.mk (orbitRel (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))) := by
    let _ := logTranslationMulAction P l
    exact isLocalDiffeomorph_torusFamilyAffineQuotient_mk (H := ℂ) (I := 𝓘(ℂ))
      (powPullbackPeriod m r P) (fun z ↦ powPullbackPeriod_injective P z (hinj _))
      (fun l' ↦ contMDiff_powPullbackPeriod P (hP l')) (fun _ _ ↦ AddMonoidHom.id E)
      (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
      (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
      (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (logTranslationSection_mul P l)
      (fun _ ↦ contMDiff_snd) (fun ζ ↦ contMDiff_logTranslationSection P hinj hP l ζ) hfree
  exact
    { toEquiv := logTranslationQuotientAddNsmulEquiv P l μ
      contMDiff_toFun :=
        (hmk₁.contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 hmk₂.contMDiff
      contMDiff_invFun :=
        (hmk₂.contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 hmk₁.contMDiff }

/-- The underlying equivalence of `logTranslationQuotientAddNsmulDiffeomorph` is
`logTranslationQuotientAddNsmulEquiv`. -/
@[simp] theorem logTranslationQuotientAddNsmulDiffeomorph_toEquiv (l μ : Λ) (hfree) :
    letI := periodAddAction (powPullbackPeriod m r P)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P (l + m • μ);
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
        (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P l;
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    (logTranslationQuotientAddNsmulDiffeomorph P hinj hP l μ hfree).toEquiv =
      logTranslationQuotientAddNsmulEquiv P l μ := (rfl)

/-- **Representative-change comparison for the downstairs logarithmic gauge.** Replacing `l` by
`l + m • μ` changes the downstairs `C^n` (or holomorphic) logarithmic gauge diffeomorphism
`Q* ≃ₘ^n Y*` by postcomposing with the logarithmic twist diffeomorphism for `-μ` (up to the
canonical identification of the two quotient manifolds). -/
theorem torusFamilyLogGaugeDiffeomorph_add_nsmul (l μ : Λ) (hr : 0 ≤ r)
    (hfree : letI := periodAddAction (powPullbackPeriod m r P)
      letI := logTranslationMulAction P l
      IsCancelSMul (rootsOfUnity m ℂ)
        (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
      (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
        isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
          continuous_const⟩ : TopologicalSpace.Opens _)
    letI := periodAddAction (powPullbackPeriod m r P)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P (l + m • μ);
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
        (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
    letI : ChartedSpace (ModelProd ℂ E)
        (letI := logTranslationMulAction P l;
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
    let UQ' : TopologicalSpace.Opens
        (letI := logTranslationMulAction P (l + m • μ);
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      ⟨{q | letI := logTranslationMulAction P (l + m • μ);
          torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
            (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
            (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
            (logTranslationSection P (l + m • μ))
            (torusFamilyProjection_logTranslationSection P (l + m • μ))
            (logTranslationSection_mul P (l + m • μ)) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩
    let UQ : TopologicalSpace.Opens
        (letI := logTranslationMulAction P l;
          orbitRel.Quotient (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
      ⟨{q | letI := logTranslationMulAction P l;
          torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
            (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
            (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
            (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
            (logTranslationSection_mul P l) q ≠ 0},
        isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
          continuous_const⟩
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E) UQ'
    letI := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E) UQ
    torusFamilyLogGaugeDiffeomorph P hinj hP (l + m • μ) hr
        (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree) =
      ((logTranslationQuotientAddNsmulDiffeomorph P hinj hP l μ hfree).subtype
          (U := UQ') (V := UQ) fun q ↦ by
            simp only [UQ', UQ, TopologicalSpace.Opens.mem_mk, Set.mem_ofPred_eq]
            exact (torusFamilyCyclicQuotientProjection_logTranslationQuotientAddNsmulEquiv
              P l μ q).symm ▸ Iff.rfl).trans
        ((torusFamilyLogGaugeDiffeomorph P hinj hP l hr hfree).trans
          (torusFamilyLogTwistDiffeomorph Subtype.val P hinj
            contMDiff_subtypeVal_ball hP (-μ))) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l' ↦ (hP l').continuous) hinj
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E)
    (⟨{y | ((torusFamilyProjection P y : Metric.ball (0 : ℂ) (r ^ m)) : ℂ) ≠ 0},
      isOpen_ne_fun (continuous_subtype_val.comp (continuous_torusFamilyProjection P))
        continuous_const⟩ : TopologicalSpace.Opens _)
  let _ := periodAddAction (powPullbackPeriod m r P)
  let _ : ChartedSpace (ModelProd ℂ E)
      (letI := logTranslationMulAction P (l + m • μ);
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) (l + m • μ)
      (isCancelSMul_logTranslationMulAction_add_nsmul P l μ hfree)
  let _ : ChartedSpace (ModelProd ℂ E)
      (letI := logTranslationMulAction P l;
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    logTranslationQuotientChartedSpace P hinj (fun l' ↦ (hP l').continuous) l hfree
  let UQ' : TopologicalSpace.Opens
      (letI := logTranslationMulAction P (l + m • μ);
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    ⟨{q | letI := logTranslationMulAction P (l + m • μ);
        torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P (l + m • μ))
          (torusFamilyProjection_logTranslationSection P (l + m • μ))
          (logTranslationSection_mul P (l + m • μ)) q ≠ 0},
      isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
        continuous_const⟩
  let UQ : TopologicalSpace.Opens
      (letI := logTranslationMulAction P l;
        orbitRel.Quotient (rootsOfUnity m ℂ)
          (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))) :=
    ⟨{q | letI := logTranslationMulAction P l;
        torusFamilyCyclicQuotientProjection (fun _ _ ↦ AddMonoidHom.id E) (fun _ _ ↦ rfl)
          (fun _ _ _ _ ↦ rfl) (powPullbackPeriod m r P)
          (Representation.trivial ℤ (rootsOfUnity m ℂ) Λ) (powPullbackPeriod_smul_apply P)
          (logTranslationSection P l) (torusFamilyProjection_logTranslationSection P l)
          (logTranslationSection_mul P l) q ≠ 0},
      isOpen_ne_fun (continuous_torusFamilyCyclicQuotientProjection _ _ _ _ _ _ _ _ _)
        continuous_const⟩
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E) UQ'
  let _ := TopologicalSpace.Opens.instChartedSpace (H := ModelProd ℂ E) UQ
  apply Diffeomorph.ext
  intro q
  have h := Equiv.congr_fun (torusFamilyLogGaugeEquiv_add_nsmul P l μ hr) q
  rw [Diffeomorph.coe_trans, Diffeomorph.coe_trans, Function.comp_apply, Function.comp_apply,
    coe_torusFamilyLogTwistDiffeomorph,
    coe_torusFamilyLogGaugeDiffeomorph P hinj hP (l + m • μ) hr,
    coe_torusFamilyLogGaugeDiffeomorph P hinj hP l hr hfree,
    h, Equiv.trans_apply, Equiv.trans_apply]
  congr 2
  apply Subtype.ext
  rw [Diffeomorph.subtype_apply_coe]
  rfl

end AddNsmulDiffeomorph

end TauCeti
