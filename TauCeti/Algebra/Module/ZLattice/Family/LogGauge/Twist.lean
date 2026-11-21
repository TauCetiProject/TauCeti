/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Algebra.Module.ZLattice.Family.Gauge
public import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Branch
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Branch

/-!
# Logarithmic twists on torus families

Over the complement `{φ ≠ 0}` of the zero locus of a `C^n` (or holomorphic) complex function `φ`
on a base manifold `Y`, a period section `μ : Λ` determines the logarithmic twist automorphism
`[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` of the punctured torus family `Y* → {φ ≠ 0}`.
Although `log (φ y)` is only locally single-valued, shifting the branch of the logarithm by
`2πi k` (`k ∈ ℤ`) shifts the fibre coordinate by `k • P y μ ∈ P y (Λ)`, so the automorphism is
globally well-defined and locally given by any `C^n` (or holomorphic) branch of `log ∘ φ`.

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

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, and A. Van de Ven, *Compact Complex Surfaces*, 2nd ed.,
  Springer, 2004, Ch. V, §13 (logarithmic transformations of torus families).
* K. Kodaira, *On compact analytic surfaces III*, Ann. of Math. **78** (1963), 1–40, §11.
-/

public section

open Complex Real TopologicalSpace
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
  have hφ : φ y ≠ 0 := hL ▸ Complex.exp_ne_zero L
  have hexp : exp (log (φ y)) = exp L := (Complex.exp_log hφ).trans hL.symm
  rw [torusFamilyLogTwistMap_mk]
  exact torusFamily_mk_add_div_two_pi_I_smul_eq_of_exp_eq P μ hexp y e

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
      torusFamilyLogTwistMap φ P μ y.val := (rfl)

/-- The punctured logarithmic twist for `0 : Λ` is the identity. -/
@[simp] theorem torusFamilyLogTwistEquiv_zero :
    torusFamilyLogTwistEquiv φ P 0 = Equiv.refl _ := by
  simp only [torusFamilyLogTwistEquiv, torusFamilyLogTwistMap_zero, Equiv.subtypeEquiv_refl]

/-- Composing punctured logarithmic twists adds their period parameters. -/
@[simp] theorem torusFamilyLogTwistEquiv_trans (μ₁ μ₂ : Λ) :
    (torusFamilyLogTwistEquiv φ P μ₁).trans (torusFamilyLogTwistEquiv φ P μ₂) =
      torusFamilyLogTwistEquiv φ P (μ₁ + μ₂) := by
  simp only [torusFamilyLogTwistEquiv, Equiv.subtypeEquiv_trans, torusFamilyLogTwistMap_trans]

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
    torusFamilyProjection P (torusFamilyLogTwistEquiv φ P μ y).val =
      torusFamilyProjection P y.val :=
  torusFamilyProjection_torusFamilyLogTwistMap φ P μ y.val

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
  let _ := torusFamilyTranslationAddAction P
  have := contMDiffVAdd_torusFamilyTranslationAddAction P hinj hP
  let y₀ := torusFamilyProjection P x
  let L : Y → ℂ := fun y ↦ log (φ y₀) + log (φ y / φ y₀)
  have hL : ContMDiffAt I 𝓘(ℂ) n L y₀ :=
    (contDiffAt_log_add_log_div hx).contMDiffAt.comp y₀ hφ.contMDiffAt
  have hproj : ContMDiff (I.prod 𝓘(ℂ, E)) I n (torusFamilyProjection P) :=
    contMDiff_torusFamilyProjection P hinj hP
  let g : AddAction.orbitRel.Quotient Λ (Y × E) →
      AddAction.orbitRel.Quotient Λ (Y × E) := fun x' ↦
    (L (torusFamilyProjection P x') / (2 * π * Complex.I)) •
      P (torusFamilyProjection P x') μ +ᵥ x'
  have hg_mk (y : Y) (e : E) :
      g (Quotient.mk _ (y, e)) =
        Quotient.mk _ (y, e + (L y / (2 * π * Complex.I)) • P y μ) := by
    dsimp only [g]
    rw [torusFamilyProjection_mk, torusFamilyTranslationAddAction_vadd_mk, add_comm]
  have hg : ContMDiffAt (I.prod 𝓘(ℂ, E)) (I.prod 𝓘(ℂ, E)) n g x :=
    (((hL.comp x hproj.contMDiffAt).div_const (2 * π * Complex.I)).smul
      ((hP μ).comp hproj).contMDiffAt).vadd contMDiffAt_id
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [(torusFamilyNonzeroOpens φ P hφ.continuous).isOpen.mem_nhds hx] with x' hx'
  obtain ⟨⟨y, e⟩, rfl⟩ := Quotient.exists_rep x'
  have hx'y : φ y ≠ 0 := by
    have h : φ (torusFamilyProjection P ⟦(y, e)⟧) ≠ 0 := hx'
    rwa [torusFamilyProjection_mk] at h
  rw [hg_mk, torusFamilyLogTwistMap_mk_of_exp_eq φ P μ (exp_log_add_log_div hx hx'y) e]

/-- The punctured logarithmic twist is `C^n` on the open submanifold `{φ ∘ p ≠ 0}`. -/
private theorem contMDiff_torusFamilyLogTwistEquiv (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    ContMDiff (I.prod 𝓘(ℂ, E)) (I.prod 𝓘(ℂ, E)) n (torusFamilyLogTwistEquiv φ P μ) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let U := torusFamilyNonzeroOpens φ P hφ.continuous
  let _ := Opens.instChartedSpace (H := ModelProd H E) U
  refine (ContMDiff.subtypeVal_comp_iff U _).1 fun y ↦ ?_
  have hcomp : (Subtype.val : U → _) ∘ torusFamilyLogTwistEquiv φ P μ =
      torusFamilyLogTwistMap φ P μ ∘ (Subtype.val : U → _) :=
    funext fun z ↦ coe_torusFamilyLogTwistEquiv φ P μ z
  rw [hcomp]
  exact (contMDiffAt_subtype_iff (U := U) (x := y)).2
    (contMDiffAt_torusFamilyLogTwistMap φ P hinj hφ hP μ y.property)

/-- **The logarithmic twist diffeomorphism.** For a `C^n` period family `P` over `Y` and a `C^n`
function `φ : Y → ℂ`, each lattice element `μ : Λ` defines a `C^n` automorphism
`[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` of the punctured open submanifold `{φ ∘ p ≠ 0}` over
`Y`. For holomorphic input (`n = ω`), this is a biholomorphism over `{φ ≠ 0}`. -/
noncomputable def torusFamilyLogTwistDiffeomorph (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    Diffeomorph (I.prod 𝓘(ℂ, E)) (I.prod 𝓘(ℂ, E))
      (torusFamilyNonzeroOpens φ P hφ.continuous)
      (torusFamilyNonzeroOpens φ P hφ.continuous) n :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  letI := Opens.instChartedSpace (H := ModelProd H E)
    (torusFamilyNonzeroOpens φ P hφ.continuous)
  { toEquiv := torusFamilyLogTwistEquiv φ P μ
    contMDiff_toFun := contMDiff_torusFamilyLogTwistEquiv φ P hinj hφ hP μ
    contMDiff_invFun := by
      rw [torusFamilyLogTwistEquiv_symm]
      exact contMDiff_torusFamilyLogTwistEquiv φ P hinj hφ hP (-μ) }

/-- The logarithmic twist diffeomorphism has underlying equivalence `torusFamilyLogTwistEquiv`. -/
@[simp] theorem torusFamilyLogTwistDiffeomorph_toEquiv (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ).toEquiv =
      torusFamilyLogTwistEquiv φ P μ := (rfl)

/-- Coercing `torusFamilyLogTwistDiffeomorph` to a function gives `torusFamilyLogTwistEquiv`. -/
@[simp] theorem coe_torusFamilyLogTwistDiffeomorph (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    ⇑(torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ) =
      torusFamilyLogTwistEquiv φ P μ := (rfl)

/-- The logarithmic twist diffeomorphism for `0 : Λ` is the identity. -/
@[simp] theorem torusFamilyLogTwistDiffeomorph_zero :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    torusFamilyLogTwistDiffeomorph φ P hinj hφ hP 0 = Diffeomorph.refl _ _ _ := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := Opens.instChartedSpace (H := ModelProd H E)
    (torusFamilyNonzeroOpens φ P hφ.continuous)
  exact Diffeomorph.toEquiv_injective (torusFamilyLogTwistEquiv_zero φ P)

/-- Composing logarithmic twist diffeomorphisms adds their period parameters. -/
@[simp] theorem torusFamilyLogTwistDiffeomorph_trans (μ₁ μ₂ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ₁).trans
        (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ₂) =
      torusFamilyLogTwistDiffeomorph φ P hinj hφ hP (μ₁ + μ₂) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := Opens.instChartedSpace (H := ModelProd H E)
    (torusFamilyNonzeroOpens φ P hφ.continuous)
  exact Diffeomorph.toEquiv_injective (torusFamilyLogTwistEquiv_trans φ P μ₁ μ₂)

/-- The inverse of a logarithmic twist diffeomorphism negates its period parameter. -/
@[simp] theorem torusFamilyLogTwistDiffeomorph_symm (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ).symm =
      torusFamilyLogTwistDiffeomorph φ P hinj hφ hP (-μ) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := Opens.instChartedSpace (H := ModelProd H E)
    (torusFamilyNonzeroOpens φ P hφ.continuous)
  exact Diffeomorph.toEquiv_injective (torusFamilyLogTwistEquiv_symm φ P μ)

/-- The logarithmic twist diffeomorphism preserves the family projection to `Y`. -/
theorem torusFamilyProjection_torusFamilyLogTwistDiffeomorph (μ : Λ)
    (y : torusFamilyNonzeroOpens φ P hφ.continuous) :
    torusFamilyProjection P (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ y).val =
      torusFamilyProjection P y.val :=
  torusFamilyProjection_torusFamilyLogTwistEquiv φ P μ y

end LogTwistDiffeomorph

end TauCeti
