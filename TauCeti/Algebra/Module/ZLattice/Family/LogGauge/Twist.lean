/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Branch
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Branch
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Logarithmic twists on torus families

Over the complement `{φ ≠ 0}` of the zero locus of a `C^n` (or holomorphic) complex function `φ`
on a base manifold `Y`, a period section `μ : Λ` determines the logarithmic twist automorphism
`[y, e] ↦ [y, e + (log (φ y) / 2πi) • P y μ]` of the punctured torus family `Y* → {φ ≠ 0}`
(`TauCeti.torusFamilyLogTwistMap`, `TauCeti.torusFamilyLogTwistEquiv` in
`TauCeti.Algebra.Module.ZLattice.Family.LogGauge.Branch`). Although `log (φ y)` is only locally
single-valued, shifting the branch of the logarithm by `2πi k` (`k ∈ ℤ`) shifts the fibre
coordinate by `k • P y μ ∈ P y (Λ)`, so the automorphism is globally well-defined and locally given
by any `C^n` (or holomorphic) branch of `log ∘ φ`.

## Main definitions and results

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
  let y₀ := torusFamilyProjection P x
  let c : Y → E := fun y ↦ ((log (φ y₀) + log (φ y / φ y₀)) / (2 * π * Complex.I)) • P y μ
  have hL : ContMDiffAt I 𝓘(ℂ) n (fun y ↦ log (φ y₀) + log (φ y / φ y₀)) y₀ :=
    (contDiffAt_log_add_log_div hx).contMDiffAt.comp y₀ hφ.contMDiffAt
  have hc : ContMDiffAt I 𝓘(ℂ, E) n c y₀ :=
    (hL.div_const (2 * π * Complex.I)).smul (hP μ).contMDiffAt
  refine (contMDiffAt_torusFamilyGauge P hinj hP hc).congr_of_eventuallyEq ?_
  filter_upwards [(torusFamilyNonzeroOpens φ P hφ.continuous).isOpen.mem_nhds hx] with x' hx'
  obtain ⟨⟨y, e⟩, rfl⟩ := Quotient.exists_rep x'
  have hx'y : φ y ≠ 0 := by
    have h : φ (torusFamilyProjection P ⟦(y, e)⟧) ≠ 0 := hx'
    rwa [torusFamilyProjection_mk] at h
  rw [torusFamilyGauge_mk,
    torusFamilyLogTwistMap_mk_of_exp_eq φ P μ (exp_log_add_log_div hx hx'y) e]

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
  apply Diffeomorph.toEquiv_injective
  simp only [torusFamilyLogTwistDiffeomorph_toEquiv, Diffeomorph.refl_toEquiv,
    torusFamilyLogTwistEquiv_zero]
  exact Equiv.ext fun _ ↦ rfl

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
  apply Diffeomorph.toEquiv_injective
  simp only [Diffeomorph.trans_toEquiv, torusFamilyLogTwistDiffeomorph_toEquiv]
  exact torusFamilyLogTwistEquiv_trans φ P μ₁ μ₂

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
  apply Diffeomorph.toEquiv_injective
  simp only [Diffeomorph.symm_toEquiv, torusFamilyLogTwistDiffeomorph_toEquiv]
  exact torusFamilyLogTwistEquiv_symm φ P μ

end LogTwistDiffeomorph

end TauCeti
