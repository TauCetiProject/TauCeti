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
  filter_upwards [(torusFamilyNonzeroOpens φ P hφ.continuous).isOpen.mem_nhds
    (SetLike.mem_coe.2 ((mem_torusFamilyNonzeroOpens φ P hφ.continuous x).2 hx))] with x' hx'
  obtain ⟨⟨y, e⟩, rfl⟩ := Quotient.exists_rep x'
  rw [SetLike.mem_coe, mem_torusFamilyNonzeroOpens, torusFamilyProjection_mk] at hx'
  rw [torusFamilyGauge_mk,
    torusFamilyLogTwistMap_mk_of_exp_eq φ P μ (exp_log_add_log_div hx hx') e]

/-- The punctured logarithmic twist is `C^n` on the open submanifold `{φ ∘ p ≠ 0}`. -/
private theorem contMDiff_torusFamilyLogTwistEquiv (μ : Λ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    ContMDiff (I.prod 𝓘(ℂ, E)) (I.prod 𝓘(ℂ, E)) n
      ((torusFamilyLogTwistMap φ P μ).subtypeEquiv fun y ↦ by
        simp : ↥(torusFamilyNonzeroOpens φ P hφ.continuous) ≃
          ↥(torusFamilyNonzeroOpens φ P hφ.continuous)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let U := torusFamilyNonzeroOpens φ P hφ.continuous
  let _ := Opens.instChartedSpace (H := ModelProd H E) U
  refine (ContMDiff.subtypeVal_comp_iff U _).1 fun y ↦ ?_
  have hcomp : (Subtype.val : U → _) ∘
      ((torusFamilyLogTwistMap φ P μ).subtypeEquiv fun z ↦ by simp [U]) =
      torusFamilyLogTwistMap φ P μ ∘ (Subtype.val : U → _) :=
    funext fun _ ↦ rfl
  rw [hcomp]
  exact (contMDiffAt_subtype_iff (U := U) (x := y)).2
    (contMDiffAt_torusFamilyLogTwistMap φ P hinj hφ hP μ
      ((mem_torusFamilyNonzeroOpens φ P hφ.continuous y.val).1 (SetLike.mem_coe.1 y.property)))

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
  { toEquiv := (torusFamilyLogTwistMap φ P μ).subtypeEquiv fun y ↦ by simp
    contMDiff_toFun := contMDiff_torusFamilyLogTwistEquiv φ P hinj hφ hP μ
    contMDiff_invFun := by
      simp only [Equiv.subtypeEquiv_symm, torusFamilyLogTwistMap_symm]
      exact contMDiff_torusFamilyLogTwistEquiv φ P hinj hφ hP (-μ) }

/-- Coercing `torusFamilyLogTwistDiffeomorph` to the ambient torus family is
`torusFamilyLogTwistMap`. -/
@[simp] theorem coe_torusFamilyLogTwistDiffeomorph (μ : Λ)
    (y : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      letI := Opens.instChartedSpace (H := ModelProd H E)
        (torusFamilyNonzeroOpens φ P hφ.continuous)
      ↥(torusFamilyNonzeroOpens φ P hφ.continuous)) :
    (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ y :
        letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) =
      torusFamilyLogTwistMap φ P μ y.val :=
  (rfl)

/-- Coercing `torusFamilyLogTwistDiffeomorph` to the ambient torus family agrees with
`torusFamilyLogTwistEquiv`. -/
theorem coe_torusFamilyLogTwistDiffeomorph_eq_torusFamilyLogTwistEquiv (μ : Λ)
    (y : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      letI := Opens.instChartedSpace (H := ModelProd H E)
        (torusFamilyNonzeroOpens φ P hφ.continuous)
      ↥(torusFamilyNonzeroOpens φ P hφ.continuous)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    (torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ y :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      (torusFamilyLogTwistEquiv φ P μ
        ⟨y.val, (mem_torusFamilyNonzeroOpens φ P hφ.continuous y.val).1
          (SetLike.mem_coe.1 y.property)⟩ :
        AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := Opens.instChartedSpace (H := ModelProd H E)
    (torusFamilyNonzeroOpens φ P hφ.continuous)
  simp

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
  refine Diffeomorph.ext fun y ↦ Subtype.ext ?_
  simp

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
  refine Diffeomorph.ext fun y ↦ Subtype.ext ?_
  rw [Diffeomorph.coe_trans, Function.comp_apply, coe_torusFamilyLogTwistDiffeomorph,
    coe_torusFamilyLogTwistDiffeomorph, coe_torusFamilyLogTwistDiffeomorph,
    ← Equiv.trans_apply, torusFamilyLogTwistMap_trans]

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
  refine Diffeomorph.ext fun y ↦ Subtype.ext ?_
  rw [coe_torusFamilyLogTwistDiffeomorph, ← Diffeomorph.coe_toEquiv, Diffeomorph.symm_toEquiv]
  simp only [torusFamilyLogTwistDiffeomorph, Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply,
    torusFamilyLogTwistMap_symm]

/-- Coercing `(torusFamilyLogTwistDiffeomorph).symm` to the ambient torus family agrees with
`(torusFamilyLogTwistEquiv).symm`. -/
theorem coe_torusFamilyLogTwistDiffeomorph_symm_eq_torusFamilyLogTwistEquiv_symm (μ : Λ)
    (y : letI := periodAddAction P
      letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
      letI := Opens.instChartedSpace (H := ModelProd H E)
        (torusFamilyNonzeroOpens φ P hφ.continuous)
      ↥(torusFamilyNonzeroOpens φ P hφ.continuous)) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    letI := Opens.instChartedSpace (H := ModelProd H E)
      (torusFamilyNonzeroOpens φ P hφ.continuous)
    ((torusFamilyLogTwistDiffeomorph φ P hinj hφ hP μ).symm y :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      ((torusFamilyLogTwistEquiv φ P μ).symm
        ⟨y.val, (mem_torusFamilyNonzeroOpens φ P hφ.continuous y.val).1
          (SetLike.mem_coe.1 y.property)⟩ :
        AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  let _ := Opens.instChartedSpace (H := ModelProd H E)
    (torusFamilyNonzeroOpens φ P hφ.continuous)
  simp

end LogTwistDiffeomorph

end TauCeti
