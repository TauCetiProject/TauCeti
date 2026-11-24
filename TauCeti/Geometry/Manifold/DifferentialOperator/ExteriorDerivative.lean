/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The exterior derivative as a differential operator between form bundles

Real differential `k`-forms on a smooth manifold `M` are the smooth sections of the bundle
`Λᵏ T*M` with fibres `T_x M [⋀^Fin k]→L[ℝ] ℝ`. The exterior derivative
`d : Γ(Λᵏ T*M) → Γ(Λᵏ⁺¹ T*M)` (`TauCeti.mextDerivSection`) is the manifold exterior derivative
`TauCeti.mextDerivₗ` of smooth forms, read on these sections. This file places it in the theory of
differential operators between sections of vector bundles, in Grothendieck's sense of iterated
commutators with multiplication by smooth functions (`TauCeti.differentialOperators`), and
computes its principal symbol.

By the Leibniz rule `d (f ω) = df ∧ ω + f dω` (`TauCeti.mextDerivSection_smul_apply`), the
commutator `[d, f]` is exterior multiplication by `df`, which is linear over the smooth
functions, so `d` is a differential operator of order at most one
(`TauCeti.mextDerivSection_mem_differentialOperators_one`); in particular it does not enlarge
supports. Its principal symbol at a covector `ξ ∈ T_x*M`, in the geometric convention, is
exterior multiplication by `ξ`:

`σ_geom(d)(ξ) ω = ξ ∧ ω`

(`TauCeti.sectionPrincipalSymbol_mextDerivSection_apply`), the wedge product
`ContinuousAlternatingMap.pairedWedge` of the `1`-form `ξ` with `ω`, whose degree `1 + k` is
identified with `k + 1`. In the Fourier convention, where `∂ⱼ` has symbol `i ξⱼ`, the symbol is
`i ξ ∧ ·`. Since `d ∘ d = 0` (`TauCeti.mextDerivSection_comp_mextDerivSection`) and principal
symbols multiply under composition, the symbols form a complex, `σ(d)(ξ) ∘ σ(d)(ξ) = 0`
(`TauCeti.sectionPrincipalSymbol_mextDerivSection_comp_sectionPrincipalSymbol_mextDerivSection`):
the symbol sequence of the de Rham complex.

## Main results

* `TauCeti.mextDerivSection`: the exterior derivative on smooth sections of the form bundles.
* `TauCeti.mextDerivSection_smul_apply`: the Leibniz rule `d (f ω) = df ∧ ω + f dω`.
* `TauCeti.mextDerivSection_mem_differentialOperators_one`: `d` is a differential operator of
  order at most one.
* `TauCeti.tsupport_mextDerivSection_apply_subset`: `d` does not enlarge supports.
* `TauCeti.sectionPrincipalSymbol_mextDerivSection_apply`: the principal symbol of `d` at `ξ` is
  `ξ ∧ ·`.
* `TauCeti.mextDerivSection_comp_mextDerivSection`: `d ∘ d = 0`.
* `TauCeti.sectionPrincipalSymbol_mextDerivSection_comp_sectionPrincipalSymbol_mextDerivSection`:
  the principal symbols of `d` form a complex.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Springer GTM 94,
  Chapter 6 (differential operators, their symbols and the de Rham complex).
* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ}

variable (I M) in
/-- **The exterior derivative** `d : Γ(Λᵏ T*M) → Γ(Λᵏ⁺¹ T*M)` on the smooth sections of the
bundles of real differential forms, whose fibre at `x` is `T_x M [⋀^Fin k]→L[ℝ] ℝ`: the manifold
exterior derivative `TauCeti.mextDerivₗ` of the corresponding smooth forms. -/
def mextDerivSection (k : ℕ) :
    Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
        fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯ where
  toFun s := (mextDerivₗ I k (SmoothBundleForm.ofContMDiffSection s)).toContMDiffSection
  map_add' s t := by
    ext x : 1
    simp
  map_smul' c s := by
    ext x : 1
    simp

/-- The value of `d s` at `x` is the manifold exterior derivative of `s` at `x`. -/
@[simp]
theorem mextDerivSection_apply
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) :
    mextDerivSection I M k s x = mextDeriv (⇑s) x := by
  simp [mextDerivSection, mextDerivₗ_apply]

/-- `d ∘ d = 0` on the smooth sections of the form bundles. -/
@[simp]
theorem mextDerivSection_comp_mextDerivSection :
    mextDerivSection I M (k + 1) ∘ₗ mextDerivSection I M k = 0 := by
  ext s x : 2
  have hds : ⇑(mextDerivSection I M k s) = mextDeriv ⇑s := funext (mextDerivSection_apply s)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, ContMDiffSection.coe_zero, Pi.zero_apply,
    mextDerivSection_apply, hds]
  simpa using congrFun (SmoothForm.mextDeriv_mextDeriv (SmoothBundleForm.ofContMDiffSection s)) x

/-- **The Leibniz rule** `d (f ω) = df ∧ ω + f dω` for a smooth function `f` and a smooth section
`ω` of `Λᵏ T*M`, evaluated on tangent vectors: `df ∧ ω` is the wedge of the `1`-form
`(df)ₓ` with `ω(x)`, whose degree `1 + k` is identified with `k + 1`. -/
theorem mextDerivSection_smul_apply (f : C^∞⟮I, M; ℝ⟯)
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) (v : Fin (k + 1) → TangentSpace I x) :
    mextDerivSection I M k (f • s) x v =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)
            (mvfderiv I f x)) (s x) (v ∘ Fin.cast (Nat.add_comm 1 k)) +
        f x * mextDerivSection I M k s x v := by
  have h := SmoothForm.mextDerivₗ_funSMulₗ_apply f (SmoothBundleForm.ofContMDiffSection s) x v
  rw [RoughForm.wedge_def, RoughForm.wedgeWith_apply', mextDeriv_ofFunction] at h
  have hfs : ⇑(f • s) = fun y ↦ f y • s y := funext (ContMDiffSection.smul_apply f s)
  simpa [mextDerivₗ_apply, hfs] using h

variable (I M k) in
/-- **The exterior derivative is a differential operator of order at most one**: by the Leibniz
rule, its commutator with multiplication by a smooth function `f` is exterior multiplication by
`df`, which is linear over the smooth functions. -/
theorem mextDerivSection_mem_differentialOperators_one :
    mextDerivSection I M k ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯
      Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
        fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun a ↦
    mem_differentialOperators_zero_iff.2 fun b s ↦ ContMDiffSection.ext fun x ↦ ?_
  ext v
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, mextDerivSection_smul_apply, smul_eq_mul,
    ContinuousAlternatingMap.pairedWedge_smul_right]
  ring

/-- The exterior derivative does not enlarge supports. -/
theorem tsupport_mextDerivSection_apply_subset [FiniteDimensional ℝ E] [T2Space M]
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯) :
    (mextDerivSection I M k s).tsupport ⊆ s.tsupport :=
  tsupport_differentialOperators_section_apply_subset
    (mextDerivSection_mem_differentialOperators_one I M k) s

section PrincipalSymbol

variable [FiniteDimensional ℝ E] [T2Space M] {x : M}

/-- **The principal symbol of the exterior derivative** at a covector `ξ ∈ T_x*M` is exterior
multiplication by `ξ`, `σ_geom(d)(ξ) α = ξ ∧ α`: the wedge of the `1`-form `ξ` with `α`, whose
degree `1 + k` is identified with `k + 1`. -/
@[simp]
theorem sectionPrincipalSymbol_mextDerivSection_apply (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (α : TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x)
    (v : Fin (k + 1) → TangentSpace I x) :
    sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M k, mextDerivSection_mem_differentialOperators_one I M k⟩ ξ α v =
      ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          (ContinuousLinearMap.mul ℝ ℝ).continuous₂
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1) ξ) α
          (v ∘ Fin.cast (Nat.add_comm 1 k)) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I)
    (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (V := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M ℝ y) ∞ x α
  rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv_of_order_one]
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    mextDerivSection_smul_apply, smul_eq_mul, add_sub_cancel_right]

/-- **The symbols of the de Rham complex form a complex**: since `d ∘ d = 0` and principal symbols
multiply under composition, `σ(d)(ξ) ∘ σ(d)(ξ) = 0`, that is `ξ ∧ ξ ∧ α = 0`. -/
@[simp]
theorem sectionPrincipalSymbol_mextDerivSection_comp_sectionPrincipalSymbol_mextDerivSection
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M (k + 1), mextDerivSection_mem_differentialOperators_one I M (k + 1)⟩
          ξ ∘ₗ
      sectionPrincipalSymbol I hx
        ⟨mextDerivSection I M k, mextDerivSection_mem_differentialOperators_one I M k⟩ ξ = 0 := by
  rw [← sectionPrincipalSymbol_comp]
  simp only [mextDerivSection_comp_mextDerivSection]
  -- The operator `⟨0, _⟩` is the zero element of the submodule of operators of order two.
  exact sectionPrincipalSymbol_zero hx ξ

end PrincipalSymbol

end TauCeti
