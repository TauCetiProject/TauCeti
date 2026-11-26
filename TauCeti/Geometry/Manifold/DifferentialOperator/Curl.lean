/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.Curl
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The curl as a differential operator on one-forms

On an oriented Riemannian manifold `M` of dimension `3`, the curl `curl α = ⋆dα` of smooth real
one-forms (`TauCeti.SmoothForm.curl`) acts on the smooth sections of the bundle `T*M = Λ¹ T*M`
(`TauCeti.curlSection`). This file places it in the theory of differential operators between
sections of vector bundles, in Grothendieck's sense of iterated commutators with multiplication by
smooth functions (`TauCeti.differentialOperators`), and computes its principal symbol, as is done
for the exterior derivative and the codifferential in
`TauCeti.Geometry.Manifold.DifferentialOperator.ExteriorDerivative` and
`TauCeti.Geometry.Manifold.DifferentialOperator.Codifferential`.

By the Leibniz rule `curl (f α) = f curl α + ⋆(df ∧ α)` (`TauCeti.curlSection_smul_apply`), the
commutator `[curl, f]` is the fibrewise map `⋆(df ∧ ·)`, so the curl is a differential operator of
order at most one (`TauCeti.curlSection_mem_differentialOperators_one`). Its principal symbol at a
covector `ξ ∈ T_x*M`, in the geometric convention, is

`σ_geom(curl)(ξ) α = ⋆(ξ ∧ α)`

(`TauCeti.sectionPrincipalSymbol_curlSection_apply`), the cross product with `ξ` on `ℝ³`; in the
Fourier convention it is `i ⋆(ξ ∧ ·)`. Since `ξ ∧ ξ = 0`, this symbol kills `ξ` itself
(`TauCeti.sectionPrincipalSymbol_curlSection_apply_self`), so the curl is not elliptic: its symbol
is not injective at any nonzero covector.

## Main definitions

* `TauCeti.curlSection`: the curl `Γ(T*M) → Γ(T*M)` of an oriented Riemannian three-manifold.

## Main results

* `TauCeti.curlSection_smul_apply`: the Leibniz rule `curl (f α) = f curl α + ⋆(df ∧ α)`.
* `TauCeti.curlSection_mem_differentialOperators_one`: the curl has order at most one.
* `TauCeti.sectionPrincipalSymbol_curlSection_apply`: its principal symbol at `ξ` is `⋆(ξ ∧ ·)`.
* `TauCeti.sectionPrincipalSymbol_curlSection_apply_self`: the symbol at `ξ` kills `ξ`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1 and Exercise 6.2.
* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §19 (local operators and their symbols).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin 3))

/-- **The curl** `Γ(T*M) → Γ(T*M)` on the smooth sections of the bundle of real one-forms of an
oriented Riemannian three-manifold, whose fibre at `x` is `T_x M [⋀^Fin 1]→L[ℝ] ℝ`: the curl
`TauCeti.SmoothForm.curl` of the corresponding smooth one-forms. -/
def curlSection :
    Cₛ^∞⟮I; E [⋀^Fin 1]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; E [⋀^Fin 1]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x⟯ where
  toFun s := (SmoothForm.curl o (SmoothBundleForm.ofContMDiffSection s)).toContMDiffSection
  map_add' s t := by
    ext x : 1
    simp
  map_smul' c s := by
    ext x : 1
    simp

/-- The value of `curl s` at `x` is the value of the curl of the smooth one-form `s`. -/
@[simp]
theorem curlSection_apply
    (s : Cₛ^∞⟮I; E [⋀^Fin 1]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) :
    curlSection o s x = (SmoothForm.curl o (SmoothBundleForm.ofContMDiffSection s)).val x :=
  SmoothForm.toContMDiffSection_apply _ x

/-- **The Leibniz rule for the curl** `curl (f α) = f curl α + ⋆(df ∧ α)` for a smooth function `f`
and a smooth section `α` of `T*M`, where `df` at `x` is the one-form `mvfderiv I f x`. -/
theorem curlSection_smul_apply (f : C^∞⟮I, M; ℝ⟯)
    (s : Cₛ^∞⟮I; E [⋀^Fin 1]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) :
    curlSection o (f • s) x =
      f x • curlSection o s x + formHodgeStarCLM o (k := 2) (l := 1) rfl x
        ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)
          (mvfderiv I f x)).wedge (s x)) := by
  rw [curlSection_apply, curlSection_apply, SmoothForm.ofContMDiffSection_smul_eq_funSMulₗ,
    ← mextDeriv_ofFunction]
  simpa only [SmoothBundleForm.coe_ofContMDiffSection] using
    congrFun (SmoothForm.coe_curl_funSMulₗ o f (SmoothBundleForm.ofContMDiffSection s)) x

/-- **The curl is a differential operator of order at most one**: by the Leibniz rule, its
commutator with multiplication by a smooth function `f` is `⋆(df ∧ ·)`, which is linear over the
smooth functions. -/
theorem curlSection_mem_differentialOperators_one :
    curlSection o ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E [⋀^Fin 1]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x⟯
      Cₛ^∞⟮I; E [⋀^Fin 1]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun a ↦
    mem_differentialOperators_zero_iff.2 fun b s ↦ ContMDiffSection.ext fun x ↦ ?_
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, curlSection_smul_apply,
    ContinuousAlternatingMap.wedge_smul_right, map_smul]
  module

/-- **The principal symbol of the curl** at a covector `ξ ∈ T_x*M` is
`σ_geom(curl)(ξ) α = ⋆(ξ ∧ α)`, the Hodge star of the wedge of the one-form `ξ` with `α`: the cross
product with `ξ`. -/
@[simp]
theorem sectionPrincipalSymbol_curlSection_apply [T2Space M] {x : M} (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (α : TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) :
    sectionPrincipalSymbol I hx ⟨curlSection o, curlSection_mem_differentialOperators_one o⟩ ξ α =
      formHodgeStarCLM o (k := 2) (l := 1) rfl x
        ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1) ξ).wedge
          α) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I)
    (F := E [⋀^Fin 1]→L[ℝ] ℝ)
    (V := fun y : M ↦ TangentSpace I y [⋀^Fin 1]→L[ℝ] Trivial M ℝ y) ∞ x α
  rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv_of_order_one,
    curlSection_smul_apply, add_sub_cancel_left]

/-- **The curl is not elliptic**: its principal symbol at a covector `ξ` kills the one-form `ξ`
itself, since `ξ ∧ ξ = 0`. So the symbol is not injective at any nonzero covector. -/
theorem sectionPrincipalSymbol_curlSection_apply_self [T2Space M] {x : M} (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx ⟨curlSection o, curlSection_mem_differentialOperators_one o⟩ ξ
      (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1) ξ) = 0 := by
  rw [sectionPrincipalSymbol_curlSection_apply, ContinuousAlternatingMap.wedge_self_of_odd odd_one,
    map_zero]

end TauCeti
