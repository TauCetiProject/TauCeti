/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.ExteriorDerivative
public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The codifferential and the Hodge Laplacian as differential operators between form bundles

Let `M` be an oriented Riemannian manifold of dimension `m`. Real differential `k`-forms on `M`
are the smooth sections of the bundle `Λᵏ T*M` with fibres `T_x M [⋀^Fin k]→L[ℝ] ℝ`. The
codifferential `d* = ± ⋆ d ⋆` and the Hodge Laplacian `Δ = d*d + dd*` of smooth forms
(`TauCeti.SmoothForm.codifferential`, `TauCeti.SmoothForm.hodgeLaplacian`) act on these sections
(`TauCeti.codifferentialSection`, `TauCeti.hodgeLaplacianSection`). This file places them in the
theory of differential operators between sections of vector bundles, in Grothendieck's sense of
iterated commutators with multiplication by smooth functions (`TauCeti.differentialOperators`),
and computes their principal symbols, as is done for the exterior derivative in
`TauCeti.Geometry.Manifold.DifferentialOperator.ExteriorDerivative`.

By the Leibniz rule `d*(f β) = f d*β - ι_(grad f) β` (`TauCeti.codifferentialSection_smul_apply`),
the commutator `[d*, f]` is the contraction `-ι_(grad f)`, which is linear over the smooth
functions, so `d*` is a differential operator of order at most one
(`TauCeti.codifferentialSection_mem_differentialOperators_one`). Its principal symbol at a
covector `ξ ∈ T_x*M`, in the geometric convention, is minus the contraction with the vector `ξ♯`
dual to `ξ` for the metric (`TauCeti.sectionPrincipalSymbol_codifferentialSection_apply`):

`σ_geom(d*)(ξ) β = -ι_(ξ♯) β`.

The double commutator of the Hodge Laplacian with multiplication by smooth functions `f` and `g`
is multiplication by `-2 ⟪grad f, grad g⟫`
(`TauCeti.smulCommutator_smulCommutator_hodgeLaplacianSection_apply`). So `Δ` is a differential
operator of order at most two (`TauCeti.hodgeLaplacianSection_mem_differentialOperators_two`)
with geometric principal symbol `-‖ξ‖² Id`, the norm being the one the metric induces on `T_x*M`
(`TauCeti.sectionPrincipalSymbol_hodgeLaplacianSection`). In the Fourier convention, where `∂ⱼ`
has symbol `i ξⱼ`, this is `‖ξ‖² Id`: the Hodge Laplacian is of Laplace type with constant `1`
(`TauCeti.isSectionLaplaceType_hodgeLaplacianSection`), and in particular elliptic, in every
degree, including degree `0`, where it is `d*d`, and the top degree, where it is `dd*`.

## Main definitions

* `TauCeti.codifferentialSection`: the codifferential `d* : Γ(Λᵏ⁺¹ T*M) → Γ(Λᵏ T*M)`.
* `TauCeti.hodgeLaplacianSection`: the Hodge Laplacian `Δ : Γ(Λᵏ T*M) → Γ(Λᵏ T*M)`.

## Main results

* `TauCeti.ofContMDiffSection_codifferentialSection`,
  `TauCeti.ofContMDiffSection_hodgeLaplacianSection`: `d*` and `Δ` on sections are the
  codifferential and the Hodge Laplacian of the corresponding smooth forms.
* `TauCeti.codifferentialSection_comp_codifferentialSection`: `d* ∘ d* = 0` on sections.
* `TauCeti.codifferentialSection_smul_apply`: the Leibniz rule `d*(f β) = f d*β - ι_(grad f) β`.
* `TauCeti.codifferentialSection_mem_differentialOperators_one`: `d*` has order at most one.
* `TauCeti.sectionPrincipalSymbol_codifferentialSection_apply`: the principal symbol of `d*` at
  `ξ` is `-ι_(ξ♯)`.
* `TauCeti.smulCommutator_smulCommutator_hodgeLaplacianSection_apply`:
  `[[Δ, f], g] = -2 ⟪grad f, grad g⟫`.
* `TauCeti.hodgeLaplacianSection_mem_differentialOperators_two`: `Δ` has order at most two.
* `TauCeti.sectionPrincipalSymbol_hodgeLaplacianSection`: the principal symbol of `Δ` at `ξ` is
  `-‖ξ‖² Id`.
* `TauCeti.isSectionLaplaceType_hodgeLaplacianSection`: `Δ` is of Laplace type with constant `1`.
* `TauCeti.hodgeLaplacianSection_add_one_add_one_eq_comp_add_comp`: `Δ = d* ∘ d + d ∘ d*` on
  sections, with `Δ = d* ∘ d` in degree `0` and `Δ = d ∘ d*` in the top degree.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Springer GTM 94,
  Chapter 6 (differential operators, their symbols and the Hodge Laplacian).
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992, §2.1
  (generalized Laplacians).
-/

public section

noncomputable section

open Bundle Riemannian.Tensor
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {m k l : ℕ}

/-! ### Transporting operators on forms to operators on sections -/

/-- If the operator `P` on sections of the form bundles is the operator `L` on smooth forms, then
its commutator with multiplication by `f` is the commutator `L ∘ f - f ∘ L`. -/
private theorem ofContMDiffSection_smulCommutator {i j : ℕ}
    {P : Cₛ^∞⟮I; E [⋀^Fin i]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin i]→L[ℝ] Trivial M ℝ x⟯
      →ₗ[ℝ] Cₛ^∞⟮I; E [⋀^Fin j]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin j]→L[ℝ] Trivial M ℝ x⟯}
    {L : SmoothForm I M ℝ i →ₗ[ℝ] SmoothForm I M ℝ j}
    (hPL : ∀ s, SmoothBundleForm.ofContMDiffSection (P s) =
      L (SmoothBundleForm.ofContMDiffSection s))
    (f : C^∞⟮I, M; ℝ⟯)
    (s : Cₛ^∞⟮I; E [⋀^Fin i]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin i]→L[ℝ] Trivial M ℝ x⟯) :
    SmoothBundleForm.ofContMDiffSection (smulCommutator ℝ f P s) =
      (L ∘ₗ SmoothForm.funSMulₗ f - SmoothForm.funSMulₗ f ∘ₗ L)
        (SmoothBundleForm.ofContMDiffSection s) := by
  have hP (t) (x : M) : P t x = (L (SmoothBundleForm.ofContMDiffSection t)).val x := by
    rw [← hPL, SmoothBundleForm.coe_ofContMDiffSection]
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [SmoothBundleForm.coe_ofContMDiffSection, smulCommutator_apply_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.smul_apply, hP, hP,
    SmoothBundleForm.ofContMDiffSection_smul_eq_funSMulₗ]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Submodule.coe_sub, Pi.sub_apply,
    SmoothForm.coe_funSMulₗ]

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### The codifferential -/

section Codifferential

variable (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)

/-- **The codifferential** `d* : Γ(Λᵏ⁺¹ T*M) → Γ(Λᵏ T*M)` on the smooth sections of the bundles of
real differential forms of an oriented Riemannian manifold of dimension `m = k + 1 + l`, whose fibre
at `x` is `T_x M [⋀^Fin (k + 1)]→L[ℝ] ℝ`: the codifferential `TauCeti.SmoothForm.codifferential`
of the corresponding smooth forms. -/
def codifferentialSection :
    Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
        fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯ where
  toFun s :=
    (SmoothForm.codifferential o hkl (SmoothBundleForm.ofContMDiffSection s)).toContMDiffSection
  map_add' s t := by
    ext x : 1
    simp
  map_smul' c s := by
    ext x : 1
    simp

/-- The value of `d* s` at `x` is the value of the codifferential of the smooth form `s`. -/
@[simp]
theorem codifferentialSection_apply
    (s : Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯) (x : M) :
    codifferentialSection o hkl s x =
      (SmoothForm.codifferential o hkl (SmoothBundleForm.ofContMDiffSection s)).val x :=
  SmoothForm.toContMDiffSection_apply _ x

/-- The section `d* s` is the codifferential of the smooth form `s`. -/
@[simp]
theorem ofContMDiffSection_codifferentialSection
    (s : Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯) :
    SmoothBundleForm.ofContMDiffSection (codifferentialSection o hkl s) =
      SmoothForm.codifferential o hkl (SmoothBundleForm.ofContMDiffSection s) :=
  Subtype.ext (funext fun x ↦ by
    rw [SmoothBundleForm.coe_ofContMDiffSection, codifferentialSection_apply])

/-- `d* ∘ d* = 0` on the smooth sections of the form bundles. -/
@[simp]
theorem codifferentialSection_comp_codifferentialSection {l' : ℕ} (hkl' : k + 1 + 1 + l' = m) :
    codifferentialSection o hkl ∘ₗ codifferentialSection o hkl' = 0 := by
  ext s x : 2
  simp [SmoothForm.codifferential_codifferential]

/-- `d* (d* s) = 0` for every smooth section `s` of the form bundle. -/
@[simp]
theorem codifferentialSection_codifferentialSection {l' : ℕ} (hkl' : k + 1 + 1 + l' = m)
    (s : Cₛ^∞⟮I; E [⋀^Fin (k + 1 + 1)]→L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1 + 1)]→L[ℝ] Trivial M ℝ x⟯) :
    codifferentialSection o hkl (codifferentialSection o hkl' s) = 0 :=
  LinearMap.congr_fun (codifferentialSection_comp_codifferentialSection o hkl hkl') s

/-- **The Leibniz rule for the codifferential** `d*(f β) = f d*β - ι_(grad f) β` for a smooth
function `f` and a smooth section `β` of `Λᵏ⁺¹ T*M`, evaluated on tangent vectors: the contraction
`ι_(grad f) β` inserts the gradient of `f` into the first slot of `β`. -/
theorem codifferentialSection_smul_apply (f : C^∞⟮I, M; ℝ⟯)
    (s : Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) (v : Fin k → TangentSpace I x) :
    codifferentialSection o hkl (f • s) x v =
      f x * codifferentialSection o hkl s x v -
        s x (Matrix.vecCons (Manifold.mgradient I f x) v) := by
  have h := DFunLike.congr_fun (congrFun
    (SmoothForm.coe_codifferential_funSMulₗ o hkl f (SmoothBundleForm.ofContMDiffSection s)) x) v
  rw [codifferentialSection_apply, codifferentialSection_apply,
    SmoothBundleForm.ofContMDiffSection_smul_eq_funSMulₗ]
  simpa using h

/-- **The codifferential is a differential operator of order at most one**: by the Leibniz rule,
its commutator with multiplication by a smooth function `f` is the contraction `-ι_(grad f)`,
which is linear over the smooth functions. -/
theorem codifferentialSection_mem_differentialOperators_one :
    codifferentialSection o hkl ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
        fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯
      Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯ 1 := by
  refine mem_differentialOperators_succ_iff.2 fun a ↦
    mem_differentialOperators_zero_iff.2 fun b s ↦ ContMDiffSection.ext fun x ↦ ?_
  ext v
  simp only [smulCommutator_apply_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, codifferentialSection_smul_apply, smul_eq_mul]
  ring

/-- The codifferential does not enlarge supports. -/
theorem tsupport_codifferentialSection_apply_subset [T2Space M]
    (s : Cₛ^∞⟮I; E [⋀^Fin (k + 1)]→L[ℝ] ℝ,
      fun x : M ↦ TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x⟯) :
    (codifferentialSection o hkl s).tsupport ⊆ s.tsupport :=
  tsupport_differentialOperators_section_apply_subset
    (codifferentialSection_mem_differentialOperators_one o hkl) s

/-- **The principal symbol of the codifferential** at a covector `ξ ∈ T_x*M` is minus the
contraction with the vector `ξ♯` dual to `ξ` for the metric, `σ_geom(d*)(ξ) β = -ι_(ξ♯) β`:
`ξ♯` is inserted into the first slot of `β`. -/
@[simp]
theorem sectionPrincipalSymbol_codifferentialSection_apply [T2Space M] {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ)
    (β : TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ x) (v : Fin k → TangentSpace I x) :
    sectionPrincipalSymbol I hx
        ⟨codifferentialSection o hkl,
          codifferentialSection_mem_differentialOperators_one o hkl⟩ ξ β v =
      -β (Matrix.vecCons (rieszDual x ξ) v) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I)
    (F := E [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (V := fun y : M ↦ TangentSpace I y [⋀^Fin (k + 1)]→L[ℝ] Trivial M ℝ y) ∞ x β
  rw [ContMDiffSection.evalLinearMap_apply, sectionPrincipalSymbol_mvfderiv_of_order_one,
    ← Manifold.mgradient_def]
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    codifferentialSection_smul_apply, smul_eq_mul]
  ring

end Codifferential

/-! ### The Hodge Laplacian -/

section HodgeLaplacian

variable (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)

/-- **The Hodge Laplacian** `Δ = d*d + dd* : Γ(Λᵏ T*M) → Γ(Λᵏ T*M)` on the smooth sections of the
bundle of real differential `k`-forms of an oriented Riemannian manifold of dimension `m = k + l`:
the Hodge Laplacian `TauCeti.SmoothForm.hodgeLaplacian` of the corresponding smooth forms. -/
def hodgeLaplacianSection :
    Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯ where
  toFun s :=
    (SmoothForm.hodgeLaplacian o hkl (SmoothBundleForm.ofContMDiffSection s)).toContMDiffSection
  map_add' s t := by
    ext x : 1
    simp
  map_smul' c s := by
    ext x : 1
    simp

/-- The value of `Δ s` at `x` is the value of the Hodge Laplacian of the smooth form `s`. -/
@[simp]
theorem hodgeLaplacianSection_apply
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) :
    hodgeLaplacianSection o hkl s x =
      (SmoothForm.hodgeLaplacian o hkl (SmoothBundleForm.ofContMDiffSection s)).val x :=
  SmoothForm.toContMDiffSection_apply _ x

/-- The section `Δ s` is the Hodge Laplacian of the smooth form `s`. -/
@[simp]
theorem ofContMDiffSection_hodgeLaplacianSection
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯) :
    SmoothBundleForm.ofContMDiffSection (hodgeLaplacianSection o hkl s) =
      SmoothForm.hodgeLaplacian o hkl (SmoothBundleForm.ofContMDiffSection s) :=
  Subtype.ext (funext fun x ↦ by
    rw [SmoothBundleForm.coe_ofContMDiffSection, hodgeLaplacianSection_apply])

/-- **The double commutator of the Hodge Laplacian** with multiplication by smooth functions is
multiplication by `-2` times the inner product of their gradients:
`[[Δ, f], g] s = -2 ⟪grad f, grad g⟫ s`. -/
theorem smulCommutator_smulCommutator_hodgeLaplacianSection_apply (f g : C^∞⟮I, M; ℝ⟯)
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯)
    (x : M) :
    smulCommutator ℝ g (smulCommutator ℝ f (hodgeLaplacianSection o hkl)) s x =
      -(2 * ⟪Manifold.mgradient I f x, Manifold.mgradient I g x⟫) • s x := by
  have h₂ := ofContMDiffSection_smulCommutator
    (ofContMDiffSection_smulCommutator (ofContMDiffSection_hodgeLaplacianSection o hkl) f) g s
  have h := congrFun (congrArg Subtype.val h₂) x
  have hΔ := congrFun (SmoothForm.coe_lie_lie_hodgeLaplacian_funSMulₗ o hkl f g
    (SmoothBundleForm.ofContMDiffSection s)) x
  simp only [SmoothBundleForm.coe_ofContMDiffSection] at h
  rw [h, ← neg_mul]
  -- The ring commutators `⁅⁅Δ, f⁆, g⁆` of `TauCeti.SmoothForm.coe_lie_lie_hodgeLaplacian_funSMulₗ`
  -- are the composites `(Δ ∘ f - f ∘ Δ) ∘ g - g ∘ (Δ ∘ f - f ∘ Δ)` of linear maps.
  simpa only [Ring.lie_def, Module.End.mul_eq_comp, SmoothBundleForm.coe_ofContMDiffSection]
    using hΔ

/-- The Hodge Laplacian is a differential operator of order at most two on the smooth sections of
the form bundle. -/
theorem hodgeLaplacianSection_mem_differentialOperators_two :
    hodgeLaplacianSection o hkl ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯
      Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯
      Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯ 2 :=
  mem_differentialOperators_two_of_smulCommutator_smulCommutator
    (smulCommutator_smulCommutator_hodgeLaplacianSection_apply o hkl)

/-- The Hodge Laplacian does not enlarge supports. -/
theorem tsupport_hodgeLaplacianSection_apply_subset [T2Space M]
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x⟯) :
    (hodgeLaplacianSection o hkl s).tsupport ⊆ s.tsupport :=
  tsupport_differentialOperators_section_apply_subset
    (hodgeLaplacianSection_mem_differentialOperators_two o hkl) s

/-- **The principal symbol of the Hodge Laplacian.** The geometric principal symbol of
`Δ = d*d + dd*` is `ξ ↦ -‖ξ‖² Id`, the norm being the one the metric induces on `T_x*M`; in the
Fourier convention it is `‖ξ‖² Id`. -/
@[simp]
theorem sectionPrincipalSymbol_hodgeLaplacianSection [T2Space M] {x : M}
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
      ⟨hodgeLaplacianSection o hkl, hodgeLaplacianSection_mem_differentialOperators_two o hkl⟩ ξ =
        -(‖ξ‖ ^ 2) • LinearMap.id :=
  sectionPrincipalSymbol_of_smulCommutator_smulCommutator
    (smulCommutator_smulCommutator_hodgeLaplacianSection_apply o hkl) hx ξ

/-- **The Hodge Laplacian is of Laplace type** with constant `1`: its geometric principal symbol
is `-‖ξ‖² Id`. In particular it is elliptic in every degree. -/
theorem isSectionLaplaceType_hodgeLaplacianSection [T2Space M] :
    IsSectionLaplaceType
      ⟨hodgeLaplacianSection o hkl, hodgeLaplacianSection_mem_differentialOperators_two o hkl⟩ 1 :=
  isSectionLaplaceType_of_smulCommutator_smulCommutator
    (smulCommutator_smulCommutator_hodgeLaplacianSection_apply o hkl)

end HodgeLaplacian

/-! ### The Hodge Laplacian as `d*d + dd*` on sections -/

section Decomposition

variable (o : Manifold.Orientation I M (Fin m))

/-- In positive dimension the Hodge Laplacian on sections of `Λ⁰ T*M` is `Δ = d* ∘ d`. -/
theorem hodgeLaplacianSection_zero_add_one_eq_comp (hkl : 0 + (l + 1) = m)
    (hkl' : 0 + 1 + l = m) :
    hodgeLaplacianSection o hkl = codifferentialSection o hkl' ∘ₗ mextDerivSection I M 0 := by
  refine LinearMap.ext fun s ↦ SmoothBundleForm.ofContMDiffSection_injective ?_
  simp [SmoothForm.hodgeLaplacian_zero_add_one o hkl hkl']

/-- In the top degree the Hodge Laplacian on sections is `Δ = d ∘ d*`. -/
theorem hodgeLaplacianSection_add_one_zero_eq_comp (hkl : k + 1 + 0 = m) :
    hodgeLaplacianSection o hkl = mextDerivSection I M k ∘ₗ codifferentialSection o hkl := by
  refine LinearMap.ext fun s ↦ SmoothBundleForm.ofContMDiffSection_injective ?_
  simp [SmoothForm.hodgeLaplacian_add_one_zero o hkl]

/-- Strictly between degree `0` and the top degree the Hodge Laplacian on sections is
`Δ = d* ∘ d + d ∘ d*`. -/
theorem hodgeLaplacianSection_add_one_add_one_eq_comp_add_comp (hkl : k + 1 + (l + 1) = m)
    (hkl' : k + 1 + 1 + l = m) :
    hodgeLaplacianSection o hkl =
      codifferentialSection o hkl' ∘ₗ mextDerivSection I M (k + 1) +
        mextDerivSection I M k ∘ₗ codifferentialSection o hkl := by
  refine LinearMap.ext fun s ↦ SmoothBundleForm.ofContMDiffSection_injective ?_
  simp [SmoothForm.hodgeLaplacian_add_one_add_one o hkl hkl']

end Decomposition

end TauCeti
