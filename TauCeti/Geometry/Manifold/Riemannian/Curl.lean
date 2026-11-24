/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# The curl of an oriented Riemannian three-manifold

On an oriented Riemannian manifold `M` of dimension `3`, the *curl* of a smooth one-form `α` is
the one-form

`curl α = ⋆dα`,

the Hodge star of its exterior derivative (`TauCeti.SmoothForm.curl`). Through the musical
isomorphisms it is the curl `∇ × X` of vector fields: on `ℝ³` with the standard metric and
orientation, the one-form `α = a dx + b dy + c dz` has the classical curl
`curl α = (c_y - b_z) dx + (a_z - c_x) dy + (b_x - a_y) dz`. It is one of the model first-order
operators built from `d`, `d*` and `⋆`, alongside the codifferential and the Hodge Laplacian of
`TauCeti.Geometry.Manifold.Riemannian.Codifferential`.

The classical vector-calculus identities are identities of forms:

* `curl (df) = ⋆ddf = 0` (`TauCeti.SmoothForm.curl_mextDerivₗ`): gradients are curl-free;
* `d* (curl α) = 0` (`TauCeti.SmoothForm.codifferential_curl`): curls are divergence-free, where
  `d*` on one-forms is minus the divergence;
* `curl α = d* ⋆α` (`TauCeti.SmoothForm.curl_eq_codifferential_hodgeStar`);
* `curl (curl α) = d* dα` (`TauCeti.SmoothForm.curl_curl`), and hence
  `curl (curl α) = Δα - d d* α` for the Hodge Laplacian `Δ = d*d + dd*`
  (`TauCeti.SmoothForm.curl_curl_add_mextDerivₗ_codifferential`), the form version of
  `∇ × ∇ × X = ∇(∇ · X) - ∇²X`;
* on a boundaryless manifold, `curl` is formally self-adjoint for the `L²` pairing of forms,
  `∫_M ⟨curl α, β⟩ vol = ∫_M ⟨α, curl β⟩ vol` when `α` or `β` is compactly supported
  (`TauCeti.SmoothForm.integralTopForm_inner_curl_eq_inner_curl`);
* reversing the orientation negates the curl (`TauCeti.SmoothForm.curl_neg_orientation`).

## The principal symbol

By the Leibniz rule `d (f α) = f dα + df ∧ α`, the commutator of `curl` with multiplication by a
smooth function `f` is the zeroth-order operator

`[curl, f] α = ⋆(df ∧ α)`

(`TauCeti.SmoothForm.coe_curl_funSMulₗ`). It is multiplication by a smooth tensor, so every double
commutator `[[curl, f], g]` vanishes (`TauCeti.SmoothForm.lie_lie_curl_funSMulₗ`): the curl is a
first-order operator, with geometric principal symbol `σ_geom(curl)(ξ) α = ⋆(ξ ∧ α)` in the
iterated-commutator normalization `σ_geom(P)(df) = [P, f]` of first-order operators, the cross
product `ξ × α` on `ℝ³`. In the Fourier convention `σ(∂ⱼ) = i ξⱼ` its symbol is
`i ⋆(ξ ∧ ·)`. Since `ξ ∧ ξ = 0`, this symbol kills `ξ` itself, so the curl is not elliptic:
concretely `curl (f df) = 0` for every smooth function `f`
(`TauCeti.SmoothForm.curl_funSMulₗ_mextDerivₗ_self`).

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1 and Exercise 6.2.
* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §19 (local operators and their symbols).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

namespace SmoothForm

/-- The curl `curl α = ⋆dα` of a smooth one-form `α` on an oriented Riemannian three-manifold:
the Hodge star of the two-form `dα`, again a one-form. -/
def curl (o : Manifold.Orientation I M (Fin 3)) :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 1 :=
  hodgeStar o (k := 2) (l := 1) rfl ∘ₗ mextDerivₗ I 1

variable (o : Manifold.Orientation I M (Fin 3))

/-- The curl is `⋆d`. -/
theorem curl_apply (α : SmoothForm I M ℝ 1) :
    curl o α = hodgeStar o (k := 2) (l := 1) rfl (mextDerivₗ I 1 α) :=
  (rfl)

/-- The curl at a point is the fibrewise Hodge star of the exterior derivative. -/
theorem coe_curl_apply (α : SmoothForm I M ℝ 1) (x : M) :
    (curl o α).val x = formHodgeStarCLM o (k := 2) (l := 1) rfl x ((mextDerivₗ I 1 α).val x) := by
  rw [curl_apply, coe_hodgeStar, RoughForm.hodgeStar_eq_formHodgeStarCLM]

/-- Reversing the orientation negates the curl. -/
@[simp]
theorem curl_neg_orientation (α : SmoothForm I M ℝ 1) : curl (-o) α = -curl o α := by
  simp only [curl_apply, hodgeStar_neg_orientation]

/-- **Gradients are curl-free**: `curl (df) = ⋆ddf = 0`. -/
@[simp]
theorem curl_mextDerivₗ (f : SmoothForm I M ℝ 0) : curl o (mextDerivₗ I 0 f) = 0 := by
  have h := LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I (M := M) (F := ℝ) 0) f
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [curl_apply, h, map_zero]

/-- **Curls are divergence-free**: `d* (curl α) = 0`, where `d*` on one-forms is minus the
divergence. -/
@[simp]
theorem codifferential_curl (α : SmoothForm I M ℝ 1) :
    codifferential o (k := 0) (l := 2) rfl (curl o α) = 0 := by
  have h := LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I (M := M) (F := ℝ) 1) α
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [codifferential_apply o rfl (by norm_num : 2 + 1 + 0 = 3), curl_apply,
    hodgeStar_hodgeStar, map_smul, h, smul_zero, map_zero, smul_zero]

/-- The curl of a one-form on a three-manifold is `curl α = d* ⋆α`. -/
theorem curl_eq_codifferential_hodgeStar (α : SmoothForm I M ℝ 1) :
    curl o α = codifferential o (k := 1) (l := 1) rfl (hodgeStar o (k := 1) (l := 2) rfl α) := by
  rw [curl_apply, hodgeStar_mextDeriv o (k := 1) (l := 1) rfl rfl rfl α]
  norm_num

/-- **The curl of the curl** is `curl (curl α) = d* dα`. -/
theorem curl_curl (α : SmoothForm I M ℝ 1) :
    curl o (curl o α) = codifferential o (k := 1) (l := 1) rfl (mextDerivₗ I 1 α) := by
  rw [curl_eq_codifferential_hodgeStar, curl_apply, hodgeStar_hodgeStar]
  norm_num

/-- **The curl of the curl and the Hodge Laplacian**: `curl (curl α) + d d* α = Δα` for the Hodge
Laplacian `Δ = d*d + dd*` of one-forms, the form version of `∇ × ∇ × X = ∇(∇ · X) - ∇²X`. -/
theorem curl_curl_add_mextDerivₗ_codifferential (α : SmoothForm I M ℝ 1) :
    curl o (curl o α) + mextDerivₗ I 0 (codifferential o (k := 0) (l := 2) rfl α) =
      hodgeLaplacian o (k := 1) (l := 2) rfl α := by
  rw [curl_curl, hodgeLaplacian_add_one_add_one o (k := 0) (l := 1) rfl rfl]

/-! ### The commutator with functions and the principal symbol -/

/-- **The commutator of the curl with a function**: `curl (f α) = f curl α + ⋆(df ∧ α)`. The
commutator `[curl, f] α = ⋆(df ∧ α)` is the principal symbol of the curl at `df`, the cross
product with `df`. -/
theorem coe_curl_funSMulₗ (f : C^∞⟮I, M; ℝ⟯) (α : SmoothForm I M ℝ 1) :
    (curl o (funSMulₗ f α) : RoughForm I M ℝ 1) = fun x ↦
      f x • (curl o α).val x + formHodgeStarCLM o (k := 2) (l := 1) rfl x
        ((mextDeriv (RoughForm.ofFunction I f) x).wedge (α.val x)) := by
  funext x
  rw [coe_curl_apply, mextDerivₗ_funSMulₗ]
  simp only [Submodule.coe_add, Pi.add_apply, coe_funSMulₗ, map_add, map_smul, coe_curl_apply]
  rw [add_comm]
  congr 2
  ext v
  simp only [extDerivWedgeₗ_apply, RoughForm.wedge_def, RoughForm.wedgeWith_apply', Fin.cast_refl,
    CompTriple.comp_eq, ContinuousAlternatingMap.wedge_def]

/-- **The curl has order one**: its double commutators with multiplication operators vanish,
`[[curl, f], g] = 0`. -/
@[simp]
theorem lie_lie_curl_funSMulₗ (f g : C^∞⟮I, M; ℝ⟯) :
    ⁅⁅curl o, funSMulₗ (F := ℝ) (k := 1) f⁆, funSMulₗ (F := ℝ) (k := 1) g⁆ = 0 := by
  ext α : 1
  refine Subtype.ext (funext fun x ↦ ?_)
  simp only [Ring.lie_def, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.zero_apply,
    Submodule.coe_sub, Submodule.coe_zero, Pi.sub_apply, Pi.zero_apply, coe_curl_funSMulₗ,
    coe_funSMulₗ, map_sub, map_smul, ContinuousAlternatingMap.wedge_smul_right]
  module

/-- **The curl is not elliptic**: its principal symbol `⋆(df ∧ ·)` at `df` kills `df`, that is
`curl (f df) = 0` for every smooth function `f`. -/
@[simp]
theorem curl_funSMulₗ_mextDerivₗ_self (f : C^∞⟮I, M; ℝ⟯) :
    curl o (funSMulₗ f (mextDerivₗ I 0 (ofFunction f))) = 0 := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [coe_curl_funSMulₗ, curl_mextDerivₗ, mextDerivₗ_apply, coe_ofFunction]
  beta_reduce
  rw [ContinuousAlternatingMap.wedge_self_of_odd odd_one, map_zero]
  simp

/-! ### Formal self-adjointness -/

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The curl is formally self-adjoint**: on an oriented boundaryless Riemannian three-manifold,
`∫_M ⟨curl α, β⟩ vol = ∫_M ⟨α, curl β⟩ vol` for smooth one-forms `α` and `β`, one of them
compactly supported. -/
theorem integralTopForm_inner_curl_eq_inner_curl (α β : SmoothForm I M ℝ 1)
    (h : α ∈ compactlySupportedForms I M 1 ∨ β ∈ compactlySupportedForms I M 1) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 1
        ((curl o α).val x) (β.val x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 1
        (α.val x) ((curl o β).val x) • riemannianVolumeForm o x) := by
  -- Pointwise `⟨⋆dα, β⟩ = ⟨⋆⋆dα, ⋆β⟩ = ⟨dα, ⋆β⟩`, since `⋆` is an isometry and `⋆⋆ = 1` on
  -- two-forms.
  have hpt (x : M) : alternatingFormInner (TangentSpace I x) 1 ((curl o α).val x) (β.val x) =
      alternatingFormInner (TangentSpace I x) 2 ((mextDerivₗ I 1 α).val x)
        ((hodgeStar o (k := 1) (l := 2) rfl β).val x) := by
    rw [← alternatingFormInner_formHodgeStarCLM o (k := 1) (l := 2) rfl x, coe_curl_apply,
      ← ContinuousLinearMap.comp_apply, formHodgeStarCLM_comp_formHodgeStarCLM, coe_hodgeStar,
      RoughForm.hodgeStar_eq_formHodgeStarCLM]
    norm_num
  simp_rw [hpt]
  rw [integralTopForm_inner_mextDeriv_eq_inner_codifferential o (k := 1) (l := 1) rfl α _
    (h.imp_right (hodgeStar_mem_compactlySupportedForms o rfl)),
    ← curl_eq_codifferential_hodgeStar]

end SmoothForm

end TauCeti
