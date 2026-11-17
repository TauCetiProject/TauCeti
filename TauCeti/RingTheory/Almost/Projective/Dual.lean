/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.Projective.Basic

/-!
# Duality for almost finite projective modules

For an almost finite projective module `M`, the canonical map
`dualTensorHom : Dual V M ⊗[V] N →ₗ[V] (M →ₗ[V] N)` is an almost isomorphism for every `N`.
Thus endomorphisms of `M` are represented, up to almost zero modules, by tensors with its dual.
This is the linear-algebra input to evaluation and coevaluation in almost modules.
The dual is again almost finite projective, and the evaluation map from `M` to its double dual
is an almost isomorphism.

The argument uses the existing ε-factorisations through finite free modules and Mathlib's
`dualTensorHomEquiv` on those modules; it does not assume that `M` is finite or projective
as an ordinary module.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, §2.4, Lemmas 2.4.15, 2.4.29 and 2.4.31.
-/

public section

open LinearMap Module TensorProduct

namespace TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V] {S : BasicSetup V}
  {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

/-- The dual–tensor–Hom comparison for an almost finite projective source is an almost
isomorphism, without a finiteness assumption on its target. -/
theorem IsAlmostFiniteProjective.isAlmostIso_dualTensorHom (h : S.IsAlmostFiniteProjective M) :
    S.IsAlmostIso (M := Dual V M ⊗[V] N) (N := M →ₗ[V] N) (dualTensorHom V M N) := by
  apply (isAlmostIso_iff_forall_exists_comp_eq_smul_id
    (M := Dual V M ⊗[V] N) (N := M →ₗ[V] N)).mpr
  intro ε hε
  obtain ⟨n, u, v, huv⟩ := isAlmostFiniteProjective_iff.mp h ε hε
  let e := dualTensorHomEquiv V (Fin n → V) N
  refine ⟨u.dualMap.rTensor N ∘ₗ e.symm.toLinearMap ∘ₗ v.lcomp V N, ?_, ?_⟩
  · rw [← LinearMap.comp_assoc, dualTensorHom_comp_rTensor_dualMap]
    ext f x
    have hx := LinearMap.congr_fun huv x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
    simp [e, hx]
  · apply TensorProduct.ext'
    intro φ y
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have he := (LinearMap.congr_fun
      (dualTensorHom_comp_rTensor_dualMap (P := N) v) (φ ⊗ₜ y)).symm
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul] at he
    rw [he]
    simp only [e, LinearEquiv.coe_coe, dualTensorHomEquiv_symm_dualTensorHom,
      LinearMap.rTensor_tmul]
    have hφ : u.dualMap (v.dualMap φ) = ε • φ := by
      ext x
      simpa using congrArg φ (LinearMap.congr_fun huv x)
    rw [hφ, smul_tmul']

/-- The ordinary dual of an almost finite projective module is again almost finite projective.
No flatness assumption on the basic ideal itself is required. -/
theorem IsAlmostFiniteProjective.dual (h : S.IsAlmostFiniteProjective M) :
    S.IsAlmostFiniteProjective (Dual V M) := by
  rw [isAlmostFiniteProjective_iff]
  intro ε hε
  obtain ⟨n, u, v, huv⟩ := isAlmostFiniteProjective_iff.mp h ε hε
  obtain ⟨k, f, g, _, _, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective V (Dual V (Fin n → V))
  refine ⟨k, g ∘ₗ v.dualMap, u.dualMap ∘ₗ f, ?_⟩
  calc
    _ = u.dualMap ∘ₗ v.dualMap := by
      simpa only [LinearMap.comp_assoc, LinearMap.id_comp] using
        congrArg (fun k ↦ u.dualMap ∘ₗ k ∘ₗ v.dualMap) hfg
    _ = ε • LinearMap.id := by
      ext φ x
      simpa using congrArg φ (LinearMap.congr_fun huv x)

/-- An almost finite projective module is almost reflexive: evaluation in the double dual
has almost zero kernel and cokernel. -/
theorem IsAlmostFiniteProjective.isAlmostIso_eval (h : S.IsAlmostFiniteProjective M) :
    S.IsAlmostIso (M := M) (N := Dual V (Dual V M)) (Dual.eval V M) := by
  apply (isAlmostIso_iff_forall_exists_comp_eq_smul_id
    (M := M) (N := Dual V (Dual V M))).mpr
  intro ε hε
  obtain ⟨n, u, v, huv⟩ := isAlmostFiniteProjective_iff.mp h ε hε
  let e := Module.evalEquiv V (Fin n → V)
  refine ⟨v ∘ₗ e.symm.toLinearMap ∘ₗ u.dualMap.dualMap, ?_, ?_⟩
  · ext Φ φ
    have hφ : u.dualMap (v.dualMap φ) = ε • φ := by
      ext x
      simpa using congrArg φ (LinearMap.congr_fun huv x)
    have he : φ (v (e.symm (u.dualMap.dualMap Φ))) =
        Φ (u.dualMap (v.dualMap φ)) :=
      LinearMap.congr_fun (LinearMap.congr_fun
        (Dual.eval_comp_comp_evalEquiv_eq (f := v)) (u.dualMap.dualMap Φ)) φ
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Dual.eval_apply,
      LinearMap.smul_apply, LinearMap.id_apply, hφ, map_smul] using he
  · ext x
    have he := LinearMap.congr_fun (Dual.eval_naturality u) x
    simp only [LinearMap.comp_apply] at he
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      LinearMap.id_apply, he, e, ← Module.evalEquiv_apply, LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun huv x

end TauCeti.Almost.BasicSetup
