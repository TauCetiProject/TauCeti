/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Semisimple modules: binary products and endomorphisms between elements

Mathlib closes `IsSemisimpleModule` under submodules, quotients, `Finsupp`, and finite dependent
products `Π i, M i`. The dependent product covers a binary product only when both factors lie in
the same universe, since the family `M : ι → Type u` is universe-monomorphic; this file supplies
the binary case with the two factors in unrelated universes.

It also records which elements of a semisimple module an endomorphism can connect: some
`R`-linear endomorphism sends `w` to `x` exactly when every scalar killing `w` kills `x`. This
criterion turns reachability under endomorphisms into a containment between torsion ideals, a form
useful in centralizer arguments.

## Main results

* `TauCeti.IsSemisimpleModule.prod`: a product of two semisimple modules is semisimple.
* `TauCeti.IsSemisimpleModule.exists_end_apply_eq_iff`: in a semisimple module, an endomorphism
  sends `w` to `x` if and only if the torsion ideal of `w` is contained in that of `x`.
-/

public section

namespace TauCeti

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **A product of two semisimple modules is semisimple.** -/
instance IsSemisimpleModule.prod [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by
  -- The plan is that of Mathlib's binary-product `IsSemisimpleRing` instance, one level down:
  -- `M × N` is the join of the two coordinate copies, each of which is a semisimple submodule.
  have hsup := _root_.IsSemisimpleModule.sup
    (_root_.IsSemisimpleModule.range (LinearMap.inl R M N))
    (_root_.IsSemisimpleModule.range (LinearMap.inr R M N))
  rw [LinearMap.sup_range_inl_inr] at hsup
  exact .congr Submodule.topEquiv.symm

/-- **Endomorphisms between two elements of a semisimple module.** Some `R`-linear endomorphism of
a semisimple module sends `w` to `x` exactly when every scalar annihilating `w` annihilates `x`,
that is, when `Ideal.torsionOf R M w ≤ Ideal.torsionOf R M x`. -/
theorem IsSemisimpleModule.exists_end_apply_eq_iff [IsSemisimpleModule R M] {w x : M} :
    (∃ f : Module.End R M, f w = x) ↔ Ideal.torsionOf R M w ≤ Ideal.torsionOf R M x := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, rfl⟩ r hr
    rw [Ideal.mem_torsionOf_iff] at hr ⊢
    rw [← f.map_smul, hr, map_zero]
  · -- `r • w ↦ r • x` is well defined on `R ∙ w ≃ R ⧸ torsionOf w`; extend it to all of `M`
    let g : (R ∙ w) →ₗ[R] M :=
      (Ideal.torsionOf R M w).liftQ (LinearMap.toSpanSingleton R M x) h ∘ₗ
        (Ideal.quotTorsionOfEquivSpanSingleton R M w).symm.toLinearMap
    obtain ⟨f, hf⟩ := _root_.IsSemisimpleModule.extension_property _
      (R ∙ w).subtype_injective g
    refine ⟨f, ?_⟩
    have hw := Ideal.quotTorsionOfEquivSpanSingleton_apply_mk w (1 : R)
    rw [one_smul] at hw
    have hfw := LinearMap.congr_fun hf ⟨w, Submodule.mem_span_singleton_self w⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at hfw
    rw [hfw, ← hw]
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    -- `liftQ` evaluates on the class of `1` to `1 • x` by definition; the `Ideal R` and
    -- `Submodule R R` forms of the kernel condition block rewriting with `Submodule.liftQ_apply`
    exact one_smul R x

end TauCeti
