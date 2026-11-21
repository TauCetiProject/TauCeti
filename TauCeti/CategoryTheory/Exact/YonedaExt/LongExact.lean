/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# The long exact `Hom`–`Ext¹` sequences of a conflation

For an exact structure `E` on an additive category, a conflation `e : X ⟶ Y ⟶ Z` and an object
`W`, the two six-term sequences
`0 → Hom(W, X) → Hom(W, Y) → Hom(W, Z) → Ext¹_E(W, X) → Ext¹_E(W, Y) → Ext¹_E(W, Z)` and
`0 → Hom(Z, W) → Hom(Y, W) → Hom(X, W) → Ext¹_E(Z, W) → Ext¹_E(Y, W) → Ext¹_E(X, W)`
are exact. The connecting maps are `u ↦ u^* [e]` and `v ↦ v_* [e]`, and the maps between the
`Ext¹` groups are cobase change along the inflation and the deflation of `e`, respectively base
change along the deflation and the inflation.

The substantial step is exactness at the middle terms `Ext¹_E(W, Y)` and `Ext¹_E(Y, W)`. A class
`ξ = [Y ⟶ M ⟶ W]` whose cobase change along the deflation `Y ⟶ Z` splits is a cobase change
along the inflation `X ⟶ Y`: the Noether isomorphism `TauCeti.ExactStructure.exists_conflation_comp`
presents that cobase change as the conflation `Y/X ⟶ M/X ⟶ M/Y`, and base change of the
conflation `X ⟶ M ⟶ M/X` along a section of its deflation `M/X ⟶ W` is a preimage of `ξ`.
The contravariant statement is dual, through `TauCeti.ExactStructure.exists_conflation_comp'`.
Exactness at the other terms is the kernel–cokernel property of `e` together with
`TauCeti.ExactStructure.Ext1.mk_pullback_eq_zero_iff`,
`TauCeti.ExactStructure.Ext1.pushout_f_eq_zero_iff` and their duals.

The statements are pointed-set statements (`Function.Exact`, `Function.Injective`), which need
only the base point of `Ext¹`; with the Baer sum the maps are additive, so these are exact
sequences of abelian groups, and of `R`-modules for an `R`-linear category.

## Main results

* `TauCeti.ExactStructure.Ext1.pushout_g_eq_zero_iff`: exactness at `Ext¹_E(W, Y)`.
* `TauCeti.ExactStructure.Ext1.pullback_f_eq_zero_iff`: exactness at `Ext¹_E(Y, W)`.
* `TauCeti.ExactStructure.Extension.injective_comp_f`,
  `TauCeti.ExactStructure.Extension.exact_comp_f_comp_g`,
  `TauCeti.ExactStructure.Extension.exact_comp_g_mk_pullback`,
  `TauCeti.ExactStructure.Extension.exact_mk_pullback_pushout_f` and
  `TauCeti.ExactStructure.Extension.exact_pushout_f_pushout_g`: the covariant sequence.
* `TauCeti.ExactStructure.Extension.injective_g_comp`,
  `TauCeti.ExactStructure.Extension.exact_g_comp_f_comp`,
  `TauCeti.ExactStructure.Extension.exact_f_comp_mk_pushout`,
  `TauCeti.ExactStructure.Extension.exact_mk_pushout_pullback_g` and
  `TauCeti.ExactStructure.Extension.exact_pullback_g_pullback_f`: the contravariant sequence.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>. Lemma 3.5 is the Noether isomorphism used here.
* Saunders Mac Lane, *Homology*, Grundlehren **114**, Springer (1963), Chapter III, for the two
  exact `Hom`–`Ext` sequences of modules, proved there through extensions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {W X Z : C}

namespace Ext1

/-- **Exactness at `Ext¹_E(W, Y)`.** For a conflation `e : X ⟶ Y ⟶ Z`, a class
`ξ ∈ Ext¹_E(W, Y)` is a cobase change `f_* η` along the inflation of `e` exactly when its cobase
change along the deflation of `e` vanishes. -/
theorem pushout_g_eq_zero_iff (e : E.Extension Z X) (ξ : E.Ext1 W e.obj) :
    ξ.pushout e.g = 0 ↔ ∃ η : E.Ext1 W X, η.pushout e.f = ξ := by
  refine ⟨fun h ↦ ?_, fun ⟨η, hη⟩ ↦ hη ▸ ?_⟩
  · induction ξ using induction with
    | h e₀ =>
      -- The Noether conflations `X ⟶ M ⟶ Q` and `Z ⟶ Q ⟶ W` for `e₀ : Y ⟶ M ⟶ W`.
      obtain ⟨Q, c, α, β, hc, hβ, hM, hQ, hcα, hcβ⟩ :=
        E.exists_conflation_comp e.conflation e₀.conflation
      let eM : E.Extension Q X := ⟨e₀.obj, e.f ≫ e₀.f, c, hc, hM⟩
      let eQ : E.Extension W Z := ⟨Q, α, β, hβ, hQ⟩
      have hξ : (mk e₀).pushout e.g = mk eQ := by
        rw [pushout_mk_eq_pullback_mk (e' := eQ) (c := 𝟙 W) c hcα (by simp [eQ, hcβ]), pullback_id]
      rw [hξ, mk_eq_zero_iff_isSplitEpi] at h
      refine ⟨mk (eM.pullback (section_ β)), ?_⟩
      refine (pushout_mk_eq_pullback_mk (c := 𝟙 W) (eM.pullbackFst _) (by simp [eM]) ?_).trans
        (pullback_id _)
      rw [← hcβ, Category.comp_id]
      exact (eM.pullbackFst_g_assoc (section_ β) β).trans (by simp)
  · rw [pushout_pushout, Extension.zero, pushout_zero]

/-- **Exactness at `Ext¹_E(Y, W)`.** For a conflation `e : X ⟶ Y ⟶ Z`, a class
`ξ ∈ Ext¹_E(Y, W)` is a base change `g^* η` along the deflation of `e` exactly when its base
change along the inflation of `e` vanishes. -/
theorem pullback_f_eq_zero_iff (e : E.Extension Z X) (ξ : E.Ext1 e.obj W) :
    ξ.pullback e.f = 0 ↔ ∃ η : E.Ext1 Z W, η.pullback e.g = ξ := by
  refine ⟨fun h ↦ ?_, fun ⟨η, hη⟩ ↦ hη ▸ ?_⟩
  · induction ξ using induction with
    | h e₀ =>
      -- The dual Noether conflations `Q ⟶ M ⟶ Z` and `W ⟶ Q ⟶ X` for `e₀ : W ⟶ M ⟶ Y`.
      obtain ⟨Q, c, α, β, hc, hβ, hM, hQ, hcα, hβc⟩ :=
        E.exists_conflation_comp' e.conflation e₀.conflation
      let eM : E.Extension Z Q := ⟨e₀.obj, c, e₀.g ≫ e.g, hc, hM⟩
      let eQ : E.Extension X W := ⟨Q, β, α, hβ, hQ⟩
      have hξ : (mk e₀).pullback e.f = mk eQ := by
        rw [← pushout_mk_eq_pullback_mk (e := eQ) (a := 𝟙 W) c (by simp [eQ, hβc]) hcα, pushout_id]
      rw [hξ, mk_eq_zero_iff_isSplitMono] at h
      refine ⟨mk (eM.pushout (retraction β)), ?_⟩
      refine ((pushout_mk_eq_pullback_mk (a := 𝟙 W) (eM.pushoutInl _) ?_ (by simp [eM])).symm.trans
        (pushout_id _))
      rw [← hβc, Category.id_comp, Category.assoc]
      exact (congrArg (β ≫ ·) (eM.f_pushoutInl (retraction β))).trans (by simp)
  · rw [pullback_pullback, Extension.zero, pullback_zero]

end Ext1

namespace Extension

/-! ### The covariant sequence `0 → Hom(W, X) → Hom(W, Y) → Hom(W, Z) → Ext¹_E(W, X) → …` -/

variable (e : E.Extension Z X) (W)

/-- **Exactness at `Hom(W, X)`**: composition with the inflation is injective. -/
theorem injective_comp_f : Function.Injective fun a : W ⟶ X ↦ a ≫ e.f :=
  fun _ _ h ↦ e.isKernelCokernelPair.mono_f.right_cancellation _ _ h

/-- **Exactness at `Hom(W, Y)`**: a morphism into the middle term is killed by the deflation
exactly when it factors through the inflation. -/
theorem exact_comp_f_comp_g :
    Function.Exact (fun a : W ⟶ X ↦ a ≫ e.f) fun t : W ⟶ e.obj ↦ t ≫ e.g := fun t ↦
  ⟨fun ht ↦ ⟨e.isKernelCokernelPair.lift t ht, e.isKernelCokernelPair.lift_f t ht⟩,
    by rintro ⟨a, rfl⟩; simp⟩

/-- **Exactness at `Hom(W, Z)`**: the connecting map `u ↦ u^* [e]` vanishes exactly on the
morphisms factoring through the deflation. -/
theorem exact_comp_g_mk_pullback :
    Function.Exact (fun t : W ⟶ e.obj ↦ t ≫ e.g) fun u : W ⟶ Z ↦ (Ext1.mk e).pullback u :=
  fun u ↦ Ext1.mk_pullback_eq_zero_iff e u

/-- **Exactness at `Ext¹_E(W, X)`**: the image of the connecting map is the kernel of cobase
change along the inflation. -/
theorem exact_mk_pullback_pushout_f :
    Function.Exact (fun u : W ⟶ Z ↦ (Ext1.mk e).pullback u)
      fun ξ : E.Ext1 W X ↦ ξ.pushout e.f :=
  fun ξ ↦ Ext1.pushout_f_eq_zero_iff e ξ

/-- **Exactness at `Ext¹_E(W, Y)`**: the image of cobase change along the inflation is the kernel
of cobase change along the deflation. -/
theorem exact_pushout_f_pushout_g :
    Function.Exact (fun η : E.Ext1 W X ↦ η.pushout e.f)
      fun ξ : E.Ext1 W e.obj ↦ ξ.pushout e.g :=
  fun ξ ↦ Ext1.pushout_g_eq_zero_iff e ξ

/-! ### The contravariant sequence `0 → Hom(Z, W) → Hom(Y, W) → Hom(X, W) → Ext¹_E(Z, W) → …` -/

/-- **Exactness at `Hom(Z, W)`**: precomposition with the deflation is injective. -/
theorem injective_g_comp : Function.Injective fun b : Z ⟶ W ↦ e.g ≫ b :=
  fun _ _ h ↦ e.isKernelCokernelPair.epi_g.left_cancellation _ _ h

/-- **Exactness at `Hom(Y, W)`**: a morphism out of the middle term is killed by the inflation
exactly when it factors through the deflation. -/
theorem exact_g_comp_f_comp :
    Function.Exact (fun b : Z ⟶ W ↦ e.g ≫ b) fun t : e.obj ⟶ W ↦ e.f ≫ t := fun t ↦
  ⟨fun ht ↦ ⟨e.isKernelCokernelPair.desc t ht, e.isKernelCokernelPair.g_desc t ht⟩,
    by rintro ⟨b, rfl⟩; simp⟩

/-- **Exactness at `Hom(X, W)`**: the connecting map `v ↦ v_* [e]` vanishes exactly on the
morphisms extending along the inflation. -/
theorem exact_f_comp_mk_pushout :
    Function.Exact (fun t : e.obj ⟶ W ↦ e.f ≫ t) fun v : X ⟶ W ↦ (Ext1.mk e).pushout v :=
  fun v ↦ Ext1.mk_pushout_eq_zero_iff e v

/-- **Exactness at `Ext¹_E(Z, W)`**: the image of the connecting map is the kernel of base change
along the deflation. -/
theorem exact_mk_pushout_pullback_g :
    Function.Exact (fun v : X ⟶ W ↦ (Ext1.mk e).pushout v)
      fun ξ : E.Ext1 Z W ↦ ξ.pullback e.g :=
  fun ξ ↦ Ext1.pullback_g_eq_zero_iff e ξ

/-- **Exactness at `Ext¹_E(Y, W)`**: the image of base change along the deflation is the kernel
of base change along the inflation. -/
theorem exact_pullback_g_pullback_f :
    Function.Exact (fun η : E.Ext1 Z W ↦ η.pullback e.g)
      fun ξ : E.Ext1 e.obj W ↦ ξ.pullback e.f :=
  fun ξ ↦ Ext1.pullback_f_eq_zero_iff e ξ

end Extension

end ExactStructure

end TauCeti
