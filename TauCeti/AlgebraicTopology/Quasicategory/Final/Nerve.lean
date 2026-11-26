/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Final
public import TauCeti.AlgebraicTopology.Quasicategory.Final
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Connected
public import TauCeti.CategoryTheory.Comma.Under.Pullback

/-!
# Finality for maps of nerves

The undercategory comparison `CategoryTheory.nerve.cosliceIso` and Mathlib's
`CategoryTheory.nerveAdjunction` identify the fibres tested by `SSet.IsFinal` with nerves
of structured arrow categories. Weak contractibility implies connectedness, giving
ordinary finality in the sense of `CategoryTheory.Functor.Final`.

## References

* J. Lurie, *Higher Topos Theory*, Theorem 4.1.3.1.
-/

public section

universe u

open SSet CategoryTheory Limits Simplicial

namespace CategoryTheory.nerve

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- The nerve of the structured arrow category over `x` is the pullback of the nerve
map of `F` along the simplicial coslice projection at `x`. -/
theorem isPullback_structuredArrow_coslice (F : C ⥤ D) (x : D) :
    IsPullback (nerveMap (StructuredArrow.proj x F))
      (nerveMap (StructuredArrow.pre x F (𝟭 D)) ≫ (cosliceIso x).hom)
      (nerveMap F) (coslice.π (const (nerveEquiv.symm x) : Δ[0] ⟶ nerve D)) := by
  have : nerveFunctor.{u, u}.IsRightAdjoint := nerveAdjunction.isRightAdjoint
  have h : IsPullback (nerveMap (StructuredArrow.proj x F))
      (nerveMap (StructuredArrow.pre x F (𝟭 D))) (nerveMap F) (nerveMap (Under.forget x)) :=
    (F.isPullback_structuredArrow_pre (𝟭 D) x).map nerveFunctor
  refine h.of_iso (Iso.refl _) (Iso.refl _) (cosliceIso x) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (cosliceIso_hom_comp_π x).symm

/-- A map of nerves is final exactly when the structured arrow categories have weakly
contractible nerves, the comma-category condition of HTT Theorem 4.1.3.1. -/
theorem isFinal_nerveMap_iff (F : C ⥤ D) :
    SSet.IsFinal (nerveMap F) ↔ ∀ x : D, IsWeaklyContractible (nerve (StructuredArrow x F)) := by
  rw [SSet.isFinal_iff]
  constructor
  · intro h x
    have := h (nerveEquiv.symm x)
    exact IsWeaklyContractible.of_iso (isPullback_structuredArrow_coslice F x).isoPullback.symm
  · intro h y
    obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective y
    have := h x
    exact IsWeaklyContractible.of_iso (isPullback_structuredArrow_coslice F x).isoPullback

/-- A functor whose nerve map is final is final in the ordinary sense. -/
theorem _root_.CategoryTheory.Functor.final_of_isFinal_nerveMap (F : C ⥤ D)
    (h : SSet.IsFinal (nerveMap F)) : F.Final := by
  constructor
  intro x
  have := (isFinal_nerveMap_iff F).1 h x
  exact (isConnected_nerve_iff _).1 inferInstance

end CategoryTheory.nerve
