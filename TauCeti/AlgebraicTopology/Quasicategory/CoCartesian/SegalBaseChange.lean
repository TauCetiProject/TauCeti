/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.BaseChange
public import TauCeti.AlgebraicTopology.Quasicategory.SymmetricMonoidal
public import TauCeti.CategoryTheory.CategoryOfOperators.LM

/-!
# Restricting Segal transports to Assoc and LM

The operator maps to finite pointed sets preserve the designated projections. A family of
chosen Segal transports therefore restricts along either operator map, and its pulled-back
product map is a categorical equivalence. The target fibres for LM are indexed by the
individual output colors. These restrictions supply the Segal condition for monoidal
categories and for categories with a left action, including the empty family of projections.

## References

* J. Lurie, *Higher Algebra*, §§4.1.1 and 4.2.1.
-/

public section

universe u

open CategoryTheory Limits Simplicial SSet

namespace TauCeti

private lemma assoc_projection_map (a : Assoc.{u}) (i : Fin a.len) :
    (nerve.edgeMk (Assoc.ρ i)).map (nerveMap Assoc.toFinPointed) =
      nerve.edgeMk (FinPointed.ρ (n := FinPointed.mk a.len) i) := by
  apply Edge.ext
  exact (nerveMap_app_mk₁ _ _).trans (by
    simp only [Assoc.toFinPointed_map, Assoc.ρ_base]
    exact (nerve.edgeMk_edge _).symm)

private lemma lm_projection_map (a : LM.{u}) (i : Fin a.len) :
    (nerve.edgeMk (LM.ρ i)).map (nerveMap LM.toFinPointed) =
      nerve.edgeMk (FinPointed.ρ (n := FinPointed.mk a.len) i) := by
  apply Edge.ext
  exact (nerveMap_app_mk₁ _ _).trans (by
    simp only [LM.toFinPointed_map, LM.ρ_toAssoc, Assoc.ρ_base]
    exact (nerve.edgeMk_edge _).symm)

variable {X X' : SSet.{u}} {p : X ⟶ nerve FinPointed.{u}} {t : X' ⟶ X}

/-- A Segal family over finite pointed sets restricts to a family over the designated
projections of `Assoc`, still giving a categorical equivalence to the product of the fibres. -/
theorem Assoc.exists_isCategoricalEquivalence_piFunctor_of_isPullback
    {p' : X' ⟶ nerve Assoc.{u}} [InnerFibration p] (a : Assoc.{u})
    (sq : IsPullback t p' p (nerveMap Assoc.toFinPointed))
    (T : ∀ i : Fin a.len, CoCartesianTransport p
      (nerve.edgeMk (FinPointed.ρ (n := FinPointed.mk a.len) i)))
    (hT : QCat.IsCategoricalEquivalence
      (X := ⟨fiber p (FinPointed.mk a.len).vertex, inferInstance⟩)
      (Y := ⟨∏ᶜ fun _ : Fin a.len ↦ (fiber p (FinPointed.mk 1).vertex : SSet), inferInstance⟩)
      (ObjectProperty.homMk (segalMap T))) :
    letI : InnerFibration p' := ⟨innerFibrations.of_isPullback sq (mem_innerFibrations p)⟩
    ∃ U : ∀ i : Fin a.len, CoCartesianTransport p' (nerve.edgeMk (Assoc.ρ i)),
      QCat.IsCategoricalEquivalence
        (X := ⟨fiber p' (nerveEquiv.symm a),
          by exact @fiber.quasicategory _ _ p' inferInstance (nerveEquiv.symm a)⟩)
        (Y := ⟨∏ᶜ fun _ : Fin a.len ↦ (fiber p' (nerveEquiv.symm (Assoc.mk 1)) : SSet),
          by
            exact @quasicategory_piObj (Fin a.len)
              (fun _ ↦ (fiber p' (nerveEquiv.symm (Assoc.mk 1)) : SSet)) inferInstance
              (fun _ ↦ @fiber.quasicategory _ _ p' inferInstance _)⟩)
        (ObjectProperty.homMk (CoCartesianTransport.piFunctor U)) := by
  let : InnerFibration p' := ⟨innerFibrations.of_isPullback sq (mem_innerFibrations p)⟩
  let V : ∀ i : Fin a.len, CoCartesianTransport p
      ((nerve.edgeMk (Assoc.ρ i)).map (nerveMap Assoc.toFinPointed)) :=
    fun i ↦ (assoc_projection_map a i).symm ▸ T i
  have hcast {s r : (nerve FinPointed.{u}) _⦋0⦌} {e e' : Edge s r}
      (T₀ : CoCartesianTransport p e) (h : e = e') : (h ▸ T₀).functor = T₀.functor := by
    cases h
    rfl
  have hV : CoCartesianTransport.piFunctor V = segalMap (n := FinPointed.mk a.len) T := by
    apply Pi.hom_ext
    intro i
    exact (CoCartesianTransport.piFunctor_π V i).trans
      ((hcast (T i) (assoc_projection_map a i).symm).trans
        (segalMap_π (p := p) (n := FinPointed.mk a.len) T i).symm)
  refine ⟨fun i ↦ (V i).baseChange sq, ?_⟩
  apply (CoCartesianTransport.isCategoricalEquivalence_piFunctor_baseChange_iff V sq).2
  rw [hV]
  exact hT

/-- A Segal family over finite pointed sets restricts to the projections of `LM`, giving a
categorical equivalence to the product of the fibres over the individual output colors. -/
theorem LM.exists_isCategoricalEquivalence_piFunctor_of_isPullback
    {p' : X' ⟶ nerve LM.{u}} [InnerFibration p] (a : LM.{u})
    (sq : IsPullback t p' p (nerveMap LM.toFinPointed))
    (T : ∀ i : Fin a.len, CoCartesianTransport p
      (nerve.edgeMk (FinPointed.ρ (n := FinPointed.mk a.len) i)))
    (hT : QCat.IsCategoricalEquivalence
      (X := ⟨fiber p (FinPointed.mk a.len).vertex, inferInstance⟩)
      (Y := ⟨∏ᶜ fun _ : Fin a.len ↦ (fiber p (FinPointed.mk 1).vertex : SSet), inferInstance⟩)
      (ObjectProperty.homMk (segalMap T))) :
    letI : InnerFibration p' := ⟨innerFibrations.of_isPullback sq (mem_innerFibrations p)⟩
    ∃ U : ∀ i : Fin a.len, CoCartesianTransport p' (nerve.edgeMk (LM.ρ i)),
      QCat.IsCategoricalEquivalence
        (X := ⟨fiber p' (nerveEquiv.symm a),
          by exact @fiber.quasicategory _ _ p' inferInstance (nerveEquiv.symm a)⟩)
        (Y := ⟨∏ᶜ fun i : Fin a.len ↦
          (fiber p' (nerveEquiv.symm (⟨1, fun _ ↦ a.color i⟩ : LM)) : SSet),
          by
            exact @quasicategory_piObj (Fin a.len)
              (fun i ↦ (fiber p' (nerveEquiv.symm (⟨1, fun _ ↦ a.color i⟩ : LM)) : SSet))
              inferInstance (fun _ ↦ @fiber.quasicategory _ _ p' inferInstance _)⟩)
        (ObjectProperty.homMk (CoCartesianTransport.piFunctor U)) := by
  let : InnerFibration p' := ⟨innerFibrations.of_isPullback sq (mem_innerFibrations p)⟩
  let V : ∀ i : Fin a.len, CoCartesianTransport p
      ((nerve.edgeMk (LM.ρ i)).map (nerveMap LM.toFinPointed)) :=
    fun i ↦ (lm_projection_map a i).symm ▸ T i
  have hcast {s r : (nerve FinPointed.{u}) _⦋0⦌} {e e' : Edge s r}
      (T₀ : CoCartesianTransport p e) (h : e = e') : (h ▸ T₀).functor = T₀.functor := by
    cases h
    rfl
  have hV : CoCartesianTransport.piFunctor V = segalMap (n := FinPointed.mk a.len) T := by
    apply Pi.hom_ext
    intro i
    exact (CoCartesianTransport.piFunctor_π V i).trans
      ((hcast (T i) (lm_projection_map a i).symm).trans
        (segalMap_π (p := p) (n := FinPointed.mk a.len) T i).symm)
  refine ⟨fun i ↦ (V i).baseChange sq, ?_⟩
  apply (CoCartesianTransport.isCategoricalEquivalence_piFunctor_baseChange_iff V sq).2
  rw [hV]
  exact hT

end TauCeti
