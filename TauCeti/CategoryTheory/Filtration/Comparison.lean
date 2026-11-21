/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Filtration.Completeness
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Comparison of finite filtrations

A morphism of finite decreasing filtrations is invertible if it induces isomorphisms on all
associated graded pieces. Mathlib's short five lemma
(`ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'`) propagates invertibility from one step to the
next using the quotient of the two steps. Starting at a common zero step, this gives isomorphisms
at every step; a common full step then identifies the underlying objects.
-/

public section

namespace CategoryTheory.FilteredObject

open Limits

variable {C I : Type*} [Category* C] [Abelian C] [Category* I]

/-- An isomorphism at the source of a filtration transition and on its quotient implies an
isomorphism at the target of the transition. -/
lemma isIso_natTrans_app_of_isIso_subquotientFunctor_map {i j : I} (u : i ⟶ j)
    {F G : FilteredObject C I} (f : F ⟶ G) (hi : IsIso (f.natTrans.app i))
    (hq : IsIso ((subquotientFunctor u).map f)) : IsIso (f.natTrans.app j) := by
  let S (A : FilteredObject C I) :=
    ShortComplex.mk (A.filtrationDiagram.map u) (subquotientπ u A) (map_subquotientπ u A)
  have hS (A : FilteredObject C I) : (S A).ShortExact := by
    have w : A.filtrationDiagram.map u ≫ A.filtration.ι.app j = A.filtration.ι.app i := by
      simpa using A.filtration.ι.naturality u
    have hm : Mono (A.filtrationDiagram.map u ≫ A.filtration.ι.app j) := w.symm ▸ inferInstance
    exact ShortComplex.ShortExact.mk' ((S A).exact_of_g_is_cokernel (subquotientπIsCokernel u A))
      (mono_of_mono _ (A.filtration.ι.app j)) (inferInstanceAs (Epi (subquotientπ u A)))
  let φ : S F ⟶ S G := ShortComplex.homMk (f.natTrans.app i) (f.natTrans.app j)
    ((subquotientFunctor u).map f) (f.natTrans.naturality u).symm
    (subquotientπ_naturality u f).symm
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' φ (hS F) (hS G) hi hq

/-- If both decreasing filtrations reach zero at step `b`, isomorphisms on the graded pieces
below `b` induce isomorphisms at every step. No assumption about a full step is needed. -/
lemma isIso_natTrans_app_of_isIso_gradedPieceFunctor_map {F G : FilteredObject C ℤᵒᵖ}
    (f : F ⟶ G) {b : ℤ} (hF : F.step (Opposite.op b) = ⊥) (hG : G.step (Opposite.op b) = ⊥)
    (h : ∀ p < b, IsIso ((gradedPieceFunctor p).map f)) (p : ℤ) :
    IsIso (f.natTrans.app (Opposite.op p)) := by
  have zeroStep (p : ℤ) (hp : b ≤ p) : IsIso (f.natTrans.app (Opposite.op p)) := by
    have eqBot (A : FilteredObject C ℤᵒᵖ) (hA : A.step (Opposite.op b) = ⊥) :
        A.step (Opposite.op p) = ⊥ :=
      le_bot_iff.mp ((A.step_le_of_hom (homOfLE hp).op).trans_eq hA)
    have zeroObj (A : FilteredObject C ℤᵒᵖ) (hA : A.step (Opposite.op b) = ⊥) :
        IsZero (A.filtration.obj (Opposite.op p)) :=
      IsZero.of_mono_eq_zero _ ((A.step_eq_bot_iff _).1 (eqBot A hA))
    exact isIso_of_source_target_iso_zero _ (zeroObj F hF).isoZero (zeroObj G hG).isoZero
  rcases le_total b p with hp | hp
  · exact zeroStep p hp
  · induction p, hp using Int.leInductionDown with
    | base => exact zeroStep b le_rfl
    | pred q hq ih =>
      have e : q - 1 + 1 = q := Int.sub_add_cancel q 1
      exact isIso_natTrans_app_of_isIso_subquotientFunctor_map _ f
        (e.symm ▸ ih) (h (q - 1) (by omega))

/-- A morphism of finite decreasing filtrations is an isomorphism if it is an isomorphism on
every graded piece. -/
lemma isIso_of_isIso_gradedPieceFunctor_map {F G : FilteredObject C ℤᵒᵖ} (f : F ⟶ G)
    (hF : F.IsFinite) (hG : G.IsFinite) (h : ∀ p : ℤ, IsIso ((gradedPieceFunctor p).map f)) :
    IsIso f := by
  obtain ⟨aF, bF, _, haF, hbF⟩ := F.isFinite_iff.1 hF
  obtain ⟨aG, bG, _, haG, hbG⟩ := G.isFinite_iff.1 hG
  let a := min aF aG
  let b := max bF bG
  have haF' : F.step (Opposite.op a) = ⊤ :=
    top_le_iff.mp (haF.symm.trans_le (F.step_le_of_hom (homOfLE (min_le_left aF aG)).op))
  have haG' : G.step (Opposite.op a) = ⊤ :=
    top_le_iff.mp (haG.symm.trans_le (G.step_le_of_hom (homOfLE (min_le_right aF aG)).op))
  have hbF' : F.step (Opposite.op b) = ⊥ :=
    le_bot_iff.mp ((F.step_le_of_hom (homOfLE (le_max_left bF bG)).op).trans_eq hbF)
  have hbG' : G.step (Opposite.op b) = ⊥ :=
    le_bot_iff.mp ((G.step_le_of_hom (homOfLE (le_max_right bF bG)).op).trans_eq hbG)
  have hi (i : ℤᵒᵖ) : IsIso (f.natTrans.app i) :=
    isIso_natTrans_app_of_isIso_gradedPieceFunctor_map f hbF' hbG' (fun p _ ↦ h p) i.unop
  have := (F.isIso_ι_app_iff _).2 haF'
  have := (G.isIso_ι_app_iff _).2 haG'
  have : IsIso f.hom := IsIso.of_isIso_fac_left (f.comm (Opposite.op a)).symm
  let e := isoMk (asIso f.hom) (fun i ↦ asIso (f.natTrans.app i)) f.comm
  have he : e.hom = f := hom_ext rfl
  rw [← he]
  infer_instance

end CategoryTheory.FilteredObject
