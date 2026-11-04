/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms

/-!
# The presentation of the simplex category

The canonical functor `SimplexCategoryGenRel.toSimplexCategory` is an equivalence.
Thus faces and degeneracies satisfying the simplicial identities determine functors
on the usual simplex category. This permits the construction of simplicial objects
from algebraic operations, such as the counit and comultiplication of a comonad.

The proof completes Robin Carlier's presentation and degeneracy normal forms in
Mathlib. Pure face maps are determined by their images, and pure degeneracies by
the positions where consecutive values agree. The epi-mono factorization then
establishes faithfulness for arbitrary morphisms.

## References

* [Kerodon, Tag 04FQ](https://kerodon.net/tag/04FQ).
* [Kerodon, Tag 04FT](https://kerodon.net/tag/04FT).
-/

public section

open CategoryTheory Limits
open scoped Simplicial

namespace SimplexCategoryGenRel

-- Fix the finite ordinal types before applying the comparison: otherwise rewriting
-- its object map can leave different preorder instances on definitionally equal types.
private abbrev eval {x y : SimplexCategoryGenRel} (f : x ⟶ y) :
    Fin (x.len + 1) →o Fin (y.len + 1) := (toSimplexCategory.map f).toOrderHom

private lemma eval_comp_apply {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z)
    (a : Fin (x.len + 1)) : eval (f ≫ g) a = eval g (eval f a) :=
  congrArg (fun k : toSimplexCategory.obj x ⟶ toSimplexCategory.obj z ↦ k.toOrderHom a)
    (toSimplexCategory.map_comp f g)

private lemma eval_id (x : SimplexCategoryGenRel) : eval (𝟙 x) = OrderHom.id :=
  congrArg SimplexCategory.Hom.toOrderHom (toSimplexCategory.map_id x)

private lemma factor_face {n : ℕ} {x : SimplexCategoryGenRel}
    (f : x ⟶ mk (n + 1)) (hf : P_δ f) (i : Fin (n + 2))
    (hi : ∀ a, eval f a ≠ i) :
    ∃ g : x ⟶ mk n, P_δ g ∧ f = g ≫ δ i := by
  cases hf with
  | of _ h =>
    cases h with | δ j =>
    have hij : i = j := by
      by_contra h
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h
      exact hi a ha
    subst hij
    exact ⟨𝟙 _, P_δ.id_mem _, by simp⟩
  | id => exact (hi i (by rw [eval_id]; rfl)).elim
  | comp_of g _ hg h =>
    cases h with | δ j =>
    by_cases hij : i = j
    · subst hij
      exact ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    have hmissing : ∀ a, eval g a ≠ k := by
      intro a ha
      apply hi a
      exact (eval_comp_apply g (δ j) a).trans ((congrArg j.succAbove ha).trans hk)
    cases n with
    | zero => exact (hmissing 0 (Subsingleton.elim (α := Fin 1) _ _)).elim
    | succ n =>
      obtain ⟨g', hg', rfl⟩ := factor_face g hg k hmissing
      -- Move the omitted vertex to the final face using the face-face identity.
      by_cases hkj : k.castSucc < j
      · have hij' : i = k.castSucc := by
          rw [Fin.succAbove_of_castSucc_lt _ _ hkj] at hk
          exact hk.symm
        obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hkj)
        refine ⟨g' ≫ δ j', P_δ.comp_mem _ _ hg' (P_δ.δ _), ?_⟩
        rw [Category.assoc, δ_comp_δ (Fin.castSucc_lt_succ_iff.mp hkj), hij', Category.assoc]
      · have hij' : i = k.succ := by
          rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkj)] at hk
          exact hk.symm
        obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last
          (Fin.ne_last_of_lt (lt_of_le_of_lt (le_of_not_gt hkj) k.castSucc_lt_last))
        refine ⟨g' ≫ δ j', P_δ.comp_mem _ _ hg' (P_δ.δ _), ?_⟩
        rw [Category.assoc, ← δ_comp_δ (Fin.castSucc_le_castSucc_iff.mp
          (le_of_not_gt hkj)), hij', Category.assoc]
termination_by n

private lemma map_injective_faces {n : ℕ} {x : SimplexCategoryGenRel}
    (f g : x ⟶ mk n) (hf : P_δ f) (hg : P_δ g)
    (h : toSimplexCategory.map f = toSimplexCategory.map g) : f = g := by
  induction n generalizing x with
  | zero =>
    have hmono := isSplitMono_toSimplexCategory_map_of_P_δ hf
    have hx : x = mk 0 := by
      apply SimplexCategoryGenRel.ext
      have := SimplexCategory.len_le_of_mono (toSimplexCategory.map f)
      simpa using this
    subst hx
    obtain ⟨_, rfl⟩ | hn := eq_or_len_le_of_P_δ hf
    · obtain ⟨_, rfl⟩ | hn := eq_or_len_le_of_P_δ hg
      · rfl
      · simp at hn
    · simp at hn
  | succ n ih =>
    cases hf with
    | id =>
      obtain ⟨_, rfl⟩ | hn := eq_or_len_le_of_P_δ hg
      · rfl
      · simp at hn
    | of _ hface =>
      cases hface with | δ i =>
      have hmissing : ∀ a, eval g a ≠ i := by
        have he : eval (δ i) = eval g := congrArg SimplexCategory.Hom.toOrderHom h
        intro a ha
        exact Fin.succAbove_ne i a ((congrArg (fun q ↦ q a) he).trans ha)
      obtain ⟨g', hg', hg⟩ := factor_face g hg i hmissing
      have h' : toSimplexCategory.map (𝟙 (mk n)) = toSimplexCategory.map g' := by
        apply (cancel_mono (SimplexCategory.δ i)).1
        simpa [hg] using h
      rw [hg, ← ih (𝟙 _) g' (P_δ.id_mem _) hg' h', Category.id_comp]
    | comp_of f' _ hf' hface =>
      cases hface with | δ i =>
      have hmissing : ∀ a, eval g a ≠ i := by
        have he : eval (f' ≫ δ i) = eval g := congrArg SimplexCategory.Hom.toOrderHom h
        intro a ha
        exact Fin.succAbove_ne i _ ((eval_comp_apply f' (δ i) a).symm.trans
          ((congrArg (fun q ↦ q a) he).trans ha))
      obtain ⟨g', hg', hg⟩ := factor_face g hg i hmissing
      have h' : toSimplexCategory.map f' = toSimplexCategory.map g' := by
        apply (cancel_mono (SimplexCategory.δ i)).1
        simpa [hg] using h
      rw [hg, ih f' g' hf' hg' h']

private lemma map_injective_degeneracies {x y : SimplexCategoryGenRel}
    (f g : x ⟶ y) (hf : P_σ f) (hg : P_σ g)
    (h : toSimplexCategory.map f = toSimplexCategory.map g) : f = g := by
  obtain ⟨L, m, b, rfl, rfl, rfl, hL, rfl⟩ := exists_normal_form_P_σ f hf
  obtain ⟨L', m', b', he, he', hb', hL', hg⟩ := exists_normal_form_P_σ g hg
  have hm : m' = m := congrArg SimplexCategoryGenRel.len he
  subst m'
  have hb : b' = L.length := by
    have := congrArg SimplexCategoryGenRel.len he'
    simp only [mk_len] at this
    omega
  have hlen : L'.length = L.length := hb'.trans hb
  have heval (j : ℕ) (hj : j < m + L.length + 1) :
      simplicialEvalσ L j = simplicialEvalσ L' j := by
    have hvalue := congrArg (fun k ↦ (k.toOrderHom ⟨j,
      by simpa only [toSimplexCategory_len, mk_len] using hj⟩ : ℕ)) h
    rw [hg] at hvalue
    exact (simplicialEvalσ_of_isAdmissible L _ _ hL rfl j hj).symm.trans
      (hvalue.trans (simplicialEvalσ_of_isAdmissible L' _ _ hL'
        (congrArg (m + ·) hlen) j hj))
  have hmem (j : ℕ) : j ∈ L ↔ j ∈ L' := by
    rw [mem_isAdmissible_iff L hL j, mem_isAdmissible_iff L' hL' j, hlen]
    by_cases hj : j < m + L.length
    · rw [heval j (by omega), heval (j + 1) (by omega)]
    · simp [hj]
  have hLL : L = L' := hL.sortedLT.eq_of_mem_iff hL'.sortedLT hmem
  subst hLL
  simpa using hg.symm

private lemma map_surjective_mk (n m : ℕ) (f : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    ∃ g : mk n ⟶ mk m, toSimplexCategory.map g = f := by
  classical
  by_cases hinj : Function.Injective f.toOrderHom
  · by_cases hsurj : Function.Surjective f.toOrderHom
    · have := SimplexCategory.isIso_of_bijective ⟨hinj, hsurj⟩
      have hnm : n = m := by
        have := SimplexCategory.skeletal ⟨asIso f⟩
        exact congrArg SimplexCategory.len this
      subst m
      exact ⟨𝟙 _, (toSimplexCategory.map_id _).trans
        (SimplexCategory.eq_id_of_isIso f).symm⟩
    · cases m with
      | zero =>
        exact (hsurj fun a ↦ ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩).elim
      | succ m =>
        obtain ⟨i, f', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f hsurj
        obtain ⟨g, hg⟩ := map_surjective_mk n m f'
        exact ⟨g ≫ δ i, by rw [toSimplexCategory.map_comp, hg, toSimplexCategory_map_δ]; rfl⟩
  · cases n with
    | zero => exact (hinj fun _ _ _ ↦ Subsingleton.elim (α := Fin 1) _ _).elim
    | succ n =>
      obtain ⟨i, f', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hinj
      obtain ⟨g, hg⟩ := map_surjective_mk n m f'
      exact ⟨σ i ≫ g, by rw [toSimplexCategory.map_comp, hg, toSimplexCategory_map_σ]; rfl⟩
termination_by n + m

/-- The generators and relations supply every monotone map of finite nonempty ordinals. -/
instance : toSimplexCategory.Full where
  map_surjective {x y} f := by
    cases x using SimplexCategoryGenRel.rec
    cases y using SimplexCategoryGenRel.rec
    exact map_surjective_mk _ _ f

/-- The simplicial identities identify any two words inducing the same monotone map. -/
instance : toSimplexCategory.Faithful where
  map_injective {x y} f g h := by
    obtain ⟨z, e, i, he, hi, rfl⟩ := exists_P_σ_P_δ_factorization f
    obtain ⟨z', e', i', he', hi', rfl⟩ := exists_P_σ_P_δ_factorization g
    have := isSplitEpi_toSimplexCategory_map_of_P_σ he
    have := isSplitEpi_toSimplexCategory_map_of_P_σ he'
    have := isSplitMono_toSimplexCategory_map_of_P_δ hi
    have := isSplitMono_toSimplexCategory_map_of_P_δ hi'
    have hz : z = z' := by
      apply SimplexCategoryGenRel.ext
      have hz := SimplexCategory.image_eq
        (toSimplexCategory.map_comp e i).symm
      have hz' := SimplexCategory.image_eq
        ((toSimplexCategory.map_comp e' i').symm.trans h.symm)
      exact congrArg SimplexCategory.len (hz.symm.trans hz')
    subst z'
    have := strongEpi_of_epi (toSimplexCategory.map e)
    have := strongEpi_of_epi (toSimplexCategory.map e')
    have hiF : toSimplexCategory.map i = toSimplexCategory.map i' := by
      let E := (image.isoStrongEpiMono (toSimplexCategory.map e)
        (toSimplexCategory.map i) (toSimplexCategory.map_comp e i).symm) ≪≫
        (image.isoStrongEpiMono (toSimplexCategory.map e')
          (toSimplexCategory.map i')
          ((toSimplexCategory.map_comp e' i').symm.trans h.symm)).symm
      have hE : E.hom ≫ toSimplexCategory.map i' = toSimplexCategory.map i := by
        simp [E, Category.assoc]
      simpa only [SimplexCategory.eq_id_of_isIso E.hom, Category.id_comp] using hE.symm
    have hi_eq : i = i' := map_injective_faces i i' hi hi' hiF
    subst i'
    have heF : toSimplexCategory.map e = toSimplexCategory.map e' := by
      apply (cancel_mono (toSimplexCategory.map i)).1
      simpa only [toSimplexCategory.map_comp] using h
    rw [map_injective_degeneracies e e' he he' heF]

/-- Every finite nonempty ordinal is the image of the generator with the same length. -/
instance : toSimplexCategory.EssSurj where
  mem_essImage x := ⟨mk x.len, ⟨eqToIso (SimplexCategory.mk_len x)⟩⟩

/-- The presentation by faces, degeneracies and simplicial identities is equivalent
to the usual simplex category. -/
instance : toSimplexCategory.IsEquivalence where

end SimplexCategoryGenRel
