/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import TauCeti.AlgebraicTopology.DGNerve.HornFilling
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# The differential graded nerve is a quasicategory

Every inner horn `Λ[n, k] ⟶ N_dg(C)` in the differential graded nerve of a dg category has a
filler, so `TauCeti.dgNerve R C` is a quasicategory. The faces of the horn are glued into
coherences on the horn: a coherence missing a vertex `l ≠ k` is read off the face opposite to `l`,
extended degenerately to the whole simplex, and two faces give the same coherence because they
agree on their common face. These coherences satisfy the dg nerve equation, since each of them
lies in a face, so `TauCeti.DGNerve.Coherences.exists_simplex_of_horn` fills the horn. Outer horns
do not fill in general.

## Main results

* `TauCeti.dgNerve.quasicategory`: the differential graded nerve is a quasicategory.

## References

* J. Lurie, *Higher Algebra*, Proposition 1.3.1.10.
-/

public section

open CategoryTheory Finset Simplicial

namespace TauCeti

universe v u

namespace DGNerve

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C] {n : ℕ}

/-- Two faces `a < b` of a horn that agree on their common face give the same coherences away from
`a` and `b`, once extended degenerately to the whole simplex along retractions `ρa` and `ρb` of
the face maps. -/
private lemma map_coh_heq_of_retraction {a b : Fin (n + 3)} (hab : a < b)
    (ya yb : Simplex R C (n + 1))
    (hy : ya.map (SimplexCategory.δ (b.pred (Fin.ne_zero_of_lt hab))).toOrderHom =
      yb.map (SimplexCategory.δ (a.castPred (Fin.ne_last_of_lt hab))).toOrderHom)
    {ρa ρb : Fin (n + 3) →o Fin (n + 2)} (hρa : ∀ v, v ≠ a → a.succAbove (ρa v) = v)
    (hρb : ∀ v, v ≠ b → b.succAbove (ρb v) = v) {ρ' : Fin (n + 2) →o Fin (n + 1)}
    (hρ' : ∀ w, w ≠ b.pred (Fin.ne_zero_of_lt hab) →
      (b.pred (Fin.ne_zero_of_lt hab)).succAbove (ρ' w) = w)
    {i j : Fin (n + 3)} {S : Finset (Fin (n + 3))} {d : ℤ} {hij : i ≤ j} {hS : S ⊆ Ioo i j}
    {hd : d + #S = 0} (hT : ∀ v, (v = i ∨ v = j ∨ v ∈ S) → v ≠ a ∧ v ≠ b) :
    (ya.map ρa).coh i j S d hij hS hd ≍ (yb.map ρb).coh i j S d hij hS hd := by
  set a' := a.castPred (Fin.ne_last_of_lt hab)
  set b' := b.pred (Fin.ne_zero_of_lt hab)
  -- The first simplicial identity, evaluated at a vertex.
  have hδδ : ∀ w, b.succAbove (a'.succAbove w) = a.succAbove (b'.succAbove w) := fun w ↦ by
    have := congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2) ↦ f.toOrderHom w)
      (SimplexCategory.δ_comp_δ' (i := a') (j := b) (by simpa [a'] using hab))
    simpa [SimplexCategory.δ, a', b'] using this
  -- Both extensions factor, away from `a` and `b`, through the common face.
  let γ : Fin (n + 3) →o Fin (n + 1) := ρ'.comp ρa
  have h₁ : ∀ v, v ≠ a → v ≠ b → b'.succAbove (γ v) = ρa v := fun v hva hvb ↦
    hρ' _ fun h ↦ hvb (by
      rw [← hρa v hva, h]
      exact Fin.succAbove_pred_of_lt a b hab)
  have h₂ : ∀ v, v ≠ a → v ≠ b → a'.succAbove (γ v) = ρb v := fun v hva hvb ↦
    Fin.succAbove_right_injective (p := b) (by rw [hρb v hvb, hδδ, h₁ v hva hvb, hρa v hva])
  have hT' := fun s (hs : s ∈ S) ↦ hT s (Or.inr (Or.inr hs))
  refine (ya.map_coh_heq (β := (SimplexCategory.δ b').toOrderHom.comp γ)
    (h₁ i (hT i (Or.inl rfl)).1 (hT i (Or.inl rfl)).2).symm
    (h₁ j (hT j (Or.inr (Or.inl rfl))).1 (hT j (Or.inr (Or.inl rfl))).2).symm
    fun s hs ↦ (h₁ s (hT' s hs).1 (hT' s hs).2).symm).trans ?_
  rw [← Simplex.map_map, hy, Simplex.map_map]
  exact yb.map_coh_heq (h₂ i (hT i (Or.inl rfl)).1 (hT i (Or.inl rfl)).2)
    (h₂ j (hT j (Or.inr (Or.inl rfl))).1 (hT j (Or.inr (Or.inl rfl))).2)
    fun s hs ↦ h₂ s (hT' s hs).1 (hT' s hs).2

/-- **Inner horn filling for simplices of the differential graded nerve**: faces `y l` for
`l ≠ k`, with objects given by `X` and agreeing on their common faces, are the faces of an
`(n + 2)`-simplex, provided `0 < k < n + 2`. -/
private theorem exists_map_δ_eq {k : Fin (n + 3)} (hk₀ : 0 < k) (hkn : k < Fin.last (n + 2))
    (X : Fin (n + 3) → C) (y : ∀ l, l ≠ k → Simplex R C (n + 1))
    (hX : ∀ l hl p, (y l hl).obj p = X (l.succAbove p))
    (hy : ∀ a b (ha : a ≠ k) (hb : b ≠ k) (hab : a < b),
      (y a ha).map (SimplexCategory.δ (b.pred (Fin.ne_zero_of_lt hab))).toOrderHom =
        (y b hb).map (SimplexCategory.δ (a.castPred (Fin.ne_last_of_lt hab))).toOrderHom) :
    ∃ x : Simplex R C (n + 2), ∀ l hl, x.map (SimplexCategory.δ l).toOrderHom = y l hl := by
  classical
  have hsub : ∀ (l : Fin (n + 3)) {i' j' : Fin (n + 2)} {S' : Finset (Fin (n + 2))},
      S' ⊆ Ioo i' j' → S'.image l.succAbove ⊆ Ioo (l.succAbove i') (l.succAbove j') :=
    fun l i' j' S' hS ↦ by
      rw [← coe_subset, coe_image, coe_Ioo]
      exact (Set.image_mono (by rwa [← coe_Ioo, coe_subset])).trans
        (Fin.strictMono_succAbove l).image_Ioo_subset
  -- Each face map has a monotone retraction.
  have hretr : ∀ {m : ℕ} (l : Fin (m + 2)),
      ∃ ρ : Fin (m + 2) →o Fin (m + 1), ∀ v, v ≠ l → l.succAbove (ρ v) = v := by
    intro m l
    by_cases hl : l = Fin.last (m + 1)
    · subst hl
      refine ⟨⟨(Fin.last m).predAbove, Fin.predAbove_right_monotone _⟩, fun v hv ↦ ?_⟩
      rw [← Fin.succ_last] at hv ⊢
      exact Fin.succ_succAbove_predAbove hv
    · refine ⟨⟨(l.castPred hl).predAbove, Fin.predAbove_right_monotone _⟩, fun v hv ↦ ?_⟩
      have := Fin.succAbove_predAbove (p := l.castPred hl) (i := v)
        (by rwa [Fin.castSucc_castPred])
      rwa [Fin.castSucc_castPred] at this
  choose ρ hρ using fun l : Fin (n + 3) ↦ hretr l
  have hρδ : ∀ l w, ρ l (l.succAbove w) = w := fun l w ↦
    Fin.succAbove_right_injective (hρ l _ (Fin.succAbove_ne l w))
  -- The face opposite to `l`, extended degenerately to the whole simplex, has the objects `X`
  -- away from `l`, and two such extensions have the same coherences away from both faces.
  have hz : ∀ l hl v, v ≠ l → ((y l hl).map (ρ l)).obj v = X v := fun l hl v hv ↦
    (hX l hl _).trans (congrArg X (hρ l v hv))
  have hind : ∀ a b (ha : a ≠ k) (hb : b ≠ k) {i j S d hij hS hd},
      (∀ v, (v = i ∨ v = j ∨ v ∈ S) → v ≠ a ∧ v ≠ b) →
      ((y a ha).map (ρ a)).coh i j S d hij hS hd ≍
        ((y b hb).map (ρ b)).coh i j S d hij hS hd := by
    intro a b ha hb i j S d hij hS hd hT
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact map_coh_heq_of_retraction hab _ _ (hy a b ha hb hab) (hρ a) (hρ b)
        (hretr _).choose_spec hT
    · rfl
    · exact (map_coh_heq_of_retraction hab _ _ (hy b a hb ha hab) (hρ b) (hρ a)
        (hretr _).choose_spec fun v hv ↦ (hT v hv).symm).symm
  -- The glued coherences: on a coherence of the horn, read off any face containing it.
  let f : Coherences R X := fun i j S d hij hS hd ↦
    if h : ∃ l, l ≠ k ∧ l ≠ i ∧ l ≠ j ∧ l ∉ S then
      cast (congrArg₂ (DGHom R d) (hz _ h.choose_spec.1 i (Ne.symm h.choose_spec.2.1))
          (hz _ h.choose_spec.1 j (Ne.symm h.choose_spec.2.2.1)))
        (((y _ h.choose_spec.1).map (ρ h.choose)).coh i j S d hij hS hd)
    else 0
  have hf : ∀ l (hl : l ≠ k) {i j S d hij hS hd}, l ≠ i → l ≠ j → l ∉ S →
      f i j S d hij hS hd ≍ ((y l hl).map (ρ l)).coh i j S d hij hS hd := by
    intro l hl i j S d hij hS hd hli hlj hlS
    have h : ∃ l, l ≠ k ∧ l ≠ i ∧ l ≠ j ∧ l ∉ S := ⟨l, hl, hli, hlj, hlS⟩
    refine (heq_of_eq (dite_eq_left h)).trans ((cast_heq _ _).trans (hind _ _ _ _ ?_))
    obtain ⟨-, hi, hj, hS'⟩ := h.choose_spec
    rintro v (rfl | rfl | hv)
    · exact ⟨Ne.symm hi, Ne.symm hli⟩
    · exact ⟨Ne.symm hj, Ne.symm hlj⟩
    · exact ⟨fun h ↦ hS' (h ▸ hv), fun h ↦ hlS (h ▸ hv)⟩
  -- On the face opposite to `l` the glued coherences are those of `y l`.
  have hface : ∀ l (hl : l ≠ k) {i' j' S'} {d : ℤ} (hij : i' ≤ j') (hS : S' ⊆ Ioo i' j')
      (hd : d + #S' = 0), f.comap (Fin.strictMono_succAbove l) i' j' S' d hij hS hd ≍
        (y l hl).coh i' j' S' d hij hS hd := by
    intro l hl i' j' S' d hij hS hd
    rw [Coherences.comap_apply _ _ _ _ _ ((Fin.strictMono_succAbove l).monotone hij) (hsub l hS)
      (by rwa [card_image_of_injective _ (Fin.strictMono_succAbove l).injective])]
    refine (hf l hl (Fin.succAbove_ne l i').symm (Fin.succAbove_ne l j').symm
      (by simp [Fin.succAbove_ne])).trans ((heq_of_eq (((y l hl).map (ρ l)).map_coh_of_strictMono
        (α := (SimplexCategory.δ l).toOrderHom) (Fin.strictMono_succAbove l) hij hS hd
          (hsub l hS)).symm).trans
          ?_)
    rw [Simplex.map_map]
    refine ((y l hl).map_coh_heq (β := OrderHom.id) (hρδ l i') (hρδ l j')
      fun s _ ↦ hρδ l s).trans ?_
    rw [Simplex.map_id]
  have hself : ∀ i, f i i ∅ 0 le_rfl (empty_subset _) (by simp) = dgId R (X i) := by
    intro i
    obtain ⟨l, hl, hli⟩ : ∃ l, l ≠ k ∧ l ≠ i := by
      by_cases hi : i = 0
      · exact ⟨Fin.last (n + 2), hkn.ne', fun h ↦ (hk₀.trans hkn).ne' (h.trans hi)⟩
      · exact ⟨0, hk₀.ne, Ne.symm hi⟩
    exact eq_of_heq ((hf l hl hli hli (notMem_empty _)).trans
      ((heq_of_eq (Simplex.coh_self _ i)).trans (by rw [hz l hl i (Ne.symm hli)])))
  -- On the horn, the glued coherences satisfy the dg nerve equation, read off a face.
  have heq : ∀ i j S d hij hS hd, (∃ l, l ≠ k ∧ l ≠ i ∧ l ≠ j ∧ l ∉ S) →
      dgDifferential R d (f i j S d hij hS hd) = boundary R f i j S d hij hS hd := by
    rintro i j S d hij hS hd ⟨l, hl, hli, hlj, hlS⟩
    have he := Fin.strictMono_succAbove l
    obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hli)
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hlj)
    obtain ⟨S', rfl⟩ : ∃ S', S'.image l.succAbove = S :=
      ⟨S.preimage l.succAbove Fin.succAbove_right_injective.injOn, by
        rw [image_preimage]
        exact filter_true_of_mem fun s hs ↦ Fin.exists_succAbove_eq fun h ↦ hlS (h ▸ hs)⟩
    have hij' : i' ≤ j' := he.le_iff_le.1 hij
    have hS' : S' ⊆ Ioo i' j' := fun s hs ↦ by
      have := mem_Ioo.1 (hS (mem_image_of_mem _ hs))
      exact mem_Ioo.2 ⟨he.lt_iff_lt.1 this.1, he.lt_iff_lt.1 this.2⟩
    have hd' : d + #S' = 0 := by rwa [card_image_of_injective _ he.injective] at hd
    let y' := (y l hl).copy (X ∘ l.succAbove) (funext (hX l hl))
    have hcomap : f.comap he = y'.coh := by
      funext i₁ j₁ S₁ d₁ h₁ h₂ h₃
      exact eq_of_heq ((hface l hl h₁ h₂ h₃).trans (congr_arg_heq
        (fun s : Simplex R C (n + 1) ↦ s.coh i₁ j₁ S₁ d₁ h₁ h₂ h₃) ((y l hl).copy_eq _ _)).symm)
    rw [← Coherences.comap_apply f he hij' hS' hd', ← boundary_comap f he hij' hS' hd', hcomap]
    exact y'.dgDifferential_coh i' j' S' d hij' hS' hd'
  obtain ⟨x, hxobj, hxcoh⟩ := f.exists_simplex_of_horn hk₀ hkn hself heq
  refine ⟨x, fun l hl ↦ Simplex.ext (funext fun p ↦ (congrFun hxobj _).trans (hX l hl p).symm)
    fun i' j' S' d hij hS hd ↦ ?_⟩
  refine (heq_of_eq (x.map_coh_of_strictMono (α := (SimplexCategory.δ l).toOrderHom)
    (Fin.strictMono_succAbove l) hij hS hd (hsub l hS))).trans ?_
  refine (hxcoh _ _ _ _ _ _ _ ⟨l, hl, (Fin.succAbove_ne l i').symm, (Fin.succAbove_ne l j').symm,
    fun h ↦ ?_⟩).trans ((heq_of_eq (Coherences.comap_apply _ _ _ _ _ _ _ _).symm).trans
      (hface l hl hij hS hd))
  obtain ⟨s, -, hs⟩ := mem_image.1 h
  exact Fin.succAbove_ne l s hs

end DGNerve

open DGNerve SSet

/-- **The differential graded nerve is a quasicategory**: every inner horn in it has a filler. -/
instance dgNerve.quasicategory (R : Type v) [CommRing R] (C : Type u) [DGCategory R C] :
    (dgNerve R C).Quasicategory where
  hornFilling' n k σ₀ hk₀ hkn := by
    -- The faces of the horn have the objects of its vertices, and agree on common faces.
    have hX : ∀ l (hl : l ≠ k) p, Simplex.obj (R := R) (σ₀.app _ (horn.face k l hl)) p =
        Simplex.obj (R := R) (σ₀.app (Opposite.op ⦋0⦌) (horn.const n k (l.succAbove p) _)) 0 := by
      intro l hl p
      have h := NatTrans.naturality_apply σ₀ (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ p).op
        (horn.face k l hl)
      have hc : (Λ[n + 2, k] : SSet).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ p).op
          (horn.face k l hl) = horn.const n k (l.succAbove p) _ := by
        apply Subtype.ext
        ext i
        fin_cases i
        rfl
      rw [hc] at h
      rw [h]
      rfl
    have hy : ∀ a b (ha : a ≠ k) (hb : b ≠ k) (hab : a < b),
        Simplex.map (σ₀.app _ (horn.face k a ha))
          (SimplexCategory.δ (b.pred (Fin.ne_zero_of_lt hab))).toOrderHom =
        Simplex.map (σ₀.app _ (horn.face k b hb))
          (SimplexCategory.δ (a.castPred (Fin.ne_last_of_lt hab))).toOrderHom := by
      intro a b ha hb hab
      have h := (horn.isCompatible_iff _).1 (horn.IsCompatible.of_hom σ₀) a b ha hb hab
      rw [horn.ι, horn.ι, yonedaEquiv_symm_comp, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm] at h
      exact SSet.yonedaEquiv.symm.injective h
    obtain ⟨x, hx⟩ := exists_map_δ_eq (R := R) hk₀ hkn
      (fun i ↦ Simplex.obj (R := R) (σ₀.app (Opposite.op ⦋0⦌) (horn.const n k i _)) 0) _ hX hy
    let x' : (dgNerve R C) _⦋n + 2⦌ := x
    refine ⟨yonedaEquiv.symm x', horn.hom_ext' fun l hl ↦ ?_⟩
    rw [horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.eq_symm_apply,
      SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι]
    exact (hx l hl).symm

end TauCeti
