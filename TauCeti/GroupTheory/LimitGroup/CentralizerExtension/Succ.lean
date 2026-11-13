/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic

/-!
# Splitting off the last letter of an extension of a centralizer

Let `u` be an element of a group `G` such that every conjugate of `u` that commutes with `u` is `u`
itself: `g⁻¹ * u * g ∈ C_G(u)` only for `g ∈ C_G(u)`. This holds in every CSA group, for instance in
a free group. Then the centralizer of `u` in `G(u, ℤⁿ) = G ∗_{C_G(u)} (C_G(u) × ℤⁿ)` is the factor
`C_G(u) × ℤⁿ`, so extending it once more by `ℤ` gives back `G(u, ℤⁿ⁺¹)`:
`G(u, ℤⁿ⁺¹) ≃* G(u, ℤⁿ)(u, ℤ)`, the identity on `G` and on the first `n` letters, and the last
letter `tₙ` going to the new letter. Applying this `n` times, an extension of the centralizer of
`u` of rank `n` is a succession of `n` extensions of the centralizer of `u` by `ℤ`.

The hypothesis on `u` cannot be dropped once `n ≥ 1`: in the Klein bottle group
`⟨a, y | a * y * a⁻¹ = y⁻¹⟩` the element `a⁻¹ * t₀ * a` of `G(y, ℤ)` commutes with `y`, so the
next letter commutes with it in `G(y, ℤ)(y, ℤ)`, while `t₁` does not commute with it in
`G(y, ℤ²)`.

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.succEquiv`: the isomorphism `G(u, ℤⁿ⁺¹) ≃* G(u, ℤⁿ)(u, ℤ)`.

## References

* A. G. Myasnikov, V. N. Remeslennikov, *Exponential groups 2: extensions of centralizers and
  tensor completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996), §6, Lemma 1 and
  Corollary 2.
-/

public section

open Subgroup

namespace TauCeti.LimitGroup.CentralizerExt

variable {G : Type*} [Group G] {u : G} {n : ℕ}

/-- If `k * a₁ * ⋯ * aᵣ` commutes with `u` in `G(u, ℤⁿ)`, for `k ∈ G` and a reduced word
`a₁ * ⋯ * aᵣ` starting in the factor `C_G(u) × ℤⁿ`, then `k` centralizes `u`. -/
private theorem mem_centralizer_of_commute_of_mul_prod
    (hu : ∀ g : G, g⁻¹ * u * g ∈ centralizer {u} → g ∈ centralizer {u})
    {L : List (Σ b, CentralizerExtFactor u n b)} (hc : L.IsChain fun l l' => l.1 ≠ l'.1)
    (hred : ∀ l ∈ L, l.2 ∉ (centralizerExtMap u n l.1).range) (hhead : ∀ l ∈ L.head?, l.1 = true)
    {k : G} (h : Commute (of k *
      (L.map fun l => Monoid.PushoutI.of (φ := centralizerExtMap u n) l.1 l.2).prod) (of u)) :
    k ∈ centralizer {u} := by
  by_contra hk
  have huu : u ∈ centralizer {u} := mem_centralizer_singleton_iff.2 rfl
  refine Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_base
    (centralizerExtMap_injective u n) hc hred (i := false) (g := k⁻¹ * u * k) ?_
    (fun l hl => by simp [hhead l hl]) ⟨⟨u, huu⟩, ?_⟩
  · rintro ⟨c, hcu⟩
    rw [centralizerExtMap_false] at hcu
    exact hk (hu k (hcu ▸ c.2))
  · rw [← Monoid.PushoutI.of_apply_eq_base _ false, ← of_def, centralizerExtMap_false]
    simpa [mul_assoc] using h.inv_mul_cancel.symm

/-- A reduced word `a₁ * ⋯ * aᵣ` of `G(u, ℤⁿ)` that starts in the factor `C_G(u) × ℤⁿ` and
commutes with `u` lies in that factor. -/
private theorem prod_mem_range_ofProd
    (hu : ∀ g : G, g⁻¹ * u * g ∈ centralizer {u} → g ∈ centralizer {u})
    {L : List (Σ b, CentralizerExtFactor u n b)} (hc : L.IsChain fun l l' => l.1 ≠ l'.1)
    (hred : ∀ l ∈ L, l.2 ∉ (centralizerExtMap u n l.1).range) (hhead : ∀ l ∈ L.head?, l.1 = true)
    (h : Commute (L.map fun l => Monoid.PushoutI.of (φ := centralizerExtMap u n) l.1 l.2).prod
      (of u)) :
    (L.map fun l => Monoid.PushoutI.of (φ := centralizerExtMap u n) l.1 l.2).prod ∈
      (ofProd : _ →* CentralizerExt u n).range := by
  rcases L with _ | ⟨⟨_ | _, p⟩, L⟩
  · exact one_mem _
  · exact absurd (hhead _ rfl) (by simp)
  rcases L with _ | ⟨⟨_ | _, a⟩, L⟩
  · exact ⟨p, by simp [ofProd_def]⟩
  · -- The word continues with `a ∈ G ∖ C_G(u)`; as `p` commutes with `u`, so does the rest.
    simp only [List.map_cons, List.prod_cons, ← ofProd_def, ← of_def] at h
    have ha := mem_centralizer_of_commute_of_mul_prod hu hc.tail.tail
      (fun l hl => hred l (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)))
      (fun l hl => by simpa using ((List.isChain_cons.1 hc.tail).1 l hl).symm) (k := a)
      (by simpa using (commute_ofProd_of p).inv_left.mul_left h)
    exact absurd ⟨⟨a, ha⟩, by simp⟩
      (hred _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact absurd (List.isChain_cons_cons.1 hc).1 (by simp)

/-- If every conjugate of `u` commuting with `u` is `u`, the centralizer of `u` in `G(u, ℤⁿ)` lies
in the factor `C_G(u) × ℤⁿ`. -/
private theorem centralizer_of_le_range_ofProd
    (hu : ∀ g : G, g⁻¹ * u * g ∈ centralizer {u} → g ∈ centralizer {u}) :
    centralizer {(of u : CentralizerExt u n)} ≤ (ofProd : _ →* CentralizerExt u n).range := by
  intro x hx
  obtain ⟨k, L, hc, hred, hhead, rfl⟩ := exists_eq_of_mul_list_prod x
  have hx' : Commute (of k * (L.map fun l =>
      Monoid.PushoutI.of (φ := centralizerExtMap u n) l.1 l.2).prod) (of u) :=
    (commute_iff_eq _ _).2 (mem_centralizer_singleton_iff.1 hx)
  have hk := mem_centralizer_of_commute_of_mul_prod hu hc hred hhead hx'
  have hku : Commute (of k : CentralizerExt u n) (of u) :=
    ((commute_iff_eq _ _).2 (mem_centralizer_singleton_iff.1 hk)).map of
  exact mul_mem ⟨(⟨k, hk⟩, 1), ofProd_inl _⟩
    (prod_mem_range_ofProd hu hc hred hhead (by simpa using hku.inv_left.mul_left hx'))

/-- The letters `tᵢ` lie in the centralizer of `u` in `G(u, ℤⁿ)`. -/
private theorem t_mem_centralizer (i : Fin n) : (t i : CentralizerExt u n) ∈ centralizer {of u} :=
  mem_centralizer_singleton_iff.2 (commute_of_t (mem_centralizer_singleton_iff.2 rfl) i).eq.symm

/-- The images of the letters of `G(u, ℤⁿ⁺¹)` in `G(u, ℤⁿ)(u, ℤ)`: the letters of `G(u, ℤⁿ)`, and
the new letter for the last one. -/
private def succLetter (i : Fin (n + 1)) : CentralizerExt (of u : CentralizerExt u n) 1 :=
  Fin.lastCases (t 0) (fun j => of (t j)) i

/-- The images of the letters of `G(u, ℤⁿ⁺¹)` in `G(u, ℤⁿ)(u, ℤ)` commute pairwise. -/
private theorem commute_succLetter (i j : Fin (n + 1)) :
    Commute (succLetter (u := u) i) (succLetter j) := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [succLetter, Fin.lastCases_last, Fin.lastCases_castSucc]
  · exact .refl _
  · exact (commute_of_t (t_mem_centralizer _) 0).symm
  · exact commute_of_t (t_mem_centralizer _) 0
  · exact (commute_t_t _ _).map of

/-- The homomorphism `G(u, ℤⁿ⁺¹) →* G(u, ℤⁿ)(u, ℤ)` that is the identity on `G` and on the first
`n` letters and sends the last letter to the new letter. -/
private def toSucc : CentralizerExt u (n + 1) →* CentralizerExt (of u : CentralizerExt u n) 1 :=
  lift (of.comp of) succLetter commute_succLetter fun c hc i => by
    have hc' : (of c : CentralizerExt u n) ∈ centralizer {of u} := by
      simpa using map_centralizer_le_centralizer_image {u} of (mem_map_of_mem of hc)
    induction i using Fin.lastCases <;>
      simp only [succLetter, Fin.lastCases_last, Fin.lastCases_castSucc, MonoidHom.comp_apply]
    · exact commute_of_t hc' 0
    · exact (commute_of_t hc _).map of

/-- The homomorphism `G(u, ℤⁿ) →* G(u, ℤⁿ⁺¹)` that is the identity on `G` and on the letters. -/
private def castSuccHom : CentralizerExt u n →* CentralizerExt u (n + 1) :=
  lift of (fun i => t i.castSucc) (fun _ _ => commute_t_t _ _) fun _ hc _ => commute_of_t hc _

/-- The inverse of `toSucc`: the last letter commutes with the image of the centralizer of `u` in
`G(u, ℤⁿ)`, because that centralizer is the factor `C_G(u) × ℤⁿ`. -/
private def ofSucc (hu : ∀ g : G, g⁻¹ * u * g ∈ centralizer {u} → g ∈ centralizer {u}) :
    CentralizerExt (of u : CentralizerExt u n) 1 →* CentralizerExt u (n + 1) :=
  lift castSuccHom (fun _ => t (Fin.last n)) (fun _ _ => .refl _) fun x hx _ => by
    obtain ⟨p, rfl⟩ := centralizer_of_le_range_ofProd hu hx
    rw [castSuccHom, lift_ofProd]
    exact (commute_of_t p.1.2 _).mul_left
      (commute_zpowersPiHom (fun _ => commute_t_t _ _) p.2).symm

/-- **Splitting off the last letter of an extension of a centralizer.** If every conjugate of `u`
that commutes with `u` is `u` itself (for instance in a CSA group), then `G(u, ℤⁿ⁺¹)` is the
extension of the centralizer of `u` in `G(u, ℤⁿ)` by `ℤ`. The isomorphism is the identity on `G`
and on the letters `t₀, …, tₙ₋₁`, and sends the last letter `tₙ` to the new letter. -/
def succEquiv (hu : ∀ g : G, g⁻¹ * u * g ∈ centralizer {u} → g ∈ centralizer {u}) (n : ℕ) :
    CentralizerExt u (n + 1) ≃* CentralizerExt (of u : CentralizerExt u n) 1 :=
  toSucc.toMulEquiv (ofSucc hu)
    (hom_ext (by ext; simp [toSucc, ofSucc, castSuccHom]) fun i => by
      induction i using Fin.lastCases <;> simp [toSucc, ofSucc, castSuccHom, succLetter])
    (hom_ext (hom_ext (by ext; simp [toSucc, ofSucc, castSuccHom]) fun i => by
        simp [toSucc, ofSucc, castSuccHom, succLetter]) fun i => by
      simp [toSucc, ofSucc, succLetter, Subsingleton.elim i 0])

variable (hu : ∀ g : G, g⁻¹ * u * g ∈ centralizer {u} → g ∈ centralizer {u})

@[simp] theorem succEquiv_of (g : G) : succEquiv hu n (of g) = of (of g) :=
  lift_of _ _ _ _ g

@[simp] theorem succEquiv_t_castSucc (i : Fin n) : succEquiv hu n (t i.castSucc) = of (t i) := by
  simp [succEquiv, toSucc, succLetter]

@[simp] theorem succEquiv_t_last : succEquiv hu n (t (Fin.last n)) = t 0 := by
  simp [succEquiv, toSucc, succLetter]

@[simp] theorem succEquiv_symm_of_of (g : G) : (succEquiv hu n).symm (of (of g)) = of g :=
  (succEquiv hu n).symm_apply_eq.2 (succEquiv_of hu g).symm

@[simp] theorem succEquiv_symm_of_t (i : Fin n) :
    (succEquiv hu n).symm (of (t i)) = t i.castSucc :=
  (succEquiv hu n).symm_apply_eq.2 (succEquiv_t_castSucc hu i).symm

@[simp] theorem succEquiv_symm_t (i : Fin 1) : (succEquiv hu n).symm (t i) = t (Fin.last n) :=
  (succEquiv hu n).symm_apply_eq.2 (by rw [succEquiv_t_last, Subsingleton.elim i 0])

end TauCeti.LimitGroup.CentralizerExt
