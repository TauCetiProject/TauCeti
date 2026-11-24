/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Centralizer

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
    obtain ⟨p, rfl⟩ := (centralizer_of_eq_range_ofProd hu).le hx
    rw [castSuccHom, lift_ofProd]
    exact (commute_of_t p.1.property _).mul_left
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
