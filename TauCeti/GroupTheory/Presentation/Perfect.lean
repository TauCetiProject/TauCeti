/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation
public import TauCeti.GroupTheory.IsPerfect
public import TauCeti.GroupTheory.Presentation.ExponentSum

/-!
# Perfectness of two-generator presentations

A two-generator presentation defines a perfect group if its transcribed relations include
power relations on both generators and their product with pairwise coprime exponents.
Additional relations are allowed, so the criterion applies without checking the rest of the
presentation or assuming finiteness.

More generally, a presentation defines a perfect group when integer combinations of the
exponent-sum vectors of its transcribed relators give every unit vector: every homomorphism to a
commutative group then kills each generator.

## Main results

* `TauCeti.GroupPresentation.isPerfect_of_coprime`: the coprime power-relation criterion.
* `TauCeti.GroupPresentation.eq_one_of_expSum`: a homomorphism to a commutative group is trivial
  when combinations of the relators' exponent sums give every unit vector.
* `TauCeti.GroupPresentation.isPerfect_of_expSum` and `isPerfect_of_expSum_two`: the resulting
  perfectness criterion, and its form for two generators.
-/

public section

namespace TauCeti.GroupPresentation

/-- A two-generator presentation containing pairwise coprime power relations on the generators
and their product defines a perfect group. -/
theorem isPerfect_of_coprime (P : GroupPresentation) (hP : P.generatorCount = 2)
    {a b c : ℕ}
    (ha : .pow (.gen ⟨0, by omega⟩) a ∈ P.transcribed)
    (hb : .pow (.gen ⟨1, by omega⟩) b ∈ P.transcribed)
    (hc : .pow (.mul (.gen ⟨0, by omega⟩) (.gen ⟨1, by omega⟩)) c ∈ P.transcribed)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    Group.IsPerfect P.Group := by
  let x : P.Group := PresentedGroup.of ⟨0, by omega⟩
  let y : P.Group := PresentedGroup.of ⟨1, by omega⟩
  have hgen : Subgroup.closure ({x, y} : Set P.Group) = ⊤ := by
    apply top_unique
    rw [← PresentedGroup.closure_range_of]
    apply Subgroup.closure_mono
    rintro _ ⟨i, rfl⟩
    have hi : i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
      rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hi with rfl | rfl <;> simp [x, y]
  apply isPerfect_of_coprime_pow_eq_one hgen (a := a) (b := b) (c := c)
  · simpa only [Relator.eval_pow, Relator.eval_gen] using P.eval_of_eq_one _ ha
  · simpa only [Relator.eval_pow, Relator.eval_gen] using P.eval_of_eq_one _ hb
  · simpa only [Relator.eval_pow, Relator.eval_mul, Relator.eval_gen] using P.eval_of_eq_one _ hc
  · exact hab
  · exact hac
  · exact hbc

/-- Every homomorphism from a presented group to a commutative group is trivial when, for each
generator `i`, a list of integer coefficients combines the transcribed relators position by
position into total exponent `1` at `i` and `0` at every other generator. Coefficients beyond
the end of the relator list are ignored. -/
theorem eq_one_of_expSum (P : GroupPresentation)
    (h : ∀ i, ∃ cs : List ℤ, ∀ j,
      (List.zipWith (fun c r => c * r.expSum j) cs P.transcribed).sum = if j = i then 1 else 0)
    {G : Type*} [CommGroup G] (f : P.Group →* G) : f = 1 := by
  refine PresentedGroup.ext fun i => ?_
  obtain ⟨cs, hcs⟩ := h i
  let g : Fin P.generatorCount → G := fun j => f (PresentedGroup.of j)
  have hrel : ∀ r ∈ P.transcribed, ∏ j, g j ^ r.expSum j = 1 := by
    intro r hr
    have := Relator.map_eval f PresentedGroup.of r
    rw [P.eval_of_eq_one r hr, map_one] at this
    rw [← Relator.eval_eq_prod_zpow]
    exact this.symm
  have hcomb : ∀ (cs : List ℤ) (rs : List (Relator (Fin P.generatorCount))),
      (∀ r ∈ rs, ∏ j, g j ^ r.expSum j = 1) →
      ∏ j, g j ^ (List.zipWith (fun c r => c * r.expSum j) cs rs).sum = 1 := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      intro rs hrs
      cases rs with
      | nil => simp
      | cons r rs =>
        simp only [List.zipWith_cons_cons, List.sum_cons, zpow_add, Finset.prod_mul_distrib]
        rw [ih rs fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'), mul_one]
        calc ∏ j, g j ^ (c * r.expSum j) = (∏ j, g j ^ r.expSum j) ^ c := by
              rw [← Finset.prod_zpow]
              simp only [← zpow_mul, mul_comm]
          _ = 1 := by rw [hrs r List.mem_cons_self, one_zpow]
  have key := hcomb cs P.transcribed hrel
  simp only [hcs] at key
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ i) h)]
    at key
  simpa [g] using key

/-- A presentation defines a perfect group when, for each generator `i`, a list of integer
coefficients combines the transcribed relators into total exponent `1` at `i` and `0` at every
other generator. -/
theorem isPerfect_of_expSum (P : GroupPresentation)
    (h : ∀ i, ∃ cs : List ℤ, ∀ j,
      (List.zipWith (fun c r => c * r.expSum j) cs P.transcribed).sum = if j = i then 1 else 0) :
    Group.IsPerfect P.Group := by
  constructor
  rw [← Group.Abelianization.ker_of, P.eq_one_of_expSum h Group.Abelianization.of]
  exact MonoidHom.ker_one

/-- The two-generator form of `isPerfect_of_expSum`: the coefficient lists `cs₀` and `cs₁`
combine the transcribed relators into exponent sums `(1, 0)` and `(0, 1)`. -/
theorem isPerfect_of_expSum_two (P : GroupPresentation) (hP : P.generatorCount = 2)
    (cs₀ cs₁ : List ℤ)
    (h₀₀ : (List.zipWith (fun c r => c * r.expSum ⟨0, by omega⟩) cs₀ P.transcribed).sum = 1)
    (h₀₁ : (List.zipWith (fun c r => c * r.expSum ⟨1, by omega⟩) cs₀ P.transcribed).sum = 0)
    (h₁₀ : (List.zipWith (fun c r => c * r.expSum ⟨0, by omega⟩) cs₁ P.transcribed).sum = 0)
    (h₁₁ : (List.zipWith (fun c r => c * r.expSum ⟨1, by omega⟩) cs₁ P.transcribed).sum = 1) :
    Group.IsPerfect P.Group := by
  have two : ∀ i : Fin P.generatorCount, i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
    intro i
    rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  refine P.isPerfect_of_expSum fun i => ?_
  rcases two i with rfl | rfl
  · refine ⟨cs₀, fun j => ?_⟩
    rcases two j with rfl | rfl
    · simpa using h₀₀
    · simpa using h₀₁
  · refine ⟨cs₁, fun j => ?_⟩
    rcases two j with rfl | rfl
    · simpa using h₁₀
    · simpa using h₁₁

end TauCeti.GroupPresentation
