/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Comparison of spectral sequences on later pages

A morphism `f : E ⟶ E'` of spectral sequences commutes with the identifications of the homology
of a page with the next page. Hence if `f` is an isomorphism on every object of the `r`th page,
it is an isomorphism on the homology of the `r`th page, so on every object of the `(r + 1)`st
page, and, by induction, on every object of every page `r' ≥ r`.

## Main results

* `CategoryTheory.SpectralSequence.Hom.isIso_hom_f_add_one`: the comparison at one position, from
  the three positions joined by the differentials of the previous page.
* `CategoryTheory.SpectralSequence.Hom.isIso_hom_f_of_le`: the comparison on later pages.
* `CategoryTheory.SpectralSequence.Hom.isIso_of_isIso_hom_f`: a morphism which is an isomorphism
  on every object of the first page is an isomorphism of spectral sequences.
* `CategoryTheory.SpectralSequence.Hom.hom_add_one_eq`,
  `CategoryTheory.SpectralSequence.Hom.hom_eq_of_le`: two morphisms which agree on the `r`th page
  agree on every later page.
* `ComplexShape.add_two_mul_eq_of_up'_rel`: the differentials of the page `r` of a cohomological
  spectral sequence shift `a + 2b` at the position `(a, b)` by `±(2 - r)`, so those of the page `2`
  preserve the lines `a + 2b = const`.
* `ComplexShape.snd_eq_of_up'_rel`: the differentials of the page `r` of a cohomological spectral
  sequence shift the second coordinate `b` by `±(r - 1)`.

An isomorphism of spectral sequences is an isomorphism on every page (an instance on `f.hom r`).

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Chapter 3 (comparison theorem).
-/

public section

namespace ComplexShape

/-- A differential of the page `r` of a cohomological spectral sequence shifts `a + 2b` at the
position `(a, b)` by `2 - r` in one direction or the other; in particular the differentials of the
page `2` preserve `a + 2b`. -/
lemma add_two_mul_eq_of_up'_rel {r : ℤ} {pq pq' : ℤ × ℤ}
    (h : (up' ((r, 1 - r) : ℤ × ℤ)).Rel pq pq' ∨ (up' ((r, 1 - r) : ℤ × ℤ)).Rel pq' pq) :
    pq'.1 + 2 * pq'.2 = pq.1 + 2 * pq.2 + (2 - r) ∨
      pq'.1 + 2 * pq'.2 = pq.1 + 2 * pq.2 - (2 - r) := by
  rcases h with rfl | rfl
  · left
    simp only [Prod.fst_add, Prod.snd_add]
    lia
  · right
    simp only [Prod.fst_add, Prod.snd_add]
    lia

/-- A differential of the page `r` of a cohomological spectral sequence shifts the second
coordinate `b` of the position `(a, b)` by `r - 1` in one direction or the other. -/
lemma snd_eq_of_up'_rel {r : ℤ} {pq pq' : ℤ × ℤ}
    (h : (up' ((r, 1 - r) : ℤ × ℤ)).Rel pq pq' ∨ (up' ((r, 1 - r) : ℤ × ℤ)).Rel pq' pq) :
    pq'.2 = pq.2 + 1 - r ∨ pq'.2 = pq.2 - 1 + r := by
  rcases h with h | h <;> have := congrArg Prod.snd h <;> simp only [Prod.snd_add] at this <;> lia

end ComplexShape

namespace CategoryTheory.SpectralSequence.Hom

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {E E' : SpectralSequence C c r₀} (f : E ⟶ E')

/-- An isomorphism of spectral sequences is an isomorphism on every page. -/
instance [IsIso f] (r : ℤ) (hr : r₀ ≤ r) : IsIso (f.hom r hr) :=
  ⟨(inv f).hom r hr, by rw [← comp_hom _ _ r hr, IsIso.hom_inv_id, id_hom],
    by rw [← comp_hom _ _ r hr, IsIso.inv_hom_id, id_hom]⟩

/-- A morphism of spectral sequences which is an isomorphism, on the `r`th page, at `pq` and at
the two positions joined to `pq` by the differentials of that page is an isomorphism at `pq` on
the `(r + 1)`st page. -/
lemma isIso_hom_f_add_one (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (h : ∀ pq', pq' = pq ∨ (c r).Rel pq pq' ∨ (c r).Rel pq' pq → IsIso ((f.hom r hr).f pq')) :
    IsIso ((f.hom (r + 1) (hr.trans (Int.le_add_one le_rfl))).f pq) := by
  have h₁ : IsIso ((f.hom r hr).f ((c r).prev pq)) := by
    by_cases hp : (c r).Rel ((c r).prev pq) pq
    · exact h _ (Or.inr (Or.inr hp))
    · rw [(c r).prev_eq_self pq hp]
      exact h _ (Or.inl rfl)
  have h₃ : IsIso ((f.hom r hr).f ((c r).next pq)) := by
    by_cases hn : (c r).Rel pq ((c r).next pq)
    · exact h _ (Or.inr (Or.inl hn))
    · rw [(c r).next_eq_self pq hn]
      exact h _ (Or.inl rfl)
  have : IsIso (HomologicalComplex.homologyMap (f.hom r hr) pq) :=
    ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
      ((HomologicalComplex.shortComplexFunctor _ _ pq).map (f.hom r hr))
      (inferInstanceAs (Epi ((f.hom r hr).f _))) (h pq (Or.inl rfl))
      (inferInstanceAs (Mono ((f.hom r hr).f _)))
  rw [← isIso_comp_left_iff (E.iso r _ pq).hom, ← f.comm r (r + 1)]
  infer_instance

/-- A morphism of spectral sequences which is an isomorphism on every object of the `r`th page is
an isomorphism on every object of every page `r' ≥ r`. -/
lemma isIso_hom_f_of_le (r : ℤ) (hr : r₀ ≤ r) (h : ∀ pq, IsIso ((f.hom r hr).f pq))
    (r' : ℤ) (hrr' : r ≤ r') (pq : κ) :
    IsIso ((f.hom r' (hr.trans hrr')).f pq) := by
  induction r', hrr' using Int.leInduction generalizing pq with
  | base => exact h pq
  | succ r' hrr' ih => exact f.isIso_hom_f_add_one r' (hr.trans hrr') pq fun pq' _ ↦ ih pq'

/-- Two morphisms of spectral sequences which agree on the `r`th page agree on the `(r + 1)`st
page: each is determined there, through the identifications of the homology of a page with the
next page, by the map it induces on the homology of the `r`th page. -/
lemma hom_add_one_eq (g : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) (h : f.hom r hr = g.hom r hr) :
    f.hom (r + 1) (hr.trans (Int.le_add_one le_rfl)) =
      g.hom (r + 1) (hr.trans (Int.le_add_one le_rfl)) := by
  ext pq : 1
  rw [← cancel_epi (E.iso r (r + 1) pq).hom, ← f.comm r (r + 1), ← g.comm r (r + 1), h]

/-- Two morphisms of spectral sequences which agree on the `r`th page agree on every page
`r' ≥ r`. -/
lemma hom_eq_of_le (g : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) (h : f.hom r hr = g.hom r hr) (r' : ℤ)
    (hrr' : r ≤ r') : f.hom r' (hr.trans hrr') = g.hom r' (hr.trans hrr') := by
  induction r', hrr' using Int.leInduction with
  | base => exact h
  | succ r' hrr' ih => exact f.hom_add_one_eq g r' (hr.trans hrr') ih

/-- **The comparison theorem.** A morphism of spectral sequences which is an isomorphism on every
object of the first page `r₀` is an isomorphism of spectral sequences: its inverse is, on every
page, the inverse of the morphism of that page, which is an isomorphism on every object by
`CategoryTheory.SpectralSequence.Hom.isIso_hom_f_of_le`. -/
lemma isIso_of_isIso_hom_f (h : ∀ pq, IsIso ((f.hom r₀ le_rfl).f pq)) : IsIso f := by
  have (r : ℤ) (hr : r₀ ≤ r) : IsIso (f.hom r hr) :=
    have := f.isIso_hom_f_of_le r₀ le_rfl h r hr
    HomologicalComplex.Hom.isIso_of_components _
  refine ⟨⟨{ hom r hr := inv (f.hom r hr), comm r r' pq hrr' hr := ?_ }, ?_, ?_⟩⟩
  · -- The square for the inverses is the square for `f`, composed with the inverses on both sides.
    rw [← cancel_mono ((f.hom r' (hr.trans (by lia))).f pq), Category.assoc, Category.assoc,
      ← f.comm r r' pq]
    simp
  all_goals ext r hr : 1; simp

end CategoryTheory.SpectralSequence.Hom
