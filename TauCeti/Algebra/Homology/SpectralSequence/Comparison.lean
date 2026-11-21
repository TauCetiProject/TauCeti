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
* `ComplexShape.add_two_mul_eq_of_up'_rel`: the differentials of the page `r` of a cohomological
  spectral sequence shift `a + 2b` at the position `(a, b)` by `±(2 - r)`, so those of the page `2`
  preserve the lines `a + 2b = const`.

An isomorphism of spectral sequences is an isomorphism on every page (an instance on `f.hom r`).
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

end CategoryTheory.SpectralSequence.Hom
