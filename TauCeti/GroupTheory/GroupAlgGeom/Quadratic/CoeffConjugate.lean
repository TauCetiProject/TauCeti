/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic

/-!
# Standard quadratic words are not conjugate to coefficients

By [IFT], §2.7, Lemma 1, a strictly quadratic word of `G[X] = G ∗ F(X)` is carried to a
standard quadratic word by an automorphism of `G[X]` fixing `G`. As stated this fails for the
coefficients and their conjugates, such as the strictly quadratic word `z⁻¹ c z`: the reduction
ends, after a conjugation, either at a coefficient `c ∈ G` or at a standard quadratic word. This
file shows that the two alternatives exclude each other: no standard quadratic word is conjugate
in `G[X]` to a coefficient, the trivial coefficient included
(`TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_inl`). Consequently a conjugate
`v⁻¹ c v` of a coefficient is not carried to a standard quadratic word by any homomorphism sending
`c` to a coefficient `d` followed by a conjugation (`Standard.toWord_ne_conj_map_conj_inl`). For
`z⁻¹ c z` with `c ≠ 1` this shows that the coefficient alternative cannot be avoided.

The separation follows from cyclic reduction relative to `G`: a standard quadratic word has a
cyclically reduced normal form (`Standard.isCyclicallyReduced_reducedWord`) in which every variable
from its nonempty variable set `S.vars` occurs twice (`Standard.vars_nonempty`,
`Standard.occurrences_toWord_of_mem_vars`), whereas any cyclically reduced word conjugate to a
coefficient has no variable letters (`GX.IsCyclicallyReduced.countVar_eq_zero_of_eq_conj_inl`).

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_inl`: a standard quadratic
  word is not conjugate to a coefficient.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_map_conj_inl`: a homomorphism
  sending a coefficient to a coefficient and a conjugation do not carry a conjugate of that
  coefficient to a standard quadratic word.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definition 3 and Lemma 1.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

variable {G X : Type*} [Group G]

/-! ### Standard quadratic words and coefficients -/

/-- **A standard quadratic word is not conjugate to a coefficient**, the trivial coefficient
included. Hence the two possible outcomes of reducing a strictly quadratic word by automorphisms
of `G[X]` fixing `G` and conjugations, a coefficient or a standard quadratic word, exclude each
other. -/
theorem toWord_ne_conj_inl (S : Standard G X) (u : GX G X) (g : G) :
    S.toWord ≠ u * inl g * u⁻¹ := by
  intro h
  obtain ⟨x, hx⟩ := S.vars_nonempty
  have hc := S.isCyclicallyReduced_reducedWord.countVar_eq_zero_of_eq_conj_inl
    (by simpa [GX.prod_reducedWord] using h) x
  have ho := S.occurrences_toWord_of_mem_vars hx
  rw [occurrences_eq_countVar_reducedWord, hc] at ho
  exact absurd ho (by decide)

/-- A homomorphism `A[Y] → G[X]` sending the coefficient `inl c` to a coefficient `inl d`,
followed by a conjugation, does not carry a conjugate `v⁻¹ c v` of `c` to a standard quadratic
word. For instance the strictly quadratic word `z⁻¹ c z` is not brought to a standard quadratic
word by a change of coordinates over `G` and a conjugation. -/
theorem toWord_ne_conj_map_conj_inl {A Y : Type*} [Group A] (S : Standard G X)
    {f : GX A Y →* GX G X} {c : A} {d : G} (hf : f (inl c) = inl d) (u : GX G X) (v : GX A Y) :
    S.toWord ≠ u * f (v⁻¹ * inl c * v) * u⁻¹ := by
  simpa [hf, mul_assoc] using S.toWord_ne_conj_inl (u * (f v)⁻¹) d

end TauCeti.GroupAlgGeom.Quadratic.Standard
