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
(`TauCeti.GroupAlgGeom.Quadratic.Standard.not_isConj_inl`,
`TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_inl`). Consequently a conjugate
`w` of `a` in any group `A` is not carried to a standard quadratic word by any homomorphism sending
`a` to a coefficient `inl d` followed by a conjugation
(`Standard.toWord_ne_conj_map_of_isConj_of_map_eq_inl`).
For `z⁻¹ c z` with `c ≠ 1` this shows that the coefficient alternative cannot be avoided.

The separation follows from cyclic reduction relative to `G`: a standard quadratic word has a
cyclically reduced normal form (`Standard.isCyclicallyReduced_reducedWord`) in which every variable
from its nonempty variable set `S.vars` occurs twice (`Standard.vars_nonempty`,
`Standard.occurrences_toWord_of_mem_vars`), whereas any cyclically reduced word conjugate to a
coefficient has no variable letters (`GX.IsCyclicallyReduced.countVar_eq_zero_of_eq_conj_inl`).

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.not_isConj_inl`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_inl`: a standard quadratic word is not
  conjugate to a coefficient.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_ne_conj_map_of_isConj_of_map_eq_inl`: a
  homomorphism sending an element `a` to a coefficient and a conjugation do not carry a conjugate
  of `a` to a standard quadratic word.

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
theorem not_isConj_inl (S : Standard G X) (g : G) : ¬IsConj (inl g : GX G X) S.toWord := by
  intro h
  obtain ⟨u, hu⟩ := isConj_iff.1 h
  obtain ⟨x, hx⟩ := S.vars_nonempty
  have hc := S.isCyclicallyReduced_reducedWord.countVar_eq_zero_of_eq_conj_inl
    (by simpa [GX.prod_reducedWord] using hu.symm) x
  have ho := S.occurrences_toWord_of_mem_vars hx
  rw [GX.occurrences_eq_countVar_reducedWord, hc] at ho
  exact absurd ho (by decide)

/-- A standard quadratic word is not equal to any conjugate `u * inl g * u⁻¹` of a coefficient. -/
theorem toWord_ne_conj_inl (S : Standard G X) (u : GX G X) (g : G) :
    S.toWord ≠ u * inl g * u⁻¹ :=
  fun h => S.not_isConj_inl g (isConj_iff.2 ⟨u, h.symm⟩)

/-- A homomorphism `A →* G[X]` sending `a : A` to a coefficient `inl d`, followed by a
conjugation in `G[X]`, does not carry any conjugate `w` of `a` to a standard quadratic word.
For instance the strictly quadratic word `z⁻¹ c z` is not brought to a standard quadratic word by
a change of coordinates over `G` and a conjugation. -/
theorem toWord_ne_conj_map_of_isConj_of_map_eq_inl {A F : Type*} [Group A] [FunLike F A (GX G X)]
    [MonoidHomClass F A (GX G X)] (S : Standard G X) {f : F} {a w : A} {d : G}
    (hw : IsConj a w) (hf : f a = inl d) (u : GX G X) :
    S.toWord ≠ u * f w * u⁻¹ := by
  intro h
  have hfw : IsConj (f a) (f w) := by simpa using (MonoidHom.ofClass f).map_isConj hw
  rw [hf] at hfw
  exact S.not_isConj_inl d (hfw.trans (isConj_iff.2 ⟨u, h.symm⟩))

end TauCeti.GroupAlgGeom.Quadratic.Standard
