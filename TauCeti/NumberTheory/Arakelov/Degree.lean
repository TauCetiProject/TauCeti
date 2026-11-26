/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Arakelov.HermitianVectorBundle
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The Arakelov degree of a hermitian line bundle does not depend on the section

Let `K` be a number field and `L` a hermitian line bundle over `Spec 𝓞 K`, that is a hermitian
vector bundle of rank one. For a nonzero section `s` of `L`, the expression
`log #(L / 𝓞 K • s) - Σ_σ log ‖s‖_σ` (`HermitianVectorBundle.sectionDegree`) does not depend on
`s`, so it is an invariant of the hermitian line bundle: its Arakelov degree.

Two nonzero sections of a line bundle are commensurable, `a • t = b • s` for nonzero integers
`a, b` of `K` (`Module.exists_smul_eq_smul_of_finrank_eq_one`). Replacing `s` by `a • s`
multiplies the index `#(L / 𝓞 K • s)`, which is finite
(`Module.finite_quotient_span_singleton_of_finrank_eq_one`), by the absolute norm
`#(𝓞 K / (a)) = |N(a)|`, and multiplies each `‖s‖_σ` by `|σ(a)|`; since `∏_σ |σ(a)| = |N(a)|`,
the two changes cancel. This is the product formula for the element `a`.

The expression is also invariant under isometries, so the degree descends to isometry classes of
hermitian line bundles.

## Main results

* `TauCeti.HermitianVectorBundle.sectionDegree_smul`: in a bundle of rank one, the degree computed
  with `a • s` equals the one computed with `s`, for `a ≠ 0`.
* `TauCeti.HermitianVectorBundle.sectionDegree_eq_sectionDegree`: in a bundle of rank one, any two
  nonzero sections compute the same degree.
* `TauCeti.HermitianVectorBundle.Isometry.sectionDegree_apply`: isometries preserve the degree
  computed with corresponding sections.
* `TauCeti.HermitianVectorBundle.sectionDegree_trivial`: every nonzero section computes the degree
  `0` of the trivial bundle `Ō_K`.

## References

* P. Deligne, *Preuve des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616
  (1983/84), §1.1, p. 25.
* G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73
  (1983), §3, p. 354.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.2, Proposition 1.1 and
  Corollaire, pp. 13–14.
-/

public section

open NumberField Module Submodule

namespace TauCeti.HermitianVectorBundle

variable {K : Type*} [Field K] [NumberField K] (E : HermitianVectorBundle K)

/-- **Independence of the multiple.** In a hermitian vector bundle of rank one, the degree computed
with `a • s` equals the one computed with `s`, for every nonzero integer `a` of `K`: the index of
the multiples of `s` grows by `|N(a)|` and the norms of `s` by `|σ(a)|`, and
`∏_σ |σ(a)| = |N(a)|`. -/
theorem sectionDegree_smul (hE : E.rank = 1) {a : 𝓞 K} (ha : a ≠ 0) (s : E) :
    E.sectionDegree (a • s) = E.sectionDegree s := by
  obtain rfl | hs := eq_or_ne s 0
  · rw [smul_zero]
  rw [sectionDegree_eq_sectionDegreeOfNorms, sectionDegree_eq_sectionDegreeOfNorms]
  exact sectionDegreeOfNorms_smul (E.rank_def ▸ hE) E.norm_smul hs
    (fun σ ↦ (E.norm_pos σ hs).ne') ha

/-- **Independence of the section.** In a hermitian vector bundle of rank one, any two nonzero
sections compute the same degree `log #(L / 𝓞 K • s) - Σ_σ log ‖s‖_σ`. This is the
product formula, and it makes this expression an invariant of the line bundle: its Arakelov
degree. -/
theorem sectionDegree_eq_sectionDegree (hE : E.rank = 1) {s t : E} (hs : s ≠ 0) (ht : t ≠ 0) :
    E.sectionDegree s = E.sectionDegree t := by
  rw [sectionDegree_eq_sectionDegreeOfNorms, sectionDegree_eq_sectionDegreeOfNorms]
  exact sectionDegreeOfNorms_eq_of_finrank_eq_one (E.rank_def ▸ hE) E.norm_smul
    (fun σ _ hx ↦ (E.norm_pos σ hx).ne') hs ht

variable {E} {F : HermitianVectorBundle K}

/-- An isometry preserves the degree computed with corresponding sections: both the index of the
multiples of a section and its norms are preserved. -/
@[simp]
theorem Isometry.sectionDegree_apply (f : Isometry E F) (s : E) :
    F.sectionDegree (f.toLinearEquiv s) = E.sectionDegree s := by
  have hq : (span (𝓞 K) {f.toLinearEquiv s}).cardQuot = (span (𝓞 K) {s}).cardQuot := by
    rw [cardQuot_apply, cardQuot_apply]
    exact Nat.card_congr (Quotient.equiv _ _ f.toLinearEquiv (by simp [map_span])).toEquiv.symm
  simp only [sectionDegree_def, hq, Isometry.norm_apply]

/-- Every nonzero section computes the degree `0` of the trivial bundle `Ō_K`. -/
theorem sectionDegree_trivial {s : 𝓞 K} (hs : s ≠ 0) : (trivial K).sectionDegree s = 0 := by
  rw [sectionDegree_eq_sectionDegree _ rank_trivial hs one_ne_zero, sectionDegree_trivial_one]

end TauCeti.HermitianVectorBundle
