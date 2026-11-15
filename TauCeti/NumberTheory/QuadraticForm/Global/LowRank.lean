/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.LowRank
import TauCeti.NumberTheory.QuadraticForm.Global.Discriminant
import TauCeti.NumberTheory.QuadraticForm.Global.Squares

/-!
# Local-to-global isotropy for quadratic forms of dimension at most two

Over a field in which `2` is invertible, an anisotropic quadratic form is automatically regular
(`QuadraticMap.Anisotropic.nondegenerate`), and regular quadratic forms of rank at most two have
purely discriminant-governed isotropy:
* in rank zero or one every regular form is anisotropic
  (`QuadraticForm.anisotropic_of_finrank_le_one`);
* in rank two a regular form is isotropic precisely when its discriminant is the square class of
  `-1` (`QuadraticForm.not_anisotropic_iff_discr_eq_neg_one_of_finrank_eq_two`).

Combining these algebraic criteria with the global square theorem
(`Units.isSquare_of_isSquare_unitAtFinitePlace_of_notMem`) yields the low-rank case of the
Hasse–Minkowski isotropy theorem over a number field `K` in any universe, in a sharpened
finite-place form with no archimedean or nondegeneracy hypothesis (O'Meara 66:1; Milne,
Chapter VIII, Theorem 3.5(b) for `n = 2`): a quadratic form of dimension `≤ 2` that is isotropic
at all but finitely many finite places is isotropic over `K`. Consequently, a quadratic form of
dimension `≤ 2` is isotropic if and only if it is locally isotropic
(`QuadraticForm.IsLocallyIsotropic`), and is anisotropic over `K` if and only if it is anisotropic
at infinitely many finite places (in sharp contrast to
`QuadraticForm.finite_setOfPred_anisotropic_atFinitePlace` in dimension `≥ 3`).

## Main results

* `QuadraticForm.not_anisotropic_of_not_anisotropic_atFinitePlace_of_notMem_of_finrank_le_two`:
  local-to-global isotropy in dimension `≤ 2` away from a finite set of finite places.
* `QuadraticForm.not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two`: Hasse–Minkowski for
  isotropy in dimension `≤ 2`.
* `QuadraticForm.infinite_setOf_anisotropic_atFinitePlace_iff_of_finrank_le_two`: a quadratic form
  of dimension `≤ 2` is anisotropic over `K` iff it is anisotropic at infinitely many finite places.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:1.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, Theorem 3.5(b) and Proposition 3.7(b),
  pp. 236–237.
-/

public section

open IsDedekindDomain NumberField QuadraticMap TauCeti

universe u v

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Hasse–Minkowski for isotropy in dimension at most two, away from a finite set of finite
places.** A quadratic form of dimension `≤ 2` over a number field that is isotropic at all but
finitely many finite places is isotropic over `K`. Neither nondegeneracy nor an archimedean
hypothesis is needed. -/
theorem not_anisotropic_of_not_anisotropic_atFinitePlace_of_notMem_of_finrank_le_two
    (Q : _root_.QuadraticForm K V) (hV : Module.finrank K V ≤ 2)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬(Q.atFinitePlace v).Anisotropic) :
    ¬Q.Anisotropic := by
  intro hA
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hQ : Q.Nondegenerate := hA.nondegenerate
  rcases lt_or_eq_of_le hV with hlt | h2
  · obtain ⟨v, hv⟩ := S.exists_notMem
    exact h v hv (anisotropic_of_finrank_le_one (Q.atFinitePlace v)
      (Nondegenerate.atFinitePlace hQ v) (by rw [Module.finrank_baseChange]; omega))
  · refine ((not_anisotropic_iff_discr_eq_neg_one_of_finrank_eq_two Q hQ h2).mpr ?_) hA
    refine eq_of_squareClassMap_adicCompletion_eq_of_notMem S fun v hv ↦ ?_
    let _ : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    have hiso : RegularFormClass.discr
        (formClass (Q.atFinitePlace v) (Nondegenerate.atFinitePlace hQ v)) =
        squareClass (-1 : (v.adicCompletion K)ˣ) :=
      (not_anisotropic_iff_discr_eq_neg_one_of_finrank_eq_two (Q.atFinitePlace v)
        (Nondegenerate.atFinitePlace hQ v) (by rw [Module.finrank_baseChange]; exact h2)).mp
        (h v hv)
    rw [← discr_atFinitePlace Q hQ v, hiso, ← v.squareClass_unitAtFinitePlace (-1 : Kˣ)]
    exact congrArg squareClass (Units.ext (by simp))

/-- **Hasse–Minkowski for isotropy in dimension at most two** (O'Meara 66:1; Milne, VIII, Theorem
3.5(b) for `n = 2`). A quadratic form of dimension `≤ 2` over a number field is isotropic over `K`
if and only if it is isotropic at every finite and every real place. -/
theorem not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two
    (Q : _root_.QuadraticForm K V) (hV : Module.finrank K V ≤ 2) :
    ¬Q.Anisotropic ↔ Q.IsLocallyIsotropic :=
  ⟨Q.isLocallyIsotropic_of_not_anisotropic,
    fun h ↦ not_anisotropic_of_not_anisotropic_atFinitePlace_of_notMem_of_finrank_le_two Q hV ∅
      fun v _ ↦ ((isLocallyIsotropic_iff Q).mp h).1 v⟩

/-- A quadratic form of dimension `≤ 2` over a number field is anisotropic at infinitely many finite
places if and only if it is anisotropic over `K`. -/
theorem infinite_setOf_anisotropic_atFinitePlace_iff_of_finrank_le_two
    (Q : _root_.QuadraticForm K V) (hV : Module.finrank K V ≤ 2) :
    {v : HeightOneSpectrum (𝓞 K) | (Q.atFinitePlace v).Anisotropic}.Infinite ↔ Q.Anisotropic := by
  refine ⟨fun hinf ↦ by_contra fun hiso ↦ ?_, fun hani hfin ↦ ?_⟩
  · obtain ⟨v, hv⟩ := hinf.nonempty
    exact ((isLocallyIsotropic_iff Q).mp (Q.isLocallyIsotropic_of_not_anisotropic hiso)).1 v hv
  · classical
    exact not_anisotropic_of_not_anisotropic_atFinitePlace_of_notMem_of_finrank_le_two Q hV
      hfin.toFinset (fun v hv hani_v ↦ hv (hfin.mem_toFinset.mpr hani_v)) hani

end QuadraticForm
