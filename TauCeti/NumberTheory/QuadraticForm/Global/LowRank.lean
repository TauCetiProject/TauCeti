/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.LowRank
import TauCeti.NumberTheory.QuadraticForm.Global.Classification
import TauCeti.NumberTheory.QuadraticForm.Global.Squares

/-!
# Local-to-global principles for quadratic forms of low rank

Over a field in which `2` is invertible, regular quadratic forms of rank at most two have purely
discriminant-governed behavior:
* in rank zero or one every regular form is anisotropic, a rank-one form represents exactly the
  units in its discriminant square class, and regular forms of the same rank at most one are
  isometric precisely when their discriminants agree;
* in rank two a regular form is isotropic precisely when its discriminant is the square class of
  `-1` (`QuadraticForm.not_anisotropic_iff_discr_eq_neg_one_of_finrank_eq_two`).

Combining these algebraic criteria with the global square theorem
(`TauCeti.isSquare_of_isSquare_unitAtFinitePlace_of_notMem`) yields the low-rank cases of the
Hasse–Minkowski theorem over a number field `K` in any universe, in a sharpened finite-place form
with no archimedean hypothesis:
* **Isotropy in dimension at most two** (O'Meara 66:1; Milne, Chapter VIII, Theorem 3.5(b) for
  `n = 2`): a regular form of dimension `≤ 2` that is isotropic at all but finitely many finite
  places is isotropic over `K`. Consequently, a regular form of dimension `≤ 2` is isotropic if and
  only if it is locally isotropic (`QuadraticForm.IsLocallyIsotropic`), and is anisotropic over `K`
  if and only if it is anisotropic at infinitely many finite places (in sharp contrast to
  `QuadraticForm.finite_setOfPred_anisotropic_atFinitePlace` in dimension `≥ 3`).
* **Scalar representation in dimension at most one** (O'Meara 66:3 in dimension `≤ 1`): a regular
  form of dimension `≤ 1` represents a scalar `a : K` whenever its localizations represent `a`
  outside finitely many finite places, and in particular if and only if it locally represents `a`
  (`QuadraticForm.LocallyRepresentsScalar`).
* **Isometry in dimension at most one** (O'Meara 66:4 in dimension `≤ 1`): a regular form of
  dimension `≤ 1` is isometric to another regular form whenever their localizations are isometric
  outside finitely many finite places, and in particular if and only if they are locally equivalent
  (`QuadraticForm.LocallyEquivalent`).

## Main results

* `QuadraticForm.not_anisotropic_of_not_anisotropic_atFinitePlace_of_notMem_of_finrank_le_two`:
  local-to-global isotropy in dimension `≤ 2` away from a finite set of finite places.
* `QuadraticForm.not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two`: Hasse–Minkowski for
  isotropy in dimension `≤ 2`.
* `QuadraticForm.infinite_setOf_anisotropic_atFinitePlace_iff_of_finrank_le_two`: a regular form of
  dimension `≤ 2` is anisotropic over `K` iff it is anisotropic at infinitely many finite places.
* `QuadraticForm.represents_of_represents_atFinitePlace_of_notMem_of_finrank_le_one`,
  `QuadraticForm.represents_iff_locallyRepresentsScalar_of_finrank_le_one`: local-to-global scalar
  representation in dimension `≤ 1`.
* `QuadraticForm.equivalent_of_equivalent_atFinitePlace_of_notMem_of_finrank_le_one`,
  `QuadraticForm.equivalent_iff_locallyEquivalent_of_finrank_le_one`: local-to-global isometry in
  dimension `≤ 1`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:1, 66:3, and 66:4.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, Theorem 3.5(b) and Proposition 3.7(b),
  pp. 236–237.
-/

public section

open IsDedekindDomain NumberField QuadraticMap TauCeti

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-! ### Isotropy in dimension at most two -/

/-- **Hasse–Minkowski for isotropy in dimension at most two, away from a finite set of finite
places.** A regular quadratic form of dimension `≤ 2` over a number field that is isotropic at all
but finitely many finite places is isotropic over `K`. No archimedean hypothesis is needed. -/
theorem not_anisotropic_of_not_anisotropic_atFinitePlace_of_notMem_of_finrank_le_two
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V ≤ 2)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬(Q.atFinitePlace v).Anisotropic) :
    ¬Q.Anisotropic := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rcases lt_or_eq_of_le hV with hlt | h2
  · obtain ⟨v, hv⟩ := S.exists_notMem
    exact absurd (anisotropic_of_finrank_le_one (Q.atFinitePlace v)
      (Nondegenerate.atFinitePlace hQ v) (by rw [Module.finrank_baseChange]; omega)) (h v hv)
  · rw [not_anisotropic_iff_discr_eq_neg_one_of_finrank_eq_two Q hQ h2]
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
3.5(b) for `n = 2`). A regular quadratic form of dimension `≤ 2` over a number field is isotropic
over `K` if and only if it is isotropic at every finite and every real place. -/
theorem not_anisotropic_iff_isLocallyIsotropic_of_finrank_le_two
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V ≤ 2) :
    ¬Q.Anisotropic ↔ Q.IsLocallyIsotropic :=
  ⟨Q.isLocallyIsotropic_of_not_anisotropic,
    fun h ↦ not_anisotropic_of_not_anisotropic_atFinitePlace_of_notMem_of_finrank_le_two Q hQ hV ∅
      fun v _ ↦ ((isLocallyIsotropic_iff Q).mp h).1 v⟩

/-- A regular quadratic form of dimension `≤ 2` over a number field is anisotropic at infinitely
many finite places if and only if it is anisotropic over `K`. -/
theorem infinite_setOf_anisotropic_atFinitePlace_iff_of_finrank_le_two
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V ≤ 2) :
    {v : HeightOneSpectrum (𝓞 K) | (Q.atFinitePlace v).Anisotropic}.Infinite ↔ Q.Anisotropic := by
  refine ⟨fun hinf ↦ by_contra fun hiso ↦ ?_, fun hani hfin ↦ ?_⟩
  · obtain ⟨v, hv⟩ := hinf.nonempty
    exact ((isLocallyIsotropic_iff Q).mp (Q.isLocallyIsotropic_of_not_anisotropic hiso)).1 v hv
  · classical
    exact not_anisotropic_of_not_anisotropic_atFinitePlace_of_notMem_of_finrank_le_two Q hQ hV
      hfin.toFinset (fun v hv hani_v ↦ hv (hfin.mem_toFinset.mpr hani_v)) hani

/-! ### Scalar representation in dimension at most one -/

/-- A regular quadratic form of dimension `≤ 1` over a number field represents a scalar `a : K`
whenever its localizations represent `a` at all but finitely many finite places. -/
theorem represents_of_represents_atFinitePlace_of_notMem_of_finrank_le_one
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V ≤ 1)
    (a : K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      Represents (Q.atFinitePlace v) (algebraMap K (v.adicCompletion K) a)) :
    Represents Q a := by
  by_cases ha : a = 0
  · exact ha ▸ Q.represents_zero
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with h0 | h1
  · obtain ⟨v, hv⟩ := S.exists_notMem
    have hx0 : ∀ x : v.FiniteScalarExtension (V := V), x = 0 :=
      (finrank_zero_iff_forall_zero (K := v.adicCompletion K)).mp
        (by rw [Module.finrank_baseChange, h0])
    obtain ⟨x, hx⟩ := (represents_iff _ _).mp (h v hv)
    rw [hx0 x, map_zero] at hx
    exact absurd ((RingHom.injective (algebraMap K (v.adicCompletion K)))
      (hx.symm.trans (map_zero _).symm)) ha
  · let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    let u : Kˣ := Units.mk0 a ha
    rw [← Units.val_mk0 ha, ← mem_unitValueSet,
      mem_unitValueSet_iff_squareClass_eq_discr_of_finrank_eq_one Q hQ h1 u]
    refine eq_of_squareClassMap_adicCompletion_eq_of_notMem S fun v hv ↦ ?_
    let _ : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    have hrep : v.unitAtFinitePlace u ∈ (Q.atFinitePlace v).unitValueSet := by
      rw [mem_unitValueSet, v.unitAtFinitePlace_apply]
      exact h v hv
    rw [← v.squareClass_unitAtFinitePlace u, ← discr_atFinitePlace Q hQ v]
    exact (mem_unitValueSet_iff_squareClass_eq_discr_of_finrank_eq_one (Q.atFinitePlace v)
      (Nondegenerate.atFinitePlace hQ v) (by rw [Module.finrank_baseChange]; exact h1)
      (v.unitAtFinitePlace u)).mp hrep

/-- **Hasse–Minkowski for scalar representation in dimension at most one.** A regular quadratic form
of dimension `≤ 1` over a number field represents a scalar `a : K` if and only if it represents `a`
at every finite and every real place. -/
theorem represents_iff_locallyRepresentsScalar_of_finrank_le_one
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V ≤ 1) (a : K) :
    Represents Q a ↔ Q.LocallyRepresentsScalar a :=
  ⟨LocallyRepresentsScalar.of_represents,
    fun h ↦ represents_of_represents_atFinitePlace_of_notMem_of_finrank_le_one Q hQ hV a ∅
      fun v _ ↦ ((locallyRepresentsScalar_iff Q a).mp h).1 v⟩

/-! ### Isometry in dimension at most one -/

/-- Two regular quadratic forms over a number field, the first of dimension `≤ 1`, whose
localizations are isometric at all but finitely many finite places are globally isometric. -/
theorem equivalent_of_equivalent_atFinitePlace_of_notMem_of_finrank_le_one
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (R : _root_.QuadraticForm K W) (hR : R.Nondegenerate)
    (hV : Module.finrank K V ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (Q.atFinitePlace v).Equivalent (R.atFinitePlace v)) :
    Q.Equivalent R := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨v₀, hv₀⟩ := S.exists_notMem
  have hdim : Module.finrank K V = Module.finrank K W :=
    ((equivalent_atFinitePlace_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq Q hQ R hR v₀).mp
      (h v₀ hv₀)).1
  refine (equivalent_iff_discr_eq_and_hasseInvariant_eq Q hQ hR hdim (by omega)).mpr
    ⟨discr_eq_of_equivalent_atFinitePlace_of_notMem hQ hR S h, ?_⟩
  rw [RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simpa using hV),
    RegularFormClass.hasseInvariant_eq_one_of_rank_le_one (by simpa [← hdim] using hV)]

/-- **Hasse–Minkowski for isometry in dimension at most one.** Two regular quadratic forms over a
number field, the first of dimension `≤ 1`, are isometric if and only if they are isometric at
every finite and every real place. -/
theorem equivalent_iff_locallyEquivalent_of_finrank_le_one
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (R : _root_.QuadraticForm K W) (hR : R.Nondegenerate)
    (hV : Module.finrank K V ≤ 1) :
    Q.Equivalent R ↔ Q.LocallyEquivalent R :=
  ⟨LocallyEquivalent.of_equivalent,
    fun h ↦ equivalent_of_equivalent_atFinitePlace_of_notMem_of_finrank_le_one Q hQ R hR hV ∅
      fun v _ ↦ ((locallyEquivalent_iff Q R).mp h).1 v⟩

end QuadraticForm
