/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Representation
public import TauCeti.NumberTheory.QuadraticForm.Global.Predicates
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.RingTheory.DedekindDomain.SelmerGroup
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Henselian.BinaryForm

/-!
# Quadratic forms of rank at least three are isotropic at almost every finite place

Let `Q` be a quadratic form over a number field `K` on a space of dimension at least three. This
file proves that `Q` is isotropic at all but finitely many finite places of `K`.

Isotropic global forms are isotropic at every place, so only anisotropic, hence regular, forms need
an argument. Such a form has a diagonalization `⟨a₁, …, aₙ⟩` with nonzero coefficients. At every
finite place `v` not above `2` at which every `aᵢ` is a `v`-adic unit, the binary form `⟨a₁, a₂⟩`
represents the unit `-a₃` over the ring of integers of the completion `K_v`, a Henselian local ring
with finite residue field of odd characteristic; this gives an isotropic vector of `Q` over `K_v`.
The remaining places are those dividing `2` or one of the finitely many nonzero coefficients.

The rank bound is necessary: the binary form `⟨1, 1⟩` over `ℚ` is anisotropic at every prime
congruent to `3` modulo `4`. The finiteness of the anisotropic places of a form of rank at least
three is what allows the weak-approximation step of the Hasse–Minkowski theorem in rank at least
five, where it is applied to the complement of a binary summand.

## Main results

* `QuadraticForm.not_anisotropic_atFinitePlace_weightedSumSquares`: a diagonal form is isotropic
  at every finite place at which `2` and three of its coefficients are units.
* `QuadraticForm.finite_setOfPred_anisotropic_atFinitePlace`: a quadratic form on a space of
  dimension at least three is anisotropic at only finitely many finite places.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 66:1, the finiteness of the
  exceptional set in the case of dimension at least five.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §3.2, the proof of the Hasse–Minkowski
  theorem in dimension at least five.
-/

public section

open IsDedekindDomain NumberField QuadraticMap

namespace QuadraticForm

variable {K : Type*} [Field K] [NumberField K]

/-- **Isotropy at a good place.** A diagonal form over a number field is isotropic at every finite
place `v` at which `2` and three of its coefficients have valuation one. -/
theorem not_anisotropic_atFinitePlace_weightedSumSquares {ι : Type*} [Fintype ι] (a : ι → K)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (v : HeightOneSpectrum (𝓞 K))
    (h2 : v.valuation K 2 = 1) (hi : v.valuation K (a i) = 1) (hj : v.valuation K (a j) = 1)
    (hk : v.valuation K (a k) = 1) :
    ¬ (atFinitePlace (weightedSumSquares K a) v).Anisotropic := by
  classical
  rw [Equivalent.anisotropic_iff ⟨atFinitePlaceWeightedSumSquares v a⟩]
  -- The ring of integers of `K_v` is Henselian with finite residue field, and `2` is a unit there.
  have : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  -- An element of `K` of valuation one is a unit of the ring of integers of `K_v`.
  have hunit {c : K} (hc : v.valuation K c = 1) : ∃ u : v.adicCompletionIntegers K, IsUnit u ∧
      (u : v.adicCompletion K) = algebraMap K (v.adicCompletion K) c := by
    have hv : Valued.v (algebraMap K (v.adicCompletion K) c) = 1 := by
      rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using hc
    exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ K v).mpr hv.le⟩,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hv, rfl⟩
  obtain ⟨t, ht, ht2⟩ := hunit h2
  have ht2' : t = 2 := Subtype.ext (by rw [ht2, map_ofNat]; norm_cast)
  obtain ⟨uᵢ, huᵢ, huᵢa⟩ := hunit hi
  obtain ⟨uⱼ, huⱼ, huⱼa⟩ := hunit hj
  obtain ⟨uₖ, huₖ, huₖa⟩ := hunit hk
  -- The binary form `⟨aᵢ, aⱼ⟩` represents `-aₖ` over the integers of `K_v`.
  obtain ⟨x, y, hxy⟩ := TauCeti.exists_mul_sq_add_mul_sq_eq_of_isUnit (ht2' ▸ ht) huᵢ huⱼ huₖ.neg
  have hxy' := congrArg (fun z : v.adicCompletionIntegers K ↦ (z : v.adicCompletion K)) hxy
  push_cast at hxy'
  rw [huᵢa, huⱼa, huₖa] at hxy'
  -- So `x eᵢ + y eⱼ + eₖ` is a nonzero isotropic vector.
  let f : ι → v.adicCompletion K := Pi.single i (x : v.adicCompletion K) + Pi.single j ↑y +
    Pi.single k 1
  intro hanis
  have hf : f = 0 := hanis f <| by
    rw [weightedSumSquares_apply, ← Finset.sum_subset (Finset.subset_univ {i, j, k})]
    · rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
        Finset.sum_singleton]
      simp only [f, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm,
        Pi.single_eq_of_ne hik.symm, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hjk.symm,
        Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hjk, smul_eq_mul]
      linear_combination hxy'
    · intro l _ hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      simp [f, hl.1, hl.2.1, hl.2.2]
  have hfk := congrFun hf k
  simp [f, hik.symm, hjk.symm] at hfk

/-- **Almost-all isotropy.** A quadratic form over a number field on a space of dimension at
least three is isotropic at all but finitely many finite places. -/
theorem finite_setOfPred_anisotropic_atFinitePlace {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (hV : 3 ≤ Module.finrank K V) :
    {v : HeightOneSpectrum (𝓞 K) | (Q.atFinitePlace v).Anisotropic}.Finite := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  -- A globally isotropic form is isotropic at every place.
  by_cases hQ : Q.Anisotropic
  swap
  · refine Set.finite_empty.subset fun v hv ↦ ?_
    exact ((isLocallyIsotropic_iff Q).mp (Q.isLocallyIsotropic_of_not_anisotropic hQ)).1 v hv
  -- An anisotropic form is regular, so it has a diagonalization by units.
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (separatingLeft_of_anisotropic Q hQ)
  rw [weightedSumSquares_units] at hw
  refine ((HeightOneSpectrum.finite_setOfPred_valuation_ne_one (two_ne_zero' K)).union
    (Set.finite_iUnion fun i ↦
      HeightOneSpectrum.finite_setOfPred_valuation_ne_one (w i).ne_zero)).subset fun v hv ↦ ?_
  by_contra hbad
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists,
    not_not] at hbad
  -- The first three coefficients are `v`-adic units.
  let i₀ : Fin (Module.finrank K V) := ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank K V) := ⟨1, by omega⟩
  let i₂ : Fin (Module.finrank K V) := ⟨2, by omega⟩
  exact not_anisotropic_atFinitePlace_weightedSumSquares _ (i := i₀) (j := i₁) (k := i₂)
    (by simp [i₀, i₁, Fin.ext_iff]) (by simp [i₀, i₂, Fin.ext_iff])
    (by simp [i₁, i₂, Fin.ext_iff]) v hbad.1 (hbad.2 _) (hbad.2 _) (hbad.2 _)
    ((hw.atFinitePlace v).anisotropic_iff.mp hv)

end QuadraticForm
