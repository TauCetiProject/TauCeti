/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Rational.Basic

/-!
# Standard rational covers of classical affinoid spectra

For a finite tuple `g`, the standard rational domains `R(g/gᵢ)` cover precisely the points
where at least one `gᵢ` is nonzero. Consequently they cover an affinoid spectrum if and only
if the entries of `g` generate the unit ideal. This gives finite covers by the rational
fraction algebras, not merely inequalities between point norms.

The empty tuple is allowed: its domains cover exactly when the algebra is the zero ring.
For arbitrary rational domains, generating the unit ideal by the denominators alone is not
a covering criterion. A scalar of norm greater than one gives an empty rational domain with
denominator one, even over the coefficient field.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§7.2.3 and 8.2.
-/

public section

namespace TauCeti

variable {K : Type*} [NontriviallyNormedField K]
    {A : Type*} [CommRing A] [Algebra K A] {n : ℕ}

/-- A point belongs to a standard rational domain for `g` exactly when some entry of `g`
has nonzero value there. This includes the empty tuple. -/
@[simp↓]
theorem mem_iUnion_rationalDomain_self (g : Fin n → A) (x : MaximalSpectrum A) :
    x ∈ ⋃ i, rationalDomain K (g i) g ↔ ∃ i, pointNorm K x (g i) ≠ 0 := by
  classical
  simp only [Set.mem_iUnion, mem_rationalDomain]
  constructor
  · rintro ⟨i, hi, -⟩
    exact ⟨i, hi⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, -, hi⟩ := Finset.univ.exists_max_image (fun i ↦ pointNorm K x (g i))
      ⟨j, Finset.mem_univ j⟩
    refine ⟨i, ?_, fun k ↦ hi k (Finset.mem_univ k)⟩
    exact ne_of_gt ((lt_of_le_of_ne (pointNorm_nonneg _) (Ne.symm hj)).trans_le
      (hi j (Finset.mem_univ j)))

namespace IsAffinoidAlgebra

variable [IsUltrametricDist K] [CompleteSpace K]

/-- **Standard rational-cover criterion.** The domains `R(g/gᵢ)` cover the classical spectrum
of an affinoid algebra exactly when the entries of `g` generate the unit ideal. No
nontriviality assumption on the algebra or nonemptiness assumption on the tuple is needed. -/
theorem iUnion_rationalDomain_self_eq_univ_iff (hA : IsAffinoidAlgebra K A) (g : Fin n → A) :
    (⋃ i, rationalDomain K (g i) g) = Set.univ ↔ Ideal.span (Set.range g) = ⊤ := by
  rw [Set.eq_univ_iff_forall]
  simp only [mem_iUnion_rationalDomain_self, ne_eq, hA.pointNorm_eq_zero_iff]
  constructor
  · intro h
    by_contra hg
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hg
    obtain ⟨i, hi⟩ := h ⟨M, hM⟩
    exact hi (hle (Ideal.subset_span (Set.mem_range_self i)))
  · intro hg x
    by_contra hx
    push Not at hx
    have hle : Ideal.span (Set.range g) ≤ x.asIdeal := Ideal.span_le.mpr <| by
      rintro _ ⟨i, rfl⟩
      exact hx i
    exact x.isMaximal.ne_top (top_unique (hg ▸ hle))

end IsAffinoidAlgebra

namespace RationalFraction

variable [IsUltrametricDist K] [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- The spectra of the standard rational fraction algebras are jointly surjective onto the
classical spectrum when the tuple generates the unit ideal. -/
theorem exists_maximalSpectrumComap_eq (hA : IsAffinoidAlgebra K A) (g : Fin n → A)
    (hg : Ideal.span (Set.range g) = ⊤) (x : MaximalSpectrum A) :
    ∃ i, ∃ y : MaximalSpectrum (RationalFraction (g i) g),
      (isAffinoidAlgebra hA (g i) g).maximalSpectrumComap (IsScalarTower.toAlgHom K A _) y = x := by
  have hx : x ∈ ⋃ i, rationalDomain K (g i) g := by
    rw [(hA.iUnion_rationalDomain_self_eq_univ_iff g).mpr hg]
    exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hgi : Ideal.span (insert (g i) (Set.range g)) = ⊤ := by
    simpa only [Set.insert_eq_of_mem (Set.mem_range_self i)] using hg
  rw [← (isAffinoidSubdomainMap hA hgi).range_maximalSpectrumComap hA] at hi
  exact ⟨i, hi⟩

end RationalFraction

/-- A scalar larger than one defines an empty rational domain with denominator one.
Thus a unit denominator does not by itself ensure that rational domains cover. -/
theorem rationalDomain_one_algebraMap_eq_empty {c : K} (hc : 1 < ‖c‖) :
    rationalDomain K (1 : A) (fun _ : Fin 1 ↦ algebraMap K A c) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := (mem_rationalDomain.mp hx).2 0
  simp only [pointNorm_algebraMap, pointNorm_one] at h
  exact hc.not_ge h

end TauCeti
