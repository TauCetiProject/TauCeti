/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.KnotTheory.Khovanov.Complex
public import TauCeti.KnotTheory.Khovanov.Resolution.EulerCharacteristic
public import TauCeti.KnotTheory.Khovanov.Resolution.Support

/-!
# Finiteness and support of normalized Khovanov cohomology

The normalized complex of a planar oriented PD-code has finite free terms. Over a Noetherian
commutative ring its cohomology is finitely generated; in particular this gives finite generation
over `ℤ` and finite-dimensionality over a field. No Noetherian hypothesis is needed for the
support bounds.

Write `kA` and `kB` for the circle counts of the all-A and all-B resolutions. The terms and
cohomology vanish outside the rectangle with cochain interval `[-n₋, n₊]` and quantum interval
`[-kA + n₊ - 2n₋, n + kB + n₊ - 2n₋]`. These are the bracket bounds translated by the actual
normalization shifts. Thus only finitely many bidegrees can contribute to cohomology, including
for the empty diagram and over rings with torsion. The assertions use the native homology
objects of the quantum component complexes, without choosing bases or homology presentations.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.2.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
  (R : Type u) [CommRing R]

/-- Every normalized cochain term is free over the coefficient ring. -/
instance khovanovComplex_moduleFree_X (j i : ℤ) :
    Module.Free R ((D.khovanovComplex hD R j).X i) := by
  rw [khovanovComplex_X]
  infer_instance

/-- Every normalized cochain term is finitely generated over the coefficient ring. -/
instance khovanovComplex_moduleFinite_X (j i : ℤ) :
    Module.Finite R ((D.khovanovComplex hD R j).X i) := by
  rw [khovanovComplex_X]
  infer_instance

/-- Normalized cohomology is finitely generated over a Noetherian coefficient ring. This
specializes to integral finite generation and finite-dimensionality over every field. -/
instance khovanovComplex_moduleFinite_homology [IsNoetherianRing R] (j i : ℤ) :
    Module.Finite R ((D.khovanovComplex hD R j).homology i) := by
  -- The middle term of the native short complex is the cochain term in degree `i`.
  have : IsNoetherian R ((D.khovanovComplex hD R j).sc i).X₂ :=
    inferInstanceAs (IsNoetherian R ((D.khovanovComplex hD R j).X i))
  exact ((D.khovanovComplex hD R j).sc i).finite_homology

/-- No normalized cochain term occurs outside `[-n₋, n₊]`. -/
theorem isZero_khovanovComplex_X_of_cochain_notMem_Icc (j : ℤ) {i : ℤ}
    (hi : i ∉ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount) :
    IsZero ((D.khovanovComplex hD R j).X i) :=
  (D.khovanovComplex hD R j).isZero_X_of_notMem_Icc _ _ hi

/-- Normalized cohomology vanishes outside `[-n₋, n₊]`, over any coefficient ring. -/
theorem isZero_homology_khovanovComplex_of_cochain_notMem_Icc (j : ℤ) {i : ℤ}
    (hi : i ∉ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount) :
    IsZero ((D.khovanovComplex hD R j).homology i) :=
  (D.khovanovComplex hD R j).isZero_homology_of_notMem_Icc _ _ hi

/-- Every normalized term vanishes outside the translated extreme-resolution quantum interval.
The bound is independent of the cochain degree and the coefficient ring. -/
theorem isZero_khovanovComplex_X_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc
      (-(D.toPDCode.stateLoopCount (PDCode.cubeState ∅) : ℤ) +
        D.positiveCrossingCount - 2 * D.negativeCrossingCount)
      ((n : ℤ) + D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ) +
        D.positiveCrossingCount - 2 * D.negativeCrossingCount)) (i : ℤ) :
    IsZero ((D.khovanovComplex hD R j).X i) := by
  rw [khovanovComplex_X, ← PDCode.khovanovBracket_apply]
  apply D.toPDCode.isZero_khovanovBracket_X_of_quantum_notMem_Icc hD R
  simp only [Set.mem_Icc] at hj ⊢
  omega

/-- A whole quantum component complex vanishes outside the normalized quantum interval. -/
theorem isZero_khovanovComplex_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc
      (-(D.toPDCode.stateLoopCount (PDCode.cubeState ∅) : ℤ) +
        D.positiveCrossingCount - 2 * D.negativeCrossingCount)
      ((n : ℤ) + D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ) +
        D.positiveCrossingCount - 2 * D.negativeCrossingCount)) :
    IsZero (D.khovanovComplex hD R j) := by
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  exact (D.isZero_khovanovComplex_X_of_quantum_notMem_Icc hD R hj i).eq_of_src _ _

/-- Normalized cohomology vanishes outside the same quantum interval as the cochain terms. -/
theorem isZero_homology_khovanovComplex_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc
      (-(D.toPDCode.stateLoopCount (PDCode.cubeState ∅) : ℤ) +
        D.positiveCrossingCount - 2 * D.negativeCrossingCount)
      ((n : ℤ) + D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ) +
        D.positiveCrossingCount - 2 * D.negativeCrossingCount)) (i : ℤ) :
    IsZero ((D.khovanovComplex hD R j).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (D.isZero_khovanovComplex_X_of_quantum_notMem_Icc hD R hj i)).isZero_homology

/-- Only finitely many quantum-component complexes of the normalized complex are nonzero. -/
theorem finite_quantumSupport_khovanovComplex :
    {j : ℤ | ¬ IsZero (D.khovanovComplex hD R j)}.Finite :=
  (Set.finite_Icc _ _).subset fun _ hj ↦ by
    by_contra h
    exact hj (D.isZero_khovanovComplex_of_quantum_notMem_Icc hD R h)

/-- The normalized cochain terms have finite support jointly in cochain and quantum degree. -/
theorem finite_bigradedSupport_khovanovComplex :
    {p : ℤ × ℤ | ¬ IsZero ((D.khovanovComplex hD R p.2).X p.1)}.Finite := by
  refine ((Set.finite_Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount).prod
    (Set.finite_Icc
      (-(D.toPDCode.stateLoopCount (PDCode.cubeState ∅) : ℤ) +
        D.positiveCrossingCount - 2 * D.negativeCrossingCount)
      ((n : ℤ) + D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ) +
        D.positiveCrossingCount - 2 * D.negativeCrossingCount))).subset ?_
  rintro ⟨i, j⟩ h
  constructor
  · by_contra hi
    exact h (D.isZero_khovanovComplex_X_of_cochain_notMem_Icc hD R j (by simpa using hi))
  · by_contra hj
    exact h (D.isZero_khovanovComplex_X_of_quantum_notMem_Icc hD R hj i)

/-- Only finitely many bigraded cohomology groups are nonzero, over any coefficient ring. -/
theorem finite_bigradedSupport_homology_khovanovComplex :
    {p : ℤ × ℤ | ¬ IsZero ((D.khovanovComplex hD R p.2).homology p.1)}.Finite :=
  (D.finite_bigradedSupport_khovanovComplex hD R).subset fun _ hp hX ↦
    hp (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology

end TauCeti.OrientedPDCode
