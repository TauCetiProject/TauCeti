/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Complex
public import TauCeti.KnotTheory.Khovanov.Resolution.EulerCharacteristic
public import TauCeti.KnotTheory.Khovanov.Resolution.Support
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Quantum-component Khovanov cohomology

The homology of each quantum component of the normalized complex defines
`TauCeti.OrientedPDCode.khovanovHomology`. The normalized complex has finite free terms over
every commutative ring, and its homology is finitely generated over a Noetherian ring (in
particular over the integers), hence finite-dimensional over a field. Both gradings have finite
support, uniformly in the coefficient ring, including the zero ring and the empty diagram.

`khovanovHomologyBracketIso` compares the normalized groups with bracket homology at the
translated bidegree. It uses the signed native-shift comparison, not an unsigned identification
of differentials. No Reidemeister invariance is asserted here.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
  (R : Type u) [CommRing R]

/-- **Khovanov homology** `Khⁱʲ(D; R)` of a planar oriented code `D`: the cohomology in cochain
degree `i` of the quantum component `j` of the normalized Khovanov complex. -/
abbrev khovanovHomology (i j : ℤ) : ModuleCat.{u} R :=
  (D.khovanovComplex hD R j).homology i

/-- Khovanov homology in bidegree `(i, j)` is the cohomology in degree `i` of the quantum
component `j` of the normalized Khovanov complex. -/
theorem khovanovHomology_def (i j : ℤ) :
    D.khovanovHomology hD R i j = (D.khovanovComplex hD R j).homology i :=
  (rfl)

/-- `Khⁱʲ(D; R)` is isomorphic to bracket homology in cochain degree `i + n₋` and quantum
degree `j - n₊ + 2n₋`.
The comparison retains the degreewise sign in `khovanovComplexShiftIso`. -/
def khovanovHomologyBracketIso (i j : ℤ) :
    D.khovanovHomology hD R i j ≅
      (D.toPDCode.khovanovBracket hD R
        (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).homology
          (i + D.negativeCrossingCount) :=
  (homologyFunctor _ _ i).mapIso (D.khovanovComplexShiftIso hD R j) ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R)
      D.negativeCrossingCount i (i + D.negativeCrossingCount) (by omega)).app _

/-- Every term of the normalized complex is free, without a nontriviality assumption on `R`. -/
instance (i j : ℤ) : Module.Free R ((D.khovanovComplex hD R j).X i) := by
  rw [khovanovComplex_X, ← PDCode.khovanovBracket_apply]
  infer_instance

/-- Every term of the normalized complex is finitely generated. -/
instance (i j : ℤ) : Module.Finite R ((D.khovanovComplex hD R j).X i) := by
  rw [khovanovComplex_X, ← PDCode.khovanovBracket_apply]
  infer_instance

/-- Over a Noetherian coefficient ring Khovanov cohomology is finitely generated.
This includes integral finite generation and finite-dimensionality over fields. -/
instance [IsNoetherianRing R] (i j : ℤ) :
    Module.Finite R (D.khovanovHomology hD R i j) := by
  let : Module.Finite R ((D.khovanovComplex hD R j).sc i).X₂ :=
    inferInstanceAs (Module.Finite R ((D.khovanovComplex hD R j).X i))
  exact ((D.khovanovComplex hD R j).sc i).finite_homology

/-- Khovanov cohomology vanishes outside the normalized cochain interval `[-n₋, n₊]`. -/
theorem isZero_khovanovHomology_of_cochain_notMem_Icc {i : ℤ}
    (hi : i ∉ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount) (j : ℤ) :
    IsZero (D.khovanovHomology hD R i j) :=
  (D.khovanovComplex hD R j).isZero_homology_of_notMem_Icc
    (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount (by simpa using hi)

/-- The normalized chain groups vanish outside the translated extreme-resolution quantum
interval. Circle counts include all crossing-free components. -/
theorem isZero_khovanovComplex_X_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc
      ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount -
        D.toPDCode.stateLoopCount (PDCode.cubeState ∅))
      ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount + n +
        D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ))) (i : ℤ) :
    IsZero ((D.khovanovComplex hD R j).X i) := by
  rw [khovanovComplex_X, ← PDCode.khovanovBracket_apply]
  apply D.toPDCode.isZero_khovanovBracket_X_of_quantum_notMem_Icc hD R
  intro h
  rcases h with ⟨hl, hu⟩
  exact hj ⟨by omega, by omega⟩

/-- The entire normalized quantum-component complex vanishes outside the same interval. -/
theorem isZero_khovanovComplex_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc
      ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount -
        D.toPDCode.stateLoopCount (PDCode.cubeState ∅))
      ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount + n +
        D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ))) :
    IsZero (D.khovanovComplex hD R j) := by
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  exact (D.isZero_khovanovComplex_X_of_quantum_notMem_Icc hD R hj i).eq_of_src _ _

/-- Khovanov cohomology vanishes outside the normalized quantum interval. -/
theorem isZero_khovanovHomology_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc
      ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount -
        D.toPDCode.stateLoopCount (PDCode.cubeState ∅))
      ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount + n +
        D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ))) (i : ℤ) :
    IsZero (D.khovanovHomology hD R i j) :=
  (ExactAt.of_isZero
    (D.isZero_khovanovComplex_X_of_quantum_notMem_Icc hD R hj i)).isZero_homology

/-- Only finitely many normalized quantum-component complexes are nonzero. -/
theorem finite_quantumSupport_khovanovComplex :
    {j : ℤ | ¬ IsZero (D.khovanovComplex hD R j)}.Finite :=
  (Set.finite_Icc _ _).subset fun _ hj ↦ by
    by_contra h
    exact hj (D.isZero_khovanovComplex_of_quantum_notMem_Icc hD R h)

/-- Khovanov cohomology is supported in a finite rectangle in the two gradings jointly. -/
theorem finite_bigradedSupport_khovanovHomology :
    {p : ℤ × ℤ | ¬ IsZero (D.khovanovHomology hD R p.1 p.2)}.Finite := by
  refine ((Set.finite_Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount).prod
    (Set.finite_Icc
      ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount -
        D.toPDCode.stateLoopCount (PDCode.cubeState ∅))
      ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount + n +
        D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ)))).subset ?_
  rintro ⟨i, j⟩ h
  constructor
  · by_contra hi
    exact h (D.isZero_khovanovHomology_of_cochain_notMem_Icc hD R hi j)
  · by_contra hj
    exact h (D.isZero_khovanovHomology_of_quantum_notMem_Icc hD R hj i)

end TauCeti.OrientedPDCode
