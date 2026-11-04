/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Resolution.Cube
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Data.Int.Interval

/-!
# Quantum support of the Khovanov bracket

The bracket has finite support in both cochain and quantum degree. If `kA` and `kB` are the
numbers of circles in the all-A and all-B resolutions of an `n`-crossing diagram, every quantum
degree of the bracket lies in `[-kA, n + kB]`. This includes the crossing-free components and
the empty diagram. The bound is uniform in the cochain degree and in the coefficient ring,
so the family of quantum components can be totalized using only finitely many nonzero pieces.
The same bound holds for its homology.

Over a nontrivial coefficient ring, a term is nonzero exactly when there is an enhanced state
of its bidegree. This describes chain groups, rather than asserting that every such state
survives in homology.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Finset

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n)

/-- A resolution has at most one additional circle per B-smoothing relative to the all-A
resolution. This also holds for nonplanar codes. -/
theorem stateLoopCount_cubeState_le_allA (S : Finset (Fin n)) :
    D.stateLoopCount (cubeState S) ≤ D.stateLoopCount (cubeState ∅) + #S := by
  simpa [cubeState_apply] using
    D.stateLoopCount_le_add_card_filter_ne (cubeState ∅) (cubeState S)

/-- A resolution has at most one additional circle per A-smoothing relative to the all-B
resolution. This also holds for nonplanar codes. -/
theorem stateLoopCount_cubeState_le_allB (S : Finset (Fin n)) :
    D.stateLoopCount (cubeState S) ≤ D.stateLoopCount (cubeState univ) + (n - #S) := by
  have hfilter : ({i | cubeState univ i ≠ cubeState S i} : Finset (Fin n)) = Sᶜ := by
    ext i
    simp [cubeState_apply]
  have h := D.stateLoopCount_le_add_card_filter_ne (cubeState univ) (cubeState S)
  rw [hfilter, card_compl, Fintype.card_fin] at h
  exact h

variable (hD : D.IsPlanar) (R : Type u) [CommRing R]

/-- A bidegree of the bracket is absent exactly when it has no enhanced states, over a
nontrivial coefficient ring. -/
theorem isZero_khovanovBracket_X_iff [Nontrivial R] (j r : ℤ) :
    IsZero ((D.khovanovBracket hD R j).X r) ↔
      ∀ S : Finset (Fin n), (#S : ℤ) = r →
        ∀ l : D.ResolvedCircle (cubeState S) → Bool,
          (#S : ℤ) + Khovanov.labelingQuantumDegree _ l ≠ j := by
  rw [khovanovBracket_apply, Functor.isZero_cubeComplex_X_iff]
  simp only [resolutionCube_obj, ModuleCat.isZero_of_iff_subsingleton,
    Submodule.subsingleton_iff_eq_bot, Khovanov.circleQuantumGrading_piece_eq_bot_iff,
    Subtype.forall]
  constructor
  · intro h S hS l hl
    exact h S hS l (by omega)
  · intro h S hS l hl
    exact h S hS l (by omega)

/-- Every enhanced state of the bracket lies between the extreme-resolution quantum bounds. -/
theorem card_add_labelingQuantumDegree_mem_Icc (S : Finset (Fin n))
    (l : D.ResolvedCircle (cubeState S) → Bool) :
    (#S : ℤ) + Khovanov.labelingQuantumDegree _ l ∈
      Set.Icc (-(D.stateLoopCount (cubeState ∅) : ℤ))
        ((n : ℤ) + D.stateLoopCount (cubeState univ)) := by
  have hlabel := Khovanov.abs_labelingQuantumDegree_le l
  rw [card_resolvedCircle, abs_le] at hlabel
  have hA := D.stateLoopCount_cubeState_le_allA S
  have hB := D.stateLoopCount_cubeState_le_allB S
  have hS := card_le_univ S
  simp only [Fintype.card_fin] at hS
  constructor <;> omega

/-- Every term vanishes outside the uniform quantum interval determined by the all-A and all-B
circle counts, over any commutative coefficient ring. -/
theorem isZero_khovanovBracket_X_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc (-(D.stateLoopCount (cubeState ∅) : ℤ))
      ((n : ℤ) + D.stateLoopCount (cubeState univ))) (r : ℤ) :
    IsZero ((D.khovanovBracket hD R j).X r) := by
  rw [khovanovBracket_apply, Functor.isZero_cubeComplex_X_iff]
  intro S
  rw [resolutionCube_obj, ModuleCat.isZero_of_iff_subsingleton,
    Submodule.subsingleton_iff_eq_bot]
  apply Khovanov.circleQuantumGrading_piece_eq_bot
  intro l hl
  apply hj
  have hmem := D.card_add_labelingQuantumDegree_mem_Icc S.1 l
  convert hmem using 1
  omega

/-- The whole quantum-component complex vanishes outside the extreme-resolution interval. -/
theorem isZero_khovanovBracket_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc (-(D.stateLoopCount (cubeState ∅) : ℤ))
      ((n : ℤ) + D.stateLoopCount (cubeState univ))) :
    IsZero (D.khovanovBracket hD R j) := by
  rw [IsZero.iff_id_eq_zero]
  ext r : 1
  exact (D.isZero_khovanovBracket_X_of_quantum_notMem_Icc hD R hj r).eq_of_src _ _

/-- Only finitely many quantum-component complexes of the bracket are nonzero. -/
theorem finite_quantumSupport_khovanovBracket :
    {j : ℤ | ¬ IsZero (D.khovanovBracket hD R j)}.Finite :=
  (Set.finite_Icc _ _).subset fun _ hj ↦ by
    by_contra h
    exact hj (D.isZero_khovanovBracket_of_quantum_notMem_Icc hD R h)

/-- Bracket homology vanishes outside the same quantum interval as the chain groups. -/
theorem isZero_homology_khovanovBracket_of_quantum_notMem_Icc {j : ℤ}
    (hj : j ∉ Set.Icc (-(D.stateLoopCount (cubeState ∅) : ℤ))
      ((n : ℤ) + D.stateLoopCount (cubeState univ))) (r : ℤ) :
    IsZero ((D.khovanovBracket hD R j).homology r) :=
  (HomologicalComplex.ExactAt.of_isZero
    (D.isZero_khovanovBracket_X_of_quantum_notMem_Icc hD R hj r)).isZero_homology

/-- The set of nonzero chain groups is finite in the two gradings jointly. -/
theorem finite_bigradedSupport_khovanovBracket :
    {p : ℤ × ℤ | ¬ IsZero ((D.khovanovBracket hD R p.2).X p.1)}.Finite := by
  refine ((Set.finite_Icc (0 : ℤ) n).prod
    (Set.finite_Icc (-(D.stateLoopCount (cubeState ∅) : ℤ))
      ((n : ℤ) + D.stateLoopCount (cubeState univ)))).subset ?_
  rintro ⟨r, j⟩ h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra hr
    apply h
    rw [khovanovBracket_apply]
    exact (D.resolutionCube hD R j).isZero_cubeComplex_X_of_neg (by omega)
  · by_contra hr
    apply h
    rw [khovanovBracket_apply]
    exact (D.resolutionCube hD R j).isZero_cubeComplex_X_of_card_lt (by simpa using hr)
  · by_contra hj
    exact h (D.isZero_khovanovBracket_X_of_quantum_notMem_Icc hD R hj r)

end TauCeti.PDCode
