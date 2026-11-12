/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Prime
public import TauCeti.Geometry.Manifold.Orientation.Basic

/-!
# The prime decomposition of 3-manifolds

Every closed connected orientable `3`-manifold `M` splits along embedded `2`-spheres as a connected
sum `M ≃ P₁ # ⋯ # P_k` of prime manifolds (Kneser, 1929), and the prime factors are unique up to
order and diffeomorphism (Milnor, 1962). This is the first of the two canonical decompositions of a
`3`-manifold. The second cuts each prime factor along incompressible tori and is the JSJ
decomposition of `TauCeti.LowDimTopology.JSJDecomposition`; a prime factor other than `S¹ × S²` is
irreducible, which is the hypothesis of the geometrization conjecture
`TauCeti.GeometrizationConjecture`.

The connected sum is the one of `TauCeti.Geometry.Manifold.ConnectedSum.Prime`: a smooth
`3`-manifold is prime (`TauCeti.IsPrimeManifold 3 M`) when it is not `S³` and in every
decomposition of it as a connected sum of two closed `3`-manifolds one summand is `S³`; and
`TauCeti.IsIteratedConnectedSum 3 P M` presents `M` as the connected sum of the closed manifolds
`P 0, …, P (k - 1)`, with `k = 0` for `S³` itself.

* `TauCeti.KneserPrimeDecompositionTheorem` asserts that every closed connected orientable smooth
  `3`-manifold is a connected sum of finitely many closed prime `3`-manifolds.
* `TauCeti.MilnorPrimeDecompositionTheorem` asserts that two such presentations of the same
  manifold have the same number of factors and, after a permutation, diffeomorphic factors.

Both are stated, not proved. Orientations are not recorded. Milnor's theorem for oriented
manifolds says the factors are unique up to orientation-preserving diffeomorphism. A presentation
along arbitrary coordinate balls is an oriented one for suitable orientations of the factors, so
Milnor's theorem gives the unoriented uniqueness stated here. Orientability cannot be dropped from
the uniqueness: for a nonorientable `N`, the manifolds `N # (S¹ × S²)` and `N # (S¹ ×~ S²)`, the
latter the nonorientable `2`-sphere bundle over the circle, are diffeomorphic.

## Main definitions

* `TauCeti.KneserPrimeDecompositionTheorem`: existence of prime decompositions of closed connected
  orientable `3`-manifolds.
* `TauCeti.MilnorPrimeDecompositionTheorem`: uniqueness of prime decompositions of closed connected
  orientable `3`-manifolds.

## Main results

* `TauCeti.KneserPrimeDecompositionTheorem.exists_isIteratedConnectedSum` and
  `TauCeti.MilnorPrimeDecompositionTheorem.exists_equiv`: applying the theorems.
* `TauCeti.MilnorPrimeDecompositionTheorem.card_eq`: the number of prime factors is an invariant of
  the manifold.
* `TauCeti.MilnorPrimeDecompositionTheorem.eq_one_of_isPrimeManifold` and
  `TauCeti.MilnorPrimeDecompositionTheorem.nonempty_diffeomorph_of_isPrimeManifold`: a prime
  decomposition of a prime manifold has exactly one factor, diffeomorphic to the manifold.

## References

* H. Kneser, *Geschlossene Flächen in dreidimensionalen Mannigfaltigkeiten*, Jahresber. Deutsch.
  Math.-Verein. 38 (1929), 248–260.
* J. Milnor, *A unique decomposition theorem for 3-manifolds*, Amer. J. Math. 84 (1962), 1–7,
  Theorems 1 and 2.
* J. Hempel, *3-Manifolds*, Annals of Mathematics Studies 86, Princeton University Press (1976),
  Theorems 3.15 and 3.21.
* A. Hatcher, *Notes on Basic 3-Manifold Topology*, Section 1.1, Theorem 1.5.
-/

public section

open scoped Manifold ContDiff

universe u

namespace TauCeti

/-- **Kneser's prime decomposition theorem**, as a statement: every closed connected orientable
smooth `3`-manifold `M` is a connected sum `P 0 # ⋯ # P (k - 1)` of finitely many closed prime
smooth `3`-manifolds; the empty connected sum, `k = 0`, is `S³`. -/
def KneserPrimeDecompositionTheorem : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [Orientable (𝓡 3) M],
    ∃ (k : ℕ) (P : Fin k → Type u) (_ : ∀ i, TopologicalSpace (P i)) (_ : ∀ i, T2Space (P i))
      (_ : ∀ i, CompactSpace (P i)) (_ : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i))
      (_ : ∀ i, IsManifold (𝓡 3) ∞ (P i)),
      (∀ i, IsPrimeManifold 3 (P i)) ∧ IsIteratedConnectedSum 3 P M

/-- **Milnor's uniqueness of prime decompositions**, as a statement: if a closed connected
orientable smooth `3`-manifold `M` is a connected sum of the closed prime `3`-manifolds
`P 0, …, P (k - 1)` and also of the closed prime `3`-manifolds `Q 0, …, Q (l - 1)`, then there is
a bijection `σ : Fin k ≃ Fin l` with each `P i` diffeomorphic to `Q (σ i)`. -/
def MilnorPrimeDecompositionTheorem : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [Orientable (𝓡 3) M]
    (k : ℕ) (P : Fin k → Type u) [∀ i, TopologicalSpace (P i)] [∀ i, T2Space (P i)]
    [∀ i, CompactSpace (P i)] [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
    [∀ i, IsManifold (𝓡 3) ∞ (P i)]
    (l : ℕ) (Q : Fin l → Type u) [∀ j, TopologicalSpace (Q j)] [∀ j, T2Space (Q j)]
    [∀ j, CompactSpace (Q j)] [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Q j)]
    [∀ j, IsManifold (𝓡 3) ∞ (Q j)],
    (∀ i, IsPrimeManifold 3 (P i)) → (∀ j, IsPrimeManifold 3 (Q j)) →
      IsIteratedConnectedSum 3 P M → IsIteratedConnectedSum 3 Q M →
        ∃ σ : Fin k ≃ Fin l, ∀ i, Nonempty (P i ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ Q (σ i))

section Apply

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [Orientable (𝓡 3) M]

variable (M) in
/-- Applying Kneser's theorem: a closed connected orientable smooth `3`-manifold is a connected sum
of finitely many closed prime `3`-manifolds. -/
theorem KneserPrimeDecompositionTheorem.exists_isIteratedConnectedSum
    (h : KneserPrimeDecompositionTheorem.{u}) :
    ∃ (k : ℕ) (P : Fin k → Type u) (_ : ∀ i, TopologicalSpace (P i)) (_ : ∀ i, T2Space (P i))
      (_ : ∀ i, CompactSpace (P i)) (_ : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i))
      (_ : ∀ i, IsManifold (𝓡 3) ∞ (P i)),
      (∀ i, IsPrimeManifold 3 (P i)) ∧ IsIteratedConnectedSum 3 P M :=
  h M

variable {k : ℕ} {P : Fin k → Type u} [∀ i, TopologicalSpace (P i)] [∀ i, T2Space (P i)]
  [∀ i, CompactSpace (P i)] [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
  [∀ i, IsManifold (𝓡 3) ∞ (P i)]
  {l : ℕ} {Q : Fin l → Type u} [∀ j, TopologicalSpace (Q j)] [∀ j, T2Space (Q j)]
  [∀ j, CompactSpace (Q j)] [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Q j)]
  [∀ j, IsManifold (𝓡 3) ∞ (Q j)]

/-- Applying Milnor's theorem: two prime decompositions of a closed connected orientable smooth
`3`-manifold have, after a permutation, diffeomorphic factors. -/
theorem MilnorPrimeDecompositionTheorem.exists_equiv (h : MilnorPrimeDecompositionTheorem.{u})
    (hP : ∀ i, IsPrimeManifold 3 (P i)) (hQ : ∀ j, IsPrimeManifold 3 (Q j))
    (hPM : IsIteratedConnectedSum 3 P M) (hQM : IsIteratedConnectedSum 3 Q M) :
    ∃ σ : Fin k ≃ Fin l, ∀ i, Nonempty (P i ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ Q (σ i)) :=
  h M k P l Q hP hQ hPM hQM

/-- **The number of prime factors is an invariant**: by Milnor's theorem, two prime
decompositions of a closed connected orientable smooth `3`-manifold have the same number of
factors. -/
theorem MilnorPrimeDecompositionTheorem.card_eq (h : MilnorPrimeDecompositionTheorem.{u})
    (hP : ∀ i, IsPrimeManifold 3 (P i)) (hQ : ∀ j, IsPrimeManifold 3 (Q j))
    (hPM : IsIteratedConnectedSum 3 P M) (hQM : IsIteratedConnectedSum 3 Q M) : k = l := by
  obtain ⟨σ, -⟩ := h.exists_equiv hP hQ hPM hQM
  simpa using Fintype.card_congr σ

end Apply

section Prime

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [Orientable (𝓡 3) M]
  {k : ℕ} {P : Fin k → Type} [∀ i, TopologicalSpace (P i)] [∀ i, T2Space (P i)]
  [∀ i, CompactSpace (P i)] [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
  [∀ i, IsManifold (𝓡 3) ∞ (P i)]

/-- The one-factor decomposition `M ≃ M # S³` of a prime manifold, compared with a prime
decomposition `P` by Milnor's theorem. -/
private theorem MilnorPrimeDecompositionTheorem.exists_equiv_fin_one
    (h : MilnorPrimeDecompositionTheorem.{0}) (hM : IsPrimeManifold 3 M)
    (hP : ∀ i, IsPrimeManifold 3 (P i)) (hPM : IsIteratedConnectedSum 3 P M) :
    ∃ σ : Fin k ≃ Fin 1, ∀ i, Nonempty (P i ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (fun _ : Fin 1 ↦ M) (σ i)) :=
  h.exists_equiv (Q := fun _ : Fin 1 ↦ M) hP (fun _ ↦ hM) hPM
    (isIteratedConnectedSum_one _ (Diffeomorph.refl _ _ _))

/-- **A prime manifold has a single prime factor**: by Milnor's theorem, a prime decomposition of a
closed connected orientable prime smooth `3`-manifold has exactly one factor. -/
theorem MilnorPrimeDecompositionTheorem.eq_one_of_isPrimeManifold
    (h : MilnorPrimeDecompositionTheorem.{0}) (hM : IsPrimeManifold 3 M)
    (hP : ∀ i, IsPrimeManifold 3 (P i)) (hPM : IsIteratedConnectedSum 3 P M) : k = 1 := by
  obtain ⟨σ, -⟩ := h.exists_equiv_fin_one hM hP hPM
  simpa using Fintype.card_congr σ

/-- **A prime manifold is its own prime factor**: by Milnor's theorem, the factor of a prime
decomposition of a closed connected orientable prime smooth `3`-manifold `M` is diffeomorphic to
`M`. -/
theorem MilnorPrimeDecompositionTheorem.nonempty_diffeomorph_of_isPrimeManifold
    (h : MilnorPrimeDecompositionTheorem.{0}) (hM : IsPrimeManifold 3 M)
    (hP : ∀ i, IsPrimeManifold 3 (P i)) (hPM : IsIteratedConnectedSum 3 P M) (i : Fin k) :
    Nonempty (P i ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ M) :=
  (h.exists_equiv_fin_one hM hP hPM).elim fun _ hσ ↦ hσ i

end Prime

end TauCeti
