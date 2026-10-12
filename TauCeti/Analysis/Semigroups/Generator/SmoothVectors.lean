/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.IteratedDomain
public import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smooth vectors of a strongly continuous semigroup

A vector is smooth when it belongs to every iterated domain of the infinitesimal generator.
Its semigroup orbit is then smooth on the closed nonnegative half-line, including right
derivatives at the origin. More generally, membership in `D(Aⁿ)` gives `Cⁿ` regularity.
The semigroup preserves smooth vectors, and the generator maps them to smooth vectors.

These facts connect the iterated-domain construction to regularity of the abstract Cauchy
problem. The orbit characterization can identify time-smoothed approximants as members of
`smoothVectors` once their orbits are shown to be smooth.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Lemma II.1.3.
-/

public section

noncomputable section

open Set
open scoped ContDiff Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X)

/-- A smooth vector belongs to the domain of every power of the generator. -/
def IsSmoothVector (x : X) : Prop := ∀ n : ℕ, x ∈ domainPow S.generator n

omit [CompleteSpace X] in
/-- The linear subspace of vectors in every iterated generator domain. -/
def smoothVectors : Submodule ℝ X := ⨅ n : ℕ, domainPow S.generator n

omit [CompleteSpace X] in
/-- Membership in the smooth-vector submodule is smoothness of the vector. -/
@[simp] theorem mem_smoothVectors {x : X} :
    x ∈ S.smoothVectors ↔ S.IsSmoothVector x := by
  simp [smoothVectors, IsSmoothVector, Submodule.mem_iInf]

omit [CompleteSpace X] in
/-- Every smooth vector belongs to the generator domain. -/
theorem IsSmoothVector.mem_domain {x : X} (hx : S.IsSmoothVector x) : x ∈ S.domain := by
  rw [← S.generator_domain, ← domainPow_one]
  exact hx 1

omit [CompleteSpace X] in
/-- The generator sends a smooth vector to another smooth vector. -/
theorem IsSmoothVector.generator {x : X} (hx : S.IsSmoothVector x) :
    S.IsSmoothVector (S.generator ⟨x, by rw [S.generator_domain]; exact hx.mem_domain⟩) := by
  intro n
  exact apply_mem_domainPow (hx (n + 1))

omit [CompleteSpace X] in
/-- Every semigroup operator preserves smooth vectors. -/
theorem IsSmoothVector.realOperator {x : X} (hx : S.IsSmoothVector x) {t : ℝ}
    (ht : 0 ≤ t) : S.IsSmoothVector (S.realOperator t x) :=
  fun n => S.realOperator_mem_domainPow ht (hx n)

/-- Membership in `D(Aⁿ)` gives `Cⁿ` regularity of the orbit on the nonnegative half-line. -/
theorem contDiffOn_realOperator_of_mem_domainPow (n : ℕ) {x : X}
    (hx : x ∈ domainPow S.generator n) :
    ContDiffOn ℝ n (fun t : ℝ => S.realOperator t x) (Ici 0) := by
  induction n generalizing x with
  | zero =>
      exact contDiffOn_zero.mpr (S.realOperator_continuousOn_Ici x)
  | succ n ih =>
      obtain ⟨hxd, hAx⟩ := mem_domainPow_succ.mp hx
      rw [S.generator_domain] at hxd
      rw [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
      refine ⟨fun t ht => (S.realOperator_hasDerivWithinAt_Ici ⟨x, hxd⟩ ht).differentiableWithinAt,
        by simp, ?_⟩
      apply (ih hAx).congr
      intro t ht
      simpa using S.realOperator_derivWithin_Ici ⟨x, hxd⟩ ht

/-- The orbit is `Cⁿ` on the nonnegative half-line exactly when its initial vector belongs
to the domain `D(Aⁿ)`. At the boundary, differentiability is understood from the right. -/
theorem mem_domainPow_iff_contDiffOn_realOperator (n : ℕ) (x : X) :
    x ∈ domainPow S.generator n ↔
      ContDiffOn ℝ n (fun t : ℝ => S.realOperator t x) (Ici 0) := by
  induction n generalizing x with
  | zero =>
      simp [S.realOperator_continuousOn_Ici]
  | succ n ih =>
      constructor
      · exact S.contDiffOn_realOperator_of_mem_domainPow (n + 1)
      · intro h
        rw [Nat.cast_add, Nat.cast_one,
          contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)] at h
        obtain ⟨hdiff, -, hderiv⟩ := h
        have hxd : x ∈ S.domain :=
          (S.mem_domain_iff_differentiableWithinAt_realOperator_zero x).2
            (hdiff 0 (by simp))
        refine mem_domainPow_succ.mpr ⟨by rwa [S.generator_domain], ?_⟩
        apply (ih (S.generator ⟨x, by rwa [S.generator_domain]⟩)).2
        apply hderiv.congr
        intro t ht
        exact (S.realOperator_derivWithin_Ici ⟨x, hxd⟩ ht).symm

/-- The orbit of a smooth vector is infinitely differentiable on the nonnegative half-line,
with one-sided derivatives at time zero. -/
theorem IsSmoothVector.contDiffOn_realOperator {x : X} (hx : S.IsSmoothVector x) :
    ContDiffOn ℝ ∞ (fun t : ℝ => S.realOperator t x) (Ici 0) := by
  rw [contDiffOn_infty]
  exact fun n => S.contDiffOn_realOperator_of_mem_domainPow n (hx n)

/-- Smooth vectors are precisely those with a smooth orbit on the nonnegative half-line. -/
theorem isSmoothVector_iff_contDiffOn_realOperator (x : X) :
    S.IsSmoothVector x ↔
      ContDiffOn ℝ ∞ (fun t : ℝ => S.realOperator t x) (Ici 0) := by
  rw [contDiffOn_infty]
  exact forall_congr' fun n => S.mem_domainPow_iff_contDiffOn_realOperator n x

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end

end
