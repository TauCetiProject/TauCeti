/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.OrbitWeight
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The mass of labelled Galois sets

The discriminant exponent of a labelled Galois set is the sum of the discriminant exponents
of its orbit fields. For a transitive nonempty action it is the discriminant exponent of the
field fixed by any point stabilizer. Equivariant relabelling preserves this weight.

`TauCeti.etaleMass K n` is the sum of the inverse discriminant norms of labelled Galois sets
of size `n`, divided by `n!`. It takes values in `ℝ≥0∞`: in positive characteristic there can
be infinitely many such actions. Dividing by the number of labellings gives the normalization
for counting étale algebras with reciprocal automorphism weights. The masses in degrees zero
and one are both one.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density
  of number field discriminants*, IMRN 2007, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN 2007, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

namespace GaloisSet

/-- The discriminant exponent of a labelled Galois set, summed over its orbit fields. -/
def discriminantExponent (ρ : GaloisSet K n) : ℕ :=
  letI := ρ.mulAction
  orbitDiscriminantExponent K (Fin n)

/-- The discriminant exponent is the orbit discriminant weight of the associated action. -/
theorem discriminantExponent_def (ρ : GaloisSet K n) :
    ρ.discriminantExponent = (letI := ρ.mulAction; orbitDiscriminantExponent K (Fin n)) :=
  (rfl)

/-- Equivariant bijections preserve the discriminant exponent of labelled Galois sets. -/
theorem discriminantExponent_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (i : Fin n),
      e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.discriminantExponent = τ.discriminantExponent := by
  let := ρ.mulAction
  let := τ.mulAction
  exact orbitDiscriminantExponent_eq_of_equiv K e he

/-- A transitive Galois set has the discriminant exponent of the fixed field of any point
stabilizer. The point excludes the empty action. -/
theorem discriminantExponent_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive)
    (i : Fin n) :
    ρ.discriminantExponent =
      (letI := ρ.mulAction
      (IntermediateField.fixedField
        (MulAction.stabilizer
          (SeparableClosure K ≃ₐ[K] SeparableClosure K) i)).discriminantExponent) := by
  let := ρ.mulAction
  have : MulAction.IsPretransitive (SeparableClosure K ≃ₐ[K] SeparableClosure K) (Fin n) :=
    (MulAction.isPretransitive_iff _ _).mpr (ρ.isTransitive_iff.mp hρ)
  exact orbitDiscriminantExponent_of_isPretransitive K i

/-- Trivial Galois sets have zero discriminant exponent. -/
@[simp]
theorem discriminantExponent_trivial : (trivial K n).discriminantExponent = 0 := by
  let := (trivial K n).mulAction
  rw [discriminantExponent_def]
  exact orbitDiscriminantExponent_of_trivial K fun σ i ↦ trivial_val_apply σ i

/-- An action on at most one point has zero discriminant exponent. -/
@[simp]
theorem discriminantExponent_of_subsingleton [Subsingleton (Fin n)] (ρ : GaloisSet K n) :
    ρ.discriminantExponent = 0 := by
  let := ρ.mulAction
  rw [discriminantExponent_def]
  exact orbitDiscriminantExponent_of_subsingleton K

end GaloisSet

/-- The degree-`n` étale mass: the sum of inverse discriminant norms over labelled Galois
sets, normalized by `n!`. The extended nonnegative reals accommodate infinite families. -/
def etaleMass (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : ℝ≥0∞ :=
  (1 / (n.factorial : ℝ≥0∞)) *
    ∑' ρ : GaloisSet K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent

/-- The defining labelled-action sum for the étale mass. -/
theorem etaleMass_def :
    etaleMass K n = (1 / (n.factorial : ℝ≥0∞)) *
      ∑' ρ : GaloisSet K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent :=
  (rfl)

/-- The empty Galois set contributes mass one, with the normalization `0! = 1`. -/
@[simp]
theorem etaleMass_zero : etaleMass K 0 = 1 := by
  simp [etaleMass_def]

/-- The sole degree-one Galois set is trivial, so its mass is one. -/
@[simp]
theorem etaleMass_one : etaleMass K 1 = 1 := by
  simp [etaleMass_def]

end TauCeti
