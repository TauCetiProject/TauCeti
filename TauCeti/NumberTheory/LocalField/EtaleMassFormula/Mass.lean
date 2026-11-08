/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.OrbitWeight

/-!
# The étale mass of a local field

For a nonarchimedean local field `K` with residue field of cardinality `q`, the discriminant
exponent `d(ρ)` of a labelled Galois set `ρ : TauCeti.GaloisSet K n` is the orbit discriminant
exponent of its action, and the étale mass is
`M_n(K) = (1 / n!) ∑_ρ q ^ (-d(ρ))`,
summed over all labelled Galois sets of size `n` in `ℝ≥0∞`. A Galois set of size `n` is the set of
`K`-embeddings of an étale `K`-algebra of degree `n` into `SeparableClosure K`, labelled by
`Fin n`, and `d(ρ)` is the valuation of the discriminant of that algebra. Each isomorphism class
of algebras `A` carries `n! / #Aut_K(A)` labellings, which is why `M_n(K)` is Bhargava's mass
`∑_[A] 1 / (#Aut_K(A) q ^ (v(Disc A)))`; that identification is not proved in this file.

A transitive Galois set has a single orbit, so its discriminant exponent is that of the fixed
field of any point stabilizer. Combined with `TauCeti.GaloisSet.tsum_isTransitive`, the
transitive Galois sets of size `n` weigh `(n - 1)!` times the subextensions of degree `n`.

In equal characteristic there can be infinitely many Galois sets of a given size, which is why the
mass is valued in `ℝ≥0∞`.

## Main definitions and results

* `TauCeti.GaloisSet.discriminantExponent`: the discriminant exponent of a labelled Galois set.
* `TauCeti.GaloisSet.discriminantExponent_eq_of_equiv`: invariance under equivariant relabelling.
* `TauCeti.etaleMass`: the étale mass `M_n(K)`.
* `TauCeti.GaloisSet.discriminantExponent_of_isTransitive`: the transitive case.
* `TauCeti.tsum_isTransitive_one_div_natCard_residueField_pow_discriminantExponent`: the
  transitive Galois sets weigh `(n - 1)!` times the subextensions of degree `n`.
* `TauCeti.etaleMass_zero` and `TauCeti.etaleMass_one`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2 and §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

namespace GaloisSet

/-- The discriminant exponent `d(ρ)` of a labelled Galois set: the orbit discriminant exponent of
its action, that is, the sum over the orbits of the discriminant exponents of the fixed fields of
point stabilizers. -/
def discriminantExponent (ρ : GaloisSet K n) : ℕ :=
  letI := ρ.mulAction
  orbitDiscriminantExponent K (Fin n)

/-- The discriminant exponent of a labelled Galois set is the orbit discriminant exponent of its
action. -/
theorem discriminantExponent_def (ρ : GaloisSet K n) :
    ρ.discriminantExponent = (letI := ρ.mulAction; orbitDiscriminantExponent K (Fin n)) :=
  (rfl)

/-- Equivariant bijections preserve the discriminant exponent of labelled Galois sets. -/
theorem discriminantExponent_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n),
      e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.discriminantExponent = τ.discriminantExponent := by
  let := ρ.mulAction
  let := τ.mulAction
  exact orbitDiscriminantExponent_eq_of_equiv K e he

/-- A transitive labelled Galois set has the discriminant exponent of the fixed field of the
stabilizer of any of its labels. -/
theorem discriminantExponent_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive)
    (i : Fin n) :
    ρ.discriminantExponent =
      (letI := ρ.mulAction
      (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) i)).discriminantExponent) := by
  let := ρ.mulAction
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  exact orbitDiscriminantExponent_of_isPretransitive K i

/-- The trivial labelled Galois set has discriminant exponent zero. -/
@[simp]
theorem discriminantExponent_trivial : (trivial K n).discriminantExponent = 0 := by
  let := (trivial K n).mulAction
  exact orbitDiscriminantExponent_of_trivial K fun σ i ↦ trivial_val_apply σ i

/-- An action on at most one point has zero discriminant exponent. -/
@[simp]
theorem discriminantExponent_of_subsingleton [Subsingleton (Fin n)] (ρ : GaloisSet K n) :
    ρ.discriminantExponent = 0 := by
  let := ρ.mulAction
  exact orbitDiscriminantExponent_of_subsingleton K

end GaloisSet

variable (K) in
/-- The **étale mass** `M_n(K) = (1 / n!) ∑_ρ q ^ (-d(ρ))` of a nonarchimedean local field `K`,
summed over the labelled Galois sets of size `n`, where `q` is the residue cardinality of `K`. -/
def etaleMass (n : ℕ) : ℝ≥0∞ :=
  (n.factorial : ℝ≥0∞)⁻¹ *
    ∑' ρ : GaloisSet K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent

variable (K) in
/-- The étale mass is `1 / n!` times the sum of `q ^ (-d(ρ))` over the labelled Galois sets. -/
theorem etaleMass_def (n : ℕ) :
    etaleMass K n = (n.factorial : ℝ≥0∞)⁻¹ *
      ∑' ρ : GaloisSet K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent :=
  (rfl)

variable (K) in
/-- The étale mass of size zero is `1`, from the empty Galois set. -/
@[simp]
theorem etaleMass_zero : etaleMass K 0 = 1 := by
  rw [etaleMass_def, tsum_eq_single (GaloisSet.trivial K 0)
    fun ρ hρ ↦ (hρ (Subsingleton.elim _ _)).elim]
  simp

variable (K) in
/-- The étale mass of size one is `1`, from the one-point Galois set. -/
@[simp]
theorem etaleMass_one : etaleMass K 1 = 1 := by
  rw [etaleMass_def, tsum_eq_single (GaloisSet.trivial K 1)
    fun ρ hρ ↦ (hρ (Subsingleton.elim _ _)).elim]
  simp

/-- **The transitive mass by subextensions.** Summed over the transitive labelled Galois sets of
positive size `n`, the weights `q ^ (-d(ρ))` are `(n - 1)!` times the sum of `q ^ (-d(L))` over
the subextensions `L` of `SeparableClosure K` of degree `n`. -/
theorem tsum_isTransitive_one_div_natCard_residueField_pow_discriminantExponent (hn : 0 < n) :
    ∑' ρ : {ρ : GaloisSet K n // ρ.IsTransitive},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ((n - 1).factorial : ℝ≥0∞) *
        ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = n},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent := by
  refine (tsum_congr fun ρ ↦ ?_).trans (GaloisSet.tsum_isTransitive ⟨0, hn⟩
    fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent)
  rw [ρ.1.discriminantExponent_of_isTransitive ρ.2 ⟨0, hn⟩]

end TauCeti
