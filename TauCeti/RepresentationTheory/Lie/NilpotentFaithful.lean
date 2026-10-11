/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Weighted.Basic
public import TauCeti.Algebra.Lie.OfAssociative

/-!
# Birkhoff's faithful nilpotent representation

A positively weighted ordered Lie basis gives a left-multiplication action on the weighted
PBW quotient at cutoff `N`. Every acting operator has `N`-th power zero, and the action is
faithful when `N` exceeds every basis weight. A finite basis gives a module-finite carrier.
Lower-central weights supply these conditions for every finite-dimensional nilpotent Lie
algebra, over a field of any characteristic.

The action reuses `LieHom.leftRegularRep`. The carrier, its finiteness, separation of the
Lie generators, and their uniform power bound come from the weighted PBW construction in
`TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Weighted.Basic`. No Lie-module instance is installed
on the quotient: consumers use the explicit Lie homomorphism.

## References

* N. Jacobson, *Lie Algebras*, Chapter V, Birkhoff's theorem.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.
-/

public section

open Module

namespace Module.Basis

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι]
  (b : Basis ι R L) (w : ι → ℕ)
  (hbracket : ∀ i j k, w k < w i + w j → b.repr ⁅b i, b j⁆ k = 0)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "J" => b.weightedPBWIdeal w hbracket

/-- Left multiplication by Lie generators on the weighted PBW quotient at cutoff `N`. -/
noncomputable def weightedPBWRepresentation (N : ℕ) : L →ₗ⁅R⁆ Module.End R (U ⧸ J N) :=
  (((Ideal.Quotient.mkₐ R (J N)).toLieHom).comp
    (_root_.UniversalEnvelopingAlgebra.ι R)).leftRegularRep

/-- The weighted action is the left-regular representation of the canonical quotient map. -/
theorem weightedPBWRepresentation_def (N : ℕ) :
    b.weightedPBWRepresentation w hbracket N =
      (((Ideal.Quotient.mkₐ R (J N)).toLieHom).comp
        (_root_.UniversalEnvelopingAlgebra.ι R)).leftRegularRep :=
  (rfl)

/-- The weighted action multiplies by the quotient class of the canonical Lie generator. -/
@[simp]
theorem weightedPBWRepresentation_apply (N : ℕ) (x : L) (a : U ⧸ J N) :
    b.weightedPBWRepresentation w hbracket N x a =
      Ideal.Quotient.mk (J N) (_root_.UniversalEnvelopingAlgebra.ι R x) * a := by
  simp only [weightedPBWRepresentation_def, LieHom.leftRegularRep_apply,
    LieHom.comp_apply, AlgHom.coe_toLieHom, Ideal.Quotient.mkₐ_eq_mk]

/-- Acting on a representative multiplies by the Lie generator before taking its quotient class. -/
theorem weightedPBWRepresentation_apply_mk (N : ℕ) (x : L) (a : U) :
    b.weightedPBWRepresentation w hbracket N x (Ideal.Quotient.mk (J N) a) =
      Ideal.Quotient.mk (J N) (_root_.UniversalEnvelopingAlgebra.ι R x * a) := by
  rw [weightedPBWRepresentation_apply, ← map_mul]

/-- A Lie element acts by zero precisely when its canonical image lies in the weighted ideal. -/
@[simp]
theorem weightedPBWRepresentation_eq_zero_iff (N : ℕ) (x : L) :
    b.weightedPBWRepresentation w hbracket N x = 0 ↔
      _root_.UniversalEnvelopingAlgebra.ι R x ∈ J N := by
  rw [weightedPBWRepresentation_def, LieHom.leftRegularRep_eq_zero_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The weighted action is faithful when the cutoff exceeds every basis weight. -/
theorem weightedPBWRepresentation_injective (N : ℕ) (hN : ∀ i, w i < N) :
    Function.Injective (b.weightedPBWRepresentation w hbracket N) := by
  rw [weightedPBWRepresentation_def, LieHom.leftRegularRep_injective_iff]
  exact b.quotient_weightedPBWIdeal_ι_injective w hbracket N hN

/-- With positive weights, every acting operator has `N`-th power zero, uniformly in the
Lie element. No nilpotence, finiteness, or field assumption is needed for this bound. -/
@[simp]
theorem weightedPBWRepresentation_pow_eq_zero (hpos : ∀ i, 0 < w i) (N : ℕ) (x : L) :
    b.weightedPBWRepresentation w hbracket N x ^ N = 0 := by
  rw [weightedPBWRepresentation_def, LieHom.leftRegularRep_eq_mulLeft,
    LinearMap.pow_mulLeft, LinearMap.mulLeft_eq_zero_iff]
  simpa only [LieHom.comp_apply, AlgHom.coe_toLieHom, Ideal.Quotient.mkₐ_eq_mk] using
    b.quotient_weightedPBWIdeal_ι_pow_eq_zero w hbracket hpos N x

end Module.Basis

namespace TauCeti

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieRing.IsNilpotent L]

/-- **Birkhoff's theorem on a weighted PBW quotient.** A finite-dimensional nilpotent Lie
algebra has a faithful left-multiplication representation on a finite-dimensional weighted
enveloping quotient, with one positive nilpotence bound for all acting operators.
The basis, weights, and cutoff are supplied by the conclusion, in every characteristic. -/
theorem exists_faithful_weightedPBWRepresentation :
    ∃ (N : ℕ) (b : Basis (Fin (Module.finrank K L)) K L)
      (w : Fin (Module.finrank K L) → ℕ)
      (hbracket : ∀ i j k, w k < w i + w j → b.repr ⁅b i, b j⁆ k = 0),
      0 < N ∧ (∀ i, 0 < w i ∧ w i < N) ∧
      Module.Finite K (_root_.UniversalEnvelopingAlgebra K L ⧸
        b.weightedPBWIdeal w hbracket N) ∧
      Function.Injective (b.weightedPBWRepresentation w hbracket N) ∧
      ∀ x : L, b.weightedPBWRepresentation w hbracket N x ^ N = 0 := by
  obtain ⟨N, b, w, hbracket, hN, hweight, hfinite, _, _⟩ :=
    UniversalEnvelopingAlgebra.exists_weightedPBWIdeal_of_isNilpotent K L
  refine ⟨N, b, w, hbracket, hN, hweight, hfinite, ?_, ?_⟩
  · exact b.weightedPBWRepresentation_injective w hbracket N (fun i ↦ (hweight i).2)
  · exact b.weightedPBWRepresentation_pow_eq_zero w hbracket (fun i ↦ (hweight i).1) N

end TauCeti
