/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.Basic
public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.NumberTheory.LocalField.Padic

/-!
# Degree-one local Galois cohomology with trivial coefficients

For a nonarchimedean local field `K` and a prime `p` invertible in `K`, the continuous
cohomology `H¹(G_K, 𝔽_p)` is finite and hence finite-dimensional. If `K` contains a primitive
`p`th root of unity, Kummer theory shows that it is nontrivial. If `K` is a finite compatible
extension of `ℚ_[p]` containing a primitive `p`th root of unity, its dimension is
`[K : ℚ_[p]] + 2`: Kummer theory identifies it with `Kˣ/(Kˣ)^p`, which for every finite
compatible extension of `ℚ_[p]` has `p · #μ_p(K) · p ^ [K : ℚ_[p]]` elements.

These degree-one counts are the arithmetic input to generator ranks of maximal pro-`p`
Galois quotients.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., VII §3.
* J.-P. Serre, *Galois Cohomology*, II §5.2.
-/

public section

namespace TauCeti

open ContCohomology ClassFieldTheory ValuativeRel

universe u

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [Fact p.Prime] in
/-- Degree-one absolute Galois cohomology with trivial `ℤ/p` coefficients is finite when
`p` is nonzero in the local field, even when `p` is not prime. At prime `p`, this also supplies
its finite-dimensionality over `𝔽_p`. -/
instance finite_cohomFp_one_absoluteGaloisGroup [NeZero (p : K)] :
    Finite (cohomFp p (Field.absoluteGaloisGroup K) 1) := by
  have : NeZero p := ⟨fun h ↦ NeZero.ne (p : K) (by simp [h])⟩
  exact finite_continuousCohomology_of_le_one (NeZero.ne (p : K))
    (trivialFp p (Field.absoluteGaloisGroup K))
    (isSmoothDiscrete_trivialFp p (Field.absoluteGaloisGroup K)) (by omega)

omit [Fact p.Prime] in
/-- If the local field contains a primitive `p`th root of unity with `1 < p`, then
`H¹(G_K, ℤ/p)` with trivial coefficients is nontrivial: by Kummer theory it has as many elements
as `Kˣ/(Kˣ)^p`, a nonzero multiple of `p`. -/
theorem nontrivial_cohomFp_one_absoluteGaloisGroup_of_isPrimitiveRoot [Fact (1 < p)] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : Nontrivial (cohomFp p (Field.absoluteGaloisGroup K) 1) := by
  have hp : 1 < p := Fact.out
  have : NeZero p := ⟨by omega⟩
  have : NeZero (p : K) := hζ.neZero'
  have hcard := natCard_cohomFp_one_absoluteGaloisGroup_of_isPrimitiveRoot p K hζ
  rw [powerClassQuotient, powerSubgroup_eq_range_powMonoidHom,
    card_powerClasses (NeZero.ne (p : K)), mul_assoc] at hcard
  rw [← Finite.one_lt_card_iff_nontrivial]
  exact hp.trans_le (Nat.le_of_dvd Nat.card_pos (Dvd.intro _ hcard.symm))

/-- For a finite compatible extension `K` of `ℚ_[p]`, the group `Kˣ/(Kˣ)^p` of `p`th power classes
has `p · #μ_p(K) · p ^ [K : ℚ_[p]]` elements: the residue-field factor of the local count is
`p ^ (f · e)`, with `f · e = [K : ℚ_[p]]`. -/
theorem natCard_powerClassQuotient_eq_mul_pow_finrank
    [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K] :
    Nat.card (powerClassQuotient Kˣ p) =
      p * Nat.card (rootsOfUnity p K) * p ^ Module.finrank ℚ_[p] K := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  have hvaluation : natCastValuation K p (NeZero.ne (p : K)) =
      ramificationIndex ℚ_[p] K := by
    rw [natCastValuation_eq_ramificationIndex_mul (K := ℚ_[p]) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
      Padic.natCastValuation_self, mul_one]
  rw [powerClassQuotient, powerSubgroup_eq_range_powMonoidHom,
    card_powerClasses (NeZero.ne (p : K)), hvaluation, natCard_residueField ℚ_[p] K,
    Padic.natCard_residueField, ← ramificationIndex_mul_inertiaDegree ℚ_[p] K]
  ring

/-- If a finite compatible extension of `ℚ_[p]` contains `μ_p`, then
`dim H¹(G_K, 𝔽_p) = [K : ℚ_[p]] + 2`. -/
theorem finrank_cohomFp_one_absoluteGaloisGroup_of_exists_isPrimitiveRoot
    [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 1) =
      Module.finrank ℚ_[p] K + 2 := by
  obtain ⟨ζ, hζ⟩ := hmu
  have : NeZero (p : K) := ⟨hζ.neZero'.out⟩
  have hcard := natCard_cohomFp_one_absoluteGaloisGroup_of_isPrimitiveRoot p K hζ
  rw [natCard_powerClassQuotient_eq_mul_pow_finrank, hζ.card_rootsOfUnity] at hcard
  have hfin := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := cohomFp p (Field.absoluteGaloisGroup K) 1)
  rw [Nat.card_zmod, hcard] at hfin
  refine Nat.pow_right_injective (Fact.out : p.Prime).two_le ?_
  dsimp only
  rw [← hfin]
  ring

end TauCeti
