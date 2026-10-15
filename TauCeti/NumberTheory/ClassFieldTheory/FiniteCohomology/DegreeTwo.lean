/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Torsion

/-!
# Finiteness of local Galois cohomology through degree two

For a nonarchimedean local field `F`, every finite smooth discrete Galois module killed by an
integer invertible in `F` has finite cohomology in degrees zero, one and two. In particular this
includes every nonzero exponent over a field of characteristic zero, even an exponent divisible
by the residue characteristic.

The degree-two arithmetic input is the local Brauer invariant: Kummer theory embeds
`H²(G_F, μₙ)` in `Br F`, and its invariant lies in the finite `n`-torsion subgroup of `ℚ/ℤ`.
Over a finite extension containing the roots of unity, every trivial module of prime order
is a roots-of-unity module. The open-normal-subgroup finiteness theorem then uses Shapiro and
coinduction to pass to arbitrary finite coefficients. This does not require a filtration by
trivial modules for the original Galois action.

The construction uses `h2MuToBr`, `invMap`, and
`ContinuousCohomology.finite_continuousCohomology_of_isOpen_of_normal_of_prime`.

## Main results

* `finite_continuousCohomology_muNRep_two`: finiteness with roots-of-unity coefficients.
* `finite_H2_of_isPrimitiveRoot_of_natCard_dvd`: finiteness for cyclic trivial coefficients.
* `finite_H`: finiteness with arbitrary finite smooth discrete coefficients through degree two.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.2, Proposition 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VII, §1,
  and (6.2.1) for the Kummer sequence.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology TauCeti.ContinuousCohomology

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

attribute [local instance] TopRep.distribMulAction

/-- Roots-of-unity cohomology in degree two is finite when the exponent is invertible in the
local field, since its Brauer invariant is killed by that exponent. -/
theorem finite_continuousCohomology_muNRep_two (hn : IsUnit (n : F)) :
    Finite (continuousCohomology 2 (muNRep n F)) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn.ne_zero (by simp [h])
  let f : continuousCohomology 2 (muNRep n F) → {x : AddCircle (1 : ℚ) | n • x = 0} :=
    fun x => ⟨invMap F (h2MuToBr n F x), by
      simp only [Set.mem_ofPred_eq]
      rw [← map_nsmul, (h2MuToBr_range n F hn _).1 ⟨x, rfl⟩, _root_.map_zero]⟩
  have := (AddCircle.finite_torsion (1 : ℚ) hn0).to_subtype
  exact Finite.of_injective f fun x y h => h2MuToBr_injective n F hn
    ((invMap F).injective (congrArg Subtype.val h))

/-- Degree-two cohomology of a cyclic trivial module of order dividing `n` is finite over a local
field containing a primitive `n`th root of unity. The group may be any topological copy of `G_F`. -/
theorem finite_H2_of_isPrimitiveRoot_of_natCard_dvd [NeZero n] {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) {H : Type} [Group H] [TopologicalSpace H] [ContinuousMul H]
    (φ : AbsoluteGaloisGroup F ≃ₜ* H) (M : Type) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction H M] [ContinuousSMul H M]
    [IsAddCyclic M] (hMn : Nat.card M ∣ n) (htriv : ∀ (h : H) (m : M), h • m = m) :
    Finite (H2 H M) := by
  have : NeZero (Nat.card M) := ⟨fun h ↦ NeZero.ne n (Nat.eq_zero_of_zero_dvd (h ▸ hMn))⟩
  -- A primitive n-th root supplies a primitive root of every order dividing n.
  have hζM : IsPrimitiveRoot (ζ ^ (n / Nat.card M)) (Nat.card M) := by
    have h := hζ.pow_of_dvd
      (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hMn) (NeZero.pos _)).ne'
      (Nat.div_dvd_of_dvd hMn)
    rwa [Nat.div_div_self hMn (NeZero.ne n)] at h
  have := hζM.neZero'
  have := finite_continuousCohomology_muNRep_two (NeZero.ne (Nat.card M : F)).isUnit
  have : Finite (H2 (AbsoluteGaloisGroup F) (KummerCoeff F (Nat.card M))) :=
    Finite.of_equiv _ (muNRepH2Equiv (Nat.card M) F).symm.toEquiv
  have hcard : Nat.card (KummerCoeff F (Nat.card M)) = Nat.card M :=
    (Nat.card_congr Additive.toMul).trans
      (hζM.map_of_injective (algebraMap F (SeparableClosure F)).injective).card_rootsOfUnity
  exact Finite.of_equiv _ (explicitMap2Equiv H M (AbsoluteGaloisGroup F)
    (KummerCoeff F (Nat.card M)) φ
    (addEquivOfAddCyclicCardEq hcard.symm) continuous_of_discreteTopology
    continuous_of_discreteTopology fun g m ↦ by
      rw [htriv, smul_kummerCoeff_eq_self hζM]).symm.toEquiv

/-- Cohomology in degrees zero through two of a finite smooth discrete Galois module over a
nonarchimedean local field is finite, provided its exponent is invertible in the field. -/
theorem finite_H (hn : (n : F) ≠ 0) (A : GalRep n F)
    (hA : IsSmoothDiscrete (ZMod n) A) [Finite A.V] {i : ℕ} (hi : i ≤ 2) :
    Finite (continuousCohomology i A) := by
  by_cases hi1 : i ≤ 1
  · exact finite_continuousCohomology_of_le_one hn A hA hi1
  obtain rfl : i = 2 := by omega
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  refine finite_continuousCohomology_of_prime_ge_two hn A hA 2 ?_
  intro L _ _ _ _ ζ hζ H _ _ _ _ φ j hj₀ hj M _ _ _ _ _ _ hM hMn hMtriv
  obtain rfl : j = 2 := by omega
  have := isAddCyclic_of_prime_card rfl (hp := ⟨hM⟩)
  have := finite_H2_of_isPrimitiveRoot_of_natCard_dvd hζ φ M hMn hMtriv
  exact Finite.of_equiv _ (explicitH2AddEquivContinuousCohomology H M).toEquiv

end TauCeti.ClassFieldTheory
