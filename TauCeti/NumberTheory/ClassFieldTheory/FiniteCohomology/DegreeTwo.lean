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
* `finite_H2_of_isPrimitiveRoot_of_natCard_eq`: finiteness for cyclic trivial coefficients.
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

/-- Degree-two cohomology of a cyclic trivial module of order `n` is finite over a local field
containing a primitive `n`th root of unity. The group may be any topological copy of `G_F`. -/
theorem finite_H2_of_isPrimitiveRoot_of_natCard_eq [NeZero n] {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) {H : Type} [Group H] [TopologicalSpace H] [ContinuousMul H]
    (φ : AbsoluteGaloisGroup F ≃ₜ* H) (M : Type) [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction H M] [ContinuousSMul H M]
    [IsAddCyclic M] (hM : Nat.card M = n) (htriv : ∀ (h : H) (m : M), h • m = m) :
    Finite (H2 H M) := by
  have := hζ.neZero'
  have := finite_continuousCohomology_muNRep_two (NeZero.ne (n : F)).isUnit
  have : Finite (H2 (AbsoluteGaloisGroup F) (KummerCoeff F n)) :=
    Finite.of_equiv _ (muNRepH2Equiv n F).symm.toEquiv
  have hcard : Nat.card (KummerCoeff F n) = Nat.card M :=
    (Nat.card_congr Additive.toMul).trans
      (((hζ.map_of_injective (algebraMap F (SeparableClosure F)).injective).card_rootsOfUnity).trans
        hM.symm)
  exact Finite.of_equiv _ (explicitMap2Equiv H M (AbsoluteGaloisGroup F) (KummerCoeff F n) φ
    (addEquivOfAddCyclicCardEq hcard.symm) continuous_of_discreteTopology
    continuous_of_discreteTopology fun g m ↦ by
      rw [htriv, smul_kummerCoeff_eq_self hζ]).symm.toEquiv

/-- Cohomology in degrees zero through two of a finite smooth discrete Galois module over a
nonarchimedean local field is finite, provided its exponent is invertible in the field. -/
theorem finite_H (hn : (n : F) ≠ 0) (A : GalRep n F)
    (hA : IsSmoothDiscrete (ZMod n) A) [Finite A.V] {i : ℕ} (hi : i ≤ 2) :
    Finite (continuousCohomology i A) := by
  by_cases hi1 : i ≤ 1
  · exact finite_continuousCohomology_of_le_one hn A hA hi1
  obtain rfl : i = 2 := by omega
  have := hA.discreteTopology
  have := hA.continuousSMul
  suffices Finite (continuousCohomology 2 (ofDiscreteModule ℤ (Field.absoluteGaloisGroup F) A.V))
    from Finite.of_equiv _ (ofDiscreteModuleRestrictScalarsIntEquiv A 2).toEquiv
  have : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  -- Choose a finite Galois extension trivializing the action and containing the roots of unity.
  set e := absoluteGaloisGroupRestrictEquiv F
  obtain ⟨W, ⟨ζ, hζ⟩, hW⟩ := exists_classField_trivializing hn A hA
  let L := classField F W
  let := finiteExtensionValuativeRel F L
  let := finiteExtensionNormedFieldTopology F L
  have := finiteExtension_isNonarchimedeanLocalField F L
  set U := (galoisSubgroup F L L.val).toSubgroup
  have hUW : U = W.toSubgroup := (galoisSubgroup_toSubgroup F L L.val).trans <| by
    rw [IntermediateField.fieldRange_val]
    exact fixingSubgroup_classField W
  set V := U.map (e.symm : AbsoluteGaloisGroup F →* Field.absoluteGaloisGroup F)
  have : V.Normal := (hUW ▸ W.isNormal' : U.Normal).map _ e.symm.surjective
  let ψ : U ≃ₜ* V :=
    { e.symm.toMulEquiv.subgroupMap U with
      continuous_toFun := continuous_induced_rng.2 (e.symm.continuous.comp continuous_subtype_val)
      continuous_invFun := continuous_induced_rng.2 (e.continuous.comp continuous_subtype_val) }
  -- Transport its absolute Galois group to the corresponding open normal subgroup of G_F.
  have hV : IsOpen (V : Set (Field.absoluteGaloisGroup F)) :=
    e.symm.isOpenMap _ (galoisSubgroup F L L.val).isOpen
  have : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  refine finite_continuousCohomology_of_isOpen_of_normal_of_prime (V := V)
    hV 2 (N := n) ?_ A.V (fun a ↦ ?_)
    fun v hv a ↦ ?_
  -- Coinduction reduces to trivial prime-order modules on this subgroup in degrees one and two.
  · intro j hj₀ hj M _ _ _ _ _ _ hM hMn hMtriv
    have := isAddCyclic_of_prime_card rfl (hp := ⟨hM⟩)
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
    · have := finite_H1_of_isPrimitiveRoot_of_natCard_dvd L hζ
        ((galoisSubgroupEquiv F L L.val).trans ψ) M hMn hMtriv
      exact Finite.of_equiv _ (explicitH1AddEquivContinuousCohomology V M).toEquiv
    · have : NeZero (Nat.card M) := ⟨hM.ne_zero⟩
      -- A primitive n-th root supplies a primitive root of every order dividing n.
      have hζM : IsPrimitiveRoot (ζ ^ (n / Nat.card M)) (Nat.card M) := by
        have h := hζ.pow_of_dvd
          (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hMn) (NeZero.pos _)).ne'
          (Nat.div_dvd_of_dvd hMn)
        rwa [Nat.div_div_self hMn (NeZero.ne n)] at h
      have := finite_H2_of_isPrimitiveRoot_of_natCard_eq hζM
        ((galoisSubgroupEquiv F L L.val).trans ψ) M rfl hMtriv
      exact Finite.of_equiv _ (explicitH2AddEquivContinuousCohomology V M).toEquiv
  · rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hv
    exact hW u (hUW ▸ hu : u ∈ W.toSubgroup) a

end TauCeti.ClassFieldTheory
