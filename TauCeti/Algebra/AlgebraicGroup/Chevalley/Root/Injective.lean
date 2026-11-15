/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.FieldTheory.IsAlgClosed.Units
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.FieldEndomorphism

/-!
# Injectivity and distinctness of root subgroups of a Chevalley datum

For the simply connected datum `TauCeti.DynkinType.scChevalleyDatum`, every root subgroup is a
closed immersion over `ℤ` (`TauCeti.DynkinType.ChevalleyDatum.isClosedImmersion_rootSubgroup`), so
its additive parameter is faithful over arbitrary commutative rings. For a general
`TauCeti.DynkinType.ChevalleyDatum`, closed immersion over nonreduced rings need not hold: in the
three-dimensional symmetric-square lattice of `SL₂` (adjoint type `A₁`), the divided-power
exponential in characteristic two sends `u` to a matrix whose off-diagonal entries are multiples of
`u²`, killing square-zero nilpotents.

Over any *integral domain* `A`, however, `D.rootSubgroupPoints γ A` is injective for every
Chevalley datum `D` (`TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_injective`). Over a field
`K` with divisible units, a nonzero element in the kernel of `x_γ` can be rescaled to `1` by
conjugating with the actual torus `D.torusPoints K` because `D.coordinateRoot γ ≠ 0`, contradicting
`D.rootSubgroupPoints_ofAdd_one_ne_one`. Scalar extension along
`A →+* FractionRing A →+* AlgebraicClosure (FractionRing A)` transfers injectivity to every domain.

Combining injectivity over an algebraically closed residue field with the pinning equation,
reducedness of the root datum, and trivial intersection of negative root subgroups with
`D.borelSubgroup` shows further that over *every nontrivial commutative ring* `A`, no root subgroup
is contained in a distinct root subgroup
(`TauCeti.DynkinType.ChevalleyDatum.range_rootSubgroupPoints_le_iff`).

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.weightLatticeEmbedding_coordinateRoot`,
  `TauCeti.DynkinType.ChevalleyDatum.coordinateRoot_injective`, and
  `TauCeti.DynkinType.ChevalleyDatum.coordinateRoot_ne_zero`: basic faithfulness of
  `D.coordinateRoot` in the chosen character-lattice basis.
* `TauCeti.DynkinType.ChevalleyDatum.eq_of_nsmul_coordinateRoot_eq`: positive integer multiples of
  coordinate roots agree only at equal root indices.
* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_injective`: `D.rootSubgroupPoints γ A` is
  injective over every integral domain `A`.
* `TauCeti.DynkinType.ChevalleyDatum.inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot`:
  opposite root subgroups intersect trivially over every commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.range_rootSubgroupPoints_le_iff` and
  `TauCeti.DynkinType.ChevalleyDatum.range_rootSubgroupPoints_injective`: over any nontrivial
  commutative ring, distinct root indices have distinct root-subgroup images.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 17–19.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §10–11.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open Multiplicative

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Coordinate roots in the character lattice -/

/-- Embedding `D.coordinateRoot γ` from the chosen basis of `Λ(D)` into the full weight lattice
recovers the root of `t.simplyConnectedRootDatum ht`. -/
@[simp]
theorem weightLatticeEmbedding_coordinateRoot (γ : Fin t.numRoots) :
    D.weightLatticeEmbedding (D.coordinateRoot γ) = (t.simplyConnectedRootDatum ht).root γ := by
  rw [coordinateRoot_def, weightLatticeEmbedding_repr]

/-- Distinct root indices have distinct coordinate roots in `Λ(D)`. -/
theorem coordinateRoot_injective : Function.Injective D.coordinateRoot := by
  intro α β h
  apply (t.simplyConnectedRootDatum ht).root.injective
  simpa only [D.weightLatticeEmbedding_coordinateRoot] using
    congrArg D.weightLatticeEmbedding h

/-- Every coordinate root of a Chevalley datum is nonzero. -/
@[simp]
theorem coordinateRoot_ne_zero (γ : Fin t.numRoots) : D.coordinateRoot γ ≠ 0 := by
  intro h
  apply (t.simplyConnectedRootDatum ht).ne_zero γ
  simpa only [D.weightLatticeEmbedding_coordinateRoot, map_zero] using
    congrArg D.weightLatticeEmbedding h

/-- **Positive integer multiples of coordinate roots determine the root index.** Since the pinned
root datum is reduced and no root is zero, `m • D.coordinateRoot α = d • D.coordinateRoot β` with
`0 < m` forces `α = β` without any positivity hypothesis on `d`. -/
theorem eq_of_nsmul_coordinateRoot_eq {α β : Fin t.numRoots} {m d : ℕ}
    (hm : 0 < m) (h : m • D.coordinateRoot α = d • D.coordinateRoot β) :
    α = β := by
  let P := t.simplyConnectedRootDatum ht
  have : P.IsReduced := t.isReduced_simplyConnectedRootDatum ht
  have hroot : (m : ℤ) • P.root α = (d : ℤ) • P.root β := by
    simpa only [map_nsmul, D.weightLatticeEmbedding_coordinateRoot, natCast_zsmul] using
      congrArg D.weightLatticeEmbedding h
  have hdep : ¬ LinearIndependent ℤ ![P.root α, P.root β] := by
    rw [LinearIndependent.pair_iff]
    intro hli
    have hm0 : (m : ℤ) = 0 :=
      (hli m (-d) (by rw [neg_smul, hroot, add_neg_cancel])).1
    exact hm.ne' (Int.ofNat.inj hm0)
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) α β hdep with heq | hneg
  · exact P.root.injective heq
  · exfalso
    have hsum : ((m + d : ℕ) : ℤ) • P.root β = 0 := by
      rw [Nat.cast_add, add_smul, ← hroot, hneg, smul_neg, add_neg_cancel]
    have hpos : ((m + d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.add_pos_left hm d).ne'
    exact P.ne_zero β ((smul_eq_zero.mp hsum).resolve_left hpos)

/-! ## Injectivity of root subgroups -/

/-- Over a field whose unit group is divisible, every root subgroup of `D` is injective: any
nonzero element of the kernel can be conjugated to `x_γ(1)` by a point of `D.torusPoints K`. -/
private theorem rootSubgroupPoints_injective_of_rootableBy (K : Type v) [Field K]
    [RootableBy Kˣ ℕ] (γ : Fin t.numRoots) : Function.Injective (D.rootSubgroupPoints γ K) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  by_contra hu1
  have ha : toAdd u ≠ 0 := fun h0 => hu1 (toAdd.injective h0)
  obtain ⟨s, hs⟩ :=
    torusCharacter_surjective (D.coordinateRoot_ne_zero γ) (Units.mk0 (toAdd u) ha)⁻¹
  dsimp only at hs
  have hconj := D.torusPoints_conj_rootSubgroupPoints γ K s (toAdd u)
  rw [ofAdd_toAdd, hu, mul_one, mul_inv_cancel, hs, Units.val_inv_eq_inv_val, Units.val_mk0,
    inv_mul_cancel₀ ha] at hconj
  exact D.rootSubgroupPoints_ofAdd_one_ne_one K γ hconj.symm

/-- **Every root subgroup of a Chevalley datum is injective over an integral domain.**
This embeds `A` into an algebraic closure of its fraction field and transfers faithfulness via
`D.map_rootSubgroupPoints`. -/
theorem rootSubgroupPoints_injective (A : Type v) [CommRing A] [IsDomain A]
    (γ : Fin t.numRoots) : Function.Injective (D.rootSubgroupPoints γ A) := by
  let F := FractionRing A
  let K := AlgebraicClosure F
  let φ : A →+* K := (algebraMap F K).comp (algebraMap A F)
  have hφ : Function.Injective φ :=
    (RingHom.injective (algebraMap F K)).comp (IsFractionRing.injective A F)
  intro u₁ u₂ h
  have hmap := congrArg ((D.pointsPresentation A).map (D.pointsPresentation K) φ) h
  rw [D.map_rootSubgroupPoints, D.map_rootSubgroupPoints] at hmap
  have heq := D.rootSubgroupPoints_injective_of_rootableBy K γ hmap
  exact toAdd.injective (hφ (toAdd_ofAdd _ ▸ toAdd_ofAdd _ ▸ congrArg toAdd heq))

@[simp]
theorem rootSubgroupPoints_eq_one_iff (A : Type v) [CommRing A] [IsDomain A]
    (γ : Fin t.numRoots) (u : Multiplicative A) :
    D.rootSubgroupPoints γ A u = 1 ↔ u = 1 :=
  map_eq_one_iff (D.rootSubgroupPoints γ A) (D.rootSubgroupPoints_injective A γ)

/-! ## Trivial intersection of opposite root subgroups and distinctness -/

/-- **Opposite root subgroups intersect trivially over every commutative ring.** One of the two
roots is positive and the other is negative, and negative root elements in `D.borelSubgroup A` are
trivial. -/
theorem inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot (A : Type v) [CommRing A]
    (γ : Fin t.numRoots) :
    (D.rootSubgroupPoints γ A).range ⊓
      (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) A).range = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro g ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
  rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht) γ with
    hpos | hneg
  · have hneg' : (t.simplyConnectedRootDatum ht).reflectionPerm γ γ ∈
        negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [← t.reflectionPerm_rationalRootSystem ht]
      exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ _ _).mpr hpos
    have hmem : D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) A v ∈
        D.borelSubgroup A := by
      rw [hv]
      exact D.positivePoints_le_borelSubgroup A (D.rootSubgroupPoints_mem_positivePoints A hpos u)
    rw [← hv]
    exact (D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A hneg' v).mp hmem
  · have hpos' : (t.simplyConnectedRootDatum ht).reflectionPerm γ γ ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [← t.reflectionPerm_rationalRootSystem ht,
        ← reflectionPerm_self_mem_negRoots_iff_mem_posRoots]
      have hinv : (t.rationalRootSystem ht).reflectionPerm
          ((t.rationalRootSystem ht).reflectionPerm γ γ)
          ((t.rationalRootSystem ht).reflectionPerm γ γ) = γ :=
        reflectionPerm_self_involutive _ γ
      rwa [hinv]
    have hmem : D.rootSubgroupPoints γ A u ∈ D.borelSubgroup A := by
      rw [← hv]
      exact D.positivePoints_le_borelSubgroup A (D.rootSubgroupPoints_mem_positivePoints A hpos' v)
    exact (D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A hneg u).mp hmem

/-- Over an infinite field, `x_α(1)` lies in the `β`-root subgroup only when `α = β`. -/
private theorem eq_of_rootSubgroupPoints_ofAdd_one_mem_range (K : Type v) [Field K] [Infinite K]
    {α β : Fin t.numRoots}
    (hmem : D.rootSubgroupPoints α K (ofAdd 1) ∈ (D.rootSubgroupPoints β K).range) :
    α = β := by
  obtain ⟨b, hb⟩ := hmem
  have hb0 : toAdd b ≠ 0 := by
    intro h0
    have hb1 : b = 1 := toAdd.injective h0
    rw [hb1, map_one] at hb
    exact D.rootSubgroupPoints_ofAdd_one_ne_one K α hb.symm
  have hker : ∀ s : Fin t.rank → Kˣ,
      torusCharacter s (D.coordinateRoot α) = 1 →
        torusCharacter s (D.coordinateRoot β) = 1 := by
    intro s hs
    have hconj := congrArg (fun g => D.torusPoints K s * g * (D.torusPoints K s)⁻¹) hb
    rw [← ofAdd_toAdd b, D.torusPoints_conj_rootSubgroupPoints,
      D.torusPoints_conj_rootSubgroupPoints, hs, Units.val_one, one_mul, ← hb] at hconj
    have hval : (torusCharacter s (D.coordinateRoot β) : K) * toAdd b = 1 * toAdd b := by
      simpa only [one_mul, toAdd_ofAdd] using
        congrArg toAdd (D.rootSubgroupPoints_injective K β hconj)
    exact Units.ext (mul_right_cancel₀ hb0 hval)
  obtain ⟨d, hd, z, hz⟩ := exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp hker
  let P := t.simplyConnectedRootDatum ht
  have : P.IsReduced := t.isReduced_simplyConnectedRootDatum ht
  have hroot : (d : ℤ) • P.root β = z • P.root α := by
    simpa only [map_nsmul, map_zsmul, D.weightLatticeEmbedding_coordinateRoot, natCast_zsmul] using
      congrArg D.weightLatticeEmbedding hz
  have hdep : ¬ LinearIndependent ℤ ![P.root α, P.root β] := by
    rw [LinearIndependent.pair_iff]
    intro hli
    have hd0 : -(d : ℤ) = 0 :=
      (hli z (-(d : ℤ)) (by rw [neg_smul, hroot, add_neg_cancel])).2
    exact hd.ne' (Int.ofNat.inj (neg_eq_zero.mp hd0))
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) α β hdep with heq | hneg
  · exact P.root.injective heq
  · exfalso
    have hβ : β = P.reflectionPerm α α :=
      P.root.injective (by
        rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, hneg, neg_neg])
    subst hβ
    have hbot : D.rootSubgroupPoints α K (ofAdd 1) ∈ (⊥ : Subgroup (D.points K)) := by
      rw [← D.inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot K α]
      exact ⟨⟨ofAdd 1, rfl⟩, ⟨b, hb⟩⟩
    exact D.rootSubgroupPoints_ofAdd_one_ne_one K α (Subgroup.mem_bot.mp hbot)

/-- **Over any nontrivial commutative ring, one root subgroup is contained in another only at the
same root.** Passing to an algebraic closure of a residue field `A ⧸ 𝔪` reduces to the
infinite-field case. -/
@[simp]
theorem range_rootSubgroupPoints_le_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (D.rootSubgroupPoints α A).range ≤ (D.rootSubgroupPoints β A).range ↔ α = β := by
  refine ⟨fun hle => ?_, fun h => h ▸ le_rfl⟩
  obtain ⟨b, hb⟩ := hle ⟨ofAdd 1, rfl⟩
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let K := AlgebraicClosure (A ⧸ 𝔪)
  let φ : A →+* K := (algebraMap (A ⧸ 𝔪) K).comp (Ideal.Quotient.mk 𝔪)
  have hmap := congrArg ((D.pointsPresentation A).map (D.pointsPresentation K) φ) hb
  rw [D.map_rootSubgroupPoints, D.map_rootSubgroupPoints, toAdd_ofAdd, map_one] at hmap
  exact D.eq_of_rootSubgroupPoints_ofAdd_one_mem_range K ⟨_, hmap⟩

/-- **Over any nontrivial commutative ring, distinct root indices give distinct root subgroups.** -/
theorem range_rootSubgroupPoints_injective (A : Type v) [CommRing A] [Nontrivial A] :
    Function.Injective fun α : Fin t.numRoots => (D.rootSubgroupPoints α A).range :=
  fun _ _ h => (D.range_rootSubgroupPoints_le_iff A).mp h.le

@[simp]
theorem range_rootSubgroupPoints_eq_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (D.rootSubgroupPoints α A).range = (D.rootSubgroupPoints β A).range ↔ α = β :=
  (D.range_rootSubgroupPoints_injective A).eq_iff

end TauCeti.DynkinType.ChevalleyDatum
