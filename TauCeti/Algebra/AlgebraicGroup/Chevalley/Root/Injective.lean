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
closed immersion over `ℤ` (`TauCeti.DynkinType.ChevalleyDatum.isClosedImmersion_rootSubgroup`). For
a general `TauCeti.DynkinType.ChevalleyDatum`, closed immersion over nonreduced rings can fail (for
example in the symmetric-square lattice of `SL₂` in characteristic `2`), yet:

* over every *integral domain* `A`, `D.rootSubgroupPoints γ A` is injective
  (`rootSubgroupPoints_injective`), proved over fields with divisible units via torus conjugation
  since `D.coordinateRoot γ ≠ 0`, then transferred along
  `A →+* FractionRing A →+* AlgebraicClosure (FractionRing A)`;
* over *every commutative ring* `A`, opposite root subgroups intersect trivially
  (`inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot`);
* over *every nontrivial commutative ring* `A`, distinct root indices have incomparable and
  distinct root subgroups (`range_rootSubgroupPoints_le_iff`,
  `range_rootSubgroupPoints_injective`), proved by passing to an algebraic closure of a residue
  field `A ⧸ 𝔪`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 17–19.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  §§10–11.
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
theorem coordinateRoot_injective : Function.Injective D.coordinateRoot := fun _ _ h =>
  (t.simplyConnectedRootDatum ht).root.injective
    (by simpa only [D.weightLatticeEmbedding_coordinateRoot] using
      congrArg D.weightLatticeEmbedding h)

/-- Every coordinate root of a Chevalley datum is nonzero. -/
@[simp]
theorem coordinateRoot_ne_zero (γ : Fin t.numRoots) : D.coordinateRoot γ ≠ 0 := fun h =>
  (t.simplyConnectedRootDatum ht).ne_zero γ
    (by simpa only [D.weightLatticeEmbedding_coordinateRoot, map_zero] using
      congrArg D.weightLatticeEmbedding h)

private theorem eq_or_eq_reflectionPerm_of_zsmul_coordinateRoot_eq {α β : Fin t.numRoots}
    {a b : ℤ} (ha : a ≠ 0) (h : a • D.coordinateRoot α = b • D.coordinateRoot β) :
    α = β ∨ α = (t.simplyConnectedRootDatum ht).reflectionPerm β β := by
  let P := t.simplyConnectedRootDatum ht
  have : P.IsReduced := t.isReduced_simplyConnectedRootDatum ht
  have hroot : a • P.root α = b • P.root β := by
    simpa only [map_zsmul, D.weightLatticeEmbedding_coordinateRoot] using
      congrArg D.weightLatticeEmbedding h
  have hdep : ¬ LinearIndependent ℤ ![P.root α, P.root β] := fun hli =>
    ha ((LinearIndependent.pair_iff.mp hli a (-b) (by rw [neg_smul, hroot, add_neg_cancel])).1)
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) α β hdep with heq | hneg
  · exact Or.inl (P.root.injective heq)
  · exact Or.inr (P.root.injective (by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, hneg]))

/-- **Positive integer multiples of coordinate roots determine the root index.** Since the pinned
root datum is reduced and no root is zero, `m • D.coordinateRoot α = d • D.coordinateRoot β` with
`0 < m` forces `α = β` without any positivity hypothesis on `d`. -/
theorem eq_of_nsmul_coordinateRoot_eq {α β : Fin t.numRoots} {m d : ℕ}
    (hm : 0 < m) (h : m • D.coordinateRoot α = d • D.coordinateRoot β) : α = β := by
  have hz : (m : ℤ) • D.coordinateRoot α = (d : ℤ) • D.coordinateRoot β := by
    simpa only [natCast_zsmul] using h
  rcases D.eq_or_eq_reflectionPerm_of_zsmul_coordinateRoot_eq (Int.natCast_ne_zero.mpr hm.ne') hz
    with rfl | rfl
  · rfl
  · rw [D.coordinateRoot_reflectionPerm_self, smul_neg] at h
    have hsum : (m + d) • D.coordinateRoot β = 0 := by rw [add_smul, ← h, add_neg_cancel]
    exact (D.coordinateRoot_ne_zero β
      ((smul_eq_zero.mp hsum).resolve_left (Nat.add_pos_left hm d).ne')).elim

/-! ## Injectivity of root subgroups -/

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

private theorem eq_one_of_mem_posRoots_of_mem_range_reflectionPerm_self {A : Type v} [CommRing A]
    {γ : Fin t.numRoots} (hpos : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {g : D.points A} (hg : g ∈ (D.rootSubgroupPoints γ A).range)
    (hg' : g ∈ (D.rootSubgroupPoints
      ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) A).range) : g = 1 := by
  obtain ⟨u, rfl⟩ := hg; obtain ⟨v, hv⟩ := hg'
  have hneg : (t.simplyConnectedRootDatum ht).reflectionPerm γ γ ∈
      negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [← t.reflectionPerm_rationalRootSystem ht]
    exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ _ _).mpr hpos
  have hB : D.rootSubgroupPoints _ A v ∈ D.borelSubgroup A :=
    hv ▸ D.positivePoints_le_borelSubgroup A (D.rootSubgroupPoints_mem_positivePoints A hpos u)
  exact hv ▸ (D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A hneg v).mp hB

/-- **Opposite root subgroups intersect trivially over every commutative ring.** One of the two
roots is positive and the other is negative, and negative root elements in `D.borelSubgroup A` are
trivial. -/
theorem inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot (A : Type v) [CommRing A]
    (γ : Fin t.numRoots) :
    (D.rootSubgroupPoints γ A).range ⊓
      (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) A).range = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro g ⟨hg, hg'⟩
  rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht) γ with
    hpos | hneg
  · exact D.eq_one_of_mem_posRoots_of_mem_range_reflectionPerm_self hpos hg hg'
  · have hinv₁ : (t.rationalRootSystem ht).reflectionPerm
        ((t.rationalRootSystem ht).reflectionPerm γ γ)
        ((t.rationalRootSystem ht).reflectionPerm γ γ) = γ := reflectionPerm_self_involutive _ γ
    have hinv₂ : (t.simplyConnectedRootDatum ht).reflectionPerm
        ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)
        ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) = γ :=
      reflectionPerm_self_involutive _ γ
    have hpos' : (t.simplyConnectedRootDatum ht).reflectionPerm γ γ ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [← t.reflectionPerm_rationalRootSystem ht,
        ← reflectionPerm_self_mem_negRoots_iff_mem_posRoots]
      rwa [hinv₁]
    exact D.eq_one_of_mem_posRoots_of_mem_range_reflectionPerm_self hpos' hg' (by rwa [hinv₂])

private theorem eq_of_rootSubgroupPoints_ofAdd_one_mem_range (K : Type v) [Field K] [Infinite K]
    {α β : Fin t.numRoots}
    (hmem : D.rootSubgroupPoints α K (ofAdd 1) ∈ (D.rootSubgroupPoints β K).range) : α = β := by
  obtain ⟨b, hb⟩ := hmem
  have hb0 : toAdd b ≠ 0 := fun h0 => by
    have hb1 : b = 1 := toAdd.injective h0; rw [hb1, map_one] at hb
    exact D.rootSubgroupPoints_ofAdd_one_ne_one K α hb.symm
  obtain ⟨d, hd, z, hz⟩ := exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp
    (ξ := D.coordinateRoot α) (η := D.coordinateRoot β) fun s hs => by
      have hconj := congrArg (fun g => D.torusPoints K s * g * (D.torusPoints K s)⁻¹) hb
      rw [← ofAdd_toAdd b, D.torusPoints_conj_rootSubgroupPoints,
        D.torusPoints_conj_rootSubgroupPoints, hs, Units.val_one, one_mul, ← hb] at hconj
      have hval : (torusCharacter s (D.coordinateRoot β) : K) * toAdd b = 1 * toAdd b := by
        simpa only [one_mul, toAdd_ofAdd] using
          congrArg toAdd (D.rootSubgroupPoints_injective K β hconj)
      exact Units.ext (mul_right_cancel₀ hb0 hval)
  have hz' : (d : ℤ) • D.coordinateRoot β = z • D.coordinateRoot α := by
    simpa only [natCast_zsmul] using hz
  rcases D.eq_or_eq_reflectionPerm_of_zsmul_coordinateRoot_eq (Int.natCast_ne_zero.mpr hd.ne') hz'
    with rfl | rfl
  · rfl
  · have hbot : D.rootSubgroupPoints α K (ofAdd 1) ∈ (⊥ : Subgroup (D.points K)) := by
      rw [← D.inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot K α]
      exact ⟨⟨ofAdd 1, rfl⟩, ⟨b, hb⟩⟩
    exact (D.rootSubgroupPoints_ofAdd_one_ne_one K α (Subgroup.mem_bot.mp hbot)).elim

/-- **Over any nontrivial commutative ring, one root subgroup is contained in another only at the
same root.** Passing to an algebraic closure of a residue field `A ⧸ 𝔪` reduces to the
infinite-field case. -/
@[simp]
theorem range_rootSubgroupPoints_le_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (D.rootSubgroupPoints α A).range ≤ (D.rootSubgroupPoints β A).range ↔ α = β := by
  refine ⟨fun hle => ?_, fun h => h ▸ le_rfl⟩
  obtain ⟨b, hb⟩ := hle ⟨ofAdd 1, rfl⟩
  obtain ⟨𝔪, _⟩ := Ideal.exists_maximal A
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
