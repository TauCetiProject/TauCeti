/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel

/-!
# Distinctness and trivial intersection of root subgroups of a Chevalley datum

For any `TauCeti.DynkinType.ChevalleyDatum`, we prove pointwise root-subgroup separation:
`inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot` over every commutative ring, and
`rootSubgroupPoints_ofAdd_one_mem_range_iff`, `exists_rootSubgroupPoints_eq_ofAdd_one_iff`,
`range_rootSubgroupPoints_le_iff`, `range_rootSubgroupPoints_injective`, and
`range_rootSubgroupPoints_inj` over every nontrivial commutative ring. Injectivity of individual
root subgroups `D.rootSubgroupPoints γ A` over every commutative ring is proved in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.ClosedImmersion`
(`ChevalleyDatum.rootSubgroupPoints_injective`).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Ch. 3, Lemmas 17–19; *Endomorphisms of linear
  algebraic groups*, Mem. Amer. Math. Soc. **80** (1968), §§10–11.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum
open Multiplicative
universe v
variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Trivial intersection of opposite root subgroups and distinctness -/

/-- **Opposite root subgroups intersect trivially over every commutative ring.** -/
@[simp] theorem inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot (A : Type v) [CommRing A]
    (γ : Fin t.numRoots) : (D.rootSubgroupPoints γ A).range ⊓
      (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) A).range = ⊥ := by
  let P := t.simplyConnectedRootDatum ht
  have hpos {δ} (hd : δ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) {g : D.points A}
      (hg : g ∈ (D.rootSubgroupPoints δ A).range)
      (hg' : g ∈ (D.rootSubgroupPoints (P.reflectionPerm δ δ) A).range) : g = 1 := by
    obtain ⟨u, rfl⟩ := hg; obtain ⟨v, hv⟩ := hg'
    exact hv ▸ (D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A
      (by rw [← t.reflectionPerm_rationalRootSystem ht]
          exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ _ _).mpr hd) v).mp
      (hv ▸ D.positivePoints_le_borelSubgroup A (D.rootSubgroupPoints_mem_positivePoints A hd u))
  rw [Subgroup.eq_bot_iff_forall]; rintro g ⟨hg, hg'⟩
  rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht) γ with h | h
  · exact hpos h hg hg'
  · refine hpos (by rw [← t.reflectionPerm_rationalRootSystem ht,
      reflectionPerm_self_mem_posRoots_iff_mem_negRoots]; exact h) hg'
      (by have := reflectionPerm_self_involutive P γ; dsimp [P] at this; rwa [this])

private theorem eq_of_rootSubgroupPoints_ofAdd_one_mem_range (K : Type v) [Field K] [Infinite K]
    {α β : Fin t.numRoots}
    (hmem : D.rootSubgroupPoints α K (ofAdd 1) ∈ (D.rootSubgroupPoints β K).range) : α = β := by
  obtain ⟨b, hb⟩ := hmem
  have hb0 : toAdd b ≠ 0 := fun h0 => D.rootSubgroupPoints_ofAdd_one_ne_one K α
    (by rw [← hb, toAdd.injective (h0.trans toAdd_one.symm), map_one])
  obtain ⟨d, hd, z, hz⟩ := exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp
    (ξ := D.coordinateRoot α) (η := D.coordinateRoot β) fun s hs => by
      have hconj := congrArg (fun g => D.torusPoints K s * g * (D.torusPoints K s)⁻¹) hb
      rw [← ofAdd_toAdd b, D.torusPoints_conj_rootSubgroupPoints,
        D.torusPoints_conj_rootSubgroupPoints, hs, Units.val_one, one_mul, ← hb] at hconj
      exact Units.ext (mul_right_cancel₀ hb0
        (by simpa using congrArg toAdd (D.rootSubgroupPoints_injective β K hconj)))
  rcases D.eq_or_eq_reflectionPerm_of_zsmul_coordinateRoot_eq (b := z)
      (Int.natCast_ne_zero.mpr hd.ne') (by simpa only [natCast_zsmul] using hz) with rfl | rfl
  · rfl
  · exact (D.rootSubgroupPoints_ofAdd_one_ne_one K α (Subgroup.mem_bot.mp
      ((D.inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot K α).symm ▸
        ⟨⟨ofAdd 1, rfl⟩, ⟨b, hb⟩⟩))).elim

/-- **Over any nontrivial commutative ring, `x_α(1)` belongs to the `β`-root subgroup iff
`α = β`.** -/
-- Not @[simp]: the LHS simplifies via `MonoidHom.mem_range` and `Multiplicative.exists`.
theorem rootSubgroupPoints_ofAdd_one_mem_range_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    D.rootSubgroupPoints α A (ofAdd 1) ∈ (D.rootSubgroupPoints β A).range ↔ α = β :=
  ⟨fun ⟨b, hb⟩ => by
    obtain ⟨𝔪, _⟩ := Ideal.exists_maximal A
    let _ : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪; let K := AlgebraicClosure (A ⧸ 𝔪)
    have hmap := congrArg ((D.pointsPresentation A).map (D.pointsPresentation K)
      ((algebraMap (A ⧸ 𝔪) K).comp (Ideal.Quotient.mk 𝔪))) hb
    rw [D.map_rootSubgroupPoints, D.map_rootSubgroupPoints, toAdd_ofAdd, map_one] at hmap
    exact D.eq_of_rootSubgroupPoints_ofAdd_one_mem_range K ⟨_, hmap⟩,
   fun h => h ▸ ⟨ofAdd 1, rfl⟩⟩

/-- **Over any nontrivial commutative ring, `x_α(1)` lies in the image of `x_β` iff `α = β`
(normal form after `simp` expands `MonoidHom.mem_range`).** -/
@[simp] theorem exists_rootSubgroupPoints_eq_ofAdd_one_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (∃ a : A, D.rootSubgroupPoints β A (ofAdd a) = D.rootSubgroupPoints α A (ofAdd 1)) ↔
      α = β := by
  simpa only [MonoidHom.mem_range, Multiplicative.exists] using
    D.rootSubgroupPoints_ofAdd_one_mem_range_iff A (α := α) (β := β)

/-- **Over any nontrivial commutative ring, one root subgroup is contained in another only at the
same root.** -/
@[simp] theorem range_rootSubgroupPoints_le_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (D.rootSubgroupPoints α A).range ≤ (D.rootSubgroupPoints β A).range ↔ α = β :=
  ⟨fun hle => (D.rootSubgroupPoints_ofAdd_one_mem_range_iff A).mp (hle ⟨ofAdd 1, rfl⟩),
   fun h => h ▸ le_rfl⟩

/-- **Over any nontrivial commutative ring, distinct root indices give distinct root subgroups.** -/
theorem range_rootSubgroupPoints_injective (A : Type v) [CommRing A] [Nontrivial A] :
    Function.Injective fun α : Fin t.numRoots => (D.rootSubgroupPoints α A).range :=
  fun _ _ h => (D.range_rootSubgroupPoints_le_iff A).mp h.le

/-- Over any nontrivial commutative ring, two root subgroups coincide iff they share a root. -/
@[simp] theorem range_rootSubgroupPoints_inj (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (D.rootSubgroupPoints α A).range = (D.rootSubgroupPoints β A).range ↔ α = β :=
  (D.range_rootSubgroupPoints_injective A).eq_iff

end TauCeti.DynkinType.ChevalleyDatum
