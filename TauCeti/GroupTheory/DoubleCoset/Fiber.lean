/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Orbits

/-!
# Fibres of maps between orbit spaces

If `H` has finite index in `K`, every fibre of the map from `H`-orbits to `K`-orbits
is finite. The cosets of `H` in `K` cover each fibre by translating a representative of
the larger orbit. This applies even when the ambient action has nontrivial stabilizers.

When the stabilizer of the representative acts trivially on the coset space, distinct
cosets give distinct `H`-orbits. The resulting equivalence counts the fibre by the
subgroup index, with no finite-index assumption. For an infinite index, both `Nat.card`
and the index are zero.
-/

public noncomputable section

open MulAction

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X]

/-- A coset determines a point in the fibre over the orbit of `x`. -/
noncomputable def cosetToOrbitRelMapFiber {H K : Subgroup G} (h : H ≤ K) (x : X) :
    K ⧸ H.subgroupOf K →
      {q : orbitRel.Quotient H X //
        Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) h) q =
          Quotient.mk'' x} :=
  fun c => ⟨orbitOfCosetTranslate (𝒢 := H) (ℋ := K) x c, by
    induction c using QuotientGroup.induction_on with
    | H k =>
      simp only [orbitOfCosetTranslate_mk, TauCeti.Setoid.map_of_le_mk]
      exact Quotient.sound (orbitRel_apply.mpr (mem_orbit _ k⁻¹))⟩

/-- The coset-to-fibre map sends a coset to the orbit of its inverse translate. -/
@[simp]
theorem cosetToOrbitRelMapFiber_apply {H K : Subgroup G} (h : H ≤ K) (x : X)
    (q : K ⧸ H.subgroupOf K) :
    (cosetToOrbitRelMapFiber h x q).1 = orbitOfCosetTranslate x q :=
  (rfl)

/-- Every orbit in the fibre is represented by a coset. -/
theorem cosetToOrbitRelMapFiber_surjective {H K : Subgroup G} (h : H ≤ K) (x : X) :
    Function.Surjective (cosetToOrbitRelMapFiber h x) := by
  intro q
  let y : X := q.1.out
  have hy : (Quotient.mk'' y : orbitRel.Quotient K X) = Quotient.mk'' x := by
    calc
      _ = Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) h)
          (Quotient.mk'' y : orbitRel.Quotient H X) :=
        (TauCeti.Setoid.map_of_le_mk _ y).symm
      _ = Quotient.mk'' x :=
        (congrArg (Setoid.map_of_le
          (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) h))
          (Quotient.out_eq q.1)).trans q.2
  rw [Quotient.eq'', orbitRel_apply, mem_orbit_iff] at hy
  obtain ⟨k, hk⟩ := hy
  refine ⟨((k⁻¹ : K) : K ⧸ H.subgroupOf K), Subtype.ext ?_⟩
  simp only [cosetToOrbitRelMapFiber_apply, orbitOfCosetTranslate_mk]
  have heq := congrArg (fun z : X =>
    (Quotient.mk'' z : orbitRel.Quotient H X)) hk
  have heq' : (Quotient.mk'' ((k : G) • x) : orbitRel.Quotient H X) =
      Quotient.mk'' y := by simpa [Subgroup.smul_def] using heq
  simpa only [Subgroup.coe_inv, inv_inv] using heq'.trans (Quotient.out_eq q.1)

/-- Every fibre of the orbit map for a finite-index subgroup inclusion is finite. -/
theorem finite_fiber_orbitRel_map_of_isFiniteRelIndex {H K : Subgroup G}
    (h : H ≤ K) [H.IsFiniteRelIndex K] (p : orbitRel.Quotient K X) :
    Finite {q : orbitRel.Quotient H X //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) h) q = p} := by
  induction p using Quotient.inductionOn' with
  | h x =>
    have : (H.subgroupOf K).FiniteIndex := inferInstance
    have : Finite (K ⧸ H.subgroupOf K) := inferInstance
    exact Finite.of_surjective (cosetToOrbitRelMapFiber h x)
      (cosetToOrbitRelMapFiber_surjective h x)

/-- If the stabilizer acts trivially on the coset space, the fibre of an orbit map is
indexed exactly by the cosets of the smaller subgroup in the larger one. -/
noncomputable def cosetsEquivOrbitRelMapFiber {H K : Subgroup G} (h : H ≤ K)
    (x : X) (hx : stabilizer K x ≤ (H.subgroupOf K).normalCore) :
    (K ⧸ H.subgroupOf K) ≃
      {q : orbitRel.Quotient H X //
        Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) h) q =
          Quotient.mk'' x} := by
  refine Equiv.ofBijective (cosetToOrbitRelMapFiber h x) ⟨?_,
    cosetToOrbitRelMapFiber_surjective h x⟩
  · intro a b hab
    have heq : orbitOfCosetTranslate (𝒢 := H) (ℋ := K) x a =
        orbitOfCosetTranslate (𝒢 := H) (ℋ := K) x b := congrArg Subtype.val hab
    obtain ⟨s, hs⟩ := (orbitOfCosetTranslate_eq_iff h x a b).mp heq
    have hsfix : (s : K) • b = b := by
      have hker : (s : K) ∈ (MulAction.toPermHom K (K ⧸ H.subgroupOf K)).ker := by
        rw [← Subgroup.normalCore_eq_ker]
        exact hx s.2
      rw [MonoidHom.mem_ker, MulAction.toPermHom_apply] at hker
      exact congrArg (fun e : Equiv.Perm (K ⧸ H.subgroupOf K) => e b) hker
    exact hs.symm.trans hsfix

/-- A coset maps to the smaller-subgroup orbit of the inverse translate. -/
@[simp]
theorem cosetsEquivOrbitRelMapFiber_apply {H K : Subgroup G} (h : H ≤ K)
    (x : X) (hx : stabilizer K x ≤ (H.subgroupOf K).normalCore)
    (q : K ⧸ H.subgroupOf K) :
    (cosetsEquivOrbitRelMapFiber h x hx q).1 = orbitOfCosetTranslate x q :=
  (rfl)

/-- The fibre cardinality equals the subgroup index when the stabilizer acts trivially
on the coset space. -/
theorem card_fiber_orbitRel_map_of_stabilizer_le_normalCore {H K : Subgroup G} (h : H ≤ K)
    (x : X) (hx : stabilizer K x ≤ (H.subgroupOf K).normalCore) :
    Nat.card {q : orbitRel.Quotient H X //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) h) q =
        Quotient.mk'' x} = (H.subgroupOf K).index := by
  rw [← Nat.card_congr (cosetsEquivOrbitRelMapFiber h x hx)]
  exact (H.subgroupOf K).index_eq_card.symm

end TauCeti
