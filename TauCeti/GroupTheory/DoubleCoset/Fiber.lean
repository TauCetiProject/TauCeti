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
-/

public noncomputable section

open MulAction

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X]

/-- Every fibre of the orbit map for a finite-index subgroup inclusion is finite. -/
theorem finite_fiber_orbitRel_map_of_isFiniteRelIndex {H K : Subgroup G}
    (h : H ≤ K) [H.IsFiniteRelIndex K] (p : orbitRel.Quotient K X) :
    Finite {q : orbitRel.Quotient H X //
      Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) h) q = p} := by
  induction p using Quotient.inductionOn' with
  | h x =>
    let f : K ⧸ H.subgroupOf K →
        {q : orbitRel.Quotient H X //
          Setoid.map_of_le (TauCeti.MulAction.orbitRel_le_of_subgroup_le (X := X) h) q =
            Quotient.mk'' x} :=
      fun c => ⟨orbitOfCosetTranslate (𝒢 := H) (ℋ := K) x c, by
        induction c using QuotientGroup.induction_on with
        | H k =>
          simp only [orbitOfCosetTranslate_mk, TauCeti.Setoid.map_of_le_mk]
          exact Quotient.sound (orbitRel_apply.mpr (mem_orbit _ k⁻¹))⟩
    have : (H.subgroupOf K).FiniteIndex := inferInstance
    have : Finite (K ⧸ H.subgroupOf K) := inferInstance
    apply Finite.of_surjective f
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
    simp only [f, orbitOfCosetTranslate_mk]
    have heq := congrArg (fun z : X =>
      (Quotient.mk'' z : orbitRel.Quotient H X)) hk
    have heq' : (Quotient.mk'' ((k : G) • x) : orbitRel.Quotient H X) =
        Quotient.mk'' y := by simpa [Subgroup.smul_def] using heq
    simpa only [Subgroup.coe_inv, inv_inv] using heq'.trans (Quotient.out_eq q.1)

end TauCeti
