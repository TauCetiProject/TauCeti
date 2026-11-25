/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.BaseChange
public import TauCeti.RepresentationTheory.OfMulAction.BaseChange
public import Mathlib.Data.ZMod.Basic

/-!
# Examples of change of coefficients

Base change of a smooth representation is smooth; over a field, extension of scalars along a
field extension commutes with the invariants of a finite group. Flat change of coefficients
commutes with the invariants of a compact subgroup `U` of a smooth representation. Arbitrary
change of coefficients commutes with the invariants of `U` on the permutation representation
`A[G/U']`, both sides being free on the finite `U`-orbits of `G/U'`; this needs neither `U` compact
nor `U'` open. For the sign
representation of `ℤˣ ≅ ℤ/2` on `ℤ` and `B = ℤ/2`, the comparison map `B ⊗ V^U → (B ⊗ V)^U` is
the map `0 → ℤ/2`, which is not surjective.
-/

public section

open Representation TensorProduct

namespace TauCeti

/-- The base change of a smooth representation is smooth. -/
example {A B G V : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [AddCommMonoid V] [Module A V]
    (ρ : Representation A G V) [IsSmooth ρ] : IsSmooth (baseChange B ρ) :=
  inferInstance

/-- For a finite group and a field extension `K → L`, `L ⊗ V^G → (L ⊗ V)^G` is bijective. -/
example {K L G V : Type*} [Field K] [Field L] [Algebra K L] [Group G] [Finite G]
    [AddCommGroup V] [Module K V] (ρ : Representation K G V) :
    Function.Bijective (ρ.invariantsBaseChangeMap (A := L)) :=
  ρ.invariantsBaseChangeMap_bijective

/-- For `B` flat over `A`, a compact subgroup `U` and a smooth representation `V`,
`B ⊗ V^U → (B ⊗ V)^U` is bijective. -/
example {A B G V : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] [Group G]
    [TopologicalSpace G] [SeparatelyContinuousMul G] [AddCommGroup V] [Module A V]
    (ρ : Representation A G V) [IsSmooth ρ] {U : Subgroup G} (hU : IsCompact (U : Set G)) :
    Function.Bijective (invariantsBaseChangeMap (A := B) (ρ.comp U.subtype)) :=
  invariantsBaseChangeMap_comp_subtype_bijective_of_isCompact hU

/-- For subgroups `U` and `U'` (for instance `U` compact open and `U'` open) and any commutative
`A`-algebra `B`, flat or not, `B ⊗ A[G/U']^U → (B ⊗ A[G/U'])^U` is bijective, both sides being free
on the finite `U`-orbits of `G/U'`. -/
example {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G] (U U' : Subgroup G) :
    Function.Bijective
      (invariantsBaseChangeMap (A := B) ((ofMulAction A G (G ⧸ U')).comp U.subtype)) := by
  rw [ofMulAction_comp_subtype]
  exact invariantsBaseChangeMap_ofMulAction_bijective

/-- In particular reduction modulo `2`, which is not flat over `ℤ`, commutes with the invariants of
`ℤ[G/U']` under a subgroup `U`. -/
example {G : Type*} [Group G] (U U' : Subgroup G) :
    Function.Bijective
      (invariantsBaseChangeMap (A := ZMod 2) ((ofMulAction ℤ G (G ⧸ U')).comp U.subtype)) := by
  rw [ofMulAction_comp_subtype]
  exact invariantsBaseChangeMap_ofMulAction_bijective

/-- The sign representation of `ℤˣ` on `ℤ`. -/
noncomputable abbrev signRepresentation : Representation ℤ ℤˣ ℤ :=
  ofDistribMulAction ℤ ℤˣ ℤ

/-- **Base change need not commute with invariants.** For the sign representation of `ℤˣ` on `ℤ`
and `B = ℤ/2`, the comparison map `B ⊗ V^U → (B ⊗ V)^U` is not surjective: its source is zero,
while `1 ⊗ 1` is a nonzero invariant of the target. -/
theorem signRepresentation_invariantsBaseChangeMap_not_surjective :
    ¬Function.Surjective (signRepresentation.invariantsBaseChangeMap (A := ZMod 2)) := by
  intro h
  have h0 (v : signRepresentation.invariants) : v = 0 := by
    have hv := (mem_invariants _ _).1 v.property (-1)
    refine Subtype.ext ?_
    simp only [ofDistribMulAction_apply_apply, Units.smul_def, Units.val_neg, Units.val_one,
      neg_smul, one_smul] at hv
    simp only [ZeroMemClass.coe_zero]
    omega
  have : Subsingleton signRepresentation.invariants := ⟨fun a b ↦ (h0 a).trans (h0 b).symm⟩
  have hmem :
      (1 : ZMod 2) ⊗ₜ[ℤ] (1 : ℤ) ∈ (baseChange (ZMod 2) signRepresentation).invariants := by
    refine (mem_invariants _ _).2 fun g ↦ ?_
    rw [baseChange_apply, LinearMap.baseChange_tmul, ofDistribMulAction_apply_apply]
    rcases Int.units_eq_one_or g with rfl | rfl
    · simp
    · simp [tmul_neg, ← neg_tmul, CharTwo.neg_eq]
  obtain ⟨y, hy⟩ := h ⟨_, hmem⟩
  have h1 := congrArg Subtype.val hy
  rw [Subsingleton.elim y 0, map_zero] at h1
  have h2 := congrArg (TensorProduct.rid ℤ (ZMod 2)) h1
  simp at h2

end TauCeti
