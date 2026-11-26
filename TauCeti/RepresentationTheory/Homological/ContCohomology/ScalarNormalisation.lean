/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CocycleCount
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LinearComparison

/-!
# Cocycles normalised at an element acting by a scalar

Let `G` act on `M`, let `R` be a commutative ring acting on `M` compatibly with `G`, and let
`γ : G` act on `M` by a scalar `c : R` with `c - 1` a unit. A coboundary `g ↦ g • m - m` takes the
value `(c - 1) • m` at `γ`, so it vanishes at `γ` only if `m = 0`. Hence every class in `H¹(G, M)`
contains **exactly one** cocycle vanishing at `γ`: from any cocycle `f` in the class subtract the
coboundary of `(c - 1)⁻¹ • f γ`. The normalised cocycle depends `R`-linearly on the class.

For a discrete `G`-module `M` this file states the result on the cohomology
`continuousCohomology 1 (ofDiscreteModule ℤ G M)` with its `R`-module structure by instance
(`TauCeti.ContinuousCohomology.instModuleOfDiscreteModule`), through the explicit cocycles
`TauCeti.ContCohomology.Z1` and the linear comparison
`TauCeti.ContCohomology.explicitH1LinearEquivContinuousCohomology`: the map
`TauCeti.ContCohomology.normalisedCocycle` sends a class to its unique cocycle vanishing at `γ`,
and is an `R`-linear injection onto the cocycles vanishing at `γ`. For counting, a group `W` of
cocycles with `B¹ ≤ W ≤ Z¹` has as many elements vanishing at `γ` as `W` has classes.

The typical case is a Galois representation on which an element of `G` acts by a scalar `ϑ` with
`ϑ - 1` invertible in the coefficients, for instance a root of unity of order prime to `p` other
than `1` on a `p`-adic or `p`-torsion module. Selmer groups are then presented by the cocycles that
vanish at that element, and the statements here turn counts and presentations of those cocycles
into statements about classes.

## Main definitions

* `TauCeti.ContCohomology.normaliseAt`: the `R`-linear map `f ↦ f - d⁰((c - 1)⁻¹ • f γ)` on
  `1`-cochains.
* `TauCeti.ContCohomology.normalisedCocycle`: the cocycle vanishing at `γ` in a class of
  `continuousCohomology 1 (ofDiscreteModule ℤ G M)`, as an `R`-linear map.

## Main results

* `TauCeti.ContCohomology.eq_zero_of_mem_B1_of_apply_eq_zero`: a coboundary vanishing at `γ` is
  zero.
* `TauCeti.ContCohomology.existsUnique_mem_Z1_apply_eq_zero`: every class contains exactly one
  cocycle vanishing at `γ`.
* `TauCeti.ContCohomology.normalisedCocycle_apply_self`,
  `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_normalisedCocycle` and
  `TauCeti.ContCohomology.normalisedCocycle_eq`: the normalised cocycle vanishes at `γ`, lies in
  the class, and is the only such cocycle.
* `TauCeti.ContCohomology.range_normalisedCocycle`: its values are exactly the cocycles vanishing
  at `γ`.
* `TauCeti.ContCohomology.natCard_inf_ker_eval_of_B1_le_of_le_Z1`: for `B¹ ≤ W ≤ Z¹`, the
  cocycles in `W` vanishing at `γ` are as many as the classes of `W`.

## Provenance

The normalisation is adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic, PBC), file `src/New/Congruences/Selmer/SelmerData.lean`, where the
Selmer data impose the relation "vanishing at `γ_*`" on cocycles (`New.Selmer.classRelations`)
and use the scalar action of `γ_*` as in Sah's lemma. The class-level form follows the
`TauCeti.RepresentationTheory.Homological.ContCohomology.Sah` file, which uses the same
bijectivity of `m ↦ γ • m - m`.

## References

* C.-H. Sah, *Automorphisms of finite groups*, J. Algebra 10 (1968), 47–68.
-/

public section

namespace TauCeti.ContCohomology

section Cochains

variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {M : Type*} [AddCommGroup M]
  [Module R M] [DistribMulAction G M] [SMulCommClass G R M]

/-- The coboundary map commutes with the scalars. -/
theorem d0_smul (r : R) (m : M) : d0 G M (r • m) = r • d0 G M m :=
  funext fun g ↦ by simp [d0_apply, smul_sub, smul_comm g r m]

variable {γ : G} {c : R}

omit [SMulCommClass G R M] in
/-- The value of a coboundary at an element acting by the scalar `c` is `(c - 1) • m`. -/
theorem d0_apply_of_smul_eq (hγ : ∀ m : M, γ • m = c • m) (m : M) :
    d0 G M m γ = (c - 1) • m := by
  rw [d0_apply, hγ, sub_smul, one_smul]

omit [SMulCommClass G R M] in
/-- **A coboundary vanishing at a scalar element is zero.** If `γ` acts by a scalar `c` with
`c - 1` a unit, the only `1`-coboundary vanishing at `γ` is zero. -/
theorem eq_zero_of_mem_B1_of_apply_eq_zero (hγ : ∀ m : M, γ • m = c • m) (hc : IsUnit (c - 1))
    {f : G → M} (hf : f ∈ B1 G M) (h : f γ = 0) : f = 0 := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hf
  obtain rfl : f = d0 G M m := funext fun g ↦ by rw [d0_apply]; exact (hm g).symm
  rw [d0_apply_of_smul_eq hγ, hc.smul_eq_zero] at h
  rw [h, map_zero]

omit [SMulCommClass G R M] in
/-- The coboundaries meet the cochains vanishing at a scalar element `γ` trivially. -/
theorem B1_inf_ker_eval_eq_bot (hγ : ∀ m : M, γ • m = c • m) (hc : IsUnit (c - 1)) :
    B1 G M ⊓ (Pi.evalAddMonoidHom (fun _ : G ↦ M) γ).ker = ⊥ :=
  eq_bot_iff.2 fun _ hf ↦ eq_zero_of_mem_B1_of_apply_eq_zero hγ hc hf.1 hf.2

variable (γ) in
/-- **Normalisation at `γ`.** For `c - 1` a unit, the `R`-linear map
`f ↦ f - d⁰((c - 1)⁻¹ • f γ)` on `1`-cochains. When `γ` acts by the scalar `c` it changes `f` by
a coboundary and makes it vanish at `γ`. -/
noncomputable def normaliseAt (hc : IsUnit (c - 1)) : (G → M) →ₗ[R] (G → M) where
  toFun f := f - d0 G M ((hc.unit⁻¹ : Rˣ) • f γ)
  map_add' f f' := by simp only [Pi.add_apply, smul_add, map_add]; abel
  map_smul' r f := by
    simp only [Pi.smul_apply, smul_comm _ r, d0_smul, RingHom.id_apply, smul_sub]

/-- The normalisation at `γ` subtracts the coboundary of `(c - 1)⁻¹ • f γ`. -/
theorem normaliseAt_apply (hc : IsUnit (c - 1)) (f : G → M) :
    normaliseAt γ hc f = f - d0 G M ((hc.unit⁻¹ : Rˣ) • f γ) :=
  (rfl)

/-- A cochain differs from its normalisation by a coboundary. -/
theorem sub_normaliseAt_mem_B1 (hc : IsUnit (c - 1)) (f : G → M) :
    f - normaliseAt γ hc f ∈ B1 G M := by
  rw [normaliseAt_apply, sub_sub_cancel]
  exact d0_mem_B1 _

/-- The normalisation at `γ` vanishes at `γ`. -/
@[simp]
theorem normaliseAt_apply_self (hγ : ∀ m : M, γ • m = c • m) (hc : IsUnit (c - 1)) (f : G → M) :
    normaliseAt γ hc f γ = 0 := by
  rw [normaliseAt_apply, Pi.sub_apply, d0_apply_of_smul_eq hγ, Units.smul_def, ← mul_smul,
    hc.mul_val_inv, one_smul, sub_self]

/-- A cochain that already vanishes at `γ` is its own normalisation. -/
theorem normaliseAt_eq_self (hc : IsUnit (c - 1)) {f : G → M} (h : f γ = 0) :
    normaliseAt γ hc f = f := by
  rw [normaliseAt_apply, h, smul_zero, map_zero, sub_zero]

/-- The normalisation of a coboundary is zero. -/
theorem normaliseAt_eq_zero_of_mem_B1 (hγ : ∀ m : M, γ • m = c • m) (hc : IsUnit (c - 1))
    {f : G → M} (hf : f ∈ B1 G M) : normaliseAt γ hc f = 0 := by
  refine eq_zero_of_mem_B1_of_apply_eq_zero hγ hc ?_ (normaliseAt_apply_self hγ hc f)
  simpa using sub_mem hf (sub_normaliseAt_mem_B1 hc f)

variable [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]

/-- The normalisation of a continuous `1`-cocycle is a continuous `1`-cocycle. -/
theorem normaliseAt_mem_Z1 (hc : IsUnit (c - 1)) {f : G → M} (hf : f ∈ Z1 G M) :
    normaliseAt γ hc f ∈ Z1 G M := by
  simpa using sub_mem hf (B1_le_Z1 G M (sub_normaliseAt_mem_B1 hc f))

/-- **Counting the cocycles vanishing at a scalar element.** Let `γ` act by a scalar `c` with
`c - 1` a unit. For a group `W` of `1`-cocycles containing the coboundaries, the cocycles in `W`
vanishing at `γ` are exactly as many as the classes of `W`. -/
theorem natCard_inf_ker_eval_of_B1_le_of_le_Z1 (hγ : ∀ m : M, γ • m = c • m)
    (hc : IsUnit (c - 1)) {W : AddSubgroup (G → M)} (hB : B1 G M ≤ W) (hW : W ≤ Z1 G M) :
    Nat.card (W ⊓ (Pi.evalAddMonoidHom (fun _ : G ↦ M) γ).ker :) =
      Nat.card ((W.addSubgroupOf (Z1 G M)).map (H1pi G M)) := by
  set W₀ := W ⊓ (Pi.evalAddMonoidHom (fun _ : G ↦ M) γ).ker
  have hB₀ : W₀ ⊓ B1 G M = ⊥ :=
    eq_bot_iff.2 fun f hf ↦ eq_zero_of_mem_B1_of_apply_eq_zero hγ hc hf.2 hf.1.2
  -- every class of `W` has its normalised representative in `W₀`
  have hmap : (W₀.addSubgroupOf (Z1 G M)).map (H1pi G M) =
      (W.addSubgroupOf (Z1 G M)).map (H1pi G M) := by
    refine le_antisymm (AddSubgroup.map_mono fun f hf ↦ ?_) ?_
    · exact AddSubgroup.mem_addSubgroupOf.2 (AddSubgroup.mem_addSubgroupOf.1 hf).1
    rintro _ ⟨f, hf, rfl⟩
    have hfW : (f : G → M) ∈ W := AddSubgroup.mem_addSubgroupOf.1 hf
    refine ⟨⟨normaliseAt γ hc f, normaliseAt_mem_Z1 hc f.property⟩,
      AddSubgroup.mem_addSubgroupOf.2 ⟨?_, normaliseAt_apply_self hγ hc f⟩, ?_⟩
    · simpa using sub_mem hfW (hB (sub_normaliseAt_mem_B1 hc f))
    · rw [← sub_eq_zero, ← map_sub]
      refine H1pi_eq_zero_iff.2 ?_
      rw [AddSubgroup.coe_sub, ← neg_sub]
      exact neg_mem (sub_normaliseAt_mem_B1 hc _)
  rw [natCard_of_le_Z1 (inf_le_left.trans hW), hB₀, hmap, AddSubgroup.card_bot, mul_one]

end Cochains

section Classes

universe u w

variable {R : Type w} [CommRing R] {G M : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [SMulCommClass G R M] {γ : G} {c : R}

/-- Normalisation at `γ` on the explicit `H¹(G, M)`. -/
private noncomputable def H1.normaliseAt (hγ : ∀ m : M, γ • m = c • m) (hc : IsUnit (c - 1)) :
    H1 G M →ₗ[R] (G → M) where
  toFun := QuotientAddGroup.lift _ ((ContCohomology.normaliseAt γ hc).toAddMonoidHom.comp
    (Z1 G M).subtype) fun f hf ↦
      normaliseAt_eq_zero_of_mem_B1 hγ hc (AddSubgroup.mem_addSubgroupOf.1 hf)
  map_add' := map_add _
  map_smul' r x := by
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [H1.smul_mk]
      exact (ContCohomology.normaliseAt γ hc).map_smul r (f : G → M)

/-- **The normalised cocycle of a class.** Let `γ` act on the discrete `G`-module `M` by a scalar
`c` with `c - 1` a unit. A class in `H¹(G, M) = continuousCohomology 1 (ofDiscreteModule ℤ G M)`
goes to the unique continuous `1`-cocycle in it that vanishes at `γ`; the map is `R`-linear for
the `R`-module structure of the cohomology by instance. -/
noncomputable def normalisedCocycle (hγ : ∀ m : M, γ • m = c • m) (hc : IsUnit (c - 1)) :
    continuousCohomology 1 (ofDiscreteModule ℤ G M) →ₗ[R] (G → M) :=
  H1.normaliseAt hγ hc ∘ₗ (explicitH1LinearEquivContinuousCohomology R G M).symm.toLinearMap

/-- The normalised cocycle of the class of a cocycle `f` is the normalisation of `f`. -/
theorem normalisedCocycle_explicitH1AddEquivContinuousCohomology (hγ : ∀ m : M, γ • m = c • m)
    (hc : IsUnit (c - 1)) (f : Z1 G M) :
    normalisedCocycle hγ hc (explicitH1AddEquivContinuousCohomology G M f) =
      ContCohomology.normaliseAt γ hc f := by
  rw [← explicitH1LinearEquivContinuousCohomology_apply (R := R)]
  exact congrArg (H1.normaliseAt hγ hc)
    ((explicitH1LinearEquivContinuousCohomology R G M).symm_apply_apply _)

variable (hγ : ∀ m : M, γ • m = c • m) (hc : IsUnit (c - 1))
  (x : continuousCohomology 1 (ofDiscreteModule ℤ G M))

/-- The normalised cocycle of a class is a continuous `1`-cocycle. -/
theorem normalisedCocycle_mem_Z1 : normalisedCocycle hγ hc x ∈ Z1 G M := by
  obtain ⟨f, rfl⟩ := (explicitH1AddEquivContinuousCohomology G M).surjective x
  induction f using QuotientAddGroup.induction_on with
  | _ f =>
    rw [normalisedCocycle_explicitH1AddEquivContinuousCohomology]
    exact normaliseAt_mem_Z1 hc f.property

/-- The normalised cocycle of a class vanishes at `γ`. -/
@[simp]
theorem normalisedCocycle_apply_self : normalisedCocycle hγ hc x γ = 0 := by
  obtain ⟨f, rfl⟩ := (explicitH1AddEquivContinuousCohomology G M).surjective x
  induction f using QuotientAddGroup.induction_on with
  | _ f =>
    rw [normalisedCocycle_explicitH1AddEquivContinuousCohomology]
    exact normaliseAt_apply_self hγ hc f

/-- **The normalised cocycle lies in the class.** -/
theorem explicitH1AddEquivContinuousCohomology_normalisedCocycle :
    explicitH1AddEquivContinuousCohomology G M
      ((⟨normalisedCocycle hγ hc x, normalisedCocycle_mem_Z1 hγ hc x⟩ : Z1 G M) : H1 G M) = x := by
  obtain ⟨f, rfl⟩ := (explicitH1AddEquivContinuousCohomology G M).surjective x
  induction f using QuotientAddGroup.induction_on with
  | _ f =>
    congr 1
    rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, H1pi_eq_zero_iff, AddSubgroup.coe_sub]
    change normalisedCocycle hγ hc (explicitH1AddEquivContinuousCohomology G M f) - f ∈ B1 G M
    rw [normalisedCocycle_explicitH1AddEquivContinuousCohomology, ← neg_sub]
    exact neg_mem (sub_normaliseAt_mem_B1 hc _)

/-- **Uniqueness of the normalised cocycle.** A cocycle in the class `x` that vanishes at `γ` is
the normalised cocycle of `x`. -/
theorem normalisedCocycle_eq {f : Z1 G M} (hf : (f : G → M) γ = 0)
    (hx : explicitH1AddEquivContinuousCohomology G M f = x) :
    normalisedCocycle hγ hc x = f := by
  rw [← hx, normalisedCocycle_explicitH1AddEquivContinuousCohomology, normaliseAt_eq_self hc hf]

include hγ hc in
/-- **Every class has exactly one cocycle vanishing at `γ`.** Let `γ` act on the discrete
`G`-module `M` by a scalar `c` with `c - 1` a unit. Each class of
`continuousCohomology 1 (ofDiscreteModule ℤ G M)` contains exactly one continuous `1`-cocycle that
vanishes at `γ`. -/
theorem existsUnique_mem_Z1_apply_eq_zero :
    ∃! f : Z1 G M, (f : G → M) γ = 0 ∧ explicitH1AddEquivContinuousCohomology G M f = x :=
  ⟨⟨normalisedCocycle hγ hc x, normalisedCocycle_mem_Z1 hγ hc x⟩,
    ⟨normalisedCocycle_apply_self hγ hc x,
      explicitH1AddEquivContinuousCohomology_normalisedCocycle hγ hc x⟩,
    fun _ ⟨hf, hx⟩ ↦ Subtype.ext (normalisedCocycle_eq hγ hc x hf hx).symm⟩

include hγ hc in
/-- The normalised cocycle determines the class. -/
theorem normalisedCocycle_injective : Function.Injective (normalisedCocycle hγ hc) := by
  intro x y h
  rw [← explicitH1AddEquivContinuousCohomology_normalisedCocycle hγ hc x,
    ← explicitH1AddEquivContinuousCohomology_normalisedCocycle hγ hc y]
  congr 2
  exact Subtype.ext h

include hγ hc in
/-- The normalised cocycles are exactly the continuous `1`-cocycles vanishing at `γ`. -/
theorem range_normalisedCocycle :
    Set.range (normalisedCocycle hγ hc) = {f | f ∈ Z1 G M ∧ f γ = 0} := by
  refine Set.ext fun f ↦ ⟨?_, fun ⟨hf, h⟩ ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨normalisedCocycle_mem_Z1 hγ hc x, normalisedCocycle_apply_self hγ hc x⟩
  · exact ⟨_, normalisedCocycle_eq hγ hc _ (f := ⟨f, hf⟩) h rfl⟩

end Classes

end TauCeti.ContCohomology
