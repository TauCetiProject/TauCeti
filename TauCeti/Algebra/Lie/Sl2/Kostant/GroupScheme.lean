/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Kostant.Points
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points

/-!
# The full-weight rank-one Kostant carrier

The standard two-dimensional `sl₂` module has weights `1` and `-1`.  In particular, unlike the
adjoint representation with weights `0`, `2`, and `-2`, its weights generate the full rank-one
weight lattice rather than only the root lattice.  This file feeds that admissible integral
lattice into the toral Kostant construction and names the resulting rank-one group scheme, its
two root subgroups, and its split torus.

The carrier is completely explicit.  It is the smallest closed subgroup scheme of `GL₂` containing
the upper and lower elementary transvections and the diagonal matrices

```text
diag(s, s⁻¹).
```

The root operators have weights `2` and `-2`, so conjugation by the torus multiplies their
parameters by `s²` and `s⁻²`, respectively.  Thus the represented torus is the coroot torus and its
characters are the full simply connected type-`A₁` character lattice.

This is the first non-adjoint carrier in the explicit Chevalley--Demazure construction requested
by Layer 9 of the ReductiveGroups roadmap.  The same full-weight admissible-lattice step remains
for the higher-rank types whose root and weight lattices differ.  Identifying this carrier with
the standard special-linear group scheme, and assembling a Borel into a pinning, are separate
scheme-theoretic steps.

## Main declarations

* `TauCeti.Sl2Std.rankOneWeight`: the two weights `1` and `-1` of the integral basis.
* `TauCeti.Sl2Std.span_range_rankOneWeight_eq_top`: these weights generate the full character
  lattice `Fin 1 → ℤ`.
* `TauCeti.Sl2Std.rankOneGroupScheme`: the toral Kostant closure for the standard integral
  lattice.
* `TauCeti.Sl2Std.rankOneRootSubgroup` and `TauCeti.Sl2Std.rankOneWeightTorus`: the two root
  subgroups and the closed split torus in that carrier.
* `TauCeti.Sl2Std.rankOneCarrierPoints`: the matrix-valued points of the carrier, with its
  root-subgroup and torus points and their functoriality in the value ring.
* `TauCeti.Sl2Std.rankOneTorusMatrix`: the associated torus representation.
* `TauCeti.Sl2Std.rankOneTorusMatrix_apply`: its matrix equation `diag(s, s⁻¹)`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.Sl2Std

open TauCeti.UniversalEnvelopingAlgebra

universe u v

local notation "e" => ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1]
local notation "h" => ![slFinTwoBasis ℚ 2]
local notation "ρ" => repEnveloping ℚ 1
local notation "M" => Submodule.toAddSubgroup (integralLattice 1)
local notation "b" => integralLatticeAddSubgroupBasis 1
local notation "hnil" => isNilpotent_repEnveloping_root ℚ 1
local notation "hM" => kostantForm_apply_mem_integralLattice 1

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-! ## The full rank-one weight lattice -/

/-- The integral weight of the `i`th standard basis vector of the two-dimensional `sl₂` module:
`v₀` has weight `1` and `v₁` has weight `-1`. -/
def rankOneWeight (i : Fin 2) : Fin 1 → ℤ :=
  fun _ => if i = 0 then 1 else -1

@[simp]
theorem rankOneWeight_zero : rankOneWeight 0 = ![1] := by
  funext j
  fin_cases j
  simp [rankOneWeight]

@[simp]
theorem rankOneWeight_one : rankOneWeight 1 = ![-1] := by
  funext j
  fin_cases j
  simp [rankOneWeight]

/-- Each vector of the standard integral basis is a weight vector of its recorded rank-one
weight. -/
theorem isCartanWeightVector_integralLatticeAddSubgroupBasis (i : Fin 2) :
    IsCartanWeightVector h ρ (rankOneWeight i) ((b i : M) : Sl2Std ℚ 1) := by
  rw [isCartanWeightVector_iff]
  intro j
  fin_cases j
  -- After specializing to the unique Cartan generator, expose the enveloping-algebra action
  -- and the integral-basis coercion that the representation lemmas describe.
  change ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (slFinTwoBasis ℚ 2))
      ((b i : M) : Sl2Std ℚ 1) = ((rankOneWeight i 0 : ℤ) : ℚ) • (b i : Sl2Std ℚ 1)
  rw [repEnveloping_ι_slFinTwoBasis, coe_integralLatticeAddSubgroupBasis_apply]
  -- The preceding rewrites identify the action with `diag`; unfold only the remaining
  -- basis-vector coercion so that `diag_basis` applies.
  change diag ℚ 1 (basis ℚ 1 i) = _
  rw [diag_basis]
  fin_cases i <;> norm_num [rankOneWeight]

/-- The two standard weights generate the full character lattice `Fin 1 → ℤ`.  In fact the
highest-weight basis vector already has the primitive weight `1`. -/
theorem span_range_rankOneWeight_eq_top :
    Submodule.span ℤ (Set.range rankOneWeight) = ⊤ := by
  rw [eq_top_iff]
  intro μ _
  have hμ : μ = μ 0 • rankOneWeight 0 := by
    funext j
    fin_cases j
    simp
  rw [hμ]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self (0 : Fin 2)))

/-- The weight of the `i`th root operator: the raising operator has weight `2` and the lowering
operator has weight `-2`.  These are the two roots inside the full weight lattice generated by
`rankOneWeight`. -/
def rankOneRootWeight (i : Fin 2) : Fin 1 → ℤ :=
  fun _ => if i = 0 then 2 else -2

@[simp]
theorem rankOneRootWeight_zero : rankOneRootWeight 0 = ![2] := by
  funext j
  fin_cases j
  simp [rankOneRootWeight]

@[simp]
theorem rankOneRootWeight_one : rankOneRootWeight 1 = ![-2] := by
  funext j
  fin_cases j
  simp [rankOneRootWeight]

/-- A character of a rank-one split torus evaluates to the corresponding integral power of its
unique parameter. -/
@[simp]
theorem torusCharacter_singleton {A : Type*} [CommRing A]
    (s : Fin 1 → Aˣ) (n : ℤ) :
    torusCharacter s ![n] = (s 0) ^ n := by
  rw [torusCharacter_def]
  simp

/-- The two distinguished root vectors have weights `2` and `-2` for the rank-one Cartan
generator. -/
theorem lie_cartan_root_eq_smul (i : Fin 2) (j : Fin 1) :
    ⁅h j, e i⁆ = ((rankOneRootWeight i j : ℤ) : ℚ) • e i := by
  fin_cases j
  fin_cases i
  · simp [rankOneRootWeight]
  · simp [rankOneRootWeight]

/-! ## The explicit carrier and its pinned generators -/

/-- The rank-one Chevalley carrier obtained from the full-weight standard integral `sl₂` lattice:
the closed subgroup scheme of `GL₂` generated by its two root subgroups and its represented split
torus. -/
noncomputable def rankOneGroupScheme :
    Grp (Over (Spec (CommRingCat.of ℤ))) :=
  kostantToralGroupScheme e h ρ M hM hnil b rankOneWeight

private theorem rankOneGroupScheme_eq_def :
    rankOneGroupScheme = kostantToralGroupScheme e h ρ M hM hnil b rankOneWeight :=
  rfl

/-- The rank-one carrier is the toral Kostant group scheme for the standard integral lattice. -/
theorem rankOneGroupScheme_def :
    rankOneGroupScheme = kostantToralGroupScheme e h ρ M hM hnil b rankOneWeight :=
  rankOneGroupScheme_eq_def

/-- The closed immersion of the rank-one carrier into `GL₂`. -/
noncomputable def rankOneGroupSchemeι :
    rankOneGroupScheme ⟶ GeneralLinear.groupScheme ℤ 2 :=
  eqToHom rankOneGroupScheme_def ≫
    kostantToralGroupSchemeι e h ρ M hM hnil b rankOneWeight

private theorem rankOneGroupSchemeι_eq_def :
    rankOneGroupSchemeι =
      eqToHom rankOneGroupScheme_def ≫
        kostantToralGroupSchemeι e h ρ M hM hnil b rankOneWeight :=
  rfl

/-- The inclusion of the rank-one carrier is the generic toral Kostant inclusion, transported
along its defining equality. -/
theorem rankOneGroupSchemeι_def :
    rankOneGroupSchemeι =
      eqToHom rankOneGroupScheme_def ≫
        kostantToralGroupSchemeι e h ρ M hM hnil b rankOneWeight :=
  rankOneGroupSchemeι_eq_def

/-- The inclusion of the rank-one carrier into `GL₂` is a closed immersion. -/
instance isClosedImmersion_rankOneGroupSchemeι :
    IsClosedImmersion rankOneGroupSchemeι.hom.hom.left :=
  isClosedImmersion_kostantToralGroupSchemeι e h ρ M hM hnil b rankOneWeight

/-- The root subgroup indexed by `0` or `1` in the rank-one carrier. -/
noncomputable def rankOneRootSubgroup (i : Fin 2) :
    AdditiveGroup.groupScheme ℤ ⟶ rankOneGroupScheme :=
  kostantRootSubgroupToToral e h ρ M hM hnil b rankOneWeight i ≫
    eqToHom rankOneGroupScheme_def.symm

private theorem rankOneRootSubgroup_eq_def (i : Fin 2) :
    rankOneRootSubgroup i =
      kostantRootSubgroupToToral e h ρ M hM hnil b rankOneWeight i ≫
        eqToHom rankOneGroupScheme_def.symm :=
  rfl

/-- A rank-one root subgroup is the generic toral Kostant root subgroup, transported into the
named carrier. -/
theorem rankOneRootSubgroup_def (i : Fin 2) :
    rankOneRootSubgroup i =
      kostantRootSubgroupToToral e h ρ M hM hnil b rankOneWeight i ≫
        eqToHom rankOneGroupScheme_def.symm :=
  rankOneRootSubgroup_eq_def i

/-- The represented split torus in the rank-one carrier. -/
noncomputable def rankOneWeightTorus :
    SplitTorus.groupScheme ℤ (Fin 1) ⟶ rankOneGroupScheme :=
  kostantWeightTorusToToral e h ρ M hM hnil b rankOneWeight ≫
    eqToHom rankOneGroupScheme_def.symm

private theorem rankOneWeightTorus_eq_def :
    rankOneWeightTorus =
      kostantWeightTorusToToral e h ρ M hM hnil b rankOneWeight ≫
        eqToHom rankOneGroupScheme_def.symm :=
  rfl

/-- The rank-one weight torus is the generic toral Kostant weight torus, transported into the
named carrier. -/
theorem rankOneWeightTorus_def :
    rankOneWeightTorus =
      kostantWeightTorusToToral e h ρ M hM hnil b rankOneWeight ≫
        eqToHom rankOneGroupScheme_def.symm :=
  rankOneWeightTorus_eq_def

/-- Including a root subgroup into `GL₂` recovers its represented Kostant root subgroup. -/
@[simp]
theorem rankOneRootSubgroup_comp_ι (i : Fin 2) :
    rankOneRootSubgroup i ≫ rankOneGroupSchemeι =
      kostantRootSubgroup e h ρ M hM i (hnil i) b :=
  kostantRootSubgroupToToral_comp_ι e h ρ M hM hnil b rankOneWeight i

/-- Including the rank-one weight torus into `GL₂` recovers its diagonal weight
representation. -/
@[simp]
theorem rankOneWeightTorus_comp_ι :
    rankOneWeightTorus ≫ rankOneGroupSchemeι =
      GeneralLinear.weightTorus (R := ℤ) rankOneWeight :=
  kostantWeightTorusToToral_comp_ι e h ρ M hM hnil b rankOneWeight

/-- The rank-one weight torus is a closed immersion into the carrier because its two weights
generate the full character lattice. -/
instance isClosedImmersion_rankOneWeightTorus :
    IsClosedImmersion rankOneWeightTorus.hom.hom.left :=
  isClosedImmersion_kostantWeightTorusToToral e h ρ M hM hnil b rankOneWeight
    span_range_rankOneWeight_eq_top

/-- The rank-one split torus as a closed subgroup scheme of the carrier. -/
noncomputable def rankOneWeightTorusInGroupScheme :
    ClosedSubgroupScheme rankOneGroupScheme :=
  ClosedSubgroupScheme.mk rankOneWeightTorus

/-- The subobject underlying the closed rank-one weight torus is represented by its inclusion. -/
@[simp]
theorem coe_rankOneWeightTorusInGroupScheme :
    (rankOneWeightTorusInGroupScheme).1 = Subobject.mk rankOneWeightTorus := by
  rw [rankOneWeightTorusInGroupScheme]
  exact ClosedSubgroupScheme.coe_mk _

/-- Each root subgroup is a closed immersion into the rank-one carrier. -/
instance isClosedImmersion_rankOneRootSubgroup (i : Fin 2) :
    IsClosedImmersion (rankOneRootSubgroup i).hom.hom.left := by
  have hcomp : IsClosedImmersion
      ((rankOneRootSubgroup i ≫ rankOneGroupSchemeι).hom.hom.left) := by
    rw [rankOneRootSubgroup_comp_ι]
    exact isClosedImmersion_kostantRootSubgroup_one i
  exact @IsClosedImmersion.of_comp _ _ _
    (rankOneRootSubgroup i).hom.hom.left rankOneGroupSchemeι.hom.hom.left hcomp inferInstance

/-! ## Matrix-valued points -/

/-- The represented split torus on `A`-points, written in the integral basis. -/
noncomputable def rankOneTorusMatrix {A : Type*} [CommRing A] :
    ((Fin 1 → Aˣ) →* Matrix.GeneralLinearGroup (Fin 2) A) :=
  kostantTorusMatrix M b rankOneWeight

/-- A rank-one torus point is the diagonal matrix `diag(s, s⁻¹)`. -/
@[simp]
theorem rankOneTorusMatrix_apply {A : Type*} [CommRing A] (s : Fin 1 → Aˣ) :
    rankOneTorusMatrix s = diagGL ![s 0, (s 0)⁻¹] := by
  rw [rankOneTorusMatrix, kostantTorusMatrix_apply]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneWeight, torusCharacter_def]

/-- The points of the full-weight rank-one Kostant carrier, embedded in `GL₂`. -/
noncomputable def rankOneCarrierPoints (A : Type u) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) A) :=
  kostantToralPointsSubgroup e h ρ M hM hnil b rankOneWeight A

/-- The named rank-one carrier points are the specialization of the generic toral Kostant
points. -/
theorem rankOneCarrierPoints_def (A : Type u) [CommRing A] :
    rankOneCarrierPoints A =
      kostantToralPointsSubgroup e h ρ M hM hnil b rankOneWeight A := by
  rw [rankOneCarrierPoints]

/-- Membership in the rank-one carrier points is vanishing on its defining Hopf ideal. -/
@[simp]
theorem mem_rankOneCarrierPoints_iff (A : Type u) [CommRing A]
    (g : Matrix.GeneralLinearGroup (Fin 2) A) :
    g ∈ rankOneCarrierPoints A ↔
      ∀ x ∈ kostantToralDefiningIdeal e h ρ M hM hnil b rankOneWeight,
        ((GeneralLinear.pointsMulEquiv (R := ℤ) 2).symm g).ofConv x = 0 := by
  rw [rankOneCarrierPoints_def]
  exact mem_kostantToralPointsSubgroup_iff e h ρ M hM hnil b rankOneWeight A g

/-- The two parametrized root subgroups in the points of the rank-one carrier. -/
noncomputable def rankOneCarrierRootSubgroupHom (i : Fin 2) (A : Type u) [CommRing A] :
    Multiplicative A →* rankOneCarrierPoints A :=
  ((MulEquiv.subgroupCongr (rankOneCarrierPoints_def A)).symm.toMonoidHom).comp
    (kostantToralRootSubgroupPoints e h ρ M hM hnil b rankOneWeight i A)

/-- A parametrized root-subgroup point in the rank-one carrier. -/
noncomputable abbrev rankOneCarrierRootSubgroupPoint
    (i : Fin 2) (A : Type u) [CommRing A] (t : Multiplicative A) :
    rankOneCarrierPoints A :=
  rankOneCarrierRootSubgroupHom i A t

/-- A carrier-valued root-subgroup point is its represented divided-power exponential matrix. -/
theorem coe_rankOneCarrierRootSubgroupPoint
    (i : Fin 2) (A : Type u) [CommRing A] (t : Multiplicative A) :
    (rankOneCarrierRootSubgroupPoint i A t : Matrix.GeneralLinearGroup (Fin 2) A) =
      kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) := by
  rw [rankOneCarrierRootSubgroupPoint, rankOneCarrierRootSubgroupHom,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_symm_apply, coe_kostantToralRootSubgroupPoints]

/-- The entries of a carrier-valued root-subgroup point are those of the corresponding elementary
transvection. -/
@[simp]
theorem coe_rankOneCarrierRootSubgroupPoint_apply
    (i : Fin 2) (A : Type u) [CommRing A] (t : Multiplicative A) (r s : Fin 2) :
    ((rankOneCarrierRootSubgroupPoint i A t : Matrix.GeneralLinearGroup (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) r s =
      (if r = s then 1 else 0) +
        if s = i.rev ∧ r = i then Multiplicative.toAdd t else 0 := by
  rw [coe_rankOneCarrierRootSubgroupPoint, kostantRootSubgroupMatrix_eq_transvectionUnit,
    TauCeti.coe_transvectionUnit]
  simp [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm,
    and_comm]

/-- The represented full-weight torus homomorphism into the points of the rank-one carrier. -/
noncomputable def rankOneCarrierTorusHom (A : Type u) [CommRing A] :
    (Fin 1 → Aˣ) →* rankOneCarrierPoints A :=
  ((MulEquiv.subgroupCongr (rankOneCarrierPoints_def A)).symm.toMonoidHom).comp
    (kostantToralWeightTorusPoints e h ρ M hM hnil b rankOneWeight A)

/-- A represented full-weight torus point in the rank-one carrier. -/
noncomputable abbrev rankOneCarrierTorusPoint
    (A : Type u) [CommRing A] (s : Fin 1 → Aˣ) : rankOneCarrierPoints A :=
  rankOneCarrierTorusHom A s

/-- The represented full-weight torus subgroup inside the points of the rank-one carrier. -/
noncomputable abbrev rankOneCarrierTorusPoints (A : Type u) [CommRing A] :
    Subgroup (rankOneCarrierPoints A) :=
  (rankOneCarrierTorusHom A).range

/-- In the standard basis, a carrier torus point is `diag(s, s⁻¹)`. -/
@[simp]
theorem coe_rankOneCarrierTorusPoint (A : Type u) [CommRing A] (s : Fin 1 → Aˣ) :
    (rankOneCarrierTorusPoint A s : Matrix.GeneralLinearGroup (Fin 2) A) =
      diagGL ![s 0, (s 0)⁻¹] := by
  rw [rankOneCarrierTorusPoint, rankOneCarrierTorusHom,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_symm_apply, coe_kostantToralWeightTorusPoints]
  simpa only [rankOneTorusMatrix] using rankOneTorusMatrix_apply s

private theorem rankOneCarrierPoints_eq_hopfIdealPoints
    (A : Type u) [CommRing A] :
    rankOneCarrierPoints A = GeneralLinear.hopfIdealPointsSubgroup 2
      (kostantToralDefiningIdeal e h ρ M hM hnil b rankOneWeight) A :=
  (rankOneCarrierPoints_def A).trans
    (kostantToralPointsSubgroup_def e h ρ M hM hnil b rankOneWeight A)

/-- The map on rank-one carrier points induced by a homomorphism of value rings. -/
noncomputable def rankOneCarrierPointsMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) : rankOneCarrierPoints A →* rankOneCarrierPoints B :=
  ((MulEquiv.subgroupCongr (rankOneCarrierPoints_eq_hopfIdealPoints B)).symm.toMonoidHom).comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup 2
      (kostantToralDefiningIdeal e h ρ M hM hnil b rankOneWeight) f.toIntAlgHom).comp
      (MulEquiv.subgroupCongr (rankOneCarrierPoints_eq_hopfIdealPoints A)).toMonoidHom)

/-- The induced map on rank-one carrier points is the entrywise map. -/
@[simp]
theorem coe_rankOneCarrierPointsMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (g : rankOneCarrierPoints A) :
    (rankOneCarrierPointsMap f g : Matrix.GeneralLinearGroup (Fin 2) B) =
      Matrix.GeneralLinearGroup.map f g := by
  have hring : f.toIntAlgHom.toRingHom = f := RingHom.ext (RingHom.toIntAlgHom_apply f)
  rw [rankOneCarrierPointsMap]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_symm_apply, GeneralLinear.coe_mapHopfIdealPointsSubgroup,
    MulEquiv.subgroupCongr_apply, hring]

/-- Entrywise, the induced map applies the value-ring homomorphism to each matrix entry. -/
theorem coe_rankOneCarrierPointsMap_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (g : rankOneCarrierPoints A) (i j : Fin 2) :
    ((rankOneCarrierPointsMap f g : Matrix.GeneralLinearGroup (Fin 2) B) :
        Matrix (Fin 2) (Fin 2) B) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j) := by
  rw [coe_rankOneCarrierPointsMap, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism induces the identity on rank-one carrier points. -/
@[simp]
theorem rankOneCarrierPointsMap_id {A : Type u} [CommRing A] :
    rankOneCarrierPointsMap (RingHom.id A) = MonoidHom.id _ := by
  have hid : (RingHom.id A).toIntAlgHom = AlgHom.id ℤ A := AlgHom.ext fun _ ↦ rfl
  rw [rankOneCarrierPointsMap, hid, GeneralLinear.mapHopfIdealPointsSubgroup_id]
  apply MonoidHom.ext
  intro g
  exact (MulEquiv.subgroupCongr
    (rankOneCarrierPoints_eq_hopfIdealPoints A)).symm_apply_apply g

/-- The induced maps on rank-one carrier points compose. -/
@[simp]
theorem rankOneCarrierPointsMap_comp
    {A : Type u} {B : Type v} {C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    rankOneCarrierPointsMap (g.comp f) =
      (rankOneCarrierPointsMap g).comp (rankOneCarrierPointsMap f) := by
  have hcomp : (g.comp f).toIntAlgHom = g.toIntAlgHom.comp f.toIntAlgHom :=
    AlgHom.ext fun _ ↦ rfl
  apply MonoidHom.ext
  intro x
  simp only [rankOneCarrierPointsMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hcomp,
    GeneralLinear.mapHopfIdealPointsSubgroup_comp, MulEquiv.apply_symm_apply]

/-- An injective value-ring homomorphism induces an injective map on rank-one carrier points. -/
theorem rankOneCarrierPointsMap_injective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (rankOneCarrierPointsMap f) := by
  rw [rankOneCarrierPointsMap]
  exact (MulEquiv.subgroupCongr
    (rankOneCarrierPoints_eq_hopfIdealPoints B)).symm.injective.comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup_injective 2
      (kostantToralDefiningIdeal e h ρ M hM hnil b rankOneWeight) hf).comp
      (MulEquiv.subgroupCongr (rankOneCarrierPoints_eq_hopfIdealPoints A)).injective)

/-- The induced map carries rank-one root-subgroup parameters along the value-ring map. -/
@[simp]
theorem rankOneCarrierPointsMap_rootSubgroupPoint
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (i : Fin 2) (t : Multiplicative A) :
    rankOneCarrierPointsMap f (rankOneCarrierRootSubgroupPoint i A t) =
      rankOneCarrierRootSubgroupPoint i B
        (Multiplicative.ofAdd (f (Multiplicative.toAdd t))) := by
  apply Subtype.ext
  rw [coe_rankOneCarrierPointsMap]
  simp only [rankOneCarrierRootSubgroupPoint, rankOneCarrierRootSubgroupHom,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_symm_apply,
    coe_kostantToralRootSubgroupPoints]
  rw [map_kostantRootSubgroupMatrix, AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply,
    RingHom.toIntAlgHom_apply]

/-- The induced map carries a torus point coordinatewise along the value-ring map. -/
@[simp]
theorem rankOneCarrierPointsMap_torusPoint
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (s : Fin 1 → Aˣ) :
    rankOneCarrierPointsMap f (rankOneCarrierTorusPoint A s) =
      rankOneCarrierTorusPoint B (fun i ↦ Units.map (f : A →* B) (s i)) := by
  apply Subtype.ext
  rw [coe_rankOneCarrierPointsMap]
  simp only [rankOneCarrierTorusPoint, rankOneCarrierTorusHom,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_symm_apply,
    coe_kostantToralWeightTorusPoints]
  exact map_kostantTorusMatrix M b rankOneWeight f s

/-- The represented rank-one weight torus on points of a value algebra. -/
noncomputable def rankOneTorusPoints (A : CommAlgCat.{u} ℤ) :
    (Fin 1 → Aˣ) →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  kostantTorusPoints M b rankOneWeight A

/-- The parametrized root subgroup for one of the two rank-one root generators. -/
noncomputable def rankOneRootSubgroupParam (i : Fin 2) (A : CommAlgCat.{u} ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  kostantRootSubgroupParam e h ρ M hM i (hnil i) A

/-- A rank-one torus point scales each base-changed basis vector by its recorded weight
character. -/
@[simp]
theorem rankOneTorusPoints_apply_baseChange_basis
    {A : Type u} [CommRing A] (s : Fin 1 → Aˣ) (i : Fin 2) :
    (rankOneTorusPoints (CommAlgCat.of ℤ A) s).val (1 ⊗ₜ[ℤ] b i) =
      (torusCharacter s (rankOneWeight i) : A) • (b).baseChange A i := by
  rw [Module.Basis.baseChange_apply, rankOneTorusPoints, kostantTorusPoints_tmul_basis]
  simp [smul_tmul']

/-- A parametrized rank-one root element adds `t` times the `i`th basis vector to the opposite
basis vector and fixes the other basis vector. -/
@[simp]
theorem rankOneRootSubgroupParam_apply_baseChange_basis
    {A : Type u} [CommRing A] (i s : Fin 2) (t : Multiplicative A) :
    (rankOneRootSubgroupParam i (CommAlgCat.of ℤ A) t).val (1 ⊗ₜ[ℤ] b s) =
      (b).baseChange A s +
        if s = i.rev then Multiplicative.toAdd t • (b).baseChange A i else 0 := by
  rw [rankOneRootSubgroupParam, kostantRootSubgroupParam_apply]
  simpa using kostantRootSubgroupPoints_apply_baseChange_basis_one i s
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t)

/-- **The rank-one pinning equation on points.** Conjugation by the full-weight torus sends the
root element `xᵢ(t)` to `xᵢ(αᵢ(s)t)`, where `α₀ = 2` and `α₁ = -2`. -/
theorem rankOneTorusPoints_conj_rootSubgroupParam
    (A : CommAlgCat.{u} ℤ) (s : Fin 1 → Aˣ) (i : Fin 2) (t : Multiplicative A) :
    rankOneTorusPoints A s * rankOneRootSubgroupParam i A t *
        (rankOneTorusPoints A s)⁻¹ =
      rankOneRootSubgroupParam i A
        (Multiplicative.ofAdd
          ((torusCharacter s (rankOneRootWeight i) : A) * Multiplicative.toAdd t)) :=
  by
    simpa only [rankOneTorusPoints, rankOneRootSubgroupParam] using
      kostantTorusPoints_conj_kostantRootSubgroupParam e h ρ M hM b rankOneWeight
        isCartanWeightVector_integralLatticeAddSubgroupBasis (lie_cartan_root_eq_smul i) (hnil i)
          A s t

end TauCeti.Sl2Std
