/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Coroot
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Gauss

/-!
# Gauss factorization at every Chevalley root

For a Chevalley datum, opposite root elements can be collected in either order whenever
`u = 1 + r * s` is a unit. The resulting three factors are an opposite root element, the
coroot value at `u` or `u⁻¹`, and a root element. These are the rank-one coordinate changes used in
big-cell calculations. The formulas hold over every commutative ring, including nonreduced
rings; neither root parameter needs to be a unit.

The middle factor is evaluated in the datum's actual character-lattice torus, by restricting
the full-weight coroot parameter. No surjectivity of this restriction, generation of all
scheme points, or simply connectedness of the datum is assumed.

The proof applies the integral Kostant Gauss identity
`kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f` to the named Chevalley root vectors
and the chosen root's Killing coroot. Admissibility and the integral coroot coordinates come
from `kostantForm_chevalleySystem_coroot_apply_mem` and
`apply_ι_coroot_rootEquiv_of_isCartanWeightVector`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–20, and Chapter 5.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TensorProduct Multiplicative
open LieAlgebra LieAlgebra.IsKilling
open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

universe v

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (α : Fin t.numRoots) (A : Type v) [CommRing A]

/-- Opposite root elements admit a Gauss factorization if `1 + r * s` is a unit.
The coroot is evaluated in the actual torus of the datum, even for a proper weight lattice. -/
theorem rootSubgroupPoints_mul_opposite_eq_gauss (r s : A) (u : Aˣ)
    (hu : (u : A) = 1 + r * s) :
    D.rootSubgroupPoints α A (ofAdd r) *
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A (ofAdd s) =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A
          (ofAdd (s * ↑u⁻¹)) *
        D.torusPoints A (D.fullWeightTorusRestriction A
          (fun i => u ^ (t.simplyConnectedRootDatum ht).coroot α i)) *
        D.rootSubgroupPoints α A (ofAdd (r * ↑u⁻¹)) := by
  -- Use a single Cartan generator, the chosen coroot, in the integral Gauss identity.
  let H : Unit → t.lieAlgebra ht := fun _ =>
    ((coroot (t.rootEquiv ht α : LieModule.Weight ℚ (t.cartanSubalgebra ht)
      (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht)
  let W : Fin D.dim → Unit → ℤ := fun j _ =>
    ∑ i, (t.simplyConnectedRootDatum ht).coroot α i * D.weight j i
  let hM := fun z hz w hw => kostantForm_chevalleySystem_coroot_apply_mem
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator α (u := z) hz (v := w) hw
  have hw j : IsCartanWeightVector H D.representation (W j) (D.basis j : D) := by
    rw [isCartanWeightVector_iff]
    exact fun _ => apply_ι_coroot_rootEquiv_of_isCartanWeightVector D.representation
      (D.isCartanWeightVector_basis j) α
  have hT := (t.isSl2Triple_chevalleySystem ht α).map
    (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))
    (fun hz => (t.isSl2Triple_chevalleySystem ht α).h_ne_zero
      (D.injective_representation_ι (by simpa using hz)))
  have hpos : ∀ j, ⁅H j, t.chevalleySystem ht α⁆ = ((fun _ : Unit => 2) j : ℚ) •
      t.chevalleySystem ht α := fun _ => (t.isSl2Triple_chevalleySystem ht α).lie_h_e_smul ℚ
  have hneg : ∀ j, ⁅H j, t.chevalleySystem ht
      ((t.simplyConnectedRootDatum ht).reflectionPerm α α)⁆ =
      -(((fun _ : Unit => 2) j : ℚ) • t.chevalleySystem ht
        ((t.simplyConnectedRootDatum ht).reflectionPerm α α)) := fun _ =>
    (t.isSl2Triple_chevalleySystem ht α).lie_lie_smul_f ℚ
  have hg := kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f
    (t.chevalleySystem ht) H D.representation D.lattice hM
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator α)
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator _)
    D.basis W hw (c := ()) hT hpos hneg (CommAlgCat.of ℤ A) r s u hu
  -- Identify the re-presented root maps and coroot action before taking matrices.
  have hx (γ : Fin t.numRoots) (a : Multiplicative A) :
      kostantRootSubgroupParam (t.chevalleySystem ht) H D.representation D.lattice hM γ
        (isNilpotent_apply_ι_chevalleySystem D.representation
          D.isNilpotent_representation_rootGenerator γ) (CommAlgCat.of ℤ A) a =
      chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A) a := by
    refine Units.ext (LinearMap.ext fun z => ?_)
    rw [kostantRootSubgroupParam_val_apply, chevalleyRootSubgroup_val]
  have htorus : kostantCoordinateCocharacter D.lattice D.basis W (CommAlgCat.of ℤ A) () u =
      kostantTorusPoints D.lattice D.basis D.weight (CommAlgCat.of ℤ A)
        (fun i => u ^ (t.simplyConnectedRootDatum ht).coroot α i) := by
    refine Units.ext (Module.Basis.ext (D.basis.baseChange A) fun j => ?_)
    simp only [Module.Basis.baseChange_apply, kostantCoordinateCocharacter_tmul_basis,
      kostantTorusPoints_tmul_basis, W, torusCharacter_def, ← zpow_mul,
      Finset.prod_zpow_eq_zpow_sum]
  rw [hx, hx, hx, hx, htorus] at hg
  have hm := congrArg (fun g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice) =>
    Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom g) hg
  apply Subtype.ext
  simpa only [map_mul, Subgroup.coe_mul, coe_rootSubgroupPoints, coe_torusPoints,
    MulEquiv.toMonoidHom_eq_coe, ← kostantTorusMatrix_weight,
    basisMatrix_kostantTorusPoints] using hm

/-- The reverse-order Gauss factorization has the inverse coroot in the middle.
Only `1 + r * s`, rather than either additive root parameter, must be invertible. -/
theorem opposite_mul_rootSubgroupPoints_eq_gauss (r s : A) (u : Aˣ)
    (hu : (u : A) = 1 + r * s) :
    D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A (ofAdd s) *
        D.rootSubgroupPoints α A (ofAdd r) =
      D.rootSubgroupPoints α A (ofAdd (r * ↑u⁻¹)) *
        D.torusPoints A (D.fullWeightTorusRestriction A
          (fun i => u⁻¹ ^ (t.simplyConnectedRootDatum ht).coroot α i)) *
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm α α) A
          (ofAdd (s * ↑u⁻¹)) := by
  have h := congrArg Inv.inv (D.rootSubgroupPoints_mul_opposite_eq_gauss α A (-r) (-s) u
    (by simpa only [neg_mul_neg] using hu))
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, neg_mul, Pi.inv_def,
    ← zpow_neg, inv_zpow, mul_assoc] using h

end

end TauCeti.DynkinType.ChevalleyDatum
