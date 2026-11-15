/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Coroot
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# Steinberg's rank-one relations at every root of a Chevalley datum

For a Chevalley datum `D`, a root `γ` and a unit `s` of a commutative ring `A`, Steinberg's
element `n_γ(s) = x_γ(s) x_{-γ}(-s⁻¹) x_γ(s)` of `D.points A` satisfies

```text
n_γ(s) n_γ(s')⁻¹ = h_γ(s s'⁻¹),        n_γ(s) x_γ(u) n_γ(s)⁻¹ = x_{-γ}(-s⁻² u),
```

where `h_γ(v)` is the point of the actual torus of `D` obtained by restricting the full-weight
parameter `i ↦ v ^ γ^∨(i)` to the weight lattice of `D`. In particular
`h_γ(s) = n_γ(s) n_γ(1)⁻¹` is multiplicative in `s`. These are the rank-one relations of
Steinberg's presentation of a Chevalley group, at every root rather than only at the simple ones,
over every commutative ring.

The proof applies the integral Kostant rank-one relations
`kostantWeylParam_mul_inv_kostantWeylParam` and `kostantWeylParam_conj_kostantRootSubgroupParam_e`
to the named Chevalley root vectors `e_{±γ}` and the Killing coroot of `γ`, as in the Gauss
factorization `ChevalleyDatum.rootSubgroupPoints_mul_opposite_eq_gauss`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.weylElement_mul_inv_weylElement`:
  `n_γ(s) n_γ(s')⁻¹ = h_γ(s s'⁻¹)`.
* `TauCeti.DynkinType.ChevalleyDatum.weylElement_eq_torusPoints_mul`: `n_γ(s) = h_γ(s) n_γ(1)`.
* `TauCeti.DynkinType.ChevalleyDatum.weylElement_mul_inv_mul_weylElement_mul_inv`:
  `h_γ(s) h_γ(s') = h_γ(s s')` for `h_γ(s) = n_γ(s) n_γ(1)⁻¹`.
* `TauCeti.DynkinType.ChevalleyDatum.weylElement_conj_rootSubgroupPoints_self`:
  `n_γ(s) x_γ(u) n_γ(s)⁻¹ = x_{-γ}(-s⁻² u)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 20, and Chapter 6.
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
variable (γ : Fin t.numRoots) (A : Type v) [CommRing A]

/-! ### The rank-one Kostant data of a root

The integral rank-one relations are applied to the root vectors `e_{±γ}` and the single Cartan
vector given by the Killing coroot of `γ`, on which the weight basis of the datum has the integral
weights `j ↦ ⟨wt j, γ^∨⟩`. -/

/-- The Killing coroot of `γ`, as the single Cartan vector of the rank-one Kostant data. -/
private noncomputable def corootFamily (γ : Fin t.numRoots) : Unit → t.lieAlgebra ht :=
  fun _ => ((coroot (t.rootEquiv ht γ : LieModule.Weight ℚ (t.cartanSubalgebra ht)
    (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht)

/-- The weights of the weight basis of the datum on the coroot of `γ`. -/
private def corootWeight : Fin D.dim → Unit → ℤ :=
  fun j _ => ∑ i, (t.simplyConnectedRootDatum ht).coroot γ i * D.weight j i

private theorem corootFamily_apply_mem :
    ∀ z ∈ UniversalEnvelopingAlgebra.kostantForm (t.chevalleySystem ht)
    (corootFamily (ht := ht) γ), ∀ w ∈ D.lattice, D.representation z w ∈ D.lattice :=
  fun _ hz _ hw => kostantForm_chevalleySystem_coroot_apply_mem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ hz hw

private theorem isCartanWeightVector_corootWeight (j : Fin D.dim) :
    IsCartanWeightVector (corootFamily (ht := ht) γ) D.representation (D.corootWeight γ j)
      (D.basis j : D) := by
  rw [isCartanWeightVector_iff]
  exact fun _ => apply_ι_coroot_rootEquiv_of_isCartanWeightVector D.representation
    (D.isCartanWeightVector_basis j) γ

private theorem isSl2Triple_corootFamily :
    IsSl2Triple (D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (corootFamily (ht := ht) γ ())))
      (D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ)))
      (D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)))) :=
  (t.isSl2Triple_chevalleySystem ht γ).map
    (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))
    (fun hz => (t.isSl2Triple_chevalleySystem ht γ).h_ne_zero
      (D.injective_representation_ι (by simpa using hz)))

private theorem lie_corootFamily_chevalleySystem (j : Unit) :
    ⁅corootFamily (ht := ht) γ j, t.chevalleySystem ht γ⁆ =
      (((fun _ : Unit => (2 : ℤ)) j : ℤ) : ℚ) • t.chevalleySystem ht γ := by
  simpa [corootFamily] using (t.isSl2Triple_chevalleySystem ht γ).lie_h_e_smul ℚ

private theorem lie_corootFamily_chevalleySystem_neg (j : Unit) :
    ⁅corootFamily (ht := ht) γ j,
        t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)⁆ =
      -((((fun _ : Unit => (2 : ℤ)) j : ℤ) : ℚ) •
        t.chevalleySystem ht ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)) := by
  simpa [corootFamily] using (t.isSl2Triple_chevalleySystem ht γ).lie_lie_smul_f ℚ

private theorem kostantRootSubgroupParam_corootFamily (δ : Fin t.numRoots)
    (a : Multiplicative A) :
    kostantRootSubgroupParam (t.chevalleySystem ht) (corootFamily γ) D.representation D.lattice
        (D.corootFamily_apply_mem γ) δ (isNilpotent_apply_ι_chevalleySystem D.representation
          D.isNilpotent_representation_rootGenerator δ) (CommAlgCat.of ℤ A) a =
      chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator δ (CommAlgCat.of ℤ A) a := by
  refine Units.ext (LinearMap.ext fun z => ?_)
  rw [kostantRootSubgroupParam_val_apply, chevalleyRootSubgroup_val]

private theorem kostantCoordinateCocharacter_corootWeight (v : Aˣ) :
    kostantCoordinateCocharacter D.lattice D.basis (D.corootWeight γ) (CommAlgCat.of ℤ A) () v =
      kostantTorusPoints D.lattice D.basis D.weight (CommAlgCat.of ℤ A)
        (fun i => v ^ (t.simplyConnectedRootDatum ht).coroot γ i) := by
  refine Units.ext (Module.Basis.ext (D.basis.baseChange A) fun j => ?_)
  simp only [Module.Basis.baseChange_apply, kostantCoordinateCocharacter_tmul_basis,
    kostantTorusPoints_tmul_basis, corootWeight, torusCharacter_def, ← zpow_mul,
    Finset.prod_zpow_eq_zpow_sum]

private theorem basisMatrix_kostantWeylParam_corootFamily (v : Aˣ) :
    Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom
        (kostantWeylParam (t.chevalleySystem ht) (corootFamily γ) D.representation D.lattice
          (D.corootFamily_apply_mem γ) (isNilpotent_apply_ι_chevalleySystem D.representation
            D.isNilpotent_representation_rootGenerator γ)
          (isNilpotent_apply_ι_chevalleySystem D.representation
            D.isNilpotent_representation_rootGenerator
            ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ)) (CommAlgCat.of ℤ A) v) =
      (D.weylElement γ A v : Matrix.GeneralLinearGroup (Fin D.dim) A) := by
  rw [kostantWeylParam_def, map_mul, map_mul, kostantRootSubgroupParam_corootFamily,
    kostantRootSubgroupParam_corootFamily]
  simp only [weylElement_def, Subgroup.coe_mul, coe_rootSubgroupPoints,
    MulEquiv.toMonoidHom_eq_coe]

/-! ### The rank-one relations -/

/-- **Quotients of Steinberg's elements are coroot values.** For units `s` and `s'`,
`n_γ(s) n_γ(s')⁻¹ = h_γ(s s'⁻¹)`, where `h_γ(v)` is the point of the actual torus obtained by
restricting the full-weight parameter `i ↦ v ^ γ^∨(i)` to the weight lattice of the datum. -/
theorem weylElement_mul_inv_weylElement (s s' : Aˣ) :
    D.weylElement γ A s * (D.weylElement γ A s')⁻¹ =
      D.torusPoints A (D.fullWeightTorusRestriction A
        (fun i => (s * s'⁻¹) ^ (t.simplyConnectedRootDatum ht).coroot γ i)) := by
  apply Subtype.ext
  have h := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom)
    (kostantWeylParam_mul_inv_kostantWeylParam (t.chevalleySystem ht) (corootFamily γ)
      D.representation D.lattice (D.corootFamily_apply_mem γ)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator γ)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator _) D.basis (D.corootWeight γ)
      (D.isCartanWeightVector_corootWeight γ) (c := ()) (D.isSl2Triple_corootFamily γ)
      (lie_corootFamily_chevalleySystem γ) (lie_corootFamily_chevalleySystem_neg γ)
      (CommAlgCat.of ℤ A) s s')
  rw [kostantCoordinateCocharacter_corootWeight, map_mul, map_inv,
    basisMatrix_kostantWeylParam_corootFamily, basisMatrix_kostantWeylParam_corootFamily] at h
  rw [Subgroup.coe_mul, Subgroup.coe_inv, h, coe_torusPoints, ← kostantTorusMatrix_weight,
    ← basisMatrix_kostantTorusPoints]
  rfl

/-- **Chevalley's identity at every root**: `n_γ(s) = h_γ(s) n_γ(1)`, with `h_γ(s)` the point of
the actual torus obtained by restricting the full-weight parameter `i ↦ s ^ γ^∨(i)`. -/
theorem weylElement_eq_torusPoints_mul (s : Aˣ) :
    D.weylElement γ A s =
      D.torusPoints A (D.fullWeightTorusRestriction A
        (fun i => s ^ (t.simplyConnectedRootDatum ht).coroot γ i)) * D.weylElement γ A 1 := by
  have h := D.weylElement_mul_inv_weylElement γ A s 1
  rw [inv_one, mul_one] at h
  rw [← h, inv_mul_cancel_right]

/-- **Steinberg's coroot words are multiplicative.** Writing `h_γ(s) = n_γ(s) n_γ(1)⁻¹`, one has
`h_γ(s) h_γ(s') = h_γ(s s')` for all units `s` and `s'`. -/
theorem weylElement_mul_inv_mul_weylElement_mul_inv (s s' : Aˣ) :
    D.weylElement γ A s * (D.weylElement γ A 1)⁻¹ *
        (D.weylElement γ A s' * (D.weylElement γ A 1)⁻¹) =
      D.weylElement γ A (s * s') * (D.weylElement γ A 1)⁻¹ := by
  simp only [weylElement_mul_inv_weylElement, inv_one, mul_one, ← map_mul]
  congr 2
  funext i
  simp [mul_zpow]

/-- **Steinberg's rank-one relation at every root**:
`n_γ(s) x_γ(u) n_γ(s)⁻¹ = x_{-γ}(-s⁻² u)` for every unit `s`, over every commutative ring. -/
theorem weylElement_conj_rootSubgroupPoints_self (s : Aˣ) (u : A) :
    D.weylElement γ A s * D.rootSubgroupPoints γ A (ofAdd u) * (D.weylElement γ A s)⁻¹ =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) A
        (ofAdd (-(((s⁻¹ : Aˣ) : A) ^ 2 * u))) := by
  apply Subtype.ext
  have h := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom)
    (kostantWeylParam_conj_kostantRootSubgroupParam_e (t.chevalleySystem ht) (corootFamily γ)
      D.representation D.lattice (D.corootFamily_apply_mem γ)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator γ)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator _) D.basis (D.corootWeight γ)
      (D.isCartanWeightVector_corootWeight γ) (c := ()) (D.isSl2Triple_corootFamily γ)
      (lie_corootFamily_chevalleySystem γ) (lie_corootFamily_chevalleySystem_neg γ)
      (CommAlgCat.of ℤ A) s u)
  rw [kostantRootSubgroupParam_corootFamily, kostantRootSubgroupParam_corootFamily, map_mul,
    map_mul, map_inv, basisMatrix_kostantWeylParam_corootFamily] at h
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_rootSubgroupPoints,
    coe_rootSubgroupPoints]
  exact h

end

end TauCeti.DynkinType.ChevalleyDatum
