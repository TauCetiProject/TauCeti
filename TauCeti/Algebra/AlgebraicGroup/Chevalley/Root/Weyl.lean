/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coroot
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

where `h_γ = D.corootPoints γ A` is the coroot of `γ` in the actual torus of `D`. In particular
`h_γ(s) = n_γ(s) n_γ(1)⁻¹` is multiplicative in `s`. These are the rank-one relations of
Steinberg's presentation of a Chevalley group, at every root rather than only at the simple ones,
over every commutative ring.

The quotient relation is Chevalley's identity
`TauCeti.DynkinType.chevalleyRootSubgroup_mul_mul_eq_kostantTorusPoints_mul` read in the weight
basis of the datum. The conjugation relation applies the integral Kostant rank-one relation
`kostantWeylParam_conj_kostantRootSubgroupParam_e` to the named Chevalley root vectors `e_{±γ}`
and the Killing coroot of `γ`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.weylElement_eq_corootPoints_mul`: `n_γ(s) = h_γ(s) n_γ(1)`.
* `TauCeti.DynkinType.ChevalleyDatum.weylElement_mul_inv_weylElement`:
  `n_γ(s) n_γ(s')⁻¹ = h_γ(s s'⁻¹)`.
* `TauCeti.DynkinType.ChevalleyDatum.weylElement_mul_inv_mul_weylElement_mul_inv`:
  `h_γ(s) h_γ(s') = h_γ(s s')` for `h_γ(s) = n_γ(s) n_γ(1)⁻¹`.
* `TauCeti.DynkinType.ChevalleyDatum.weylElement_conj_rootSubgroupPoints_self`:
  `n_γ(s) x_γ(u) n_γ(s)⁻¹ = x_{-γ}(-s⁻² u)`.
* `TauCeti.DynkinType.ChevalleyDatum.weylElement_simpleIndex_conj_rootSubgroupPoints`:
  `n_{αᵢ}(s) x_γ(u) n_{αᵢ}(s)⁻¹ = x_{sᵢγ}(s ^ ⟨sᵢγ, αᵢ^∨⟩ ε u)` for a simple root `αᵢ`.

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

/-- **Chevalley's identity at every root**: `n_γ(s) = h_γ(s) n_γ(1)`, with `h_γ` the coroot of
`γ` in the actual torus of the datum. -/
theorem weylElement_eq_corootPoints_mul (s : Aˣ) :
    D.weylElement γ A s = D.corootPoints γ A s * D.weylElement γ A 1 := by
  have h := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom)
    (chevalleyRootSubgroup_mul_mul_eq_kostantTorusPoints_mul D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator D.basis D.weight
      D.isCartanWeightVector_basis γ (CommAlgCat.of ℤ A) s)
  apply Subtype.ext
  simpa only [map_mul, Subgroup.coe_mul, weylElement_def, coe_rootSubgroupPoints,
    corootPoints_apply, coe_torusPoints, MulEquiv.toMonoidHom_eq_coe, ← kostantTorusMatrix_weight,
    basisMatrix_kostantTorusPoints, inv_one, Units.val_one] using h

/-- **Chevalley's identity at a simple root in actual torus coordinates**:
`nᵢ(s) = torusPoints (simpleCorootParameter i s) * nᵢ(1)` over every commutative ring. -/
theorem weylElement_simpleIndex_eq_torusPoints_mul (i : Fin t.rank) (s : Aˣ) :
    D.weylElement (t.simpleIndex ht i) A s =
      D.torusPoints A (D.simpleCorootParameter i A s) *
        D.weylElement (t.simpleIndex ht i) A 1 := by
  rw [D.weylElement_eq_corootPoints_mul, ← D.simpleCorootPoints_eq_corootPoints,
    D.simpleCorootPoints_eq_torusPoints]

/-- Conjugating by a coroot value rescales each root parameter by `s` raised to the
corresponding Cartan integer. -/
theorem corootPoints_conj_rootSubgroupPoints (β : Fin t.numRoots) (s : Aˣ) (u : A) :
    D.corootPoints γ A s * D.rootSubgroupPoints β A (ofAdd u) *
        (D.corootPoints γ A s)⁻¹ =
      D.rootSubgroupPoints β A (ofAdd
        (((s ^ (t.simplyConnectedRootDatum ht).pairing β γ : Aˣ) : A) * u)) := by
  rw [corootPoints_eq_torusPoints, D.torusPoints_conj_rootSubgroupPoints,
    D.torusCharacter_corootParameter_coordinateRoot]

/-- **Quotients of Steinberg's elements are coroot values.** For units `s` and `s'`,
`n_γ(s) n_γ(s')⁻¹ = h_γ(s s'⁻¹)`, with `h_γ` the coroot of `γ` in the actual torus of the
datum. -/
theorem weylElement_mul_inv_weylElement (s s' : Aˣ) :
    D.weylElement γ A s * (D.weylElement γ A s')⁻¹ = D.corootPoints γ A (s * s'⁻¹) := by
  rw [D.weylElement_eq_corootPoints_mul γ A s, D.weylElement_eq_corootPoints_mul γ A s',
    mul_inv_rev, mul_assoc, mul_inv_cancel_left, map_mul, map_inv]

/-- **Steinberg's coroot words are multiplicative.** Writing `h_γ(s) = n_γ(s) n_γ(1)⁻¹`, one has
`h_γ(s) h_γ(s') = h_γ(s s')` for all units `s` and `s'`. -/
theorem weylElement_mul_inv_mul_weylElement_mul_inv (s s' : Aˣ) :
    D.weylElement γ A s * (D.weylElement γ A 1)⁻¹ *
        (D.weylElement γ A s' * (D.weylElement γ A 1)⁻¹) =
      D.weylElement γ A (s * s') * (D.weylElement γ A 1)⁻¹ := by
  simp only [weylElement_mul_inv_weylElement, inv_one, mul_one, map_mul]

/-- **Steinberg's rank-one relation at every root**:
`n_γ(s) x_γ(u) n_γ(s)⁻¹ = x_{-γ}(-s⁻² u)` for every unit `s`, over every commutative ring. -/
theorem weylElement_conj_rootSubgroupPoints_self (s : Aˣ) (u : A) :
    D.weylElement γ A s * D.rootSubgroupPoints γ A (ofAdd u) * (D.weylElement γ A s)⁻¹ =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) A
        (ofAdd (-(((s⁻¹ : Aˣ) : A) ^ 2 * u))) := by
  -- Apply the Kostant relation to the single Cartan vector of the coroot of `γ`.
  have h := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMulEquiv.toMonoidHom)
    (kostantWeylParam_conj_kostantRootSubgroupParam_e (t.chevalleySystem ht)
      (fun _ : Unit => ((coroot (t.rootEquiv ht γ : LieModule.Weight ℚ (t.cartanSubalgebra ht)
        (t.lieAlgebra ht)) : t.cartanSubalgebra ht) : t.lieAlgebra ht))
      D.representation D.lattice
      (fun _ hz _ hw => kostantForm_chevalleySystem_coroot_apply_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ hz hw)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator γ)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator _) D.basis
      (fun j _ => ∑ i, (t.simplyConnectedRootDatum ht).coroot γ i * D.weight j i)
      (fun j => isCartanWeightVector_coroot_rootEquiv D.representation
        (D.isCartanWeightVector_basis j) γ) (c := ())
      ((t.isSl2Triple_chevalleySystem ht γ).map
        (D.representation.toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))
        (fun hz => (t.isSl2Triple_chevalleySystem ht γ).h_ne_zero
          (D.injective_representation_ι (by simpa using hz))))
      (fun _ => (t.isSl2Triple_chevalleySystem ht γ).lie_h_e_smul ℚ)
      (fun _ => (t.isSl2Triple_chevalleySystem ht γ).lie_lie_smul_f ℚ)
      (CommAlgCat.of ℤ A) s u)
  simp only [kostantWeylParam_def,
    kostantRootSubgroupParam_coroot_eq_chevalleyRootSubgroup D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ _
      (CommAlgCat.of ℤ A)] at h
  apply Subtype.ext
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, weylElement_def,
    coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using h

/-- **Conjugation by a simple Weyl element.** For a simple root `αᵢ`, a unit `s` and every root
`γ`, `n_{αᵢ}(s) x_γ(u) n_{αᵢ}(s)⁻¹ = x_{sᵢγ}(s ^ ⟨sᵢγ, αᵢ^∨⟩ ε u)`, where `sᵢγ` is the reflection
of `γ` in `αᵢ` and `ε = ±1` is the sign `TauCeti.DynkinType.chevalleyWeylSign` of the pinned
Chevalley system. -/
theorem weylElement_simpleIndex_conj_rootSubgroupPoints (i : Fin t.rank) (s : Aˣ) (u : A) :
    D.weylElement (t.simpleIndex ht i) A s * D.rootSubgroupPoints γ A (ofAdd u) *
        (D.weylElement (t.simpleIndex ht i) A s)⁻¹ =
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ)
        A (ofAdd (((s ^ (t.simplyConnectedRootDatum ht).pairing
            ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) γ)
            (t.simpleIndex ht i) : Aˣ) : A) *
          (((t.chevalleyWeylSign ht (t.simpleIndex ht i) γ : ℤ) : A) * u))) := by
  rw [← D.corootPoints_conj_rootSubgroupPoints (t.simpleIndex ht i) A _ s,
    ← D.weylElement_conj_rootSubgroupPoints i γ A u, D.weylElement_eq_corootPoints_mul _ A s]
  group

end

end TauCeti.DynkinType.ChevalleyDatum
