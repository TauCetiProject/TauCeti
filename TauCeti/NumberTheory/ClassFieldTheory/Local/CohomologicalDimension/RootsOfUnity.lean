/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.OpenSubgroup
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ClosedSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars

/-!
# The third cohomology of the roots of unity of a local field

Let `K` be a nonarchimedean local field with separable closure `Kˢ` and `G_K = Gal(Kˢ/K)`, and let
`n` be invertible in `K`. This file proves that

```text
H³(V, μₙ) = 0
```

for every closed subgroup `V` of `G_K` (`subsingleton_h3_kummerCoeff_of_isClosed`). Applied to a
Sylow pro-`ℓ` subgroup, for a prime `ℓ` invertible in `K`, it is the input of the bound
`cd_ℓ G_K ≤ 2`.

For an open subgroup `V`, with fixed field `E` a finite extension of `K`, the Kummer sequence
`1 → μₙ → (Kˢ)ˣ → (Kˢ)ˣ → 1` restricted to `V` gives the exact sequence

```text
H²(V, (Kˢ)ˣ) --n--> H²(V, (Kˢ)ˣ) --δ--> H³(V, μₙ) → H³(V, (Kˢ)ˣ).
```

The last group is `H³(G_E, (Eˢ)ˣ) = 0` (`TauCeti.ClassFieldTheory.subsingleton_h3_unitsRep` for
`E`, read on `V` through `G_E ≃ₜ* V`), and the first map is onto because `H²(V, (Kˢ)ˣ)` is
isomorphic to `ℚ/ℤ` by the local invariant of `V`
(`TauCeti.ClassFieldTheory.subgroupInvMap`), which is divisible. Hence `H³(V, μₙ) = 0`
(`subsingleton_h3_kummerCoeff_of_isOpen`). For a closed subgroup, every class of `H³(V, μₙ)` is
restricted from an open subgroup containing `V`
(`TauCeti.ContinuousCohomology.exists_openSubgroup_le_resLE_eq`).

In degree two, by contrast, `H²(G_K, μₙ) ≅ ℤ/n` by the local invariant
(`TauCeti.ClassFieldTheory.h2MuEquivZMod`), so it is nonzero for `n > 1`
(`nontrivial_h2_kummerCoeff`), which is the input of the bound `cd_ℓ G_K ≥ 2`.

## Main results

* `TauCeti.ClassFieldTheory.subsingleton_h3_unitsCoeff_of_isOpen`: `H³(V, (Kˢ)ˣ) = 0` for an
  open subgroup `V` of `G_K`.
* `TauCeti.ClassFieldTheory.surjective_coeffMap_unitsCoeffPow_two`: the `n`-th power map is
  onto on `H²(V, (Kˢ)ˣ)`.
* `TauCeti.ClassFieldTheory.nontrivial_h2_kummerCoeff`: `H²(G_K, μₙ) ≠ 0` for `n > 1`.
* `TauCeti.ClassFieldTheory.subsingleton_h3_kummerCoeff_of_isOpen`,
  `TauCeti.ClassFieldTheory.subsingleton_h3_kummerCoeff_of_isClosed`: `H³(V, μₙ) = 0` for an
  open, respectively closed, subgroup `V` of `G_K`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.3, Prop. 12.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.1.8).
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology _root_.TauCeti.ContinuousCohomology

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local instance] TopRep.distribMulAction

/-- The absolute Galois group is locally compact, being compact and Hausdorff. Instance search
does not find this within its default budget under the imports of this file, so it is assembled
here from the Krull topology being Hausdorff, as in `TauCeti.Algebra.CrossedProduct.CupProduct`. -/
local instance : LocallyCompactSpace (AbsoluteGaloisGroup K) :=
  have : R1Space (AbsoluteGaloisGroup K) := @T2Space.r1Space _ _ krullTopology_t2
  have : WeaklyLocallyCompactSpace (AbsoluteGaloisGroup K) :=
    ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace

/-- **`H³(V, (Kˢ)ˣ) = 0` for an open subgroup `V` of `G_K`.** The subgroup is the absolute Galois
group of its fixed field `E`, a finite extension of `K` and hence a nonarchimedean local field,
and `H³(G_E, (Eˢ)ˣ) = 0`. -/
theorem subsingleton_h3_unitsCoeff_of_isOpen (V : Subgroup (AbsoluteGaloisGroup K))
    (hV : IsOpen (V : Set (AbsoluteGaloisGroup K))) :
    Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ V (UnitsCoeff K))) := by
  -- `V` is the subgroup fixing its fixed field `E`, which is finite over `K`.
  obtain ⟨E, _, rfl⟩ : ∃ E : IntermediateField K (SeparableClosure K),
      FiniteDimensional K E ∧ E.val.fieldRange.fixingSubgroup = V := by
    obtain ⟨E, hE⟩ : ∃ E : IntermediateField K (SeparableClosure K), E.fixingSubgroup = V :=
      ⟨_, InfiniteGalois.fixingSubgroup_fixedField ⟨V, Subgroup.isClosed_of_isOpen V hV⟩⟩
    refine ⟨E, ?_, by rw [IntermediateField.fieldRange_val, hE]⟩
    rw [← InfiniteGalois.isOpen_iff_finite, hE]
    exact hV
  -- The canonical structure of nonarchimedean local field on `E`.
  let _ := finiteExtensionValuativeRel K E
  let _ := finiteExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  have := subsingleton_h3_unitsRep E
  have : Subsingleton (continuousCohomology 3
      (ofDiscreteModule ℤ (Field.absoluteGaloisGroup E) (unitsRep E).V)) :=
    (ofDiscreteModuleRestrictScalarsIntEquiv (unitsRep E) 3).injective.subsingleton
  -- Transport along `V ≃ₜ* G_E` and the identification of the units of the separable closures.
  let f : UnitsCoeff E ≃+ UnitsCoeff K :=
    { toFun := unitsCoeffMapSymm K E E.val
      invFun := unitsCoeffMap K E E.val
      left_inv := unitsCoeffMap_unitsCoeffMapSymm K E E.val
      right_inv := unitsCoeffMapSymm_unitsCoeffMap K E E.val
      map_add' := map_add _ }
  refine subsingleton_continuousCohomology_ofDiscreteModule_of_continuousMulEquiv
    ((absoluteGaloisGroupEquivFixingSubgroup K E E.val).symm.trans
      (absoluteGaloisGroupRestrictEquiv E).symm)
    ((unitsCoeffEquivUnitsRep E).symm.trans f).toIntLinearEquiv (fun v m => ?_) 3
  obtain ⟨m, rfl⟩ := (unitsCoeffEquivUnitsRep E).surjective m
  rw [TopRep.distribMulAction_smul, ← unitsCoeffEquivUnitsRep_smul]
  simp only [AddEquiv.coe_toIntLinearEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply, f, AddEquiv.coe_mk,
    Equiv.coe_fn_mk]
  exact unitsCoeffMapSymm_smul K E E.val v m

variable {K} {n : ℕ}

/-- **The `n`-th power map is onto on `H²(V, (Kˢ)ˣ)`** for an open subgroup `V` of `G_K`: the
local invariant of `V` identifies `H²(V, (Kˢ)ˣ)` with the divisible group `ℚ/ℤ`, and the map is
multiplication by `n`. -/
theorem surjective_coeffMap_unitsCoeffPow_two (hn : IsUnit (n : K))
    (V : Subgroup (AbsoluteGaloisGroup K)) (hV : IsOpen (V : Set (AbsoluteGaloisGroup K))) :
    Function.Surjective (coeffMap
      (ofDiscreteModuleMap ((kummerShortExact K n hn).restrict V).proj.toIntLinearMap
        ((kummerShortExact K n hn).restrict V).proj_equivariant) 2) := by
  have : V.FiniteIndex := (⟨V, hV⟩ : OpenSubgroup (AbsoluteGaloisGroup K)).finiteIndex_toSubgroup
  have : CompactSpace V := isCompact_iff_compactSpace.1
    (Subgroup.isClosed_of_isOpen V hV).isCompact
  have : LocallyCompactSpace V := (Subgroup.isClosed_of_isOpen V hV).locallyCompactSpace
  have hn0 : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.2 fun h => by simp [h] at hn
  rw [← DiscreteShortExact.ofDiscreteModuleMap_projDistribMulActionHom]
  intro y
  obtain ⟨x, rfl⟩ := (explicitH2AddEquivContinuousCohomology V (UnitsCoeff K)).surjective y
  -- divide the invariant of `x` by `n`
  let e := subgroupInvMap K V hV
  refine ⟨explicitH2AddEquivContinuousCohomology V (UnitsCoeff K)
    (e.symm (DivisibleBy.div (e x) (n : ℤ))), ?_⟩
  rw [explicitH2AddEquivContinuousCohomology_coeffMap,
    explicitCoeff2_eq_nsmul V (UnitsCoeff K) _ continuous_of_discreteTopology fun m => by
      rw [DiscreteShortExact.projDistribMulActionHom_apply, DiscreteShortExact.restrict_proj,
        kummerShortExact_proj, unitsCoeffPow_eq_nsmul]]
  congr 1
  apply e.injective
  rw [map_nsmul, AddEquiv.apply_symm_apply, ← natCast_zsmul, DivisibleBy.div_cancel _ hn0]

/-- **`H³(V, μₙ) = 0` for an open subgroup `V` of `G_K`**, for `n` invertible in `K`: by the Kummer
sequence, `H³(V, μₙ)` sits between the cokernel of `n` on `H²(V, (Kˢ)ˣ)`, which vanishes, and
`H³(V, (Kˢ)ˣ) = 0`. -/
theorem subsingleton_h3_kummerCoeff_of_isOpen (hn : IsUnit (n : K))
    (V : Subgroup (AbsoluteGaloisGroup K)) (hV : IsOpen (V : Set (AbsoluteGaloisGroup K))) :
    Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ V (KummerCoeff K n))) := by
  have : CompactSpace V := isCompact_iff_compactSpace.1
    (Subgroup.isClosed_of_isOpen V hV).isCompact
  have : LocallyCompactSpace V := (Subgroup.isClosed_of_isOpen V hV).locallyCompactSpace
  have := subsingleton_h3_unitsCoeff_of_isOpen K V hV
  set S := (kummerShortExact K n hn).restrict V
  refine subsingleton_of_forall_eq 0 fun x => ?_
  -- the image of `x` in `H³(V, (Kˢ)ˣ) = 0` vanishes, so `x = δ c`
  obtain ⟨c, rfl⟩ := (S.longExact_exact₁ 2 x).1 (Subsingleton.elim _ _)
  -- and `c` is the image of a class of `H²(V, (Kˢ)ˣ)` under the `n`-th power map, so `δ c = 0`
  obtain ⟨b, rfl⟩ := surjective_coeffMap_unitsCoeffPow_two hn V hV c
  exact (S.longExact_exact₃ 2).apply_apply_eq_zero b

/-- **`H³(V, μₙ) = 0` for a closed subgroup `V` of `G_K`**, for `n` invertible in `K`: every class
of `H³(V, μₙ)` is restricted from an open subgroup containing `V`, where `H³` vanishes. -/
theorem subsingleton_h3_kummerCoeff_of_isClosed (hn : IsUnit (n : K))
    (V : Subgroup (AbsoluteGaloisGroup K)) (hV : IsClosed (V : Set (AbsoluteGaloisGroup K))) :
    Subsingleton (continuousCohomology 3 (ofDiscreteModule ℤ V (KummerCoeff K n))) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨W, hVW, x, rfl⟩ := exists_openSubgroup_le_resLE_eq
    (ofDiscreteModule_isSmoothDiscrete ℤ (AbsoluteGaloisGroup K) (KummerCoeff K n)) hV y
  have : Subsingleton (continuousCohomology 3
      (TopRep.res ((W : Subgroup (AbsoluteGaloisGroup K)).subtype :
          (W : Subgroup (AbsoluteGaloisGroup K)) →* AbsoluteGaloisGroup K)
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K n)))) :=
    subsingleton_h3_kummerCoeff_of_isOpen hn (W : Subgroup (AbsoluteGaloisGroup K)) W.isOpen
  rw [Subsingleton.elim x 0]
  exact map_zero _

/-- **`H²(G_K, μₙ)` is nonzero** for `1 < n` invertible in `K`: the local invariant identifies it
with `ℤ/n` (`h2MuEquivZMod`). -/
theorem nontrivial_h2_kummerCoeff (hn : IsUnit (n : K)) (h1 : 1 < n) :
    Nontrivial (continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (KummerCoeff K n))) := by
  have : Fact (1 < n) := ⟨h1⟩
  exact ((((explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup K)
    (KummerCoeff K n)).symm.trans (muNRepH2Equiv n K)).trans
      (h2MuEquivZMod K hn)).toEquiv.nontrivial)

end TauCeti.ClassFieldTheory
