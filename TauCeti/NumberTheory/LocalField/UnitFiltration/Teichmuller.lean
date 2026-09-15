/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.Valuation.RootsOfUnity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Teichmuller

/-!
# Teichmüller representatives of a local field

For a nonarchimedean local field `K`, this file constructs the Teichmüller lift

`TauCeti.teichmullerLift K : 𝓀[K] →*₀ 𝒪[K]`

and its restriction

`TauCeti.teichmuller K : 𝓀[K]ˣ →* 𝒪[K]ˣ`

to the multiplicative groups. The latter is the unique monoid-homomorphic section of reduction,
and its values are precisely the units of `𝒪[K]` killed by the exponent `q - 1`, where
`q = Nat.card 𝓀[K]`. These representatives identify the multiplicative group of the residue field
with the `(q - 1)`-st roots of unity in both `𝒪[K]` and `K`, the latter through the comparison
`TauCeti.integerRootsOfUnityEquivRootsOfUnity`.

## Main definitions

* `TauCeti.teichmullerLift`: the zero-preserving multiplicative lift from the residue field.
* `TauCeti.teichmuller`: the Teichmüller section on unit groups.
* `TauCeti.teichmullerEquivIntegerRootsOfUnity`: the equivalence with the roots of unity in
  `𝒪[K]`.
* `TauCeti.teichmullerEquivRootsOfUnity`: the equivalence with the roots of unity in `K`.

## Main results

* `TauCeti.teichmuller_section`: the Teichmüller map is a section of reduction.
* `TauCeti.teichmullerLift_pow_card`: each Teichmüller representative is fixed by the `q`-th power
  map.
* `TauCeti.teichmullerLift_unique`: the Teichmüller lift is the only zero-preserving multiplicative
  section of reduction.
* `TauCeti.eq_teichmuller_iff`: a unit is the representative of `a` exactly when it reduces to
  `a` and its `(q - 1)`-st power is one.
* `TauCeti.teichmuller_unique`: the Teichmüller map is the only monoid-homomorphic section of
  reduction.
* `TauCeti.range_teichmuller`: its range is the `(q - 1)`-st roots of unity in `𝒪[K]`.

## Implementation notes

The construction specializes Mathlib's `Perfection.teichmuller₀`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- Provenance: this is the finite-residue-field specialization of Mathlib's
-- `Perfection.teichmuller₀`, using `PerfectionMap.id` to identify a perfect field with its
-- perfection.
/-- The Teichmüller lift from the residue field of `K` to its ring of integers. It preserves zero
and multiplication and is a section of reduction. -/
noncomputable def teichmullerLift (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : 𝓀[K] →*₀ 𝒪[K] := by
  let p := ringChar 𝓀[K]
  letI : Fact p.Prime := ⟨CharP.prime_ringChar 𝓀[K]⟩
  letI : PerfectRing 𝓀[K] p := PerfectField.toPerfectRing p
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  have h : Perfection 𝓀[K] p →*₀ 𝒪[K] := Perfection.teichmuller₀ p 𝓂[K]
  exact h.comp (PerfectionMap.id p 𝓀[K]).equiv.toMonoidWithZeroHom

/-- Reduction of a Teichmüller lift is the original residue-field element. -/
@[simp]
theorem residue_teichmullerLift (a : 𝓀[K]) :
    IsLocalRing.residue 𝒪[K] (teichmullerLift K a) = a := by
  let p := ringChar 𝓀[K]
  let _ : Fact p.Prime := ⟨CharP.prime_ringChar 𝓀[K]⟩
  let _ : PerfectRing 𝓀[K] p := PerfectField.toPerfectRing p
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  let _ := isUniformAddGroup_of_addCommGroup (G := K)
  let e := (PerfectionMap.id p 𝓀[K]).equiv
  exact (Perfection.mk_teichmuller₀ (e a)).trans
    (PerfectionMap.comp_equiv (PerfectionMap.id p 𝓀[K]) a)

/-- Each Teichmüller representative is fixed by the `q`-th power map, where `q = Nat.card 𝓀[K]`.

This is not a `simp` lemma: `simp` normalizes `Nat.card 𝓀[K]` to `Fintype.card 𝓀[K]`, so the
left-hand side is not in `simp`-normal form. -/
theorem teichmullerLift_pow_card (a : 𝓀[K]) :
    teichmullerLift K a ^ Nat.card 𝓀[K] = teichmullerLift K a := by
  classical
  let _ := Fintype.ofFinite 𝓀[K]
  rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

/-- The Teichmüller section on unit groups, from the units of the residue field to the units of the
ring of integers. -/
noncomputable def teichmuller (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : 𝓀[K]ˣ →* 𝒪[K]ˣ :=
  Units.map (teichmullerLift K).toMonoidHom

/-- The Teichmüller section on unit groups is the Teichmüller lift on underlying elements. -/
@[simp]
theorem coe_teichmuller_apply (a : 𝓀[K]ˣ) :
    ((teichmuller K a : 𝒪[K]ˣ) : 𝒪[K]) = teichmullerLift K (a : 𝓀[K]) :=
  -- `teichmuller` is `Units.map` of the lift, so this is `Units.coe_map`. The parentheses are the
  -- module system's: the body of `teichmuller` is not `@[expose]`d, so a bare `rfl`, whose proof
  -- term is exported, does not elaborate outside this module.
  (rfl)

/-- The Teichmüller map is a section of reduction on unit groups. -/
@[simp]
theorem teichmuller_section (a : 𝓀[K]ˣ) :
    Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) (teichmuller K a) = a := by
  ext
  exact residue_teichmullerLift (K := K) a

/-- The Teichmüller section is injective. -/
theorem teichmuller_injective : Function.Injective (teichmuller K) :=
  Function.LeftInverse.injective (teichmuller_section (K := K))

private theorem units_pow_card_sub_one_eq_one (a : 𝓀[K]ˣ) :
    a ^ (Nat.card 𝓀[K] - 1) = 1 := by
  classical
  let _ := Fintype.ofFinite 𝓀[K]
  rw [Nat.card_eq_fintype_card]
  apply Units.ext
  exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero a)

/-- Every Teichmüller representative is a `(q - 1)`-st root of unity, where
`q = Nat.card 𝓀[K]`.

This is not a `simp` lemma: `simp` normalizes `Nat.card 𝓀[K]` to `Fintype.card 𝓀[K]`, so the
left-hand side is not in `simp`-normal form. -/
theorem teichmuller_pow_card_sub_one (a : 𝓀[K]ˣ) :
    teichmuller K a ^ (Nat.card 𝓀[K] - 1) = 1 := by
  rw [← map_pow, units_pow_card_sub_one_eq_one, map_one]

private theorem eq_one_of_residue_eq_one_of_pow_card_sub_one_eq_one
    (u : 𝒪[K]ˣ)
    (hres : Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u = 1)
    (hpow : u ^ (Nat.card 𝓀[K] - 1) = 1) : u = 1 := by
  classical
  let _ := Fintype.ofFinite 𝓀[K]
  let q := Nat.card 𝓀[K]
  let s : 𝒪[K] := ∑ i ∈ Finset.range (q - 1), (u : 𝒪[K]) ^ i
  have hu_res : IsLocalRing.residue 𝒪[K] (u : 𝒪[K]) = 1 := by
    have hu_res := congrArg Units.val hres
    simpa only [Units.coe_map, Units.val_one, MonoidHom.coe_coe] using hu_res
  have hs_res : IsLocalRing.residue 𝒪[K] s = -1 := by
    simp only [s]
    rw [map_sum]
    simp_rw [map_pow, hu_res, one_pow]
    rw [Finset.sum_const, nsmul_one, Finset.card_range, Nat.cast_sub]
    · simp only [q, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero, zero_sub,
        Nat.cast_one]
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  have hs : s ≠ 0 := by
    intro hs
    rw [hs, map_zero] at hs_res
    exact (neg_ne_zero.mpr one_ne_zero) hs_res.symm
  apply Units.ext
  apply sub_eq_zero.mp
  have hu_pow : (u : 𝒪[K]) ^ (q - 1) = 1 := by
    simpa only [q, Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hpow
  have hprod : ((u : 𝒪[K]) - 1) * s = 0 := by
    simp only [s]
    rw [mul_geom_sum, hu_pow, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_right hs

/-- A unit of `𝒪[K]` is the Teichmüller representative of its reduction if it is killed by the
exponent `q - 1`. -/
theorem eq_teichmuller_of_residue_eq_of_pow_card_sub_one_eq_one
    (u : 𝒪[K]ˣ) (a : 𝓀[K]ˣ)
    (hres : Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u = a)
    (hpow : u ^ (Nat.card 𝓀[K] - 1) = 1) : u = teichmuller K a := by
  apply mul_right_cancel (b := (teichmuller K a)⁻¹)
  rw [mul_inv_cancel]
  apply eq_one_of_residue_eq_one_of_pow_card_sub_one_eq_one (K := K)
  · rw [map_mul, map_inv, hres, teichmuller_section, mul_inv_cancel]
  · rw [mul_pow, hpow, inv_pow, teichmuller_pow_card_sub_one, inv_one, mul_one]

/-- The public uniqueness characterization of Teichmüller representatives: a unit represents
`a : 𝓀[K]ˣ` exactly when it reduces to `a` and its `(q - 1)`-st power is one. -/
theorem eq_teichmuller_iff (u : 𝒪[K]ˣ) (a : 𝓀[K]ˣ) :
    u = teichmuller K a ↔
      Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u = a ∧
        u ^ (Nat.card 𝓀[K] - 1) = 1 := by
  constructor
  · rintro rfl
    exact ⟨teichmuller_section _, teichmuller_pow_card_sub_one _⟩
  · rintro ⟨hres, hpow⟩
    exact eq_teichmuller_of_residue_eq_of_pow_card_sub_one_eq_one u a hres hpow

/-- The Teichmüller map is the unique monoid-homomorphic section of reduction. The values of such
a section are automatically `(q - 1)`-st roots of unity, because `𝓀[K]ˣ` is killed by `q - 1`. -/
theorem teichmuller_unique
    (f : 𝓀[K]ˣ →* 𝒪[K]ˣ)
    (hsection : (Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K])).comp f = .id 𝓀[K]ˣ) :
    f = teichmuller K := by
  apply MonoidHom.ext
  intro a
  apply eq_teichmuller_of_residue_eq_of_pow_card_sub_one_eq_one
  · exact DFunLike.congr_fun hsection a
  · rw [← map_pow, units_pow_card_sub_one_eq_one, map_one]

/-- The Teichmüller lift is the unique zero-preserving multiplicative section of reduction. -/
theorem teichmullerLift_unique (f : 𝓀[K] →*₀ 𝒪[K])
    (hsection : ∀ a, IsLocalRing.residue 𝒪[K] (f a) = a) : f = teichmullerLift K := by
  have hunits : Units.map (f : 𝓀[K] →* 𝒪[K]) = teichmuller K :=
    teichmuller_unique _ (MonoidHom.ext fun a ↦ Units.ext (by simpa using hsection (a : 𝓀[K])))
  ext a
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, map_zero]
  · simpa using
      congrArg (fun g : 𝓀[K]ˣ →* 𝒪[K]ˣ ↦ ((g (Units.mk0 a ha) : 𝒪[K]ˣ) : 𝒪[K])) hunits

/-- The image of the Teichmüller map is exactly the `(q - 1)`-st roots of unity in `𝒪[K]`. -/
theorem range_teichmuller :
    (teichmuller K).range = rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K] := by
  ext u
  constructor
  · rintro ⟨a, rfl⟩
    exact teichmuller_pow_card_sub_one a
  · intro hu
    let a := Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u
    exact ⟨a, (eq_teichmuller_of_residue_eq_of_pow_card_sub_one_eq_one
      u a rfl hu).symm⟩

/-- Reduction and Teichmüller lifting identify the residue-field units with the `(q - 1)`-st
roots of unity in `𝒪[K]`. -/
noncomputable def teichmullerEquivIntegerRootsOfUnity :
    𝓀[K]ˣ ≃* rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K] :=
  (MonoidHom.ofLeftInverse (teichmuller_section (K := K))).trans
    (MulEquiv.subgroupCongr range_teichmuller)

/-- The integral-roots equivalence sends `a` to its Teichmüller representative. -/
@[simp]
theorem teichmullerEquivIntegerRootsOfUnity_apply (a : 𝓀[K]ˣ) :
    (teichmullerEquivIntegerRootsOfUnity (K := K) a : 𝒪[K]ˣ) = teichmuller K a := by
  rw [teichmullerEquivIntegerRootsOfUnity, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofLeftInverse_apply]

/-- The inverse of the integral-roots equivalence is reduction. -/
@[simp]
theorem teichmullerEquivIntegerRootsOfUnity_symm_apply
    (u : rootsOfUnity (Nat.card 𝓀[K] - 1) 𝒪[K]) :
    (teichmullerEquivIntegerRootsOfUnity (K := K)).symm u =
      Units.map (IsLocalRing.residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u := by
  rw [teichmullerEquivIntegerRootsOfUnity, MulEquiv.symm_trans_apply,
    MonoidHom.ofLeftInverse_symm_apply, MulEquiv.subgroupCongr_symm_apply]

/-- Teichmüller lifting identifies the multiplicative group of the residue field with the
`(q - 1)`-st roots of unity in `K`. -/
noncomputable def teichmullerEquivRootsOfUnity :
    𝓀[K]ˣ ≃* rootsOfUnity (Nat.card 𝓀[K] - 1) K :=
  haveI : NeZero (Nat.card 𝓀[K] - 1) :=
    ⟨by have := Finite.one_lt_card (α := 𝓀[K]); omega⟩
  teichmullerEquivIntegerRootsOfUnity.trans (integerRootsOfUnityEquivRootsOfUnity K _)

/-- The roots-of-unity equivalence sends `a` to the image in `K` of its Teichmüller
representative. -/
@[simp]
theorem teichmullerEquivRootsOfUnity_apply (a : 𝓀[K]ˣ) :
    ((teichmullerEquivRootsOfUnity (K := K) a : Kˣ) : K) =
      ((teichmuller K a : 𝒪[K]ˣ) : 𝒪[K]) := by
  rw [teichmullerEquivRootsOfUnity, MulEquiv.trans_apply,
    integerRootsOfUnityEquivRootsOfUnity_apply, teichmullerEquivIntegerRootsOfUnity_apply]

/-- The inverse of the roots-of-unity equivalence sends a root of unity `z` of `K` to the residue
class whose Teichmüller representative is `z`. -/
@[simp]
theorem teichmullerLift_teichmullerEquivRootsOfUnity_symm_apply
    (z : rootsOfUnity (Nat.card 𝓀[K] - 1) K) :
    ((teichmullerLift K ((teichmullerEquivRootsOfUnity (K := K)).symm z : 𝓀[K]) : 𝒪[K]) : K) =
      ((z : Kˣ) : K) := by
  rw [← coe_teichmuller_apply, ← teichmullerEquivRootsOfUnity_apply,
    MulEquiv.apply_symm_apply]

end TauCeti
