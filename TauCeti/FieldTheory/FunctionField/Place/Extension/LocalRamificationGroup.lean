/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.TotallyRamified
public import TauCeti.FieldTheory.FunctionField.Place.Extension.RamificationGroup
public import TauCeti.RingTheory.LocalRing.RamificationGroup

/-!
# Function-field and local-ring ramification groups

The lower ramification groups of a place are the generic local-ring ramification filtration of
its valuation ring. More precisely, for a place `P` of `F' / k` over `F`, this file identifies

`Place.ramificationGroup F P i`

with `IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers i`.
The comparison rests on the equality between the place filtration and powers of the maximal
ideal of `P.integers`.

The decomposition group acts faithfully on the valuation ring: agreement there implies
agreement on its fraction field. Consequently, after rewriting along the comparison, the generic
lower index (`IsLocalRing.mem_ramificationGroup_iff_le_lowerIndex`) and Hilbert counting identity
(`IsLocalRing.sum_addVal_smul_sub_eq_finsum_card_ramificationGroup_sub_one`) apply directly to
the function-field groups.

Over the inertia field `T` of `P`, the inertia group acts on `𝒪_P` by `𝒪_{P ∩ T}`-algebra
automorphisms, and when the residue extension is separable `P` is totally ramified over `T`, so a
uniformizer generates `𝒪_P` over `𝒪_{P ∩ T}`. The generic monogenic criterion then reads the
ramification groups off a single uniformizer.

## Main results

* `TauCeti.Place.ramificationGroup_eq_isLocalRing_ramificationGroup`: the two lower ramification
  filtrations agree.
* `TauCeti.Place.algebra_adjoin_restrict_inertiaField_eq_top_of_ord_eq_one`: a uniformizer at `P`
  generates `𝒪_P` over the valuation ring below it in the inertia field.
* `TauCeti.Place.mem_ramificationGroup_iff_sub_mem_filtration`: an element of the inertia group
  lies in `G_i` exactly when it moves a uniformizer by something of order at least `i + 1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.8.5 and
  Theorem 3.8.7.
* J.-P. Serre, *Local Fields*, Chapter IV, Section 1.
-/

public section

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

/-- The lower ramification groups defined using the order filtration of the function field are
the generic local-ring ramification groups of the valuation ring. -/
theorem ramificationGroup_eq_isLocalRing_ramificationGroup (P : Place k F') (i : ℕ) :
    ramificationGroup F P i =
      IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers i := by
  ext g
  rw [mem_ramificationGroup_iff, IsLocalRing.mem_ramificationGroup_natCast_iff]
  constructor
  · intro h x
    rw [P.mem_maximalIdeal_pow_iff_coe_mem_filtration, AddSubgroupClass.coe_sub,
      ValuationSubring.coe_decompositionSubgroup_smul, Nat.cast_add, Nat.cast_one]
    exact h x x.2
  · intro h x hx
    have h' := (P.mem_maximalIdeal_pow_iff_coe_mem_filtration (i + 1) _).mp (h ⟨x, hx⟩)
    rwa [AddSubgroupClass.coe_sub, ValuationSubring.coe_decompositionSubgroup_smul,
      Nat.cast_add, Nat.cast_one] at h'

section InertiaField

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable (F) [FiniteDimensional F F'] [IsGalois F F'] (P : Place k F')

omit [IsGalois F F'] in
/-- The inertia group of `P` fixes the inertia field pointwise, so its action on `𝒪_P` is by
algebra automorphisms over the valuation ring below `P` in the inertia field. -/
instance instSMulCommClassInertiaSubgroupIntegers :
    SMulCommClass (P.integers.inertiaSubgroup F) (P.restrict k (inertiaField F P)).integers
      P.integers where
  smul_comm g a b := Subtype.ext <| by
    rw [Algebra.smul_def, Algebra.smul_def, Subgroup.smul_def, Subgroup.smul_def,
      ValuationSubring.coe_decompositionSubgroup_smul, Submonoid.coe_mul, Submonoid.coe_mul,
      map_mul, coe_algebraMap_integers, IntermediateField.algebraMap_apply,
      (mem_inertiaField_iff F P _).mp (a : inertiaField F P).2 g g.2,
      ValuationSubring.coe_decompositionSubgroup_smul]

variable [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]

/-- **A uniformizer generates the valuation ring over the inertia field**: when the residue
extension is separable, `P` is totally ramified over its inertia field `T`, so any `t` of order
`1` at `P` generates `𝒪_P` as an algebra over the valuation ring of `P ∩ T`. -/
theorem algebra_adjoin_restrict_inertiaField_eq_top_of_ord_eq_one {t : P.integers}
    (ht : P.ord (t : F') = 1) :
    Algebra.adjoin (P.restrict k (inertiaField F P)).integers {t} = ⊤ := by
  set T := inertiaField F P
  -- Over `T`, the valuation ring of `P` is the integral closure of `𝒪_{P ∩ T}` in `F'`.
  have hint {z : F'} : IsIntegral (P.restrict k T).integers z ↔ z ∈ P.integers :=
    isIntegral_iff_mem_integers_of_decompositionSubgroup_eq_top T P
      (decompositionSubgroup_inertiaField_eq_top F P)
  let f : integralClosure (P.restrict k T).integers F' →ₐ[(P.restrict k T).integers] P.integers :=
    { toFun y := ⟨y, hint.mp y.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      commutes' _ := rfl }
  have hadj : Algebra.adjoin (P.restrict k T).integers
      {(⟨t, hint.mpr t.2⟩ : integralClosure (P.restrict k T).integers F')} = ⊤ :=
    algebra_adjoin_integralClosure_eq_top_of_isTotallyRamified (k := k) T
      (isTotallyRamified_inertiaField F P) ht
  have hft : f ⟨t, hint.mpr t.2⟩ = t := rfl
  refine eq_top_iff.mpr fun x _ ↦ ?_
  rw [← hft, ← Set.image_singleton, ← AlgHom.map_adjoin, hadj]
  exact ⟨⟨x, hint.mpr x.2⟩, Algebra.mem_top, rfl⟩

/-- **The ramification groups are read off a uniformizer** (Stichtenoth, Proposition 3.8.5): when
the residue extension is separable, an element `σ` of the inertia group of `P` lies in the `i`-th
ramification group exactly when `σ t - t` has order at least `i + 1` for one uniformizer `t` at
`P`. -/
theorem mem_ramificationGroup_iff_sub_mem_filtration {t : F'} (ht : P.ord t = 1)
    {g : P.integers.decompositionSubgroup F} (hg : g ∈ P.integers.inertiaSubgroup F) (i : ℕ) :
    g ∈ ramificationGroup F P i ↔ (g : F' ≃ₐ[F] F') t - t ∈ P.filtration (i + 1) := by
  have htP : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hadj := algebra_adjoin_restrict_inertiaField_eq_top_of_ord_eq_one F P
    (t := ⟨t, htP⟩) ht
  have hi : ((i : ℤ) + 1).toNat = i + 1 := by omega
  rw [ramificationGroup_eq_isLocalRing_ramificationGroup,
    ← Subgroup.mem_subgroupOf (h := (⟨g, hg⟩ : P.integers.inertiaSubgroup F)),
    IsLocalRing.subgroupOf_ramificationGroup,
    IsLocalRing.mem_ramificationGroup_iff_of_adjoin_singleton_eq_top hadj, hi,
    P.mem_maximalIdeal_pow_iff_coe_mem_filtration, AddSubgroupClass.coe_sub, Subgroup.smul_def,
    ValuationSubring.coe_decompositionSubgroup_smul, Nat.cast_add, Nat.cast_one]

end InertiaField

end Place

end TauCeti
