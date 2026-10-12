/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ResidueCorrespondence
public import TauCeti.NumberTheory.LocalField.Teichmuller
public import Mathlib.RingTheory.Frobenius

/-!
# Frobenius in unramified local fields

The arithmetic Frobenius of a finite unramified extension is compatible with restriction through
a normal intermediate field. This identifies the Frobenius elements at different finite levels
of an unramified tower, rather than merely identifying arbitrary generators of their cyclic Galois
groups. Under a change of ground field `K ⊆ K'`, the Frobenius of an unramified extension of `K'`
restricts to the power of the Frobenius over `K` by the residue degree of `K'/K`. The Teichmüller
lifts of a residue element's Frobenius image and its power by the cardinality of the base residue
field agree. Frobenius raises prime-to-residue-characteristic roots of unity to that same power.

## Main result

* `TauCeti.frobeniusAlgEquiv_restrictNormal`: restricting arithmetic Frobenius to a normal
  intermediate field gives arithmetic Frobenius there.
* `TauCeti.frobeniusAlgEquiv_restrictScalars_restrictNormal`: the arithmetic Frobenius of `L'/K'`
  restricts on `L ⊆ L'` to the `f(K'/K)`-th power of the arithmetic Frobenius of `L/K`.
* `TauCeti.frobeniusAlgEquiv_teichmullerLift`: the Teichmüller lifts of the Frobenius action
  on a residue element and its `q`-th power agree.
* `TauCeti.frobeniusAlgEquiv_rootsOfUnity`: on prime-to-residue-characteristic roots of
  unity, arithmetic Frobenius acts by the `q`-th power map.
* `TauCeti.frobeniusAlgEquiv_apply_of_pow_eq_one`: the same holds for every root of unity whose
  order is invertible in `𝒪[L]`, not only for the `(q_L − 1)`-st roots of unity.
* `TauCeti.frobeniusAlgEquiv_apply_of_pow_natCard_pow_eq_self`: it raises every root of
  `X^{q^g} − X` to the `q`-th power.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

section Teichmuller

variable {K L : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

/-- The Teichmüller lifts of the Frobenius action on `a` and of `a ^ q` agree,
where `q` is the cardinality of the residue field of the base. -/
@[simp]
theorem frobeniusAlgEquiv_teichmullerLift [IsUnramified K L] (a : 𝓀[L]) :
    teichmullerLift L (frobeniusAlgEquiv (K := K) (L := L) • a) =
      teichmullerLift L (a ^ Nat.card 𝓀[K]) := by
  congr 1
  have h := congrArg (fun e : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] ↦ e a)
    (residueField_toAlgEquiv_frobeniusAlgEquiv (K := K) (L := L))
  simpa only [MulSemiringAction.toAlgEquiv_apply,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    Fintype.card_eq_nat_card] using h

/-- Arithmetic Frobenius raises every `(q_L - 1)`-st root of unity in an unramified extension
to the `q_K`-th power. -/
@[simp]
theorem frobeniusAlgEquiv_rootsOfUnity [IsUnramified K L]
    (ζ : rootsOfUnity (Nat.card 𝓀[L] - 1) L) :
    frobeniusAlgEquiv (K := K) (L := L) ((ζ : Lˣ) : L) =
      (((ζ : Lˣ) : L) ^ Nat.card 𝓀[K]) := by
  let a := rootsOfUnityAlgebraMulEquivUnitsResidueField 𝒪[L] L ζ
  have hζ : ((ζ : Lˣ) : L) = ((teichmullerLift L (a : 𝓀[L]) : 𝒪[L]) : L) := by
    rw [← coe_teichmuller_apply]
    exact (algebraMap_teichmuller_rootsOfUnityAlgebraMulEquivUnitsResidueField
      𝒪[L] L ζ).symm
  rw [hζ]
  rw [← AlgEquiv.coe_smul_integerRing, AlgEquiv.smul_teichmullerLift,
    frobeniusAlgEquiv_teichmullerLift,
    map_pow]
  exact (map_pow (algebraMap 𝒪[L] L) (teichmullerLift L (a : 𝓀[L]))
    (Nat.card 𝓀[K])).symm

/-- **Arithmetic Frobenius on roots of unity of order prime to the residue characteristic.** In a
finite unramified Galois extension `L / K`, if `x ^ n = 1` for an `n` invertible in `𝒪[L]`, then
`Frob x = x ^ q`, where `q` is the cardinality of the residue field of `K`. -/
theorem frobeniusAlgEquiv_apply_of_pow_eq_one [IsUnramified K L] {n : ℕ}
    (hn : IsUnit (n : 𝒪[L])) {x : L} (hx : x ^ n = 1) :
    frobeniusAlgEquiv (K := K) (L := L) x = x ^ Nat.card 𝓀[K] := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  -- A root of unity has valuation `1`, so it is integral.
  have hxv : x ∈ 𝒪[L] := (Valuation.mem_integer_iff _ _).2
    ((pow_le_one_iff_of_nonneg zero_le hn0).1 (by rw [← map_pow, hx, map_one]))
  -- `𝓂[L]` lies over `𝓂[K]`, the kernel of reduction `𝒪[K] → 𝓀[K]`, so the quotient is `𝓀[K]`.
  have hq : Nat.card (𝒪[K] ⧸ 𝓂[L].under 𝒪[K]) = Nat.card 𝓀[K] := by
    rw [← Ideal.over_def 𝓂[L] 𝓂[K], ← IsLocalRing.ker_residue]
    exact Nat.card_congr
      (RingHom.quotientKerEquivOfSurjective IsLocalRing.residue_surjective).toEquiv
  -- Frobenius is an arithmetic Frobenius of `𝒪[L] / 𝒪[K]` at the maximal ideal, so Mathlib's
  -- `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` applies.
  have hσ : IsArithFrobAt 𝒪[K] (frobeniusAlgEquiv (K := K) (L := L)) 𝓂[L] := fun y ↦ by
    rw [hq]
    refine (Valuation.mem_maximalIdeal_iff (v := valuation L)).2 ?_
    rw [MulSemiringAction.toAlgHom_apply, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow,
      AlgEquiv.coe_smul_integerRing]
    exact valuation_frobeniusAlgEquiv_sub_pow (K := K) (L := L) y
  have h := hσ.apply_of_pow_eq_one (ζ := ⟨x, hxv⟩)
    (Subtype.ext (by rw [SubmonoidClass.coe_pow, hx, OneMemClass.coe_one]))
    ((IsLocalRing.mem_maximalIdeal _).not.2 (not_not.2 hn))
  rw [hq, MulSemiringAction.toAlgHom_apply] at h
  have h' := congrArg Subtype.val h
  rwa [AlgEquiv.coe_smul_integerRing, SubmonoidClass.coe_pow] at h'

/-- **Arithmetic Frobenius on the roots of `X^{q^g} − X`.** In a finite unramified Galois extension
`L / K`, if `x ^ (q ^ g) = x` for some `g ≠ 0`, then `Frob x = x ^ q`, where `q` is the cardinality
of the residue field of `K`. -/
theorem frobeniusAlgEquiv_apply_of_pow_natCard_pow_eq_self [IsUnramified K L] {g : ℕ} (hg : g ≠ 0)
    {x : L} (hx : x ^ Nat.card 𝓀[K] ^ g = x) :
    frobeniusAlgEquiv (K := K) (L := L) x = x ^ Nat.card 𝓀[K] := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero, zero_pow Nat.card_pos.ne']
  -- A nonzero root of `X^{q^g} − X` is a `(q^g − 1)`-st root of unity, and `q^g − 1` is prime
  -- to the residue characteristic.
  refine frobeniusAlgEquiv_apply_of_pow_eq_one (n := Nat.card 𝓀[K] ^ g - 1) ?_ ?_
  · simpa using (isUnit_natCast_natCard_pow_sub_one K hg).map (algebraMap 𝒪[K] 𝒪[L])
  · refine mul_right_cancel₀ hx0 ?_
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ Nat.card_pos), hx]

end Teichmuller

variable {K L M : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M]

variable [FiniteDimensional K M] [Normal K L] [IsGalois K M]

/-- Arithmetic Frobenius restricts to arithmetic Frobenius through a normal intermediate field
of a finite unramified extension of nonarchimedean local fields. -/
@[simp]
theorem frobeniusAlgEquiv_restrictNormal :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    ∀ [IsUnramified K M],
    letI : FiniteDimensional K L :=
      FiniteDimensional.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap
        (IsScalarTower.toAlgHom K L M).injective
    letI : Algebra.IsSeparable K L :=
      Algebra.isSeparable_tower_bot_of_isSeparable K L M
    letI : IsGalois K L := ⟨⟩
    letI := IsUnramified.tower_bot K L M
    (frobeniusAlgEquiv (K := K) (L := M)).restrictNormal L =
      frobeniusAlgEquiv (K := K) (L := L) := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  intro
  let _ : FiniteDimensional K L :=
    FiniteDimensional.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap
      (IsScalarTower.toAlgHom K L M).injective
  let _ : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : IsGalois K L := ⟨⟩
  let _ : IsUnramified K L := IsUnramified.tower_bot K L M
  let σ := frobeniusAlgEquiv (K := K) (L := M)
  apply eq_frobeniusAlgEquiv_of_valuation_sub_pow_lt_one
  intro y
  let d : 𝒪[L] := (σ.restrictNormal L).integerRingEquiv y - y ^ Nat.card 𝓀[K]
  have hdcoe : (d : L) =
      (σ.restrictNormal L) (y : L) - (y : L) ^ Nat.card 𝓀[K] := by
    -- Expose the field-valued expression represented by the integer-ring difference `d`.
    change ((((σ.restrictNormal L).integerRingEquiv y : 𝒪[L]) : L) -
      (y : L) ^ Nat.card 𝓀[K]) = _
    rw [AlgEquiv.integerRingEquiv_apply, AlgEquiv.coe_smul_integerRing]
  have hd : d ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
    have hσ := valuation_frobeniusAlgEquiv_sub_pow (K := K) (L := M)
      (algebraMap 𝒪[L] 𝒪[M] y)
    have hdM : algebraMap 𝒪[L] 𝒪[M] d ∈ IsLocalRing.maximalIdeal 𝒪[M] := by
      apply (Valuation.mem_maximalIdeal_iff (v := valuation M)).2
      rw [coe_algebraMap_integerRing, hdcoe, map_sub, map_pow,
        AlgEquiv.restrictNormal_commutes]
      exact hσ
    exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
      (valuation L) (valuation M)).mp hdM
  have hv := (Valuation.mem_maximalIdeal_iff (v := valuation L)).1 hd
  rw [hdcoe] at hv
  simpa only [σ] using hv

section BaseChange

variable {K L K' L' : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Field L'] [ValuativeRel L'] [TopologicalSpace L'] [IsNonarchimedeanLocalField L']
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
  [Algebra K K'] [ValuativeExtension K K']
  [Algebra K' L'] [ValuativeExtension K' L'] [FiniteDimensional K' L'] [IsGalois K' L']
  [Algebra K L'] [IsScalarTower K K' L'] [Algebra L L'] [IsScalarTower K L L']
  [ValuativeExtension L L']

/-- **Arithmetic Frobenius under base change.** Let `L/K` and `L'/K'` be finite unramified
extensions with `K ⊆ K'` and `L ⊆ L'`. The arithmetic Frobenius of `L'/K'`, restricted to `L`, is
the power of the arithmetic Frobenius of `L/K` by the residue degree `f(K'/K)`. -/
@[simp]
theorem frobeniusAlgEquiv_restrictScalars_restrictNormal [IsUnramified K L] [IsUnramified K' L'] :
    ((frobeniusAlgEquiv (K := K') (L := L')).restrictScalars K).restrictNormal L =
      frobeniusAlgEquiv (K := K) (L := L) ^ inertiaDegree K K' := by
  let σ := ((frobeniusAlgEquiv (K := K') (L := L')).restrictScalars K).restrictNormal L
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  apply (residueFieldAutEquiv (K := K) (L := L)).injective
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  have hφ : residueFieldAutEquiv (frobeniusAlgEquiv (K := K) (L := L)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L] := by
    rw [residueFieldAutEquiv_apply, MulSemiringAction.toAlgAut_apply,
      residueField_toAlgEquiv_frobeniusAlgEquiv]
  rw [map_pow, hφ, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    Fintype.card_eq_nat_card, ← natCard_residueField K K', residueFieldAutEquiv_apply,
    MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply,
    ← IsLocalRing.ResidueField.residue_smul]
  -- The iterate of the finite-field Frobenius is the `fun x ↦ x ^ q` of Mathlib, applied.
  beta_reduce
  rw [← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  -- The congruence of the Frobenius of `L'/K'` at `y ∈ 𝒪[L]` descends from `𝒪[L']` to `𝒪[L]`.
  have hσ := valuation_frobeniusAlgEquiv_sub_pow (K := K') (L := L') (algebraMap 𝒪[L] 𝒪[L'] y)
  have hd : algebraMap 𝒪[L] 𝒪[L'] (σ • y - y ^ Nat.card 𝓀[K']) ∈ 𝓂[L'] := by
    refine (Valuation.mem_maximalIdeal_iff (v := valuation L')).2 ?_
    rwa [coe_algebraMap_integerRing, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow,
      AlgEquiv.coe_smul_integerRing, map_sub, map_pow, AlgEquiv.restrictNormal_commutes,
      AlgEquiv.restrictScalars_apply, ← coe_algebraMap_integerRing]
  exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff (valuation L) (valuation L')).mp hd

end BaseChange

end TauCeti
