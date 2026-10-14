/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.UnitsDecomposition

/-!
# Unramified Kummer classes over a local field

Let `K` be a nonarchimedean local field, `I_K` its inertia subgroup, and `n` a natural number
prime to the residue characteristic. A class in `H¹(G_K, μₙ)` is **unramified** when its
restriction to `I_K` vanishes. Under the Kummer isomorphism `Kˣ ⧸ (Kˣ)ⁿ ≃ H¹(G_K, μₙ)` these are
exactly the classes of units:

  the Kummer class of `a ∈ Kˣ` is unramified `↔` `n ∣ v_K(a)`.

This is the local input to the finiteness of Selmer groups: a global Kummer class unramified at a
finite place prime to `n` comes from an element whose valuation there is divisible by `n`, and the
classes unramified outside a finite set of places are then controlled by the `S`-units and the
`S`-class group.

The proof compares the Kummer cocycle `g ↦ g α / α` of an `n`th root `α` of `a` with the inertia
subgroup, transported from `Gal(K^{alg}/K)` to `AbsoluteGaloisGroup K` along
`TauCeti.absoluteGaloisGroupRestrictEquiv`. Inertia fixes the `n`th roots of unity, since `n` is
prime to the residue characteristic, so on inertia a coboundary vanishes and the class restricts to
zero exactly when inertia fixes `α`.

* If `n ∣ v_K(a)`, then `a` is a unit times an `n`th power, so its Kummer class is that of a unit
  `u`, and the `n`th roots of `u` lie in the maximal unramified extension, which inertia fixes.
* If inertia fixes `α`, then `K(α)` is unramified over `K`, so the normalized valuation of
  `K(α)` restricts to that of `K`, and `v_K(a) = v_{K(α)}(αⁿ) = n · v_{K(α)}(α)`.

## Main results

* `TauCeti.explicitRes1_kummerMap_eq_zero_iff`: the Kummer class of `a` restricts to zero on
  inertia exactly when `n` divides the normalized valuation of `a`.
* `TauCeti.explicitRes1_eq_zero_iff_exists_kummerMap`: the classes of `H¹(G_K, μₙ)` vanishing on
  inertia are exactly the Kummer classes of units of the valuation ring.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.1, proof of
  Proposition VIII.1.6, and X.4.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {n : ℕ}

/-- Inertia, transported to `AbsoluteGaloisGroup K`, acts trivially on `μₙ` when `n` is prime to
the residue characteristic. -/
private theorem smul_kummerCoeff_eq_self_of_mem_inertiaSubgroup (hp : ¬ ringChar 𝓀[K] ∣ n)
    {τ : AbsoluteGaloisGroup K}
    (hτ : τ ∈ (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
    (x : KummerCoeff K n) : τ • x = x := by
  obtain ⟨σ, hσ, rfl⟩ := hτ
  have hm : n.Coprime (ringChar 𝓀[K]) :=
    ((CharP.prime_ringChar 𝓀[K]).coprime_iff_not_dvd.2 hp).symm
  refine Additive.toMul.injective (Subtype.ext (Units.ext ?_))
  have hx : (((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) : AlgebraicClosure K) ^ n =
      1 := by
    have := congrArg (fun u : (SeparableClosure K)ˣ ↦ ((u : SeparableClosure K) :
      AlgebraicClosure K)) ((mem_rootsOfUnity _ _).1 x.toMul.2)
    simpa using this
  have h := apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ hm hx
  simp only [Additive.toMul_smul, rootsOfUnity.coe_smul, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_ofClass, MulEquiv.coe_toMonoidHom]
  exact Subtype.ext ((coe_absoluteGaloisGroupRestrictEquiv_apply K σ _).trans h)

/-- **The Kummer class of an `n`th root restricts to zero on inertia exactly when inertia fixes
the root**, for `n` prime to the residue characteristic. -/
private theorem explicitRes1_kummerCocycleClass_eq_zero_iff (hp : ¬ ringChar 𝓀[K] ∣ n)
    {a : Kˣ} {α : (SeparableClosure K)ˣ}
    (hα : α ^ n = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    explicitRes1 (AbsoluteGaloisGroup K) (KummerCoeff K n)
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
        (kummerCocycleClass hα) = 0 ↔
      ∀ σ : Gal(AlgebraicClosure K/K), σ ∈ inertiaSubgroup K →
        σ ((α : SeparableClosure K) : AlgebraicClosure K) = (α : SeparableClosure K) := by
  rw [kummerCocycleClass_def, QuotientAddGroup.mk'_apply, explicitRes1_mk, H1pi_eq_zero_iff,
    mem_B1_iff]
  -- on inertia every coboundary vanishes, so the restricted cocycle is a coboundary iff it is zero
  have hcob : ∀ (x : KummerCoeff K n)
      (τ : (inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom),
      τ • x - x = 0 := fun x τ ↦ by
    rw [Subgroup.smul_def, smul_kummerCoeff_eq_self_of_mem_inertiaSubgroup hp τ.2, sub_self]
  simp only [groupCohomology.IsCoboundary₁, hcob, cocyclesMap1_apply, AddMonoidHom.id_apply,
    ContinuousMonoidHom.subgroupSubtype_apply, exists_const]
  -- the image of `σ` fixes `α` in `Kˢ` exactly when `σ` fixes it in `K^{alg}`
  have hfix (σ : Gal(AlgebraicClosure K/K)) :
      kummerCocycle hα (absoluteGaloisGroupRestrictEquiv K σ) = 0 ↔
        σ ((α : SeparableClosure K) : AlgebraicClosure K) = (α : SeparableClosure K) := by
    rw [kummerCocycle_eq_zero_iff, Units.ext_iff, AlgEquiv.smul_units_def, Units.coe_map,
      MonoidHom.coe_ofClass, ← coe_absoluteGaloisGroupRestrictEquiv_apply K σ, SetLike.coe_eq_coe]
  refine ⟨fun h σ hσ ↦ (hfix σ).1 (h ⟨_, σ, hσ, rfl⟩).symm, fun h ⟨_, σ, hσ, hτ⟩ ↦ ?_⟩
  subst hτ
  exact ((hfix σ).2 (h σ hσ)).symm

/-- If `n` divides the normalized valuation of `a`, then `a` has the Kummer class of a unit of the
valuation ring: `a = u · (ϖ ^ k) ^ n` for a uniformizer `ϖ`. -/
private theorem exists_kummerMap_eq_of_dvd (hn : IsUnit (n : K)) {a : Kˣ}
    (ha : (n : ℤ) ∣ (normalizedValuation K a).toAdd) :
    ∃ u ∈ unitFiltration K 0, kummerMap K n hn u = kummerMap K n hn a := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer (K := K)
  refine ⟨_, mul_zpow_neg_mem_unitFiltration_zero ((isUniformizer_def ϖ).1 hϖ) a, ?_⟩
  have hpow : kummerMap K n hn (ϖ ^ (-(normalizedValuation K a).toAdd)) = 1 :=
    (kummerMap_eq_one_iff hn _).2 ⟨ϖ ^ (-k), by rw [hk, ← zpow_natCast, ← zpow_mul]; congr 1; ring⟩
  rw [map_mul, hpow, mul_one]

variable (K) in
/-- **Unramified Kummer classes.** Let `n` be prime to the residue characteristic of the
nonarchimedean local field `K`. The Kummer class of `a ∈ Kˣ` in `H¹(G_K, μₙ)` restricts to zero on
the inertia subgroup exactly when `n` divides the normalized valuation of `a`. -/
theorem explicitRes1_kummerMap_eq_zero_iff (hn : IsUnit (n : K)) (hp : ¬ ringChar 𝓀[K] ∣ n)
    (a : Kˣ) :
    explicitRes1 (AbsoluteGaloisGroup K) (KummerCoeff K n)
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom)
        (kummerMap K n hn a).toAdd = 0 ↔
      (n : ℤ) ∣ (normalizedValuation K a).toAdd := by
  constructor
  · intro h
    obtain ⟨α, hα⟩ := exists_pow_eq_units_map hn a
    rw [kummerMap_eq_kummerCocycleClass hn hα,
      explicitRes1_kummerCocycleClass_eq_zero_iff hp hα] at h
    set x : AlgebraicClosure K := ((α : SeparableClosure K) : AlgebraicClosure K)
    have hx : x ^ n = algebraMap K (AlgebraicClosure K) a := by
      have := congrArg (fun v : (SeparableClosure K)ˣ ↦
        ((v : SeparableClosure K) : AlgebraicClosure K)) hα
      simpa using this
    -- `K(x)` is a finite separable subextension fixed by inertia, hence unramified
    set E := IntermediateField.adjoin K {x}
    have : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : Algebra.IsSeparable K E :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (AlgebraicClosure K)).2
        (mem_separableClosure_iff.1 (α : SeparableClosure K).2)
    let := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) E
    let := finiteIntermediateFieldTopology K (AlgebraicClosure K) E
    have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) E
    have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) E
    have hur : IsUnramified K E := (inertiaSubgroup_le_fixingSubgroup_iff E).1 <|
      (IntermediateField.le_iff_le _ _).1 (IntermediateField.adjoin_simple_le_iff.2 fun σ ↦
        h σ σ.2)
    -- in `E`, `a = yⁿ`, and the normalized valuation of `E` extends that of `K`
    have hx0 : x ≠ 0 := by simp [x]
    set y : Eˣ := Units.mk0 ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
      fun h ↦ hx0 (by simpa using congrArg ((↑) : E → AlgebraicClosure K) h)
    have hy : Units.map (algebraMap K E : K →* E) a = y ^ n := by
      ext
      simp [y, hx]
    refine ⟨(normalizedValuation E y).toAdd, ?_⟩
    rw [← hur.normalizedValuation_algebraMap a, hy, map_pow, toAdd_pow, nsmul_eq_mul]
  · intro h
    obtain ⟨u, hu, hua⟩ := exists_kummerMap_eq_of_dvd hn h
    obtain ⟨α, hα⟩ := exists_pow_eq_units_map hn u
    rw [← hua, kummerMap_eq_kummerCocycleClass hn hα,
      explicitRes1_kummerCocycleClass_eq_zero_iff hp hα]
    -- the `n`th roots of the unit `u` lie in the maximal unramified extension
    have hx : ((α : SeparableClosure K) : AlgebraicClosure K) ^ n =
        algebraMap K (AlgebraicClosure K) u := by
      have := congrArg (fun v : (SeparableClosure K)ˣ ↦
        ((v : SeparableClosure K) : AlgebraicClosure K)) hα
      simpa using this
    exact fun σ hσ ↦
      mem_inertiaSubgroup_iff.1 hσ _ (mem_maximalUnramifiedExtension_of_pow_eq hp hu hx)

variable (K) in
/-- **The unramified classes of `H¹(G_K, μₙ)` are the Kummer classes of units.** For `n` prime to
the residue characteristic of `K`, a class restricts to zero on the inertia subgroup exactly when
it is the Kummer class of a unit of the valuation ring. -/
theorem explicitRes1_eq_zero_iff_exists_kummerMap (hn : IsUnit (n : K))
    (hp : ¬ ringChar 𝓀[K] ∣ n) (c : H1 (AbsoluteGaloisGroup K) (KummerCoeff K n)) :
    explicitRes1 (AbsoluteGaloisGroup K) (KummerCoeff K n)
        ((inertiaSubgroup K).map (absoluteGaloisGroupRestrictEquiv K).toMonoidHom) c = 0 ↔
      ∃ u ∈ unitFiltration K 0, (kummerMap K n hn u).toAdd = c := by
  obtain ⟨a, ha⟩ := kummerMap_surjective hn (Multiplicative.ofAdd c)
  obtain rfl : (kummerMap K n hn a).toAdd = c := by rw [ha, toAdd_ofAdd]
  rw [explicitRes1_kummerMap_eq_zero_iff K hn hp]
  refine ⟨fun h ↦ ?_, fun ⟨u, hu, hua⟩ ↦ ?_⟩
  · obtain ⟨u, hu, hua⟩ := exists_kummerMap_eq_of_dvd hn h
    exact ⟨u, hu, by rw [hua]⟩
  · rw [← explicitRes1_kummerMap_eq_zero_iff K hn hp, ← hua,
      explicitRes1_kummerMap_eq_zero_iff K hn hp]
    rw [← ker_normalizedValuation] at hu
    rw [MonoidHom.mem_ker.1 hu, toAdd_one]
    exact dvd_zero _

end TauCeti
