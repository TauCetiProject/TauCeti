/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IsAlgClosed.Automorphism
public import TauCeti.RingTheory.LaurentSeries.Puiseux.AlgClosure
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Galois.Inertia
public import TauCeti.RingTheory.LaurentSeries.Puiseux.KaehlerDifferential.Pullback
public import TauCeti.RingTheory.LaurentSeries.Puiseux.ParameterChange

import Mathlib.Algebra.Field.ULift
import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial

/-!
# Substitution and coordinate-change lifts on the Puiseux field

Let `K` be a field, `F = K⸨X⸩` the formal Laurent series field, and `P = puiseuxField K` the
Puiseux series field over `K`. A nonzero power series `φ ∈ K⟦X⟧` with zero constant coefficient
defines the substitution endomorphism `f ↦ f (φ)` of `F`
(`TauCeti.LaurentSeries.substAlgHom`), and a formal coordinate `φ = u X + ⋯` (`u ≠ 0`) defines the
substitution automorphism `TauCeti.LaurentSeries.substAlgEquiv φ`. Any `K`-algebra endomorphism `ρ`
of `P` extending `f ↦ f (φ)` along `algebraMap F P` (or more generally intertwining ramified level
embeddings `levelEmbedding K n` and `levelEmbedding K m`) maps `K⟦X⟧` into the valuation ring of
`P`. By `TauCeti.puiseuxField.continuous_algHom_iff`, every such algebraic lift `ρ` is
**automatically continuous** for the valuation topology, is a topological embedding, and scales
rational orders by `(n / m) ord φ`. Conversely, every continuous `K`-algebra endomorphism of `P`
restricts on `F` to `levelEmbedding K m` composed with a Laurent substitution `f ↦ f (φ)` for some
ramified level `m` and nonzero `φ ∈ X K⟦X⟧`. In particular, any algebraic lift of a formal
coordinate change is an isometric topological-algebra automorphism `P ≃A[K] P`.

Because `K` is integrally closed in `F` and every element of `P` lies in a finite ramified level,
`K` is integrally closed in `P`, so every root of unity of `P` lies in `K` over *any* field `K`.
Consequently, for any field `K`, any two `K`-algebra endomorphisms `ρ₁, ρ₂ : P →ₐ[K] P` agreeing
on `F` differ by precomposition with a unique Kummer automorphism `ζ ∈ lim_n μₙ(K)`:
`ρ₂ = ρ₁ ∘ kummer K ζ`. Specializing to `ρ₁ = id` shows that `kummer K` is bijective onto
`Gal(P/F)` over every coefficient field `K`, without any root-of-unity or characteristic
assumption. Over an algebraically closed field `K` of characteristic zero, `P` is an algebraic
closure of `F`, so every `K`-algebra endomorphism (resp. automorphism) of `F` lifts to `P`; hence
every substitution `f ↦ f (φ)` lifts to a continuous endomorphism `P →A[K] P` and every formal
coordinate lifts to a bicontinuous automorphism `P ≃A[K] P`.

In characteristic zero, automatic continuity eliminates the continuity hypothesis when applying the
chain rule, the finite-map and coordinate-change residue formulas, and the pullback of continuous
Kähler differentials `ContinuousKaehlerDifferential K` to algebraic lifts of Laurent substitutions
and formal coordinates.

## Main definitions

* `TauCeti.puiseuxField.continuousAlgEquivKummer`: the Kummer automorphism attached to
  `ζ : PrimeToPTateModule 1 K` as a continuous `K⸨X⸩`-algebra equivalence.
* `TauCeti.puiseuxField.continuousAlgHomOfLevelSubst` and
  `TauCeti.puiseuxField.continuousAlgHomOfSubst`: an algebraic lift of a Laurent substitution
  bundled as a continuous `K`-algebra endomorphism `puiseuxField K →A[K] puiseuxField K`.
* `TauCeti.puiseuxField.continuousAlgEquivOfSubst`: an algebraic lift of a formal-coordinate
  substitution bundled as a bicontinuous `K`-algebra automorphism
  `puiseuxField K ≃A[K] puiseuxField K`.

## Main results

* `TauCeti.puiseuxField.isIntegrallyClosedIn` and
  `TauCeti.puiseuxField.exists_rootsOfUnity_algebraMap_eq`: `K` is integrally closed in
  `puiseuxField K`, and every `d`-th root of unity in `puiseuxField K` comes from `K`.
* `TauCeti.puiseuxField.existsUnique_kummer_comp_of_apply_algebraMap` and
  `TauCeti.puiseuxField.existsUnique_kummer_trans_of_apply_algebraMap`: over any field `K`, lifts
  of the same `K`-algebra map on `K⸨X⸩` form a torsor under the Kummer action of
  `PrimeToPTateModule 1 K`.
* `TauCeti.puiseuxField.kummer_surjective` and `TauCeti.puiseuxField.kummer_bijective`: over any
  field `K`, the Kummer action is a bijection `PrimeToPTateModule 1 K → Gal(puiseuxField K / K⸨X⸩)`.
* `TauCeti.puiseuxField.continuous_of_apply_levelEmbedding_substAlgHom`,
  `TauCeti.puiseuxField.continuous_iff_exists_apply_algebraMap_eq_levelEmbedding_substAlgHom`, and
  `TauCeti.puiseuxField.valuation_of_apply_algebraMap_substAlgEquiv`: automatic continuity,
  classification of continuous `K`-algebra endomorphisms by ramified substitutions, valuation
  scaling, and isometricity of coordinate-change lifts.
* `TauCeti.puiseuxField.exists_continuousAlgHom_apply_algebraMap_substAlgHom` and
  `TauCeti.puiseuxField.exists_continuousAlgEquiv_apply_algebraMap_substAlgEquiv`: existence of
  continuous lifts over algebraically closed fields of characteristic zero.
* `TauCeti.puiseuxField.derivation_of_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.residue_mul_derivative_of_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.residue_mul_derivative_of_apply_algebraMap_substAlgEquiv`, and
  `ContinuousKaehlerDifferential.pullback_continuousAlgHomOfLevelSubst_levelMap`:
  continuity-free chain rule, residue formulas, and differential level comparisons for substitution
  lifts.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103, Cambridge University Press, 2007, §1.2.
* Henning Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Graduate Texts in
  Mathematics 254, Springer, 2009, §IV.2.
-/

public section

open HahnSeries LaurentSeries Polynomial PowerSeries Topology WithZero
open scoped LaurentSeries PowerSeries

namespace TauCeti.puiseuxField

open PrimeToPTateModule

section IntegrallyClosedAndKummer

variable (K : Type*) [Field K]

/-- Every coefficient field `K` is integrally closed in `puiseuxField K`: any Puiseux series
integral over `K` lies in a single ramified level `K⸨t ^ (1 / d)⸩ ≅ K⸨X⸩`, where the elements
integral over `K` are the constants. -/
instance isIntegrallyClosedIn : IsIntegrallyClosedIn K (puiseuxField K) := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap K (puiseuxField K)).injective, fun {x} hx ↦ ?_⟩
  obtain ⟨d, f, hf⟩ := exists_mem_range_levelEmbedding x
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
  subst hf
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    ((isIntegral_algHom_iff (levelEmbedding K d) (levelEmbedding K d).injective).mp hx)
  exact ⟨c, ((levelEmbedding K d).commutes c).symm⟩

variable {K}

/-- Every `d`-th root of unity in `puiseuxField K` is the image of a `d`-th root of unity in `K`. -/
theorem exists_rootsOfUnity_algebraMap_eq {d : ℕ+} {w : puiseuxField K} (hw : w ^ (d : ℕ) = 1) :
    ∃ η : rootsOfUnity d K, algebraMap K (puiseuxField K) ((η : Kˣ) : K) = w := by
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    (IsIntegral.of_pow (R := K) d.pos (hw ▸ isIntegral_one))
  have hcd : c ^ (d : ℕ) = 1 :=
    (algebraMap K (puiseuxField K)).injective (by rw [map_pow, hc, hw, map_one])
  exact ⟨rootsOfUnity.mkOfPowEq c hcd, by rw [rootsOfUnity.coe_mkOfPowEq, hc]⟩

/-- For two `K`-algebra endomorphisms agreeing on `K⸨X⸩`, their values on the level-`d` parameter
differ by a `d`-th root of unity in `K`. -/
private theorem exists_rootsOfUnity_apply_levelParameter
    {ρ₁ ρ₂ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ₂ (algebraMap K⸨X⸩ (puiseuxField K) f) = ρ₁ (algebraMap K⸨X⸩ (puiseuxField K) f))
    (d : ℕ+) :
    ∃ η : rootsOfUnity d K, ρ₂ (levelParameter K d : puiseuxField K) =
      algebraMap K (puiseuxField K) ((η : Kˣ) : K) * ρ₁ (levelParameter K d : puiseuxField K) := by
  set u : puiseuxField K := (levelParameter K d : puiseuxField K)
  have hu0 : ρ₁ u ≠ 0 :=
    (map_ne_zero_iff ρ₁ ρ₁.injective).mpr (levelPowerBasis_gen_ne_zero K d)
  have hpow : (ρ₂ u / ρ₁ u) ^ (d : ℕ) = 1 := by
    rw [div_pow, ← map_pow, ← map_pow, coe_levelParameter_pow, h, ← coe_levelParameter_pow,
      map_pow, div_self (pow_ne_zero _ hu0)]
  obtain ⟨η, hη⟩ := exists_rootsOfUnity_algebraMap_eq hpow
  exact ⟨η, by rw [hη, div_mul_cancel₀ _ hu0]⟩

private noncomputable def liftRootOfUnity {ρ₁ ρ₂ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ₂ (algebraMap K⸨X⸩ (puiseuxField K) f) = ρ₁ (algebraMap K⸨X⸩ (puiseuxField K) f))
    (d : ℕ+) : rootsOfUnity d K :=
  (exists_rootsOfUnity_apply_levelParameter h d).choose

private theorem apply_levelParameter_eq_liftRootOfUnity
    {ρ₁ ρ₂ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ₂ (algebraMap K⸨X⸩ (puiseuxField K) f) = ρ₁ (algebraMap K⸨X⸩ (puiseuxField K) f))
    (d : ℕ+) :
    ρ₂ (levelParameter K d : puiseuxField K) =
      algebraMap K (puiseuxField K) ((liftRootOfUnity h d : Kˣ) : K) *
        ρ₁ (levelParameter K d : puiseuxField K) :=
  (exists_rootsOfUnity_apply_levelParameter h d).choose_spec

/-- The roots of unity relating two lifts on the level parameters are compatible under
divisibility. -/
private theorem liftRootOfUnity_pow_div {ρ₁ ρ₂ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ₂ (algebraMap K⸨X⸩ (puiseuxField K) f) = ρ₁ (algebraMap K⸨X⸩ (puiseuxField K) f))
    {n m : ℕ+} (hnm : (n : ℕ) ∣ m) :
    (liftRootOfUnity h m : Kˣ) ^ ((m : ℕ) / n) = liftRootOfUnity h n := by
  have hm : (m : ℕ) = n * ((m : ℕ) / n) := (Nat.mul_div_cancel' hnm).symm
  have hgen : ((levelParameter K m : puiseuxField K) ^ ((m : ℕ) / n)) = levelParameter K n :=
    coe_levelPowerBasis_gen_pow K hm
  have hu0 : ρ₁ (levelParameter K n : puiseuxField K) ≠ 0 :=
    (map_ne_zero_iff ρ₁ ρ₁.injective).mpr (levelPowerBasis_gen_ne_zero K n)
  have h1 := apply_levelParameter_eq_liftRootOfUnity h n
  rw [← hgen, map_pow, apply_levelParameter_eq_liftRootOfUnity h m, mul_pow, ← map_pow, ← map_pow,
    hgen] at h1
  have hcancel := (algebraMap K (puiseuxField K)).injective (mul_right_cancel₀ hu0 h1)
  rw [← Units.val_pow_eq_pow_val] at hcancel
  exact Units.ext hcancel

/-- **Classification of lifts (Kummer torsor).** Over *any* field `K`, any two `K`-algebra
endomorphisms `ρ₁, ρ₂` of `puiseuxField K` agreeing on `K⸨X⸩` differ by precomposition with a
unique Kummer automorphism `ζ : PrimeToPTateModule 1 K`. -/
theorem existsUnique_kummer_comp_of_apply_algebraMap
    {ρ₁ ρ₂ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ₂ (algebraMap K⸨X⸩ (puiseuxField K) f) = ρ₁ (algebraMap K⸨X⸩ (puiseuxField K) f)) :
    ∃! ζ : PrimeToPTateModule 1 K, ρ₂ = ρ₁.comp ((kummer K ζ).restrictScalars K).toAlgHom := by
  let ζ : PrimeToPTateModule 1 K := PrimeToPTateModule.mk
    (fun m ↦ liftRootOfUnity h ⟨m, Nat.pos_of_ne_zero m.2.1⟩)
    (mem_primeToPTateModuleSubgroup_iff.mpr fun m n hmn ↦
      liftRootOfUnity_pow_div h
        (n := ⟨n, Nat.pos_of_ne_zero n.2.1⟩) (m := ⟨m, Nat.pos_of_ne_zero m.2.1⟩) hmn)
  have hζ : ρ₂ = ρ₁.comp ((kummer K ζ).restrictScalars K).toAlgHom := by
    refine AlgHom.ext fun x ↦ ?_
    obtain ⟨d, hd⟩ := exists_mem_range_levelEmbedding x
    obtain ⟨P, hP⟩ := (levelPowerBasis K d).exists_eq_aeval' ⟨x, (mem_level_iff K d x).mpr hd⟩
    have hx : x = Polynomial.aeval (levelParameter K d : puiseuxField K) P := by
      rw [IntermediateField.aeval_coe, ← hP]
    have hproj : proj ⟨d, d.ne_zero, Nat.coprime_one_right _⟩ ζ = liftRootOfUnity h d :=
      proj_mk _ _ _
    have hparam :
        ρ₂ (levelParameter K d : puiseuxField K) =
          ρ₁ (kummer K ζ (levelParameter K d : puiseuxField K)) := by
      rw [kummer_coe_level ζ (levelParameter K d), levelKummer_levelParameter, MulMemClass.coe_mul,
        IntermediateField.coe_algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_mul,
        AlgHom.commutes, hproj, apply_levelParameter_eq_liftRootOfUnity h d]
    rw [hx, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars_apply, map_sum,
      map_mul, map_pow, AlgEquiv.commutes, h, hparam]
  refine ⟨ζ, hζ, fun ζ' hζ' ↦ kummer_injective (AlgEquiv.ext fun x ↦ ρ₁.injective ?_)⟩
  have hx := AlgHom.congr_fun (hζ'.symm.trans hζ) x
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.restrictScalars_apply] using hx

/-- **Classification of automorphism lifts.** Over any field `K`, any two `K`-algebra automorphisms
`ρ₁, ρ₂` of `puiseuxField K` agreeing on `K⸨X⸩` differ by precomposition with a unique Kummer
automorphism. -/
theorem existsUnique_kummer_trans_of_apply_algebraMap
    {ρ₁ ρ₂ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ₂ (algebraMap K⸨X⸩ (puiseuxField K) f) = ρ₁ (algebraMap K⸨X⸩ (puiseuxField K) f)) :
    ∃! ζ : PrimeToPTateModule 1 K, ρ₂ = ((kummer K ζ).restrictScalars K).trans ρ₁ := by
  obtain ⟨ζ, hζ, huniq⟩ := existsUnique_kummer_comp_of_apply_algebraMap (ρ₁ := ρ₁.toAlgHom)
    (ρ₂ := ρ₂.toAlgHom) h
  refine ⟨ζ, AlgEquiv.ext fun x ↦ AlgHom.congr_fun hζ x, fun ζ' hζ' ↦ huniq ζ' ?_⟩
  exact AlgHom.ext fun x ↦ AlgEquiv.congr_fun hζ' x

/-- **Every `K⸨X⸩`-automorphism of the Puiseux field is a Kummer automorphism**, over *any*
coefficient field `K` (without assuming roots of unity or characteristic zero). -/
theorem kummer_surjective : Function.Surjective (kummer K) := by
  intro σ
  obtain ⟨ζ, hζ, -⟩ := existsUnique_kummer_trans_of_apply_algebraMap
    (ρ₁ := AlgEquiv.refl) (ρ₂ := σ.restrictScalars K) (fun f ↦ σ.commutes f)
  exact ⟨ζ, AlgEquiv.ext fun x ↦ (AlgEquiv.congr_fun hζ x).symm⟩

/-- Over *any* coefficient field `K`, the Kummer action `PrimeToPTateModule 1 K →* Gal(P/K⸨X⸩)` is
bijective. -/
theorem kummer_bijective : Function.Bijective (kummer K) :=
  ⟨kummer_injective, kummer_surjective⟩

/-- Every Kummer automorphism `kummer K ζ` of `puiseuxField K` is continuous for the valuation
topology (distinct from `continuous_kummer`, which states Krull-topology continuity of
`ζ ↦ kummer K ζ`). -/
@[fun_prop]
theorem continuous_kummer_apply (ζ : PrimeToPTateModule 1 K) : Continuous (kummer K ζ) :=
  (continuous_algHom_iff_addVal_nonneg (ρ := ((kummer K ζ).restrictScalars K).toAlgHom)).mpr
    fun x hx ↦ by rwa [AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars_apply, addVal_kummer]

variable (K) in
/-- The Kummer automorphism attached to `ζ : PrimeToPTateModule 1 K` as a bicontinuous
`K⸨X⸩`-algebra automorphism of `puiseuxField K`. -/
noncomputable def continuousAlgEquivKummer (ζ : PrimeToPTateModule 1 K) :
    puiseuxField K ≃A[K⸨X⸩] puiseuxField K where
  toAlgEquiv := kummer K ζ
  continuous_toFun := continuous_kummer_apply ζ
  continuous_invFun := by
    change Continuous (kummer K ζ).symm
    have hsymm : (kummer K ζ).symm = kummer K ζ⁻¹ := by rw [map_inv]; rfl
    rw [hsymm]
    exact continuous_kummer_apply ζ⁻¹

@[simp]
theorem continuousAlgEquivKummer_apply (ζ : PrimeToPTateModule 1 K) (x : puiseuxField K) :
    continuousAlgEquivKummer K ζ x = kummer K ζ x :=
  (rfl)

@[simp]
theorem toAlgEquiv_continuousAlgEquivKummer (ζ : PrimeToPTateModule 1 K) :
    (continuousAlgEquivKummer K ζ).toAlgEquiv = kummer K ζ :=
  (rfl)

/-- Over *any* field `K`, every `K⸨X⸩`-automorphism of `puiseuxField K` is continuous for the
valuation topology. -/
@[fun_prop]
theorem continuous_gal_apply (σ : Gal(puiseuxField K/K⸨X⸩)) : Continuous σ := by
  obtain ⟨ζ, rfl⟩ := kummer_surjective σ
  exact continuous_kummer_apply ζ

end IntegrallyClosedAndKummer

/-! ### Automatic continuity and valuation scaling of substitution lifts -/

section SubstitutionLift

variable {K : Type*} [Field K]

/-- **Automatic continuity of ramified substitution lifts.** Any `K`-algebra endomorphism `ρ` of
`puiseuxField K` intertwining `levelEmbedding K n` and `levelEmbedding K m` along a Laurent
substitution `substAlgHom hφ hφ₀` is continuous for the valuation topology. -/
theorem continuous_of_apply_levelEmbedding_substAlgHom (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    Continuous ρ := by
  refine continuous_algHom_iff.mpr fun g ↦ ?_
  rw [← levelEmbedding_expand_self n (g : K⸨X⸩), h]
  have h0 : (0 : WithTop ℚ) = (((0 : ℤ) : ℚ) / m : ℚ) := by simp
  rw [h0, div_le_addVal_levelEmbedding_iff, LaurentSeries.orderTop_substAlgHom,
    _root_.LaurentSeries.orderTop_expand]
  exact nsmul_nonneg (nsmul_nonneg (by simp [PowerSeries.orderTop_coe]) _) _

/-- **Classification of continuous `K`-algebra endomorphisms of the Puiseux field.** Over *any*
field `K`, a `K`-algebra endomorphism `ρ` of `puiseuxField K` is continuous for the valuation
topology if and only if its restriction to `K⸨X⸩` factors as `levelEmbedding K m` composed with a
Laurent substitution `substAlgHom hφ hφ₀` for some ramified level `m` and nonzero `φ ∈ X K⟦X⟧`. -/
theorem continuous_iff_exists_apply_algebraMap_eq_levelEmbedding_substAlgHom
    {ρ : puiseuxField K →ₐ[K] puiseuxField K} :
    Continuous ρ ↔ ∃ (m : ℕ+) (φ : K⟦X⟧) (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0),
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f) := by
  refine ⟨fun hρ ↦ ?_, fun ⟨m, φ, hφ, hφ₀, h⟩ ↦
    continuous_of_apply_levelEmbedding_substAlgHom 1 m hφ hφ₀ h⟩
  obtain ⟨m, g, hg⟩ := exists_mem_range_levelEmbedding (ρ (single K 1 1))
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hg
  have hg1 : (1 : WithTop ℤ) ≤ g.orderTop := by
    have hpos := addVal_algHom_single_one_pos hρ
    rw [← hg, addVal_levelEmbedding] at hpos
    cases hord : g.orderTop with
    | top => exact le_top
    | coe k =>
      rw [hord, WithTop.map_coe, ← WithTop.coe_zero, WithTop.coe_lt_coe,
        div_pos_iff_of_pos_right (by positivity)] at hpos
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast Int.add_one_le_iff.mpr (Int.cast_pos.mp hpos))
  obtain ⟨φ, hφg⟩ : g ∈ Set.range (ofPowerSeries ℤ K) :=
    TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff.mpr fun k hk ↦
      coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hg1)
  have hφ : constantCoeff φ = 0 := by
    have h0 : g.coeff 0 = 0 :=
      coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr zero_lt_one) hg1)
    simpa [PowerSeries.coeff_coe] using (congrArg (fun z : K⸨X⸩ ↦ z.coeff 0) hφg).trans h0
  have hφ₀ : φ ≠ 0 := by
    rintro rfl
    rw [PowerSeries.coe_zero] at hφg
    rw [← hφg, map_zero] at hg
    exact (map_ne_zero_iff ρ ρ.injective).mpr (single_eq_zero_iff.not.mpr one_ne_zero) hg.symm
  have hX : ρ (algebraMap K⸨X⸩ (puiseuxField K) (HahnSeries.single 1 1)) =
      levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ (HahnSeries.single 1 1)) := by
    rw [algebraMap_laurentSeries_apply, LaurentSeries.substAlgHom_single_one, hφg, hg]
    exact congrArg ρ (levelEmbedding_single_self 1)
  refine ⟨m, φ, hφ, hφ₀, congrFun (LaurentPolynomial.denseRange_toLaurentSeries.equalizer
    (hρ.comp (continuous_levelEmbedding 1))
    ((continuous_levelEmbedding m).comp (LaurentSeries.continuous_substAlgHom hφ hφ₀)) ?_)⟩
  funext p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [Function.comp_apply, map_add] at *; rw [hp, hq]
  | C_mul_T k r =>
    have hs : (HahnSeries.single k r : K⸨X⸩) = algebraMap K K⸨X⸩ r * HahnSeries.single 1 1 ^ k := by
      rw [← mul_one r, ← zero_add k, ← HahnSeries.single_mul_single, mul_one, zero_add,
        RatFunc.single_zpow, ← HahnSeries.C_apply, ← _root_.LaurentSeries.algebraMap_apply]
    simp only [Function.comp_apply, ← LaurentPolynomial.single_eq_C_mul_T,
      LaurentPolynomial.toLaurentSeries_single, hs, map_mul, map_zpow₀,
      ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    rw [hX]

/-- Any `K`-algebra endomorphism `ρ` intertwining `levelEmbedding K n` and `levelEmbedding K m`
along `substAlgHom hφ hφ₀` is a topological embedding. -/
theorem isEmbedding_of_apply_levelEmbedding_substAlgHom (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    IsEmbedding ρ :=
  isEmbedding_of_continuous_algHom (continuous_of_apply_levelEmbedding_substAlgHom n m hφ hφ₀ h)

/-- A lift `ρ` intertwining `levelEmbedding K n` and `levelEmbedding K m` along `substAlgHom hφ hφ₀`
sends the parameter `t` to a series of rational order `n * ord φ / m`. -/
theorem order_single_one_of_apply_levelEmbedding_substAlgHom (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (ρ (single K 1 1) : HahnSeries ℚ K).order = (n : ℚ) * φ.order.toNat / m := by
  rw [← levelEmbedding_single_self n, h, coe_levelEmbedding, order_ramifiedEmbedding,
    LaurentSeries.order_substAlgHom, HahnSeries.order_single one_ne_zero]
  push_cast
  ring

/-- Valuation scaling for a lift intertwining `levelEmbedding K n` and `levelEmbedding K m` along
`substAlgHom hφ hφ₀`. -/
theorem addVal_of_apply_levelEmbedding_substAlgHom (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    addVal K (ρ x) = (addVal K x).map (((n : ℚ) * φ.order.toNat / m) * ·) := by
  rw [addVal_algHom_apply (continuous_of_apply_levelEmbedding_substAlgHom n m hφ hφ₀ h),
    order_single_one_of_apply_levelEmbedding_substAlgHom n m hφ hφ₀ h]

/-- Rational-order scaling for a lift intertwining `levelEmbedding K n` and `levelEmbedding K m`
along `substAlgHom hφ hφ₀`. -/
theorem order_of_apply_levelEmbedding_substAlgHom (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order = ((n : ℚ) * φ.order.toNat / m) * (x : HahnSeries ℚ K).order := by
  rw [order_algHom_apply (continuous_of_apply_levelEmbedding_substAlgHom n m hφ hφ₀ h),
    order_single_one_of_apply_levelEmbedding_substAlgHom n m hφ hφ₀ h]

/-- An algebraic lift of a Laurent substitution between ramified levels `n` and `m`, bundled as a
continuous `K`-algebra endomorphism of `puiseuxField K`. -/
noncomputable def continuousAlgHomOfLevelSubst (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    puiseuxField K →A[K] puiseuxField K where
  toAlgHom := ρ
  cont := continuous_of_apply_levelEmbedding_substAlgHom n m hφ hφ₀ h

@[simp]
theorem continuousAlgHomOfLevelSubst_apply (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    continuousAlgHomOfLevelSubst n m hφ hφ₀ ρ h x = ρ x :=
  (rfl)

@[simp]
theorem toAlgHom_continuousAlgHomOfLevelSubst (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (continuousAlgHomOfLevelSubst n m hφ hφ₀ ρ h).toAlgHom = ρ :=
  (rfl)

section BaseLevelSubst

variable {φ : K⟦X⟧} (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0)

/-- **Automatic continuity of substitution lifts.** Any `K`-algebra endomorphism `ρ` of
`puiseuxField K` extending `LaurentSeries.substAlgHom hφ hφ₀` on `K⸨X⸩` is continuous for the
valuation topology. -/
theorem continuous_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    Continuous ρ :=
  continuous_of_apply_levelEmbedding_substAlgHom 1 1 hφ hφ₀ h

/-- A lift `ρ` of `substAlgHom hφ hφ₀` sends `t` to `φ (t)`, whose rational order is `ord φ`. -/
theorem order_single_one_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (ρ (single K 1 1) : HahnSeries ℚ K).order = φ.order.toNat := by
  simpa using order_single_one_of_apply_levelEmbedding_substAlgHom 1 1 hφ hφ₀ h

/-- Any lift `ρ` of `substAlgHom hφ hφ₀` multiplies the additive valuation by `ord φ`. -/
theorem addVal_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    addVal K (ρ x) = (addVal K x).map ((φ.order.toNat : ℚ) * ·) := by
  simpa using addVal_of_apply_levelEmbedding_substAlgHom 1 1 hφ hφ₀ h x

/-- Any lift `ρ` of `substAlgHom hφ hφ₀` multiplies rational orders by `ord φ`. -/
theorem order_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order = φ.order.toNat * (x : HahnSeries ℚ K).order := by
  simpa using order_of_apply_levelEmbedding_substAlgHom 1 1 hφ hφ₀ h x

/-- Any lift `ρ` of `substAlgHom hφ hφ₀` raises the multiplicative Puiseux valuation to the power
`ord φ`. -/
theorem valuation_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x ^ φ.order.toNat := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, zero_pow (toNat_order_ne_zero hφ hφ₀)]
  have hx0 : (x : HahnSeries ℚ K) ≠ 0 := by exact_mod_cast hx
  have hrx0 : (ρ x : HahnSeries ℚ K) ≠ 0 := by
    exact_mod_cast (map_ne_zero_iff ρ ρ.injective).mpr hx
  rw [valuation_apply, valuation_apply, valuation_eq_exp_neg_order hrx0,
    valuation_eq_exp_neg_order hx0, ← exp_nsmul, exp_inj, smul_neg, neg_inj, nsmul_eq_mul,
    order_of_apply_algebraMap_substAlgHom hφ hφ₀ h]

/-- An algebraic lift of `LaurentSeries.substAlgHom hφ hφ₀` bundled as a continuous `K`-algebra
endomorphism of `puiseuxField K`. -/
noncomputable def continuousAlgHomOfSubst (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    puiseuxField K →A[K] puiseuxField K :=
  continuousAlgHomOfLevelSubst 1 1 hφ hφ₀ ρ h

@[simp]
theorem continuousAlgHomOfSubst_apply (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    continuousAlgHomOfSubst hφ hφ₀ ρ h x = ρ x :=
  (rfl)

@[simp]
theorem toAlgHom_continuousAlgHomOfSubst (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (continuousAlgHomOfSubst hφ hφ₀ ρ h).toAlgHom = ρ :=
  (rfl)

end BaseLevelSubst

/-! ### Algebraic lifts of formal coordinate changes -/

private theorem toAlgHom_apply_algebraMap_substAlgHom {φ : FormalCoordinate K}
    {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (f : K⸨X⸩) :
    ρ.toAlgHom (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K)
        (LaurentSeries.substAlgHom φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero f) := by
  rw [AlgEquiv.coe_toAlgHom, h, LaurentSeries.coe_substAlgEquiv]

/-- If `ρ` extends the substitution automorphism of a formal coordinate `φ`, then `ρ.symm` extends
the substitution automorphism of the inverse formal coordinate `φ⁻¹`. -/
theorem symm_apply_algebraMap_substAlgEquiv {φ : FormalCoordinate K}
    {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (f : K⸨X⸩) :
    ρ.symm (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ⁻¹ f) :=
  ρ.symm_apply_eq.mpr (by rw [h, ← LaurentSeries.substAlgEquiv_symm, AlgEquiv.apply_symm_apply])

section CoordinateSubst

variable (φ : FormalCoordinate K)

/-- Any `K`-algebra automorphism `ρ` of `puiseuxField K` extending `LaurentSeries.substAlgEquiv φ`
is continuous. -/
theorem continuous_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    Continuous ρ :=
  continuous_of_apply_algebraMap_substAlgHom φ.constantCoeff_toPowerSeries
    φ.toPowerSeries_ne_zero (toAlgHom_apply_algebraMap_substAlgHom h)

/-- The inverse of any `K`-algebra automorphism `ρ` extending `LaurentSeries.substAlgEquiv φ` is
also continuous. -/
theorem continuous_symm_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    Continuous ρ.symm :=
  continuous_of_apply_algebraMap_substAlgEquiv φ⁻¹ (symm_apply_algebraMap_substAlgEquiv h)

/-- Any lift `ρ` of `LaurentSeries.substAlgEquiv φ` sends `t` to a Puiseux series of order one. -/
theorem order_single_one_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    (ρ (single K 1 1) : HahnSeries ℚ K).order = 1 := by
  simpa [φ.order_toPowerSeries] using order_single_one_of_apply_algebraMap_substAlgHom
    φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero (toAlgHom_apply_algebraMap_substAlgHom h)

/-- **Coordinate-change lifts preserve the additive valuation.** -/
theorem addVal_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    addVal K (ρ x) = addVal K x :=
  addVal_algHom_eq_of_order_eq_one (ρ := ρ.toAlgHom)
    (continuous_of_apply_algebraMap_substAlgEquiv φ h)
    (order_single_one_of_apply_algebraMap_substAlgEquiv φ h) x

/-- **Coordinate-change lifts are isometries.** Every algebraic lift of the substitution
automorphism of a formal coordinate preserves the multiplicative Puiseux valuation. -/
theorem valuation_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x :=
  valuation_algHom_eq_of_order_eq_one (ρ := ρ.toAlgHom)
    (continuous_of_apply_algebraMap_substAlgEquiv φ h)
    (order_single_one_of_apply_algebraMap_substAlgEquiv φ h) x

/-- An algebraic lift of a formal-coordinate substitution `LaurentSeries.substAlgEquiv φ`, bundled
as a bicontinuous `K`-algebra automorphism of `puiseuxField K`. -/
noncomputable def continuousAlgEquivOfSubst (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    puiseuxField K ≃A[K] puiseuxField K :=
  ContinuousAlgEquiv.mk ρ (continuous_of_apply_algebraMap_substAlgEquiv φ h)
    (continuous_symm_of_apply_algebraMap_substAlgEquiv φ h)

@[simp]
theorem continuousAlgEquivOfSubst_apply (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    continuousAlgEquivOfSubst φ ρ h x = ρ x :=
  (rfl)

@[simp]
theorem toAlgEquiv_continuousAlgEquivOfSubst (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    (continuousAlgEquivOfSubst φ ρ h).toAlgEquiv = ρ :=
  (rfl)

@[simp]
theorem symm_continuousAlgEquivOfSubst (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    (continuousAlgEquivOfSubst φ ρ h).symm =
      continuousAlgEquivOfSubst φ⁻¹ ρ.symm (symm_apply_algebraMap_substAlgEquiv h) :=
  ContinuousAlgEquiv.toAlgEquiv_injective rfl

end CoordinateSubst

end SubstitutionLift

/-! ### Existence of continuous substitution lifts over algebraically closed fields

Both `[IsAlgClosed K]` and `[CharZero K]` are required for `puiseuxField K` to be algebraically
closed (in characteristic `p > 0`, Artin–Schreier equations such as `Y ^ p - Y - X⁻¹ = 0` have no
root in `puiseuxField K`). -/

section Existence

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

private theorem exists_algHom_apply_algebraMap (τ : K⸨X⸩ →ₐ[K] K⸨X⸩) :
    ∃ ρ : puiseuxField K →ₐ[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) = algebraMap K⸨X⸩ (puiseuxField K) (τ f) := by
  let : IsAlgClosed (ULift.{0} (puiseuxField K)) :=
    IsAlgClosed.of_ringEquiv (puiseuxField K) _ ULift.ringEquiv.symm
  let : Algebra K⸨X⸩ (ULift.{0} (puiseuxField K)) :=
    (ULift.ringEquiv.symm.toRingHom.comp
      ((algebraMap K⸨X⸩ (puiseuxField K)).comp τ.toRingHom)).toAlgebra
  let liftHom : puiseuxField K →ₐ[K⸨X⸩] ULift.{0} (puiseuxField K) := IsAlgClosed.lift
  let ρRing : puiseuxField K →+* puiseuxField K :=
    ULift.ringEquiv.toRingHom.comp liftHom.toRingHom
  have hF (f : K⸨X⸩) :
      ρRing (algebraMap K⸨X⸩ (puiseuxField K) f) = algebraMap K⸨X⸩ (puiseuxField K) (τ f) :=
    congrArg ULift.down (liftHom.commutes f)
  refine ⟨{ ρRing with commutes' := fun c ↦ ?_ }, hF⟩
  change ρRing (algebraMap K (puiseuxField K) c) = algebraMap K (puiseuxField K) c
  rw [IsScalarTower.algebraMap_apply K K⸨X⸩ (puiseuxField K), hF, τ.commutes]

/-- Over an algebraically closed field `K` of characteristic zero, every nonzero `φ ∈ X K⟦X⟧`
admits a continuous `K`-algebra endomorphism of `puiseuxField K` extending `substAlgHom hφ hφ₀`. -/
theorem exists_continuousAlgHom_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) :
    ∃ ρ : puiseuxField K →A[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f) := by
  obtain ⟨ρ, hρ⟩ := exists_algHom_apply_algebraMap (LaurentSeries.substAlgHom hφ hφ₀)
  exact ⟨continuousAlgHomOfSubst hφ hφ₀ ρ hρ, fun f ↦ hρ f⟩

/-- Over an algebraically closed field `K` of characteristic zero, every formal coordinate `φ`
admits a bicontinuous `K`-algebra automorphism of `puiseuxField K` extending
`LaurentSeries.substAlgEquiv φ`. -/
theorem exists_continuousAlgEquiv_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K) :
    ∃ ρ : puiseuxField K ≃A[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f) := by
  obtain ⟨ρ, hρ⟩ := (LaurentSeries.substAlgEquiv φ).exists_algEquiv_apply_algebraMap
    (Ω := puiseuxField K)
  exact ⟨continuousAlgEquivOfSubst φ ρ hρ, fun f ↦ hρ f⟩

end Existence

/-! ### Chain rule, residues, and continuous Kähler differentials (without continuity hypotheses) -/

section Calculus

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem apply_single_one_eq_algebraMap_coe {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    ρ (single K 1 1) = algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩) := by
  have ht : single K 1 1 = algebraMap K⸨X⸩ (puiseuxField K) (HahnSeries.single 1 1) := by
    rw [algebraMap_laurentSeries_apply]
    exact (levelEmbedding_single_self 1).symm
  rw [ht, h, LaurentSeries.substAlgHom_single_one]

/-- **Chain rule for algebraic lifts of Laurent substitutions.** For any `K`-algebra endomorphism
`ρ` of `puiseuxField K` extending `substAlgHom hφ hφ₀` (with no continuity assumption),
`d/dt (ρ x) = ρ (dx/dt) * φ'(t)`. -/
theorem derivation_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    derivation K (ρ x) =
      ρ (derivation K x) *
        algebraMap K⸨X⸩ (puiseuxField K) (_root_.LaurentSeries.derivative K (φ : K⸨X⸩)) := by
  rw [derivation_algHom_apply ρ (continuous_of_apply_algebraMap_substAlgHom hφ hφ₀ h),
    apply_single_one_eq_algebraMap_coe hφ hφ₀ h, derivation_algebraMap_laurentSeries]

/-- **Chain rule for algebraic lifts of formal coordinates.** -/
theorem derivation_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    derivation K (ρ x) =
      ρ (derivation K x) *
        algebraMap K⸨X⸩ (puiseuxField K)
          (_root_.LaurentSeries.derivative K (φ.toPowerSeries : K⸨X⸩)) :=
  derivation_of_apply_algebraMap_substAlgHom φ.constantCoeff_toPowerSeries
    φ.toPowerSeries_ne_zero (toAlgHom_apply_algebraMap_substAlgHom h) x

/-- **Finite-map residue formula for Puiseux substitution lifts.** For any algebraic lift `ρ` of
`substAlgHom hφ hφ₀`, `Res (ρ(x) φ'(t) dt) = ord φ • Res (x dt)`. -/
theorem residue_mul_derivative_of_apply_algebraMap_substAlgHom {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    residue K
        (ρ x * algebraMap K⸨X⸩ (puiseuxField K) (_root_.LaurentSeries.derivative K (φ : K⸨X⸩))) =
      φ.order.toNat • residue K x := by
  rw [← derivation_algebraMap_laurentSeries, ← apply_single_one_eq_algebraMap_coe hφ hφ₀ h,
    residue_map_mul_derivation_eq_mul ρ (continuous_of_apply_algebraMap_substAlgHom hφ hφ₀ h),
    order_single_one_of_apply_algebraMap_substAlgHom hφ hφ₀ h, Rat.cast_natCast, nsmul_eq_mul]

/-- **Coordinate-change invariance of Puiseux residues** (with no continuity assumption on the
lift `ρ`). -/
theorem residue_mul_derivative_of_apply_algebraMap_substAlgEquiv (φ : FormalCoordinate K)
    {ρ : puiseuxField K ≃ₐ[K] puiseuxField K}
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    residue K
        (ρ x * algebraMap K⸨X⸩ (puiseuxField K)
          (_root_.LaurentSeries.derivative K (φ.toPowerSeries : K⸨X⸩))) =
      residue K x := by
  simpa [AlgEquiv.coe_toAlgHom, φ.order_toPowerSeries] using
    residue_mul_derivative_of_apply_algebraMap_substAlgHom φ.constantCoeff_toPowerSeries
      φ.toPowerSeries_ne_zero (toAlgHom_apply_algebraMap_substAlgHom h) x

namespace ContinuousKaehlerDifferential

/-- Pullback of continuous Puiseux differentials along an algebraic lift `ρ` intertwining
`levelEmbedding K n` and `levelEmbedding K m` agrees with Laurent differential substitution. -/
theorem pullback_continuousAlgHomOfLevelSubst_levelMap (n m : ℕ+) {φ : K⟦X⟧}
    (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    (h : ∀ f, ρ (levelEmbedding K n f) = levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f))
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    pullback (continuousAlgHomOfLevelSubst n m hφ hφ₀ ρ h) (levelMap K n ω) =
      levelMap K m (TauCeti.ContinuousKaehlerDifferential.subst hφ hφ₀ ω) :=
  pullback_levelMap_subst (continuousAlgHomOfLevelSubst n m hφ hφ₀ ρ h) n m hφ hφ₀ (fun f ↦ h f) ω

section Subst

variable {φ : K⟦X⟧} (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
  (ρ : puiseuxField K →ₐ[K] puiseuxField K)

/-- Pullback along an algebraic lift of `substAlgHom hφ hφ₀` commutes with `levelMap K 1` and
Laurent differential substitution. -/
theorem pullback_continuousAlgHomOfSubst_levelMap_one
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    pullback (continuousAlgHomOfSubst hφ hφ₀ ρ h) (levelMap K 1 ω) =
      levelMap K 1 (TauCeti.ContinuousKaehlerDifferential.subst hφ hφ₀ ω) :=
  pullback_continuousAlgHomOfLevelSubst_levelMap 1 1 hφ hφ₀ ρ h ω

/-- Coordinate expression in the frame `dt` for pullback along a lift of `substAlgHom hφ hφ₀`. -/
theorem equivPuiseuxField_pullback_continuousAlgHomOfSubst
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (ω : ContinuousKaehlerDifferential K) :
    equivPuiseuxField K (pullback (continuousAlgHomOfSubst hφ hφ₀ ρ h) ω) =
      ρ (equivPuiseuxField K ω) *
        algebraMap K⸨X⸩ (puiseuxField K) (_root_.LaurentSeries.derivative K (φ : K⸨X⸩)) := by
  rw [equivPuiseuxField_pullback, continuousAlgHomOfSubst_apply, continuousAlgHomOfSubst_apply,
    apply_single_one_eq_algebraMap_coe hφ hφ₀ h, derivation_algebraMap_laurentSeries]

/-- Pullback along a lift of `substAlgHom hφ hφ₀` multiplies the residue of a continuous Puiseux
one-form by `ord φ`. -/
theorem residue_equivPuiseuxField_pullback_continuousAlgHomOfSubst
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (ω : ContinuousKaehlerDifferential K) :
    residue K (equivPuiseuxField K (pullback (continuousAlgHomOfSubst hφ hφ₀ ρ h) ω)) =
      φ.order.toNat • residue K (equivPuiseuxField K ω) := by
  rw [equivPuiseuxField_pullback_continuousAlgHomOfSubst]
  exact residue_mul_derivative_of_apply_algebraMap_substAlgHom hφ hφ₀ h _

end Subst

section Coordinate

variable (φ : FormalCoordinate K) (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)

/-- Pullback equivalence along an algebraic lift of a formal coordinate `φ` commutes with
`levelMap K 1` and `TauCeti.ContinuousKaehlerDifferential.substEquiv φ`. -/
theorem pullbackEquiv_continuousAlgEquivOfSubst_levelMap_one
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    pullbackEquiv (continuousAlgEquivOfSubst φ ρ h) (levelMap K 1 ω) =
      levelMap K 1 (TauCeti.ContinuousKaehlerDifferential.substEquiv φ ω) := by
  rw [pullbackEquiv_apply, TauCeti.ContinuousKaehlerDifferential.substEquiv_apply]
  refine pullback_levelMap_subst _ 1 1 φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
    (fun f ↦ ?_) ω
  simpa [algebraMap_laurentSeries_apply, LaurentSeries.coe_substAlgEquiv] using h f

/-- Pullback equivalence along an algebraic lift of a formal coordinate preserves the residue of
every continuous Puiseux one-form. -/
theorem residue_equivPuiseuxField_pullbackEquiv_continuousAlgEquivOfSubst
    (h : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (ω : ContinuousKaehlerDifferential K) :
    residue K (equivPuiseuxField K (pullbackEquiv (continuousAlgEquivOfSubst φ ρ h) ω)) =
      residue K (equivPuiseuxField K ω) := by
  rw [pullbackEquiv_apply]
  exact residue_equivPuiseuxField_pullback_of_order_eq_one
    (continuousAlgEquivOfSubst φ ρ h).toContinuousAlgHom
    (order_single_one_of_apply_algebraMap_substAlgEquiv φ h) ω

end Coordinate

end ContinuousKaehlerDifferential

end Calculus

end TauCeti.puiseuxField
