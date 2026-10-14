/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.NumberTheory.LocalField.NormedField
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# Algebraic extensions of a nonarchimedean local field

The spectral norm extends the normalized absolute value of a nonarchimedean local field `K`
to every algebraic extension `M/K`. This file constructs the corresponding normed field,
topology and valuative relation, and proves uniqueness of the extended absolute value and
valuation class. The structures are named definitions, installed locally, so an existing
compatible topology or valuative relation acquires no instance diamond.

The valuation ring is the integral closure of `𝒪[K]` in `M`. Algebra maps from algebraic
extensions preserve compatible valuations and therefore restrict to local maps of integer
rings and induce functorial embeddings of residue fields. Automorphisms preserve the valuation
and are continuous for its topology.

For finite-dimensional extensions, completeness and local compactness are proved in
`TauCeti.NumberTheory.LocalField.FiniteExtension.Basic`.

## Main definitions

* `TauCeti.algebraicExtensionNormedField`: the spectral norm as a normed field.
* `TauCeti.algebraicExtensionNormedFieldTopology`: the topology of that norm.
* `TauCeti.algebraicExtensionValuativeRel`: the valuative relation of that norm.
* `AlgHom.integerRingHom`, `AlgHom.residueFieldHom`: the induced maps on integers and residues.

## Main results

* `TauCeti.algebraicExtensionNormedField_norm_unique`: uniqueness of the extended absolute value.
* `TauCeti.algebraicExtensionValuation_isEquiv`: uniqueness of the extended valuation class.
* `TauCeti.algebraicExtensionValuativeRel_eq`: uniqueness of the extended valuative relation.
* `TauCeti.algebraicExtensionNormedFieldTopology_eq`: compatibility with a given valuative
  topology.
* `AlgHom.valuativeExtension`: algebra maps preserve the extended valuation.
* `TauCeti.integerRing_eq_integralClosure`: identification of the valuation ring with the integral
  closure of `𝒪[K]`.

## Implementation notes

The norm is Mathlib's `spectralNorm.normedField`, applied after locally installing
`normalizedNontriviallyNormedField K`; completeness and ultrametricity of `K` come from
`normalizedNormedField_completeSpace` and `normalizedNormedField_isUltrametricDist`. The
valuative topology comes from Mathlib's `NormedField.toValued`. Uniqueness of the valuation
uses the integrality of the minimal polynomial of any element of spectral norm at most `1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 (Theorem 4.8) and §6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (M : Type*) [Field M] [Algebra K M] [Algebra.IsAlgebraic K M]

/-- The normed-field structure on an algebraic extension `M` of a nonarchimedean local field `K`
given by the spectral norm of `M/K` with respect to the normalized absolute value of `K`. -/
@[expose, implicit_reducible]
def algebraicExtensionNormedField : NormedField M :=
  letI := normalizedNontriviallyNormedField K
  haveI := normalizedNormedField_completeSpace K
  haveI := normalizedNormedField_isUltrametricDist K
  spectralNorm.normedField K M

/-- The topology on an algebraic extension `M` of a nonarchimedean local field `K` induced by the
norm of `algebraicExtensionNormedField K M`. -/
@[expose, implicit_reducible]
def algebraicExtensionNormedFieldTopology : TopologicalSpace M :=
  (algebraicExtensionNormedField K M).toUniformSpace.toTopologicalSpace

/-- The norm of `algebraicExtensionNormedField K M` is the spectral norm of `M/K`. -/
theorem algebraicExtensionNormedField_norm_def (x : M) :
    letI := algebraicExtensionNormedField K M
    letI := normalizedNontriviallyNormedField K
    ‖x‖ = spectralNorm K M x := (rfl)

variable {K M} in
/-- The norm of `algebraicExtensionNormedField K M` extends the normalized absolute value of `K`. -/
@[simp]
theorem algebraicExtensionNormedField_norm_algebraMap (x : K) :
    letI := algebraicExtensionNormedField K M
    ‖algebraMap K M x‖ = normalizedAbsoluteValue K x := by
  let _ := normalizedNontriviallyNormedField K
  rw [algebraicExtensionNormedField_norm_def, spectralNorm_extends]
  exact normalizedNormedField_norm_def x

variable {M} in
/-- The norm of `algebraicExtensionNormedField K M` is the only real absolute value on `M` extending
the normalized absolute value of `K`. -/
theorem algebraicExtensionNormedField_norm_unique {f : AbsoluteValue M ℝ}
    (hf : ∀ x : K, f (algebraMap K M x) = normalizedAbsoluteValue K x) (x : M) :
    letI := algebraicExtensionNormedField K M
    f x = ‖x‖ := by
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_completeSpace K
  have := normalizedNormedField_isUltrametricDist K
  rw [algebraicExtensionNormedField_norm_def]
  exact spectralNorm_unique_field_norm_ext hf x

/-- The norm of `algebraicExtensionNormedField K M` is ultrametric. -/
theorem algebraicExtensionNormedField_isUltrametricDist :
    letI := algebraicExtensionNormedField K M
    IsUltrametricDist M := by
  let _ := algebraicExtensionNormedField K M
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_isUltrametricDist K
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm

/-- The valuative relation on an algebraic extension `M` of a nonarchimedean local field `K` defined
by the norm of `algebraicExtensionNormedField K M`: `x ≤ᵥ y` exactly when `‖x‖ ≤ ‖y‖`. -/
@[expose, implicit_reducible]
def algebraicExtensionValuativeRel : ValuativeRel M :=
  letI := algebraicExtensionNormedField K M
  haveI := algebraicExtensionNormedField_isUltrametricDist K M
  ValuativeRel.ofValuation (NormedField.valuation (K := M))

variable {K M} in
/-- The relation `algebraicExtensionValuativeRel K M` compares norms. -/
@[simp]
theorem algebraicExtensionValuativeRel_vle_iff (x y : M) :
    letI := algebraicExtensionValuativeRel K M
    letI := algebraicExtensionNormedField K M
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ :=
  -- `ValuativeRel.ofValuation` defines `x ≤ᵥ y` as `‖x‖₊ ≤ ‖y‖₊` for `NormedField.valuation`.
  NNReal.coe_le_coe

/-- The valuative relation `algebraicExtensionValuativeRel K M` extends the valuative relation
of `K`. -/
theorem algebraicExtension_valuativeExtension :
    letI := algebraicExtensionValuativeRel K M
    ValuativeExtension K M := by
  let _ := algebraicExtensionValuativeRel K M
  refine ⟨fun a b => ?_⟩
  rw [algebraicExtensionValuativeRel_vle_iff, algebraicExtensionNormedField_norm_algebraMap,
    algebraicExtensionNormedField_norm_algebraMap, NNRat.cast_le,
    normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff, (valuation K).vle_iff_le]

/-- The norm topology `algebraicExtensionNormedFieldTopology K M` is the valuative topology of
`algebraicExtensionValuativeRel K M`. -/
theorem algebraicExtension_isValuativeTopology :
    @IsValuativeTopology M _ (algebraicExtensionValuativeRel K M)
      (algebraicExtensionNormedFieldTopology K M) := by
  let _ := algebraicExtensionNormedField K M
  let _ := algebraicExtensionValuativeRel K M
  have := algebraicExtensionNormedField_isUltrametricDist K M
  have := Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle NormedField.valuation
    fun {s} => NormedField.toValued.is_topological_valuation s

/-! ### Uniqueness of the extended valuation -/

section Uniqueness

variable {K M} {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- The coefficients of the minimal polynomial over `K` of an element of `M` of spectral norm at
most `1` lie in `𝒪[K]`. -/
private theorem coeff_minpoly_mem_integer_of_algebraicExtensionNormedField_norm_le_one {x : M}
    (hx : letI := algebraicExtensionNormedField K M; ‖x‖ ≤ 1) (n : ℕ) :
    (minpoly K x).coeff n ∈ 𝒪[K] := by
  let _ := normalizedNontriviallyNormedField K
  have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : ‖(minpoly K x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hmon).1 hx n
  exact (mem_integer_iff_normalizedAbsoluteValue_le_one _).2
    (by exact_mod_cast (normalizedNormedField_norm_def ((minpoly K x).coeff n)).symm.trans_le h)

/-- If a valuation `w` on `M` restricts to the valuation class of `K`, every element of `M` of
spectral norm at most `1` has `w`-valuation at most `1`: the coefficients of its minimal
polynomial over `K` are integral, so it is integral over the valuation ring of `w`. -/
private theorem valuation_le_one_of_algebraicExtensionNormedField_norm_le_one
    {Γ' : Type*} [LinearOrderedCommMonoidWithZero Γ'] {w : Valuation M Γ'}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) {x : M}
    (hx : letI := algebraicExtensionNormedField K M; ‖x‖ ≤ 1) : w x ≤ 1 := by
  have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hcoeff (n : ℕ) : w (algebraMap K M ((minpoly K x).coeff n)) ≤ 1 := by
    simpa using hw.le_one_iff_le_one.2
      (coeff_minpoly_mem_integer_of_algebraicExtensionNormedField_norm_le_one hx n)
  refine w.le_one_of_root_monic (hmon.map (algebraMap K M)) (fun n _ => ?_) ?_
  · simpa using hcoeff n
  · rw [Polynomial.eval_map_algebraMap, minpoly.aeval]

/-- If a valuation `w` on `M` restricts to the valuation class of `K`, every element of `M` of
spectral norm less than `1` has `w`-valuation less than `1`. -/
private theorem valuation_lt_one_of_algebraicExtensionNormedField_norm_lt_one {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) {x : M}
    (hx : letI := algebraicExtensionNormedField K M; ‖x‖ < 1) : w x < 1 := by
  let _ := algebraicExtensionNormedField K M
  -- Compare a power of `x` with an element `y` of `K` with `0 < ‖y‖ < 1`.
  obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hy0' : algebraMap K M y ≠ 0 := by simpa using hy0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hy0') hx
  have h : w (x ^ k / algebraMap K M y) ≤ 1 := by
    refine valuation_le_one_of_algebraicExtensionNormedField_norm_le_one hw ?_
    rw [norm_div, norm_pow, div_le_one₀ (norm_pos_iff.2 hy0')]
    exact hk.le
  have hwy : w (algebraMap K M y) < 1 := by simpa using hw.lt_one_iff_lt_one.2 hy1
  have hwy0 : w (algebraMap K M y) ≠ 0 := by simpa using hy0'
  rw [map_div₀, map_pow, div_le_one₀ (zero_lt_iff.2 hwy0)] at h
  by_contra hx1
  exact ((one_le_pow₀ (not_lt.1 hx1)).trans h).not_gt hwy

/-- A valuation `w` on an algebraic extension `M` of a nonarchimedean local field
`K` which restricts to the valuation class of `K` has the closed unit ball of the spectral norm of
`M/K` as its valuation ring. -/
theorem algebraicExtensionNormedField_norm_le_one_iff {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) (x : M) :
    letI := algebraicExtensionNormedField K M
    ‖x‖ ≤ 1 ↔ w x ≤ 1 := by
  let _ := algebraicExtensionNormedField K M
  refine ⟨valuation_le_one_of_algebraicExtensionNormedField_norm_le_one hw, fun h => ?_⟩
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h' := valuation_lt_one_of_algebraicExtensionNormedField_norm_lt_one hw (x := x⁻¹)
    (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (not_le.1 hx))
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 (by simpa using hx0))] at h'
  exact h'.not_ge h

/-- A valuation `w` on an algebraic extension `M` of a nonarchimedean local field
`K` which restricts to the valuation class of `K` induces the same order on `M` as the spectral
norm of `M/K`. -/
theorem algebraicExtensionNormedField_norm_le_norm_iff {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) (x y : M) :
    letI := algebraicExtensionNormedField K M
    ‖x‖ ≤ ‖y‖ ↔ w x ≤ w y := by
  let _ := algebraicExtensionNormedField K M
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hwy : w y ≠ 0 := by simpa using hy
  have h := algebraicExtensionNormedField_norm_le_one_iff hw (x / y)
  rwa [norm_div, div_le_one₀ (norm_pos_iff.2 hy), map_div₀, div_le_one₀ (zero_lt_iff.2 hwy)] at h

/-- **Uniqueness of the extended valuation.** Any two valuations on an algebraic extension `M` of a
nonarchimedean local field `K` which restrict to the valuation class of `K` are equivalent. -/
theorem algebraicExtensionValuation_isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂] {w₁ : Valuation M Γ₁} {w₂ : Valuation M Γ₂}
    (h₁ : (w₁.comap (algebraMap K M)).IsEquiv (valuation K))
    (h₂ : (w₂.comap (algebraMap K M)).IsEquiv (valuation K)) :
    w₁.IsEquiv w₂ := fun x y =>
  (algebraicExtensionNormedField_norm_le_norm_iff h₁ x y).symm.trans
    (algebraicExtensionNormedField_norm_le_norm_iff h₂ x y)

variable (K) in
/-- For any valuative relation on an algebraic extension `M` of a nonarchimedean local field `K`
extending that of `K`, `x ≤ᵥ y` holds exactly when the spectral norm of `x` is at most that of
`y`. -/
theorem vle_iff_algebraicExtensionNormedField_norm_le [ValuativeRel M]
    [ValuativeExtension K M] (x y : M) :
    letI := algebraicExtensionNormedField K M
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [(valuation M).vle_iff_le, algebraicExtensionNormedField_norm_le_norm_iff
    (ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K))]

variable (K M) in
/-- **Uniqueness of the extended valuative relation.** A valuative relation on an algebraic
extension `M` of a nonarchimedean local field `K` which extends that of `K` is the relation
`algebraicExtensionValuativeRel K M` of the spectral norm. -/
theorem algebraicExtensionValuativeRel_eq [ValuativeRel M] [ValuativeExtension K M] :
    algebraicExtensionValuativeRel K M = ‹ValuativeRel M› := by
  ext x y
  exact algebraicExtensionValuativeRel_vle_iff x y |>.trans
    (vle_iff_algebraicExtensionNormedField_norm_le K x y).symm

variable (K M) in
/-- The topology `algebraicExtensionNormedFieldTopology K M` of the spectral norm is the topology of
any valuative topological structure on `M` whose valuative relation extends that of `K`. -/
theorem algebraicExtensionNormedFieldTopology_eq [ValuativeRel M] [ValuativeExtension K M]
    [TopologicalSpace M] [IsValuativeTopology M] :
    algebraicExtensionNormedFieldTopology K M = ‹TopologicalSpace M› := by
  have h := algebraicExtension_isValuativeTopology K M
  rw [algebraicExtensionValuativeRel_eq K M] at h
  -- Both topologies are valuative for the same relation, so they have the same neighbourhoods.
  refine TopologicalSpace.ext_nhds fun x => Filter.ext fun s => ?_
  rw [@IsValuativeTopology.mem_nhds_iff _ _ _ (algebraicExtensionNormedFieldTopology K M) h,
    IsValuativeTopology.mem_nhds_iff]

/-- **Galois invariance of the valuation.** Every `K`-algebra automorphism of an algebraic extension
`M` of a nonarchimedean local field `K` preserves the canonical valuation of any valuative relation
on `M` extending that of `K`. -/
@[simp]
theorem _root_.AlgEquiv.valuation_eq [ValuativeRel M] [ValuativeExtension K M] (σ : M ≃ₐ[K] M)
    (x : M) : valuation M (σ x) = valuation M x := by
  let _ := algebraicExtensionNormedField K M
  let _ := normalizedNontriviallyNormedField K
  have hw := ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K)
  -- The spectral norm is invariant under `K`-algebra automorphisms.
  have h : ‖σ x‖ = ‖x‖ := (spectralNorm_eq_of_equiv σ x).symm
  exact le_antisymm ((algebraicExtensionNormedField_norm_le_norm_iff hw _ _).1 h.le)
    ((algebraicExtensionNormedField_norm_le_norm_iff hw _ _).1 h.ge)

/-- **Embeddings respect the extended valuations.** A `K`-algebra map `ι : M →ₐ[K] N` from an
algebraic extension `M` of a nonarchimedean local field `K` to a commutative ring `N`, with
valuative relations on `M` and `N` both extending that of `K`, makes `N` a valuative extension of
`M` through `ι.toAlgebra`. -/
theorem _root_.AlgHom.valuativeExtension {N : Type*} [CommRing N] [ValuativeRel N] [Algebra K N]
    [ValuativeExtension K N] [ValuativeRel M] [ValuativeExtension K M] (ι : M →ₐ[K] N) :
    letI := ι.toAlgebra
    ValuativeExtension M N := by
  let _ := ι.toAlgebra
  -- The valuation of `N` pulled back along `ι` extends the valuation class of `K`, so by
  -- uniqueness it is the valuation of `M`.
  have hN := ValuativeRel.isEquiv ((valuation N).comap (algebraMap K N)) (valuation K)
  rw [← ι.comp_algebraMap, Valuation.comap_comp] at hN
  have h := algebraicExtensionValuation_isEquiv hN
    (ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K))
  exact ⟨fun a b ↦ (valuation N).vle_iff_le.trans ((h a b).trans (valuation M).vle_iff_le.symm)⟩

end Uniqueness

/-! ### The ring of integers is the integral closure -/

section IntegralClosure

variable {K M} [ValuativeRel M] [ValuativeExtension K M]

/-- **The integers of an algebraic extension are the integral elements.** Let `M` be an algebraic
extension of a nonarchimedean local field `K`, with a valuative relation extending that of `K`,
and let `O` be any ring of integers of `K`, that is, `(valuation K).Integers O`. An element of
`M` is integral over `O` exactly when its valuation is at most `1`; see Neukirch, Chapter II,
§4 and §6. -/
theorem _root_.Valuation.Integers.isIntegral_iff_valuation_le_one {O : Type*} [CommRing O]
    [Algebra O K] [Algebra O M] [IsScalarTower O K M] (hO : (valuation K).Integers O) (x : M) :
    IsIntegral O x ↔ valuation M x ≤ 1 := by
  have hw := ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K)
  constructor
  · -- A root of a monic polynomial with coefficients of valuation at most `1` has valuation at
    -- most `1`.
    rintro ⟨p, hp, hpx⟩
    refine (valuation M).le_one_of_root_monic (hp.map (algebraMap O M)) (fun n _ => ?_) ?_
    · rw [Polynomial.coeff_map, IsScalarTower.algebraMap_apply O K M]
      exact hw.le_one_iff_le_one.2 (hO.map_le_one _)
    · rwa [Polynomial.eval_map]
  · -- The minimal polynomial over `K` has coefficients in `𝒪[K]`, so it lifts to a monic
    -- polynomial over `O`.
    intro hx
    let _ := algebraicExtensionNormedField K M
    have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
    have hlifts : minpoly K x ∈ Polynomial.lifts (algebraMap O K) :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun n => hO.exists_of_le_one
        (coeff_minpoly_mem_integer_of_algebraicExtensionNormedField_norm_le_one
          ((algebraicExtensionNormedField_norm_le_one_iff hw x).2 hx) n)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmon
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq, minpoly.aeval]

variable (K M) in
/-- The ring of integers `𝒪[M]` of an algebraic extension `M` of a nonarchimedean local field `K`,
for a valuative relation extending that of `K`, is the integral closure of `𝒪[K]` in `M`. -/
theorem integerRing_eq_integralClosure :
    𝒪[M] = (integralClosure 𝒪[K] M).toSubring := by
  ext x
  rw [Subalgebra.mem_toSubring, mem_integralClosure_iff,
    Valuation.Integers.isIntegral_iff_valuation_le_one
      (Valuation.integer.integers (valuation K)),
    Valuation.mem_integer_iff]

end IntegralClosure

section IntegerRingEquiv

variable {K M} [ValuativeRel M] [ValuativeExtension K M]
variable {L : Type*} [Field L] [ValuativeRel L] [Algebra K L]
  [ValuativeExtension K L]

variable (K M) in
/-- The ring of integers `𝒪[M]` of an algebraic extension `M` of a nonarchimedean local field `K`,
as an `𝒪[K]`-algebra, is the integral closure of `𝒪[K]` in `M`; this is the equivalence given by
`integerRing_eq_integralClosure`. -/
def integerRingEquivIntegralClosure : 𝒪[M] ≃ₐ[𝒪[K]] integralClosure 𝒪[K] M :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr (integerRing_eq_integralClosure K M))
    fun _ ↦ Subtype.ext (RingEquiv.coe_subringCongr_apply _ _)

/-- The equivalence `integerRingEquivIntegralClosure` does not change the underlying element. -/
@[simp]
theorem coe_integerRingEquivIntegralClosure_apply (x : 𝒪[M]) :
    (integerRingEquivIntegralClosure K M x : M) = x := by
  rw [integerRingEquivIntegralClosure, AlgEquiv.ofRingEquiv_apply]
  exact RingEquiv.coe_subringCongr_apply _ _

/-- The inverse of `integerRingEquivIntegralClosure` does not change the underlying element. -/
@[simp]
theorem coe_integerRingEquivIntegralClosure_symm_apply (x : integralClosure 𝒪[K] M) :
    ((integerRingEquivIntegralClosure K M).symm x : M) = x := by
  conv_rhs => rw [← (integerRingEquivIntegralClosure K M).apply_symm_apply x]
  exact (coe_integerRingEquivIntegralClosure_apply _).symm

/-- A base-field algebra equivalence restricts to an algebra equivalence of integer rings. -/
def _root_.AlgEquiv.integerRingEquiv (e : L ≃ₐ[K] M) : 𝒪[L] ≃ₐ[𝒪[K]] 𝒪[M] :=
  letI := e.symm.isAlgebraic
  ((integerRingEquivIntegralClosure K L).trans (e.restrictScalars 𝒪[K]).mapIntegralClosure).trans
    (integerRingEquivIntegralClosure K M).symm

/-- The integer-ring equivalence acts by the original field equivalence. -/
@[simp]
theorem _root_.AlgEquiv.coe_integerRingEquiv_apply (e : L ≃ₐ[K] M) (x : 𝒪[L]) :
    (e.integerRingEquiv x : M) = e (x : L) := by
  simp [AlgEquiv.integerRingEquiv]

end IntegerRingEquiv

variable {K M} in
/-- **Galois automorphisms are continuous.** Every `K`-algebra automorphism of an algebraic
extension `M` of a nonarchimedean local field `K` is continuous for its valuative topology, since
it preserves the valuation. -/
theorem _root_.AlgEquiv.continuous_of_valuativeExtension [ValuativeRel M]
    [ValuativeExtension K M] [TopologicalSpace M] [IsValuativeTopology M] (σ : M ≃ₐ[K] M) :
    Continuous σ := by
  refine continuous_of_continuousAt_zero σ ?_
  rw [ContinuousAt, map_zero]
  exact ((IsValuativeTopology.hasBasis_nhds_zero M).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero M)).mpr fun γ _ ↦
      ⟨γ, trivial, fun x hx ↦ by simpa [σ.valuation_eq] using hx⟩

end TauCeti

namespace AlgHom

open TauCeti

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsAlgebraic K L] [Field M] [ValuativeRel M] [Algebra K M] [ValuativeExtension K M]

/-- A base-field algebra map from an algebraic extension to a compatible valued field restricts to
an algebra map of integer rings. -/
def integerRingHom (ι : L →ₐ[K] M) : 𝒪[L] →ₐ[𝒪[K]] 𝒪[M] := by
  let _ := ι.toAlgebra
  have := ι.valuativeExtension
  refine
    { ι.toRingHom.restrict 𝒪[L] 𝒪[M] (fun x hx ↦ ?_) with
      commutes' := fun x ↦ Subtype.ext ?_ }
  · exact (Valuation.HasExtension.val_map_le_one_iff (valuation L) (valuation M) x).2 hx
  · simp

/-- The integer-ring map acts by the original field map. -/
@[simp]
theorem coe_integerRingHom_apply (ι : L →ₐ[K] M) (x : 𝒪[L]) :
    (ι.integerRingHom x : M) = ι (x : L) := (rfl)

/-- Restricting a composite embedding to integer rings gives the composite restrictions. -/
@[simp]
theorem integerRingHom_comp {N : Type*} [Field N] [ValuativeRel N] [Algebra K N]
    [ValuativeExtension K N] [Algebra.IsAlgebraic K M] (ι₂ : M →ₐ[K] N) (ι₁ : L →ₐ[K] M) :
    (ι₂.comp ι₁).integerRingHom = ι₂.integerRingHom.comp ι₁.integerRingHom := by
  ext x
  simp

/-- Restricting the identity embedding to integer rings gives the identity. -/
@[simp]
theorem integerRingHom_id : (AlgHom.id K L).integerRingHom = AlgHom.id 𝒪[K] 𝒪[L] := by
  ext x
  simp

/-- A `K`-embedding from an algebraic extension of a nonarchimedean local field to a compatible
valued field restricts to a local homomorphism of their rings of integers. -/
instance isLocalHom_integerRingHom (ι : L →ₐ[K] M) : IsLocalHom ι.integerRingHom := by
  let _ := ι.toAlgebra
  have := ι.valuativeExtension
  have hmap : (ι.integerRingHom : 𝒪[L] →+* 𝒪[M]) = algebraMap 𝒪[L] 𝒪[M] := by
    ext x
    simp only [coe_integerRingHom_apply, TauCeti.coe_algebraMap_integerRing]
  have hlocal : IsLocalHom (ι.integerRingHom : 𝒪[L] →+* 𝒪[M]) :=
    hmap.symm ▸ (inferInstance : IsLocalHom (algebraMap 𝒪[L] 𝒪[M]))
  exact ⟨hlocal.map_nonunit⟩

/-- The embedding of residue fields induced by a `K`-embedding from an algebraic extension of a
nonarchimedean local field `K` to a compatible valued field. It is linear over the residue field
of `K`. -/
noncomputable def residueFieldHom (ι : L →ₐ[K] M) : 𝓀[L] →ₐ[𝓀[K]] 𝓀[M] :=
  IsLocalRing.ResidueField.mapAlgHom' ι.integerRingHom

/-- The induced embedding of residue fields sends the residue of an integer `x` to the residue of
its image. -/
@[simp]
theorem residueFieldHom_residue (ι : L →ₐ[K] M) (x : 𝒪[L]) :
    ι.residueFieldHom (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[M] (ι.integerRingHom x) :=
  IsLocalRing.ResidueField.mapAlgHom'_residue _ _

/-- Passing to residue fields is functorial. -/
@[simp]
theorem residueFieldHom_comp {N : Type*} [Field N] [ValuativeRel N] [Algebra K N]
    [ValuativeExtension K N] [Algebra.IsAlgebraic K M] (ι₂ : M →ₐ[K] N) (ι₁ : L →ₐ[K] M) :
    (ι₂.comp ι₁).residueFieldHom = ι₂.residueFieldHom.comp ι₁.residueFieldHom := by
  ext x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  simp only [residueFieldHom_residue, AlgHom.comp_apply]
  exact congrArg _ (Subtype.ext (by simp))

/-- Passing the identity embedding to residue fields gives the identity embedding. -/
@[simp]
theorem residueFieldHom_id : (AlgHom.id K L).residueFieldHom = AlgHom.id 𝓀[K] 𝓀[L] := by
  ext x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  simp only [residueFieldHom_residue, AlgHom.id_apply]
  exact congrArg _ (Subtype.ext (by simp))

end AlgHom

namespace IntermediateField

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- A compatible valued ambient field is a valuative extension of any algebraic intermediate
field carrying a valuation extending the base-field valuation. -/
theorem valuativeExtension [ValuativeRel Ω] [ValuativeExtension K Ω]
    (E : IntermediateField K Ω) [Algebra.IsAlgebraic K E] [ValuativeRel E]
    [ValuativeExtension K E] : ValuativeExtension E Ω := by
  have h := E.val.valuativeExtension
  exact ⟨fun a b ↦ h.vle_iff_vle a b⟩

end IntermediateField
