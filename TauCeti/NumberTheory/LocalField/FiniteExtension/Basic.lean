/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.NumberTheory.LocalField.NormedField
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# Finite extensions of a nonarchimedean local field are local fields

Let `K` be a nonarchimedean local field and let `M` be a field that is a finite-dimensional
`K`-algebra, with no topology or valuative relation assumed on `M`. Since `K` is complete for its
normalized absolute value (`TauCeti.normalizedNormedField`), the spectral norm of `M/K` is a
multiplicative ultrametric norm on `M` extending that absolute value, and it is the only absolute
value on `M` that does so. This file equips `M` with the resulting normed field, its topology,
and the valuative relation of the norm, and proves that with these structures `M` is a
nonarchimedean local field whose valuation extends that of `K`.

Completeness of `K` also makes this extension of the valuation unique: any valuation on `M`
restricting to the valuation class of `K` induces the order of the spectral norm, since an
element of spectral norm at most `1` has a minimal polynomial with integral coefficients. Hence
any valuative relation on `M` extending that of `K` is the one constructed here, any compatible
valuative topology on `M` is the norm topology, and every `K`-algebra automorphism of `M`
preserves the valuation. The same integrality of the minimal polynomial identifies the ring of
integers of `M` with the integral closure of that of `K`.

All structures are named definitions rather than global instances, so that a field already
carrying a compatible topology or valuative relation acquires no diamond. They are meant to be
installed locally, as in `letI := finiteExtensionValuativeRel K M`.

## Main definitions

* `TauCeti.finiteExtensionNormedField K M`: the spectral norm of `M/K` as a normed field.
* `TauCeti.finiteExtensionNormedFieldTopology K M`: the topology of that norm.
* `TauCeti.finiteExtensionValuativeRel K M`: the valuative relation of that norm.

## Main results

* `TauCeti.finiteExtensionNormedField_norm_algebraMap`: the norm extends the normalized absolute
  value of `K`.
* `TauCeti.finiteExtensionNormedField_norm_unique`: it is the only absolute value on `M` doing so.
* `TauCeti.finiteExtensionNormedField_completeSpace`: `M` is complete for the norm.
* `TauCeti.finiteExtension_valuativeExtension`: the valuative relation on `M` extends that of `K`.
* `TauCeti.finiteExtension_isValuativeTopology`: the norm topology is the valuative topology.
* `TauCeti.finiteExtension_isNonarchimedeanLocalField`: `M` is a nonarchimedean local field.
* `TauCeti.finiteExtensionNormedField_norm_le_norm_iff`: a valuation on `M` restricting to the
  valuation class of `K` induces the order of the spectral norm.
* `TauCeti.finiteExtensionValuation_isEquiv`: any two such valuations are equivalent.
* `TauCeti.finiteExtensionValuativeRel_eq`: any valuative relation on `M` extending that of `K`
  is `finiteExtensionValuativeRel K M`.
* `TauCeti.finiteExtensionNormedFieldTopology_eq`: any valuative topology for such a relation is
  the norm topology.
* `AlgEquiv.valuation_eq`: `K`-algebra automorphisms of `M` preserve the valuation.
* `TauCeti.normalizedValuation_algEquiv`: the corresponding invariance of the normalized
  valuation on units.
* `Valuation.Integers.isIntegral_iff_valuation_le_one`: for any valuative relation on `M`
  extending that of `K`, an element of `M` is integral over a ring of integers of `K` exactly when
  its valuation is at most `1`.
* `TauCeti.integerRing_eq_integralClosure`: `𝒪[M]` is the integral closure of `𝒪[K]` in `M`.

## Implementation notes

The norm is Mathlib's `spectralNorm.normedField`, applied after locally installing
`normalizedNontriviallyNormedField K`; the needed completeness and ultrametricity of `K` are
`normalizedNormedField_completeSpace` and `normalizedNormedField_isUltrametricDist`. The
valuative topology comes from Mathlib's `NormedField.toValued`, and local compactness of `M`
from `FiniteDimensional.proper`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 (Theorem 4.8) and §6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (M : Type*) [Field M] [Algebra K M] [Module.Finite K M]

/-- The normed-field structure on a finite extension `M` of a nonarchimedean local field `K`
given by the spectral norm of `M/K` with respect to the normalized absolute value of `K`. -/
@[expose, implicit_reducible]
def finiteExtensionNormedField : NormedField M :=
  letI := normalizedNontriviallyNormedField K
  haveI := normalizedNormedField_completeSpace K
  haveI := normalizedNormedField_isUltrametricDist K
  spectralNorm.normedField K M

/-- The topology on a finite extension `M` of a nonarchimedean local field `K` induced by the
norm of `finiteExtensionNormedField K M`. -/
@[expose, implicit_reducible]
def finiteExtensionNormedFieldTopology : TopologicalSpace M :=
  (finiteExtensionNormedField K M).toUniformSpace.toTopologicalSpace

/-- The norm of `finiteExtensionNormedField K M` is the spectral norm of `M/K`. -/
theorem finiteExtensionNormedField_norm_def (x : M) :
    letI := finiteExtensionNormedField K M
    letI := normalizedNontriviallyNormedField K
    ‖x‖ = spectralNorm K M x := (rfl)

variable {K M} in
/-- The norm of `finiteExtensionNormedField K M` extends the normalized absolute value of `K`. -/
@[simp]
theorem finiteExtensionNormedField_norm_algebraMap (x : K) :
    letI := finiteExtensionNormedField K M
    ‖algebraMap K M x‖ = normalizedAbsoluteValue K x := by
  let _ := normalizedNontriviallyNormedField K
  rw [finiteExtensionNormedField_norm_def, spectralNorm_extends]
  exact normalizedNormedField_norm_def x

variable {M} in
/-- The norm of `finiteExtensionNormedField K M` is the only real absolute value on `M` extending
the normalized absolute value of `K`. -/
theorem finiteExtensionNormedField_norm_unique {f : AbsoluteValue M ℝ}
    (hf : ∀ x : K, f (algebraMap K M x) = normalizedAbsoluteValue K x) (x : M) :
    letI := finiteExtensionNormedField K M
    f x = ‖x‖ := by
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_completeSpace K
  have := normalizedNormedField_isUltrametricDist K
  rw [finiteExtensionNormedField_norm_def]
  exact spectralNorm_unique_field_norm_ext hf x

/-- The norm of `finiteExtensionNormedField K M` is ultrametric. -/
theorem finiteExtensionNormedField_isUltrametricDist :
    letI := finiteExtensionNormedField K M
    IsUltrametricDist M := by
  let _ := finiteExtensionNormedField K M
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_isUltrametricDist K
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm

/-- A finite extension of a nonarchimedean local field is complete for the norm of
`finiteExtensionNormedField K M`. -/
theorem finiteExtensionNormedField_completeSpace :
    letI := finiteExtensionNormedField K M
    CompleteSpace M := by
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_completeSpace K
  have := normalizedNormedField_isUltrametricDist K
  exact spectralNorm.completeSpace K M

/-- The valuative relation on a finite extension `M` of a nonarchimedean local field `K` defined
by the norm of `finiteExtensionNormedField K M`: `x ≤ᵥ y` exactly when `‖x‖ ≤ ‖y‖`. -/
@[expose, implicit_reducible]
def finiteExtensionValuativeRel : ValuativeRel M :=
  letI := finiteExtensionNormedField K M
  haveI := finiteExtensionNormedField_isUltrametricDist K M
  ValuativeRel.ofValuation (NormedField.valuation (K := M))

variable {K M} in
/-- The relation `finiteExtensionValuativeRel K M` compares norms. -/
@[simp]
theorem finiteExtensionValuativeRel_vle_iff (x y : M) :
    letI := finiteExtensionValuativeRel K M
    letI := finiteExtensionNormedField K M
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ :=
  -- `ValuativeRel.ofValuation` defines `x ≤ᵥ y` as `‖x‖₊ ≤ ‖y‖₊` for `NormedField.valuation`.
  NNReal.coe_le_coe

/-- The valuative relation `finiteExtensionValuativeRel K M` extends the valuative relation
of `K`. -/
theorem finiteExtension_valuativeExtension :
    letI := finiteExtensionValuativeRel K M
    ValuativeExtension K M := by
  let _ := finiteExtensionValuativeRel K M
  refine ⟨fun a b => ?_⟩
  rw [finiteExtensionValuativeRel_vle_iff, finiteExtensionNormedField_norm_algebraMap,
    finiteExtensionNormedField_norm_algebraMap, NNRat.cast_le,
    normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff, (valuation K).vle_iff_le]

/-- The norm topology `finiteExtensionNormedFieldTopology K M` is the valuative topology of
`finiteExtensionValuativeRel K M`. -/
theorem finiteExtension_isValuativeTopology :
    @IsValuativeTopology M _ (finiteExtensionValuativeRel K M)
      (finiteExtensionNormedFieldTopology K M) := by
  let _ := finiteExtensionNormedField K M
  let _ := finiteExtensionValuativeRel K M
  have := finiteExtensionNormedField_isUltrametricDist K M
  have := Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle NormedField.valuation
    fun {s} => NormedField.toValued.is_topological_valuation s

/-- A finite extension `M` of a nonarchimedean local field `K`, with the topology and valuative
relation of the spectral norm, is a nonarchimedean local field. -/
theorem finiteExtension_isNonarchimedeanLocalField :
    @IsNonarchimedeanLocalField M _ (finiteExtensionValuativeRel K M)
      (finiteExtensionNormedFieldTopology K M) := by
  let _ := finiteExtensionNormedField K M
  let _ := finiteExtensionValuativeRel K M
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_isUltrametricDist K
  have := normalizedNormedField_completeSpace K
  have := finiteExtensionNormedField_isUltrametricDist K M
  have := finiteExtension_isValuativeTopology K M
  -- Local compactness: `K` is locally compact for its norm, so the finite-dimensional normed
  -- `K`-space `M` is proper.
  have : @LocallyCompactSpace K (normalizedNormedFieldTopology K) := by
    rw [normalizedNormedField_topology_eq]
    infer_instance
  let _ := spectralNorm.normedSpace K M
  have : ProperSpace M := FiniteDimensional.proper K M
  -- Nontriviality: an element of `K` of valuation strictly between `0` and `1` keeps its
  -- absolute value in `M`.
  have : ValuativeRel.IsNontrivial M := by
    have := Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
    refine (isNontrivial_iff_isNontrivial NormedField.valuation).2 ?_
    obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    refine ⟨⟨algebraMap K M y, by simpa using hy0, fun h => ?_⟩⟩
    have h' : ‖algebraMap K M y‖ = 1 := by simpa using congrArg NNReal.toReal h
    rw [finiteExtensionNormedField_norm_algebraMap] at h'
    exact ((normalizedAbsoluteValue_lt_one_iff y).2 hy1).ne (mod_cast h')
  exact { }

/-! ### Uniqueness of the extended valuation -/

section Uniqueness

variable {K M} {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- The coefficients of the minimal polynomial over `K` of an element of `M` of spectral norm at
most `1` lie in `𝒪[K]`. -/
private theorem coeff_minpoly_mem_integer_of_finiteExtensionNormedField_norm_le_one {x : M}
    (hx : letI := finiteExtensionNormedField K M; ‖x‖ ≤ 1) (n : ℕ) :
    (minpoly K x).coeff n ∈ 𝒪[K] := by
  let _ := normalizedNontriviallyNormedField K
  have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : ‖(minpoly K x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hmon).1 hx n
  exact (mem_integer_iff_normalizedAbsoluteValue_le_one _).2
    (by exact_mod_cast (normalizedNormedField_norm_def ((minpoly K x).coeff n)).symm.trans_le h)

/-- If a valuation `w` on `M` restricts to the valuation class of `K`, every element of `M` of
spectral norm at most `1` has `w`-valuation at most `1`: the coefficients of its minimal
polynomial over `K` are integral, so it is integral over the valuation ring of `w`. -/
private theorem valuation_le_one_of_finiteExtensionNormedField_norm_le_one {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) {x : M}
    (hx : letI := finiteExtensionNormedField K M; ‖x‖ ≤ 1) : w x ≤ 1 := by
  have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hcoeff (n : ℕ) : w (algebraMap K M ((minpoly K x).coeff n)) ≤ 1 := by
    simpa using hw.le_one_iff_le_one.2
      (coeff_minpoly_mem_integer_of_finiteExtensionNormedField_norm_le_one hx n)
  refine w.le_one_of_root_monic (hmon.map (algebraMap K M)) (fun n _ => ?_) ?_
  · simpa using hcoeff n
  · rw [Polynomial.eval_map_algebraMap, minpoly.aeval]

/-- If a valuation `w` on `M` restricts to the valuation class of `K`, every element of `M` of
spectral norm less than `1` has `w`-valuation less than `1`. -/
private theorem valuation_lt_one_of_finiteExtensionNormedField_norm_lt_one {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) {x : M}
    (hx : letI := finiteExtensionNormedField K M; ‖x‖ < 1) : w x < 1 := by
  let _ := finiteExtensionNormedField K M
  -- Compare a power of `x` with an element `y` of `K` with `0 < ‖y‖ < 1`.
  obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hy0' : algebraMap K M y ≠ 0 := by simpa using hy0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hy0') hx
  have h : w (x ^ k / algebraMap K M y) ≤ 1 := by
    refine valuation_le_one_of_finiteExtensionNormedField_norm_le_one hw ?_
    rw [norm_div, norm_pow, div_le_one₀ (norm_pos_iff.2 hy0')]
    exact hk.le
  have hwy : w (algebraMap K M y) < 1 := by simpa using hw.lt_one_iff_lt_one.2 hy1
  have hwy0 : w (algebraMap K M y) ≠ 0 := by simpa using hy0'
  rw [map_div₀, map_pow, div_le_one₀ (zero_lt_iff.2 hwy0)] at h
  by_contra hx1
  exact ((one_le_pow₀ (not_lt.1 hx1)).trans h).not_gt hwy

/-- A valuation `w` on a finite extension `M` of a nonarchimedean local field `K` which restricts
to the valuation class of `K` has the closed unit ball of the spectral norm of `M/K` as its
valuation ring. -/
theorem finiteExtensionNormedField_norm_le_one_iff {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) (x : M) :
    letI := finiteExtensionNormedField K M
    ‖x‖ ≤ 1 ↔ w x ≤ 1 := by
  let _ := finiteExtensionNormedField K M
  refine ⟨valuation_le_one_of_finiteExtensionNormedField_norm_le_one hw, fun h => ?_⟩
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h' := valuation_lt_one_of_finiteExtensionNormedField_norm_lt_one hw (x := x⁻¹)
    (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (not_le.1 hx))
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 (by simpa using hx0))] at h'
  exact h'.not_ge h

/-- A valuation `w` on a finite extension `M` of a nonarchimedean local field `K` which restricts
to the valuation class of `K` induces the same order on `M` as the spectral norm of `M/K`. -/
theorem finiteExtensionNormedField_norm_le_norm_iff {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) (x y : M) :
    letI := finiteExtensionNormedField K M
    ‖x‖ ≤ ‖y‖ ↔ w x ≤ w y := by
  let _ := finiteExtensionNormedField K M
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hwy : w y ≠ 0 := by simpa using hy
  have h := finiteExtensionNormedField_norm_le_one_iff hw (x / y)
  rwa [norm_div, div_le_one₀ (norm_pos_iff.2 hy), map_div₀, div_le_one₀ (zero_lt_iff.2 hwy)] at h

/-- **Uniqueness of the extended valuation.** Any two valuations on a finite extension `M` of a
nonarchimedean local field `K` which restrict to the valuation class of `K` are equivalent. -/
theorem finiteExtensionValuation_isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂] {w₁ : Valuation M Γ₁} {w₂ : Valuation M Γ₂}
    (h₁ : (w₁.comap (algebraMap K M)).IsEquiv (valuation K))
    (h₂ : (w₂.comap (algebraMap K M)).IsEquiv (valuation K)) :
    w₁.IsEquiv w₂ := fun x y =>
  (finiteExtensionNormedField_norm_le_norm_iff h₁ x y).symm.trans
    (finiteExtensionNormedField_norm_le_norm_iff h₂ x y)

variable (K) in
/-- For any valuative relation on a finite extension `M` of a nonarchimedean local field `K`
extending that of `K`, `x ≤ᵥ y` holds exactly when the spectral norm of `x` is at most that of
`y`. -/
theorem vle_iff_finiteExtensionNormedField_norm_le [ValuativeRel M] [ValuativeExtension K M]
    (x y : M) :
    letI := finiteExtensionNormedField K M
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [(valuation M).vle_iff_le, finiteExtensionNormedField_norm_le_norm_iff
    (ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K))]

variable (K M) in
/-- **Uniqueness of the extended valuative relation.** A valuative relation on a finite extension
`M` of a nonarchimedean local field `K` which extends that of `K` is the relation
`finiteExtensionValuativeRel K M` of the spectral norm. -/
theorem finiteExtensionValuativeRel_eq [ValuativeRel M] [ValuativeExtension K M] :
    finiteExtensionValuativeRel K M = ‹ValuativeRel M› := by
  ext x y
  exact finiteExtensionValuativeRel_vle_iff x y |>.trans
    (vle_iff_finiteExtensionNormedField_norm_le K x y).symm

variable (K M) in
/-- The topology `finiteExtensionNormedFieldTopology K M` of the spectral norm is the topology of
any valuative topological structure on `M` whose valuative relation extends that of `K`. -/
theorem finiteExtensionNormedFieldTopology_eq [ValuativeRel M] [ValuativeExtension K M]
    [TopologicalSpace M] [IsValuativeTopology M] :
    finiteExtensionNormedFieldTopology K M = ‹TopologicalSpace M› := by
  have h := finiteExtension_isValuativeTopology K M
  rw [finiteExtensionValuativeRel_eq K M] at h
  -- Both topologies are valuative for the same relation, so they have the same neighbourhoods.
  refine TopologicalSpace.ext_nhds fun x => Filter.ext fun s => ?_
  rw [@IsValuativeTopology.mem_nhds_iff _ _ _ (finiteExtensionNormedFieldTopology K M) h,
    IsValuativeTopology.mem_nhds_iff]

/-- **Galois invariance of the valuation.** Every `K`-algebra automorphism of a finite extension
`M` of a nonarchimedean local field `K` preserves the canonical valuation of any valuative relation
on `M` extending that of `K`. -/
@[simp]
theorem _root_.AlgEquiv.valuation_eq [ValuativeRel M] [ValuativeExtension K M] (σ : M ≃ₐ[K] M)
    (x : M) : valuation M (σ x) = valuation M x := by
  let _ := finiteExtensionNormedField K M
  let _ := normalizedNontriviallyNormedField K
  have hw := ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K)
  -- The spectral norm is invariant under `K`-algebra automorphisms.
  have h : ‖σ x‖ = ‖x‖ := (spectralNorm_eq_of_equiv σ x).symm
  exact le_antisymm ((finiteExtensionNormedField_norm_le_norm_iff hw _ _).1 h.le)
    ((finiteExtensionNormedField_norm_le_norm_iff hw _ _).1 h.ge)

/-- A `K`-automorphism of a finite local-field extension preserves its normalized valuation. -/
@[simp]
theorem normalizedValuation_algEquiv [ValuativeRel M] [ValuativeExtension K M]
    [TopologicalSpace M] [IsNonarchimedeanLocalField M] (σ : M ≃ₐ[K] M) (x : Mˣ) :
    normalizedValuation M (Units.map σ x) = normalizedValuation M x := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_normalizedValuation_eq_neg_log, Units.coe_map]
  -- The log expressions are definitionally the normalized values of the two field elements.
  change -((valueGroupWithZeroIsoInt M) (valuation M (σ (x : M)))).log =
    -((valueGroupWithZeroIsoInt M) (valuation M (x : M))).log
  rw [σ.valuation_eq]

end Uniqueness

/-! ### The ring of integers is the integral closure -/

section IntegralClosure

variable {K M} [ValuativeRel M] [ValuativeExtension K M]

/-- **The integers of a finite extension are the integral elements.** Let `M` be a finite
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
    let _ := finiteExtensionNormedField K M
    have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
    have hlifts : minpoly K x ∈ Polynomial.lifts (algebraMap O K) :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun n => hO.exists_of_le_one
        (coeff_minpoly_mem_integer_of_finiteExtensionNormedField_norm_le_one
          ((finiteExtensionNormedField_norm_le_one_iff hw x).2 hx) n)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmon
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq, minpoly.aeval]

variable (K M) in
/-- The ring of integers `𝒪[M]` of a finite extension `M` of a nonarchimedean local field `K`,
for a valuative relation extending that of `K`, is the integral closure of `𝒪[K]` in `M`. -/
theorem integerRing_eq_integralClosure :
    𝒪[M] = (integralClosure 𝒪[K] M).toSubring := by
  ext x
  rw [Subalgebra.mem_toSubring, mem_integralClosure_iff,
    Valuation.Integers.isIntegral_iff_valuation_le_one
      (Valuation.integer.integers (valuation K)),
    Valuation.mem_integer_iff]

end IntegralClosure

end TauCeti
