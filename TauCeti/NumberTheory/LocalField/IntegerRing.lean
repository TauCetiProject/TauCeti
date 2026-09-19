/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Localization.Finiteness
public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.RingTheory.AdicCompletion.Pi
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# The ring of integers of an extension of local fields is a finite free module

Let `L/K` be an extension of nonarchimedean local fields whose valuations are compatible, in the
sense of `ValuativeExtension K L`. This file proves that `𝒪[L]` is a finite `𝒪[K]`-module. Since
`𝒪[K]` is a discrete valuation ring, hence a principal ideal domain, and `𝒪[L]` is torsion-free,
`𝒪[L]` is then a free `𝒪[K]`-module; that instance is Mathlib's
`Module.free_of_finite_type_torsion_free'` and needs no separate statement. Its rank is `[L : K]`,
and in particular `L/K` is finite: no finiteness of `L/K` is assumed anywhere below.

The proof of finiteness is the complete Nakayama lemma (Mathlib's
`surjective_of_mkQ_comp_surjective`). The quotient `𝒪[L] / 𝓂[K] 𝒪[L]` is finite, because
`𝓂[K] 𝒪[L]` is a nonzero ideal of the discrete valuation ring `𝒪[L]`, hence a power of `𝓂[L]`,
and the residue field of `L` is finite. `𝒪[L]` is `𝓂[K]`-adically separated, because
`𝓂[K] 𝒪[L] ≤ 𝓂[L]` and `𝒪[L]` is a noetherian local ring, while `𝒪[K]`, and hence every finite
product of copies of it, is `𝓂[K]`-adically complete. Hence lifts of generators of the quotient
generate `𝒪[L]`.

The rank is computed by localization: every element of `L` becomes integral after multiplication
by a power of a uniformizer of `K`, so `L` is the localization of `𝒪[L]` at the nonzero elements
of `𝒪[K]`.

## Main results

* `TauCeti.integerRingModuleFinite`: `𝒪[L]` is a finite `𝒪[K]`-module.
* `TauCeti.isLocalization_integerRing`: `L` is the localization of `𝒪[L]` at the image of the
  nonzero elements of `𝒪[K]`.
* `TauCeti.finrank_integerRing`: the rank of `𝒪[L]` over `𝒪[K]` is `[L : K]`.
* `TauCeti.finite_of_valuativeExtension`: `L` is a finite extension of `K`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §4, Proposition 10, and Chapter II, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- The reduction `𝒪[L] / 𝓂[K] 𝒪[L]` is finite: `𝓂[K] 𝒪[L]` is a nonzero ideal of the discrete
valuation ring `𝒪[L]`, so it contains a power of `𝓂[L]`, and the residue field of `L` is finite. -/
theorem finite_quotient_maximalIdeal_smul_integerRing :
    Finite (𝒪[L] ⧸ (𝓂[K] • ⊤ : Submodule 𝒪[K] 𝒪[L])) := by
  set J := 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L])
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hJ : J ≠ ⊥ := by
    intro h
    have hπJ : algebraMap 𝒪[K] 𝒪[L] π ∈ J := Ideal.mem_map_of_mem _ <|
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ ▸
        Ideal.mem_span_singleton_self π
    rw [h, Ideal.mem_bot] at hπJ
    exact hπ.ne_zero (FaithfulSMul.algebraMap_injective 𝒪[K] 𝒪[L] (by simpa using hπJ))
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ hϖ
  have : Finite (𝒪[L] ⧸ J) := by
    rw [IsLocalRing.finite_quotient_iff]
    refine ⟨n, ?_⟩
    rw [hn, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.span_singleton_pow]
  rw [Ideal.smul_top_eq_map]
  exact .of_equiv _ (Submodule.Quotient.restrictScalarsEquiv 𝒪[K] J).toEquiv.symm

/-- The ring of integers of an extension of nonarchimedean local fields is a finite module over
the ring of integers of the base. -/
instance integerRingModuleFinite : Module.Finite 𝒪[K] 𝒪[L] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  -- `𝒪[L]` is `𝓂[K]`-adically separated since `𝓂[K] 𝒪[L] ≤ 𝓂[L]` (Krull intersection theorem).
  have : IsHausdorff 𝓂[K] 𝒪[L] := .of_map (map_maximalIdeal_le (algebraMap 𝒪[K] 𝒪[L]))
  have := finite_quotient_maximalIdeal_smul_integerRing K L
  obtain ⟨n, f, hf⟩ :=
    Module.Finite.exists_fin' 𝒪[K] (𝒪[L] ⧸ (𝓂[K] • ⊤ : Submodule 𝒪[K] 𝒪[L]))
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property (Submodule.mkQ _) f (Submodule.mkQ_surjective _)
  exact .of_surjective g (surjective_of_mkQ_comp_surjective (I := 𝓂[K]) (hg ▸ hf))

/-- Every element of `L` is carried into `𝒪[L]` by a nonzero element of `𝒪[K]`: a large enough
power of a uniformizer of `K` will do. -/
theorem exists_algebraMap_mul_mem_integerRing (x : L) :
    ∃ a : 𝒪[K], a ≠ 0 ∧ algebraMap K L a * x ∈ 𝒪[L] := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨1, one_ne_zero, by simp⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set πu : Kˣ := Units.mk0 (π : K) fun h ↦ hπ.ne_zero (Subtype.ext h)
  set n := (normalizedValuation L (Units.mk0 x hx)).toAdd.natAbs
  refine ⟨π ^ n, pow_ne_zero _ hπ.ne_zero, ?_⟩
  have hunit : ((Units.map (algebraMap K L : K →* L) (πu ^ n) * Units.mk0 x hx : Lˣ) : L) =
      algebraMap K L (π ^ n : 𝒪[K]) * x := by
    simp [πu]
  rw [← hunit, mem_integer_iff_toAdd_normalizedValuation_nonneg, map_mul, toAdd_mul,
    toAdd_normalizedValuation_algebraMap, map_pow, toAdd_pow,
    normalizedValuation_irreducible hπ, toAdd_ofAdd, nsmul_eq_mul, mul_one]
  have he : (1 : ℤ) ≤ ramificationIndex K L := by exact_mod_cast ramificationIndex_pos
  have hn : (0 : ℤ) ≤ n + (normalizedValuation L (Units.mk0 x hx)).toAdd := by omega
  nlinarith

/-- `L` is the localization of `𝒪[L]` at the image of the nonzero elements of `𝒪[K]`. -/
theorem isLocalization_integerRing :
    IsLocalization (Algebra.algebraMapSubmonoid 𝒪[L] (nonZeroDivisors 𝒪[K])) L where
  map_units := by
    rintro ⟨_, a, ha, rfl⟩
    refine IsUnit.mk0 _ ?_
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply 𝒪[K] K L]
    simpa using nonZeroDivisors.ne_zero ha
  surj x := by
    obtain ⟨a, ha, hax⟩ := exists_algebraMap_mul_mem_integerRing K L x
    refine ⟨⟨⟨_, hax⟩, ⟨_, a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩⟩, ?_⟩
    -- `algebraMap 𝒪[L] L` is the subring coercion; `change` exposes it so that
    -- `coe_algebraMap_integerRing` applies.
    change x * ((algebraMap 𝒪[K] 𝒪[L] a : 𝒪[L]) : L) = algebraMap K L a * x
    rw [coe_algebraMap_integerRing, mul_comm]
  exists_of_eq {x y} h := ⟨1, by simpa using Subtype.ext h⟩

/-- The rank of `𝒪[L]` as a free `𝒪[K]`-module is the degree `[L : K]`. -/
theorem finrank_integerRing : Module.finrank 𝒪[K] 𝒪[L] = Module.finrank K L := by
  have := isLocalization_integerRing K L
  have : IsLocalizedModule (nonZeroDivisors 𝒪[K])
      (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap :=
    (isLocalizedModule_iff_isLocalization ..).2 this
  exact (Module.finrank_of_isLocalizedModule_of_free K (nonZeroDivisors 𝒪[K])
    (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L).toLinearMap).symm

/-- An extension of nonarchimedean local fields with compatible valuations is finite. -/
theorem finite_of_valuativeExtension : Module.Finite K L :=
  have := isLocalization_integerRing K L
  .of_isLocalization 𝒪[K] 𝒪[L] (nonZeroDivisors 𝒪[K])

end TauCeti
