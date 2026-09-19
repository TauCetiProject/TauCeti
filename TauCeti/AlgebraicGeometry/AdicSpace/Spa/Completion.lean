/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import Mathlib.Topology.Algebra.UniformRing
import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Continuous valuations extend to the completion

Let `A` be a topological ring with a compatible uniform structure, and let `ι : A → Â` be its
Hausdorff completion. Every continuous point of `Spv A` is the pullback along `ι` of a continuous
point of `Spv Â`, and consequently pullback along `ι` maps `Spa (Â, Â⁺)` onto `Spa (A, A⁺)`, where
`Â⁺` is the closure of `ι(A⁺)`.

This is the surjectivity half of Wedhorn's Proposition 7.48, for an arbitrary subring `A⁺` of an
arbitrary topological ring `A` with a compatible uniform structure: no Huber, Hausdorff or
completeness hypothesis is needed, and `A⁺` need not be a ring of integral elements. For an
affinoid ring, `closure (ι A⁺)` is Wedhorn's `Â⁺` (Lemma 7.47). This is a step towards §3.1 of
`TauCetiRoadmap/AdicSpaces/README.md`, which asks for the adic spectrum of a completed rational
localisation to be identified with the rational subset it comes from.

## Main results

* `TauCeti.ValuationSpectrum.exists_isContinuous_comap_coeRingHom_eq` : a continuous point of
  `Spv A` is the pullback of a continuous point of `Spv Â`.
* `TauCeti.ValuationSpectrum.spaComap_coeRingHom_surjective` : pullback along `A → Â` maps
  `Spa (Â, closure (ι A⁺))` onto `Spa (A, A⁺)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.47 and
  Proposition 7.48.
* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 445–477, Proposition 3.9, which Wedhorn
  cites for Proposition 7.48.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch `dev/adic-spaces` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, file
`projects/AdicSpaces/Adic spaces/SpaRationalOpenComparison.lean`, was consulted: its `scResHom`,
`scResHom_val`, `scResHom_continuous`, `comap_coeRingHom_extensionHom_ofValuation_eq` and
`spa_completion_of_spa_localization` extend a point along the completion of a rational
localisation through the completed residue field. Nothing was copied. Here the ring is an
arbitrary uniform topological ring rather than a rational localisation, continuity is the
attained-value predicate of `Valuation.IsContinuous`, and the plus ring of the completion is the
closure of the image of `A⁺`.
-/

public section

open Valuation

private theorem Valued.isContinuous_v {R : Type*} [Ring R] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀] : (Valued.v : Valuation R Γ₀).IsContinuous :=
  isContinuous_def.mpr fun b ↦ by simpa using Valued.isOpen_ball R (Valued.v.restrict b)

namespace TauCeti.ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A]

private theorem valued_algebraMap (v : Spv A) (a : A) :
    Valued.v (algebraMap A (WithVal (residueFieldValuation v)) a) = v.valuation a := by
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal]
  exact (residueFieldValuation_algebraMap v (Ideal.Quotient.mk _ a)).trans <|
    DFunLike.congr_fun (quotientValuation_comap_quotientMk v) a

private theorem continuous_algebraMap [TopologicalSpace A] [IsTopologicalRing A] {v : Spv A}
    (hv : v.IsContinuous) : Continuous (algebraMap A (WithVal (residueFieldValuation v))) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  -- the radius `γ` is a ratio `v b / v c` of values, so continuity makes `{a | v a < γ}` open
  obtain ⟨b, c, hc, hbc⟩ :=
    exists_valuation_div_valuation_eq v (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  filter_upwards [(((isContinuous_def v).mp hv).isOpen_lt_div b hc).mem_nhds
    (by simp [hbc, zero_lt_iff])] with a ha
  rwa [restrict_lt_iff_lt_embedding, valued_algebraMap, ← hbc]

variable [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- **Continuous valuations extend to the completion.** Every continuous point of `Spv A` is the
pullback along `A → Â` of a continuous point of `Spv Â`, where `Â` is the Hausdorff completion
`UniformSpace.Completion A`. -/
theorem exists_isContinuous_comap_coeRingHom_eq {v : Spv A} (hv : v.IsContinuous) :
    ∃ w : Spv (Completion A), w.IsContinuous ∧
      comap (Completion.coeRingHom : A →+* Completion A) w = v := by
  -- `A → κ(v)` is continuous, so it completes to `Â → κ(v)^`; the valuation of `κ(v)^` pulls back
  -- along it to a continuous point of `Spv Â` lying over `v`
  let F : Completion A →+* (residueFieldValuation v).Completion :=
    Completion.mapRingHom (algebraMap A _) (continuous_algebraMap hv)
  refine ⟨ofValuation (Valued.v.comap F), ?_, ?_⟩
  · rw [isContinuous_ofValuation_iff]
    exact Valued.isContinuous_v.comap Completion.continuous_map
  · rw [comap_ofValuation]
    convert ofValuation_valuation v using 2
    ext a
    simp [F, Completion.coeRingHom, Completion.mapRingHom_coe, valued_algebraMap,
      -Completion.mapRingHom_apply]

/-- **The surjectivity half of Wedhorn Proposition 7.48, for any subring `A⁺`.** Pullback along
`A → Â` maps `Spa (Â, Â⁺)` onto `Spa (A, A⁺)`, where `Â⁺` is the closure of the image of `A⁺`.
This is the adic-spectrum form of `exists_isContinuous_comap_coeRingHom_eq`. -/
theorem spaComap_coeRingHom_surjective (Aplus : Subring A) : Function.Surjective
    (spaComap (Completion.coeRingHom : A →+* Completion A) Completion.continuous_coeRingHom Aplus
      (Aplus.map Completion.coeRingHom).topologicalClosure
      fun a ha ↦ Subring.le_topologicalClosure _ ⟨a, ha, rfl⟩) := by
  rintro ⟨v, hv⟩
  obtain ⟨w, hw, rfl⟩ := exists_isContinuous_comap_coeRingHom_eq ((mem_spa_iff Aplus v).mp hv).1
  refine ⟨⟨w, ?_⟩, Subtype.ext (spaComap_val ..)⟩
  -- `spa` ignores the closure, and `w` lies over the image of `A⁺` as its pullback lies over `A⁺`
  rwa [spa_topologicalClosure, mem_spa_map_iff Completion.continuous_coeRingHom Aplus hw]

end TauCeti.ValuationSpectrum
