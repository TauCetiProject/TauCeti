/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Valued
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import Mathlib.Topology.Algebra.UniformRing
import TauCeti.RingTheory.Valuation.Continuous.Valued

/-!
# Continuous valuations extend to the completion

Let `A` be a commutative topological ring with a compatible uniform structure, and let `ι : A → Â`
be its Hausdorff completion. Every continuous point of `Spv A` is the pullback along `ι` of a
continuous point of `Spv Â`, and consequently pullback along `ι` maps `Spa (Â, Â⁺)` onto
`Spa (A, A⁺)`, where `Â⁺` is the closure of `ι(A⁺)`.

This is the surjectivity half of Wedhorn's Proposition 7.48, for an arbitrary subring `A⁺` of an
arbitrary commutative topological ring `A` with a compatible uniform structure: no Huber,
Hausdorff or completeness hypothesis is needed, and `A⁺` need not be a ring of integral elements.
For an affinoid ring, `closure (ι A⁺)` is Wedhorn's `Â⁺` (Lemma 7.47). Together with the
corresponding statement for rational subsets, this surjectivity feeds the identification of the
adic spectrum of a completed rational localisation with the rational subset it comes from; that
identification is a homeomorphism only once the map is also shown to be inducing and injective,
the latter through the T0 separation of the adic spectrum.

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
arbitrary commutative uniform topological ring rather than a rational localisation, continuity is
the attained-value predicate of `Valuation.IsContinuous`, and the plus ring of the completion is
the closure of the image of `A⁺`.
-/

public section

namespace UniformSpace.Completion

-- `Completion.coeRingHom` bundles the coercion `α → Completion α` as a ring homomorphism, but
-- Mathlib records no lemma for it in applied form. This names that identification once, so the
-- proof below can rewrite with it rather than unfold the definition inside a `simp`.
private theorem coeRingHom_apply {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α]
    [IsUniformAddGroup α] (a : α) :
    (coeRingHom : α →+* Completion α) a = (a : Completion α) := rfl

end UniformSpace.Completion

namespace TauCeti.ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- **Continuous valuations extend to the completion.** Every continuous point of `Spv A` is the
pullback along `A → Â` of a continuous point of `Spv Â`, where `Â` is the Hausdorff completion
`UniformSpace.Completion A`. -/
theorem exists_isContinuous_comap_coeRingHom_eq {v : Spv A} (hv : v.IsContinuous) :
    ∃ w : Spv (Completion A), w.IsContinuous ∧
      comap (Completion.coeRingHom : A →+* Completion A) w = v := by
  -- `A → κ(v)` is continuous, so it completes to `Â → κ(v)^`; the valuation of `κ(v)^` pulls back
  -- along it to a continuous point of `Spv Â` lying over `v`
  let F : Completion A →+* (residueFieldValuation v).Completion :=
    Completion.mapRingHom (algebraMap A _) (continuous_algebraMap_residueFieldValuation hv)
  refine ⟨ofValuation (Valued.v.comap F), ?_, ?_⟩
  · rw [isContinuous_ofValuation_iff]
    exact Valued.isContinuous_v.comap Completion.continuous_map
  · rw [comap_ofValuation]
    convert ofValuation_valuation v using 2
    ext a
    -- `F` sends the image of `a` in `Â` to the image of `algebraMap A κ(v) a` in `κ(v)^`
    have hF : F (a : Completion A) =
        (algebraMap A (WithVal (residueFieldValuation v)) a :
          (residueFieldValuation v).Completion) := Completion.mapRingHom_coe _ a
    rw [Valuation.comap_apply, Valuation.comap_apply, Completion.coeRingHom_apply, hF,
      Valued.valuedCompletion_apply, valued_algebraMap_residueFieldValuation]

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
