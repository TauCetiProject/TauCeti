/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup

/-!
# Decomposition groups inside the image of a local absolute Galois group

Let `L/K` be a Galois extension of number fields, embedded in the separable closure `Kˢ` of `K`
by `ι : L →ₐ[K] Kˢ`, and let `w` be a finite place of `L` above a finite place `v` of `K`. An
embedding of separable closures `τ : Kˢ →ₐ[K] K_vˢ` gives the map
`TauCeti.absoluteGaloisGroupMap τ : G_{K_v} → G_K`, and restricting along `ι` reads its image in
`Gal(L/K)`. This file shows that for a suitable `τ` that image contains the decomposition group
of `w`, the stabilizer of `w` in `Gal(L/K)`
(`AlgHom.exists_stabilizer_le_range_restrictNormalHom_comp_absoluteGaloisGroupMap`).

The embedding `τ` is chosen so that its restriction to `L` factors through the completion `L_w`:
it extends `L → L_w → K_vˢ`, for some `K_v`-embedding of `L_w` into `K_vˢ`. An element `σ` of the
decomposition group extends by continuity to an automorphism of `L_w/K_v`
(`IsDedekindDomain.HeightOneSpectrum.decompositionHom`), which in turn is the restriction of some
`g ∈ G_{K_v}`, since `K_vˢ/K_v` is normal. Then `absoluteGaloisGroupMap τ g` restricts to `σ`
on `L`.

So a place whose decomposition group is the whole of `Gal(L/K)` yields an embedding `τ` along
which `G_{K_v}` maps onto `Gal(L/K)`. This is how the existence of a place of full local degree,
a statement about prime ideals, becomes a statement about the decomposition maps
`G_{K_v} → G_K` used by Galois cohomology.

## Main results

* `AlgHom.exists_stabilizer_le_range_restrictNormalHom_comp_absoluteGaloisGroupMap`: for some
  embedding `τ : Kˢ →ₐ[K] K_vˢ`, every element of the decomposition group of `w` is the
  restriction to `L` of the image of an element of `G_{K_v}`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9 (decomposition groups and completions).
-/

public section

noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension Pointwise

namespace AlgHom

open TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The decomposition group lies in the image of the local absolute Galois group.** Let `L/K`
be a Galois extension of number fields, `ι : L →ₐ[K] Kˢ` an embedding into the separable closure
of `K`, and `w` a finite place of `L` above the finite place `v` of `K`. For some embedding of
separable closures `τ : Kˢ →ₐ[K] K_vˢ`, every element of the decomposition group of `w` is the
restriction along `ι` of `absoluteGaloisGroupMap τ g` for some `g ∈ G_{K_v}`. -/
theorem exists_stabilizer_le_range_restrictNormalHom_comp_absoluteGaloisGroupMap [IsGalois K L]
    (ι : L →ₐ[K] SeparableClosure K) {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal ≤ (ι.restrictNormalHom.comp
        (absoluteGaloisGroupMap τ :
          AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K)).range := by
  -- An embedding `κ` of `L_w` into `K_vˢ`, and the embedding `j` of `L` through `L_w` it induces.
  let κ : w.adicCompletion L →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  let j : L →ₐ[K] SeparableClosure (v.adicCompletion K) :=
    (κ.restrictScalars K).comp (IsScalarTower.toAlgHom K L (w.adicCompletion L))
  -- Extend `j`, read on the image of `ι`, to `τ : Kˢ →ₐ[K] K_vˢ`.
  obtain ⟨τ, hτ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι.fieldRange
    (E := SeparableClosure K) (M := SeparableClosure (v.adicCompletion K))
    (j.comp (ι.equivFieldRange.symm : ι.fieldRange →ₐ[K] L))
  -- `τ.domRestrict` evaluates on `ι.equivFieldRange x` as `τ` on `ι x`, by definition.
  have hτι (x : L) : τ (ι x) = j x :=
    (congrArg (fun φ : ι.fieldRange →ₐ[K] _ ↦ φ (ι.equivFieldRange x)) hτ).trans
      (congrArg j (ι.equivFieldRange.symm_apply_apply x))
  refine ⟨τ, fun σ hσ ↦ ?_⟩
  -- The automorphism of `L_w` induced by `σ` is the restriction along `κ` of some `g ∈ G_{K_v}`.
  obtain ⟨g, hg⟩ :=
    κ.restrictNormalHom_surjective (HeightOneSpectrum.decompositionHom v w ⟨σ, hσ⟩)
  refine ⟨g, ι.restrictNormalHom_eq_iff.2 fun x ↦ ?_⟩
  have h : τ (absoluteGaloisGroupMap τ g (ι x)) = τ (ι (σ x)) := by
    rw [absoluteGaloisGroupMap_commutes, hτι, hτι]
    simp only [j, AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom']
    rw [← κ.restrictNormalHom_commutes, hg, HeightOneSpectrum.decompositionHom_algebraMap]
  exact τ.injective h

end AlgHom
