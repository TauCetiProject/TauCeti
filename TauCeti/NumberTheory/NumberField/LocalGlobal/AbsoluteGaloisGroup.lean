/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import TauCeti.NumberTheory.NumberField.LocalGlobal.Separable

/-!
# Decomposition groups inside the image of a local absolute Galois group

Let `K ⊆ F ⊆ E` be number fields with `E/F` Galois, let `ι : E →ₐ[K] Kˢ` embed `E` in the
separable closure `Kˢ` of `K`, and let `w` be a finite place of `E` above a place of `F` above the
finite place `v` of `K`. An embedding of separable closures `τ : Kˢ →ₐ[K] K_vˢ` gives the map
`TauCeti.absoluteGaloisGroupMap τ : G_{K_v} → G_K`. This file shows that for a suitable `τ` every
element `σ` of the decomposition group of `w` in `Gal(E/F)` is read off along `ι` from the image of
some `g ∈ G_{K_v}`: `absoluteGaloisGroupMap τ g (ι x) = ι (σ x)` for every `x ∈ E`
(`AlgHom.exists_absoluteGaloisGroupMap_apply_eq_of_mem_stabilizer`). Such an image fixes `ι(F)`
pointwise, so it lies in the subgroup of `G_K` cut out by `F`.

Let `u` be the place of `F` below `w`. The embedding `τ` is chosen so that its restriction to `E`
factors through the completion `E_w`: embed `F_u` in `K_vˢ` over `K_v`, which makes `K_vˢ` a
separable closure of `F_u`, embed `E_w` in it over `F_u`, and extend `E → E_w → K_vˢ` to `Kˢ`.
An element `σ` of the decomposition group extends by continuity to an automorphism of `E_w/F_u`
(`IsDedekindDomain.HeightOneSpectrum.decompositionHom`), which in turn is the restriction of an
automorphism of `K_vˢ` over `F_u`, since `K_vˢ/F_u` is normal; that automorphism is in particular an
element `g` of `G_{K_v}`, and `absoluteGaloisGroupMap τ g` acts as `σ` on `ι(E)`.

For `F = K` this says that the decomposition group of `w` in `Gal(E/K)` lies in the image of
`G_{K_v}` (`AlgHom.exists_stabilizer_le_range_restrictNormalHom_comp_absoluteGaloisGroupMap`). So a
place whose decomposition group is the whole Galois group yields an embedding `τ` along which
`G_{K_v}` maps onto it. This is how the existence of a place of full local degree, a statement
about prime ideals, becomes a statement about the decomposition maps `G_{K_v} → G_K` used by
Galois cohomology.

## Main results

* `AlgHom.exists_absoluteGaloisGroupMap_apply_eq_of_mem_stabilizer`: for some embedding
  `τ : Kˢ →ₐ[K] K_vˢ`, every element of the decomposition group of `w` in `Gal(E/F)` agrees on
  `ι(E)` with the image of an element of `G_{K_v}`.
* `AlgHom.exists_stabilizer_le_range_restrictNormalHom_comp_absoluteGaloisGroupMap`: the case
  `F = K`, for some embedding `τ : Kˢ →ₐ[K] K_vˢ`, every element of the decomposition group of `w`
  is the restriction to `E` of the image of an element of `G_{K_v}`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9 (decomposition groups and completions).
-/

public section

noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension Pointwise

namespace AlgHom

open TauCeti

variable {K F E : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]

/-- **The decomposition group acts through the local absolute Galois group.** Let `K ⊆ F ⊆ E` be
number fields with `E/F` Galois, `ι : E →ₐ[K] Kˢ` an embedding into the separable closure of `K`,
and `w` a finite place of `E` above a finite place `u` of `F` above the finite place `v` of `K`. For
some embedding of separable closures `τ : Kˢ →ₐ[K] K_vˢ`, every element `σ` of the decomposition
group of `w` in `Gal(E/F)` satisfies `absoluteGaloisGroupMap τ g (ι x) = ι (σ x)` for some
`g ∈ G_{K_v}` and every `x ∈ E`. -/
theorem exists_absoluteGaloisGroupMap_apply_eq_of_mem_stabilizer [IsGalois F E]
    (ι : E →ₐ[K] SeparableClosure K) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 F)} [hu : u.asIdeal.LiesOver v.asIdeal]
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver u.asIdeal] :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      ∀ σ ∈ MulAction.stabilizer Gal(E/F) w.asIdeal,
        ∃ g : AbsoluteGaloisGroup (v.adicCompletion K),
          ∀ x, absoluteGaloisGroupMap τ g (ι x) = ι (σ x) := by
  have := HeightOneSpectrum.adicCompletion_isSeparable v u
  have := HeightOneSpectrum.adicCompletion_isSeparable u w
  -- Embed `F_u` in `K_vˢ` over `K_v`, making `K_vˢ` a separable closure of `F_u`, and then embed
  -- `E_w` in it over `F_u`.
  let κ : u.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  let _ : Algebra (u.adicCompletion F) (SeparableClosure (v.adicCompletion K)) :=
    κ.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K) (u.adicCompletion F)
      (SeparableClosure (v.adicCompletion K)) := .of_algebraMap_eq fun x ↦ (κ.commutes x).symm
  have : Algebra.IsSeparable (u.adicCompletion F) (SeparableClosure (v.adicCompletion K)) :=
    Algebra.isSeparable_tower_top_of_isSeparable (v.adicCompletion K) _ _
  have : IsSepClosure (u.adicCompletion F) (SeparableClosure (v.adicCompletion K)) :=
    ⟨inferInstance, inferInstance⟩
  let τ' : w.adicCompletion E →ₐ[u.adicCompletion F] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  -- The embedding `j : E → E_w → K_vˢ` is `K`-linear, because both squares of completions commute.
  have hFE (x : F) : algebraMap E (w.adicCompletion E) (algebraMap F E x) =
      algebraMap (u.adicCompletion F) (w.adicCompletion E)
        (algebraMap F (u.adicCompletion F) x) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
    exact (HeightOneSpectrum.adicCompletionExtension_coe F E u w x).symm
  have hKF (x : K) : algebraMap F (u.adicCompletion F) (algebraMap K F x) =
      algebraMap (v.adicCompletion K) (u.adicCompletion F)
        (algebraMap K (v.adicCompletion K) x) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
    exact (HeightOneSpectrum.adicCompletionExtension_coe K F v u x).symm
  have hcomm (x : K) : τ' (algebraMap E (w.adicCompletion E) (algebraMap K E x)) =
      algebraMap K (SeparableClosure (v.adicCompletion K)) x := by
    rw [IsScalarTower.algebraMap_apply K F E, hFE, hKF, τ'.commutes,
      IsScalarTower.algebraMap_apply K (v.adicCompletion K) (SeparableClosure _)]
    exact κ.commutes _
  let j : E →ₐ[K] SeparableClosure (v.adicCompletion K) :=
    { τ'.toRingHom.comp (algebraMap E (w.adicCompletion E)) with commutes' := hcomm }
  -- Extend `j`, read on the image of `ι`, to `τ : Kˢ →ₐ[K] K_vˢ`.
  obtain ⟨τ, hτ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι.fieldRange
    (E := SeparableClosure K) (M := SeparableClosure (v.adicCompletion K))
    (j.comp (ι.equivFieldRange.symm : ι.fieldRange →ₐ[K] E))
  -- `τ.domRestrict` evaluates on `ι.equivFieldRange x` as `τ` on `ι x`, by definition.
  have hτι (x : E) : τ (ι x) = τ' (algebraMap E (w.adicCompletion E) x) :=
    (congrArg (fun φ : ι.fieldRange →ₐ[K] _ ↦ φ (ι.equivFieldRange x)) hτ).trans
      (congrArg j (ι.equivFieldRange.symm_apply_apply x))
  refine ⟨τ, fun σ hσ ↦ ?_⟩
  -- The automorphism of `E_w` induced by `σ` is the restriction along `τ'` of an automorphism `g₀`
  -- of `K_vˢ` over `F_u`, in particular over `K_v`.
  obtain ⟨g₀, hg₀⟩ :=
    τ'.restrictNormalHom_surjective (HeightOneSpectrum.decompositionHom u w ⟨σ, hσ⟩)
  refine ⟨g₀.restrictScalars (v.adicCompletion K), fun x ↦ ?_⟩
  have h : τ (absoluteGaloisGroupMap τ (g₀.restrictScalars (v.adicCompletion K)) (ι x)) =
      τ (ι (σ x)) := by
    rw [absoluteGaloisGroupMap_commutes, hτι, hτι, AlgEquiv.restrictScalars_apply,
      ← τ'.restrictNormalHom_commutes, hg₀, HeightOneSpectrum.decompositionHom_algebraMap]
  exact τ.injective h

/-- **The decomposition group lies in the image of the local absolute Galois group.** Let `E/K`
be a Galois extension of number fields, `ι : E →ₐ[K] Kˢ` an embedding into the separable closure
of `K`, and `w` a finite place of `E` above the finite place `v` of `K`. For some embedding of
separable closures `τ : Kˢ →ₐ[K] K_vˢ`, every element of the decomposition group of `w` is the
restriction along `ι` of `absoluteGaloisGroupMap τ g` for some `g ∈ G_{K_v}`. -/
theorem exists_stabilizer_le_range_restrictNormalHom_comp_absoluteGaloisGroupMap [IsGalois K E]
    (ι : E →ₐ[K] SeparableClosure K) {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      MulAction.stabilizer (E ≃ₐ[K] E) w.asIdeal ≤ (ι.restrictNormalHom.comp
        (absoluteGaloisGroupMap τ :
          AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K)).range := by
  obtain ⟨τ, hτ⟩ := exists_absoluteGaloisGroupMap_apply_eq_of_mem_stabilizer (F := K) ι (u := v) w
    (hu := ⟨(Ideal.comap_id v.asIdeal).symm⟩)
  exact ⟨τ, fun σ hσ ↦ (hτ σ hσ).imp fun g hg ↦ ι.restrictNormalHom_eq_iff.2 hg⟩

end AlgHom
