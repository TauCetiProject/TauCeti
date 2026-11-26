/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Semilocal

/-!
# Decomposition groups inside the image of a local absolute Galois group

Let `K ⊆ F ⊆ E` be number fields, let `ι : E →ₐ[K] Kˢ` embed `E` in the
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
(`IsDedekindDomain.HeightOneSpectrum.decompositionHom`), which in turn extends to an automorphism
of `K_vˢ` over `F_u`, since `K_vˢ/F_u` is normal (no normality of `E/F` is needed); that
automorphism is in particular an element `g` of `G_{K_v}`, and `absoluteGaloisGroupMap τ g` acts
as `σ` on `ι(E)`.

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
* `IntermediateField.absoluteGaloisGroupMap_mem_fixingSubgroup_of_notMem_ramifiedSupport`:
  away from a finite subextension's ramified support, local inertia fixes that subextension
  along every embedding of separable closures.
* `AlgHom.mem_fixingSubgroup_fieldRange_of_forall_apply_algebraMap`: an automorphism over `K_v`
  fixing the image of a number field `L` under `τ' : L_w →ₐ[K_v] Ω` fixes all of `τ'.fieldRange`.

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
number fields, `ι : E →ₐ[K] Kˢ` an embedding into the separable closure of `K`,
and `w` a finite place of `E` above a finite place `u` of `F` above the finite place `v` of `K`. For
some embedding of separable closures `τ : Kˢ →ₐ[K] K_vˢ`, every element `σ` of the decomposition
group of `w` in `Gal(E/F)` satisfies `absoluteGaloisGroupMap τ g (ι x) = ι (σ x)` for some
`g ∈ G_{K_v}` and every `x ∈ E`. -/
theorem exists_absoluteGaloisGroupMap_apply_eq_of_mem_stabilizer
    (ι : E →ₐ[K] SeparableClosure K) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 F)} [hu : u.asIdeal.LiesOver v.asIdeal]
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver u.asIdeal] :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      ∀ σ ∈ MulAction.stabilizer Gal(E/F) w.asIdeal,
        ∃ g : AbsoluteGaloisGroup (v.adicCompletion K),
          ∀ x, absoluteGaloisGroupMap τ g (ι x) = ι (σ x) := by
  have := HeightOneSpectrum.isSeparable_adicCompletion_of_isSeparable (K := K) (L := F) v u
  have := HeightOneSpectrum.isSeparable_adicCompletion_of_isSeparable (K := F) (L := E) u w
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
  -- The automorphism of `E_w` induced by `σ` extends along `τ'` to an automorphism `g₀` of the
  -- normal extension `K_vˢ` of `F_u`, in particular over `K_v`.
  let _ : Algebra (w.adicCompletion E) (SeparableClosure (v.adicCompletion K)) :=
    τ'.toRingHom.toAlgebra
  have : IsScalarTower (u.adicCompletion F) (w.adicCompletion E)
      (SeparableClosure (v.adicCompletion K)) := .of_algebraMap_eq fun x ↦ (τ'.commutes x).symm
  let g₀ : SeparableClosure (v.adicCompletion K) ≃ₐ[u.adicCompletion F]
      SeparableClosure (v.adicCompletion K) :=
    (HeightOneSpectrum.decompositionHom u w ⟨σ, hσ⟩).liftNormal _
  refine ⟨g₀.restrictScalars (v.adicCompletion K), fun x ↦ ?_⟩
  have h : τ (absoluteGaloisGroupMap τ (g₀.restrictScalars (v.adicCompletion K)) (ι x)) =
      τ (ι (σ x)) := by
    rw [absoluteGaloisGroupMap_commutes, hτι, hτι, AlgEquiv.restrictScalars_apply]
    exact (AlgEquiv.liftNormal_commutes _ _ _).trans
      (congrArg τ' (HeightOneSpectrum.decompositionHom_algebraMap (v := u) ⟨σ, hσ⟩ x))
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

/-- If `g : Ω ≃ₐ[K_v] Ω` fixes the image of the number field `L` under `τ' : L_w →ₐ[K_v] Ω`,
then `g` lies in the fixing subgroup of `τ'.fieldRange`. -/
theorem mem_fixingSubgroup_fieldRange_of_forall_apply_algebraMap {K L Ω : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] {v : HeightOneSpectrum (𝓞 K)}
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [Field Ω]
    [Algebra (v.adicCompletion K) Ω] (τ' : w.adicCompletion L →ₐ[v.adicCompletion K] Ω)
    {g : Ω ≃ₐ[v.adicCompletion K] Ω}
    (hfixL : ∀ a : L, g (τ' (algebraMap L (w.adicCompletion L) a)) =
      τ' (algebraMap L (w.adicCompletion L) a)) :
    g ∈ τ'.fieldRange.fixingSubgroup := by
  classical
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro _ ⟨y, rfl⟩
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  let eSemi := v.adicCompletionSemilocalEquiv K (𝓞 L) L
  let z : TensorProduct K (v.adicCompletion K) L := eSemi.symm (Pi.single ⟨w, ‹_›⟩ y)
  have hz : eSemi z ⟨w, ‹_›⟩ = y := by simp [z]
  rw [← hz]
  refine TensorProduct.inductionOn z (fun c a ↦ ?_) (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂])
  have htmul : eSemi (TensorProduct.tmul K c a) ⟨w, ‹_›⟩ =
      algebraMap (v.adicCompletion K) (w.adicCompletion L) c *
        algebraMap L (w.adicCompletion L) a := by simp [eSemi]
  rw [htmul]
  simp only [map_mul, AlgHom.commutes, AlgEquiv.commutes, hfixL]

end AlgHom

namespace IntermediateField

open TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- Away from the ramified support of a finite subextension of `Kˢ/K`, every local inertia
element fixes that subextension, for any embedding of separable closures. -/
theorem absoluteGaloisGroupMap_mem_fixingSubgroup_of_notMem_ramifiedSupport
    (E : IntermediateField K (SeparableClosure K)) [NumberField E]
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ NumberField.ramifiedSupport K E)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    {g : AbsoluteGaloisGroup (v.adicCompletion K)}
    (hg : g ∈ separableClosureInertiaSubgroup (v.adicCompletion K)) :
    absoluteGaloisGroupMap τ g ∈ E.fixingSubgroup := by
  obtain ⟨w, hw, τ', hτ⟩ := exists_algHom_adicCompletion_eq E v
    (τ.comp (IsScalarTower.toAlgHom K E (SeparableClosure K)))
  -- Register the instance that `w` lies over `v` for the unramifiedness results below.
  have hLiesOver : w.asIdeal.LiesOver v.asIdeal := hw
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    NumberField.isUnramifiedAway_ramifiedSupport v hv w.asIdeal
  have : IsUnramified (v.adicCompletion K) (w.adicCompletion E) :=
    HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt v w
  have hrange : τ'.fieldRange ≤
      maximalUnramifiedExtension (v.adicCompletion K)
        (SeparableClosure (v.adicCompletion K)) := by
    rw [τ'.fieldRange_eq_unramifiedExtension]
    exact unramifiedExtension_le_maximalUnramifiedExtension _ _ _
  have hg' : g ∈ τ'.fieldRange.fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone hrange
      ((separableClosureInertiaSubgroup_eq_fixingSubgroup _).le hg)
  have hle := E.fixingSubgroup_le_comap_absoluteGaloisGroupMap τ'.fieldRange τ
    (fun x hx ↦ ⟨algebraMap E (w.adicCompletion E) ⟨x, hx⟩, (hτ ⟨x, hx⟩).symm⟩)
  exact hle hg'

end IntermediateField
