/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.BaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of projective spectra

The projective spectrum of a graded algebra commutes with arbitrary extension of its coefficient
ring. The comparison identifies the scheme fiber product, including its structure sheaf,
rather than only its points. This permits projective constructions to be transported through
nonflat closed fibres as well as flat families.

The construction combines `Proj.map` for coefficient inclusion, the homogeneous chart
comparison `HomogeneousLocalization.Away.baseChangeEquiv`, and Mathlib's
`pullbackSpecIso` and local criterion `Scheme.isPullback_of_openCover`.

The base change need not be presented as the tensor product itself: a graded ring homomorphism
`f : 𝒜 →+*ᵍ ℬ` over `R → S` exhibiting `B` as the base change of `A` (`IsBaseChange S f`) also
gives a cartesian square of projective spectra (`Proj.isPullback_map_of_isBaseChange`). This is the
form in which affine-local `Proj` constructions, such as the charts of a relative `Proj`, are
compared over a localization of the base.

## Main results

* `AlgebraicGeometry.Proj.isPullback_baseChange`: `Proj` of `S ⊗[R] A` is the base change of
  `Proj A` along `Spec S ⟶ Spec R`.
* `AlgebraicGeometry.Proj.isPullback_map_of_isBaseChange`: the same for a graded ring homomorphism
  exhibiting `B` as the base change of `A`.

## References

* [Stacks Project, Lemma 27.11.6](https://stacks.math.columbia.edu/tag/01N2),
  base change of projective spectra via standard affine charts.
-/

public section

open CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open scoped TensorProduct
open TauCeti.GradedAlgebra

namespace AlgebraicGeometry.Proj

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The structural morphism to the spectrum of the coefficient ring of a graded algebra. -/
noncomputable def toSpecCoeff : Proj 𝒜 ⟶ Spec (.of R) :=
  toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

/-- The coefficient structure map factors through the degree-zero spectrum. -/
theorem toSpecCoeff_def :
    toSpecCoeff 𝒜 = toSpecZero 𝒜 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))) := (rfl)

/-- The coefficient morphism on a standard affine chart is the chart's coefficient map. -/
@[reassoc (attr := simp)]
theorem awayι_toSpecCoeff {f : A} {n : ℕ} (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    awayι 𝒜 f hf hn ≫ toSpecCoeff 𝒜 =
      Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 f))) := by
  rw [toSpecCoeff, awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← algebraMap_eq_comp]

/-- `Proj.map f` lies over the coefficient ring when `f` preserves the scalars in degree zero. -/
@[reassoc]
theorem map_toSpecCoeff {B : Type u} [CommRing B] [Algebra R B] {ℬ : ℕ → Submodule R B}
    [GradedAlgebra ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hR : ∀ r : R, f.gradedZeroRingHom (algebraMap R (𝒜 0) r) = algebraMap R (ℬ 0) r) :
    map f hf ≫ toSpecCoeff 𝒜 = toSpecCoeff ℬ := by
  rw [toSpecCoeff, map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, toSpecCoeff]
  congr 3
  exact RingHom.ext hR

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The projective projection induced by coefficient extension. Flatness is not needed to
construct this map. -/
noncomputable def baseChangeProjection :
    Proj (fun n ↦ (𝒜 n).baseChange S) ⟶ Proj 𝒜 :=
  map (baseChangeMap S 𝒜) (HomogeneousIdeal.irrelevant_le_map_baseChangeMap S 𝒜)

/-- The coefficient projection is the projective map of graded coefficient inclusion. -/
theorem baseChangeProjection_def :
    baseChangeProjection 𝒜 S = map (baseChangeMap S 𝒜)
      (HomogeneousIdeal.irrelevant_le_map_baseChangeMap S 𝒜) := (rfl)

/-- The preimage of a standard open is the standard open of the extended element. -/
@[simp]
theorem baseChangeProjection_preimage_basicOpen (f : A) :
    baseChangeProjection 𝒜 S ⁻¹ᵁ basicOpen 𝒜 f =
      basicOpen (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) := by
  simp [baseChangeProjection]

/-- On standard affine charts, the projective projection is coefficient extension of
homogeneous fractions. -/
@[reassoc (attr := simp)]
theorem awayι_baseChangeProjection {f : A} {n : ℕ} (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    awayι (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)
        (Submodule.tmul_mem_baseChange_of_mem 1 hf) hn ≫ baseChangeProjection 𝒜 S =
      Spec.map (CommRingCat.ofHom (Away.baseChangeMap 𝒜 S f)) ≫ awayι 𝒜 f hf hn := by
  rw [baseChangeProjection, Away.baseChangeMap_eq_map]
  -- The localization target depends on the value of the coefficient inclusion;
  -- `convert` reduces that explicit inclusion to its pure-tensor value.
  convert awayι_comp_map (baseChangeMap S 𝒜)
    (HomogeneousIdeal.irrelevant_le_map_baseChangeMap S 𝒜) hn f hf using 1
  all_goals rfl

/-- Coefficient extension gives a commutative square over the base spectra. -/
@[reassoc (attr := simp)]
theorem baseChangeProjection_toSpecCoeff :
    baseChangeProjection 𝒜 S ≫ toSpecCoeff 𝒜 =
      toSpecCoeff (fun n ↦ (𝒜 n).baseChange S) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [baseChangeProjection, toSpecCoeff, map_toSpecZero_assoc, toSpecCoeff]
  simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  simp [baseChangeMap, GradedRingHom.gradedZeroRingHom]

/-- The affine standard-chart square of coefficient extension is cartesian. -/
theorem isPullback_away_baseChange {f : A} {n : ℕ}
    (hf : f ∈ 𝒜 n) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.baseChangeMap 𝒜 S f)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 f))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let e := Away.baseChangeEquiv 𝒜 S f hf
  let iso := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R S (Away 𝒜 f)).symm ≪≫ pullbackSymmetry _ _
  refine IsPullback.of_iso_pullback ⟨?_⟩ iso ?_ ?_
  · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact Away.baseChangeMap_algebraMap 𝒜 S f r
  · simp only [iso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd]
    simp only [Functor.mapIso_hom, Iso.op_hom]
    -- `Spec.map` is Mathlib's abbreviation for the contravariant functor on a ring map.
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    simp [e, Away.baseChangeHom_tmul, Algebra.TensorProduct.includeRight_apply]
  · simp only [iso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']
    simp only [Functor.mapIso_hom, Iso.op_hom]
    -- Identify the ring-equivalence morphism with its underlying ring homomorphism.
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact e.commutes r

/-- Extension of coefficients makes the projective structural square cartesian. No
finite-generation hypothesis on the graded algebra is needed. -/
theorem isPullback_baseChange :
    IsPullback (baseChangeProjection 𝒜 S)
      (toSpecCoeff (fun n ↦ (𝒜 n).baseChange S))
      (toSpecCoeff 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (affineOpenCover 𝒜).openCover fun i ↦ ?_
  rcases i with ⟨n, f, hf⟩
  let j := awayι (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)
    (Submodule.tmul_mem_baseChange_of_mem 1 hf) n.pos
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hchart : IsPullback (Spec.map (CommRingCat.ofHom (Away.baseChangeMap 𝒜 S f)))
      j (awayι 𝒜 f hf n.pos) (baseChangeProjection 𝒜 S) :=
    IsOpenImmersion.isPullback _ _ _ _ (awayι_baseChangeProjection 𝒜 S hf n.pos)
      (by
        rw [opensRange_awayι]
        dsimp only [j]
        rw [opensRange_awayι]
        exact baseChangeProjection_preimage_basicOpen 𝒜 S f)
  let e := hchart.flip.isoPullback
  have h := (isPullback_away_baseChange 𝒜 S hf).of_iso e (.refl _) (.refl _) (.refl _)
    (fst' := pullback.snd (baseChangeProjection 𝒜 S) (awayι 𝒜 f hf n.pos))
    (snd' := pullback.fst (baseChangeProjection 𝒜 S) (awayι 𝒜 f hf n.pos) ≫
      toSpecCoeff (fun n ↦ (𝒜 n).baseChange S))
    (by simp [e])
    (f' := Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 f))))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (by simpa only [Category.comp_id, Iso.refl_hom, Category.assoc, e,
      IsPullback.isoPullback_hom_fst_assoc, j] using (awayι_toSpecCoeff
        (fun n ↦ (𝒜 n).baseChange S)
          (Submodule.tmul_mem_baseChange_of_mem 1 hf) n.pos).symm)
    (by simp) (by simp)
  -- The cover stores its pullback projections and chart morphisms through several
  -- structure fields. Normalize those fields before using the affine cartesian square.
  dsimp only [Scheme.Cover.pullbackHom, Precoverage.ZeroHypercover.pullback₁,
    PreZeroHypercover.pullback₁, Scheme.AffineOpenCover.openCover,
    Scheme.AffineCover.cover]
  convert h using 1
  all_goals first | rfl |
    (convert heq_of_eq (awayι_toSpecCoeff 𝒜 hf n.pos) using 1 <;> rfl)

/-- The canonical identification of the projective spectrum after arbitrary coefficient extension
with the fiber product over the original coefficient spectrum. -/
noncomputable def baseChangeIso :
    Proj (fun n ↦ (𝒜 n).baseChange S) ≅
      pullback (toSpecCoeff 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (isPullback_baseChange 𝒜 S).isoPullback

/-- The first projection of the comparison is the projective coefficient projection. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst :
    (baseChangeIso 𝒜 S).hom ≫ pullback.fst _ _ = baseChangeProjection 𝒜 S :=
  (isPullback_baseChange 𝒜 S).isoPullback_hom_fst

/-- The second projection of the comparison is the extended coefficient structure map. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd :
    (baseChangeIso 𝒜 S).hom ≫ pullback.snd _ _ =
      toSpecCoeff (fun n ↦ (𝒜 n).baseChange S) :=
  (isPullback_baseChange 𝒜 S).isoPullback_hom_snd

section IsBaseChange

variable {S} {B : Type u} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ] (f : 𝒜 →+*ᵍ ℬ)
  (hfR : ∀ r : R, f (algebraMap R A r) = algebraMap R B r)
  (hf : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap)

/-- **`Proj` commutes with base change.** If a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` over the
coefficient extension `R → S` exhibits `B` as the base change `S ⊗[R] A`, then the square

`Proj ℬ ⟶ Proj 𝒜`, `Spec S ⟶ Spec R`

formed by `Proj.map f` and the coefficient projections is cartesian. This is
`Proj.isPullback_baseChange` for an arbitrary presentation of the base change. -/
theorem isPullback_map_of_isBaseChange :
    IsPullback (map f (HomogeneousIdeal.irrelevant_le_map_of_isBaseChange 𝒜 f hfR hf))
      (toSpecCoeff ℬ) (toSpecCoeff 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have hfg := baseChangeLift_baseChangeLiftInv 𝒜 f hfR hf
  have hgf := baseChangeLiftInv_baseChangeLift 𝒜 f hfR hf
  have hmap : map f (HomogeneousIdeal.irrelevant_le_map_of_isBaseChange 𝒜 f hfR hf) =
      (mapIso _ _ hfg hgf).hom ≫ baseChangeProjection 𝒜 S := by
    rw [map_congr (baseChangeLift_comp_baseChangeMap 𝒜 f hfR).symm _
      (HomogeneousIdeal.irrelevant_le_map_comp
        (HomogeneousIdeal.irrelevant_le_map_baseChangeMap S 𝒜)
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _ hfg.surjective)),
      map_comp, mapIso_hom, baseChangeProjection]
  have hcoeff : (mapIso _ _ hfg hgf).hom ≫ toSpecCoeff (fun n ↦ (𝒜 n).baseChange S) =
      toSpecCoeff ℬ := by
    rw [mapIso_hom]
    exact map_toSpecCoeff _ _ _ fun r ↦ Subtype.ext (by
      simp [Algebra.smul_def])
  refine (isPullback_baseChange 𝒜 S).of_iso (mapIso _ _ hfg hgf).symm (.refl _) (.refl _)
    (.refl _) ?_ ?_ ?_ ?_
  · simp [hmap, -mapIso_hom, -mapIso_inv]
  · simp [← hcoeff, -mapIso_hom, -mapIso_inv]
  · simp
  · simp

end IsBaseChange

end AlgebraicGeometry.Proj
