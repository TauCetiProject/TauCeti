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
# Flat base change of projective spectra

The projective spectrum of a graded algebra commutes with flat extension of its coefficient
ring. The comparison identifies the scheme fiber product, including its structure sheaf,
rather than only its points. Over a field, every coefficient extension is flat. This permits
projective linear transformations to be assembled into algebraic families.

The construction combines `Proj.map` for coefficient inclusion, the homogeneous chart
comparison `HomogeneousLocalization.Away.baseChangeEquiv`, and Mathlib's
`pullbackSpecIso` and local criterion `Scheme.isPullback_of_openCover`.

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

/-- The affine standard-chart square of flat coefficient extension is cartesian. -/
theorem isPullback_away_baseChange [Module.Flat R S] {f : A} {n : ℕ}
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

/-- Flat extension of coefficients makes the projective structural square cartesian. No
finite-generation hypothesis on the graded algebra is needed. -/
theorem isPullback_baseChangeProjection [Module.Flat R S] :
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

/-- The canonical identification of the projective spectrum after flat coefficient extension
with the fiber product over the original coefficient spectrum. -/
noncomputable def baseChangeIso [Module.Flat R S] :
    Proj (fun n ↦ (𝒜 n).baseChange S) ≅
      pullback (toSpecCoeff 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (isPullback_baseChangeProjection 𝒜 S).isoPullback

/-- The first projection of the comparison is the projective coefficient projection. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst [Module.Flat R S] :
    (baseChangeIso 𝒜 S).hom ≫ pullback.fst _ _ = baseChangeProjection 𝒜 S :=
  (isPullback_baseChangeProjection 𝒜 S).isoPullback_hom_fst

/-- The second projection of the comparison is the extended coefficient structure map. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd [Module.Flat R S] :
    (baseChangeIso 𝒜 S).hom ≫ pullback.snd _ _ =
      toSpecCoeff (fun n ↦ (𝒜 n).baseChange S) :=
  (isPullback_baseChangeProjection 𝒜 S).isoPullback_hom_snd

end AlgebraicGeometry.Proj
