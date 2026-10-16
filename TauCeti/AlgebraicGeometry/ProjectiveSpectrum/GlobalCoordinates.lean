/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Unit rescaling of global projective coordinates

Multiplying the degree-`n` homogeneous coordinates by the `n`th power of a global unit
does not change the morphism to `Proj`. This is equality of scheme morphisms, including
their structure-sheaf maps, not merely equality on field-valued points. It permits
semi-invariant homogeneous coordinates to define invariant projective morphisms.

For Mathlib's `Proj.fromOfGlobalSections`, the coordinates must send the irrelevant
ideal to the unit ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace TauCeti.ProjectiveSpectrum

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}

/-- On a standard open, global homogeneous coordinates give the degree-zero localization
map of their restrictions to that open. -/
theorem toBasicOpenOfGlobalSections_eq (f : A →+* Γ(X, ⊤))
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht =
      (X.basicOpen (f t)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (Away.lift 𝒜
          ((X.presheaf.map (homOfLE le_top).op).hom.comp f)
          (X.toRingedSpace.isUnit_res_basicOpen (f t)))) ≫
        (Proj.basicOpenIsoSpec 𝒜 t ht hd).inv := by
  rw [← cancel_mono (Proj.basicOpenIsoSpec 𝒜 t ht hd).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- Restate the chart construction with scheme-typed opens: unfolding it directly
  -- exposes the underlying spectrum's distinct open-set coercions.
  have hdef : Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht =
      (X.isoOfEq (X.toSpecΓ_preimage_basicOpen (f t))).inv ≫
        X.toSpecΓ ∣_ (PrimeSpectrum.basicOpen (f t) : (Spec Γ(X, ⊤)).Opens) ≫
        (basicOpenIsoSpecAway (f t)).hom ≫ Spec.map (CommRingCat.ofHom
          ((IsLocalization.map (M := Submonoid.powers t) (T := Submonoid.powers (f t))
            (Localization.Away (f t)) f
            (by rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp
              (algebraMap (Away 𝒜 t) (Localization.Away t)))) ≫
        (Proj.basicOpenIsoSpec 𝒜 t ht hd).inv := rfl
  rw [hdef]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- Factor the restricted map to the spectrum of global sections through localization.
  let U := X.basicOpen (f t)
  let r := (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  have hu : IsUnit (r (f t)) := X.toRingedSpace.isUnit_res_basicOpen (f t)
  let l : Localization.Away (f t) →+* Γ(X, U) := IsLocalization.Away.lift (f t) hu
  have hlocal :
      (X.isoOfEq (X.toSpecΓ_preimage_basicOpen (f t))).inv ≫
          X.toSpecΓ ∣_ PrimeSpectrum.basicOpen (f t) ≫
          (basicOpenIsoSpecAway (f t)).hom =
        U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom l) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (Localization.Away (f t)))))]
    simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
    have hrest := congrArg
      (fun e ↦ (X.isoOfEq (X.toSpecΓ_preimage_basicOpen (f t))).inv ≫ e)
      (morphismRestrict_ι X.toSpecΓ
        (PrimeSpectrum.basicOpen (f t) : (Spec Γ(X, ⊤)).Opens))
    simp only [Scheme.isoOfEq_inv_ι_assoc] at hrest
    refine hrest.trans ?_
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hl : l.comp (algebraMap Γ(X, ⊤) (Localization.Away (f t))) = r :=
      IsLocalization.Away.lift_comp (f t) hu
    rw [hl]
    exact (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top U).symm
  rw [← Category.assoc, ← Category.assoc, Category.assoc
    (X.isoOfEq (X.toSpecΓ_preimage_basicOpen (f t))).inv, hlocal]
  simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  -- The remaining degree-zero maps agree on homogeneous fractions.
  congr 3
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht z
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  have hmk := Away.lift_mk (𝒜 := 𝒜) (r.comp f) hu ht n a ha
  refine Eq.trans ?_ hmk.symm
  apply (IsLocalization.lift_mk'_spec (M := Submonoid.powers (f t))
    (S := Localization.Away (f t)) (g := r) _ _ _ _).mpr
  have hs : r (f (t ^ n)) = ↑(hu.unit ^ n) := by
    rw [map_pow, map_pow, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [hs, mul_left_comm, Units.mul_inv, mul_one]
  rfl

/-- Unit rescaling of homogeneous coordinates preserves each projective chart map. -/
theorem toBasicOpenOfGlobalSections_eq_of_unit_rescaling
    (f g : A →+* Γ(X, ⊤)) (c : Γ(X, ⊤)ˣ)
    (h : ∀ n, ∀ a ∈ 𝒜 n, g a = c ^ n * f a)
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    ∃ e : X.basicOpen (f t) = X.basicOpen (g t),
      (X.isoOfEq e).hom ≫ Proj.toBasicOpenOfGlobalSections 𝒜 g rfl hd ht =
        Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht := by
  have he : X.basicOpen (f t) = X.basicOpen (g t) := by
    rw [h d t ht, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit X (c.isUnit.pow d), top_inf_eq]
  refine ⟨he, ?_⟩
  rw [toBasicOpenOfGlobalSections_eq, toBasicOpenOfGlobalSections_eq]
  have hres {U V : X.Opens} (e : U = V)
      (hf' : IsUnit (((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp f) t))
      (hg' : IsUnit (((X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.comp g) t)) :
      (X.isoOfEq e).hom ≫ V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
          (Away.lift 𝒜
            ((X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.comp g) hg')) =
        U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
          (Away.lift 𝒜
            ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp f) hf')) := by
    subst V
    simp only [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp]
    congr 3
    apply Away.lift_eq_of_forall_mem _ _
      (c.map (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom)
      (fun n a ha ↦ by simp [RingHom.comp_apply, h n a ha]) ht
  simpa only [Category.assoc] using congrArg
    (fun e ↦ e ≫ (Proj.basicOpenIsoSpec 𝒜 t ht hd).inv)
    (hres he (X.toRingedSpace.isUnit_res_basicOpen (f t))
      (X.toRingedSpace.isUnit_res_basicOpen (g t)))

/-- Multiplying the degree-`n` coordinates by the `n`th power of a global unit does not
change the resulting morphism to `Proj`. -/
theorem fromOfGlobalSections_eq_of_unit_rescaling
    (f g : A →+* Γ(X, ⊤)) (c : Γ(X, ⊤)ˣ)
    (h : ∀ n, ∀ a ∈ 𝒜 n, g a = c ^ n * f a)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    Proj.fromOfGlobalSections 𝒜 g
        (TauCeti.HomogeneousIdeal.map_irrelevant_eq_top_of_unit_rescaling
          𝒜 f g c (fun n _ ↦ h n) hf) =
      Proj.fromOfGlobalSections 𝒜 f hf := by
  let hg := TauCeti.HomogeneousIdeal.map_irrelevant_eq_top_of_unit_rescaling
    𝒜 f g c (fun n _ ↦ h n) hf
  refine (Proj.openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun ⟨d, t, hd, ht⟩ ↦ ?_
  obtain ⟨he, hchart⟩ := toBasicOpenOfGlobalSections_eq_of_unit_rescaling 𝒜 f g c h hd ht
  have hfchart := Proj.fromOfGlobalSections_resLE 𝒜 f hf hd ht
  have hgchart := Proj.fromOfGlobalSections_resLE 𝒜 g hg hd ht
  have hc := congrArg (fun e ↦ e ≫ (Proj.basicOpen 𝒜 t).ι) hchart
  rw [← hfchart, ← hgchart] at hc
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.isoOfEq_hom_ι_assoc] at hc
  exact hc

end TauCeti.ProjectiveSpectrum
