/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.AlgebraicGeometry.PuncturedSpectrum
public import TauCeti.RingTheory.LocalRing.Quotient
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Finiteness.Descent
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.Scheme.SectionsBaseChange
import TauCeti.CategoryTheory.Comma.Over
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.EqToHom
import TauCeti.RingTheory.FormalGlueing.Reconstruction

/-!
# Extending finite morphisms from the completion across the closed point

Let `A → A'` be a flat homomorphism of local rings, with `A` Noetherian, that induces a bijection
`A ⧸ 𝔪_A → A' ⧸ 𝔪_A A'` (for instance, the `𝔪_A`-adic completion `Â` of `A`). Then `𝔪_A A' = 𝔪_{A'}`
(`TauCeti.IsLocalRing.map_maximalIdeal_of_bijective_quotientMap`), so `A → A'` is faithfully flat
and the punctured spectrum `U'` of `A'` is the preimage of the punctured spectrum `U` of `A`.

Suppose `V ⟶ U` is a finite morphism whose base change `V' = V ×_U U'` to `U'` extends to a finite
morphism `Y' ⟶ Spec A'`. This file proves that `V` extends to a finite morphism `Y ⟶ Spec A` whose
base change to `Spec A'` is `Y'` and whose restriction to `U` is `V`, compatibly with the given
identification over `U'`.

The proof passes to global sections and applies subalgebra formal gluing
(`Subalgebra.exists_isBaseChange_of_formalGlueing`) along `A → A'` and a finite generating set `G`
of `𝔪_A`:

* Flat base change (`TauCeti.AlgebraicGeometry.isBaseChange_sectionsBaseChange`) identifies
  `Γ(V', ⊤)` with `A' ⊗[A] Γ(V, ⊤)`.
* Because `Y' ⟶ Spec A'` is finite over an affine base, `Y'` is affine, and for every `x ∈ G` the
  basic open `D(x)` on `Spec A'` lies in `U'`. Restricting the open immersion `V' ⟶ Y'` over the
  corresponding basic open of `Y'` gives an isomorphism of principal localizations, so
  `Γ(Y', ⊤) → Γ(V', ⊤)` becomes bijective after inverting the image of each `x ∈ G`.
* Formal gluing produces an `A`-subalgebra `B ≤ Γ(Y', ⊤)` with `A' ⊗[A] B ≃ₐ[A'] Γ(Y', ⊤)` and an
  `A`-algebra map `B →ₐ[A] Γ(V, ⊤)` compatible with `Γ(Y', ⊤) → Γ(V', ⊤)`.
* Faithfully flat descent gives finiteness of `B` over `A`, so `Y = Spec B` is finite over `Spec A`,
  and fpqc descent of isomorphisms along `U' ⟶ U` shows that the induced comparison `V ⟶ Y ×_X U`
  is an isomorphism over `U`.

## Main declarations

* `TauCeti.IsLocalRing.overRestrictPuncturedCompPullbackIso`: restriction of schemes over `Spec A`
  to the punctured spectrum commutes with pullback along `Spec A' ⟶ Spec A`.
* `TauCeti.IsLocalRing.finite_extend_of_bijective_quotientMap`: extending a finite morphism over
  the punctured spectrum of `A` from a finite extension over `Spec A'`, for any flat `A → A'`
  inducing `A ⧸ 𝔪_A ≅ A' ⧸ 𝔪_A A'`.
* `TauCeti.IsLocalRing.finite_extend_of_completion`: the case of the `𝔪_A`-adic completion `Â` of
  `A` (Stacks, Lemma 58.19.3 (0BLH)).

## References

* [The Stacks Project, Lemma 58.19.3](https://stacks.math.columbia.edu/tag/0BLH).
* [The Stacks Project, Proposition 15.91.16](https://stacks.math.columbia.edu/tag/05ER).
* [The Stacks Project, Remark 15.91.20](https://stacks.math.columbia.edu/tag/05EU).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite IsLocalRing
open scoped TensorProduct

universe u

namespace TauCeti.IsLocalRing

section PullbackIso

variable {A A' : Type u} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A'] [Algebra A A']

/-- Restriction of schemes over `Spec A` to the punctured spectrum commutes with pullback along
`Spec A' ⟶ Spec A` whenever the closed point is the only point of `Spec A'` over the closed point
of `Spec A`. -/
def overRestrictPuncturedCompPullbackIso
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A') :
    Over.pullback (puncturedSpectrum A).ι ⋙
        Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
          (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⋙
        Over.pullback (puncturedSpectrum A').ι :=
  (Over.pullbackComp _ _).symm ≪≫
    eqToIso (by
      have heq : ∀ (g₁ g₂ : (puncturedSpectrum A').toScheme ⟶ Spec (.of A))
          [i₁ : HasPullbacksAlong g₁] [i₂ : HasPullbacksAlong g₂],
          g₁ = g₂ → @Over.pullback _ _ _ _ g₁ i₁ = @Over.pullback _ _ _ _ g₂ i₂ := by
        rintro g _ _ _ rfl
        rfl
      exact heq _ _ (Scheme.Hom.resLE_comp_ι _ _)) ≪≫
    Over.pullbackComp _ _

@[reassoc (attr := simp)]
theorem overRestrictPuncturedCompPullbackIso_hom_app_left_fst_fst
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (Y : Over (Spec (.of A))) :
    ((overRestrictPuncturedCompPullbackIso h).hom.app Y).left ≫
        pullback.fst (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
          (puncturedSpectrum A').ι ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))) =
      pullback.fst (pullback.snd Y.hom (puncturedSpectrum A).ι)
          ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
            (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) ≫
        pullback.fst Y.hom (puncturedSpectrum A).ι := by
  simp [overRestrictPuncturedCompPullbackIso, Over.pullbackComp,
    eqToHom_comp_pullback_fst Y.hom
      ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE_comp_ι
        (preimage_puncturedSpectrum h).ge)]

@[reassoc (attr := simp)]
theorem overRestrictPuncturedCompPullbackIso_hom_app_left_snd
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (Y : Over (Spec (.of A))) :
    ((overRestrictPuncturedCompPullbackIso h).hom.app Y).left ≫
        pullback.snd (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
          (puncturedSpectrum A').ι =
      pullback.snd (pullback.snd Y.hom (puncturedSpectrum A).ι)
        ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
          (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) :=
  Over.w ((overRestrictPuncturedCompPullbackIso h).hom.app Y)

@[reassoc (attr := simp)]
theorem overRestrictPuncturedCompPullbackIso_inv_app_left_fst_fst
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (Y : Over (Spec (.of A))) :
    ((overRestrictPuncturedCompPullbackIso h).inv.app Y).left ≫
        pullback.fst (pullback.snd Y.hom (puncturedSpectrum A).ι)
          ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
            (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) ≫
        pullback.fst Y.hom (puncturedSpectrum A).ι =
      pullback.fst (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
          (puncturedSpectrum A').ι ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
  simp [overRestrictPuncturedCompPullbackIso, Over.pullbackComp,
    eqToHom_comp_pullback_fst Y.hom
      ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE_comp_ι
        (preimage_puncturedSpectrum h).ge).symm]

@[reassoc (attr := simp)]
theorem overRestrictPuncturedCompPullbackIso_inv_app_left_snd
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (Y : Over (Spec (.of A))) :
    ((overRestrictPuncturedCompPullbackIso h).inv.app Y).left ≫
        pullback.snd (pullback.snd Y.hom (puncturedSpectrum A).ι)
          ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
            (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) =
      pullback.snd (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
        (puncturedSpectrum A').ι :=
  Over.w ((overRestrictPuncturedCompPullbackIso h).inv.app Y)

end PullbackIso

variable {A A' : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A']

/-- Global-sections reconstruction step for `finite_extend_of_bijective_quotientMap`: formal gluing
along `A → A'` produces a module-finite `A`-algebra `B`, an identification of `A' ⊗[A] B` with
`Γ(Y', ⊤)` over `A'`, and a ring map `B →+* Γ(V, ⊤)` over `A` compatible with restriction to the
base change `V'` over the punctured spectrum of `A'`. -/
private theorem exists_finite_algebra_of_bijective_quotientMap
    (hquot : Function.Bijective (Ideal.quotientMap ((maximalIdeal A).map (algebraMap A A'))
      (algebraMap A A') Ideal.le_comap_map))
    (V : Over (puncturedSpectrum A).toScheme) [IsFinite V.hom]
    (Y' : Over (Spec (.of A'))) [IsFinite Y'.hom]
    (e' : (Over.pullback (puncturedSpectrum A').ι).obj Y' ≅
      (Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A')
        (preimage_puncturedSpectrum
          (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).ge)).obj V) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
      (b'Hom : B →+* Γ(Y'.left, ⊤)) (ψ : B →+* Γ(V.left, ⊤))
      (eSpec : Over.mk (pullback.snd (Spec.algebraMap A B)
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))) ≅ Y'),
      ψ.comp (algebraMap A B) =
          ((Scheme.ΓSpecIso (.of A)).inv ≫ (V.hom ≫ (puncturedSpectrum A).ι).appTop).hom ∧
        ((pullback.fst V.hom
          ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
            (puncturedSpectrum A) (puncturedSpectrum A')
            (preimage_puncturedSpectrum
              (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).ge)).appTop.hom).comp ψ =
          ((e'.inv.left ≫ pullback.fst Y'.hom (puncturedSpectrum A').ι).appTop.hom).comp b'Hom ∧
        eSpec.inv.left ≫ pullback.fst (Spec.algebraMap A B)
            (Spec.map (CommRingCat.ofHom (algebraMap A A'))) =
          Y'.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b'Hom) := by
  classical
  have hmap : (maximalIdeal A).map (algebraMap A A') = maximalIdeal A' :=
    map_maximalIdeal_of_bijective_quotientMap hquot
  have hrad : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A' :=
    radical_map_maximalIdeal_of_bijective_quotientMap hquot
  have : IsLocalHom (algebraMap A A') :=
    ((local_hom_tfae (algebraMap A A')).out 1 3).mpr hmap.le
  have : Module.FaithfullyFlat A A' := .of_flat_of_isLocalHom
  let U := puncturedSpectrum A
  let U' := puncturedSpectrum A'
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let r := f.resLE U U' (preimage_puncturedSpectrum hrad).ge
  have hU : IsPullback r U'.ι U.ι f := IsOpenImmersion.isPullback _ _ _ _
    (Scheme.Hom.resLE_comp_ι _ _).symm (by simpa using preimage_puncturedSpectrum hrad)
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp
    (isCompact_puncturedSpectrum_of_fg_maximalIdeal A (maximalIdeal A).fg_of_isNoetherianRing)
  have : CompactSpace U'.toScheme := isCompact_iff_compactSpace.mp
    (isCompact_puncturedSpectrum_of_fg_maximalIdeal A'
      (hmap ▸ (maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A A')))
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  have : QuasiSeparatedSpace V.left := quasiSeparatedSpace_of_quasiSeparated (V.hom ≫ U.ι)
  let V' := pullback V.hom r
  let π' : V' ⟶ U'.toScheme := pullback.snd V.hom r
  have : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace π'
  have : QuasiSeparatedSpace V' := quasiSeparatedSpace_of_quasiSeparated (π' ≫ U'.ι)
  have : IsAffine Y'.left := isAffine_of_isAffineHom Y'.hom
  -- Equip `Γ(V, ⊤)`, `Γ(V', ⊤)`, and `Γ(Y', ⊤)` with their canonical base-ring algebra structures.
  let : V.left.Over (Spec (.of A)) := ⟨V.hom ≫ U.ι⟩
  let : V'.Over (Spec (.of A')) := ⟨π' ≫ U'.ι⟩
  have H : IsPullback (pullback.fst V.hom r) (V' ↘ Spec (.of A')) (V.left ↘ Spec (.of A)) f :=
    (IsPullback.of_hasPullback V.hom r).paste_vert hU
  let aMapM : A →+* Γ(V.left, ⊤) := ((V.left.baseRingToStructurePresheaf A).app (op ⊤)).hom
  let aMapP : A' →+* Γ(V', ⊤) := ((V'.baseRingToStructurePresheaf A').app (op ⊤)).hom
  let aMapB' : A' →+* Γ(Y'.left, ⊤) := ((Scheme.ΓSpecIso (.of A')).inv ≫ Y'.hom.appTop).hom
  algebraize [aMapM, aMapP, aMapP.comp (algebraMap A A'), aMapB', aMapB'.comp (algebraMap A A')]
  have : IsScalarTower A A' Γ(V', ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A A' Γ(Y'.left, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  -- Flat base change identifies `Γ(V', ⊤)` with `A' ⊗[A] Γ(V, ⊤)`.
  have hf_bc_lin : IsBaseChange A' (TauCeti.AlgebraicGeometry.sectionsBaseChange H
      (W := ⊤) (W' := ⊤) le_top) :=
    TauCeti.AlgebraicGeometry.isBaseChange_sectionsBaseChange H isCompact_univ
      isQuasiSeparated_univ rfl
  have happ {X Y : Scheme.{u}} (g : X ⟶ Y) : g.appLE ⊤ ⊤ le_top = g.appTop :=
    (Scheme.Hom.app_eq_appLE g).symm
  let f_alg : Γ(V.left, ⊤) →ₐ[A] Γ(V', ⊤) :=
    { toRingHom := (pullback.fst V.hom r).appTop.hom
      commutes' a := by
        have hcomp_app :=
          TauCeti.AlgebraicGeometry.baseRingToStructurePresheaf_app_comp_appLE_of_isPullback
            H (W := ⊤) (W' := ⊤) le_top
        rw [happ] at hcomp_app
        exact congr($hcomp_app a) }
  have hf_eq_lin : f_alg.toLinearMap =
      TauCeti.AlgebraicGeometry.sectionsBaseChange H (W := ⊤) (W' := ⊤) le_top := by
    ext m
    exact ((TauCeti.AlgebraicGeometry.sectionsBaseChange_apply H le_top m).trans
      congr($(happ (pullback.fst V.hom r)) m)).symm
  have hf_bc : IsBaseChange A' f_alg.toLinearMap := hf_eq_lin ▸ hf_bc_lin
  -- Open immersion `j' : V' ⟶ Y'` and localized bijectivity of `g_alg : Γ(Y', ⊤) →ₐ[A'] Γ(V', ⊤)`.
  let j' : V' ⟶ Y'.left := e'.inv.left ≫ pullback.fst Y'.hom U'.ι
  have hj'_comm : j' ≫ Y'.hom = π' ≫ U'.ι := by
    have hw := Over.w e'.inv
    dsimp only [Over.pullback_obj_hom, Over.mk_hom] at hw
    dsimp only [j']
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  let e'_left : pullback Y'.hom U'.ι ≅ V' :=
    { hom := e'.hom.left
      inv := e'.inv.left
      hom_inv_id := by
        rw [← Over.comp_left, e'.hom_inv_id, Over.id_left]
        rfl
      inv_hom_id := by
        rw [← Over.comp_left, e'.inv_hom_id, Over.id_left]
        rfl }
  have hj'_pb : IsPullback j' π' Y'.hom U'.ι :=
    (IsPullback.of_hasPullback Y'.hom U'.ι).of_iso e'_left (.refl _) (.refl _) (.refl _)
      (by
        simp only [e'_left, j', Iso.refl_hom, Category.comp_id, ← Category.assoc, ← Over.comp_left,
          e'.hom_inv_id, Over.id_left]
        exact (Category.id_comp _).symm)
      (by
        have hw := Over.w e'.hom
        dsimp only [Over.pullback_obj_hom, Over.mk_hom] at hw
        exact (Category.comp_id _).trans hw.symm)
      (by simp) (by simp)
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback hj'_pb.flip inferInstance
  have hcomm_app :
      (Scheme.ΓSpecIso (.of A')).inv ≫ Y'.hom.appTop ≫ j'.appTop =
        (V'.baseRingToStructurePresheaf A').app (op ⊤) := by
    rw [← Scheme.Hom.comp_appTop, hj'_comm,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE A' V', happ]
    rfl
  let g_alg : Γ(Y'.left, ⊤) →ₐ[A'] Γ(V', ⊤) :=
    { toRingHom := j'.appTop.hom
      commutes' a' := by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        exact congr($hcomm_app a') }
  obtain ⟨G, hG_span⟩ := (maximalIdeal A).fg_of_isNoetherianRing
  have hG_quot : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (G : Set A)).map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map) :=
    hG_span ▸ hquot
  have hg_loc (x : A) (hx : x ∈ G) :
      Function.Bijective (LocalizedModule.map (.powers (algebraMap A A' x)) g_alg.toLinearMap) := by
    have hx_m : x ∈ maximalIdeal A := hG_span ▸ Ideal.subset_span hx
    have hs_m : algebraMap A A' x ∈ maximalIdeal A' := hmap ▸ Ideal.mem_map_of_mem _ hx_m
    have hrange :
        Y'.left.basicOpen (algebraMap A' Γ(Y'.left, ⊤) (algebraMap A A' x)) ≤ j'.opensRange := by
      let D : (Spec (.of A')).Opens := PrimeSpectrum.basicOpen (algebraMap A A' x)
      have h1 : Y'.left.basicOpen (algebraMap A' Γ(Y'.left, ⊤) (algebraMap A A' x)) =
          Y'.hom ⁻¹ᵁ D := by
        simp only [RingHom.algebraMap_toAlgebra, aMapB', CommRingCat.hom_comp, RingHom.comp_apply]
        rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
      rw [h1]
      intro y hy
      have hyD : Y'.hom y ∈ PrimeSpectrum.basicOpen (algebraMap A A' x) :=
        (Scheme.Hom.mem_preimage (f := Y'.hom) (U := D) (x := y)).mp hy
      have hyU' : Y'.hom y ∈ U' :=
        (mem_puncturedSpectrum_iff A' _).mpr fun hclosed ↦ hyD (by rw [hclosed]; exact hs_m)
      obtain ⟨w, hw1, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y'.hom) (g := U'.ι) y
        ⟨Y'.hom y, hyU'⟩ rfl
      refine ⟨e'.hom.left w, ?_⟩
      have he_inv_hom : (e'.hom.left ≫ e'.inv.left) w = w := by
        rw [← Over.comp_left, e'.hom_inv_id, Over.id_left]
        rfl
      dsimp only [j']
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e'.hom.left e'.inv.left, he_inv_hom, hw1]
    exact j'.bijective_localizedModuleMap_of_basicOpen_le_opensRange g_alg rfl
      (algebraMap A A' x) hrange
  -- Reconstruct the `A`-subalgebra `B ≤ Γ(Y', ⊤)` and descend finiteness from `Γ(Y', ⊤)` over `A'`.
  obtain ⟨B, ψ, hpush, hcomp, _⟩ :=
    Subalgebra.exists_isBaseChange_of_formalGlueing hG_quot f_alg hf_bc g_alg hg_loc
  have hY'_isoSpec : Y'.left.isoSpec.hom ≫ Spec.algebraMap A' Γ(Y'.left, ⊤) = Y'.hom := by
    rw [Scheme.isoSpec_hom]
    dsimp only [Spec.algebraMap]
    rw [RingHom.algebraMap_toAlgebra]
    dsimp only [aMapB']
    rw [CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have : IsFinite (Spec.algebraMap A' Γ(Y'.left, ⊤)) := by
    have heq : Spec.algebraMap A' Γ(Y'.left, ⊤) = Y'.left.isoSpec.inv ≫ Y'.hom := by
      rw [← hY'_isoSpec, Iso.inv_hom_id_assoc]
    rw [heq]
    infer_instance
  have : Module.Finite A' Γ(Y'.left, ⊤) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp ‹_›)
  have : Module.Finite A' (A' ⊗[A] B) :=
    Module.Finite.equiv (Algebra.IsPushout.equiv A A' B Γ(Y'.left, ⊤)).symm.toLinearEquiv
  have hB_fin : Module.Finite A B := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A'
  -- Assemble the `Spec`-level base-change isomorphism `eSpec` and global-section compatibilities.
  let eSpec : Over.mk (pullback.snd (Spec.algebraMap A B) f) ≅ Y' :=
    TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv A B A' Γ(Y'.left, ⊤)
      (Algebra.IsPushout.equiv A A' B Γ(Y'.left, ⊤)) ≪≫
      Over.isoMk Y'.left.isoSpec.symm (by
        rw [Iso.symm_hom, ← cancel_epi Y'.left.isoSpec.hom, Iso.hom_inv_id_assoc]
        exact hY'_isoSpec.symm)
  have hψA : ψ.toRingHom.comp (algebraMap A B) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (V.hom ≫ U.ι).appTop).hom := by
    ext a
    refine (ψ.commutes a).trans ?_
    simp only [RingHom.algebraMap_toAlgebra, aMapM]
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE A V.left, happ]
    rfl
  have hcomp_ring : (pullback.fst V.hom r).appTop.hom.comp ψ.toRingHom =
      j'.appTop.hom.comp B.val.toRingHom :=
    congrArg AlgHom.toRingHom hcomp
  have heSpec_fst : eSpec.inv.left ≫ pullback.fst (Spec.algebraMap A B) f =
      Y'.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom B.val.toRingHom) := by
    have hval : (Algebra.IsPushout.equiv A A' B Γ(Y'.left, ⊤)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom = B.val.toRingHom := by
      ext b
      exact (Algebra.IsPushout.equiv_tmul A A' B Γ(Y'.left, ⊤) 1 b).trans (by simp)
    have hproj :
        (TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv A B A' Γ(Y'.left, ⊤)
            (Algebra.IsPushout.equiv A A' B Γ(Y'.left, ⊤))).inv.left ≫
          pullback.fst (Spec.algebraMap A B) (Spec.algebraMap A A') =
          Spec.map (CommRingCat.ofHom B.val.toRingHom) := by
      rw [TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv_inv_left, Category.assoc,
        Category.assoc, pullbackSymmetry_inv_comp_fst, pullbackSpecIso_inv_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← hval]
      rfl
    dsimp only [eSpec, f, Iso.trans_inv, Over.comp_left]
    rw [Category.assoc]
    exact congrArg (Y'.left.toSpecΓ ≫ ·) hproj
  exact ⟨B, inferInstance, inferInstance, hB_fin, B.val.toRingHom, ψ.toRingHom, eSpec,
    hψA, hcomp_ring, heSpec_fst⟩

/-- **Extending a finite morphism across the closed point from a flat local extension preserving
the residue field.** Let `A → A'` be a flat homomorphism of local rings, with `A` Noetherian, that
induces a bijection `A ⧸ 𝔪_A → A' ⧸ 𝔪_A A'`. If `V ⟶ U` is a finite morphism over the punctured
spectrum `U` of `A` whose base change to the punctured spectrum `U'` of `A'` is isomorphic to the
restriction of a finite morphism `Y' ⟶ Spec A'`, then there exist a finite morphism `Y ⟶ Spec A`,
an isomorphism `Y ×_{Spec A} Spec A' ≅ Y'` over `Spec A'`, and an isomorphism `Y ×_{Spec A} U ≅ V`
over `U` compatible with the given isomorphism over `U'`. -/
theorem finite_extend_of_bijective_quotientMap
    (hquot : Function.Bijective (Ideal.quotientMap ((maximalIdeal A).map (algebraMap A A'))
      (algebraMap A A') Ideal.le_comap_map))
    (V : Over (puncturedSpectrum A).toScheme) [IsFinite V.hom]
    (Y' : Over (Spec (.of A'))) [IsFinite Y'.hom]
    (e' : (Over.pullback (puncturedSpectrum A').ι).obj Y' ≅
      (Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A')
        (preimage_puncturedSpectrum
          (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).ge)).obj V) :
    ∃ (Y : Over (Spec (.of A))) (_ : IsFinite Y.hom)
      (eY' : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A')))).obj Y ≅ Y')
      (eV : (Over.pullback (puncturedSpectrum A).ι).obj Y ≅ V),
      (overRestrictPuncturedCompPullbackIso
        (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).hom.app Y ≫
        (Over.pullback (puncturedSpectrum A').ι).map eY'.hom ≫ e'.hom =
      (Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A')
        (preimage_puncturedSpectrum
          (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).ge)).map eV.hom := by
  have hmap : (maximalIdeal A).map (algebraMap A A') = maximalIdeal A' :=
    map_maximalIdeal_of_bijective_quotientMap hquot
  have hrad : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A' :=
    radical_map_maximalIdeal_of_bijective_quotientMap hquot
  have : IsLocalHom (algebraMap A A') :=
    ((local_hom_tfae (algebraMap A A')).out 1 3).mpr hmap.le
  have : Module.FaithfullyFlat A A' := .of_flat_of_isLocalHom
  let U := puncturedSpectrum A
  let U' := puncturedSpectrum A'
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let r := f.resLE U U' (preimage_puncturedSpectrum hrad).ge
  have hU : IsPullback r U'.ι U.ι f := IsOpenImmersion.isPullback _ _ _ _
    (Scheme.Hom.resLE_comp_ι _ _).symm (by simpa using preimage_puncturedSpectrum hrad)
  obtain ⟨B, _, _, _, b'Hom, ψ, eY', hψA, hcomp_ring, heY'_fst⟩ :=
    exists_finite_algebra_of_bijective_quotientMap hquot V Y' e'
  let q : Spec (.of B) ⟶ Spec (.of A) := Spec.algebraMap A B
  have : IsFinite q := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let Y : Over (Spec (.of A)) := Over.mk q
  -- Build the comparison morphism `Φ : V ⟶ Y ×_{Spec A} U` over `U`.
  let jV : V.left ⟶ Spec (.of B) := V.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have hjV : jV ≫ q = V.hom ≫ U.ι := by
    dsimp only [jV, q, Spec.algebraMap]
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψA, CommRingCat.ofHom_hom,
      Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  let Φ : V ⟶ (Over.pullback U.ι).obj Y :=
    Over.homMk (pullback.lift jV V.hom hjV) (pullback.lift_snd _ _ _)
  -- Compare `(Over.pullback r).map Φ` with `e'.inv` over `U'`.
  have hΦ_pull :
      (Over.pullback r).map Φ =
        e'.inv ≫ (Over.pullback U'.ι).map eY'.inv ≫
          (overRestrictPuncturedCompPullbackIso hrad).inv.app Y := by
    ext1
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · dsimp only [Over.pullback_obj_hom, Over.mk_hom, Y]
        simp only [Category.assoc]
        have hL : ((Over.pullback r).map Φ).left ≫
            pullback.fst (pullback.snd q U.ι) r ≫ pullback.fst q U.ι =
            (pullback V.hom r).toSpecΓ ≫
              Spec.map (CommRingCat.ofHom ((pullback.fst V.hom r).appTop.hom.comp ψ)) := by
          have hΦ_left : Φ.left = pullback.lift jV V.hom hjV := rfl
          simp only [Over.pullback_map_left]
          dsimp only [Over.pullback_obj_hom, Over.mk_hom, Y]
          rw [pullback.lift_fst_assoc, Category.assoc, hΦ_left, pullback.lift_fst]
          dsimp only [jV]
          rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]
          rfl
        have hR_step : ((overRestrictPuncturedCompPullbackIso hrad).inv.app Y).left ≫
            pullback.fst (pullback.snd q U.ι) r ≫ pullback.fst q U.ι =
            pullback.fst (pullback.snd q f) U'.ι ≫ pullback.fst q f :=
          overRestrictPuncturedCompPullbackIso_inv_app_left_fst_fst hrad Y
        have hR : (e'.inv ≫ (Over.pullback U'.ι).map eY'.inv ≫
            (overRestrictPuncturedCompPullbackIso hrad).inv.app Y).left ≫
            pullback.fst (pullback.snd q U.ι) r ≫ pullback.fst q U.ι =
            (pullback V.hom r).toSpecΓ ≫
              Spec.map (CommRingCat.ofHom
                ((e'.inv.left ≫ pullback.fst Y'.hom U'.ι).appTop.hom.comp b'Hom)) := by
          simp only [Over.comp_left, Category.assoc, hR_step, Over.pullback_map_left]
          dsimp only [Over.pullback_obj_hom, Over.mk_hom, Y, q, f]
          rw [pullback.lift_fst_assoc, Category.assoc, heY'_fst, ← Category.assoc e'.inv.left,
            Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]
          rfl
        rw [hL, hR, hcomp_ring]
      · dsimp only [Over.pullback_obj_hom, Over.mk_hom]
        have hw1 := Over.w ((Over.pullback r).map Φ)
        have hw2 := Over.w (e'.inv ≫ (Over.pullback U'.ι).map eY'.inv ≫
          (overRestrictPuncturedCompPullbackIso hrad).inv.app Y)
        dsimp only [Functor.comp_obj, Over.pullback_obj_hom, Over.mk_hom] at hw1 hw2
        rw [Category.assoc, pullback.condition, ← Category.assoc, hw1,
          Category.assoc, pullback.condition, ← Category.assoc, hw2]
    · have hw1 := Over.w ((Over.pullback r).map Φ)
      have hw2 := Over.w (e'.inv ≫ (Over.pullback U'.ι).map eY'.inv ≫
        (overRestrictPuncturedCompPullbackIso hrad).inv.app Y)
      dsimp only [Functor.comp_obj, Over.pullback_obj_hom, Over.mk_hom] at hw1 hw2
      exact hw1.trans hw2.symm
  -- Descend `IsIso` from `(Over.pullback r).map Φ` along the fpqc morphism `r`.
  have : Flat f := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A A'›)
  have : Surjective f := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : Surjective r := MorphismProperty.of_isPullback hU.flip ‹Surjective f›
  have : Flat r := MorphismProperty.of_isPullback hU.flip ‹Flat f›
  have : QuasiCompact r := MorphismProperty.of_isPullback hU.flip inferInstance
  have hΦ_map_iso : IsIso ((Over.pullback r).map Φ) := by
    rw [hΦ_pull]
    infer_instance
  have hΦ_map_left_iso : IsIso ((Over.pullback r).map Φ).left :=
    (Over.forget _).map_isIso ((Over.pullback r).map Φ)
  have hΦ_left_iso : IsIso Φ.left :=
    (MorphismProperty.isomorphisms Scheme.{u}).of_isPullback_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (Over.isPullback_pullback_map_left r Φ)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hΦ_map_left_iso
  let eV : (Over.pullback U.ι).obj Y ≅ V :=
    (Over.isoMk (asIso Φ.left) (Over.w Φ)).symm
  have heV_inv : eV.inv = Φ := by
    ext1
    rfl
  refine ⟨Y, ‹IsFinite q›, eY', eV, ?_⟩
  rw [← cancel_mono ((Over.pullback r).map eV.inv), ← Functor.map_comp, eV.hom_inv_id,
    CategoryTheory.Functor.map_id, heV_inv, hΦ_pull]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((Over.pullback U'.ι).map eY'.hom), ← Functor.map_comp, eY'.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

omit [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A'] in
/-- **Extending a finite morphism from the completion across the closed point** (Stacks, Lemma
58.19.3 (0BLH)). Let `A` be a Noetherian local ring with `𝔪`-adic completion `Â`, punctured spectrum
`U`, and completed punctured spectrum `U'`. If `V ⟶ U` is a finite morphism whose base change to
`U'` is isomorphic to the restriction of a finite morphism `Y' ⟶ Spec Â`, then there exist a finite
morphism `Y ⟶ Spec A`, an isomorphism `Y ×_{Spec A} Spec Â ≅ Y'` over `Spec Â`, and an isomorphism
`Y ×_{Spec A} U ≅ V` over `U` compatible with the given isomorphism over `U'`. -/
@[stacks 0BLH]
theorem finite_extend_of_completion
    (V : Over (puncturedSpectrum A).toScheme) [IsFinite V.hom]
    (Y' : Over (Spec (.of (AdicCompletion (maximalIdeal A) A)))) [IsFinite Y'.hom]
    (e' : (Over.pullback (puncturedSpectrum (AdicCompletion (maximalIdeal A) A)).ι).obj Y' ≅
      (Over.pullback
        ((Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))).resLE
          (puncturedSpectrum A) (puncturedSpectrum (AdicCompletion (maximalIdeal A) A))
          (preimage_puncturedSpectrum (by
            rw [← AdicCompletion.maximalIdeal_eq_map]
            exact (maximalIdeal.isMaximal _).isPrime.radical)).ge)).obj V) :
    ∃ (Y : Over (Spec (.of A))) (_ : IsFinite Y.hom)
      (eY' : (Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A))))).obj Y ≅
          Y')
      (eV : (Over.pullback (puncturedSpectrum A).ι).obj Y ≅ V),
      (overRestrictPuncturedCompPullbackIso (A' := AdicCompletion (maximalIdeal A) A) (by
        rw [← AdicCompletion.maximalIdeal_eq_map]
        exact (maximalIdeal.isMaximal _).isPrime.radical)).hom.app Y ≫
        (Over.pullback (puncturedSpectrum (AdicCompletion (maximalIdeal A) A)).ι).map eY'.hom ≫
          e'.hom =
      (Over.pullback
        ((Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))).resLE
          (puncturedSpectrum A) (puncturedSpectrum (AdicCompletion (maximalIdeal A) A))
          (preimage_puncturedSpectrum (by
            rw [← AdicCompletion.maximalIdeal_eq_map]
            exact (maximalIdeal.isMaximal _).isPrime.radical)).ge)).map eV.hom :=
  finite_extend_of_bijective_quotientMap
    (bijective_quotientMap_iff_map_maximalIdeal_eq_and_bijective_residueFieldMap.mpr
      ⟨AdicCompletion.maximalIdeal_eq_map.symm, AdicCompletion.residueField_map_bijective A⟩)
    V Y' e'

end TauCeti.IsLocalRing
