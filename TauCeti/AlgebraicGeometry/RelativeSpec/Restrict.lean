/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.UniversalProperty

/-!
# The relative spectrum of functions on a scheme affine over an open

Let `U` be an open subscheme of a scheme `X` and `r : T ⟶ U` an affine morphism, and write
`q = r ≫ U.ι : T ⟶ X`. Suppose the function algebra `A = q_* 𝒪_T` is quasi-coherent, as it is
when `q` is quasi-compact and quasi-separated. Then the relative spectrum `Spec_X A` restricts
over `U` to `T`: the morphism `T ⟶ Spec_X A ×_X U` induced by the canonical morphism
`T ⟶ Spec_X A` over `X` (the lift `CategoryTheory.CommMon.relativeSpecLift` of the identity of
`A`) and by `r` is an isomorphism
(`TauCeti.AlgebraicGeometry.isIso_pullbackLift_relativeSpecLift_id`).

Away from `U` the relative spectrum is in general not `T`; it is a scheme affine over `X`
extending `T`. When `r` is affine over all of `X`, that is `U = X`, the relative spectrum is `T`
itself (`AlgebraicGeometry.Scheme.Hom.isIso_relativeSpecFunctionsToScheme`). This is how a
scheme affine over an open subscheme is extended to a scheme affine over `X`, for instance a
finite étale cover of `U` to a finite étale cover of `X` once its function algebra is known to be
finite étale over every affine open of `X`.

The proof checks the isomorphism over the affine opens `W ⊆ U` of `X`. There the inverse image
`q⁻¹ W` is affine, and on it the morphism `T ⟶ Spec_X A` is the identification of `q⁻¹ W` with
the spectrum of its ring of functions, followed by the chart of `Spec_X A` over `W`
(`CategoryTheory.CommMon.ι_relativeSpecLift`).

## References

* The Stacks Project, Tag 01LL (relative spectrum).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- Over an affine open `W ⊆ U`, the canonical morphism `T ⟶ Spec_X (q_* 𝒪_T)` is, on the affine
open `q⁻¹ W` of `T`, an isomorphism onto the spectrum of the sections over `W` followed by the
chart of the relative spectrum over `W`. -/
private lemma exists_isIso_ι_relativeSpecLift_id {X T : Scheme.{u}} (U : X.Opens)
    (r : T ⟶ U.toScheme) [IsAffineHom r]
    [(r ≫ U.ι).pushforwardStructureAlgebra.X.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
    (hWU : W ≤ U) :
    ∃ a : ((r ≫ U.ι) ⁻¹ᵁ W).toScheme ⟶
        Spec (.of Γ((r ≫ U.ι).pushforwardStructureAlgebra.X, W)),
      IsIso a ∧ ((r ≫ U.ι) ⁻¹ᵁ W).ι ≫
          CommMon.relativeSpecLift (𝟙 (r ≫ U.ι).pushforwardStructureAlgebra) =
        a ≫ (r ≫ U.ι).pushforwardStructureAlgebra.relativeSpecCover.f
          (⟨W, hW⟩ : X.AffineZariskiSite) := by
  set q := r ≫ U.ι
  set A := q.pushforwardStructureAlgebra
  have hqW : IsAffineOpen (q ⁻¹ᵁ W) :=
    (hW.preimage_of_isOpenImmersion U.ι (by rwa [Scheme.Opens.opensRange_ι])).preimage r
  let φ := CommRingCat.ofHom ((q.pushforwardStructureAlgebraSectionsRingEquiv W).toRingHom.comp
    (CommMon.sectionsAlgHom (𝟙 A) W).toRingHom)
  have : IsIso (q ⁻¹ᵁ W).toSpecΓ := hqW.isoSpec.isIso_hom
  have : IsIso φ := by
    simp only [φ, CommMon.sectionsAlgHom_id]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (q.pushforwardStructureAlgebraSectionsRingEquiv W).bijective
  exact ⟨(q ⁻¹ᵁ W).toSpecΓ ≫ Spec.map φ, inferInstance,
    (CommMon.ι_relativeSpecLift (𝟙 A) (⟨W, hW⟩ : X.AffineZariskiSite)).trans
      (Category.assoc _ _ _).symm⟩

/-- Over an affine open `W ⊆ U` of `X`, the base change of the morphism
`T ⟶ Spec_X (q_* 𝒪_T) ×_X U` to the inverse image of `W` is an isomorphism. -/
private lemma isIso_pullbackSnd_lift_relativeSpecLift_id {X T : Scheme.{u}} (U : X.Opens)
    (r : T ⟶ U.toScheme) [IsAffineHom r]
    [(r ≫ U.ι).pushforwardStructureAlgebra.X.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
    (hWU : W ≤ U) :
    IsIso (pullback.snd
      (pullback.lift (CommMon.relativeSpecLift (𝟙 (r ≫ U.ι).pushforwardStructureAlgebra)) r
        (CommMon.relativeSpecLift_relativeSpecToBase _))
      (pullback.fst (r ≫ U.ι).pushforwardStructureAlgebra.relativeSpecToBase U.ι ⁻¹ᵁ
        ((r ≫ U.ι).pushforwardStructureAlgebra.relativeSpecToBase ⁻¹ᵁ W)).ι) := by
  set q := r ≫ U.ι
  set A := q.pushforwardStructureAlgebra
  set p := A.relativeSpecToBase
  set t : T ⟶ A.relativeSpec := CommMon.relativeSpecLift (𝟙 A)
  have ht : t ≫ p = q := CommMon.relativeSpecLift_relativeSpecToBase _
  set s : T ⟶ Limits.pullback p U.ι := pullback.lift t r ht
  set Oi := pullback.fst p U.ι ⁻¹ᵁ (p ⁻¹ᵁ W)
  -- On `q⁻¹ W`, `t` is an isomorphism `a` onto `Spec Γ(A, W)` followed by the chart `c` of
  -- `Spec_X A` over `W`, whose image `p⁻¹ W` is also the image of `Oi`; so `e₂` identifies the
  -- chart with `Oi`, and `k` maps `q⁻¹ W` isomorphically onto `Oi`.
  obtain ⟨a, ha, hι⟩ := exists_isIso_ι_relativeSpecLift_id U r hW hWU
  let Wa : X.AffineZariskiSite := ⟨W, hW⟩
  let c := A.relativeSpecCover.f Wa
  have hc : Set.range c = p ⁻¹' W := by
    rw [← Scheme.Hom.coe_opensRange, ← A.relativeSpecToBase_preimage Wa, Scheme.Hom.coe_preimage]
  let m := Oi.ι ≫ pullback.fst p U.ι
  have hm : Set.range m = p ⁻¹' W := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Hom.coe_preimage, Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range,
      Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.mpr (Set.preimage_mono hWU)
  let e₂ := IsOpenImmersion.isoOfRangeEq c m (hc.trans hm.symm)
  let k := a ≫ e₂.hom
  have hk₁ : k ≫ m = (q ⁻¹ᵁ W).ι ≫ t :=
    calc k ≫ m = a ≫ e₂.hom ≫ m := Category.assoc _ _ _
      _ = a ≫ c := congrArg (a ≫ ·) (IsOpenImmersion.isoOfRangeEq_hom_fac c m _)
      _ = _ := hι.symm
  have hk : k ≫ Oi.ι = (q ⁻¹ᵁ W).ι ≫ s := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, s, pullback.lift_fst] using hk₁
    · rw [← cancel_mono U.ι]
      have h := congrArg (· ≫ p) hk₁
      simp only [m, Category.assoc, ht] at h
      simpa only [Category.assoc, s, pullback.lift_snd, ← pullback.condition] using h
  -- The base change of `s` to `Oi` is `k`, up to the isomorphism `e₁` of its source with `q⁻¹ W`.
  have hr : Set.range (pullback.fst s Oi.ι) = Set.range (q ⁻¹ᵁ W).ι := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    ext v
    rw [Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage,
      SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply s, pullback.lift_fst,
      ← Scheme.Hom.comp_apply, ht]
  let e₁ := IsOpenImmersion.isoOfRangeEq (pullback.fst s Oi.ι) (q ⁻¹ᵁ W).ι hr
  have hsnd : pullback.snd s Oi.ι = e₁.hom ≫ k := by
    rw [← cancel_mono Oi.ι, Category.assoc, hk, ← pullback.condition,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  have : IsIso k := IsIso.comp_isIso' ha e₂.isIso_hom
  rw [hsnd]
  infer_instance

/-- Let `U` be an open subscheme of `X` and `r : T ⟶ U` an affine morphism whose composite
`q : T ⟶ X` with the inclusion of `U` has a quasi-coherent function algebra `A = q_* 𝒪_T`. Then
the relative spectrum `Spec_X A` restricts over `U` to `T`: the morphism from `T` to
`Spec_X A ×_X U` given by the canonical morphism `T ⟶ Spec_X A` over `X` and by `r` is an
isomorphism. -/
theorem isIso_pullbackLift_relativeSpecLift_id {X T : Scheme.{u}} (U : X.Opens)
    (r : T ⟶ U.toScheme) [IsAffineHom r]
    [(r ≫ U.ι).pushforwardStructureAlgebra.X.IsQuasicoherent] :
    IsIso (pullback.lift (CommMon.relativeSpecLift (𝟙 (r ≫ U.ι).pushforwardStructureAlgebra)) r
      (CommMon.relativeSpecLift_relativeSpecToBase _)) := by
  set p := (r ≫ U.ι).pushforwardStructureAlgebra.relativeSpecToBase
  -- Being an isomorphism is checked over the cover of the pullback by the inverse images of the
  -- affine opens `W ⊆ U` of `X`.
  let O : {W : X.Opens // IsAffineOpen W ∧ W ≤ U} → (Limits.pullback p U.ι).Opens :=
    fun W ↦ pullback.fst p U.ι ⁻¹ᵁ (p ⁻¹ᵁ W.val)
  have hO : iSup O = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    have hz : p (pullback.fst p U.ι z) ∈ U := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact (pullback.snd p U.ι z).property
    obtain ⟨W, hW, hzW, hWU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW, hWU⟩, hzW⟩
  exact (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    ((Limits.pullback p U.ι).openCoverOfIsOpenCover O hO)).mpr fun W ↦
      isIso_pullbackSnd_lift_relativeSpecLift_id U r W.property.1 W.property.2

end TauCeti.AlgebraicGeometry
