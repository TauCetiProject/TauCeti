/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Gluing
public import TauCeti.AlgebraicGeometry.Limits.Finite.Presentation
public import TauCeti.AlgebraicGeometry.Limits.Affine.Localization
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
import TauCeti.Topology.Sober
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.RingTheory.Etale.NoetherianDescent
import TauCeti.RingTheory.Localization.FinitePresentation

/-!
# Spreading out finite étale covers, and extension across points where purity holds

Let `W` be a retrocompact open of a scheme `X` and `x` a point of `X`. A finite étale cover of `W`
and a finite étale cover of the local scheme `Spec 𝒪_{X,x}` that agree over
`W ×_X Spec 𝒪_{X,x}` glue to a finite étale cover of an open neighbourhood of `x` containing `W`
(`TauCeti.FiniteEtaleScheme.exists_pullback_iso_of_isPullback_fromSpecStalk`; Stacks, Lemma
32.20.3 (0BQ5), existence, for finite étale covers).

The proof presents `Spec 𝒪_{X,x}` as the cofiltered limit of the spectra of the principal
localizations `Γ(A)[1/f]`, `f(x) ≠ 0`, of an affine open neighbourhood `A` of `x`
(`Submonoid.localizationAwaySpecConeIsLimit`), since `𝒪_{X,x}` is the filtered colimit of these
rings. A finite étale cover of `Spec 𝒪_{X,x}` descends to one of these principal opens `D(f)`, as
finite étale algebras descend through filtered colimits of rings
(`TauCeti.Algebra.exists_etale_finite_algEquiv_tensorProduct_of_factorization`). Isomorphisms of
finite étale covers descend along such limits
(`TauCeti.FiniteEtaleScheme.exists_nonempty_iso_pullback_of_isLimit`, from the descent of
isomorphisms of finitely presented schemes,
`CategoryTheory.Limits.IsLimit.exists_iso_pullback_of_iso`, Stacks 01ZM and 081E), which applies
to the base change of the limit to the quasi-compact open `W` (`IsLimit.pullbackOver`). So the two
covers agree over `W ∩ D(f')` for a smaller principal open `D(f')` of `x`, and they glue along it
(`TauCeti.FiniteEtaleScheme.exists_pullback_iso_of_isPullback`).

With purity, this extends finite étale covers across points of a Noetherian scheme
(`TauCeti.FiniteEtaleScheme.essSurj_pullback_ι_of_purityHolds`; Stacks, Lemma 58.21.6 (0EY7)).
Among the opens containing `U` to which a cover of `U` extends, choose a maximal one `W`. If
`W ≠ X`, the generic point `x` of an irreducible component of `X ∖ W` has all its proper
generizations in `W`, so the preimage of `W` in `Spec 𝒪_{X,x}` is the punctured spectrum. Purity
for `𝒪_{X,x}` extends the cover over `Spec 𝒪_{X,x}`, and spreading out extends it to an open
strictly larger than `W`, a contradiction.

## Main results

* `TauCeti.FiniteEtaleScheme.exists_nonempty_iso_pullback_of_isLimit`: finite étale covers of a
  member of a cofiltered diagram of qcqs schemes with affine transition maps that are isomorphic
  over the limit are isomorphic at a finite stage.
* `TauCeti.FiniteEtaleScheme.exists_pullback_localizationAwaySpecCone_iso`: a finite étale cover
  of `Spec (M⁻¹R)` is the base change of one over some principal localization `Spec R[1/∏ s]`.
* `TauCeti.FiniteEtaleScheme.exists_pullback_iso_of_isPullback_fromSpecStalk`: spreading out a
  finite étale cover from `Spec 𝒪_{X,x}` to an open neighbourhood of `x`.
* `TauCeti.FiniteEtaleScheme.essSurj_pullback_ι_of_purityHolds`: on a Noetherian scheme, if purity
  holds for the local rings at all points outside an open `U`, every finite étale cover of `U`
  extends to `X`.

## References

* [The Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5) and
  [Lemma 32.20.4](https://stacks.math.columbia.edu/tag/0EY3), spreading out from a local scheme.
* [The Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7), extension of
  finite étale covers across points where purity holds.
* [The Stacks Project, Lemma 32.10.1](https://stacks.math.columbia.edu/tag/01ZM) and
  [Lemma 32.8.11](https://stacks.math.columbia.edu/tag/081E), descent of morphisms and
  isomorphisms along limits.
-/
public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section Limit

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}

/-- **Isomorphisms of finite étale covers descend along cofiltered limits.** Let `S = lim Dⱼ` be
a cofiltered limit of quasi-compact quasi-separated schemes with affine transition maps. If two
finite étale covers `E` and `F` of a member `Dᵢ` become isomorphic after base change to `S`, they
are already isomorphic after base change to `Dⱼ` for some `j ⟶ i`. -/
theorem exists_nonempty_iso_pullback_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c) {i : I}
    {E F : FiniteEtaleScheme (D.obj i)}
    (e : (pullback (c.π.app i)).obj E ≅ (pullback (c.π.app i)).obj F) :
    ∃ (j : I) (a : j ⟶ i), Nonempty ((pullback (D.map a)).obj E ≅ (pullback (D.map a)).obj F) := by
  -- The isomorphism `e` over the limit, as a morphism `S ×_{Dᵢ} E ⟶ S ×_{Dᵢ} F` over `S`.
  let eL : Limits.pullback E.obj.hom (c.π.app i) ≅ Limits.pullback F.obj.hom (c.π.app i) :=
    (Over.forget _).mapIso ((ObjectProperty.ι _).mapIso e)
  have heL : eL.hom ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ := Over.w e.hom.hom
  let e' : Limits.pullback (c.π.app i) E.obj.hom ≅ Limits.pullback (c.π.app i) F.obj.hom :=
    pullbackSymmetry _ _ ≪≫ eL ≪≫ pullbackSymmetry _ _
  have he' : e'.hom ≫ Limits.pullback.fst _ F.obj.hom = Limits.pullback.fst _ _ := by
    simp only [e', Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
    rw [heL, pullbackSymmetry_hom_comp_snd]
  -- It is the base change of an isomorphism over some `Dⱼ`.
  obtain ⟨j, a, e₀, he₀, -⟩ := hc.exists_iso_pullback_of_iso e' he'
  let Φ : Limits.pullback E.obj.hom (D.map a) ≅ Limits.pullback F.obj.hom (D.map a) :=
    pullbackSymmetry _ _ ≪≫ e₀ ≪≫ pullbackSymmetry _ _
  have hΦ : Φ.hom ≫ Limits.pullback.snd F.obj.hom _ = Limits.pullback.snd E.obj.hom (D.map a) := by
    simp [Φ, he₀]
  exact ⟨j, a, ⟨ObjectProperty.isoMk _ (Over.isoMk Φ hΦ)⟩⟩

end Limit

section Localization

variable {R : Type u} [CommRing R] (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S]
  [IsLocalization M S]

/-- **Finite étale covers descend to a principal localization.** Every finite étale scheme over
`Spec (M⁻¹R)` is the base change of a finite étale scheme over the spectrum of a principal
localization `R[1/∏ s]`, a member of the limit presentation
`Submonoid.localizationAwaySpecConeIsLimit`. -/
theorem exists_pullback_localizationAwaySpecCone_iso
    (Y : FiniteEtaleScheme (Spec (.of S))) :
    ∃ (s : (Finset M)ᵒᵖ) (Y₀ : FiniteEtaleScheme (M.localizationAwaySpecDiagram.obj s)),
      Nonempty ((pullback ((M.localizationAwaySpecCone S).π.app s)).obj Y₀ ≅ Y) := by
  let F := M.localizationAwayDiagram ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}
  let ψ (s : Finset M) : F.obj s →+* S := ((M.localizationAwayRingCocone S).ι.app s).hom
  -- Maps from rings of finite presentation over `ℤ` to `M⁻¹R` factor through a stage.
  have hfactor (P : Type u) [CommRing P] [Algebra.FinitePresentation ℤ P] (g : P →+* S) :
      ∃ s, ∃ φ : P →+* F.obj s, (ψ s).comp φ = g := by
    -- Lift the initial ring to the universe of the localization diagram.
    let f := (algebraMap ℤ P).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
    have hf : f.FinitePresentation :=
      (RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
        (.of_bijective ULift.ringEquiv.bijective)
    obtain ⟨s, φ, -, hφ⟩ := f.exists_factorization_localizationAwayRingCocone hf M
      ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom) g (by ext; simp [f])
    exact ⟨s, φ, hφ⟩
  -- `Y` is the spectrum of a finite étale `M⁻¹R`-algebra `B`, which descends to a stage.
  have := essSurj_spec (.of S)
  obtain ⟨B, ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage (spec (.of S)) Y
  obtain ⟨s, B₀, _, _, _, _, ⟨e⟩⟩ :=
    TauCeti.Algebra.exists_etale_finite_algEquiv_tensorProduct_of_factorization
      (fun s ↦ F.obj s) ψ hfactor B.unop.obj
  let := (ψ s).toAlgebra
  refine ⟨Opposite.op s, (spec (F.obj s)).obj (Opposite.op (CommAlgCat.FiniteEtale.of _ B₀)),
    ⟨?_ ≪≫ eB⟩⟩
  apply ObjectProperty.isoMk
  -- `Over.pullback` bundles `pullback.snd` and `algSpec` bundles `Spec.algebraMap`, so the objects
  -- are those of `pullbackSpecIsoOfAlgEquiv`, as in `essSurj_pullback_of_essSurj_baseChange`.
  rw [pullback_obj_obj, spec_obj_obj, spec_obj_obj]
  exact TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv (F.obj s) B₀ S B.unop.obj e.symm

end Localization

section Glue

/-- Finite étale covers of an open `W` of `X` and of an open subscheme `G : Z ⟶ X` which agree
over their intersection glue to a finite étale cover of `W ∪ G(Z)`. -/
private lemma exists_glue {X Z P : Scheme.{u}} {W : X.Opens} (G : Z ⟶ X) [IsOpenImmersion G]
    {i₁ : P ⟶ W} {i₂ : P ⟶ Z} (h : IsPullback i₁ i₂ W.ι G) (V : FiniteEtaleScheme W)
    (Y : FiniteEtaleScheme Z) (e : (pullback i₁).obj V ≅ (pullback i₂).obj Y) :
    ∃ V' : FiniteEtaleScheme (W ⊔ G.opensRange : X.Opens),
      Nonempty ((pullback (X.homOfLE le_sup_left)).obj V' ≅ V) ∧
      Nonempty ((pullback (G.isoOpensRange.hom ≫ X.homOfLE le_sup_right)).obj V' ≅ Y) := by
  set W' : X.Opens := W ⊔ G.opensRange
  let j₂ : Z ⟶ W' := G.isoOpensRange.hom ≫ X.homOfLE le_sup_right
  have hj₂ : j₂ ≫ W'.ι = G := by simp [j₂]
  -- The overlap square, which is cartesian over `X`, stays cartesian over the open `W'`.
  have hsq : IsPullback i₁ i₂ (X.homOfLE le_sup_left) j₂ := by
    -- Paste with the square `Z = Z ×_X W'`, which is cartesian since `W'.ι` is a monomorphism.
    refine IsPullback.of_bot (v₂₁ := 𝟙 Z) (v₂₂ := W'.ι) (h₃₁ := G) ?_
      (by rw [← cancel_mono W'.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hj₂]; exact h.w)
      (IsPullback.of_vert_isIso_mono ⟨by simp [hj₂]⟩)
    rwa [Category.comp_id, Scheme.homOfLE_ι]
  -- A point of `W'` lies in `W` or is the image of a point of `Z`.
  have hcover : (X.homOfLE (le_sup_left : W ≤ W')).opensRange ⊔ j₂.opensRange = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [Scheme.opensRange_homOfLE]
    refine (TopologicalSpace.Opens.mem_sup.mp y.property).imp id fun ⟨z, hz⟩ ↦ ⟨z, ?_⟩
    exact W'.ι.isOpenEmbedding.injective
      (by rw [← Scheme.Hom.comp_apply, hj₂, hz]; exact (W'.ι_apply y).symm)
  have : IsOpenImmersion i₁ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance
  have : IsOpenImmersion i₂ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) h inferInstance
  obtain ⟨V', e₁, e₂, -⟩ := exists_pullback_iso_of_isPullback hsq hcover e
  exact ⟨V', ⟨e₁⟩, ⟨e₂⟩⟩

/-- Let `S = lim Dⱼ` be a cofiltered limit as in `exists_nonempty_iso_pullback_of_isLimit`, with
a morphism `g : Dᵢ ⟶ X`. If a finite étale cover `V` of a retrocompact open `W` of `X` and a
finite étale cover `Y₀` of `Dᵢ` agree over `W ×_X S`, they already agree over
`Dₖ ×_{Dᵢ} (W ×_X Dᵢ)` for some `k ⟶ i`. -/
private lemma exists_iso_stage {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D}
    (hc : IsLimit c) {X : Scheme.{u}} {W : X.Opens} [QuasiCompact W.ι] {i : I}
    (g : D.obj i ⟶ X) {T : Scheme.{u}} {a : T ⟶ W} {b : T ⟶ c.pt}
    (h : IsPullback a b W.ι (c.π.app i ≫ g)) (V : FiniteEtaleScheme W)
    (Y₀ : FiniteEtaleScheme (D.obj i))
    (e : (pullback b).obj ((pullback (c.π.app i)).obj Y₀) ≅ (pullback a).obj V) :
    ∃ (k : I) (hk : k ⟶ i), Nonempty ((pullback
      (Limits.pullback.snd (D.map hk) (Limits.pullback.snd W.ι g) ≫
        Limits.pullback.fst W.ι g)).obj V ≅
      (pullback (Limits.pullback.fst (D.map hk) (Limits.pullback.snd W.ι g))).obj
        ((pullback (D.map hk)).obj Y₀)) := by
  -- Base change the diagram along `t : W ×_X Dᵢ ⟶ Dᵢ`; its limit is `S ×_{Dᵢ} (W ×_X Dᵢ)`.
  let t := Limits.pullback.snd W.ι g
  let i₀ : Over i := Over.mk (𝟙 i)
  let P := (c.pullbackOver t).π.app i₀
  -- Over `S ×_{Dᵢ} (W ×_X Dᵢ)`, which maps to `T = W ×_X S`, the two covers agree.
  let κ : Limits.pullback (c.π.app i) t ⟶ T :=
    h.lift (Limits.pullback.snd (c.π.app i) t ≫ Limits.pullback.fst W.ι g)
      (Limits.pullback.fst (c.π.app i) t) (by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
          ← Limits.pullback.condition, Category.assoc])
  have hPa : P ≫ Limits.pullback.snd (D.map (𝟙 i)) t ≫ Limits.pullback.fst W.ι g = κ ≫ a := by
    rw [h.lift_fst, ← Category.assoc]
    exact congrArg (· ≫ _) (Cone.pullbackOver_π_app_snd t c i₀)
  have hPb : P ≫ Limits.pullback.fst (D.map (𝟙 i)) t = κ ≫ b ≫ c.π.app i := by
    rw [h.lift_snd_assoc]
    exact Cone.pullbackOver_π_app_fst t c i₀
  let eLim : (pullback P).obj ((pullback (Limits.pullback.snd (D.map (𝟙 i)) t ≫
        Limits.pullback.fst W.ι g)).obj V) ≅
      (pullback P).obj ((pullback (Limits.pullback.fst (D.map (𝟙 i)) t)).obj Y₀) :=
    (pullbackComp _ _).symm.app V ≪≫ eqToIso (by rw [hPa]) ≪≫ (pullbackComp κ a).app V ≪≫
      (pullback κ).mapIso e.symm ≪≫ (pullbackComp κ b).symm.app _ ≪≫
      (pullbackComp (κ ≫ b) (c.π.app i)).symm.app Y₀ ≪≫
      eqToIso (by rw [Category.assoc, hPb]) ≪≫ (pullbackComp _ _).app Y₀
  -- The isomorphism descends to a stage `Dₖ ×_{Dᵢ} (W ×_X Dᵢ)`.
  obtain ⟨k, hk, ⟨eA⟩⟩ := exists_nonempty_iso_pullback_of_isLimit (hc.pullbackOver t) eLim
  have hkl : hk.left = k.hom := by simpa [i₀] using Over.w hk
  have hs : (D.pullbackOver t).map hk ≫ Limits.pullback.snd (D.map (𝟙 i)) t =
      Limits.pullback.snd (D.map k.hom) t := D.pullbackOver_map_snd t hk
  have hf : (D.pullbackOver t).map hk ≫ Limits.pullback.fst (D.map (𝟙 i)) t =
      Limits.pullback.fst (D.map k.hom) t ≫ D.map k.hom :=
    (D.pullbackOver_map_fst t hk).trans (by rw [hkl])
  exact ⟨k.left, k.hom, ⟨eqToIso (by rw [reassoc_of% hs]) ≪≫
    (pullbackComp _ _).app V ≪≫ eA ≪≫ (pullbackComp _ _).symm.app Y₀ ≪≫
    eqToIso (by rw [hf]) ≪≫ (pullbackComp _ _).app Y₀⟩⟩

end Glue

/-- **Spreading out a finite étale cover from the local scheme at a point.** Let `W` be a
retrocompact open of a scheme `X`, `x` a point of `X`, and `T = W ×_X Spec 𝒪_{X,x}`. If a finite
étale cover `V` of `W` and a finite étale cover `Y` of `Spec 𝒪_{X,x}` agree over `T`, they glue
to a finite étale cover `V'` of an open `W' ⊇ W` containing `x`: the restriction of `V'` to `W`
is `V`, and its pullback to `Spec 𝒪_{X,x}` is `Y`.

This is the existence part of Stacks, Lemma 32.20.3 (0BQ5), for finite étale covers; that the
glued scheme is again finite étale is the corresponding case of Lemma 32.20.4 (0EY3). -/
@[stacks 0BQ5 "Existence of the glued scheme, for finite étale covers."]
theorem exists_pullback_iso_of_isPullback_fromSpecStalk {X : Scheme.{u}} {W : X.Opens}
    [QuasiCompact W.ι] {x : X} {T : Scheme.{u}} {a : T ⟶ W}
    {b : T ⟶ Spec (X.presheaf.stalk x)} (h : IsPullback a b W.ι (X.fromSpecStalk x))
    (V : FiniteEtaleScheme W) (Y : FiniteEtaleScheme (Spec (X.presheaf.stalk x)))
    (e : (pullback b).obj Y ≅ (pullback a).obj V) :
    ∃ (W' : X.Opens) (hW : W ≤ W') (hx : x ∈ W') (V' : FiniteEtaleScheme W'),
      Nonempty ((pullback (X.homOfLE hW)).obj V' ≅ V) ∧
      Nonempty ((pullback (W'.fromSpecStalkOfMem x hx)).obj V' ≅ Y) := by
  -- Present `Spec 𝒪_{X,x}` as the limit of the principal open neighbourhoods `D(f)` of `x` in
  -- an affine open `A`, and descend `Y` to one of them.
  obtain ⟨A, hA, hxA, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  have hA : IsAffineOpen A := hA
  let M := (hA.primeIdealOf ⟨x, hxA⟩).asIdeal.primeCompl
  let alg : Algebra Γ(X, A) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxA⟩
  have loc : IsLocalization M (X.presheaf.stalk x) := hA.isLocalization_stalk ⟨x, hxA⟩
  -- The algebra structure of the stalk over `Γ(X, A)` is given by the germ map.
  have halg : CommRingCat.ofHom (algebraMap Γ(X, A) (X.presheaf.stalk x)) =
      X.presheaf.germ A x hxA := by
    rw [TopCat.Presheaf.stalk_open_algebraMap X.presheaf ⟨x, hxA⟩, CommRingCat.ofHom_hom]
  let D := M.localizationAwaySpecDiagram
  let c := M.localizationAwaySpecCone (X.presheaf.stalk x)
  have hc : IsLimit c := M.localizationAwaySpecConeIsLimit (X.presheaf.stalk x)
  let g (s : (Finset M)ᵒᵖ) : D.obj s ⟶ X := M.localizationAwaySpecToSpec s ≫ hA.fromSpec
  have hDg {s s' : (Finset M)ᵒᵖ} (f : s ⟶ s') : D.map f ≫ g s' = g s := by
    exact M.localizationAwaySpecDiagram_map_localizationAwaySpecToSpec_assoc f _
  have hcg (s : (Finset M)ᵒᵖ) : c.π.app s ≫ g s = X.fromSpecStalk x := by
    rw [M.localizationAwaySpecCone_π_app_localizationAwaySpecToSpec_assoc,
      ← hA.fromSpecStalk_eq_fromSpecStalk hxA, IsAffineOpen.fromSpecStalk, halg]
  obtain ⟨s₀, Y₀, ⟨ε⟩⟩ :=
    @exists_pullback_localizationAwaySpecCone_iso _ _ M (X.presheaf.stalk x) _ alg loc Y
  -- `V` and `Y₀` agree over a principal neighbourhood `D(f)` of `x`, where they glue.
  rw [← hcg s₀] at h
  obtain ⟨k, hk, ⟨eglue⟩⟩ := exists_iso_stage hc (g s₀) h V Y₀ ((pullback b).mapIso ε ≪≫ e)
  have hsq : IsPullback (Limits.pullback.snd (D.map hk) (Limits.pullback.snd W.ι (g s₀)) ≫
      Limits.pullback.fst W.ι (g s₀))
      (Limits.pullback.fst (D.map hk) (Limits.pullback.snd W.ι (g s₀))) W.ι (g k) := by
    rw [← hDg hk]
    exact (IsPullback.of_hasPullback (D.map hk) _).flip.paste_horiz
      (IsPullback.of_hasPullback W.ι (g s₀))
  obtain ⟨V', ⟨e₁⟩, ⟨e₂⟩⟩ := exists_glue (g k) hsq V _ eglue
  have hx : x ∈ W ⊔ (g k).opensRange := by
    have h₁ : (c.π.app k ≫ g k) (IsLocalRing.closedPoint (X.presheaf.stalk x)) = x := by
      rw [hcg k]; exact Scheme.fromSpecStalk_closedPoint
    exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr (Scheme.Hom.mem_opensRange.mpr
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans h₁⟩))
  refine ⟨_, le_sup_left, hx, V', ⟨e₁⟩, ?_⟩
  -- The pullback of the glued cover to `Spec 𝒪_{X,x}` factors through `D(f')`.
  have hfac : (W ⊔ (g k).opensRange).fromSpecStalkOfMem x hx =
      c.π.app k ≫ (g k).isoOpensRange.hom ≫ X.homOfLE le_sup_right := by
    rw [← cancel_mono (W ⊔ (g k).opensRange).ι, Scheme.Opens.fromSpecStalkOfMem_ι]
    simp [hcg]
  exact ⟨eqToIso (by rw [hfac]) ≪≫ (pullbackComp _ _).app V' ≪≫ (pullback _).mapIso e₂ ≪≫
    (pullbackComp _ _).symm.app Y₀ ≪≫ eqToIso (by rw [c.w hk]) ≪≫ ε⟩

section Purity

/-- Let `x ∉ W` be a point whose proper generizations all lie in the retrocompact open `W`, and
suppose that purity holds for `𝒪_{X,x}`. Then every finite étale cover of `W` extends to a
finite étale cover of an open `W' ⊇ W` containing `x`. -/
private lemma exists_extension_of_purityHolds {X : Scheme.{u}} {W : X.Opens}
    [QuasiCompact W.ι] {x : X} (hxW : x ∉ W) (hgen : ∀ y : X, y ∉ W → y ⤳ x → y = x)
    (hx : IsLocalRing.PurityHolds (X.presheaf.stalk x)) (V : FiniteEtaleScheme W) :
    ∃ (W' : X.Opens) (hW : W ≤ W'), x ∈ W' ∧ ∃ V' : FiniteEtaleScheme W',
      Nonempty ((pullback (X.homOfLE hW)).obj V' ≅ V) := by
  -- The preimage of `W` in `Spec 𝒪_{X,x}` is the punctured spectrum.
  have heq : X.fromSpecStalk x ⁻¹ᵁ W = IsLocalRing.puncturedSpectrum (X.presheaf.stalk x) := by
    ext p
    rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage]
    refine Iff.trans ?_ (IsLocalRing.mem_puncturedSpectrum_iff _ p).symm
    constructor
    · rintro hp rfl
      exact hxW (by rwa [Scheme.fromSpecStalk_closedPoint] at hp)
    · intro hp
      by_contra hpW
      have hsp : X.fromSpecStalk x p ⤳ x := by
        have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      refine hp ((X.fromSpecStalk x).isEmbedding.injective ?_)
      rw [hgen _ hpW hsp, Scheme.fromSpecStalk_closedPoint]
  have hsq : IsPullback ((Scheme.isoOfEq _ heq).inv ≫ X.fromSpecStalk x ∣_ W)
      (IsLocalRing.puncturedSpectrum (X.presheaf.stalk x)).ι W.ι (X.fromSpecStalk x) :=
    (isPullback_morphismRestrict (X.fromSpecStalk x) W).of_iso (Scheme.isoOfEq _ heq)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id]; exact (Scheme.isoOfEq_hom_ι _ heq).symm)
      (by simp) (by simp)
  -- Purity extends the restriction of `V` to the punctured spectrum, and the extension spreads.
  obtain ⟨Y, ⟨eY⟩⟩ := ((IsLocalRing.purityHolds_iff_essSurj _).mp hx).mem_essImage
    ((pullback ((Scheme.isoOfEq _ heq).inv ≫ X.fromSpecStalk x ∣_ W)).obj V)
  obtain ⟨W', hW, hxW', V', e₁, -⟩ :=
    exists_pullback_iso_of_isPullback_fromSpecStalk hsq V Y eY
  exact ⟨W', hW, hxW', V', e₁⟩

/-- **Extension of finite étale covers across points where purity holds.** Let `U` be an open of
a Noetherian scheme `X` such that purity holds for the local ring of `X` at every point outside
`U`. Then every finite étale cover of `U` is the restriction of a finite étale cover of `X`. -/
@[stacks 0EY7]
theorem essSurj_pullback_ι_of_purityHolds {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens)
    (h : ∀ x : X, x ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk x)) :
    (pullback U.ι).EssSurj := by
  refine ⟨fun V ↦ ?_⟩
  -- Among the opens containing `U` to which `V` extends, choose a maximal one by Noetherianity.
  let 𝒮 : Set X.Opens := {W | ∃ (hW : U ≤ W) (V' : FiniteEtaleScheme W),
    Nonempty ((pullback (X.homOfLE hW)).obj V' ≅ V)}
  have hU : U ∈ 𝒮 := ⟨le_rfl, V, ⟨eqToIso (by rw [Scheme.homOfLE_rfl]) ≪≫ pullbackId.app V⟩⟩
  obtain ⟨W₀, ⟨hUW₀, V₀, ⟨e₀⟩⟩, hmax⟩ := wellFounded_gt.has_min 𝒮 ⟨U, hU⟩
  -- If the maximal open were not everything, the cover would extend across a further point.
  obtain rfl : W₀ = ⊤ := by
    by_contra hne
    obtain ⟨y, hy⟩ : ∃ y : X, y ∉ W₀ := by
      by_contra! h
      exact hne (eq_top_iff.mpr fun y _ ↦ h y)
    obtain ⟨x, hxW, -, hgen⟩ := W₀.isOpen.isClosed_compl.exists_maximal_specializes hy
    obtain ⟨W', hW, hxW', V', ⟨e'⟩⟩ :=
      exists_extension_of_purityHolds hxW hgen (h x fun hxU ↦ hxW (hUW₀ hxU)) V₀
    refine hmax W' ⟨hUW₀.trans hW, V',
      ⟨eqToIso (by rw [← Scheme.homOfLE_homOfLE X hUW₀ hW]) ≪≫ (pullbackComp _ _).app V' ≪≫
        (pullback _).mapIso e' ≪≫ e₀⟩⟩
      (lt_of_le_of_ne hW fun hWW' ↦ hxW (hWW' ▸ hxW'))
  have hι : U.ι ≫ X.topIso.inv = X.homOfLE hUW₀ := by
    rw [← cancel_mono X.topIso.hom]; simp
  exact ⟨(pullback X.topIso.inv).obj V₀,
    ⟨(pullbackComp _ _).symm.app V₀ ≪≫ eqToIso (by rw [hι]) ≪≫ e₀⟩⟩

end Purity

end TauCeti.FiniteEtaleScheme
