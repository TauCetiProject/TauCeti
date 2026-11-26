/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.FullyFaithful
public import TauCeti.AlgebraicGeometry.FiniteEtale.SpreadingOut
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.RelativeSpec.MorphismProperties
public import TauCeti.AlgebraicGeometry.RelativeSpec.Restrict
import TauCeti.AlgebraicGeometry.Scheme.Depth

/-!
# Extending finite étale covers across a closed subset of depth two where purity holds

Let `X` be a locally Noetherian scheme and `U` an open subscheme such that, at every point
`x ∉ U`, purity holds for the local ring `𝒪_{X,x}` (`TauCeti.IsLocalRing.PurityHolds`) and
`𝒪_{X,x}` has depth at least two. Then every finite étale cover of `U` is the restriction of a
finite étale cover of `X`
(`TauCeti.FiniteEtaleScheme.essSurj_pullback_ι_of_purityHolds_of_two_le_depth`). As restriction
is then also fully faithful (`TauCeti.FiniteEtaleScheme.fullyFaithfulPullbackιOfTwoLeDepthStalk`),
it is an equivalence of categories: in the language of SGA 2, the pair `(X, X ∖ U)` is pure. For
`X` Noetherian the depth hypothesis is not needed
(`TauCeti.FiniteEtaleScheme.essSurj_pullback_ι_of_purityHolds`, Stacks 0EY7), but a locally
Noetherian scheme admits no Noetherian induction, and the extensions obtained over its affine
opens are glued by their uniqueness, which is where the depth enters.

The extension of a finite étale cover `V` of `U` is built at once, without choices: it is the
relative spectrum over `X` of the function algebra `A = q_* 𝒪_V` of `q : V ⟶ U ⟶ X`, which is
quasi-coherent because `q` is quasi-compact and quasi-separated. Over `U` this relative spectrum is
`V` (`TauCeti.AlgebraicGeometry.isIso_pullbackLift_relativeSpecLift_id`). It is finite étale over
`X` because, over every affine open `W` of `X`, the sections `Γ(V, q⁻¹ W)` of `A` form a finite
étale `Γ(X, W)`-algebra (`TauCeti.FiniteEtaleScheme.finite_etale_app_of_purityHolds`). To see this,
write `W = Spec R`. By extension across points where purity holds on the Noetherian scheme
`Spec R`, the part of `V` over `W` is the restriction of `Spec C` for a finite étale `R`-algebra
`C`, and by the algebraic Hartogs principle, as the complement of `U` in `W` has depth at least
two, `C` is the ring of functions of this restriction.

## Main results

* `TauCeti.FiniteEtaleScheme.finite_etale_app_of_purityHolds`: over an affine open `W` with
  Noetherian ring of sections, the sections over `W` of a finite étale cover of `U` are finite
  étale over `Γ(X, W)` when purity and depth at least two hold at the points of `W ∖ U`.
* `TauCeti.FiniteEtaleScheme.essSurj_pullback_ι_of_purityHolds_of_two_le_depth`: restriction of
  finite étale schemes from a locally Noetherian `X` to `U` is essentially surjective.
* `TauCeti.FiniteEtaleScheme.isEquivalence_pullback_ι_of_purityHolds_of_two_le_depth`: it is an
  equivalence.

## References

* A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et
  globaux* (SGA 2), Exposé X, Définitions 3.1–3.2 and Proposition 3.3.
* [The Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7), extension of
  finite étale covers across points where purity holds, for Noetherian schemes.
* [The Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I), extension of
  sections across a closed subset of depth at least two.
* [The Stacks Project, Section 26.13](https://stacks.math.columbia.edu/tag/01LL), relative
  spectrum.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory

universe u

namespace TauCeti.FiniteEtaleScheme

/-- Let `R` be a Noetherian ring and `W` an open subset of `Spec R` such that, at every point
outside `W`, purity holds and the local ring has depth at least two. Then the global sections of
a finite étale cover of `W` form a finite étale `R`-algebra. -/
private theorem finite_etale_appTop_of_purityHolds {R : CommRingCat.{u}} [IsNoetherianRing R]
    (W : (Spec R).Opens)
    (hpur : ∀ x ∉ W, IsLocalRing.PurityHolds ((Spec R).presheaf.stalk x))
    (hdepth : ∀ p : PrimeSpectrum R, p ∉ W →
      2 ≤ IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal)))
    (V : FiniteEtaleScheme W.toScheme) :
    (V.obj.hom ≫ W.ι).appTop.hom.Finite ∧ (V.obj.hom ≫ W.ι).appTop.hom.Etale := by
  obtain ⟨a, b, hab, ha, hb⟩ :=
    TauCeti.AlgebraicGeometry.StructureSheaf.exists_isWeaklyRegular_basicOpen_le_of_two_le_depth
      (M := R) W fun p hp ↦ p.asIdeal.depth_localizedModule_self.trans_ge (hdepth p hp)
  -- By purity, `V` extends to `Spec C` for a finite étale `R`-algebra `C`.
  have := essSurj_pullback_ι_of_purityHolds W hpur
  let Y := (pullback W.ι).objPreimage V
  let C := (spec R).objPreimage Y
  let e : (pullback W.ι).obj ((spec R).obj C) ≅ V :=
    (pullback W.ι).mapIso ((spec R).objObjPreimageIso Y) ≪≫ (pullback W.ι).objObjPreimageIso V
  -- By the Hartogs principle, `C` is the ring of functions of the part of `Spec C` over `W`.
  have hH : IsIso (pullback.fst ((spec R).obj C).obj.hom W.ι).appTop := by
    rw [spec_obj_obj]
    exact TauCeti.AlgebraicGeometry.isIso_appTop_pullback_fst_ι_of_isWeaklyRegular C.unop.obj W
      hab ha hb
  -- `ψ` maps `V` to the extension, identifying it with the part of the extension over `W`.
  let ψ : V.obj.left ⟶ ((spec R).obj C).obj.left :=
    e.inv.hom.left ≫ pullback.fst ((spec R).obj C).obj.hom W.ι
  have hψ : ψ ≫ ((spec R).obj C).obj.hom = V.obj.hom ≫ W.ι :=
    (Category.assoc _ _ _).trans <| (congrArg (e.inv.hom.left ≫ ·) pullback.condition).trans <|
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ W.ι) (Over.w e.inv.hom))
  have : IsIso e.inv.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((ObjectProperty.ι _).map e.inv)))
  have : IsIso e.inv.hom.left.appTop := inferInstanceAs (IsIso (e.inv.hom.left.app ⊤))
  have : IsIso ψ.appTop := by
    have h : ψ.appTop = _ :=
      Scheme.Hom.comp_appTop e.inv.hom.left (pullback.fst ((spec R).obj C).obj.hom W.ι)
    rw [h]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hH ‹_›
  have : IsAffine ((spec R).obj C).obj.left := isAffine_of_isAffineHom ((spec R).obj C).obj.hom
  rw [← hψ, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.RespectsIso.cancel_right_isIso RingHom.finite_respectsIso,
    RingHom.RespectsIso.cancel_right_isIso RingHom.Etale.respectsIso]
  exact ⟨Scheme.Hom.finite_appTop _,
    HasRingHomProperty.iff_of_isAffine (P := @Etale) |>.mp inferInstance⟩

/-- Let `f : S ⟶ X` be an open immersion and `r : T ⟶ U` a morphism to an open `U` of `X`. The
base change of `r` along the restriction `f⁻¹ U ⟶ U` of `f` includes into `T` with image the part
of `T` over the image of `f`. -/
private lemma range_pullbackFst_resLE {X S T : Scheme.{u}} (U : X.Opens) (f : S ⟶ X)
    (r : T ⟶ U.toScheme) :
    Set.range (pullback.fst r (f.resLE U (f ⁻¹ᵁ U) le_rfl)) = (r ≫ U.ι) ⁻¹' Set.range f := by
  set g := f.resLE U (f ⁻¹ᵁ U) le_rfl
  have hg (o : (f ⁻¹ᵁ U).toScheme) : U.ι (g o) = f ((f ⁻¹ᵁ U).ι o) := by
    rw [← Scheme.Hom.comp_apply, f.resLE_comp_ι, Scheme.Hom.comp_apply]
  ext v
  rw [Scheme.Pullback.range_fst, Set.mem_preimage, Set.mem_preimage, Scheme.Hom.comp_apply]
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨o, ho⟩
    rw [← ho, hg]
    exact ⟨_, rfl⟩
  · obtain ⟨x, hx⟩ := hv
    have hxO : x ∈ f ⁻¹ᵁ U := by
      -- Membership in the preimage `f⁻¹ U` is membership of the image point in `U`.
      change f x ∈ U
      rw [hx]
      exact (r v).property
    exact ⟨(⟨x, hxO⟩ : (f ⁻¹ᵁ U).toScheme), U.ι.isOpenEmbedding.injective ((hg _).trans hx)⟩

/-- Let `U` be an open subscheme of `X`, and `W` an affine open of `X` whose ring of sections is
Noetherian, such that at every point of `W` outside `U` purity holds and the local ring has depth
at least two. Then for a finite étale cover `V` of `U`, the sections `Γ(V, q⁻¹ W)` of `V` over `W`,
where `q : V ⟶ U ⟶ X`, form a finite étale `Γ(X, W)`-algebra. -/
theorem finite_etale_app_of_purityHolds {X : Scheme.{u}} (U : X.Opens) {W : X.Opens}
    (hW : IsAffineOpen W) [IsNoetherianRing Γ(X, W)]
    (hpur : ∀ x ∈ W, x ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk x))
    (hdepth : ∀ x ∈ W, x ∉ U →
      2 ≤ IsLocalRing.depth (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))
    (V : FiniteEtaleScheme U.toScheme) :
    ((V.obj.hom ≫ U.ι).app W).hom.Finite ∧ ((V.obj.hom ≫ U.ι).app W).hom.Etale := by
  -- Work on the affine chart `f : Spec Γ(X, W) ⟶ X` with image `W`, over the preimage `O` of `U`,
  -- with the restriction `V'` of `V` to `O`.
  set f := hW.fromSpec
  set q := V.obj.hom ≫ U.ι
  let O := f ⁻¹ᵁ U
  let g : O.toScheme ⟶ U.toScheme := f.resLE U O le_rfl
  have : IsOpenImmersion g := by
    simp only [g, Scheme.Hom.resLE]
    infer_instance
  let V' := (pullback g).obj V
  have hloc := finite_etale_appTop_of_purityHolds O
    (fun x hx ↦ IsLocalRing.purityHolds_of_ringEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
        (hpur (f x) (hW.range_fromSpec.subset ⟨x, rfl⟩) hx))
    (fun p hp ↦ (f.depth_stalk_eq_depth_localization p).symm.trans_ge
      (hdepth (f p) (hW.range_fromSpec.subset ⟨p, rfl⟩) hp)) V'
  -- The inclusion `j` of `V'` into `V` has image the part `q⁻¹ W` of `V` over `W`.
  let j : V'.obj.left ⟶ V.obj.left := pullback.fst V.obj.hom g
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (pullback.fst V.obj.hom g))
  have hj : j ≫ q = (V'.obj.hom ≫ O.ι) ≫ f :=
    ((pullback.condition_assoc (f := V.obj.hom) (g := g) U.ι).trans
      (congrArg (pullback.snd V.obj.hom g ≫ ·) (f.resLE_comp_ι le_rfl))).trans
        (Category.assoc _ _ _).symm
  have hrange : j ''ᵁ ⊤ = q ⁻¹ᵁ W := by
    refine TopologicalSpace.Opens.ext ?_
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_preimage,
      ← hW.range_fromSpec]
    exact range_pullbackFst_resLE U f V.obj.hom
  -- The sections of `V` over `W` are the global sections of `V'`: both are identified with the
  -- sections of `V'` over the preimage of `W`, by the isomorphisms of sections `J` of `j` onto
  -- its image and `F` of `f` onto its image.
  have hjW : ⊤ ≤ j ⁻¹ᵁ (q ⁻¹ᵁ W) := hrange ▸ fun x _ ↦ ⟨x, trivial, rfl⟩
  have hfW : ⊤ ≤ f ⁻¹ᵁ W := fun x _ ↦ hW.range_fromSpec.subset ⟨x, rfl⟩
  have hJ : IsIso (j.appLE (q ⁻¹ᵁ W) ⊤ hjW) :=
    (Scheme.Hom.appLE_congr j _ hrange rfl fun φ ↦ IsIso φ).mp
      (by rw [← Scheme.Hom.appIso_hom']; infer_instance)
  have hF : IsIso (f.appLE W ⊤ hfW) :=
    (Scheme.Hom.appLE_congr f _ (f.image_top_eq_opensRange.trans hW.opensRange_fromSpec) rfl
      fun φ ↦ IsIso φ).mp (by rw [← Scheme.Hom.appIso_hom']; infer_instance)
  have key : q.app W ≫ j.appLE (q ⁻¹ᵁ W) ⊤ hjW =
      f.appLE W ⊤ hfW ≫ (V'.obj.hom ≫ O.ι).appTop :=
    calc q.app W ≫ j.appLE (q ⁻¹ᵁ W) ⊤ hjW = (j ≫ q).appLE W ⊤ hjW := by
          rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]
      _ = ((V'.obj.hom ≫ O.ι) ≫ f).appLE W ⊤ (hj ▸ hjW) := Scheme.Hom.congr_appLE _ hj _ _ _ _
      _ = f.appLE W ⊤ hfW ≫ (V'.obj.hom ≫ O.ι).appLE ⊤ ⊤ (Scheme.Hom.preimage_top _).ge :=
          (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
      _ = _ := congrArg (_ ≫ ·) (Scheme.Hom.appLE_eq_app _ (U := ⊤))
  have hfin := congrArg (fun φ ↦ φ.hom.Finite) key
  have het := congrArg (fun φ ↦ φ.hom.Etale) key
  simp only [CommRingCat.hom_comp] at hfin het
  rw [RingHom.RespectsIso.cancel_right_isIso RingHom.finite_respectsIso,
    RingHom.RespectsIso.cancel_left_isIso RingHom.finite_respectsIso] at hfin
  rw [RingHom.RespectsIso.cancel_right_isIso RingHom.Etale.respectsIso,
    RingHom.RespectsIso.cancel_left_isIso RingHom.Etale.respectsIso] at het
  exact ⟨hfin.mpr hloc.1, het.mpr hloc.2⟩

/-- **Extension of finite étale covers across a closed subset of depth two where purity holds.**
Let `X` be a locally Noetherian scheme and `U` an open subscheme such that, at every point
`x ∉ U`, purity holds for `𝒪_{X,x}` and `𝒪_{X,x}` has depth at least two. Then every finite étale
cover of `U` is the restriction of a finite étale cover of `X`. -/
theorem essSurj_pullback_ι_of_purityHolds_of_two_le_depth {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens)
    (hpur : ∀ x : X, x ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk x))
    (hdepth : ∀ x : X, x ∉ U →
      2 ≤ IsLocalRing.depth (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) :
    (pullback U.ι).EssSurj := by
  refine ⟨fun V ↦ ?_⟩
  let q := V.obj.hom ≫ U.ι
  let A := q.pushforwardStructureAlgebra
  have : A.X.IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pushforward q).obj (𝟙_ V.obj.left.Modules)).IsQuasicoherent
  -- Over an affine open `W`, the sections of `A` are those of `V` over `q⁻¹ W`.
  have hA {W : X.Opens} (hW : IsAffineOpen W) :
      (algebraMap Γ(X, W) Γ(A.X, W)).Finite ∧ (algebraMap Γ(X, W) Γ(A.X, W)).Etale := by
    have h : algebraMap Γ(X, W) Γ(A.X, W) =
        (q.pushforwardStructureAlgebraSectionsRingEquiv W).symm.toRingHom.comp (q.app W).hom := by
      ext r
      exact (Scheme.Hom.pushforwardStructureAlgebra_algebraMap q W r).trans
        (q.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply W _).symm
    have := IsLocallyNoetherian.component_noetherian (X := X) ⟨W, hW⟩
    obtain ⟨hfin, het⟩ := finite_etale_app_of_purityHolds U hW (fun x _ ↦ hpur x)
      (fun x _ ↦ hdepth x) V
    rw [h]
    exact ⟨RingHom.finite_respectsIso.left _ _ hfin, RingHom.Etale.respectsIso.left _ _ het⟩
  have : IsFinite A.relativeSpecToBase :=
    A.relativeSpec_finite_iff.mpr fun W hW ↦ RingHom.finite_algebraMap.mp (hA hW).1
  have : Etale A.relativeSpecToBase :=
    A.relativeSpec_etale_iff.mpr fun W hW ↦ RingHom.etale_algebraMap.mp (hA hW).2
  -- Over `U`, the relative spectrum of `A` is `V` itself.
  let s := pullback.lift _ V.obj.hom (CommMon.relativeSpecLift_relativeSpecToBase (𝟙 A))
  have : IsIso s := AlgebraicGeometry.isIso_pullbackLift_relativeSpecLift_id U V.obj.hom
  have hs : inv s ≫ V.obj.hom = pullback.snd A.relativeSpecToBase U.ι :=
    (IsIso.inv_comp_eq s).mpr (pullback.lift_snd _ _ _).symm
  exact ⟨⟨Over.mk A.relativeSpecToBase, (finiteEtaleSchemeProperty_iff _).mpr ⟨‹_›, ‹_›⟩⟩,
    ⟨ObjectProperty.isoMk _ (Over.isoMk (asIso s).symm hs)⟩⟩

/-- Let `X` be a locally Noetherian scheme and `U` an open subscheme such that, at every point
`x ∉ U`, purity holds for `𝒪_{X,x}` and `𝒪_{X,x}` has depth at least two. Then restriction of
finite étale schemes from `X` to `U` is an equivalence of categories. -/
theorem isEquivalence_pullback_ι_of_purityHolds_of_two_le_depth {X : Scheme.{u}}
    [IsLocallyNoetherian X] (U : X.Opens)
    (hpur : ∀ x : X, x ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk x))
    (hdepth : ∀ x : X, x ∉ U →
      2 ≤ IsLocalRing.depth (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) :
    (pullback U.ι).IsEquivalence :=
  have := essSurj_pullback_ι_of_purityHolds_of_two_le_depth U hpur hdepth
  have := (fullyFaithfulPullbackιOfTwoLeDepthStalk U hdepth).full
  have := (fullyFaithfulPullbackιOfTwoLeDepthStalk U hdepth).faithful
  { }

end TauCeti.FiniteEtaleScheme
