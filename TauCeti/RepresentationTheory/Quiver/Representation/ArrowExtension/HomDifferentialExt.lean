/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.ArrowExtension.Classification
public import TauCeti.Algebra.Homology.Ext.Realization
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Arrow families and extension classes of quiver representations

The comparison `homDifferentialCokerEquivExt` sends an arrow family to its upper triangular
extension class in `Ext¹(M,N)`. It uses `QuiverRep.exists_arrowExtension_hom_fixing_ends_iff`
for injectivity and `ShortComplex.ShortExact.exists_extClass_eq` for surjectivity.

See W. Crawley-Boevey, *Lectures on Representations of Quivers*, §1, consequence (3),
and H. Derksen and J. Weyman, *An Introduction to Quiver Representations*, Chapter 1.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v w t e

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable {M N M' N' : QuiverRep.{u, v, w, t} k Q}
variable [HasExt.{e} (QuiverRep.{u, v, w, t} k Q)]

/-- Compatible endpoint maps on two arrow families induce the corresponding equality of
extension classes. -/
theorem arrowExtension_extClass_naturality (c : HomArrow M N) (d : HomArrow M' N')
    (f : M ⟶ M') (g : N ⟶ N')
    (h : ∀ i j (a : i ⟶ j),
      (homVertex N N' g j).comp (c i j a) = (d i j a).comp (homVertex M M' f i)) :
    (arrowExtensionComplex_shortExact M N c).extClass.comp (Ext.mk₀ g) (add_zero 1) =
      (Ext.mk₀ f).comp (arrowExtensionComplex_shortExact M' N' d).extClass (zero_add 1) := by
  let b : arrowExtension M N c ⟶ arrowExtension M' N' d :=
    Paths.liftNatTrans (fun i ↦ ModuleCat.ofHom
      ((homVertex N N' g i).prodMap (homVertex M M' f i))) (by
      intro i j a
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun (x : vertexSpace k Q N i × vertexSpace k Q M i) ↦ ?_
      -- Evaluate the naturality square in the product coordinates of the two extensions.
      change (homVertex N N' g j ((arrowExtension M N c).map a.toPath x).1,
          homVertex M M' f j ((arrowExtension M N c).map a.toPath x).2) =
        (arrowExtension M' N' d).map a.toPath
          (homVertex N N' g i x.1, homVertex M M' f i x.2)
      have ha := LinearMap.congr_fun (h i j a) x.2
      simp only [LinearMap.comp_apply] at ha
      simp only [arrowExtension_map_toPath, map_add, homVertex_naturality, ha])
  have hb (i : Q) (x : vertexSpace k Q N i × vertexSpace k Q M i) :
      (b.app ((Paths.of Q).obj i)).hom x =
        (homVertex N N' g i x.1, homVertex M M' f i x.2) :=
    congrArg (fun p : (arrowExtension M N c).obj i ⟶ (arrowExtension M' N' d).obj i ↦ p.hom x)
      (Paths.liftNatTrans_app _ _ i)
  have hl : g ≫ arrowExtensionInl M' N' d = arrowExtensionInl M N c ≫ b := by
    refine NatTrans.ext (funext fun (i : Q) ↦ ModuleCat.hom_ext ?_)
    refine LinearMap.ext fun (x : vertexSpace k Q N i) ↦ ?_
    -- Use pointwise composition at the underlying vertex.
    change ((arrowExtensionInl M' N' d).app ((Paths.of Q).obj i)).hom
        ((g.app ((Paths.of Q).obj i)).hom x) = (b.app ((Paths.of Q).obj i)).hom
          (((arrowExtensionInl M N c).app ((Paths.of Q).obj i)).hom x)
    rw [arrowExtensionInl_app_apply, hb, map_zero]
    exact (congrArg (fun y : vertexSpace k Q N' i ↦
      ((arrowExtensionInl M' N' d).app ((Paths.of Q).obj i)).hom y)
      (homVertex_apply N N' g i x).symm).trans (arrowExtensionInl_app_apply M' N' d i _)
  have hr : b ≫ arrowExtensionSnd M' N' d = arrowExtensionSnd M N c ≫ f := by
    refine NatTrans.ext (funext fun (i : Q) ↦ ModuleCat.hom_ext ?_)
    refine LinearMap.ext fun (x : vertexSpace k Q N i × vertexSpace k Q M i) ↦ ?_
    -- Use pointwise composition at the underlying vertex.
    change ((arrowExtensionSnd M' N' d).app ((Paths.of Q).obj i)).hom
        ((b.app ((Paths.of Q).obj i)).hom x) =
      (f.app ((Paths.of Q).obj i)).hom (((arrowExtensionSnd M N c).app ((Paths.of Q).obj i)).hom x)
    rw [hb, arrowExtensionSnd_app_apply, arrowExtensionSnd_app_apply]
    exact homVertex_apply M M' f i x.2
  let φ : arrowExtensionComplex M N c ⟶ arrowExtensionComplex M' N' d := ⟨g, b, f, hl, hr⟩
  exact (arrowExtensionComplex_shortExact M N c).extClass_naturality
    (arrowExtensionComplex_shortExact M' N' d) φ

/-- The class of an arrow extension depends linearly on its arrow family. -/
noncomputable def arrowExtensionExtClass (M N : QuiverRep.{u, v, w, t} k Q) :
    HomArrow M N →ₗ[k] Ext.{e} M N 1 where
  toFun c := (arrowExtensionComplex_shortExact M N c).extClass
  map_add' c d := by
    let b : HomArrow M (N ⊞ N) := fun i j a ↦
      (homVertex N (N ⊞ N) biprod.inl j).comp (c i j a) +
        (homVertex N (N ⊞ N) biprod.inr j).comp (d i j a)
    have hb (g : N ⊞ N ⟶ N) (i j : Q) (a : i ⟶ j) :
        (homVertex (N ⊞ N) N g j).comp (b i j a) =
          (homVertex N N (biprod.inl ≫ g) j).comp (c i j a) +
            (homVertex N N (biprod.inr ≫ g) j).comp (d i j a) := by
      have hcomp (ι : N ⟶ N ⊞ N) (x : vertexSpace k Q N j) :
          homVertex N N (ι ≫ g) j x =
            homVertex (N ⊞ N) N g j (homVertex N (N ⊞ N) ι j x) :=
        (homVertex_apply N N (ι ≫ g) j x).trans
          ((congrArg (fun y ↦ (g.app ((Paths.of Q).obj j)).hom y)
            (homVertex_apply N (N ⊞ N) ι j x).symm).trans
            (homVertex_apply (N ⊞ N) N g j _).symm)
      ext x
      simp only [b, LinearMap.comp_apply, LinearMap.add_apply, map_add, hcomp]
    have hid (X : QuiverRep.{u, v, w, t} k Q) (i : Q) :
        homVertex X X (𝟙 X) i = LinearMap.id :=
      LinearMap.ext fun x ↦ homVertex_apply X X (𝟙 X) i x
    have hz (i : Q) : homVertex N N 0 i = 0 :=
      LinearMap.ext fun x ↦ homVertex_apply N N 0 i x
    have h₁ := arrowExtension_extClass_naturality b c (𝟙 M) biprod.fst (by
      intro i j a
      simp only [hb, biprod.inl_fst, biprod.inr_fst, hid, hz,
        LinearMap.id_comp, LinearMap.zero_comp, add_zero, LinearMap.comp_id])
    have h₂ := arrowExtension_extClass_naturality b d (𝟙 M) biprod.snd (by
      intro i j a
      simp only [hb, biprod.inl_snd, biprod.inr_snd, hz, hid,
        LinearMap.zero_comp, LinearMap.id_comp, zero_add, LinearMap.comp_id])
    have h := arrowExtension_extClass_naturality b (c + d) (𝟙 M) (biprod.fst + biprod.snd) (by
      intro i j a
      simp only [hb, Preadditive.comp_add, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
        biprod.inr_snd, add_zero, zero_add, hid, LinearMap.id_comp, LinearMap.comp_id,
        Pi.add_apply])
    let β : Ext.{e} M (N ⊞ N) 1 := (arrowExtensionComplex_shortExact M (N ⊞ N) b).extClass
    have hadd := (congrArg (fun y ↦ β.comp y rfl) (Ext.mk₀_add biprod.fst biprod.snd)).trans
      (Ext.comp_add β _ _ (add_zero 1))
    exact ((Ext.mk₀_id_comp _).symm.trans h.symm).trans
      (hadd.trans (congrArg₂ (· + ·) (h₁.trans (Ext.mk₀_id_comp _))
        (h₂.trans (Ext.mk₀_id_comp _))))
  map_smul' r c := by
    have h := arrowExtension_extClass_naturality c (r • c) (𝟙 M) (r • 𝟙 N) (by
      intro i j a
      ext x
      simp only [LinearMap.comp_apply, homVertex_apply, NatTrans.app_smul, NatTrans.id_app,
        ModuleCat.hom_smul, ModuleCat.hom_id]
      rfl)
    exact ((Ext.mk₀_id_comp _).symm.trans h.symm).trans
      (Ext.smul_eq_comp_mk₀ (arrowExtensionComplex_shortExact M N c).extClass r).symm

/-- The arrow-family map evaluates to the native extension class. -/
@[simp]
theorem arrowExtensionExtClass_apply (c : HomArrow M N) :
    arrowExtensionExtClass M N c = (arrowExtensionComplex_shortExact M N c).extClass := (rfl)

-- The application simp lemma already rewrites both sides to native extension classes.
/-- Two arrow families have the same extension class precisely when they represent the
same element of the Hom cokernel. -/
theorem arrowExtensionExtClass_eq_iff {c d : HomArrow M N} :
    arrowExtensionExtClass M N c = arrowExtensionExtClass M N d ↔
      (Submodule.Quotient.mk c : HomArrow M N ⧸ (homDifferential M N).range) =
        Submodule.Quotient.mk d := by
  rw [arrowExtensionExtClass_apply, arrowExtensionExtClass_apply,
    ← exists_arrowExtension_hom_fixing_ends_iff]
  have h := (arrowExtensionComplex_shortExact M N c).exists_hom_iff_extClass_comp_eq
    (arrowExtensionComplex_shortExact M N d) (𝟙 N) (𝟙 M)
  refine (h.trans ⟨fun hh ↦ (Ext.comp_mk₀_id _).symm.trans (hh.trans (Ext.mk₀_id_comp _)),
    fun hh ↦ (Ext.comp_mk₀_id _).trans (hh.trans (Ext.mk₀_id_comp _).symm)⟩).symm.trans ⟨?_, ?_⟩
  · rintro ⟨φ, h₁, h₃⟩
    refine ⟨φ.τ₂, φ.comm₁₂.symm.trans ?_, φ.comm₂₃.trans ?_⟩
    · exact (congrArg (· ≫ (arrowExtensionComplex M N d).f) h₁).trans (Category.id_comp _)
    · exact (congrArg ((arrowExtensionComplex M N c).g ≫ ·) h₃).trans (Category.comp_id _)
  · rintro ⟨f, hf, hg⟩
    exact ⟨⟨𝟙 N, f, 𝟙 M, (Category.id_comp _).trans hf.symm,
      hg.trans (Category.comp_id _).symm⟩, rfl, rfl⟩

variable (M N) [EnoughProjectives (QuiverRep.{u, v, w, t} k Q)]

/-- The Hom cokernel computes `Ext¹(M,N)` when the representation category has enough projectives.
For a finite vertex set, apply `Equivalence.enoughProjectives_iff` to `quiverRepEquivalence`
when the path algebra is small in the universe of the vertex spaces. -/
noncomputable def homDifferentialCokerEquivExt :
    (HomArrow M N ⧸ (homDifferential M N).range) ≃ₗ[k] Ext.{e} M N 1 := by
  have hk : (homDifferential M N).range ≤ (arrowExtensionExtClass M N).ker := by
    intro c hc
    rw [LinearMap.mem_ker, ← (arrowExtensionExtClass M N).map_zero, arrowExtensionExtClass_eq_iff]
    simpa only [Submodule.Quotient.mk_zero, Submodule.Quotient.mk_eq_zero] using hc
  refine LinearEquiv.ofBijective ((homDifferential M N).range.liftQ _ hk) ⟨?_, ?_⟩
  · rintro ⟨c⟩ ⟨d⟩ h
    exact arrowExtensionExtClass_eq_iff.mp h
  · intro α
    let P := Projective.π M
    have hP : (ShortComplex.mk (kernel.ι P) P (kernel.condition P)).ShortExact :=
      ShortComplex.ShortExact.mk (ShortComplex.exact_kernel P)
    obtain ⟨E, i, p, hip, hS, rfl⟩ := hP.exists_extClass_eq N α
    obtain ⟨c, iso, hin, hout⟩ := exists_arrowExtension_iso_fixing_ends hS
    let φ : arrowExtensionComplex M N c ⟶ ShortComplex.mk i p hip :=
      ⟨𝟙 N, iso.hom, 𝟙 M, (Category.id_comp i).trans hin.symm,
        hout.trans (Category.comp_id _).symm⟩
    have h := (arrowExtensionComplex_shortExact M N c).extClass_naturality hS φ
    exact ⟨Submodule.Quotient.mk c,
      (Ext.comp_mk₀_id _).symm.trans (h.trans (Ext.mk₀_id_comp _))⟩

/-- The cokernel comparison sends the class of an arrow family to its extension class. -/
@[simp]
theorem homDifferentialCokerEquivExt_mk (c : HomArrow M N) :
    homDifferentialCokerEquivExt M N (Submodule.Quotient.mk c) =
      (arrowExtensionComplex_shortExact M N c).extClass := (rfl)

end TauCeti.QuiverRep
