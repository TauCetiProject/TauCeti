/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Lang.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.FormallyEtale
import TauCeti.AlgebraicGeometry.Frobenius.FixedPoints
import TauCeti.AlgebraicGeometry.Frobenius.Thickening
import TauCeti.AlgebraicGeometry.GroupScheme.Etale
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Colimits
import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.RationalPoint.Finite
-- Apply the general étale kernel theorem using the construction of the Lang kernel.
import all TauCeti.AlgebraicGeometry.GroupScheme.Lang.Basic

/-!
# Étaleness of the Lang map

For a commutative group scheme over a finite field, the Lang map is formally étale.
On a square-zero thickening the Frobenius of a point is determined by its reduction,
so prescribing the Lang image determines a unique lift. In particular, for a group
scheme locally of finite presentation over the field, the Lang map and its fibre over
the identity are étale. The kernel is the disjoint union of copies of the base
indexed by the rational points of the group, so it is finite when the group is of finite type.

## References

* S. Lang, *Algebraic groups over finite fields*, Amer. J. Math. 78 (1956), 555–563.
* G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987), §1.1.3.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme MonObj
open scoped CategoryTheory.Obj

namespace TauCeti.GroupScheme

universe u

variable (k : Type u) [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] (a : ℕ)
  (ha : Nat.card k = p ^ a) (G : CommGrp (Over (Spec (CommRingCat.of k))))

/-- The Lang map of any commutative group scheme over a finite field is formally étale, without
any finiteness assumption on the group scheme. -/
theorem formallyEtale_langMap : AlgebraicGeometry.FormallyEtale
    (langMap k a ha G).hom.hom.hom.left := by
  rw [AlgebraicGeometry.formallyEtale_iff_existsUnique_lift_quotient]
  intro B I hI g h w
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let L := (langMap k a ha G).hom.hom.hom
  let T' := Over.mk (h ≫ G.X.hom)
  let T := Over.mk (i ≫ h ≫ G.X.hom)
  let j : T ⟶ T' := Over.homMk i
  let y : T' ⟶ G.X := Over.homMk h
  let x : T ⟶ G.X := Over.homMk g (by
    rw [← Over.w L, reassoc_of% w]
    rfl)
  have hxy : x ≫ L = j ≫ y := Over.OverMorphism.ext w
  have hB : (p : Γ(Spec B, ⊤)) = 0 :=
    natCast_eq_zero_of_hom T'.hom (natCast_spec_eq_zero (p := p) (.of k))
  have ha0 : 0 < a := by
    by_contra! h
    have ha1 : Nat.card k = 1 := by simpa [Nat.eq_zero_of_le_zero h] using ha
    exact (not_nontrivial_iff_subsingleton.mpr ((Nat.card_eq_one_iff_unique.mp ha1).1))
      inferInstance
  -- Frobenius factors through the square-zero closed subscheme. Dividing the resulting
  -- Frobenius value by the prescribed Lang image gives the unique lift.
  obtain ⟨v, hv⟩ := exists_comp_SpecMap_quotient_mk_eq_iterateFrobenius hB I hI ha0
  have hv' : v ≫ j.left = (qPowerFrobeniusOver k a ha T').left := by
    rw [qPowerFrobeniusOver_left, qPowerFrobenius_eq_iterated]
    exact hv
  let s : T' ⟶ T := Over.homMk v (by
    rw [← Over.w j, ← Category.assoc, hv', Over.w])
  have hs : s ≫ j = qPowerFrobeniusOver k a ha T' := Over.OverMorphism.ext hv'
  have hsj : j ≫ s = qPowerFrobeniusOver k a ha T := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hs, comp_qPowerFrobeniusOver]
  have hlift : j ≫ (s ≫ x / y) = x := by
    rw [GrpObj.comp_div, ← Category.assoc, hsj, ← hxy,
      comp_langMap_hom_hom_hom, div_div_cancel]
  have hLang (z : T' ⟶ G.X) (hz : j ≫ z = x) : z ≫ L = s ≫ x / z := by
    rw [comp_langMap_hom_hom_hom, ← hs, Category.assoc, hz]
  refine ⟨(s ≫ x / y).left, ⟨congrArg (fun z ↦ z.left) hlift, ?_⟩, ?_⟩
  · have he : (s ≫ x / y) ≫ L = y := by
      rw [hLang _ hlift, div_div_cancel]
    exact congrArg (fun z ↦ z.left) he
  · intro l ⟨hl, hl'⟩
    let z : T' ⟶ G.X := Over.homMk l (by rw [← Over.w L, reassoc_of% hl']; rfl)
    have hz : j ≫ z = x := Over.OverMorphism.ext hl
    have hzy : z ≫ L = y := Over.OverMorphism.ext hl'
    have he : z = s ≫ x / y := by
      rw [← hzy, hLang z hz, div_div_cancel]
    exact congrArg (fun z ↦ z.left) he

/-- The Lang map of a commutative group scheme locally of finite presentation over a finite
field is étale. -/
instance etale_langMap [LocallyOfFinitePresentation G.X.hom] :
    Etale (langMap k a ha G).hom.hom.hom.left := by
  let L := (langMap k a ha G).hom.hom.hom
  have : LocallyOfFinitePresentation (L.left ≫ G.X.hom) := by
    rw [Over.w L]
    infer_instance
  have := locallyOfFinitePresentation_of_comp L.left G.X.hom
  have := formallyEtale_langMap k a ha G
  exact AlgebraicGeometry.etale_of_formallyEtale L.left

/-- The scheme-theoretic kernel of the Lang map is étale over the finite field. -/
instance etale_langKernel [LocallyOfFinitePresentation G.X.hom] :
    Etale (langKernel k a ha G).X.hom := by
  rw [langKernel]
  exact Grp.etale_kernel_hom ((CommGrp.forget₂Grp _).map (langMap k a ha G))
    (etale_langMap k a ha G)

/-- The disjoint union of the rational points of the group maps isomorphically to the
scheme-theoretic Lang kernel. Each component is the lift of the corresponding rational point
through the kernel inclusion. -/
theorem isIso_sigmaDesc_langKernelLift [LocallyOfFinitePresentation G.X.hom] :
    IsIso (Sigma.desc fun x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X ↦
      (langKernelLift k a ha x (by simp)).left) := by
  let H := (langKernel k a ha G).X
  let s (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X) : Spec (.of k) ⟶ H.left :=
    (langKernelLift k a ha x (by simp)).left
  have hsection (x) : s x ≫ H.hom = 𝟙 _ := Over.w (langKernelLift k a ha x (by simp))
  have : ∀ x, IsOpenImmersion (s x) := by
    intro x
    have : IsSplitMono (s x) := ⟨⟨⟨H.hom, hsection x⟩⟩⟩
    have : Etale (s x ≫ H.hom) := by rw [hsection]; infer_instance
    have : Etale (s x) := Etale.of_comp _ H.hom
    exact IsOpenImmersion.of_etale_of_universallyInjective _
  have hins (x y) (h : s x = s y) : x = y := by
    have h' : langKernelLift k a ha x (by simp) = langKernelLift k a ha y (by simp) :=
      Over.OverMorphism.ext h
    simpa only [langKernelLift_ι] using congrArg (· ≫ langKernelι k a ha G) h'
  have hdisj (x y) (hxy : x ≠ y) : Disjoint (Set.range (s x)) (Set.range (s y)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨t, rfl⟩ ⟨u, hu⟩
    have hr : Set.range (s x) ⊆ Set.range (s y) := by
      rintro _ ⟨t', rfl⟩
      exact ⟨u, (hu.trans (congrArg (s x) (Subsingleton.elim t t')))⟩
    let l := IsOpenImmersion.lift (s y) (s x) hr
    have hls : l ≫ s y = s x := IsOpenImmersion.lift_fac _ _ _
    have hl : l = 𝟙 _ := by
      rw [← Category.comp_id l, ← hsection y, ← Category.assoc, hls, hsection, hsection]
    exact hxy (hins x y (by simpa [hl] using hls.symm))
  have hF : qPowerFrobenius k H.hom a ha = 𝟙 H.left := by
    simpa only [qPowerFrobeniusOver_left, Over.id_left] using
      congrArg (fun z ↦ z.left) (qPowerFrobeniusOver_langKernel k a ha G)
  refine (isIso_iff_isOpenImmersion_and_surjective (Sigma.desc s)).2
    ⟨isOpenImmersion_sigmaDesc _ _ hdisj, ⟨fun z ↦ ?_⟩⟩
  obtain ⟨r, hr, hrz⟩ := H.hom.exists_section_of_qPowerFrobenius_eq_id ha hF z
  let r' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H := Over.homMk r hr
  let x := r' ≫ langKernelι k a ha G
  have h : s x = r := congrArg (fun z ↦ z.left)
    (langKernel_hom_ext k a ha (langKernelLift_ι k a ha x (by simp)))
  refine ⟨Sigma.ι (fun _ ↦ Spec (.of k)) x default, ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc, h, hrz]

/-- The Lang kernel of a finite-type commutative group scheme over a finite field is finite. -/
instance isFinite_langKernel [QuasiCompact G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    IsFinite (langKernel k a ha G).X.hom := by
  have : Finite k := Nat.finite_of_card_ne_zero (ha ▸ pow_ne_zero a (Fact.out : p.Prime).ne_zero)
  have := G.X.hom.finite_points (L := k)
  let toPoint (x : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) :
      {y : Spec (.of k) ⟶ G.X.left //
        y ≫ G.X.hom = Spec.map (CommRingCat.ofHom (algebraMap k k))} :=
    ⟨x.left, by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
      exact Over.w x⟩
  have : Finite (𝟙_ (Over (Spec (.of k))) ⟶ G.X) :=
    Finite.of_injective toPoint fun _ _ hx ↦ Over.OverMorphism.ext (congrArg Subtype.val hx)
  let H := (langKernel k a ha G).X
  let s (x : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : Spec (.of k) ⟶ H.left :=
    (langKernelLift k a ha x (by simp)).left
  have : IsIso (Sigma.desc s) := isIso_sigmaDesc_langKernelLift k a ha G
  have hc : Sigma.desc s ≫ H.hom = Sigma.desc (fun _ ↦ 𝟙 (Spec (.of k))) := by
    apply Sigma.hom_ext
    intro x
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact Over.w (langKernelLift k a ha x (by simp))
  have : IsFinite (Sigma.desc s ≫ H.hom) := by
    rw [hc]
    exact TauCeti.IsFinite.sigmaDesc fun _ ↦ inferInstance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) (Sigma.desc s) H.hom).1
    inferInstance

end TauCeti.GroupScheme
