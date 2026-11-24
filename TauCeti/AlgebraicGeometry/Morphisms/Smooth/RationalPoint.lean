/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.AlgebraicGeometry.BaseChangeSection
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.RationalPoint.AffineSpace
import TauCeti.AlgebraicGeometry.Scheme.Connected.Component
import TauCeti.FieldTheory.IsSepClosed

/-!
# Rational points on smooth schemes

Rational points are dense on a smooth scheme over a separably closed field. The proof uses
étale charts over affine space and lifting of geometric points along étale morphisms.

Over an arbitrary field `k`, a rational point `y` of a smooth `k`-scheme has an integral affine
open neighbourhood `V` with an étale `k`-morphism `π : V ⟶ Spec k[X_0, …, X_{m-1}]` sending `y` to
the origin (`AlgebraicGeometry.Smooth.exists_etale_chart_of_section`). This reduces the
construction of curves through `y`, defined over `k` itself, to the case of an étale chart over
affine space. For instance, pulling back a curve in affine space through the origin along `π`
and keeping the component through `y` gives a curve over `k` through `y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.denseRange_rationalSections`: rational points are dense on a
  smooth scheme over a separably closed field.
* `AlgebraicGeometry.Smooth.exists_etale_chart_of_section`: an integral affine étale chart over
  affine space, centred at a rational point of a smooth scheme over a field.

## References

* The Stacks Project, [Tag 054L](https://stacks.math.columbia.edu/tag/054L), for étale
  coordinates, and Lemma 33.25.4 (056T) and Properties, Lemma 28.7.7 (033N), for the integrality
  of a connected scheme smooth over a field.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Rational sections of a smooth scheme over a separably closed field have dense image. -/
theorem denseRange_rationalSections {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] :
    DenseRange fun s : {s : Spec (.of k) ⟶ X // s ≫ f = 𝟙 _} ↦ s.val default := by
  refine dense_iff_inter_open.mpr fun U hU ⟨x, hx⟩ ↦ ?_
  obtain ⟨V, _, hxV, n, g, hg, hgf⟩ := Smooth.exists_etale_affineSpace f x
  let W : Set V.toScheme := V.ι ⁻¹' U
  obtain ⟨t, ht, y, hy, hyt⟩ :=
    AffineSpace.exists_rationalPoint_mem_open (ULift.{u} (Fin n)) (g '' W)
    (g.isOpenMap _ (hU.preimage V.ι.continuous)) ⟨_, ⟨⟨x, hxV⟩, hx, rfl⟩⟩
  obtain ⟨s, hs, hsy⟩ := Scheme.exists_fac_of_etale_of_isSepClosed g t y
    (hyt.trans (congrArg t (Subsingleton.elim _ _)))
  refine ⟨V.ι y, hy, ⟨s ≫ V.ι, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hgf, ← Category.assoc, hs, ht]
  · exact (Scheme.Hom.comp_apply s V.ι default).trans (congrArg V.ι hsy)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

universe u

/-- **An étale chart centred at a rational point.** Let `y` be a rational point of a scheme `X`
smooth over a field `k`, that is, a section of the structure morphism `f`. Then `y` lies in an
affine open `V ⊆ X` that is integral as a scheme, and which carries an étale morphism
`π : V ⟶ Spec k[X_0, …, X_{m-1}]` over `Spec k`, for some `m`, sending `y` to the origin. -/
theorem Smooth.exists_etale_chart_of_section {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (y : Spec (.of k) ⟶ X) (hy : y ≫ f = 𝟙 _) :
    ∃ V : X.Opens, IsAffineOpen V ∧ IsIntegral V.toScheme ∧ ∃ (m : ℕ)
      (π : V.toScheme ⟶ Spec (.of (MvPolynomial (Fin m) k))) (y₀ : Spec (.of k) ⟶ V.toScheme),
      Etale π ∧ π ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = V.ι ≫ f ∧ y₀ ≫ V.ι = y ∧
        y₀ ≫ π = Spec.map (CommRingCat.ofHom MvPolynomial.constantCoeff) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let x := y default
  -- The connected component `C` of `X` through `x` is open, and integral: it is connected with
  -- regular local rings, being smooth over `k`.
  let C := X.connectedComponentOpen x
  have : IsIntegral C.toScheme := by
    have := TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth (C.ι ≫ f)
    exact TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _
  -- Étale coordinates `g` near `x`, restricted to an affine open `W ∋ x` inside `C`.
  obtain ⟨V, -, hxV, n, g, hg, hgf⟩ := Smooth.exists_etale_affineSpace f x
  obtain ⟨W, hW, hxW, hWVC⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := V ⊓ C)
    ⟨hxV, by simpa only [C, Scheme.coe_connectedComponentOpen] using mem_connectedComponent⟩
  have hWV : W ≤ V := fun z hz ↦ (hWVC hz).1
  have hWC : W ≤ C := fun z hz ↦ (hWVC hz).2
  have : Nonempty W.toScheme := ⟨⟨x, hxW⟩⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE hWC)
  let y₁ : Spec (.of k) ⟶ W.toScheme := IsOpenImmersion.lift W.ι y (by
    rintro _ ⟨z, rfl⟩
    rwa [Scheme.Opens.range_ι, Subsingleton.elim z default])
  have hy₁ : y₁ ≫ W.ι = y := IsOpenImmersion.lift_fac _ _ _
  -- Identify the target `𝔸(ULift (Fin n); Spec k)` of `g` with `Spec k[X_0, …, X_{n-1}]`.
  let e := (MvPolynomial.renameEquiv k (Equiv.ulift.{u} (α := Fin n)).symm).toRingEquiv
  let π₁ : W.toScheme ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
    X.homOfLE hWV ≫ g ≫ (AffineSpace.SpecIso _ (.of k)).hom ≫ Spec.map e.toCommRingCatIso.hom
  have he : Spec.map e.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun r ↦ by simp [e]))
  have hA : (AffineSpace.SpecIso _ (.of k)).hom ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k) := by
    rw [← Iso.eq_inv_comp, AffineSpace.SpecIso_inv_over]
  have hπ₁ : π₁ ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = W.ι ≫ f := by
    simp only [π₁, Category.assoc, he, hA, hgf, Scheme.homOfLE_ι_assoc]
  -- Translate the image of `y` to the origin.
  have hyπ₁ : (y₁ ≫ π₁) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = 𝟙 _ := by
    rw [Category.assoc, hπ₁, reassoc_of% hy₁, hy]
  obtain ⟨τ, hτ, hτC, hyτ⟩ := exists_isIso_comp_eq_SpecMap_constantCoeff _ hyπ₁
  refine ⟨W, hW, inferInstance, n, π₁ ≫ τ, y₁, inferInstance, ?_, hy₁, ?_⟩
  · rw [Category.assoc, hτC, hπ₁]
  · rw [← Category.assoc, hyτ]

end AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

/-- Ground-field rational sections remain dense after an arbitrary extension of a separably
closed field. The points are the actual base changes of sections of the original scheme. -/
theorem denseRange_baseChangeSections {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] :
    DenseRange fun s : {s : Spec (.of k) ⟶ X // s ≫ f = 𝟙 _} ↦
      baseChangeSection f s.val s.property
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (default : Spec (.of K)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine dense_iff_inter_open.mpr fun U hU hne ↦ ?_
  obtain ⟨s, y, hy, hys⟩ := (Scheme.Hom.denseRange_rationalSections f).exists_mem_open
    ((pullback.snd g f).isOpenMap _ hU) (hne.image _)
  refine ⟨_, ?_, s, rfl⟩
  -- The density witness is a subtype evaluation; identify it with the section in the fiber law.
  change baseChangeSection f s.val s.property
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (default : Spec (.of K)) ∈ U
  rw [baseChangeSection_eq_of_snd_eq f s.val s.property g default hys]
  exact hy

end TauCeti.AlgebraicGeometry
