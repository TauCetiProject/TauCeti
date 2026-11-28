/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Infinitesimal
import TauCeti.AlgebraicGeometry.Morphisms.Etale.FormallyEtale
import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Étale multiplication on smooth commutative group schemes over a field

On a smooth commutative group scheme over a field, multiplication by an integer invertible
in the field is étale. A lift along a square-zero thickening can be corrected uniquely by
an infinitesimal point at the identity, where multiplication by the integer is bijective.

## References

* J. S. Milne, *Abelian Varieties* (2022), §8, Theorem 8.2, for the abelian variety statement.
* The Stacks Project, Lemma 37.8.10 (02HM), for the infinitesimal criterion for étaleness.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace TauCeti.GroupScheme

variable {K : Type u} [Field K]

private theorem existsUnique_mulBy_lift (G : CommGrp (Over (Spec (.of K))))
    (B : CommRingCat.{u}) (t : Spec B ⟶ Spec (.of K))
    (I : Ideal B) (hI : I ^ 2 = ⊥) (n : ℤ) (hn : (n : K) ≠ 0) :
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let j : Over.mk (i ≫ t) ⟶ Over.mk t := Over.homMk i
    ∀ (x y : Over.mk t ⟶ G.X), j ≫ x ^ n = j ≫ y →
      ∃! z : Over.mk t ⟶ G.X, j ≫ z = j ≫ x ∧ z ^ n = y := by
  dsimp only
  intro x y h
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let j : Over.mk (i ≫ t) ⟶ Over.mk t := Over.homMk i
  let G' := (CommGrp.forget₂Grp _).obj G
  let r : (Over.mk t ⟶ G.X) →* (Over.mk (i ≫ t) ⟶ G.X) :=
    ((yonedaGrp.obj G').map j.op).hom
  have hr (a : Over.mk t ⟶ G.X) : r a = j ≫ a := rfl
  have hunit : IsUnit (n : B) := by
    obtain ⟨t', _⟩ := Spec.map_surjective t
    rw [← map_intCast t'.hom]
    exact (isUnit_iff_ne_zero.mpr hn).map t'.hom
  have hb : Function.Bijective (fun x : r.ker ↦ x ^ n) :=
    bijective_zpow_ker_squareZero G' t I hI n hunit
  -- Divide the discrepancy between the desired image and the current image in the kernel.
  let d : r.ker := ⟨y / x ^ n, by rw [MonoidHom.mem_ker, map_div, hr, hr, ← h, div_self']⟩
  obtain ⟨w, hw⟩ := hb.2 d
  have hw' : (w : Over.mk t ⟶ G.X) ^ n = y / x ^ n := congrArg Subtype.val hw
  refine ⟨(w : Over.mk t ⟶ G.X) * x, ⟨?_, ?_⟩, ?_⟩
  · rw [← hr, map_mul, MonoidHom.mem_ker.mp w.property, one_mul, hr]
  · rw [mul_zpow, hw', div_mul_cancel]
  · rintro z ⟨hz, hzy⟩
    let v : r.ker := ⟨z / x, by rw [MonoidHom.mem_ker, map_div, hr, hr, hz, div_self']⟩
    have hv : v ^ n = w ^ n := by
      have hwn : w ^ n = d := hw
      rw [hwn]
      apply Subtype.ext
      have hdiv : (z / x) ^ n = y / x ^ n := by rw [div_zpow, hzy]
      exact hdiv
    have hwz : z / x = (w : Over.mk t ⟶ G.X) := congrArg Subtype.val (hb.1 hv)
    exact div_eq_iff_eq_mul.mp hwz

private theorem formallyEtale_openImmersion_comp_zpow
    (G : CommGrp (Over (Spec (.of K)))) [Smooth G.X.hom]
    {U : Scheme.{u}} [IsAffine U] (u : U ⟶ G.X.left) [IsOpenImmersion u]
    (n : ℤ) (hn : (n : K) ≠ 0) :
    AlgebraicGeometry.FormallyEtale (u ≫ (𝟙 G.X ^ n : G.X ⟶ G.X).left) := by
  rw [AlgebraicGeometry.formallyEtale_iff_existsUnique_lift_quotient]
  intro B I hI a b h
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let f : G.X ⟶ G.X := 𝟙 G.X ^ n
  let t := b ≫ G.X.hom
  let j : Over.mk (i ≫ t) ⟶ Over.mk t := Over.homMk i
  have hπ : a ≫ u ≫ G.X.hom = i ≫ t := by
    rw [← Over.w f, reassoc_of% h]
  -- Lift the original point through the smooth affine chart first.
  have hu : Smooth (u ≫ G.X.hom) := inferInstance
  obtain ⟨l, hl, hlπ⟩ := (AlgebraicGeometry.formallySmooth_iff_exists_lift_quotient
    (u ≫ G.X.hom)).mp inferInstance B I hI a t hπ
  let x : Over.mk t ⟶ G.X := Over.homMk (l ≫ u) (by
    simpa only [Category.assoc, Over.mk_hom] using hlπ)
  let y : Over.mk t ⟶ G.X := Over.homMk b
  have hpow (w : Over.mk t ⟶ G.X) : w ≫ f = w ^ n := by
    simp only [f, GrpObj.comp_zpow, Category.comp_id]
  have hx : j ≫ x ^ n = j ≫ y := by
    rw [← hpow]
    apply Over.OverMorphism.ext
    simpa only [j, x, y, i, f, Over.comp_left, Over.homMk_left, ← Category.assoc, hl] using h
  obtain ⟨z, ⟨hz, hzb⟩, huniq⟩ :=
    existsUnique_mulBy_lift G B t I hI n hn x y hx
  have hi : AlgebraicGeometry.IsFirstOrderThickening i :=
    AlgebraicGeometry.IsFirstOrderThickening.SpecMap_quotient_mk hI
  have hza : i ≫ z.left = a ≫ u := by
    simpa only [x, Over.comp_left, Over.homMk_left, ← Category.assoc, hl]
      using congrArg Over.Hom.left hz
  -- The correction has the same reduction, so it still lands in the original chart.
  have hzu : Set.range z.left ⊆ Set.range u := by
    rintro v ⟨v', rfl⟩
    obtain ⟨v₀, rfl⟩ := i.surjective v'
    exact ⟨a v₀, by rw [← Scheme.Hom.comp_apply, ← hza, Scheme.Hom.comp_apply]⟩
  let z' := IsOpenImmersion.lift u z.left hzu
  have hz'u : z' ≫ u = z.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨z', ⟨(cancel_mono u).1 ?_, ?_⟩, ?_⟩
  · rwa [Category.assoc, hz'u]
  · rw [← Category.assoc, hz'u, ← Over.comp_left, hpow, hzb]
    rfl
  · rintro z₀ ⟨hz₀, hz₀f⟩
    let z₁ : Over.mk t ⟶ G.X := Over.homMk (z₀ ≫ u) (by
      rw [Category.assoc, ← Over.w f, reassoc_of% hz₀f]
      rfl)
    have hz₁ : j ≫ z₁ = j ≫ x := Over.OverMorphism.ext (by
      simp only [z₁, j, i, x, Over.comp_left, Over.homMk_left, ← Category.assoc, hz₀, hl])
    have hz₁f : z₁ ^ n = y := by
      rw [← hpow]
      exact Over.OverMorphism.ext (by
        simpa only [z₁, y, f, Over.comp_left, Over.homMk_left, Category.assoc] using hz₀f)
    exact (cancel_mono u).1 ((congrArg Over.Hom.left (huniq z₁ ⟨hz₁, hz₁f⟩)).trans hz'u.symm)

/-- The multiplication-by-`n` endomorphism of a smooth commutative group scheme over a field
is étale when `n` is nonzero in the field. -/
theorem etale_zpow_of_intCast_ne_zero (G : CommGrp (Over (Spec (.of K)))) [Smooth G.X.hom]
    {n : ℤ} (hn : (n : K) ≠ 0) : Etale ((𝟙 G.X ^ n : G.X ⟶ G.X).left) := by
  let f : G.X ⟶ G.X := 𝟙 G.X ^ n
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  refine IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) G.X.left.affineCover fun k ↦ ?_
  let u := G.X.left.affineCover.f k
  have hfp : LocallyOfFinitePresentation (f.left ≫ G.X.hom) := by
    rw [Over.w f]
    infer_instance
  have := locallyOfFinitePresentation_of_comp f.left G.X.hom
  have := formallyEtale_openImmersion_comp_zpow G u n hn
  exact AlgebraicGeometry.etale_of_formallyEtale (u ≫ f.left)

end TauCeti.GroupScheme
