/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import TauCeti.AlgebraicGeometry.Morphisms.Thickening
import TauCeti.AlgebraicGeometry.Scheme.AffinePoints

/-!
# Multiplication on the kernel of square-zero reduction

In affine coordinates near the identity of a group scheme over a field, an infinitesimal
point differs from the identity by a square-zero correction. The product of two such points
adds their corrections. Consequently multiplication by an integer invertible on the test
ring acts bijectively on the kernel of reduction.
-/

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti.GroupScheme

noncomputable section

universe u

private abbrev squareZeroTriple {B : Type u} [CommRing B] (I : Ideal B) :
    Subring (B × B × B) :=
  let q := Ideal.Quotient.mk I
  let p := RingHom.snd B (B × B)
  let third := q.comp ((RingHom.snd B B).comp p)
  (q.comp (RingHom.fst B (B × B))).eqLocus third ⊓
    (q.comp ((RingHom.fst B B).comp p)).eqLocus third

private abbrev tripleFst {B : Type u} [CommRing B] (I : Ideal B) :
    squareZeroTriple I →+* B :=
  (RingHom.fst B (B × B)).comp (squareZeroTriple I).subtype

private abbrev tripleSnd {B : Type u} [CommRing B] (I : Ideal B) :
    squareZeroTriple I →+* B :=
  ((RingHom.fst B B).comp (RingHom.snd B (B × B))).comp (squareZeroTriple I).subtype

private abbrev tripleTrd {B : Type u} [CommRing B] (I : Ideal B) :
    squareZeroTriple I →+* B :=
  ((RingHom.snd B B).comp (RingHom.snd B (B × B))).comp (squareZeroTriple I).subtype

private def tripleLift {R B : Type u} [CommRing R] [CommRing B] (I : Ideal B)
    (f g h : R →+* B)
    (h₁ : (Ideal.Quotient.mk I).comp f = (Ideal.Quotient.mk I).comp h)
    (h₂ : (Ideal.Quotient.mk I).comp g = (Ideal.Quotient.mk I).comp h) :
    R →+* squareZeroTriple I :=
  (f.prod (g.prod h)).codRestrict (squareZeroTriple I) fun x ↦
    ⟨DFunLike.congr_fun h₁ x, DFunLike.congr_fun h₂ x⟩

private def tripleCombine {B : Type u} [CommRing B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (a b : B) : squareZeroTriple I →+* B where
  toFun x := x.val.2.2 + a * (x.val.1 - x.val.2.2) + b * (x.val.2.1 - x.val.2.2)
  map_one' := by
    -- The ambient product ring has one in all three coordinates.
    change 1 + a * (1 - 1) + b * (1 - 1) = 1
    simp
  map_zero' := by
    -- The ambient product ring has zero in all three coordinates.
    change 0 + a * (0 - 0) + b * (0 - 0) = 0
    simp
  map_add' x y := by
    -- Arithmetic takes place in the three coordinates of the ambient product ring.
    change (x.val.2.2 + y.val.2.2) + a * (x.val.1 + y.val.1 - (x.val.2.2 + y.val.2.2)) +
      b * (x.val.2.1 + y.val.2.1 - (x.val.2.2 + y.val.2.2)) = _
    ring
  map_mul' x y := by
    have hzero {r s : B} (hr : r ∈ I) (hs : s ∈ I) : r * s = 0 := by
      have hrs := Ideal.mul_mem_mul hr hs
      rwa [← pow_two, hI, Ideal.mem_bot] at hrs
    have hx₁ : x.val.1 - x.val.2.2 ∈ I := Ideal.Quotient.eq.mp x.property.1
    have hx₂ : x.val.2.1 - x.val.2.2 ∈ I := Ideal.Quotient.eq.mp x.property.2
    have hy₁ : y.val.1 - y.val.2.2 ∈ I := Ideal.Quotient.eq.mp y.property.1
    have hy₂ : y.val.2.1 - y.val.2.2 ∈ I := Ideal.Quotient.eq.mp y.property.2
    -- Expand the two coordinate differences and discard products of corrections.
    change x.val.2.2 * y.val.2.2 + a * (x.val.1 * y.val.1 - x.val.2.2 * y.val.2.2) +
      b * (x.val.2.1 * y.val.2.1 - x.val.2.2 * y.val.2.2) = _
    linear_combination (a - a ^ 2) * hzero hx₁ hy₁ + (b - b ^ 2) * hzero hx₂ hy₂ -
      (a * b) * hzero hx₁ hy₂ - (a * b) * hzero hx₂ hy₁

private lemma triple_ringHom_ext {R B : Type u} [CommRing R] [CommRing B] {I : Ideal B}
    {f g : R →+* squareZeroTriple I}
    (h₁ : (tripleFst I).comp f = (tripleFst I).comp g)
    (h₂ : (tripleSnd I).comp f = (tripleSnd I).comp g)
    (h₃ : (tripleTrd I).comp f = (tripleTrd I).comp g) : f = g := by
  apply RingHom.ext
  intro x
  exact Subtype.ext (Prod.ext (RingHom.congr_fun h₁ x)
    (Prod.ext (RingHom.congr_fun h₂ x) (RingHom.congr_fun h₃ x)))

private lemma surjective_specMap_tripleTrd {B : Type u} [CommRing B] (I : Ideal B)
    (hI : I ^ 2 = ⊥) :
    Surjective (Spec.map (CommRingCat.ofHom (tripleTrd I))) := by
  let p := CommRingCat.ofHom (tripleTrd I)
  have hsurj : Function.Surjective p :=
    fun b ↦ ⟨⟨(b, b, b), rfl, rfl⟩, rfl⟩
  have hprod {a b : B} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
    have h := Ideal.mul_mem_mul ha hb
    rwa [← pow_two, hI, Ideal.mem_bot] at h
  have : IsFirstOrderThickening (Spec.map p) := (IsFirstOrderThickening.SpecMap_iff p hsurj).2 <| by
    apply le_antisymm _ bot_le
    rw [Ideal.mul_le]
    intro a ha b hb
    rw [RingHom.mem_ker] at ha hb
    -- The projection is the third coordinate of the enclosing product ring.
    change a.val.2.2 = 0 at ha
    change b.val.2.2 = 0 at hb
    refine Ideal.mem_bot.mpr (Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · apply hprod
      · simpa [p, ha] using Ideal.Quotient.eq.mp a.property.1
      · simpa [p, hb] using Ideal.Quotient.eq.mp b.property.1
    · apply hprod
      · simpa [p, ha] using Ideal.Quotient.eq.mp a.property.2
      · simpa [p, hb] using Ideal.Quotient.eq.mp b.property.2
    · exact mul_eq_zero_of_left ha _
  exact inferInstanceAs (Surjective (Spec.map p))

private lemma exists_unit_chart {K : Type u} [Field K]
    (G : Grp (Over (Spec (.of K)))) :
    ∃ (R : CommRingCat.{u}) (inc : Spec R ⟶ G.X.left), IsOpenImmersion inc ∧
      Set.range (η[G.X].left : Spec (.of K) ⟶ G.X.left) ⊆ Set.range inc := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := G.X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (η[G.X].left (default : Spec (.of K)))) isOpen_univ
  have hAff : IsAffineOpen (X := G.X.left) U := hU
  let inc : Spec Γ(G.X.left, U) ⟶ G.X.left := hAff.isoSpec.inv ≫ Scheme.Opens.ι U
  refine ⟨_, inc, inferInstance, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [Subsingleton.elim (α := Spec (.of K)) x default]
  let w : (↑U : Scheme) := ⟨_, hmem⟩
  refine ⟨hAff.isoSpec.hom w, ?_⟩
  have hcomp : hAff.isoSpec.hom ≫ inc = Scheme.Opens.ι U := by simp [inc]
  calc
    _ = (hAff.isoSpec.hom ≫ inc) w := (Scheme.Hom.comp_apply _ _ w).symm
    _ = Scheme.Opens.ι U w := congrArg (fun g : (↑U : Scheme) ⟶ G.X.left ↦ g w) hcomp
    _ = _ := rfl

private lemma tripleRing_spec_hom_ext {B R : CommRingCat.{u}} (I : Ideal B)
    {f g : Spec (.of (squareZeroTriple I)) ⟶ Spec R}
    (h₁ : Spec.map (CommRingCat.ofHom (tripleFst I)) ≫ f =
      Spec.map (CommRingCat.ofHom (tripleFst I)) ≫ g)
    (h₂ : Spec.map (CommRingCat.ofHom (tripleSnd I)) ≫ f =
      Spec.map (CommRingCat.ofHom (tripleSnd I)) ≫ g)
    (h₃ : Spec.map (CommRingCat.ofHom (tripleTrd I)) ≫ f =
      Spec.map (CommRingCat.ofHom (tripleTrd I)) ≫ g) : f = g := by
  obtain ⟨f', rfl⟩ := Spec.map_surjective f
  obtain ⟨g', rfl⟩ := Spec.map_surjective g
  simp only [← Spec.map_comp] at h₁ h₂ h₃
  congr 1
  apply CommRingCat.hom_ext
  exact triple_ringHom_ext (congrArg CommRingCat.Hom.hom (Spec.map_injective h₁))
    (congrArg CommRingCat.Hom.hom (Spec.map_injective h₂))
    (congrArg CommRingCat.Hom.hom (Spec.map_injective h₃))

private abbrev quotientPointHom {S : Scheme.{u}} {B : CommRingCat.{u}} (t : Spec B ⟶ S)
    (I : Ideal B) :
    Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ⟶ Over.mk t :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

private abbrev reductionKernel {S : Scheme.{u}} (G : Grp (Over S)) {B : CommRingCat.{u}}
    (t : Spec B ⟶ S) (I : Ideal B) : Subgroup (Over.mk t ⟶ G.X) :=
  ((yonedaGrp.obj G).map (quotientPointHom t I).op).hom.ker

private lemma reduction_point_eq_one {S : Scheme.{u}} (G : Grp (Over S))
    {B : CommRingCat.{u}} (t : Spec B ⟶ S) (I : Ideal B) (x : reductionKernel G t I) :
    quotientPointHom t I ≫ (x : Over.mk t ⟶ G.X) = 1 :=
  MonoidHom.mem_ker.mp x.property

private lemma coordinate_eq_mod {S : Scheme.{u}} (G : Grp (Over S))
    {B R : CommRingCat.{u}} {t : Spec B ⟶ S} {I : Ideal B} {x : reductionKernel G t I}
    (inc : Spec R ⟶ G.X.left) [Mono inc] {a e : R →+* B}
    (ha : Spec.map (CommRingCat.ofHom a) ≫ inc = (x : Over.mk t ⟶ G.X).left)
    (he : Spec.map (CommRingCat.ofHom e) ≫ inc = (1 : Over.mk t ⟶ G.X).left) :
    (Ideal.Quotient.mk I).comp a = (Ideal.Quotient.mk I).comp e := by
  apply inc.eq_of_specMap_comp_eq (B := CommRingCat.of (B ⧸ I))
  have h := (reduction_point_eq_one G t I x).trans
    (MonObj.comp_one (M := G.X) (quotientPointHom t I)).symm
  simpa only [Over.comp_left, quotientPointHom, Over.homMk_left,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ha, he] using congrArg Over.Hom.left h

private lemma chart_coordinates {S : Scheme.{u}} (G : Grp (Over S))
    {B R : CommRingCat.{u}} {t : Spec B ⟶ S} {I : Ideal B}
    (hI : I ^ 2 = ⊥) (inc : Spec R ⟶ G.X.left) [IsOpenImmersion inc]
    (hinc : Set.range (1 : Over.mk t ⟶ G.X).left ⊆ Set.range inc)
    (x : reductionKernel G t I) :
    ∃ a : R →+* B, Spec.map (CommRingCat.ofHom a) ≫ inc = (x : Over.mk t ⟶ G.X).left := by
  apply inc.exists_specMap_comp_eq_of_range_subset
  let j := quotientPointHom t I
  have : IsFirstOrderThickening j.left :=
    IsFirstOrderThickening.SpecMap_quotient_mk hI
  have h := (reduction_point_eq_one G t I x).trans (MonObj.comp_one (M := G.X) j).symm
  calc
    Set.range (x : Over.mk t ⟶ G.X).left = Set.range (j ≫ (x : Over.mk t ⟶ G.X)).left :=
      (range_eq_range_of_surjective _ _ j.left (by simp only [Over.comp_left])).symm
    _ = Set.range (1 : Over.mk t ⟶ G.X).left :=
      range_eq_range_of_surjective _ _ j.left (by
        simpa only [Over.comp_left] using congrArg Over.Hom.left h.symm)
    _ ⊆ Set.range inc := hinc

private lemma chart_point_eq_of_coord {S : Scheme.{u}} (G : Grp (Over S))
    {B R : CommRingCat.{u}} {t : Spec B ⟶ S} {I : Ideal B}
    (inc : Spec R ⟶ G.X.left) (c : reductionKernel G t I → R →+* B)
    (hc : ∀ x, Spec.map (CommRingCat.ofHom (c x)) ≫ inc = (x : Over.mk t ⟶ G.X).left) :
    Function.Injective c := by
  intro x y h
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [← hc x, ← hc y, h]

private abbrev tripleDiagonal {B : Type u} [CommRing B] (I : Ideal B) :
    B →+* squareZeroTriple I :=
  tripleLift I (RingHom.id B) (RingHom.id B) (RingHom.id B) rfl rfl

private abbrev tripleBase {S : Scheme.{u}} {B : CommRingCat.{u}}
    (t : Spec B ⟶ S) (I : Ideal B) : Spec (CommRingCat.of (squareZeroTriple I)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (tripleDiagonal I)) ≫ t

private noncomputable def overTripleMap {S : Scheme.{u}} {B : CommRingCat.{u}}
    (t : Spec B ⟶ S) (I : Ideal B) (p : squareZeroTriple I →+* B)
    (hp : p.comp (tripleDiagonal I) = RingHom.id B) :
    Over.mk t ⟶ Over.mk (tripleBase t I) :=
  Over.homMk (Spec.map (CommRingCat.ofHom p)) (by
    simp only [Over.mk_hom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      hp, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp t)

private abbrev triplePointFst {S : Scheme.{u}} {B : CommRingCat.{u}}
    (t : Spec B ⟶ S) (I : Ideal B) : Over.mk t ⟶ Over.mk (tripleBase t I) :=
  overTripleMap t I (tripleFst I) rfl

private abbrev triplePointSnd {S : Scheme.{u}} {B : CommRingCat.{u}}
    (t : Spec B ⟶ S) (I : Ideal B) : Over.mk t ⟶ Over.mk (tripleBase t I) :=
  overTripleMap t I (tripleSnd I) rfl

private abbrev triplePointTrd {S : Scheme.{u}} {B : CommRingCat.{u}}
    (t : Spec B ⟶ S) (I : Ideal B) : Over.mk t ⟶ Over.mk (tripleBase t I) :=
  overTripleMap t I (tripleTrd I) rfl

private lemma exists_triple_point {A B R : CommRingCat.{u}}
    (G : Grp (Over (Spec A))) {t : Spec B ⟶ Spec A} (I : Ideal B) (inc : Spec R ⟶ G.X.left)
    {x y z : Over.mk t ⟶ G.X} {a b c : R →+* B}
    (ha : Spec.map (CommRingCat.ofHom a) ≫ inc = x.left)
    (hb : Spec.map (CommRingCat.ofHom b) ≫ inc = y.left)
    (hc : Spec.map (CommRingCat.ofHom c) ≫ inc = z.left)
    (h₁ : (Ideal.Quotient.mk I).comp a = (Ideal.Quotient.mk I).comp c)
    (h₂ : (Ideal.Quotient.mk I).comp b = (Ideal.Quotient.mk I).comp c) :
    ∃ p : Over.mk (tripleBase t I) ⟶ G.X,
      p.left = Spec.map (CommRingCat.ofHom (tripleLift I a b c h₁ h₂)) ≫ inc ∧
      triplePointFst t I ≫ p = x ∧ triplePointSnd t I ≫ p = y ∧
      triplePointTrd t I ≫ p = z := by
  let f := Spec.map (CommRingCat.ofHom (tripleLift I a b c h₁ h₂)) ≫ inc
  have hf₁ : (triplePointFst t I).left ≫ f = x.left := by
    simp only [f, ← Category.assoc, triplePointFst, overTripleMap, Over.homMk_left,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact ha
  have hf₂ : (triplePointSnd t I).left ≫ f = y.left := by
    simp only [f, ← Category.assoc, triplePointSnd, overTripleMap, Over.homMk_left,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact hb
  have hf₃ : (triplePointTrd t I).left ≫ f = z.left := by
    simp only [f, ← Category.assoc, triplePointTrd, overTripleMap, Over.homMk_left,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact hc
  have hbase : f ≫ G.X.hom = tripleBase t I := by
    apply tripleRing_spec_hom_ext I
    · calc
        _ = t := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.X.hom) hf₁).trans (Over.w x))
        _ = _ := (Over.w (triplePointFst t I)).symm
    · calc
        _ = t := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.X.hom) hf₂).trans (Over.w y))
        _ = _ := (Over.w (triplePointSnd t I)).symm
    · calc
        _ = t := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.X.hom) hf₃).trans (Over.w z))
        _ = _ := (Over.w (triplePointTrd t I)).symm
  exact ⟨Over.homMk f hbase, rfl, Over.OverMorphism.ext hf₁, Over.OverMorphism.ext hf₂,
    Over.OverMorphism.ext hf₃⟩

private lemma comp_chart {S : Scheme.{u}} (G : Grp (Over S))
    {B R : CommRingCat.{u}} {t : Spec B ⟶ S} {I : Ideal B}
    (inc : Spec R ⟶ G.X.left) {p : Over.mk (tripleBase t I) ⟶ G.X}
    {a : R →+* squareZeroTriple I} (ha : p.left = Spec.map (CommRingCat.ofHom a) ≫ inc)
    (f : squareZeroTriple I →+* B) (hf : f.comp (tripleDiagonal I) = RingHom.id B) :
    (overTripleMap t I f hf ≫ p).left =
      Spec.map (CommRingCat.ofHom (f.comp a)) ≫ inc := by
  simp only [Over.comp_left, overTripleMap, Over.homMk_left, ha, ← Category.assoc,
    CommRingCat.ofHom_comp, Spec.map_comp]

private lemma tripleCombine_comp_tripleDiagonal {B : Type u} [CommRing B] (I : Ideal B)
    (hI : I ^ 2 = ⊥) (a b : B) :
    (tripleCombine I hI a b).comp (tripleDiagonal I) = RingHom.id B := by
  apply RingHom.ext
  intro x
  -- Each coordinate of the diagonal is the original input.
  change x + a * (x - x) + b * (x - x) = x
  ring

private lemma combine_tripleLift_left {R B : Type u} [CommRing R] [CommRing B]
    {I : Ideal B} (hI : I ^ 2 = ⊥) {a e : R →+* B}
    (h : (Ideal.Quotient.mk I).comp a = (Ideal.Quotient.mk I).comp e) :
    (tripleCombine I hI 1 1).comp (tripleLift I a e e h rfl) = a := by
  apply RingHom.ext
  intro r
  -- The second correction vanishes on this lift.
  change e r + 1 * (a r - e r) + 1 * (e r - e r) = a r
  ring

private lemma combine_tripleLift_right {R B : Type u} [CommRing R] [CommRing B]
    {I : Ideal B} (hI : I ^ 2 = ⊥) {a e : R →+* B}
    (h : (Ideal.Quotient.mk I).comp a = (Ideal.Quotient.mk I).comp e) :
    (tripleCombine I hI 1 1).comp (tripleLift I e a e rfl h) = a := by
  apply RingHom.ext
  intro r
  -- The first correction vanishes on this lift.
  change e r + 1 * (e r - e r) + 1 * (a r - e r) = a r
  ring

private lemma chart_coordinates_mul {A B R : CommRingCat.{u}}
    (G : Grp (Over (Spec A))) {t : Spec B ⟶ Spec A} {I : Ideal B} (hI : I ^ 2 = ⊥)
    (inc : Spec R ⟶ G.X.left) [IsOpenImmersion inc]
    (c : reductionKernel G t I → R →+* B)
    (hc : ∀ x, Spec.map (CommRingCat.ofHom (c x)) ≫ inc = (x : Over.mk t ⟶ G.X).left)
    (x y : reductionKernel G t I) (r : R) :
    c (x * y) r - c 1 r = (c x r - c 1 r) + (c y r - c 1 r) := by
  have hx := coordinate_eq_mod G inc (hc x) (hc 1)
  have hy := coordinate_eq_mod G inc (hc y) (hc 1)
  obtain ⟨p, hp, hp₁, hp₂, hp₃⟩ := exists_triple_point G I inc (hc x) (hc 1) (hc 1) hx rfl
  obtain ⟨q, hq, hq₁, hq₂, hq₃⟩ := exists_triple_point G I inc (hc 1) (hc y) (hc 1) rfl hy
  have h₁ : triplePointFst t I ≫ (p * q) = x := by simp [MonObj.comp_mul, hp₁, hq₁]
  have h₂ : triplePointSnd t I ≫ (p * q) = y := by simp [MonObj.comp_mul, hp₂, hq₂]
  have h₃ : triplePointTrd t I ≫ (p * q) = 1 := by simp [MonObj.comp_mul, hp₃, hq₃]
  have : Surjective (triplePointTrd t I).left := surjective_specMap_tripleTrd I hI
  have hrange : Set.range (p * q).left ⊆ Set.range inc := by
    have h : (triplePointTrd t I).left ≫ (p * q).left =
        Spec.map (CommRingCat.ofHom (c 1)) ≫ inc := by
      simpa only [Over.comp_left] using (congrArg Over.Hom.left h₃).trans (hc 1).symm
    rw [← range_eq_range_of_surjective _ _ _ h]
    simp only [Set.range_subset_iff, Scheme.Hom.comp_apply]
    exact fun _ ↦ Set.mem_range_self _
  obtain ⟨d, hd⟩ := inc.exists_specMap_comp_eq_of_range_subset (p * q).left hrange
  have hd₁ : (tripleFst I).comp d = c x :=
    inc.eq_of_specMap_comp_eq ((comp_chart G inc hd.symm _ rfl).symm.trans
      ((congrArg Over.Hom.left h₁).trans (hc x).symm))
  have hd₂ : (tripleSnd I).comp d = c y :=
    inc.eq_of_specMap_comp_eq ((comp_chart G inc hd.symm _ rfl).symm.trans
      ((congrArg Over.Hom.left h₂).trans (hc y).symm))
  have hd₃ : (tripleTrd I).comp d = c 1 :=
    inc.eq_of_specMap_comp_eq ((comp_chart G inc hd.symm _ rfl).symm.trans
      ((congrArg Over.Hom.left h₃).trans (hc 1).symm))
  let f := tripleCombine I hI 1 1
  let j := overTripleMap t I f (tripleCombine_comp_tripleDiagonal I hI 1 1)
  have hpx : j ≫ p = x := Over.OverMorphism.ext (by
    rw [comp_chart G inc hp, combine_tripleLift_left hI hx, hc x])
  have hqy : j ≫ q = y := Over.OverMorphism.ext (by
    rw [comp_chart G inc hq, combine_tripleLift_right hI hy, hc y])
  have heq : f.comp d = c (x * y) := inc.eq_of_specMap_comp_eq (by
    rw [← comp_chart G inc hd.symm f (tripleCombine_comp_tripleDiagonal I hI 1 1),
      MonObj.comp_mul, hpx, hqy, hc, Subgroup.coe_mul])
  rw [← heq]
  -- Read the three solved coordinate maps in the formula defining the combining map.
  change (tripleTrd I).comp d r + 1 * ((tripleFst I).comp d r - (tripleTrd I).comp d r) +
    1 * ((tripleSnd I).comp d r - (tripleTrd I).comp d r) - c 1 r = _
  rw [hd₁, hd₂, hd₃]
  ring

private lemma exists_scaled_coordinates {A B R : CommRingCat.{u}}
    (G : Grp (Over (Spec A))) {t : Spec B ⟶ Spec A} {I : Ideal B} (hI : I ^ 2 = ⊥)
    (inc : Spec R ⟶ G.X.left) [IsOpenImmersion inc]
    (c : reductionKernel G t I → R →+* B)
    (hc : ∀ x, Spec.map (CommRingCat.ofHom (c x)) ≫ inc = (x : Over.mk t ⟶ G.X).left)
    (a : B) (x : reductionKernel G t I) :
    ∃ y : reductionKernel G t I, ∀ r, c y r - c 1 r = a * (c x r - c 1 r) := by
  have hx := coordinate_eq_mod G inc (hc x) (hc 1)
  obtain ⟨p, hp, -, -, -⟩ := exists_triple_point G I inc (hc x) (hc 1) (hc 1) hx rfl
  let f := tripleCombine I hI a 0
  let j := overTripleMap t I f (tripleCombine_comp_tripleDiagonal I hI a 0)
  let d := f.comp (tripleLift I (c x) (c 1) (c 1) hx rfl)
  have hd : (j ≫ p).left = Spec.map (CommRingCat.ofHom d) ≫ inc :=
    comp_chart G inc hp f _
  have hmod : (Ideal.Quotient.mk I).comp d = (Ideal.Quotient.mk I).comp (c 1) := by
    apply RingHom.ext
    intro r
    -- The coordinate correction has zero image modulo the ideal.
    change Ideal.Quotient.mk I (c 1 r + a * (c x r - c 1 r) +
      0 * (c 1 r - c 1 r)) = Ideal.Quotient.mk I (c 1 r)
    have he := RingHom.congr_fun hx r
    simp only [RingHom.comp_apply] at he
    simp [he]
  have hred : quotientPointHom t I ≫ (j ≫ p) = 1 := by
    rw [← MonObj.comp_one (quotientPointHom t I)]
    apply Over.OverMorphism.ext
    have he : Spec.map (CommRingCat.ofHom (c 1)) ≫ inc = (1 : Over.mk t ⟶ G.X).left := hc 1
    -- Preserve the composite over the larger test ring to apply its coordinate formula.
    change (quotientPointHom t I).left ≫ (j ≫ p).left =
      (quotientPointHom t I).left ≫ (1 : Over.mk t ⟶ G.X).left
    rw [hd, ← he]
    simp only [quotientPointHom, Over.homMk_left, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hmod]
  let y : reductionKernel G t I := ⟨j ≫ p, MonoidHom.mem_ker.mpr hred⟩
  refine ⟨y, fun r ↦ ?_⟩
  have heq : c y = d := inc.eq_of_specMap_comp_eq ((hc y).trans hd)
  rw [heq]
  -- Only the first correction is scaled by the combining map.
  change c 1 r + a * (c x r - c 1 r) + 0 * (c 1 r - c 1 r) - c 1 r = _
  ring

/-- If an integer is a unit on an affine test scheme, multiplication by it is bijective on the
kernel of reduction of points of a group scheme over a square-zero ideal. -/
public theorem bijective_zpow_ker_squareZero {K : Type u} [Field K]
    (G : Grp (Over (Spec (.of K)))) {B : CommRingCat.{u}} (t : Spec B ⟶ Spec (.of K))
    (I : Ideal B) (hI : I ^ 2 = ⊥) (n : ℤ) (hn : IsUnit (n : B)) :
    let j : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ⟶ Over.mk t :=
      Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    Function.Bijective (fun x : ((yonedaGrp.obj G).map j.op).hom.ker ↦ x ^ n) := by
  -- Name the subgroup in the statement using the same abbreviation as the coordinate lemmas.
  change Function.Bijective (fun x : reductionKernel G t I ↦ x ^ n)
  obtain ⟨R, inc, hinc, hrange⟩ := exists_unit_chart G
  have he : Set.range (1 : Over.mk t ⟶ G.X).left ⊆ Set.range inc := by
    rintro _ ⟨w, rfl⟩
    apply hrange
    -- The identity-valued point is the structure map followed by the unit section.
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left, Scheme.Hom.comp_apply]
    exact ⟨t w, rfl⟩
  choose c hc using chart_coordinates G hI inc he
  let D : reductionKernel G t I →* Multiplicative (R → B) :=
    { toFun := fun x ↦ Multiplicative.ofAdd (fun r ↦ c x r - c 1 r)
      map_one' := by ext r; exact sub_self _
      map_mul' := fun x y ↦ by
        ext r
        exact chart_coordinates_mul G hI inc c hc x y r }
  have hpow (x : reductionKernel G t I) (r : R) :
      c (x ^ n) r - c 1 r = (n : B) * (c x r - c 1 r) := by
    have h := congrArg (fun d : Multiplicative (R → B) ↦ d.toAdd r) (D.map_zpow x n)
    simpa only [D, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
      toAdd_zpow, Pi.smul_apply, zsmul_eq_mul] using h
  have hinj := chart_point_eq_of_coord G inc c hc
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hinj
    apply RingHom.ext
    intro r
    have he : c x r - c 1 r = c y r - c 1 r := by
      apply hn.mul_right_injective
      exact (hpow x r).symm.trans
        ((congrArg (fun z : reductionKernel G t I ↦ c z r - c 1 r) hxy).trans (hpow y r))
    exact sub_left_inj.mp he
  · intro x
    obtain ⟨u, hu⟩ := hn
    obtain ⟨y, hy⟩ := exists_scaled_coordinates G hI inc c hc (↑u⁻¹ : B) x
    refine ⟨y, hinj ?_⟩
    apply RingHom.ext
    intro r
    have he : c (y ^ n) r - c 1 r = c x r - c 1 r := by
      rw [hpow, hy, ← hu, ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul]
    exact sub_left_inj.mp he

end

end TauCeti.GroupScheme
