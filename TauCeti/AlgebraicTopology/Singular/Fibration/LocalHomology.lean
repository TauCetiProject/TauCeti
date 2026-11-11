/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk

/-!
# Homology of a Serre fibration relative to the complement of a fibre

Let `p : E → B` be a Serre fibration over a `T₁` space `B`, and let `b` be a point in the source
of an open partial homeomorphism `φ : B → V` to a real normed space `V` of finite dimension `r`,
such as a chart of a topological manifold modelled on `V`. Write `F_b = p⁻¹(b)` for the fibre over
`b`. With coefficients in a ring `R`, the relative singular homology of `E` modulo the complement
of the fibre is the homology of the fibre, shifted up by `r`:

* `Hₘ(E, E ∖ F_b; R) = 0` for `m < r`
  (`TauCeti.TopCat.isZero_singularHomology_complFiber_of_lt`);
* `Hₙ₊ᵣ(E, E ∖ F_b; R) ≅ Hₙ(F_b; R)`
  (`TauCeti.TopCat.singularHomologyComplFiberIsoOfChart`).

For the identity of `B` the fibre is the point `b`, and the statement reduces to the computation
of the local homology `Hₖ(B, B ∖ {b})` in `TauCeti.singularHomologyComplSingletonIsoOfChart` and
`TauCeti.isZero_singularHomology_complSingleton_of_ne`. For a fibration over a closed oriented
`r`-manifold, Barraud–Damian–Humilière–Oancea (Lemma 2.9) identify the restriction
`Hₘ(E) → Hₘ(E, E ∖ F_b)`, followed by an isomorphism `Hₘ(E, E ∖ F_b) ≅ Hₘ₋ᵣ(F_b)` of this kind,
with the shriek map of the inclusion of the point `b`; a class of `Hₘ(E)` lives over the
fundamental class of the base (their Definition 2.3 and Example 2.4) when this image is nonzero.
That comparison with their Morse-theoretic shriek map is not made here.

## The argument

The fibre `F_b` is closed, since `B` is `T₁`. Choose a ball `D` about `φ b` inside the target of
`φ`, and let `U = φ.source ∩ φ⁻¹(D)`, an open neighbourhood of `b`. By excision
(`TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset`), the pair `(E, E ∖ F_b)` may
be replaced by `(p⁻¹(U), p⁻¹(U) ∖ F_b)`. Over `U`, the fibration `p` restricts to a Serre fibration,
and the homeomorphism `x ↦ φ x - φ b` of `U` with a ball about `0` turns it into a Serre fibration
over a convex neighbourhood of `0` whose fibre over `0` is `F_b`. Its homology modulo the part over
the punctured ball is computed in `TauCeti.AlgebraicTopology.Singular.Fibration.Disk`
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` and
`TauCeti.TopCat.isZero_singularHomology_preimage_ne_zero`).

## Main results

* `TauCeti.TopCat.isZero_singularHomology_complFiber_of_lt`: `Hₘ(E, E ∖ F_b; R) = 0` below the
  dimension of the chart.
* `TauCeti.TopCat.singularHomologyComplFiberIsoOfChart`: `Hₙ₊ᵣ(E, E ∖ F_b; R) ≅ Hₙ(F_b; R)`, for a
  chosen ball about `φ b` inside the target of `φ`. After excision onto the part of `E` over the
  ball, it is `TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted fibration
  `TauCeti.TopCat.SerreChart.chartFibration`
  (`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIsoOfChart_hom`
  and `TauCeti.TopCat.map_fiberHomeomorph_comp_singularHomologyComplFiberIsoOfChart_inv`).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 2.3 and Lemma 2.9.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Lemma 9.18.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module Set Topology

universe u

namespace TauCeti

namespace TopCat

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} (R : Type u) [Ring R] (φ : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ φ.source)
  {r : ℝ} (hr : ball (φ b) r ⊆ φ.target)

namespace SerreChart

/-- The open neighbourhood `φ.source ∩ φ⁻¹(D)` of `b`, for the ball `D` about `φ b` of radius
`r`. -/
def chartBall (b : B) (r : ℝ) : Set B :=
  φ.source ∩ φ ⁻¹' ball (φ b) r

@[simp]
lemma mem_chartBall {b x : B} {r : ℝ} :
    x ∈ chartBall φ b r ↔ x ∈ φ.source ∧ φ x ∈ ball (φ b) r :=
  Iff.rfl

lemma isOpen_chartBall (b : B) (r : ℝ) : IsOpen (chartBall φ b r) :=
  φ.isOpen_inter_preimage isOpen_ball

include hb in
lemma mem_chartBall_self (hr₀ : 0 < r) : b ∈ chartBall φ b r :=
  ⟨hb, mem_ball_self hr₀⟩

/-- The chart `φ` followed by the translation `v ↦ v - φ b`, which sends `b` to `0`. -/
private def translatedChart (b : B) : OpenPartialHomeomorph B V :=
  φ.trans (Homeomorph.addRight (-φ b)).toOpenPartialHomeomorph

private lemma translatedChart_apply (b x : B) : translatedChart φ b x = φ x - φ b :=
  (sub_eq_add_neg _ _).symm

include hr in
private lemma image_translatedChart_chartBall :
    translatedChart φ b '' chartBall φ b r = ball (0 : V) r := by
  ext v
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    rw [translatedChart_apply, mem_ball_zero_iff, ← dist_eq_norm]
    exact hx.2
  · have hv' : v + φ b ∈ ball (φ b) r := by
      rwa [mem_ball, dist_eq_norm, add_sub_cancel_right, ← mem_ball_zero_iff]
    exact ⟨φ.symm (v + φ b), ⟨φ.map_target (hr hv'), by rwa [mem_preimage, φ.right_inv (hr hv')]⟩,
      by rw [translatedChart_apply, φ.right_inv (hr hv'), add_sub_cancel_right]⟩

/-- The restriction of `p` over `chartBall φ b r`, read in the ball about `0` through
`x ↦ φ x - φ b`. -/
def chartFibration (p : E ⟶ B) :
    _root_.TopCat.of (p ⁻¹' chartBall φ b r) ⟶ _root_.TopCat.of (ball (0 : V) r) :=
  _root_.TopCat.ofHom (p.hom.restrictPreimage (chartBall φ b r)) ≫
    (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (chartBall φ b r))
      ((translatedChart φ b).homeomorphOfImageSubsetSource
        (fun _ hx ↦ ⟨(hx : _ ∈ chartBall φ b r).1, trivial⟩)
        (image_translatedChart_chartBall φ hr))).hom

lemma coe_chartFibration_apply (z : _root_.TopCat.of (p ⁻¹' chartBall φ b r)) :
    (chartFibration φ hr p z : V) = φ (p z) - φ b :=
  translatedChart_apply φ b (p z)

include hb in
/-- A point over `chartBall φ b r` lies over `0` in the ball exactly when it lies over `b`. -/
lemma coe_chartFibration_eq_zero_iff (z : _root_.TopCat.of (p ⁻¹' chartBall φ b r)) :
    (chartFibration φ hr p z : V) = 0 ↔ p z = b := by
  rw [coe_chartFibration_apply, sub_eq_zero]
  exact φ.injOn.eq_iff z.2.1 hb

lemma mem_serreFibrations_chartFibration (hp : serreFibrations p) :
    serreFibrations (chartFibration φ hr p) :=
  serreFibrations.comp_mem _ _ (mem_serreFibrations_restrictPreimage hp _)
    (serreFibrations.of_isIso _)

/-- Over `chartBall φ b r`, the complement of the fibre over `b` is the part over the punctured
ball. -/
def interPairIso :
    TopPair.interPair (X := E) (p ⁻¹' chartBall φ b r) (p ⁻¹' {b})ᶜ ≅
      TopPair.ofSubset (chartFibration φ hr p ⁻¹' {x | (x : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦ by
    exact (coe_chartFibration_eq_zero_iff φ hb hr z).not.symm

/-- The forward map of `interPairIso` is induced by the identity of `p⁻¹(chartBall φ b r)`. -/
lemma interPairIso_hom :
    (interPairIso (p := p) φ hb hr).hom =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' chartBall φ b r)))
        fun z hz ↦ by exact (coe_chartFibration_eq_zero_iff φ hb hr z).not.2 hz := by
  unfold interPairIso
  exact TopPair.ofSubsetIso_hom _ _

/-- The inverse map of `interPairIso` is induced by the identity of `p⁻¹(chartBall φ b r)`. -/
lemma interPairIso_inv :
    (interPairIso (p := p) φ hb hr).inv =
      TopPair.ofSubsetMap (_root_.TopCat.ofHom (Homeomorph.refl (p ⁻¹' chartBall φ b r)))
        fun z hz ↦ by exact (coe_chartFibration_eq_zero_iff φ hb hr z).not.1 hz := by
  unfold interPairIso
  exact TopPair.ofSubsetIso_inv _ _

/-- The fibre over `0` of `chartFibration φ hr p` is the fibre of `p` over `b`. -/
def fiberHomeomorph (hr₀ : 0 < r) :
    (chartFibration φ hr p ⁻¹' {x | (x : V) = 0}) ≃ₜ (p ⁻¹' {b}) where
  toFun z := ⟨z.1.1, (φ.injOn.eq_iff z.1.2.1 hb).1 <|
    sub_eq_zero.1 <| by
      rw [← coe_chartFibration_apply φ hr]
      exact z.2⟩
  invFun y :=
    have hy : p y.1 = b := y.2
    ⟨⟨y.1, by
      rw [mem_preimage, hy]
      exact mem_chartBall_self φ hb hr₀⟩, by
      rw [mem_preimage, mem_ofPred_eq, coe_chartFibration_apply]
      exact sub_eq_zero.2 (congrArg φ hy)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma coe_fiberHomeomorph_apply (hr₀ : 0 < r) (z : chartFibration φ hr p ⁻¹' {x | (x : V) = 0}) :
    (fiberHomeomorph φ hb hr hr₀ z : E) = z.1.1 :=
  (rfl)

lemma coe_fiberHomeomorph_symm_apply (hr₀ : 0 < r) (y : p ⁻¹' {b}) :
    ((fiberHomeomorph φ hb hr hr₀).symm y).1.1 = y.1 :=
  (rfl)

variable [T1Space B]

/-- Excision onto the part of `E` over `chartBall φ b r`, followed by `interPairIso`. -/
private def excisionIso (hr₀ : 0 < r) (m : ℕ) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      (TopPair.ofSubset (chartFibration φ hr p ⁻¹' {x | (x : V) ≠ 0})).singularHomology
        (ModuleCat.of R R) m :=
  haveI := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) ((isOpen_chartBall φ b r).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (mem_chartBall_self φ hb hr₀))) m
  (asIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' chartBall φ b r) (p ⁻¹' {b})ᶜ) _ m)).symm ≪≫
    asIso (TopPair.singularHomologyMap (interPairIso φ hb hr).hom _ m)

end SerreChart

open SerreChart

variable [T1Space B] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include φ hb in
/-- **The homology of a Serre fibration modulo the complement of a fibre vanishes below the
dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the source
of an open partial homeomorphism `φ : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); R) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complFiber_of_lt (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m) := by
  obtain ⟨r, hr₀, hr⟩ := Metric.isOpen_iff.1 φ.open_target (φ b) (φ.map_source hb)
  exact (isZero_singularHomology_preimage_ne_zero R (mem_serreFibrations_chartFibration φ hr hp)
    (convex_ball 0 _) (ball_mem_nhds 0 hr₀) hm).of_iso (excisionIso R φ hb hr hr₀ m)

/-- **The homology of a Serre fibration modulo the complement of a fibre is the shifted homology
of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the
source of an open partial homeomorphism `φ : B → V` to a real normed space of finite dimension `r`,
such as the chart `chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` for `m = n + r`.

The isomorphism depends on a ball of radius `r` about `φ b` inside the target of `φ`: it is
excision onto the part of `E` over `TauCeti.TopCat.SerreChart.chartBall φ b r`, followed by
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restriction of `p` over that set
(`TauCeti.TopCat.singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIsoOfChart_hom`). -/
def singularHomologyComplFiberIsoOfChart (hr₀ : 0 < r) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  excisionIso R φ hb hr hr₀ m ≪≫
    singularHomologyPreimageNeZeroIso R (mem_serreFibrations_chartFibration φ hr hp)
      (convex_ball 0 _) (ball_mem_nhds 0 hr₀) n m h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (fiberHomeomorph φ hb hr hr₀))

/-- The isomorphism `TauCeti.TopCat.singularHomologyComplFiberIsoOfChart` commutes with excision
onto the part of `E` over `TauCeti.TopCat.SerreChart.chartBall φ b r`: after excision it is
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` for the restricted fibration, followed by the
identification of its fibre over `0` with the fibre over `b`. -/
@[reassoc]
lemma singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIsoOfChart_hom
    (hr₀ : 0 < r) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap
        (TopPair.excisionMap (X := E) (p ⁻¹' chartBall φ b r) (p ⁻¹' {b})ᶜ)
        (ModuleCat.of R R) m ≫
        (singularHomologyComplFiberIsoOfChart R φ hb hr hr₀ hp n m h).hom =
      TopPair.singularHomologyMap (interPairIso φ hb hr).hom (ModuleCat.of R R) m ≫
        (singularHomologyPreimageNeZeroIso R (mem_serreFibrations_chartFibration φ hr hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hr₀) n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.isoOfHomeo (fiberHomeomorph φ hb hr hr₀)).hom := by
  simp [singularHomologyComplFiberIsoOfChart, excisionIso]

/-- The inverse of `TauCeti.TopCat.singularHomologyComplFiberIsoOfChart`, after the identification
of the fibre over `b` with the fibre over `0` of the restricted fibration, is the inverse of
`TauCeti.TopCat.singularHomologyPreimageNeZeroIso` followed by excision. -/
@[reassoc]
lemma map_fiberHomeomorph_comp_singularHomologyComplFiberIsoOfChart_inv
    (hr₀ : 0 < r) (hp : serreFibrations p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.isoOfHomeo (fiberHomeomorph φ hb hr hr₀)).hom ≫
        (singularHomologyComplFiberIsoOfChart R φ hb hr hr₀ hp n m h).inv =
      (singularHomologyPreimageNeZeroIso R (mem_serreFibrations_chartFibration φ hr hp)
          (convex_ball 0 _) (ball_mem_nhds 0 hr₀) n m h).inv ≫
        TopPair.singularHomologyMap (interPairIso φ hb hr).inv (ModuleCat.of R R) m ≫
        TopPair.singularHomologyMap
          (TopPair.excisionMap (X := E) (p ⁻¹' chartBall φ b r) (p ⁻¹' {b})ᶜ)
          (ModuleCat.of R R) m := by
  rw [Iso.comp_inv_eq, Category.assoc, Category.assoc,
    singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIsoOfChart_hom,
    ← TopPair.singularHomologyMap_comp_assoc, Iso.inv_hom_id, TopPair.singularHomologyMap_id,
    Category.id_comp, Iso.inv_hom_id_assoc]

end TopCat

end TauCeti
