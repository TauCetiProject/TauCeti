/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.AlgebraicTopology.Singular.Fibration.NormalCoordinate
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.OpenPartialHomeomorph.Ball

/-!
# Local homology of a Serre fibration along a fibre

Let `p : E → B` be a Serre fibration over a `T₁` space `B` and `b` a point of `B` in the source
of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`, such
as a chart of a topological manifold modelled on `V`. The **local homology of `E` along the
fibre** `F = p⁻¹(b)` is the relative singular homology `Hₖ(E, E ∖ F)`. This file computes it,
with coefficients in a module `M` over a ring `R`:

* `Hₘ(E, E ∖ F; M) = 0` for `m < r` (`TauCeti.TopCat.isZero_singularHomology_complFiber`);
* `Hₙ₊ᵣ(E, E ∖ F; M) ≅ Hₙ(F; M)` (`TauCeti.TopCat.singularHomologyComplFiberIso`).

For the identity of `B` this is the local homology of `B` at `b`
(`TauCeti.singularHomologyComplSingletonFinrankIso`). The composite
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` is a shriek map `j_!` of the inclusion `j` of the point `b`,
with untwisted coefficients on the total space. Barraud, Damian, Humilière and Oancea read their
`j_!` through `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E|_{B'}) ≅ Hₙ(F)`, where `B'` is the `(r - 1)`-skeleton of a CW
structure on `B` with a single top cell containing `b` (their Proposition 2.6), and use it to
detect classes **living over the fundamental class** of the base. A class `α ∈ Hₖ(E)` lives over
the fundamental class at `b` when its localization in `Hₖ(E, E ∖ F)` is nonzero
(`TauCeti.LivesOverFundamentalClass`). For a Serre fibration this happens exactly when
`j_! α ≠ 0` (`TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`), and
only in degrees at least `r` (`TauCeti.LivesOverFundamentalClass.finrank_le`).

The identification is natural in maps of fibrations: for a second Serre fibration
`p' : E' ⟶ B` and a map `f : E ⟶ E'` over `B`, the map induced by `f` on `Hₙ₊ᵣ(E, E ∖ F)` becomes,
for the same chart and ball, the map induced on `Hₙ(F)` by the restriction `F ⟶ F'` of `f` to the
fibres (`TauCeti.TopCat.singularHomologyComplFiberIso_hom_naturality`). So the shriek maps commute
with `f`, `j_! ∘ f_* = f_* ∘ j_!` (the source's Proposition 2.12), and `f_* α` lives over the
fundamental class exactly when `f_* (j_! α) ≠ 0`
(`TauCeti.livesOverFundamentalClass_homologyMap_iff`). This is the step of the source's
Corollary 2.13 that passes from a nonvanishing class of the fibre to a class of the total space
living over the fundamental class.

The relative group, rather than the shriek map itself, is used in the definition because it does
not depend on the chart: the identification `Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` depends on the chart. Its
construction `TauCeti.TopCat.singularHomologyComplFiberIso` takes a ball in the target of the
chart as an explicit argument.

## The computation

Choose a ball of positive radius `ε` about `e b` inside the target of `e`, and let `U` be its
preimage in the source of `e` (`OpenPartialHomeomorph.chartBall`), an open neighbourhood of `b`.
The homeomorphism `x ↦ e x - e b` of `U` with the ball of radius `ε` about `0`
(`OpenPartialHomeomorph.chartBallHomeomorph`) is a normal coordinate of the closed point `b`: it
vanishes exactly at `b` (`OpenPartialHomeomorph.chartBallHomeomorph_eq_zero_iff`). The local
homology along `F` is therefore the local homology along the zero set of a normal coordinate
(`TauCeti.TopCat.singularHomologyComplPreimageIso`), which is computed by excision onto `p⁻¹(U)`
and the homology of a Serre fibration over a ball modulo the part over the punctured ball.

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplFiberIso`: `Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))`,
  constructed from a ball about `e b` inside the target of `e`, as the local homology along the
  zero set of the chart coordinate (`TauCeti.TopCat.singularHomologyComplFiberIso_def`).
* `TauCeti.TopCat.isZero_singularHomology_complFiber`: `Hₘ(E, E ∖ p⁻¹(b)) = 0` for `m < r`.
* `TauCeti.livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero`: a class lives
  over the fundamental class exactly when its image in `Hₖ₋ᵣ(p⁻¹(b))` is nonzero.
* `TauCeti.LivesOverFundamentalClass.finrank_le`: such a class has degree at least `r`.
* `OpenPartialHomeomorph.chartBallTrivialization`: a trivialization of `p` over the chart ball
  identifies the part of `E` over it with the product of the ball of radius `ε` about `0` and the
  fibre, compatibly with the chart coordinate read through
  `TauCeti.TopCat.normalCoordinateProj` (`OpenPartialHomeomorph.chartBallTrivialization_apply_fst`).
* `TauCeti.TopCat.singularHomologyComplFiberIso_hom_naturality`: the identification is natural in
  maps of fibrations over `B`.
* `TauCeti.homologyMap_comp_fiberLocalization_comp_singularHomologyComplFiberIso_hom`: the shriek
  map of the inclusion of `b` commutes with maps of fibrations over `B`.
* `TauCeti.livesOverFundamentalClass_homologyMap_iff`: the image of a class under a map of
  fibrations lives over the fundamental class exactly when the image of its shriek is nonzero.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Definition 2.3, Example 2.4,
  Proposition 2.6, Proposition 2.12 and Corollary 2.13.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology

universe u

namespace OpenPartialHomeomorph

variable {V : Type u} [SeminormedAddCommGroup V] {B : _root_.TopCat.{u}}
  (e : OpenPartialHomeomorph B V) {b : B} {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

/-- The chart coordinate `x ↦ e x - e b` on `OpenPartialHomeomorph.chartBall e b ε`, as a morphism
of topological spaces, is a normal coordinate of the point `b`: it vanishes exactly on `{b}`
(`OpenPartialHomeomorph.chartBallHomeomorph_eq_zero_iff`). -/
lemma isoOfHomeo_chartBallHomeomorph_hom_eq_zero_iff (hb : b ∈ e.source) (w : e.chartBall b ε) :
    ((_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (e.chartBall b ε))
      (Y := _root_.TopCat.of (ball (0 : V) ε)) (e.chartBallHomeomorph hε)).hom w : V) = 0 ↔
      (w : B) ∈ ({b} : Set B) :=
  (e.chartBallHomeomorph_eq_zero_iff hε hb w).trans mem_singleton_iff.symm

variable {E : _root_.TopCat.{u}}

/-- Over `chartBall e b ε`, a trivialization of `p` over a base set containing the chart ball
identifies the part of `E` with the product of the ball of radius `ε` about `0` and the fibre. -/
def chartBallTrivialization {p : E ⟶ B} {Y : Type u} [TopologicalSpace Y]
    (T : Bundle.Trivialization Y p) (hT : chartBall e b ε ⊆ T.baseSet) :
    p ⁻¹' chartBall e b ε ≃ₜ ball (0 : V) ε × Y :=
  (T.preimageHomeomorph hT).trans ((e.chartBallHomeomorph hε).prodCongr (Homeomorph.refl Y))

/-- The second coordinate of `chartBallTrivialization` is the fibre coordinate of `T`. -/
@[simp]
lemma chartBallTrivialization_apply_snd {p : E ⟶ B} {Y : Type u} [TopologicalSpace Y]
    (T : Bundle.Trivialization Y p) (hT : chartBall e b ε ⊆ T.baseSet)
    (z : p ⁻¹' chartBall e b ε) :
    (chartBallTrivialization e hε T hT z).2 = (T z.val).2 := by
  simp [chartBallTrivialization]

/-- The inverse of `chartBallTrivialization` is the inverse of `T` after reading the ball
coordinate back in `B` through `OpenPartialHomeomorph.chartBallHomeomorph`. -/
@[simp]
lemma coe_chartBallTrivialization_symm_apply {p : E ⟶ B} {Y : Type u} [TopologicalSpace Y]
    (T : Bundle.Trivialization Y p) (hT : chartBall e b ε ⊆ T.baseSet)
    (x : ball (0 : V) ε × Y) :
    ((chartBallTrivialization e hε T hT).symm x : E) =
      T.toOpenPartialHomeomorph.symm (((e.chartBallHomeomorph hε).symm x.1 : B), x.2) := by
  simp [chartBallTrivialization]

end OpenPartialHomeomorph

namespace OpenPartialHomeomorph

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  (e : OpenPartialHomeomorph B V) {b : B} {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

/-- The first coordinate of `chartBallTrivialization` is the restriction of `p` over the chart
ball followed by the chart coordinate `x ↦ e x - e b`
(`TauCeti.TopCat.normalCoordinateProj`). -/
@[simp]
lemma chartBallTrivialization_apply_fst {p : E ⟶ B} {Y : Type u} [TopologicalSpace Y]
    (T : Bundle.Trivialization Y p) (hT : chartBall e b ε ⊆ T.baseSet)
    (z : p ⁻¹' chartBall e b ε) :
    (chartBallTrivialization e hε T hT z).1 =
      TauCeti.TopCat.normalCoordinateProj p
        (_root_.TopCat.isoOfHomeo (X := _root_.TopCat.of (e.chartBall b ε))
          (Y := _root_.TopCat.of (ball (0 : V) ε)) (e.chartBallHomeomorph hε)).hom z :=
  Subtype.ext (by
    rw [TauCeti.TopCat.normalCoordinateProj_apply]
    simp [chartBallTrivialization, T.preimageHomeomorph_apply])

end OpenPartialHomeomorph

namespace TauCeti

namespace TopCat

section Chart

variable {V : Type u} [NormedAddCommGroup V] {E B : _root_.TopCat.{u}}
  {p : E ⟶ B} {R : Type*} [Ring R] (M : ModuleCat.{u} R) (e : OpenPartialHomeomorph B V) {b : B}
  (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

variable [T1Space B] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

include e hb in
/-- **The homology of a Serre fibration modulo the complement of a fibre vanishes below the
dimension.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the source
of an open partial homeomorphism `e : B → V` to a finite-dimensional real normed space. Then
`Hₘ(E, E ∖ p⁻¹(b); M) = 0` for every `m < dim V`. -/
theorem isZero_singularHomology_complFiber (hp : serreFibrations p) {m : ℕ}
    (hm : m < finrank ℝ V) :
    IsZero ((TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology M m) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  exact isZero_singularHomology_complPreimage
    (e.isoOfHomeo_chartBallHomeomorph_hom_eq_zero_iff hε hb) M (e.isOpen_chartBall b ε)
    isClosed_singleton (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) hp
    (serreFibrations.of_isIso _) (convex_ball 0 _) (ball_mem_nhds 0 hε₀) hm

/-- **The homology of a Serre fibration modulo the complement of a fibre is the shifted homology
of the fibre.** Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `b` lie in the
source of an open partial homeomorphism `e : B → V` to a real normed space of finite dimension `r`,
such as the chart `chartAt V b` of a topological manifold modelled on `V`. Then
`Hₘ(E, E ∖ p⁻¹(b); M) ≅ Hₙ(p⁻¹(b); M)` for `m = n + r`.

The isomorphism depends on `e`, and is constructed from a ball of radius `ε` about `e b` inside
the target of `e`: it is `TauCeti.TopCat.singularHomologyComplPreimageIso` for the normal coordinate
`x ↦ e x - e b` of `b` on `OpenPartialHomeomorph.chartBall e b ε`
(`TauCeti.TopCat.singularHomologyComplFiberIso_def`). -/
def singularHomologyComplFiberIso (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology M m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        M).obj (_root_.TopCat.of (p ⁻¹' {b})) :=
  singularHomologyComplPreimageIso (e.isoOfHomeo_chartBallHomeomorph_hom_eq_zero_iff hε hb) M
    (e.isOpen_chartBall b ε) isClosed_singleton
    (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) hp (serreFibrations.of_isIso _)
    (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) n m h

/-- `TauCeti.TopCat.singularHomologyComplFiberIso` is the local homology along the zero set of the
normal coordinate `x ↦ e x - e b` of `b` on `OpenPartialHomeomorph.chartBall e b ε`. -/
lemma singularHomologyComplFiberIso_def (hε₀ : 0 < ε) (hp : serreFibrations p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    singularHomologyComplFiberIso M e hb hε hε₀ hp n m h =
      singularHomologyComplPreimageIso (e.isoOfHomeo_chartBallHomeomorph_hom_eq_zero_iff hε hb) M
        (e.isOpen_chartBall b ε) isClosed_singleton
        (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) hp (serreFibrations.of_isIso _)
        (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) n m h :=
  singularHomologyComplFiberIso.eq_1 M e hb hε hε₀ hp n m h

/-! ### Naturality in maps of fibrations -/

section Naturality

variable {E' : _root_.TopCat.{u}} {p' : E' ⟶ B} {f : E ⟶ E'}

/-- **The homology of a Serre fibration modulo the complement of a fibre is natural in maps of
fibrations.** Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations over a `T₁` space, `e` a chart
of dimension `r` at `b`, and `f : E ⟶ E'` a map over `B`. Under the isomorphisms
`Hₙ₊ᵣ(E, E ∖ p⁻¹(b); R) ≅ Hₙ(p⁻¹(b); R)` of `TauCeti.TopCat.singularHomologyComplFiberIso`, built
from the same ball about `e b`, the map induced by `f` on relative homology is the map induced by
the restriction `p⁻¹(b) ⟶ p'⁻¹(b)` of `f` on the homology of the fibres. -/
@[reassoc]
theorem singularHomologyComplFiberIso_hom_naturality (hε₀ : 0 < ε) (hp : serreFibrations p)
    (hp' : serreFibrations p') (hf : f ≫ p' = p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf {b}ᶜ))
        M m ≫ (singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom =
      (singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          M).map (f.preimageMap hf {b}) := by
  rw [singularHomologyComplFiberIso_def, singularHomologyComplFiberIso_def,
    singularHomologyComplPreimageIso_hom_naturality _ _ _ (f.mapsTo_preimage_of_comp_eq hf _)
      (fun x _ ↦ congrArg _ (Subtype.ext (ConcreteCategory.congr_hom hf x)))]
  -- Both maps of fibres are the restriction of `f`.
  refine congrArg _ (congrArg _ ?_)
  ext x
  exact (TopCat.Hom.coe_preimageMap_apply f hf _ x).symm

end Naturality

end Chart

section PathConnected

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} (R : Type u) [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source) {ε : ℝ}
  (hε : ball (e b) ε ⊆ e.target)

/-- **The local homology along a path-connected fibre.** For a Serre fibration over a `T₁` space
whose fibre over `b` is path connected, with a chart of dimension `r` at `b`, the local homology
`Hᵣ(E, E ∖ p⁻¹(b); R)` along the fibre is the coefficient ring `R`: it is the zeroth homology
of the fibre (`TauCeti.TopCat.singularHomologyComplFiberIso`), followed by the augmentation. -/
def singularHomologyComplFiberIsoOfPathConnectedSpace [PathConnectedSpace (p ⁻¹' {b})]
    (hε₀ : 0 < ε) (hp : serreFibrations p) :
    (TopPair.ofSubset (p ⁻¹' {b})ᶜ).singularHomology (ModuleCat.of R R) (finrank ℝ V) ≅
      ModuleCat.of R R :=
  singularHomologyComplFiberIso (ModuleCat.of R R) e hb hε hε₀ hp 0 _ (zero_add _) ≪≫
    asIso ((_root_.TopCat.of (p ⁻¹' {b})).singularHomology₀ε (ModuleCat.of R R))

/-- `TauCeti.TopCat.singularHomologyComplFiberIsoOfPathConnectedSpace` is
`TauCeti.TopCat.singularHomologyComplFiberIso` onto the zeroth homology of the fibre, followed by
the augmentation. -/
@[reassoc]
lemma singularHomologyComplFiberIsoOfPathConnectedSpace_hom [PathConnectedSpace (p ⁻¹' {b})]
    (hε₀ : 0 < ε) (hp : serreFibrations p) :
    (singularHomologyComplFiberIsoOfPathConnectedSpace R e hb hε hε₀ hp).hom =
      (singularHomologyComplFiberIso (ModuleCat.of R R) e hb hε hε₀ hp 0 _ (zero_add _)).hom ≫
        (_root_.TopCat.of (p ⁻¹' {b})).singularHomology₀ε (ModuleCat.of R R) := by
  simp [singularHomologyComplFiberIsoOfPathConnectedSpace]

end PathConnected

end TopCat

/-! ### Classes living over the fundamental class -/

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {R : Type*} [Ring R] {M : ModuleCat.{u} R}
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)

/-- **Living over the fundamental class through the shriek map.** For a Serre fibration over a
`T₁` space with a chart `e` of dimension `r` at `b`, a class `α ∈ Hₙ₊ᵣ(E; M)` lives over the
fundamental class at `b` exactly when its image under the shriek map
`Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b)) ≅ Hₙ(p⁻¹(b))` of the inclusion of `b` is nonzero, for any ball about
`e b` inside the target of `e`. -/
theorem livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero
    {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : TopCat.serreFibrations p)
    {n m : ℕ} (h : n + finrank ℝ V = m)
    (α : ((_root_.TopCat.toSSet.obj E).homology M m : ModuleCat.{u} R)) :
    LivesOverFundamentalClass M p b α ↔
      (TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom.hom
        ((fiberLocalization M p b m).hom α) ≠ 0 := by
  rw [livesOverFundamentalClass_iff, not_iff_not]
  exact ⟨fun hα ↦ by rw [hα, map_zero], fun hα ↦ by
    simpa using congrArg (TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).inv.hom hα⟩

include hb in
/-- **A class living over the fundamental class has degree at least the dimension of the base.**
For a Serre fibration over a `T₁` space with a chart of dimension `r` at `b`, the local homology
`Hₖ(E, E ∖ p⁻¹(b))` vanishes for `k < r`, so no class of degree below `r` lives over the
fundamental class at `b`. -/
theorem LivesOverFundamentalClass.finrank_le (hp : TopCat.serreFibrations p) {d : ℕ}
    {α : ((_root_.TopCat.toSSet.obj E).homology M d : ModuleCat.{u} R)}
    (h : LivesOverFundamentalClass M p b α) : finrank ℝ V ≤ d := by
  by_contra hd
  have := ModuleCat.isZero_iff_subsingleton.1 (TopCat.isZero_singularHomology_complFiber M e hb hp
    (not_le.1 hd))
  exact (livesOverFundamentalClass_iff _ _ _ _).1 h (Subsingleton.elim _ _)

/-! ### Naturality of the shriek map -/

section ShriekNaturality

variable {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) {E' : _root_.TopCat.{u}}
  {p' : E' ⟶ B} (hp : TopCat.serreFibrations p) (hp' : TopCat.serreFibrations p')
  {f : E ⟶ E'} (hf : f ≫ p' = p) {n m : ℕ} (h : n + finrank ℝ V = m)

/-- **Naturality of the shriek map of a point** (Barraud–Damian–Humilière–Oancea,
Proposition 2.12). Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations over a `T₁` space, with a
chart `e` of dimension `r` at `b`, and let `f : E ⟶ E'` be a map over `B`. The shriek map
`j_! : Hₙ₊ᵣ(E) → Hₙ(p⁻¹(b))` of the inclusion of `b` is the localization at the fibre followed by
`TauCeti.TopCat.singularHomologyComplFiberIso`. It commutes with `f`: `j_! ∘ f_* = f_* ∘ j_!`, where
on the right `f` acts through its restriction `p⁻¹(b) ⟶ p'⁻¹(b)` to the fibres. -/
@[reassoc]
theorem homologyMap_comp_fiberLocalization_comp_singularHomologyComplFiberIso_hom :
    SSet.homologyMap (_root_.TopCat.toSSet.map f) M m ≫
        fiberLocalization M p' b m ≫
          (TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp' n m h).hom =
      fiberLocalization M p b m ≫
        (TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
            M).map (f.preimageMap hf {b}) := by
  have hloc : SSet.homologyMap (_root_.TopCat.toSSet.map f) M m ≫
        fiberLocalization M p' b m =
      fiberLocalization M p b m ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hf {b}ᶜ))
          M m := by
    have hσ := homologyMap_comp_fiberLocalization M f.hom
      (congrArg (fun g : E ⟶ B ↦ ⇑g.hom) hf) b m
    -- `hσ` is stated for `TopCat.ofHom f.hom` on `TopCat.of E`, which `exact` identifies with `f`.
    rw [localHomologyMap_def] at hσ
    exact hσ
  rw [reassoc_of% hloc, TopCat.singularHomologyComplFiberIso_hom_naturality M e hb hε hε₀ hp hp' hf]

include hp' in
/-- **Living over the fundamental class under maps of fibrations.** Let `p : E ⟶ B` and
`p' : E' ⟶ B` be Serre fibrations over a `T₁` space, with a chart `e` of dimension `r` at `b`, and
let `f : E ⟶ E'` be a map over `B`. A class `f_* α`, for `α ∈ Hₙ₊ᵣ(E; R)`, lives over the
fundamental class at `b` exactly when the restriction `p⁻¹(b) ⟶ p'⁻¹(b)` of `f` sends the shriek
image `j_! α ∈ Hₙ(p⁻¹(b); R)` to a nonzero class. This is the argument of
Barraud–Damian–Humilière–Oancea, Corollary 2.13, in which `j_! α` is the fundamental class of the
fibre of a fibre bundle of closed oriented manifolds. -/
theorem livesOverFundamentalClass_homologyMap_iff
    (α : ((_root_.TopCat.toSSet.obj E).homology M m : ModuleCat.{u} R)) :
    LivesOverFundamentalClass M p' b
        ((SSet.homologyMap (_root_.TopCat.toSSet.map f) M m).hom α) ↔
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          M).map (f.preimageMap hf {b})).hom
        ((TopCat.singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom.hom
          ((fiberLocalization M p b m).hom α)) ≠ 0 := by
  have h' := congrArg (fun φ ↦ φ.hom α)
    (homologyMap_comp_fiberLocalization_comp_singularHomologyComplFiberIso_hom e hb hε hε₀ hp hp'
      hf h)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  rw [livesOverFundamentalClass_iff_singularHomologyComplFiberIso_hom_ne_zero e hb hε hε₀ hp' h, h']

end ShriekNaturality

end TauCeti
