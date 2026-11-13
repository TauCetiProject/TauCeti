/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.AlgebraicTopology.Sphere.Zero
import TauCeti.Geometry.Sphere.Circle
import TauCeti.Topology.Circle.Arc
import TauCeti.Topology.Closure
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Path.Arc

/-!
# The generalized Schoenflies theorem in dimension one

M. Brown's generalized Schoenflies theorem says that if `β : Sᵐ⁻¹ × [-1, 1] → Sᵐ` is a topological
embedding, then the complement of the image `Σ` of its zero slice `Sᵐ⁻¹ × {0}` has exactly two
components, and the closure of each is homeomorphic to the closed disc `Dᵐ` by a homeomorphism
carrying its frontier `Σ` onto the boundary sphere `∂Dᵐ`. This file proves the case `m = 1`, which
is elementary and is treated separately from `m ≥ 2`.

For `m = 1`, `Σ` is a pair of distinct points `p`, `q` of the circle `S¹`, and the collar is
irrelevant to the first two conclusions: the complement of `{p, q}` consists of the two open arcs
between them, and the closure of each is the corresponding closed arc, which is an arc in the sense
of an injective path from `p` to `q`, hence a closed one-dimensional disc with boundary `{p, q}`
(`Path.exists_homeomorph_range_closedBall`).
The open arcs are read off Mathlib's `Circle.path`, which traces the arc from one point to another
counterclockwise; that they are open, connected and disjoint and cover the complement of `{p, q}` is
in `TauCeti/Topology/Circle/Arc.lean`. The circle is then transported to the unit sphere
of any two-dimensional real normed space. The collar does govern how the two sides of `Σ`
meet the two components: at each point of `S⁰` the two collar arcs lie in different components,
since otherwise, by invariance of domain, the corresponding point of `Σ` would have a neighbourhood
missing one component, whose closure contains `Σ`. Unlike for `m ≥ 2`, the two sides
`β(S⁰ × (0, 1])` and `β(S⁰ × [-1, 0))` of the collar need not lie in different components: each
side has two pieces, one at each point of `Σ`, and the two pieces of one side may lie in different
components, so neither side need be contained in a single component.

The last section states the theorem for an injective map `σ : S⁰ → S¹` with image `Σ`, in terms
of the connected components of `S¹ ∖ Σ`, of which there are exactly two by the Jordan–Brouwer
separation theorem (`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`). Being open,
preconnected and disjoint, the two open arcs between the points of `Σ` are these components
(`IsPreconnected.connectedComponentIn_union_eq_left`). A homeomorphism of a closed arc onto `D¹`
carrying `Σ` onto `S⁰` either inverts `σ` or does so after composing with the negation of `D¹`.
For a bicollar `b` of `σ`, the slice of `b` through a point of the discrete domain `S⁰` is an open
neighbourhood of a point of `Σ`, and so meets both components. On the unit circle, with `Σ` the
points at angles `0` and `π`, a bicollar whose angle increases with `t` at the first point and
decreases with `t` at the second has both positive arcs in the upper half of the circle.

## Main results

* `TauCeti.exists_closure_homeomorph_closedBall_circle` and
  `TauCeti.exists_closure_homeomorph_closedBall_sphere`: two distinct points cut the circle, or the
  unit sphere of a two-dimensional real normed space, into two open connected sets whose
  closures are closed discs bounded by the two points.
* `TauCeti.exists_closure_homeomorph_closedBall_of_finrank_eq_one`: **the generalized Schoenflies
  theorem in dimension one**, for a continuous injection `β : S⁰ × [-1, 1] → S¹`, including the
  position of the collar arcs at each point.
* `TauCeti.closure_connectedComponentIn_compl_range_of_finrank_eq_one` and
  `TauCeti.frontier_connectedComponentIn_compl_range_of_finrank_eq_one`: for an injective
  `σ : S⁰ → S¹` with image `Σ`, the closure of each component `U` of `S¹ ∖ Σ` is `U ∪ Σ`, and its
  frontier is `Σ`.
* `TauCeti.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one`: the
  closure of each component is homeomorphic to `D¹` by a homeomorphism which inverts `σ` on `Σ`
  and carries exactly `Σ` onto `S⁰`.
* `TauCeti.IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one`: for a bicollar `b`
  of `σ`, the collar arcs `b (x, t)` with `t > 0` and with `t < 0` at each point `σ x` lie in
  different components.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

open Function Metric Module Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- The closure of one complementary arc of a pair of distinct points of the circle is the closed
arc, and it is a closed one-dimensional disc whose boundary sphere corresponds to the two points. -/
private theorem closure_path_image_Ioo_homeomorph_closedBall {z w : Circle} (hzw : z ≠ w)
    (hE : finrank ℝ E = 1) :
    closure (z.path w '' Ioo 0 1) = range (z.path w) ∧
      ∃ e : closure (z.path w '' Ioo 0 1) ≃ₜ closedBall (0 : E) 1,
        ∀ y : closure (z.path w '' Ioo 0 1), (y : Circle) ∈ ({z, w} : Set Circle) ↔
          ‖(e y : E)‖ = 1 := by
  have hcl := (z.path w).closure_image_Ioo
  obtain ⟨e, he⟩ :=
    (z.path w).exists_homeomorph_range_closedBall (Circle.path_injective_of_ne hzw) hE
  exact ⟨hcl, (Homeomorph.setCongr hcl).trans e, fun y ↦ he (Homeomorph.setCongr hcl y)⟩

/-- **Two points cut the circle into two discs.** The complement of two distinct points `z` and
`w` of the circle is the union of two disjoint open connected sets, which are therefore its two
connected components. The closure of each consists of it together with `z` and `w`, and is
homeomorphic to the closed unit ball of a one-dimensional real normed space by a homeomorphism
carrying `{z, w}` onto the unit sphere. -/
theorem exists_closure_homeomorph_closedBall_circle {z w : Circle} (hzw : z ≠ w)
    (hE : finrank ℝ E = 1) :
    ∃ A B : Set Circle, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      A ∪ B = {z, w}ᶜ ∧ closure A = A ∪ {z, w} ∧ closure B = B ∪ {z, w} ∧
      (∃ e : closure A ≃ₜ closedBall (0 : E) 1,
        ∀ y : closure A, (y : Circle) ∈ ({z, w} : Set Circle) ↔ ‖(e y : E)‖ = 1) ∧
      (∃ e : closure B ≃ₜ closedBall (0 : E) 1,
        ∀ y : closure B, (y : Circle) ∈ ({z, w} : Set Circle) ↔ ‖(e y : E)‖ = 1) := by
  obtain ⟨hAcl, eA⟩ := closure_path_image_Ioo_homeomorph_closedBall hzw hE
  obtain ⟨hBcl, eB⟩ := closure_path_image_Ioo_homeomorph_closedBall hzw.symm hE
  rw [pair_comm w z] at eB
  -- The two open arcs are the complements of the two closed arcs.
  have hA : z.path w '' Ioo 0 1 = (range (w.path z))ᶜ := (Circle.compl_range_path hzw.symm).symm
  have hB : w.path z '' Ioo 0 1 = (range (z.path w))ᶜ := (Circle.compl_range_path hzw).symm
  have hunion := Circle.path_image_Ioo_union hzw
  have hdisj := Circle.disjoint_path_image_Ioo hzw
  -- Each closed arc is the complement of the opposite open arc.
  have hcompl {S T : Set Circle} (hST : Disjoint S T) (hu : S ∪ T = {z, w}ᶜ) :
      Tᶜ = S ∪ {z, w} := by
    ext y
    refine ⟨fun hy ↦ ?_, ?_⟩
    · by_contra h
      rw [mem_union, not_or] at h
      have : y ∈ S ∪ T := hu ▸ h.2
      exact this.elim h.1 hy
    · rintro (hS | hP) hT
      · exact disjoint_left.1 hST hS hT
      · exact (hu ▸ (Or.inr hT : y ∈ S ∪ T) : y ∈ ({z, w} : Set Circle)ᶜ) hP
  refine ⟨_, _, Circle.isOpen_path_image_Ioo hzw, Circle.isOpen_path_image_Ioo hzw.symm,
    (Circle.isPathConnected_path_image_Ioo z w).isConnected,
    (Circle.isPathConnected_path_image_Ioo w z).isConnected, hdisj, hunion, ?_, ?_, eA, eB⟩
  · rw [hAcl, ← compl_compl (range _), ← hB, hcompl hdisj hunion]
  · rw [hBcl, ← compl_compl (range _), ← hA, hcompl hdisj.symm (union_comm _ _ ▸ hunion)]

/-- **Two points cut a circle into two discs**, for the unit sphere `S¹` of a two-dimensional real
normed space: the complement of two distinct points `p` and `q` of `S¹` is the union of two
disjoint open connected sets, which are therefore its two connected components; the closure of
each is it together with `p` and `q`, and is homeomorphic to the closed unit ball of a
one-dimensional real normed space by a homeomorphism carrying `{p, q}` onto the unit sphere. -/
theorem exists_closure_homeomorph_closedBall_sphere [NormedSpace ℝ F] (hE : finrank ℝ E = 1)
    (hF : finrank ℝ F = 2) {p q : sphere (0 : F) 1} (hpq : p ≠ q) :
    ∃ A B : Set (sphere (0 : F) 1), IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = {p, q}ᶜ ∧ closure A = A ∪ {p, q} ∧ closure B = B ∪ {p, q} ∧
      (∃ e : closure A ≃ₜ closedBall (0 : E) 1,
        ∀ y : closure A, (y : sphere (0 : F) 1) ∈ ({p, q} : Set _) ↔ ‖(e y : E)‖ = 1) ∧
      (∃ e : closure B ≃ₜ closedBall (0 : E) 1,
        ∀ y : closure B, (y : sphere (0 : F) 1) ∈ ({p, q} : Set _) ↔ ‖(e y : E)‖ = 1) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  obtain ⟨Φ⟩ : Nonempty (sphere (0 : F) 1 ≃ₜ Circle) :=
    ⟨(sphereHomeomorphOfFinrankEq (F := EuclideanSpace ℝ (Fin 2)) (by simp [hF])).trans
      EuclideanSpace.sphereHomeomorphCircle⟩
  -- Pulling a closed disc back along `Φ`, with its boundary sphere.
  have hdisc {S : Set Circle} (e : closure S ≃ₜ closedBall (0 : E) 1)
      (he : ∀ y : closure S, (y : Circle) ∈ Φ '' {p, q} ↔ ‖(e y : E)‖ = 1) :
      ∃ e' : closure (Φ ⁻¹' S) ≃ₜ closedBall (0 : E) 1, ∀ y : closure (Φ ⁻¹' S),
        (y : sphere (0 : F) 1) ∈ ({p, q} : Set _) ↔ ‖(e' y : E)‖ = 1 := by
    let Ψ : closure (Φ ⁻¹' S) ≃ₜ closure S :=
      Φ.subtype fun x ↦ by rw [← Φ.preimage_closure, mem_preimage]
    refine ⟨Ψ.trans e, fun y ↦ ?_⟩
    rw [Homeomorph.trans_apply, ← he, Φ.image_eq_preimage_symm, mem_preimage]
    -- The restriction `Ψ` of `Φ` to the closures is `Φ` on points, by definition.
    change _ ↔ Φ.symm (Φ y) ∈ _
    rw [Φ.symm_apply_apply]
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, hAcl, hBcl, ⟨eA, heA⟩, ⟨eB, heB⟩⟩ :=
    exists_closure_homeomorph_closedBall_circle (Φ.injective.ne hpq) hE
  have hpair : Φ ⁻¹' {Φ p, Φ q} = {p, q} := by
    rw [← image_pair, Φ.preimage_image]
  rw [← image_pair] at heA heB
  refine ⟨Φ ⁻¹' A, Φ ⁻¹' B, Φ.isOpen_preimage.2 hAo, Φ.isOpen_preimage.2 hBo,
    Φ.isConnected_preimage.2 hAc, Φ.isConnected_preimage.2 hBc, hdisj.preimage Φ, ?_, ?_, ?_,
    hdisc eA heA, hdisc eB heB⟩
  · rw [← preimage_union, hunion, preimage_compl, hpair]
  · rw [← Φ.preimage_closure, hAcl, preimage_union, hpair]
  · rw [← Φ.preimage_closure, hBcl, preimage_union, hpair]

omit [NormedSpace ℝ E] in
/-- The collar clause of the one-dimensional Schoenflies theorem: if the complement of the zero
slice `Σ` of a continuous injection `β : S⁰ × [-1, 1] → S¹` is split into open sets `A` and `B`
whose closures add exactly `Σ`, then the two collar arcs at each point lie on different sides. -/
private theorem collar_mapsTo [NormedSpace ℝ F] (hF : finrank ℝ F = 2)
    {β : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 → sphere (0 : F) 1} (hβ : Continuous β)
    (hinj : Injective β) {A B : Set (sphere (0 : F) 1)} (hAo : IsOpen A) (hBo : IsOpen B)
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = (β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}))ᶜ)
    (hAcl : closure A = A ∪ β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}))
    (hBcl : closure B = B ∪ β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}))
    (x : sphere (0 : E) 1) :
    (MapsTo (fun t ↦ β (x, t)) {t | 0 < (t : ℝ)} A ∧
        MapsTo (fun t ↦ β (x, t)) {t | (t : ℝ) < 0} B) ∨
      (MapsTo (fun t ↦ β (x, t)) {t | 0 < (t : ℝ)} B ∧
        MapsTo (fun t ↦ β (x, t)) {t | (t : ℝ) < 0} A) := by
  have h1 : (-1 : ℝ) ≤ 1 := by norm_num
  -- The collar arc at `x`, extended to a map on `ℝ`.
  let g : ℝ → sphere (0 : F) 1 := fun t ↦ β (x, projIcc (-1) 1 h1 t)
  have hg : Continuous g := hβ.comp (continuous_const.prodMk continuous_projIcc)
  have hgβ {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : g t = β (x, ⟨t, ht⟩) := by
    simp only [g, projIcc_of_mem h1 ht]
  -- Off the zero slice, the collar arc avoids `Σ`, so it lies in `A ∪ B`.
  have hgAB {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (ht0 : t ≠ 0) : g t ∈ A ∪ B := by
    rw [hunion, hgβ ht]
    rintro ⟨⟨x', t'⟩, ⟨-, ht'⟩, h⟩
    have := congrArg (fun z ↦ (z.2 : ℝ)) (hinj h)
    simp only at this ht'
    exact ht0 (this ▸ ht')
  have hside {I : Set ℝ} (hI : IsPreconnected I) (hIsub : I ⊆ Icc (-1) 1) (hI0 : (0 : ℝ) ∉ I) :
      g '' I ⊆ A ∨ g '' I ⊆ B :=
    (hI.image g hg.continuousOn).subset_or_subset hAo hBo hdisj <| by
      rintro _ ⟨t, ht, rfl⟩
      exact hgAB (hIsub ht) fun h ↦ hI0 (h ▸ ht)
  -- The two collar arcs at `x` are traced by `g` on `(0, 1]` and on `[-1, 0)`.
  have hslice {I : Set ℝ} (hI : I ⊆ Icc (-1) 1) :
      (fun t ↦ β (x, t)) '' {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) ∈ I} = g '' I := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, hgβ t.2⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, hI ht⟩, ht, (hgβ _).symm⟩
  have hIoc : Ioc (0 : ℝ) 1 ⊆ Icc (-1) 1 := fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩
  have hIco : Ico (-1 : ℝ) 0 ⊆ Icc (-1) 1 := fun t ht ↦ ⟨ht.1, by linarith [ht.2]⟩
  have hpos :
      {t : ↥(Icc (-1 : ℝ) 1) | 0 < (t : ℝ)} = {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) ∈ Ioc 0 1} :=
    Set.ext fun t ↦ ⟨fun h ↦ ⟨h, t.2.2⟩, fun h ↦ h.1⟩
  have hneg :
      {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) < 0} = {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) ∈ Ico (-1) 0} :=
    Set.ext fun t ↦ ⟨fun h ↦ ⟨t.2.1, h⟩, fun h ↦ h.2⟩
  simp only [mapsTo_iff_image_subset, hpos, hneg, hslice hIoc, hslice hIco]
  -- By invariance of domain the open collar arc is a neighbourhood of its centre `g 0 ∈ Σ`.
  -- Invariance of domain is applied in the Euclidean unit circle, through a homeomorphism `Φ`.
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  let Φ : sphere (0 : F) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    sphereHomeomorphOfFinrankEq (by simp [hF])
  have hinjOn : InjOn g (Ioo (-1) 1) := fun s hs t ht hst ↦ by
    rw [hgβ (Ioo_subset_Icc_self hs), hgβ (Ioo_subset_Icc_self ht)] at hst
    simpa using congrArg (fun z ↦ (z.2 : ℝ)) (hinj hst)
  have hN : IsOpen (g '' Ioo (-1) 1) := by
    have := isOpen_Ioo.image_of_continuousOn_of_injOn (E := ℝ) (F := EuclideanSpace ℝ (Fin 1))
      (Φ.continuous.comp hg).continuousOn (Φ.injective.comp_injOn hinjOn) (by simp)
    rwa [image_comp, Φ.isOpen_image] at this
  have h0N : g 0 ∈ g '' Ioo (-1) 1 := mem_image_of_mem g ⟨by norm_num, by norm_num⟩
  have h0S : g 0 ∈ β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}) :=
    ⟨(x, ⟨0, by norm_num⟩), ⟨mem_univ _, rfl⟩, (hgβ _).symm⟩
  have h0AB : g 0 ∉ A ∪ B := hunion ▸ fun h ↦ h h0S
  have hNsub {S : Set (sphere (0 : F) 1)} (hP : g '' Ioc 0 1 ⊆ S) (hM : g '' Ico (-1) 0 ⊆ S) :
      g '' Ioo (-1) 1 ⊆ S ∪ {g 0} := by
    rintro _ ⟨t, ht, rfl⟩
    rcases lt_trichotomy t 0 with h | rfl | h
    · exact Or.inl (hM ⟨t, ⟨ht.1.le, h⟩, rfl⟩)
    · exact Or.inr rfl
    · exact Or.inl (hP ⟨t, ⟨h, ht.2.le⟩, rfl⟩)
  -- If both arcs were on the same side, `g 0` could not be adherent to the other side.
  rcases hside isPreconnected_Ioc hIoc (fun h ↦ lt_irrefl _ h.1) with hP | hP <;>
  rcases hside isPreconnected_Ico hIco (fun h ↦ lt_irrefl _ h.2) with hM | hM
  · exact (not_subset_union_singleton_of_mem_closure hN h0N (hBcl ▸ Or.inr h0S) hdisj
      (fun h ↦ h0AB (Or.inr h)) (hNsub hP hM)).elim
  · exact Or.inl ⟨hP, hM⟩
  · exact Or.inr ⟨hP, hM⟩
  · exact (not_subset_union_singleton_of_mem_closure hN h0N (hAcl ▸ Or.inr h0S) hdisj.symm
      (fun h ↦ h0AB (Or.inl h)) (hNsub hP hM)).elim

/-- **The generalized Schoenflies theorem in dimension one.** Let `β : S⁰ × [-1, 1] → S¹` be a
continuous injection, where `S⁰` is the unit sphere of a one-dimensional real normed space `E` and
`S¹` is the unit sphere of a two-dimensional real normed space, and let `Σ` be the image of
its zero slice `S⁰ × {0}`, a pair of points. Then:

* the complement of `Σ` is the union of two disjoint open connected sets `A` and `B`, which are
  therefore its two connected components;
* the closure of each of `A` and `B` is it together with `Σ`, and is homeomorphic to the closed
  unit ball `D¹` of `E` by a homeomorphism carrying its frontier `Σ` onto the unit sphere `∂D¹`;
* at each point `x` of `S⁰`, one of the two collar arcs `β({x} × (0, 1])` and
  `β({x} × [-1, 0))` lies in `A` and the other in `B`.

Unlike in higher dimensions, the two sides `β(S⁰ × (0, 1])` and `β(S⁰ × [-1, 0))` of the collar
need not lie in different components. -/
theorem exists_closure_homeomorph_closedBall_of_finrank_eq_one [NormedSpace ℝ F]
    (hE : finrank ℝ E = 1) (hF : finrank ℝ F = 2)
    {β : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 → sphere (0 : F) 1} (hβ : Continuous β)
    (hinj : Injective β) :
    ∃ A B : Set (sphere (0 : F) 1), IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = (β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}))ᶜ ∧
      closure A = A ∪ β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}) ∧
      closure B = B ∪ β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}) ∧
      (∃ e : closure A ≃ₜ closedBall (0 : E) 1, ∀ y : closure A,
        (y : sphere (0 : F) 1) ∈ β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}) ↔
          ‖(e y : E)‖ = 1) ∧
      (∃ e : closure B ≃ₜ closedBall (0 : E) 1, ∀ y : closure B,
        (y : sphere (0 : F) 1) ∈ β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}) ↔
          ‖(e y : E)‖ = 1) ∧
      ∀ x, (MapsTo (fun t ↦ β (x, t)) {t | 0 < (t : ℝ)} A ∧
          MapsTo (fun t ↦ β (x, t)) {t | (t : ℝ) < 0} B) ∨
        (MapsTo (fun t ↦ β (x, t)) {t | 0 < (t : ℝ)} B ∧
          MapsTo (fun t ↦ β (x, t)) {t | (t : ℝ) < 0} A) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨u⟩ : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  -- The zero-sphere `S⁰` is `{u, -u}`.
  have huv' (x : sphere (0 : E) 1) : x = u ∨ x = -u := by
    have hx : (x : E) ∈ ({(u : E), -(u : E)} : Set E) :=
      sphere_eq_pair_of_finrank_eq_one hE u.2 ▸ x.2
    rcases hx with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)
  let o : Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
  -- The zero slice consists of the two distinct points `β (u, 0)` and `β (-u, 0)`.
  have hS : β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}) = {β (u, o), β (-u, o)} := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
      obtain rfl : t = o := Subtype.ext ht
      rcases huv' x with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨(u, o), ⟨mem_univ _, rfl⟩, rfl⟩
      · exact ⟨(-u, o), ⟨mem_univ _, rfl⟩, rfl⟩
  have hpq : β (u, o) ≠ β (-u, o) := fun h ↦
    ne_neg_of_mem_unit_sphere ℝ u (congrArg Prod.fst (hinj h))
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, hAcl, hBcl, eA, eB⟩ :=
    exists_closure_homeomorph_closedBall_sphere hE hF hpq
  rw [← hS] at hunion hAcl hBcl eA eB
  exact ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, hAcl, hBcl, eA, eB,
    collar_mapsTo hF hβ hinj hAo hBo hdisj hunion hAcl hBcl⟩

/-! ### The complementary domains of an injective image of `S⁰` -/

section Complement

variable [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- An open set `A` of the circle which is one of the two complementary arcs of the image of
`σ`: it is preconnected, its closure adds the image of `σ`, and the closure is a closed `1`-cell
by a homeomorphism inverting `σ` on its boundary. -/
private def IsComplementaryArc (σ : sphere (0 : E) 1 → sphere (0 : F) 1)
    (A : Set (sphere (0 : F) 1)) : Prop :=
  IsOpen A ∧ IsPreconnected A ∧ closure A = A ∪ range σ ∧
    ∃ h : closure A ≃ₜ closedBall (0 : E) 1,
      ∀ (z : closure A) x, (z : sphere (0 : F) 1) = σ x → (h z : E) = x

/-- The complement of the image of an injective map from the unit sphere of a space of dimension
`1` into the unit sphere of a space of dimension `2` is the union of two disjoint complementary
arcs. These are the arcs of `TauCeti.exists_closure_homeomorph_closedBall_sphere`. -/
private theorem exists_isComplementaryArc (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : finrank ℝ E = 1) (hσ : Function.Injective σ) :
    ∃ A₁ A₂ : Set (sphere (0 : F) 1), (range σ)ᶜ = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧
      IsComplementaryArc σ A₁ ∧ IsComplementaryArc σ A₂ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨u⟩ : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  -- The image of `σ` is the pair `{σ u, σ (-u)}`.
  have hrange : range σ = {σ u, σ (-u)} := by
    rw [← image_univ, ← image_pair]
    congr 1
    refine (eq_univ_of_forall fun x ↦ ?_).symm
    have hx : (x : E) ∈ ({(u : E), -(u : E)} : Set E) :=
      sphere_eq_pair_of_finrank_eq_one hE u.2 ▸ x.2
    rcases hx with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, hAcl, hBcl, ⟨eA, heA⟩, ⟨eB, heB⟩⟩ :=
    exists_closure_homeomorph_closedBall_sphere hE (by rw [hEF, hE])
      (hσ.ne (ne_neg_of_mem_unit_sphere ℝ u))
  rw [← hrange] at hunion hAcl hBcl heA heB
  have hsub {S : Set (sphere (0 : F) 1)} (hS : closure S = S ∪ range σ) : range σ ⊆ closure S :=
    hS ▸ subset_union_right
  obtain ⟨hA, hhA⟩ := exists_homeomorph_apply_eq_of_finrank_eq_one hE hσ (hsub hAcl) eA heA
  obtain ⟨hB, hhB⟩ := exists_homeomorph_apply_eq_of_finrank_eq_one hE hσ (hsub hBcl) eB heB
  exact ⟨A, B, hunion.symm, hdisj, ⟨hAo, hAc.isPreconnected, hAcl, hA, hhA⟩,
    ⟨hBo, hBc.isPreconnected, hBcl, hB, hhB⟩⟩

/-- The connected component of a point `y` off the image of `σ` is one of the two complementary
arcs, and the other arc is the rest of the complement. -/
private theorem exists_connectedComponentIn_eq (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : finrank ℝ E = 1) (hσ : Function.Injective σ) {y : sphere (0 : F) 1}
    (hy : y ∉ range σ) :
    ∃ A A' : Set (sphere (0 : F) 1), connectedComponentIn (range σ)ᶜ y = A ∧
      (range σ)ᶜ = A ∪ A' ∧ Disjoint A A' ∧ IsComplementaryArc σ A ∧
      IsComplementaryArc σ A' := by
  obtain ⟨A₁, A₂, hcompl, hdisj, h₁, h₂⟩ := exists_isComplementaryArc hEF hE hσ
  have hy' : y ∈ A₁ ∪ A₂ := hcompl ▸ hy
  rcases hy' with hy' | hy'
  · exact ⟨A₁, A₂, by rw [hcompl, h₁.2.1.connectedComponentIn_union_eq_left h₁.1 h₂.1 hdisj hy'],
      hcompl, hdisj, h₁, h₂⟩
  · rw [union_comm] at hcompl
    exact ⟨A₂, A₁, by
      rw [hcompl, h₂.2.1.connectedComponentIn_union_eq_left h₂.1 h₁.1 hdisj.symm hy'], hcompl,
      hdisj.symm, h₂, h₁⟩

/-- **The closure of a complementary domain of two points of a circle.** Let `σ` be an injective
map from the unit sphere of a real normed space of dimension `1`, a pair of points, into the unit
sphere of a real normed space of dimension `2`. The closure of each connected component of
the complement of its image `Σ` adds exactly `Σ`. -/
theorem closure_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    closure (connectedComponentIn (range σ)ᶜ y) = connectedComponentIn (range σ)ᶜ y ∪ range σ := by
  obtain ⟨A, -, hA, -, -, hA', -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  rw [hA]
  exact hA'.2.2.1

/-- **The frontier of a complementary domain of two points of a circle.** Let `σ` be an injective
map from the unit sphere of a real normed space of dimension `1` into the unit sphere of a real
normed space of dimension `2`. Each connected component of the complement of its image `Σ`
has frontier `Σ`. -/
theorem frontier_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    frontier (connectedComponentIn (range σ)ᶜ y) = range σ := by
  obtain ⟨A, A', hA, hcompl, -, hA', -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  have hsub : A ⊆ (range σ)ᶜ := hcompl ▸ subset_union_left
  rw [hA, hA'.1.frontier_eq, hA'.2.2.1, union_sdiff_left]
  exact (subset_compl_iff_disjoint_left.1 hsub).sdiff_eq_left

/-- **Brown's generalized Schoenflies theorem in dimension `1`.** Let `σ` be an injective map from
the unit sphere `S⁰` of a real normed space `E` of dimension `1` into the unit sphere `S¹` of a
real normed space of dimension `2`, with image `Σ`. The closure of each connected component
of `S¹ ∖ Σ` is homeomorphic to the closed unit ball `D¹` of `E`, by a homeomorphism `h` which
inverts `σ` on `Σ` and carries exactly `Σ` onto the boundary sphere `S⁰` of `D¹`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (hσ : Function.Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  obtain ⟨A, -, hA, -, -, ⟨-, -, hcl, h, hh⟩, -⟩ := exists_connectedComponentIn_eq hEF hE hσ hy
  rw [hA]
  refine ⟨h, hh, fun z ↦ ⟨fun hz ↦ ?_, ?_⟩⟩
  · -- A point sent to the boundary sphere is the image under `σ` of its image.
    let x : sphere (0 : E) 1 := ⟨h z, hz⟩
    have hx : σ x ∈ closure A := hcl ▸ Or.inr (mem_range_self x)
    have : (⟨σ x, hx⟩ : closure A) = z := h.injective (Subtype.ext (hh _ x rfl))
    exact ⟨x, congrArg Subtype.val this⟩
  · rintro ⟨x, hx⟩
    rw [hh z x hx.symm]
    exact x.2

/-- **The collar arcs at a point of a pair in a circle.** Let `b` be a bicollar of a map `σ` from
the unit sphere `S⁰` of a real normed space of dimension `1` into the unit sphere `S¹` of a real
normed space of dimension `2`. At each point `σ x`, a point `b (x, s)` with `s > 0` and a
point `b (x, t)` with `t < 0` lie in different components of the complement of the image of `σ`.

Each collar arc at `σ x` lies in a single component
(`TauCeti.IsBicollar.image_singleton_prod_subset_connectedComponentIn`), and there are exactly
two components (`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`), so each
component contains exactly one of the two arcs at `σ x`. -/
theorem IsBicollar.connectedComponentIn_compl_range_ne_of_finrank_eq_one
    {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1} (h : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : finrank ℝ E = 1) (x : sphere (0 : E) 1)
    {s t : ℝ} (hs : 0 < s) (ht : t < 0) :
    connectedComponentIn (range σ)ᶜ (b (x, s)) ≠ connectedComponentIn (range σ)ᶜ (b (x, t)) := by
  intro heq
  have hbs : b (x, s) ∉ range σ := fun hmem ↦ by
    have : (x, s) ∈ b ⁻¹' range σ := hmem
    rw [h.preimage_range] at this
    exact hs.ne' this.2
  obtain ⟨A, A', hA, hcompl, hdisj, -, hA'⟩ :=
    exists_connectedComponentIn_eq hEF hE h.injective hbs
  -- Both collar arcs at `σ x` lie in `A`.
  have hpos := h.image_singleton_prod_subset_connectedComponentIn x isPreconnected_Ioi
    (lt_irrefl 0) (mem_Ioi.2 hs)
  have hneg := h.image_singleton_prod_subset_connectedComponentIn x isPreconnected_Iio
    (lt_irrefl 0) (mem_Iio.2 ht)
  rw [hA] at hpos
  rw [← heq, hA] at hneg
  -- The domain is a pair of points, so the slice of `b` through `x` is an open neighbourhood of
  -- `σ x`; it meets the other arc `A'`, whose closure contains `σ x`.
  have := discreteTopology_sphere_of_finrank_eq_one hE (0 : E) 1
  have hW : IsOpen (b '' ({x} ×ˢ univ)) :=
    h.isOpenEmbedding.isOpenMap _ ((isOpen_discrete _).prod isOpen_univ)
  have hσx : σ x ∈ closure A' := hA'.2.2.1 ▸ Or.inr (mem_range_self x)
  obtain ⟨_, ⟨⟨x', r⟩, ⟨hx', -⟩, rfl⟩, hrA'⟩ :=
    mem_closure_iff.1 hσx _ hW ⟨(x, 0), ⟨rfl, trivial⟩, h.apply_zero x⟩
  rw [mem_singleton_iff] at hx'
  subst hx'
  have hA'sub : A' ⊆ (range σ)ᶜ := hcompl ▸ subset_union_right
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · exact disjoint_left.1 hdisj (hneg ⟨(x', r), ⟨rfl, hr⟩, rfl⟩) hrA'
  · rw [h.apply_zero] at hrA'
    exact hA'sub hrA' (mem_range_self x')
  · exact disjoint_left.1 hdisj (hpos ⟨(x', r), ⟨rfl, hr⟩, rfl⟩) hrA'

end Complement

end TauCeti
