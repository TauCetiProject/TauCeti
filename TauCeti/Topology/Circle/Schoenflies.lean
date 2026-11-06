/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.Circle.Arc
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.Topology.JordanCurve.Basic

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
of an injective path from `p` to `q`, hence a closed one-dimensional disc with boundary `{p, q}`.
The open arcs are read off Mathlib's `Circle.path`, which traces the arc from one point to another
counterclockwise; the circle is then transported to the unit sphere of any two-dimensional real
inner product space. The collar does govern how the two sides of `Σ` meet the two components: at
each point of `S⁰` the two collar arcs lie in different components, since otherwise, by invariance
of domain, the corresponding point of `Σ` would have a neighbourhood missing one component, whose
closure contains `Σ`. Unlike for `m ≥ 2`, the two sides `β(S⁰ × (0, 1])` and `β(S⁰ × [-1, 0))` of
the collar need not lie in different components: each side has two pieces, one at each point of
`Σ`, and both pieces of one side may lie in the same component.

## Main results

* `Path.exists_homeomorph_range_closedBall`: the range of an injective path in a Hausdorff space is
  homeomorphic to the closed unit ball of a one-dimensional real normed space, by a homeomorphism
  carrying the endpoints onto the unit sphere.
* `TauCeti.exists_closure_homeomorph_closedBall_circle` and
  `TauCeti.exists_closure_homeomorph_closedBall_sphere`: two distinct points cut the circle, or the
  unit sphere of a two-dimensional real inner product space, into two open connected sets whose
  closures are closed discs bounded by the two points.
* `TauCeti.exists_closure_homeomorph_closedBall_of_finrank_eq_one`: **the generalized Schoenflies
  theorem in dimension one**, for a continuous injection `β : S⁰ × [-1, 1] → S¹`, including the
  position of the collar arcs at each point.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

open Function Metric Module Set Topology

namespace TauCeti

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [TopologicalSpace X]

/-- A one-dimensional real normed space has a unit vector spanning it. -/
private theorem exists_norm_eq_one_forall_exists_smul_eq (hE : finrank ℝ E = 1) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ v : E, ∃ c : ℝ, c • u = v := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  refine ⟨‖v‖⁻¹ • v, norm_smul_inv_norm hv, ?_⟩
  exact (finrank_eq_one_iff_of_ne_zero' _
    (smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hv)) hv)).1 hE

/-- The unit interval is homeomorphic to the closed unit ball of a one-dimensional real normed
space, by a homeomorphism sending the two endpoints to the unit sphere. -/
private theorem exists_homeomorph_unitInterval_closedBall (hE : finrank ℝ E = 1) :
    ∃ e : unitInterval ≃ₜ closedBall (0 : E) 1, ∀ t, ‖(e t : E)‖ = 1 ↔ t = 0 ∨ t = 1 := by
  obtain ⟨u, hu, hspan⟩ := exists_norm_eq_one_forall_exists_smul_eq hE
  have hnorm (t : ℝ) : ‖(2 * t - 1) • u‖ = |2 * t - 1| := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
  let f : unitInterval → closedBall (0 : E) 1 := fun t ↦
    ⟨(2 * (t : ℝ) - 1) • u, by
      rw [mem_closedBall_zero_iff, hnorm, abs_le]
      constructor <;> linarith [t.2.1, t.2.2]⟩
  have hf : Continuous f := by fun_prop
  have hinj : Injective f := by
    intro s t hst
    have h := congrArg Subtype.val hst
    simp only [f] at h
    have := smul_left_injective ℝ (ne_zero_of_norm_ne_zero (hu.trans_ne one_ne_zero)) h
    exact Subtype.ext (by linarith)
  have hsurj : Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨c, rfl⟩ := hspan v
    rw [mem_closedBall_zero_iff, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_le] at hv
    refine ⟨⟨(c + 1) / 2, by constructor <;> linarith [hv.1, hv.2]⟩, Subtype.ext ?_⟩
    simp only [f]
    congr 1
    ring
  refine ⟨hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩), fun t ↦ ?_⟩
  -- The homeomorphism built from the bijection `f` is `f` itself, by definition.
  change ‖(2 * (t : ℝ) - 1) • u‖ = 1 ↔ _
  rw [hnorm, abs_eq zero_le_one]
  constructor
  · rintro (h | h)
    · exact Or.inr (Subtype.ext (show (t : ℝ) = 1 by linarith))
    · exact Or.inl (Subtype.ext (show (t : ℝ) = 0 by linarith))
  · rintro (rfl | rfl) <;> norm_num

/-- **An arc is a closed one-dimensional disc.** The range of an injective path in a Hausdorff
space is homeomorphic to the closed unit ball of a one-dimensional real normed space, by a
homeomorphism carrying the two endpoints of the path onto the unit sphere. -/
theorem _root_.Path.exists_homeomorph_range_closedBall [T2Space X] {x y : X} {γ : Path x y}
    (hγ : Injective γ) (hE : finrank ℝ E = 1) :
    ∃ e : range γ ≃ₜ closedBall (0 : E) 1,
      ∀ z : range γ, (z : X) ∈ ({x, y} : Set X) ↔ ‖(e z : E)‖ = 1 := by
  obtain ⟨e₀, he₀⟩ := exists_homeomorph_unitInterval_closedBall hE
  let h := (γ.continuous.isClosedEmbedding hγ).isEmbedding.toHomeomorph
  refine ⟨h.symm.trans e₀, fun z ↦ ?_⟩
  obtain ⟨t, rfl⟩ := h.surjective z
  rw [Homeomorph.trans_apply, Homeomorph.symm_apply_apply, he₀]
  -- The homeomorphism onto the range of the embedding `γ` is `γ`, by definition.
  change γ t ∈ ({x, y} : Set X) ↔ _
  have h0 : γ t = x ↔ t = 0 := (show γ t = x ↔ γ t = γ 0 by rw [Path.source]).trans hγ.eq_iff
  have h1 : γ t = y ↔ t = 1 := (show γ t = y ↔ γ t = γ 1 by rw [Path.target]).trans hγ.eq_iff
  rw [mem_insert_iff, mem_singleton_iff, h0, h1]

/-- One complementary arc of a pair of distinct points of the circle: it is open and connected,
its closure is the closed arc, and that closure is a closed one-dimensional disc whose boundary
sphere corresponds to the two points. -/
private theorem isOpen_isConnected_closure_path_image_Ioo {z w : Circle} (hzw : z ≠ w)
    (hE : finrank ℝ E = 1) :
    IsOpen (z.path w '' Ioo 0 1) ∧ IsConnected (z.path w '' Ioo 0 1) ∧
      closure (z.path w '' Ioo 0 1) = range (z.path w) ∧
      ∃ e : closure (z.path w '' Ioo 0 1) ≃ₜ closedBall (0 : E) 1,
        ∀ y : closure (z.path w '' Ioo 0 1), (y : Circle) ∈ ({z, w} : Set Circle) ↔
          ‖(e y : E)‖ = 1 := by
  have hcl := Circle.closure_path_image_Ioo z w
  refine ⟨?_, ?_, hcl, ?_⟩
  · rw [← Circle.compl_range_path hzw.symm]
    exact (isCompact_range (w.path z).continuous).isClosed.isOpen_compl
  · have : IsConnected (Ioo 0 1 : Set unitInterval) :=
      ⟨nonempty_Ioo.2 zero_lt_one, isPreconnected_Ioo⟩
    exact this.image _ (z.path w).continuous.continuousOn
  · obtain ⟨e, he⟩ :=
      (z.path w).exists_homeomorph_range_closedBall (Circle.path_injective_of_ne hzw) hE
    exact ⟨(Homeomorph.setCongr hcl).trans e, fun y ↦ he (Homeomorph.setCongr hcl y)⟩

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
  obtain ⟨hAo, hAc, hAcl, eA⟩ := isOpen_isConnected_closure_path_image_Ioo hzw hE
  obtain ⟨hBo, hBc, hBcl, eB⟩ := isOpen_isConnected_closure_path_image_Ioo hzw.symm hE
  rw [pair_comm w z] at eB
  -- The two open arcs are the complements of the two closed arcs, which cover the circle and
  -- meet exactly in `{z, w}`.
  have hA : z.path w '' Ioo 0 1 = (range (w.path z))ᶜ := (Circle.compl_range_path hzw.symm).symm
  have hB : w.path z '' Ioo 0 1 = (range (z.path w))ᶜ := (Circle.compl_range_path hzw).symm
  have hunion : z.path w '' Ioo 0 1 ∪ w.path z '' Ioo 0 1 = {z, w}ᶜ := by
    rw [hA, hB, ← compl_inter, inter_comm, Circle.range_path_inter_range_path hzw]
  have hdisj : Disjoint (z.path w '' Ioo 0 1) (w.path z '' Ioo 0 1) := by
    rw [hA, hB, disjoint_compl_left_iff_subset, compl_subset_iff_union,
      Circle.range_path_union_range_path hzw]
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
  refine ⟨_, _, hAo, hBo, hAc, hBc, hdisj, hunion, ?_, ?_, eA, eB⟩
  · rw [hAcl, ← compl_compl (range _), ← hB, hcompl hdisj hunion]
  · rw [hBcl, ← compl_compl (range _), ← hA, hcompl hdisj.symm (union_comm _ _ ▸ hunion)]

/-- The unit sphere of a two-dimensional real inner product space is homeomorphic to the
circle. -/
private theorem nonempty_homeomorph_sphere_circle (hF : finrank ℝ F = 2) :
    Nonempty (sphere (0 : F) 1 ≃ₜ Circle) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  let L : F ≃ₗᵢ[ℝ] ℂ := (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ ℂ)
    (finCongr (by rw [hF, Complex.finrank_real_complex]))
  exact ⟨(L.toHomeomorph.subtype fun v ↦ by simp).trans (sphereCircleHomeomorph 0 one_pos)⟩

omit [NormedSpace ℝ E] in
/-- Pulling a closed disc back along a homeomorphism: if the closure of `S` is a closed disc
whose boundary sphere corresponds to `Φ '' P`, then the closure of `Φ ⁻¹' S` is a closed disc
whose boundary sphere corresponds to `P`. -/
private theorem exists_homeomorph_closure_preimage {Y : Type*} [TopologicalSpace Y] (Φ : X ≃ₜ Y)
    {S : Set Y} {P : Set X} (e : closure S ≃ₜ closedBall (0 : E) 1)
    (he : ∀ y : closure S, (y : Y) ∈ Φ '' P ↔ ‖(e y : E)‖ = 1) :
    ∃ e' : closure (Φ ⁻¹' S) ≃ₜ closedBall (0 : E) 1,
      ∀ y : closure (Φ ⁻¹' S), (y : X) ∈ P ↔ ‖(e' y : E)‖ = 1 := by
  let Ψ : closure (Φ ⁻¹' S) ≃ₜ closure S :=
    Φ.subtype fun x ↦ by rw [← Φ.preimage_closure, mem_preimage]
  refine ⟨Ψ.trans e, fun y ↦ ?_⟩
  rw [Homeomorph.trans_apply, ← he, Φ.image_eq_preimage_symm, mem_preimage]
  -- The restriction `Ψ` of `Φ` to the closures is `Φ` on points, by definition.
  change _ ↔ Φ.symm (Φ y) ∈ P
  rw [Φ.symm_apply_apply]

/-- **Two points cut a circle into two discs**, for the unit sphere `S¹` of a two-dimensional real
inner product space: the complement of two distinct points `p` and `q` of `S¹` is the union of two
disjoint open connected sets, which are therefore its two connected components; the closure of
each is it together with `p` and `q`, and is homeomorphic to the closed unit ball of a
one-dimensional real normed space by a homeomorphism carrying `{p, q}` onto the unit sphere. -/
theorem exists_closure_homeomorph_closedBall_sphere (hE : finrank ℝ E = 1)
    (hF : finrank ℝ F = 2) {p q : sphere (0 : F) 1} (hpq : p ≠ q) :
    ∃ A B : Set (sphere (0 : F) 1), IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = {p, q}ᶜ ∧ closure A = A ∪ {p, q} ∧ closure B = B ∪ {p, q} ∧
      (∃ e : closure A ≃ₜ closedBall (0 : E) 1,
        ∀ y : closure A, (y : sphere (0 : F) 1) ∈ ({p, q} : Set _) ↔ ‖(e y : E)‖ = 1) ∧
      (∃ e : closure B ≃ₜ closedBall (0 : E) 1,
        ∀ y : closure B, (y : sphere (0 : F) 1) ∈ ({p, q} : Set _) ↔ ‖(e y : E)‖ = 1) := by
  obtain ⟨Φ⟩ := nonempty_homeomorph_sphere_circle hF
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, hAcl, hBcl, ⟨eA, heA⟩, ⟨eB, heB⟩⟩ :=
    exists_closure_homeomorph_closedBall_circle (Φ.injective.ne hpq) hE
  have hpair : Φ ⁻¹' {Φ p, Φ q} = {p, q} := by
    rw [← image_pair, Φ.preimage_image]
  rw [← image_pair] at heA heB
  refine ⟨Φ ⁻¹' A, Φ ⁻¹' B, Φ.isOpen_preimage.2 hAo, Φ.isOpen_preimage.2 hBo,
    Φ.isConnected_preimage.2 hAc, Φ.isConnected_preimage.2 hBc, hdisj.preimage Φ, ?_, ?_, ?_,
    exists_homeomorph_closure_preimage Φ eA heA, exists_homeomorph_closure_preimage Φ eB heB⟩
  · rw [← preimage_union, hunion, preimage_compl, hpair]
  · rw [← Φ.preimage_closure, hAcl, preimage_union, hpair]
  · rw [← Φ.preimage_closure, hBcl, preimage_union, hpair]

/-- The unit sphere of a one-dimensional real normed space consists of two distinct points. -/
private theorem exists_ne_forall_eq_or_eq_sphere (hE : finrank ℝ E = 1) :
    ∃ u v : sphere (0 : E) 1, u ≠ v ∧ ∀ x, x = u ∨ x = v := by
  obtain ⟨u, hu, hspan⟩ := exists_norm_eq_one_forall_exists_smul_eq hE
  have hu0 : u ≠ 0 := ne_zero_of_norm_ne_zero (hu.trans_ne one_ne_zero)
  refine ⟨⟨u, by simpa using hu⟩, ⟨-u, by simpa using hu⟩, fun h ↦ ?_, fun x ↦ ?_⟩
  · have h' : u = -u := congrArg Subtype.val h
    have h2 : (2 : ℝ) • u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h']
      exact neg_add_cancel u
    exact hu0 ((smul_eq_zero.1 h2).resolve_left two_ne_zero)
  · obtain ⟨c, hc⟩ := hspan x
    have hx : ‖(x : E)‖ = 1 := by simp
    rw [← hc, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_eq zero_le_one] at hx
    rcases hx with rfl | rfl
    · exact Or.inl (Subtype.ext (by simp [← hc]))
    · exact Or.inr (Subtype.ext (by simp [← hc]))

/-- If an open set `N` around a point `y₀` of the closure of `B` lies in `A ∪ {y₀}`, with `A`
disjoint from `B` and `y₀ ∉ B`, we have a contradiction: `N` meets `B`. -/
private theorem false_of_subset_union_singleton {A B N : Set X} {y₀ : X} (hN : IsOpen N)
    (hy₀N : y₀ ∈ N) (hy₀ : y₀ ∈ closure B) (hNA : N ⊆ A ∪ {y₀}) (hAB : Disjoint A B)
    (hy₀B : y₀ ∉ B) : False := by
  obtain ⟨y, hyN, hyB⟩ := mem_closure_iff_nhds.1 hy₀ N (hN.mem_nhds hy₀N)
  rcases hNA hyN with hyA | rfl
  · exact disjoint_left.1 hAB hyA hyB
  · exact hy₀B hyB

omit [NormedSpace ℝ E] in
/-- The collar clause of the one-dimensional Schoenflies theorem: if the complement of the zero
slice `Σ` of a continuous injection `β : S⁰ × [-1, 1] → S¹` is split into open sets `A` and `B`
whose closures add exactly `Σ`, then the two collar arcs at each point lie on different sides. -/
private theorem collar_mapsTo (hF : finrank ℝ F = 2)
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
  have : Fact (finrank ℝ F = 1 + 1) := ⟨hF⟩
  have hinjOn : InjOn g (Ioo (-1) 1) := fun s hs t ht hst ↦ by
    rw [hgβ (Ioo_subset_Icc_self hs), hgβ (Ioo_subset_Icc_self ht)] at hst
    simpa using congrArg (fun z ↦ (z.2 : ℝ)) (hinj hst)
  have hN : IsOpen (g '' Ioo (-1) 1) :=
    isOpen_Ioo.image_of_continuousOn_of_injOn (E := ℝ) (F := EuclideanSpace ℝ (Fin 1))
      hg.continuousOn hinjOn (by simp)
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
  · exact (false_of_subset_union_singleton hN h0N (hBcl ▸ Or.inr h0S) (hNsub hP hM) hdisj
      fun h ↦ h0AB (Or.inr h)).elim
  · exact Or.inl ⟨hP, hM⟩
  · exact Or.inr ⟨hP, hM⟩
  · exact (false_of_subset_union_singleton hN h0N (hAcl ▸ Or.inr h0S) (hNsub hP hM) hdisj.symm
      fun h ↦ h0AB (Or.inl h)).elim

/-- **The generalized Schoenflies theorem in dimension one.** Let `β : S⁰ × [-1, 1] → S¹` be a
continuous injection, where `S⁰` is the unit sphere of a one-dimensional real normed space `E` and
`S¹` is the unit sphere of a two-dimensional real inner product space, and let `Σ` be the image of
its zero slice `S⁰ × {0}`, a pair of points. Then:

* the complement of `Σ` is the union of two disjoint open connected sets `A` and `B`, which are
  therefore its two connected components;
* the closure of each of `A` and `B` is it together with `Σ`, and is homeomorphic to the closed
  unit ball `D¹` of `E` by a homeomorphism carrying its frontier `Σ` onto the unit sphere `∂D¹`;
* at each point `x` of `S⁰`, one of the two collar arcs `β({x} × (0, 1])` and
  `β({x} × [-1, 0))` lies in `A` and the other in `B`.

Unlike in higher dimensions, the two sides `β(S⁰ × (0, 1])` and `β(S⁰ × [-1, 0))` of the collar
need not lie in different components. -/
theorem exists_closure_homeomorph_closedBall_of_finrank_eq_one (hE : finrank ℝ E = 1)
    (hF : finrank ℝ F = 2) {β : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 → sphere (0 : F) 1}
    (hβ : Continuous β) (hinj : Injective β) :
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
  obtain ⟨u, v, huv, huv'⟩ := exists_ne_forall_eq_or_eq_sphere hE
  let o : Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
  -- The zero slice consists of the two distinct points `β (u, 0)` and `β (v, 0)`.
  have hS : β '' (univ ×ˢ {t : ↥(Icc (-1 : ℝ) 1) | (t : ℝ) = 0}) = {β (u, o), β (v, o)} := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
      obtain rfl : t = o := Subtype.ext ht
      rcases huv' x with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨(u, o), ⟨mem_univ _, rfl⟩, rfl⟩
      · exact ⟨(v, o), ⟨mem_univ _, rfl⟩, rfl⟩
  have hpq : β (u, o) ≠ β (v, o) := fun h ↦ huv (congrArg Prod.fst (hinj h))
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, hAcl, hBcl, eA, eB⟩ :=
    exists_closure_homeomorph_closedBall_sphere hE hF hpq
  rw [← hS] at hunion hAcl hBcl eA eB
  exact ⟨A, B, hAo, hBo, hAc, hBc, hdisj, hunion, hAcl, hBcl, eA, eB,
    collar_mapsTo hF hβ hinj hAo hBo hdisj hunion hAcl hBcl⟩

end TauCeti
