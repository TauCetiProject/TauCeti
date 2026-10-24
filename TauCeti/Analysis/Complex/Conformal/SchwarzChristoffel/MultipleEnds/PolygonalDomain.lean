/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Vertex
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.BoundaryPrevertex
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.EndMatching
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.LocalBoundary
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.LocallyConnectedBoundary
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.ModelEnd
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.ParallelEnd
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.PolygonalFrontier
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.SectorEnd
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.LocalFrontier
import TauCeti.Analysis.Complex.Conformal.Reflection.Infinity
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Converse
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Formula

/-!
# The Schwarz--Christoffel theorem for polygonal domains with several ends

A polygonal domain can have several vertices at infinity: a strip has two.  Such a domain `U` is
described here by its local geometry together with its shape far out.  Near each frontier point
other than the finitely many vertices `v i` it coincides with an open half-plane, and near `v i`
with the open sector of opening `(e i + 1) * π` at `v i`, where `e i ∈ (-1, 1)`.  Far out it is
covered by finitely many pairwise disjoint ends `E k ⊆ U`, each of one of two kinds:
* the far part `{ρ < ‖w - c‖, |arg ((w - c) / b)| < β * π / 2}` of a sector of opening `β * π`,
  `0 < β < 2`, with turning exponent `e' k = -β - 1`;
* a half-strip `{ρ < re ((w - c) / b), 0 < im ((w - c) / b) < π}` between two parallel sides, with
  turning exponent `e' k = -1`.
Its frontier is a finite union of closed segments and closed rays, `U` is simply connected, and
some point lies outside the closure of `U`.

Then an affine image `A * F + B` of the normalized Schwarz--Christoffel primitive `F` maps the
upper half-plane bijectively onto `U`, where `F` has one real prevertex for each finite vertex and
one for each end, with the exponents `e i` and `e' k`.  The point at infinity of the half-plane is
sent to a point on a side, so all the turning exponents together sum to `-2`.

The proof inverts `U` about an exterior point `q`.  The inverted domain has locally connected
frontier, so Carathéodory's theorem gives a Riemann map `f` whose inverted coordinate
`g = (f - q)⁻¹` is continuous on the closed upper half-plane.  The real zeros of `g` are the
accesses to infinity, and they correspond bijectively to the ends: distinct zeros lie in distinct
ends by a crosscut argument, and every end is reached because `f` is bounded away from the zeros.
A real parameter `x₀` sent to a side is then moved to infinity by `z ↦ x₀ - 1 / z`, and the local
side, corner and end conditions of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary` follow from the
local geometry of `U`.  Ends of opening `2 * π`, exteriors of half-strips, are not among the ends
allowed here.

## Main results

* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_ends` -- a polygonal
  domain with several ends is the image of the upper half-plane under an affine image of a
  Schwarz--Christoffel primitive, with the prevertices of the finite vertices sent to the vertices
  and the prevertex of each end sent into that end.
* `TauCeti.exponent_sum_eq_neg_two_of_polygonal_ends` -- the turning exponents of the finite
  vertices and of the ends of such a domain sum to `-2`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- **A Riemann map with a side point at infinity.**  Under the hypotheses of
`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_ends`, with the ends
replaced by open sets `E k` preconnected at infinity inside `U`, there is a coordinate `g`,
continuous on the closed upper half-plane, holomorphic and nonzero in the open one, and injective
away from its zeros, such that `F = q + g⁻¹` maps the upper half-plane onto `U`.  Its nonzero real
boundary values give frontier points of `U`, it has a nonzero limit at infinity, so that the point
at infinity of the half-plane is sent to a side of `U`, and accordingly
`z * F''(z) / F'(z) → -2` there.  Finally the vertices have distinct real prevertices `a i`. -/
private theorem exists_inverted_coordinate_of_polygonal_ends {ι κ : Type*} [Finite ι] [Finite κ]
    {e : ι → ℝ} (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) {U : Set ℂ} (hUo : IsOpen U)
    (hUs : IsSimplyConnected U) (hUb : ¬IsBounded U) {v : ι → ℂ} (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    {σ τ : Type*} [Finite σ] [Finite τ] {x y : σ → ℂ} {o d : τ → ℂ} (hd : ∀ k, d k ≠ 0)
    (hfr : frontier U =
      (⋃ i, segment ℝ (x i) (y i)) ∪ ⋃ k, (fun t : ℝ => o k + (t : ℂ) * d k) '' Ici 0)
    {q : ℂ} (hq : q ∉ closure U) {E : κ → Set ℂ} {R : ℝ} (hEo : ∀ k, IsOpen (E k))
    (hEd : Pairwise (Disjoint on E)) (hUE : ∀ w ∈ U, R < ‖w‖ → ∃ k, w ∈ E k)
    (hEc : ∀ k, IsPreconnectedAtInfinityIn U (E k)) :
    ∃ g : ℂ → ℂ, ∃ a : ι → ℝ, ContinuousOn g {z : ℂ | 0 ≤ z.im} ∧
      DifferentiableOn ℂ g upperHalfPlaneSet ∧ (∀ z ∈ upperHalfPlaneSet, g z ≠ 0) ∧
      InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0} ∧
      (fun z => q + (g z)⁻¹) '' upperHalfPlaneSet = U ∧
      (∀ x : ℝ, g x ≠ 0 → q + (g x)⁻¹ ∈ frontier U) ∧
      (∃ c₀ : ℂ, c₀ ≠ 0 ∧ Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 c₀)) ∧
      Tendsto (fun z => z * logDeriv (deriv fun z => q + (g z)⁻¹) z)
        (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-2)) ∧
      Injective a ∧ ∀ i, g (a i) ≠ 0 ∧ q + (g (a i))⁻¹ = v i := by
  -- a Riemann map `f` with continuous inverted coordinate `g = (f - q)⁻¹`, injective off its zeros
  have := locallyConnectedSpace_frontier_image_inv_sub_of_frontier_eq hUo hq hUb hd hfr
  obtain ⟨f, g, -, hfU, hgc, hgd, hgf, hgne, -, hgr, hg0⟩ :=
    exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub hUo hUs hq hUb
  have hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0} :=
    injOn_inverted_boundary_of_polygonal (fun i => (he i).2.le) hUo hq hUb hgc hgd hgf hfU hgr
      hg0 hside hcorner
  have hgU : (fun z => q + (g z)⁻¹) '' upperHalfPlaneSet = U := by
    rw [← hfU.image_eq]
    exact image_congr fun z hz => by simp [hgf hz]
  -- a nonzero real boundary value of `g` is the inverse of `w - q` for a frontier point `w`
  have hfront {z : ℂ} (hz : z.im = 0) (hgz : g z ≠ 0) : q + (g z)⁻¹ ∈ frontier U := by
    have hmem : g z ∈ frontier ((fun z : ℂ => (z - q)⁻¹) '' U) :=
      hgr ▸ mem_insert_of_mem _ ⟨z, hz, rfl⟩
    rw [frontier_image_inv_sub hUo hq hUb] at hmem
    obtain ⟨w, hw, hwg⟩ := hmem.resolve_left hgz
    rw [← hwg]
    simpa using hw
  -- the prevertices of the vertices
  have hvU (i : ι) : v i ∈ frontier U := by
    obtain ⟨r, hr, n, hn, hUi⟩ := hcorner i
    exact mem_frontier_of_forall_mem_iff_abs_arg_lt hr hn
      (by nlinarith [Real.pi_pos, (he i).1]) (by nlinarith [Real.pi_pos, (he i).2]) hUi
  have hvq (i : ι) : (v i - q)⁻¹ ≠ 0 :=
    inv_ne_zero (sub_ne_zero.mpr fun h => hq (h ▸ frontier_subset_closure (hvU i)))
  obtain ⟨a₀, ha₀, ha₀g⟩ :=
    exists_injective_prevertices_of_inverted_boundary hUo hq hUb hgc hgf hgr hv hvU
  -- a real parameter `x₀` that is neither a zero of `g` nor a prevertex, so is sent to a side
  obtain ⟨x₀, hx₀⟩ := ((finite_setOf_inverted_coordinate_eq_zero hgc hgd hgf hgne hfU hEo hEd hUE
    hEc).union (finite_range a₀)).exists_notMem
  have hgx₀ : g x₀ ≠ 0 := fun h => hx₀ (Or.inl h)
  have hnotv (i : ι) : q + (g x₀)⁻¹ ≠ v i := fun h => hx₀ (Or.inr ⟨i, by
    have hg : g x₀ = g (a₀ i) := by rw [(ha₀g i).1, ← h, add_sub_cancel_left, inv_inv]
    exact_mod_cast hgi ⟨by simp, (ha₀g i).1 ▸ hvq i⟩ ⟨by simp, hgx₀⟩ hg.symm⟩)
  obtain ⟨ρ₀, hρ₀, p₀, n₀, hn₀, hU₀⟩ := hside _ (hfront (by simp) hgx₀) hnotv
  obtain ⟨r₀, hr₀, hc₀, hi₀, hreal₀, hupper₀⟩ :=
    exists_ball_side_of_inverted_coordinate hgc hgi hgU hgx₀ hρ₀ hU₀
  -- move `x₀` to infinity
  obtain ⟨g₁, hg₁0, hg₁g, hg₁c, hg₁d, hg₁ne, hg₁i, hg₁U, hg₁inf⟩ :=
    exists_inverted_coordinate_comp_sub_inv hgc hgd hgne hgi hg0 x₀
  have ha0 (i : ι) : (((x₀ - a₀ i)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simpa [sub_eq_zero] using fun h => hx₀ (Or.inr ⟨i, h.symm⟩)
  refine ⟨g₁, fun i => (x₀ - a₀ i)⁻¹, hg₁c, hg₁d, hg₁ne, hg₁i, ?_, fun x hx => ?_,
    ⟨_, hgx₀, hg₁inf⟩, ?_, fun i j h => ha₀ (by simpa [sub_right_inj] using h), fun i => ?_⟩
  · rw [← image_image (fun w => q + w⁻¹) g₁, hg₁U, image_image, hgU]
  · have hx0 : (x : ℂ) ≠ 0 := fun h => hx (by rw [h, hg₁0])
    rw [hg₁g _ hx0] at hx ⊢
    exact hfront (by simp) hx
  · -- the side point `q + (g x₀)⁻¹` at infinity gives the condition at infinity
    exact tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_comp_sub_inv
      (fun z (hz : 0 < z.im) => by simp [hg₁g z fun h => by simp [h] at hz]) hr₀
      (((differentiableOn_const q).add (hgd.inv hgne)).mono inter_subset_right) hn₀ hc₀ hi₀
      hreal₀ hupper₀
  · have hg₁a : g₁ ((x₀ - a₀ i)⁻¹ : ℝ) = (v i - q)⁻¹ := by
      rw [hg₁g _ (ha0 i), ← (ha₀g i).1]
      congr 1
      simp
    rw [hg₁a, inv_inv, add_sub_cancel]
    exact ⟨hvq i, rfl⟩

/-- **The side condition away from the prevertices.**  Let `g` be continuous on the closed upper
half-plane and injective away from its zeros, with `q + g⁻¹` mapping the upper half-plane onto
`U` and its nonzero real boundary values in the frontier of `U`.  At a real parameter `x` with
`g x ≠ 0` which is not a prevertex `a i` of a vertex `v i`, the local half-plane description of
`U` gives the side condition of the Schwarz--Christoffel formula for `q + g⁻¹`. -/
private theorem exists_ball_side_of_inverted_coordinate_of_ne_prevertex {ι : Type*} {g : ℂ → ℂ}
    {q : ℂ} {U : Set ℂ} (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hgU : (fun z => q + (g z)⁻¹) '' upperHalfPlaneSet = U)
    (hgfr : ∀ x : ℝ, g x ≠ 0 → q + (g x)⁻¹ ∈ frontier U) {v : ι → ℂ}
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    {a : ι → ℝ} (hga : ∀ i, g (a i) ≠ 0 ∧ q + (g (a i))⁻¹ = v i) {x : ℝ} (hx : g x ≠ 0)
    (hxa : ∀ i, a i ≠ x) :
    ∃ r > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ContinuousOn (fun z => q + (g z)⁻¹) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn (fun z => q + (g z)⁻¹) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ ball (x : ℂ) r, z.im = 0 → ((q + (g z)⁻¹ - p) / b).im = 0) ∧
      ∀ z ∈ ball (x : ℂ) r, 0 < z.im → 0 < ((q + (g z)⁻¹ - p) / b).im := by
  have hnv (i : ι) : q + (g x)⁻¹ ≠ v i := fun h => by
    have hg : g x = g (a i) := inv_injective (add_left_cancel (h.trans (hga i).2.symm))
    exact hxa i (by exact_mod_cast hgi ⟨by simp, (hga i).1⟩ ⟨by simp, hx⟩ hg.symm)
  obtain ⟨ρ, hρ, p, b, hb, hU⟩ := hside _ (hgfr x hx) hnv
  obtain ⟨r, hr, h₁, h₂, h₃, h₄⟩ := exists_ball_side_of_inverted_coordinate hgc hgi hgU hx hρ hU
  exact ⟨r, hr, p, b, hb, h₁, h₂, h₃, h₄⟩

/-- The Schwarz--Christoffel representation of a Riemann map of a polygonal domain with several
ends, before its constants are named: a holomorphic bijection `f` of the upper half-plane onto `U`
which is an affine image of the primitive, has the limit `-2` of `z * f''(z) / f'(z)` at infinity,
tends to `v i` at `a i`, and takes values in `E k` near `a' k`. -/
private theorem exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_ends
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    (e' : κ → ℝ) (z₀ : UpperHalfPlane) {U : Set ℂ} (hUo : IsOpen U) (hUs : IsSimplyConnected U)
    (hUb : ¬IsBounded U) {v : ι → ℂ} (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    {σ τ : Type*} [Finite σ] [Finite τ] {x y : σ → ℂ} {o d : τ → ℂ} (hd : ∀ k, d k ≠ 0)
    (hfr : frontier U =
      (⋃ i, segment ℝ (x i) (y i)) ∪ ⋃ k, (fun t : ℝ => o k + (t : ℂ) * d k) '' Ici 0)
    {q : ℂ} (hq : q ∉ closure U)
    {E : κ → Set ℂ} {c b : κ → ℂ} {ρ R : ℝ} (hb : ∀ k, b k ≠ 0)
    (hE : ∀ k, (e' k ∈ Ioo (-3 : ℝ) (-1) ∧
        E k = {w : ℂ | ρ < ‖w - c k‖ ∧ |((w - c k) / b k).arg| < (-e' k - 1) * Real.pi / 2}) ∨
      (e' k = -1 ∧
        E k = {w : ℂ | ρ < ((w - c k) / b k).re ∧ ((w - c k) / b k).im ∈ Ioo 0 Real.pi}))
    (hEU : ∀ k, E k ⊆ U) (hUE : ∀ w ∈ U, R < ‖w‖ → ∃ k, w ∈ E k)
    (hEd : Pairwise (Disjoint on E)) :
    ∃ a : ι → ℝ, ∃ a' : κ → ℝ, Injective (Sum.elim a a') ∧ ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f upperHalfPlaneSet ∧ BijOn f upperHalfPlaneSet U ∧
      EqOn f (fun z => deriv f z₀ / schwarzChristoffelIntegrand (Sum.elim a a') (Sum.elim e e') z₀ *
        schwarzChristoffelPrimitive (Sum.elim a a') (Sum.elim e e') z₀ z + f z₀)
        upperHalfPlaneSet ∧
      Tendsto (fun z => z * logDeriv (deriv f) z) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
        (𝓝 (-2)) ∧
      (∀ i, Tendsto f (𝓝[upperHalfPlaneSet] ((a i : ℝ) : ℂ)) (𝓝 (v i))) ∧
      ∀ k, ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((a' k : ℝ) : ℂ), f z ∈ E k := by
  have hH : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := fun z (hz : 0 < z.im) => hz.le
  -- the open far parts `E'` of the ends, and a coordinate `g` with `f = q + g⁻¹`
  obtain ⟨E', R', hE'o, hE'E, hE'd, hUE', hE'c, hE'b⟩ := exists_far_ends hb hE hEU hUE hEd
  obtain ⟨g, a, hgc, hgd, hgne, hgi, hgU, hgfr, ⟨c₀, hc₀, hginf⟩, hinfty, ha, hga⟩ :=
    exists_inverted_coordinate_of_polygonal_ends he hUo hUs hUb hv hside hcorner hd hfr hq hE'o
      hE'd hUE' hE'c
  set f : ℂ → ℂ := fun z => q + (g z)⁻¹
  have hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet := fun z _ => by simp [f]
  have hfd : DifferentiableOn ℂ f upperHalfPlaneSet := (differentiableOn_const q).add (hgd.inv hgne)
  have hfi : InjOn f upperHalfPlaneSet := fun z hz z' hz' h =>
    hgi ⟨hH hz, hgne z hz⟩ ⟨hH hz', hgne z' hz'⟩ (inv_injective (add_left_cancel h))
  have hfB : BijOn f upperHalfPlaneSet U := ⟨hgU ▸ mapsTo_image _ _, hfi, hgU ▸ surjOn_image _ _⟩
  -- the zeros of `g` correspond exactly to the ends
  obtain ⟨m, hm, hmE⟩ :=
    exists_injective_end_of_inverted_coordinate_eq_zero hgc hgd hgf hgne hfB hE'o hE'd hUE' hE'c
  obtain ⟨μ, rfl⟩ : ∃ μ : {x : ℝ // g x = 0} ≃ κ, ⇑μ = m :=
    ⟨Equiv.ofBijective m ⟨hm, surjective_of_eventually_mem_end hgc hgne hginf hc₀ hgU hE'd
      (fun k => (hE'E k).trans (hEU k)) hE'b hmE⟩, rfl⟩
  set a' : κ → ℝ := fun k => (μ.symm k : ℝ)
  have hga' (k : κ) : g (a' k) = 0 := (μ.symm k).2
  have hfa' (k : κ) : ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((a' k : ℝ) : ℂ), f z ∈ E k := by
    simpa using (hmE (μ.symm k)).mono fun z hz => hE'E _ hz
  have hinj : Injective (Sum.elim a a') :=
    ha.sumElim (fun k l h => μ.symm.injective (Subtype.ext h)) fun i k h =>
      (hga i).1 (by rw [h, hga' k])
  refine ⟨a, a', hinj, f, hfd, hfB, ?_, hinfty, fun i => ?_, hfa'⟩
  · -- the local side, corner and end conditions of the Schwarz--Christoffel formula
    refine eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary _ _ hinj z₀ hfd
      (fun z hz => deriv_ne_zero_of_injOn hfd isOpen_upperHalfPlaneSet hfi hz) (fun x hx => ?_)
      (fun j => ?_) hinfty
    · -- away from the prevertices, `g x ≠ 0`, since every zero of `g` is some `a' k`
      have hgx : g x ≠ 0 := fun h => hx (Sum.inr (μ ⟨x, h⟩)) (by simp [a'])
      exact exists_ball_side_of_inverted_coordinate_of_ne_prevertex hgc hgi hgU hgfr hside hga hgx
        fun i => hx (Sum.inl i)
    rcases j with i | k
    · obtain ⟨ρ', hρ', n, hn, hU'⟩ := hcorner i
      rw [← (hga i).2] at hU'
      obtain ⟨r, hr, h₁, h₂, h₃, h₄⟩ :=
        exists_ball_corner_of_inverted_coordinate hgc hgi hgU (hga i).1 hρ' hn hU'
      exact Or.inl ⟨he i, r, hr, n, hn, h₁, h₂, h₃, h₄⟩
    · have hS : E k ⊆ f '' upperHalfPlaneSet := hgU ▸ hEU k
      have hfS := hfa' k
      rcases hE k with ⟨he', hEk⟩ | ⟨he', hEk⟩ <;> rw [hEk] at hS hfS
      · obtain ⟨r, hr, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
          exists_ball_sector_end_of_inverted_coordinate hgc hgd hgf hgne hgi (hga' k)
            (β := -e' k - 1) ⟨by linarith [he'.2], by linarith [he'.1]⟩ (hb k) hS hfS
        exact Or.inr (Or.inl ⟨he', r, hr, c k, b k, hb k, _, h₁, h₂, h₃, h₄, h₅, h₆⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨he', exists_ball_halfStrip_end_of_inverted_coordinate hgc
          hgd hgf hgne hgi (hga' k) (hb k) hS hfS⟩))
  · rw [← (hga i).2]
    exact tendsto_const_nhds.add
      (((hgc _ (by simp)).tendsto.mono_left (nhdsWithin_mono _ hH)).inv₀ (hga i).1)

/-- **The Schwarz--Christoffel theorem for polygonal domains with several ends.**  Let `U` be a
simply connected, unbounded open set, with a point `q` outside its closure, whose frontier is a
finite union of closed segments and closed rays.  Suppose that `U` coincides near each frontier
point other than the distinct vertices `v i` with an open half-plane, and near the vertex `v i` with
the open sector of opening `(e i + 1) * π` at `v i`, where `e i ∈ (-1, 1)`.  Suppose finally that
far out `U` is covered by pairwise disjoint ends `E k ⊆ U`, each either the far part of a sector of
opening `(-e' k - 1) * π` with `e' k ∈ (-3, -1)`, or a half-strip between two parallel sides with
`e' k = -1`.

Then there are distinct real prevertices `a i` of the vertices and `a' k` of the ends, and
constants `A ≠ 0` and `B`, such that `z ↦ A * F z + B` maps the upper half-plane bijectively onto
`U`, where `F` is the normalized Schwarz--Christoffel primitive for these prevertices and the
turning exponents `e i` and `e' k`.  The Schwarz--Christoffel vertex at `a i` is sent to `v i`, and
near `a' k` the map takes its values in the end `E k`. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_ends
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    (e' : κ → ℝ) (z₀ : UpperHalfPlane) {U : Set ℂ} (hUo : IsOpen U) (hUs : IsSimplyConnected U)
    (hUb : ¬IsBounded U) {v : ι → ℂ} (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    {σ τ : Type*} [Finite σ] [Finite τ] {x y : σ → ℂ} {o d : τ → ℂ} (hd : ∀ k, d k ≠ 0)
    (hfr : frontier U =
      (⋃ i, segment ℝ (x i) (y i)) ∪ ⋃ k, (fun t : ℝ => o k + (t : ℂ) * d k) '' Ici 0)
    {q : ℂ} (hq : q ∉ closure U)
    {E : κ → Set ℂ} {c b : κ → ℂ} {ρ R : ℝ} (hb : ∀ k, b k ≠ 0)
    (hE : ∀ k, (e' k ∈ Ioo (-3 : ℝ) (-1) ∧
        E k = {w : ℂ | ρ < ‖w - c k‖ ∧ |((w - c k) / b k).arg| < (-e' k - 1) * Real.pi / 2}) ∨
      (e' k = -1 ∧
        E k = {w : ℂ | ρ < ((w - c k) / b k).re ∧ ((w - c k) / b k).im ∈ Ioo 0 Real.pi}))
    (hEU : ∀ k, E k ⊆ U) (hUE : ∀ w ∈ U, R < ‖w‖ → ∃ k, w ∈ E k)
    (hEd : Pairwise (Disjoint on E)) :
    ∃ a : ι → ℝ, ∃ a' : κ → ℝ, Injective (Sum.elim a a') ∧ ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun z => A * schwarzChristoffelPrimitive (Sum.elim a a') (Sum.elim e e') z₀ z + B)
        upperHalfPlaneSet U ∧
      (∀ i, A * schwarzChristoffelVertex (Sum.elim a a') (Sum.elim e e') z₀ (Sum.inl i) + B =
        v i) ∧
      ∀ k, ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((a' k : ℝ) : ℂ),
        A * schwarzChristoffelPrimitive (Sum.elim a a') (Sum.elim e e') z₀ z + B ∈ E k := by
  obtain ⟨a, a', hinj, f, hfd, hfB, hform, -, hfa, hfa'⟩ :=
    exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_ends e he e' z₀ hUo hUs
      hUb hv hside hcorner hd hfr hq hb hE hEU hUE hEd
  refine ⟨a, a', hinj, _, div_ne_zero
    (deriv_ne_zero_of_injOn hfd isOpen_upperHalfPlaneSet hfB.injOn z₀.im_pos)
    (schwarzChristoffelIntegrand_ne_zero _ _ z₀.im_pos), _, hfB.congr hform, fun i => ?_,
    fun k => ?_⟩
  · -- both sides are limits at the prevertex `a i` from the upper half-plane
    have : (𝓝[upperHalfPlaneSet] ((Sum.elim a a' (Sum.inl i) : ℝ) : ℂ)).NeBot :=
      Real.nhdsWithin_upperHalfPlaneSet_neBot (a i)
    have hsum : -1 < ∑ l with Sum.elim a a' l = Sum.elim a a' (Sum.inl i), Sum.elim e e' l := by
      have hfilter : Finset.univ.filter (fun l => Sum.elim a a' l = Sum.elim a a' (Sum.inl i)) =
          {Sum.inl i} := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact hinj.eq_iff
      rw [hfilter, Finset.sum_singleton]
      exact (he i).1
    exact tendsto_nhds_unique
      (((tendsto_schwarzChristoffelPrimitive _ _ z₀ (Sum.inl i) hsum).const_mul _).add_const _)
      ((hfa i).congr' (eventually_nhdsWithin_of_forall hform))
  · filter_upwards [hfa' k, self_mem_nhdsWithin] with z hz hzH
    exact (congrArg (· ∈ E k) (hform hzH)).mp hz

/-- **The angle sum of a polygonal domain with several ends.**  Under the hypotheses of
`TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_ends`, the turning
exponents of the finite vertices and of the ends sum to `-2`.  For a strip, with two half-strip
ends of exponent `-1` and no finite vertices, this is `-1 + -1 = -2`. -/
theorem exponent_sum_eq_neg_two_of_polygonal_ends
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    (e' : κ → ℝ) {U : Set ℂ} (hUo : IsOpen U) (hUs : IsSimplyConnected U)
    (hUb : ¬IsBounded U) {v : ι → ℂ} (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    {σ τ : Type*} [Finite σ] [Finite τ] {x y : σ → ℂ} {o d : τ → ℂ} (hd : ∀ k, d k ≠ 0)
    (hfr : frontier U =
      (⋃ i, segment ℝ (x i) (y i)) ∪ ⋃ k, (fun t : ℝ => o k + (t : ℂ) * d k) '' Ici 0)
    {q : ℂ} (hq : q ∉ closure U)
    {E : κ → Set ℂ} {c b : κ → ℂ} {ρ R : ℝ} (hb : ∀ k, b k ≠ 0)
    (hE : ∀ k, (e' k ∈ Ioo (-3 : ℝ) (-1) ∧
        E k = {w : ℂ | ρ < ‖w - c k‖ ∧ |((w - c k) / b k).arg| < (-e' k - 1) * Real.pi / 2}) ∨
      (e' k = -1 ∧
        E k = {w : ℂ | ρ < ((w - c k) / b k).re ∧ ((w - c k) / b k).im ∈ Ioo 0 Real.pi}))
    (hEU : ∀ k, E k ⊆ U) (hUE : ∀ w ∈ U, R < ‖w‖ → ∃ k, w ∈ E k)
    (hEd : Pairwise (Disjoint on E)) :
    ∑ i, e i + ∑ k, e' k = -2 := by
  obtain ⟨a, a', -, f, hfd, hfB, hform, hinfty, -, -⟩ :=
    exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_ends e he e'
      UpperHalfPlane.I hUo hUs hUb hv hside hcorner hd hfr hq hb hE hEU hUE hEd
  have hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn hfd isOpen_upperHalfPlaneSet hfB.injOn hz
  -- `f` is an affine image of the primitive, so its pre-Schwarzian is the partial-fraction sum
  have hpre := (exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_iff _ _ UpperHalfPlane.I
    hfd hfn).mp ⟨_, div_ne_zero (hfn _ UpperHalfPlane.I.im_pos)
      (schwarzChristoffelIntegrand_ne_zero _ _ UpperHalfPlane.I.im_pos), _, hform⟩
  have hsum := exponent_sum_eq_of_logDeriv_deriv_eqOn (fun l => ((Sum.elim a a' l : ℝ) : ℂ))
    (fun l => ((Sum.elim e e' l : ℝ) : ℂ)) hpre hinfty
  rw [Fintype.sum_sum_type] at hsum
  exact_mod_cast hsum

end TauCeti

end
