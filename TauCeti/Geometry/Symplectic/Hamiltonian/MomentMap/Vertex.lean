/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.LocallyFree
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ConvexHull
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Perfect
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Chart
import Mathlib.Analysis.Convex.Strict.Extreme
import TauCeti.Analysis.Convex.Extreme
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Fixed points of a symplectic toric manifold are the vertices of its moment polytope

Let a torus `G`, a compact connected commutative Lie group with Lie algebra `𝔤`, act smoothly and
effectively on a compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`,
with moment map `μ : M → 𝔤*`, and suppose that `dim M = 2 dim G`. So `(M, σ, μ)` is a symplectic
toric manifold. This file proves that the fixed points of `G` correspond exactly to the vertices
of the moment polytope `conv μ(M) = conv μ(M^G)`
(`TauCeti.SmoothTwoForm.IsMomentMap.bijOn_fixedPoints_extremePoints_convexHull_range`).

The argument reads the weights at a fixed point `p` off the weight normal form
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`): in a chart `z = (q, p)` of `M` at
`p` onto a ball of `ℂⁿ`, with `2 n = dim M`,

`μ = μ(p) - ½ Σₖ (qₖ² + pₖ²) αₖ`

for weights `α₁, …, αₙ ∈ 𝔤*`.

* **The weights at a fixed point form a basis of `𝔤*`.** If `ξ` is killed by every weight, then
  `ξ_M` vanishes on the whole chart. Since the action is effective, its isotropy algebras are
  trivial on a dense set (`TauCeti.Lie.dense_setOf_isotropy_eq_bot`), so `ξ = 0`. Hence the
  `n = dim G` weights span `𝔤*` and are linearly independent.
* **Fixed points are isolated.** At a point of the chart other than `p`, some coordinate `zₖ` is
  nonzero, and an element `ξ` with `αₖ(ξ) ≠ 0` does not fix it
  (`TauCeti.SmoothTwoForm.IsMomentMap.eventually_eq_of_mem_fixedPoints`). So there are finitely
  many fixed points (`TauCeti.SmoothTwoForm.IsMomentMap.finite_fixedPoints_of_faithfulSMul`).
* **A fixed point is the unique maximum of a component.** The elements `ξ` with `αₖ(ξ) > 0` for
  every `k` form a nonempty open cone, and for each of them `μ^ξ ≤ μ^ξ(p)` on the chart: `p` is a
  local maximum of `μ^ξ`. Choosing `ξ` in this cone with dense one-parameter subgroup, `μ^ξ` is a
  Morse function with even indices (`TauCeti.SmoothTwoForm.IsMomentMap.isMorse_of_eq_top`), so
  its local maximum `p` is its unique global maximum
  (`TauCeti.SmoothTwoForm.IsMomentMap.subsingleton_setOf_isLocalMax`):
  `μ^ξ(y) < μ^ξ(p)` for every `y ≠ p`
  (`TauCeti.SmoothTwoForm.IsMomentMap.exists_forall_lt_of_mem_fixedPoints`).

Consequently `μ(p)` is an exposed point of the moment image, hence a vertex of the moment polytope,
the fibre of `μ` over `μ(p)` is the single point `p`
(`TauCeti.SmoothTwoForm.IsMomentMap.preimage_singleton_eq_of_mem_fixedPoints`), and distinct fixed
points have distinct images. Conversely every vertex of `conv μ(M^G)` is the image of a fixed
point. When `dim G > 0`, the image of a fixed point is not an interior point of the moment image
(`TauCeti.SmoothTwoForm.IsMomentMap.notMem_interior_range_of_mem_fixedPoints`); for `dim G = 0`
the manifold is a point, which is both a vertex and an interior point of its image.

These are complexity-zero statements. When `dim M > 2 dim G` there are more weights than the
dimension of `𝔤*`, and a fixed point may map into the interior of the moment image, as for the
effective circle action on `ℂ²` with weights `1` and `-1`
(`TauCeti.zero_mem_interior_range_weightMomentMap_id_neg_id`).

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `eventually_eq_of_mem_fixedPoints`, `finite_fixedPoints_of_faithfulSMul`: the fixed points of
  a symplectic toric manifold are isolated, hence finite in number.
* `exists_forall_lt_of_mem_fixedPoints`: every fixed point is the unique maximum of some component
  `μ^ξ` of the moment map.
* `preimage_singleton_eq_of_mem_fixedPoints`: the fibre of `μ` through a fixed point is that
  point.
* `bijOn_fixedPoints_extremePoints_convexHull_range`: `μ` is a bijection from the fixed points
  onto the vertices of the moment polytope `conv μ(M)`.
* `notMem_interior_range_of_mem_fixedPoints`: for `dim G > 0`, the image of a fixed point is not
  an interior point of the moment image.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*, Bull. Soc.
  Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 27–29.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, Section 2 (the local form of the moment map at a fixed point).
-/

public section

noncomputable section

open Filter Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G] [PreconnectedSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  [FaithfulSMul G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

omit [PreconnectedSpace G] [CompactSpace M] in
/-- **The local picture at a fixed point of a symplectic toric manifold.** Near a fixed point `p`,
`p` is the only fixed point, and there is a nonempty open set of elements `ξ` of the Lie algebra,
those on which every weight at `p` is positive, for which `μ^ξ ≤ μ^ξ(p)` near `p`. -/
private theorem exists_nhds_of_mem_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
    ∃ U ∈ 𝓝 p, (∀ q ∈ U, q ∈ MulAction.fixedPoints G M → q = p) ∧
      ∃ V : Set (GroupLieAlgebra I G), IsOpen V ∧ V.Nonempty ∧
        ∀ ξ ∈ V, ∀ x ∈ U, μ x ξ ≤ μ p ξ := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  obtain ⟨n, χ, α, chart, r, -, -, hpchart, hchartp, -, -, -, -, hgen, hμchart⟩ :=
    h.exists_weightModelChart hσ hG (MulAction.mem_fixedPoints.1 hp)
  -- The chart identifies the model `E'` of `M` with `ℂⁿ`, so `n = dim G`.
  have hn : finrank ℝ E = n := by
    have := (chart.isLocalDiffeomorphAt I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n)) ∞ hpchart).finrank_eq (by simp)
    rw [Module.finrank_prod, finrank_euclideanSpace_fin] at this
    omega
  -- An element killed by every weight lies in the isotropy algebra of every point of the chart,
  -- so it vanishes: the action is locally free on a dense set.
  have hsep (ξ : GroupLieAlgebra I G) (hξ : ∀ k, α k ξ = 0) : ξ = 0 := by
    obtain ⟨x, hx, hxfree⟩ := (Lie.dense_setOf_isotropy_eq_bot (I := I) (I' := I') (G := G)
      (M := M)).inter_open_nonempty chart.source chart.open_source ⟨p, hpchart⟩
    have hmem : ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x :=
      (mem_isotropy_fundamental_iff_of_mfderiv_eq hx (hgen x hx ξ)).2 fun k _ ↦ hξ k
    rw [mem_ofPred_eq.mp hxfree] at hmem
    exact hmem
  -- The weights are the coordinates of a linear isomorphism `𝔤 ≃ ℝⁿ`.
  let A : GroupLieAlgebra I G →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k ↦ (α k).toLinearMap
  have hA (ξ : GroupLieAlgebra I G) (k : Fin n) : A ξ k = α k ξ := rfl
  have hAsurj : Function.Surjective A := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 ?_
    · rwa [Module.finrank_fin_fun]
    · refine (injective_iff_map_eq_zero A).2 fun ξ hξ ↦ hsep ξ fun k ↦ ?_
      rw [← hA, hξ, Pi.zero_apply]
  obtain ⟨ξ₁, hξ₁⟩ := hAsurj fun _ ↦ 1
  refine ⟨chart.source, chart.open_source.mem_nhds hpchart, fun q hq hqfix ↦ ?_,
    A ⁻¹' {v | ∀ k, 0 < v k}, ?_, ⟨ξ₁, fun k ↦ by simp [hξ₁]⟩, fun ξ hξ x hx ↦ ?_⟩
  · -- A fixed point of the chart other than `p` would have a nonzero coordinate `zₖ`, and every
    -- element of the Lie algebra would be killed by the weight `αₖ`.
    by_contra hqp
    have hz : chart q ≠ 0 := fun hz ↦ hqp (chart.injOn hq hpchart (hz.trans hchartp.symm))
    obtain ⟨k, hk⟩ : ∃ k, (chart q).1 k ≠ 0 ∨ (chart q).2 k ≠ 0 := by
      by_contra! hk
      exact hz (Prod.ext (PiLp.ext fun k ↦ (hk k).1) (PiLp.ext fun k ↦ (hk k).2))
    have hiso : ξ₁ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy q := by
      rw [InfinitesimalAction.mem_isotropy_iff, InfinitesimalAction.fundamental_apply]
      exact fundamentalVectorField_eq_zero_of_forall_smul_eq (MulAction.mem_fixedPoints.1 hqfix) _
    have h0 := (mem_isotropy_fundamental_iff_of_mfderiv_eq hq (hgen q hq ξ₁)).1 hiso k hk
    rw [← hA, hξ₁] at h0
    exact one_ne_zero h0
  · refine IsOpen.preimage A.continuous_of_finiteDimensional ?_
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun k ↦ isOpen_lt continuous_const (continuous_apply k)
  · -- On the chart, `μ^ξ = μ^ξ(p) - ½ Σₖ αₖ(ξ) (qₖ² + pₖ²)` with every `αₖ(ξ) > 0`.
    rw [hμchart x hx ξ, add_le_iff_nonpos_right, weightMomentMap_apply α (chart x) ξ]
    refine mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Finset.sum_nonneg fun k _ ↦ ?_)
    exact mul_nonneg (hA ξ k ▸ (hξ k).le) (by positivity)

omit [PreconnectedSpace G] [CompactSpace M] in
/-- **Fixed points of a symplectic toric manifold are isolated.** Let a torus `G` act smoothly and
effectively on a connected symplectic manifold `(M, σ)` without boundary, preserving `σ`, with
moment map `μ`, and with `dim M = 2 dim G`. Then near each fixed point there is no other fixed
point. -/
theorem eventually_eq_of_mem_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
    ∀ᶠ q in 𝓝 p, q ∈ MulAction.fixedPoints G M → q = p := by
  obtain ⟨U, hU, hUp, -⟩ := h.exists_nhds_of_mem_fixedPoints hσ hG hdim hp
  exact Filter.mem_of_superset hU hUp

/-- **A symplectic toric manifold has finitely many fixed points.** -/
theorem finite_fixedPoints_of_faithfulSMul
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) :
    (MulAction.fixedPoints G M).Finite := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  exact h.finite_fixedPoints hσ.isNondegenerate fun _ hp ↦
    h.eventually_eq_of_mem_fixedPoints hσ hG hdim hp

/-- **A fixed point is the unique maximum of a moment map component.** Let a torus `G` act
smoothly and effectively on a compact connected symplectic manifold `(M, σ)` without boundary,
preserving `σ`, with moment map `μ`, and with `dim M = 2 dim G`. For every fixed point `p` there is
an element `ξ` of the Lie algebra such that `μ^ξ(y) < μ^ξ(p)` for every `y ≠ p`. -/
theorem exists_forall_lt_of_mem_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
    ∃ ξ : GroupLieAlgebra I G, ∀ y, y ≠ p → μ y ξ < μ p ξ := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  have : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  have hσG (a : G) (x : M) (u v : TangentSpace I' x) :
      σ.eval₂ (a • x) (mfderiv I' I' (a • ·) x u) (mfderiv I' I' (a • ·) x v) =
        σ.eval₂ x u v := by
    rw [← SmoothForm.eval₂_mpullback _ (ContMDiffSMul.contMDiff_const_smul (I := I) a), hG a]
  have hiso (q : M) (hq : q ∈ MulAction.fixedPoints G M) :
      ∀ᶠ y in 𝓝 q, y ∈ MulAction.fixedPoints G M → y = q :=
    h.eventually_eq_of_mem_fixedPoints hσ hG hdim hq
  obtain ⟨U, hU, -, V, hVo, hVne, hV⟩ := h.exists_nhds_of_mem_fixedPoints hσ hG hdim hp
  -- Choose `ξ` in the open cone `V` with dense one-parameter subgroup; then `μ^ξ` is Morse.
  obtain ⟨ξ, hξV, hξ⟩ :=
    (Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).inter_open_nonempty V hVo hVne
  have hM := h.isMorse_of_eq_top hσ.isNondegenerate hξ hiso
  have hmax : IsLocalMax (fun y ↦ μ y ξ) p := Filter.mem_of_superset hU fun x hx ↦ hV ξ hξV x hx
  have hglob := h.isMaxOn_of_isLocalMax hσ.isNondegenerate hσG hM hmax
  refine ⟨ξ, fun y hyp ↦ (hglob (mem_univ y)).lt_of_ne fun hy ↦ hyp ?_⟩
  -- A second maximum would be a second local maximum of the Morse function `μ^ξ`.
  have hymax : IsMaxOn (fun y ↦ μ y ξ) univ y :=
    isMaxOn_univ_iff.2 fun z ↦ (isMaxOn_univ_iff.1 hglob z).trans_eq hy.symm
  exact h.subsingleton_setOf_isLocalMax hσ.isNondegenerate hσG hM
    (hymax.isLocalMax univ_mem) hmax

/-- **The fibre through a fixed point is that point.** For a symplectic toric manifold, the only
point mapped by the moment map to the image of a fixed point `p` is `p` itself. -/
theorem preimage_singleton_eq_of_mem_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
    μ ⁻¹' {μ p} = {p} := by
  obtain ⟨ξ, hξ⟩ := h.exists_forall_lt_of_mem_fixedPoints hσ hG hdim hp
  refine eq_singleton_iff_unique_mem.2 ⟨rfl, fun y hy ↦ ?_⟩
  by_contra hyp
  exact (hξ y hyp).ne (congrArg (· ξ) hy)

/-- **Fixed points correspond exactly to vertices.** Let a torus `G` act smoothly and effectively
on a compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`, with moment
map `μ`, and with `dim M = 2 dim G`. Then `μ` maps the fixed-point set bijectively onto the set of
extreme points of the moment polytope `conv μ(M)`. -/
theorem bijOn_fixedPoints_extremePoints_convexHull_range
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) :
    BijOn μ (MulAction.fixedPoints G M) ((convexHull ℝ (range μ)).extremePoints ℝ) := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  refine ⟨fun p hp ↦ ?_, fun p _ q hq hpq ↦ ?_, ?_⟩
  · obtain ⟨ξ, hξ⟩ := h.exists_forall_lt_of_mem_fixedPoints hσ hG hdim hp
    refine mem_extremePoints_convexHull_of_strict_max (mem_range_self p)
      (Module.Dual.eval ℝ (GroupLieAlgebra I G) ξ) ?_
    rintro _ ⟨y, rfl⟩ hy
    exact hξ y fun hyp ↦ hy (congrArg μ hyp)
  · rw [← mem_singleton_iff, ← h.preimage_singleton_eq_of_mem_fixedPoints hσ hG hdim hq]
    exact hpq
  · rw [h.convexHull_range_eq_convexHull_image_fixedPoints hσ.isNondegenerate]
    exact extremePoints_convexHull_subset

/-- **Images of fixed points are not interior.** For a symplectic toric manifold of positive
dimension, the image of a fixed point under the moment map, read in the continuous dual `𝔤*`, is
not an interior point of the moment image. -/
theorem notMem_interior_range_of_mem_fixedPoints [Nontrivial E]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
    (LinearMap.toContinuousLinearMap (μ p) : StrongDual ℝ E) ∉
      interior (range fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E)) := by
  obtain ⟨ξ, hξ⟩ := h.exists_forall_lt_of_mem_fixedPoints hσ hG hdim hp
  set f : M → StrongDual ℝ E := fun x ↦ LinearMap.toContinuousLinearMap (μ x)
  have hext : f p ∈ (range f).extremePoints ℝ := by
    refine inter_extremePoints_subset_extremePoints_of_subset (subset_convexHull ℝ (range f))
      ⟨mem_range_self p, mem_extremePoints_convexHull_of_strict_max (mem_range_self p)
        (ContinuousLinearMap.apply ℝ ℝ (show E from ξ)).toLinearMap ?_⟩
    rintro _ ⟨y, rfl⟩ hy
    exact hξ y fun hyp ↦ hy (congrArg f hyp)
  exact fun hint ↦ disjoint_left.1 (disjoint_interior_extremePoints _) hint hext

end TauCeti.SmoothTwoForm.IsMomentMap
