/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.Transverse
public import TauCeti.Analysis.Convex.Sweep.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Analysis.Convex.Intrinsic

/-!
# A transverse sweep is a topological prism

The base point and ray parameter of a transverse sweep vary continuously. Thus
the bijective prism parameterization is a homeomorphism, including for unbounded
bases and bases with lineality. The base need not be closed, convex, or nonempty.
A normalized continuous height also gives an affine projection onto the base
hyperplane and expresses the sweep as a halfspace intersected with an affine preimage.
A closed transverse base has a closed sweep, without a compactness hypothesis.
Recovering the base point also sends relative interior points of the sweep to
relative interior points of the base. Thus transverse sweeping preserves
disjoint relative interiors, as needed for subdivisions.

Adapted from `Mei/Geometry/Convex/Sweep/Topology.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, released under Apache 2.0.
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

namespace ContinuousLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {P : Set V} {n : V}

/-- The affine projection recovering the base point of a transverse sweep.
When `f n = 1`, its image lies in the hyperplane `f x = c`. -/
def sweepProjection (f : V →L[ℝ] ℝ) (c : ℝ) (n : V) : V →ᴬ[ℝ] V :=
  (ContinuousLinearMap.id ℝ V - f.smulRight n).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ V (c • n)

/-- The projection adds the unique correction along the sweeping vector. -/
@[simp]
theorem sweepProjection_apply (f : V →L[ℝ] ℝ) (c : ℝ) (n y : V) :
    sweepProjection f c n y = y + (c - f y) • n := by
  simp only [sweepProjection, ContinuousAffineMap.add_apply,
    ContinuousLinearMap.coe_toContinuousAffineMap, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousAffineMap.coe_const, Function.const_apply]
  module

section Crossing

variable {ν : V →L[ℝ] ℝ} {b : ℝ} {w : V}

/-- The sweep projection onto a face along a transverse direction moves a point to
its computed crossing with the face. -/
theorem sweepProjection_inv_smul_apply (x : V) :
    sweepProjection ν b ((ν w)⁻¹ • w) x = x - ((ν x - b) / ν w) • w := by
  rw [sweepProjection_apply, smul_smul, div_eq_mul_inv]
  module

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- Moving a point of the face backward along a transverse direction by `s` makes the
crossing parameter `-s`. -/
@[simp↓]
theorem sub_div_sub_smul_eq_neg (hw : ν w ≠ 0) {y : V} (hy : ν y = b) (s : ℝ) :
    (ν (y - s • w) - b) / ν w = -s := by
  simp only [map_sub, map_smul, smul_eq_mul, hy]
  field_simp
  ring

/-- Moving a point of the face backward along `w` and projecting returns the point. -/
@[simp↓]
theorem sweepProjection_inv_smul_sub_smul (hw : ν w ≠ 0) {y : V} (hy : ν y = b) (s : ℝ) :
    sweepProjection ν b ((ν w)⁻¹ • w) (y - s • w) = y := by
  rw [sweepProjection_inv_smul_apply, sub_div_sub_smul_eq_neg hw hy]
  module

end Crossing

/-- The linear part of a sweep projection subtracts the normal component along
the sweeping vector. -/
@[simp]
theorem sweepProjection_linear (f : V →L[ℝ] ℝ) (c : ℝ) (n : V) :
    (sweepProjection f c n).toAffineMap.linear =
      LinearMap.id - f.toLinearMap.smulRight n := by
  ext x
  simp [sweepProjection, ← ContinuousAffineMap.coe_contLinear]

/-- The recovered base point has the required height. -/
theorem sweepProjection_height (f : V →L[ℝ] ℝ) (c : ℝ) {n : V}
    (hn : f n = 1) (y : V) :
    f (sweepProjection f c n y) = c := by
  simp [hn]

/-- The sweep projection fixes the base hyperplane. -/
theorem sweepProjection_eq_self (f : V →L[ℝ] ℝ) (c : ℝ) {n y : V}
    (hy : f y = c) : sweepProjection f c n y = y := by
  simp [hy]

/-- Projecting along a transverse direction recovers any point on that line
whose height is the target height. -/
theorem sweepProjection_inv_smul_eq_add_smul
    (f : V →L[ℝ] ℝ) {c s : ℝ} {Q v : V} (hv : f v ≠ 0)
    (h : f (Q + s • v) = c) :
    sweepProjection f c ((f v)⁻¹ • v) Q = Q + s • v := by
  have htime : (c - f Q) / f v = s := (f.toLinearMap.eq_div_of_apply_add_smul_eq hv h).symm
  simp only [sweepProjection_apply, smul_smul, ← div_eq_mul_inv, htime]

/-- A sweep projection followed by displacement in a transverse direction
covers the whole space. No condition on the sweeping vector is needed: the
projection fixes the hyperplane, and the displacement supplies its complement. -/
theorem smul_add_sweepProjection_surjective
    (f : V →L[ℝ] ℝ) (c : ℝ) (n v : V)
    (hv : f v ≠ 0) :
    Function.Surjective (fun z : V × ℝ => z.2 • v + sweepProjection f c n z.1) := by
  intro y
  let t := (f y - c) / f v
  let x := y - t • v
  have hx : f x = c := by
    simp only [x, map_sub, map_smul, smul_eq_mul, t, div_mul_cancel₀ _ hv]
    ring
  refine ⟨(x, t), ?_⟩
  dsimp only
  rw [sweepProjection_eq_self f c hx]
  dsimp only [x]
  module

end ContinuousLinearMap

namespace Set

open ContinuousLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {P : Set V} {n : V}

/-- The explicit projection presents the sweep as a halfspace intersected with
an affine preimage, with no boundedness hypothesis on the base. -/
theorem sweep_eq_halfspace_inter_preimage {P : Set V} {n : V}
    (f : V →L[ℝ] ℝ) (c : ℝ) (hn : f n = 1)
    (hP : ∀ x ∈ P, f x = c) :
    sweep ℝ P n = {y | f y ≤ c} ∩ sweepProjection f c n ⁻¹' P := by
  ext y
  simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
    sweepProjection_apply, ContinuousLinearMap.coe_coe] using
    (mem_sweep_iff_of_height f.toLinearMap c hn hP (y := y))

/-- Sweeping an entire transverse affine hyperplane produces its closed negative
halfspace. In particular no boundedness or absence of lineality is required. -/
theorem sweep_hyperplane (f : V →L[ℝ] ℝ) (c : ℝ) {n : V} (hn : f n = 1) :
    sweep ℝ {x : V | f x = c} n = {x : V | f x ≤ c} := by
  rw [sweep_eq_halfspace_inter_preimage f c hn (fun _ hx => hx)]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  exact and_iff_left (sweepProjection_height f c hn y)

omit [ContinuousSMul ℝ V] in
/-- A relative interior point of a transverse sweep has its base point in the
relative interior of the base. No convexity or closedness is required. -/
theorem mem_intrinsicInterior_of_sub_smul_mem_intrinsicInterior_sweep
    (hn : n ∉ vectorSpan ℝ P) {x : V} (hx : x ∈ P) {t : ℝ}
    (hy : x - t • n ∈ intrinsicInterior ℝ (sweep ℝ P n)) :
    x ∈ intrinsicInterior ℝ P := by
  let A := affineSpan ℝ P
  let B := affineSpan ℝ (sweep ℝ P n)
  have hnB : n ∈ B.direction := by
    rw [direction_affineSpan, vectorSpan_sweep ⟨x, hx⟩]
    exact (le_sup_right : Submodule.span ℝ {n} ≤ _) (Submodule.mem_span_singleton_self n)
  have hAB : A ≤ B := affineSpan_mono ℝ (subset_sweep P n)
  let f : A → B := fun z =>
    ⟨z.val - t • n, by
      simpa only [vadd_eq_add, neg_add_eq_sub] using
        B.vadd_mem_of_mem_direction (B.direction.neg_mem (B.direction.smul_mem t hnB))
          (hAB z.property)⟩
  have hf : Continuous f :=
    (continuous_subtype_val.sub continuous_const).subtype_mk _
  let xA : A := ⟨x, subset_affineSpan ℝ P hx⟩
  have hfy : f xA ∈ interior (Subtype.val ⁻¹' sweep ℝ P n : Set B) := by
    obtain ⟨y, hy, he⟩ := hy
    have heq : y = f xA := Subtype.ext he
    exact heq ▸ hy
  have hpre : f ⁻¹' (Subtype.val ⁻¹' sweep ℝ P n : Set B) ⊆
      (Subtype.val ⁻¹' P : Set A) := by
    intro z hz
    obtain ⟨p, hp, s, _, he⟩ := mem_sweep_iff_exists.mp hz
    dsimp only [f] at he
    have hzp := (sweep_coordinates_unique hn z.property
      (subset_affineSpan ℝ P hp) he).1
    rw [Set.mem_preimage, hzp]
    exact hp
  exact ⟨xA, mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hf.continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hfy)) hpre), rfl⟩

omit [ContinuousSMul ℝ V] in
/-- Sweeping bases in a common transverse affine subspace preserves disjoint
relative interiors. The bases need not be convex or closed. -/
theorem disjoint_intrinsicInterior_sweep {P Q : Set V} {n : V}
    (hn : n ∉ vectorSpan ℝ (P ∪ Q))
    (hPQ : Disjoint (intrinsicInterior ℝ P) (intrinsicInterior ℝ Q)) :
    Disjoint (intrinsicInterior ℝ (sweep ℝ P n)) (intrinsicInterior ℝ (sweep ℝ Q n)) := by
  apply Set.disjoint_left.mpr
  intro y hyP hyQ
  obtain ⟨p, hp, t, _, he⟩ := mem_sweep_iff_exists.mp (intrinsicInterior_subset hyP)
  obtain ⟨q, hq, s, _, he'⟩ := mem_sweep_iff_exists.mp (intrinsicInterior_subset hyQ)
  obtain ⟨hpq, _⟩ := sweep_coordinates_unique hn (subset_affineSpan ℝ _ (Or.inl hp))
    (subset_affineSpan ℝ _ (Or.inr hq))
    (he.symm.trans he')
  subst q
  exact Set.disjoint_left.mp hPQ
    (mem_intrinsicInterior_of_sub_smul_mem_intrinsicInterior_sweep
      (fun hm => hn (vectorSpan_mono ℝ Set.subset_union_left hm)) hp (he ▸ hyP))
    (mem_intrinsicInterior_of_sub_smul_mem_intrinsicInterior_sweep
      (fun hm => hn (vectorSpan_mono ℝ Set.subset_union_right hm)) hq (he' ▸ hyQ))

end Set

namespace Set

open ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {P : Set V} {n : V}

/-- A closed transverse base has a closed sweep, even when unbounded. -/
theorem _root_.IsClosed.sweep {P : Set V} {n : V} (hP : IsClosed P)
    (hn : n ∉ vectorSpan ℝ P) : IsClosed (sweep ℝ P n) := by
  rcases P.eq_empty_or_nonempty with he | hne
  · subst P
    simp only [sweep_empty, isClosed_empty]
  · obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height hne hn
    let f' := LinearMap.toContinuousLinearMap f
    rw [sweep_eq_halfspace_inter_preimage f' c hfn hfP]
    exact (isClosed_le f'.continuous continuous_const).inter
      (hP.preimage (sweepProjection f' c n).continuous)

/-- The prism parameterization is a homeomorphism for every transverse base. -/
noncomputable def sweepHomeomorph (hn : n ∉ vectorSpan ℝ P) :
    (P × {t : ℝ // 0 ≤ t}) ≃ₜ sweep ℝ P n where
  toEquiv := sweepEquiv P n hn
  continuous_toFun := by
    rw [Equiv.toFun_as_coe]
    apply continuous_induced_rng.mpr
    simp only [Function.comp_def, sweepEquiv_apply]
    exact (continuous_subtype_val.comp continuous_fst).sub
      ((continuous_subtype_val.comp continuous_snd).smul continuous_const)
  continuous_invFun := by
    rw [Equiv.invFun_as_coe]
    rcases P.eq_empty_or_nonempty with rfl | hP
    · have : IsEmpty (sweep ℝ (∅ : Set V) n) := by
        rw [sweep_empty]
        infer_instance
      exact continuous_of_discreteTopology
    · obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height hP hn
      let f' := LinearMap.toContinuousLinearMap f
      have hf : Continuous (fun y : sweep ℝ P n => f (y : V)) :=
        f'.continuous.comp continuous_subtype_val
      have hproj : Continuous (fun y : sweep ℝ P n =>
          (y : V) + (c - f y) • n) := by
        simpa only [Function.comp_def, sweepProjection_apply, f',
          LinearMap.coe_toContinuousLinearMap'] using
          (sweepProjection f' c n).continuous.comp continuous_subtype_val
      rw [funext (sweepEquiv_symm_apply hn f c hfn hfP)]
      exact (Continuous.subtype_mk hproj _).prodMk
        (Continuous.subtype_mk (continuous_const.sub hf) _)

/-- Forgetting the topology recovers the algebraic prism equivalence. -/
@[simp]
theorem sweepHomeomorph_toEquiv (hn : n ∉ vectorSpan ℝ P) :
    (sweepHomeomorph hn).toEquiv = sweepEquiv P n hn := (rfl)

/-- The inverse homeomorphism has the same coordinates as the algebraic prism equivalence. -/
@[simp]
theorem sweepHomeomorph_symm_apply (hn : n ∉ vectorSpan ℝ P) (y : sweep ℝ P n) :
    (sweepHomeomorph hn).symm y = (sweepEquiv P n hn).symm y := (rfl)

/-- The topological prism uses the original negative-ray parameterization. -/
@[simp]
theorem sweepHomeomorph_apply (hn : n ∉ vectorSpan ℝ P)
    (z : P × {t : ℝ // 0 ≤ t}) :
    (sweepHomeomorph hn z : V) = z.1.1 - z.2.1 • n := by
  exact sweepEquiv_apply P n hn z

end Set
