/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.BrokenPath
public import TauCeti.Topology.PathSpace.Moore.Sampling

/-!
# Straightening the arcs of sampled Moore paths

The straightening homotopy `TauCeti.straightenArcs ρ r f` from a path `f : C(I, X)` to its broken
path `TauCeti.brokenPath ρ r f` through the vertices `f (i/r)`, for a path interpolation `ρ` on a
set `U` of pairs of points, is constructed in `TauCeti.Topology.PathSpace.BrokenPath`. This file
applies it to Moore paths.

For Moore paths the construction is applied to the reparametrization `γ.toUnitPath` to the unit
interval and the duration is kept: `TauCeti.MoorePath.arcStraightening` is a homotopy, on the
Moore paths whose arcs lie in `U`, from the inclusion to the broken paths of the same duration,
through Moore paths with the same end points, duration and sampled vertices. It restricts to free
Moore loops (`TauCeti.MooreFreeLoopSpace.arcStraightening`). For a compact family of Moore paths
in a pseudometric space and an entourage `U`, every sufficiently fine subdivision has arcs within
`U` (`TauCeti.MoorePath.exists_subset_arcsWithin`).

In the finite-dimensional approximation of the free loop space of a Riemannian manifold by broken
geodesics, the interpolating paths are the minimizing geodesics between points closer than the
convexity radius. The homotopy then joins a compact family of loops to broken geodesics through
their sampled vertices, run with the original duration split equally among the arcs; their
reparametrization at unit speed is a separate step.

## Main definitions

* `TauCeti.MoorePath.arcsWithin U r`: the Moore paths whose `r` arcs lie in `U`.
* `TauCeti.MoorePath.arcStraightening`, `TauCeti.MooreFreeLoopSpace.arcStraightening`: the
  homotopies of Moore paths and of free Moore loops from the inclusion to the broken paths.

## Main results

* `TauCeti.MoorePath.sample_arcStraighteningMap`: the homotopy fixes the sampled vertices.
* `TauCeti.MoorePath.exists_subset_arcsWithin`: compact families are finely subdivided into arcs
  within an entourage.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public noncomputable section

open scoped NNReal unitInterval
open Set unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-! ### Moore paths -/

namespace MoorePath

variable {ρ : X × X → C(I, X)} {U : Set (X × X)} {r : ℕ}

variable (U r) in
/-- The Moore paths whose reparametrization to the unit interval has its `r` arcs within `U`. -/
def arcsWithin : Set (MoorePath X) :=
  {γ | ArcsWithin U r γ.toUnitPath}

@[simp]
theorem mem_arcsWithin {γ : MoorePath X} : γ ∈ arcsWithin U r ↔ ArcsWithin U r γ.toUnitPath :=
  Iff.rfl

/-- The straightening of a Moore path of length zero whose arcs lie in `U` is constant at its
start point. -/
private theorem straightenArcs_toUnitPath_of_length_eq_zero (hρ : IsPathInterpolation ρ U)
    {γ : MoorePath X} (hγ : ArcsWithin U r γ.toUnitPath) (hr : 0 < r) (h : γ.length = 0)
    (t s : I) : straightenArcs ρ r γ.toUnitPath t s = γ.source := by
  have hγc := (congrArg toUnitPath (eq_refl_of_length_eq_zero h)).trans (toUnitPath_refl _)
  have hx := hγ 0 hr 0
  rw [hγc] at hx ⊢
  exact straightenArcs_const hρ hx t s

/-- The straightening homotopy on the unit interval, as a continuous map of the time, the Moore
path and the parameter. -/
private def straightenArcsUnit (hρ : IsPathInterpolation ρ U) (hr : 0 < r) :
    C((I × arcsWithin U r) × I, X) where
  toFun q := straightenArcs ρ r (q.1.2 : MoorePath X).toUnitPath q.1.1 q.2
  continuous_toFun := (continuous_straightenArcs hρ hr
    (continuous_toUnitPath.comp continuous_subtypeVal) fun γ ↦ γ.property).comp
      (by fun_prop : Continuous fun q : (I × arcsWithin U r) × I ↦ (q.1.2, q.1.1, q.2))

private theorem straightenArcsUnit_apply (hρ : IsPathInterpolation ρ U) (hr : 0 < r) (t s : I)
    (γ : arcsWithin U r) :
    straightenArcsUnit hρ hr ((t, γ), s) = straightenArcs ρ r (γ : MoorePath X).toUnitPath t s :=
  (rfl)

/-- The straightening homotopy of Moore paths whose arcs lie in `U`: at time `t` the Moore path
of the same length as `γ` running along `straightenArcs ρ r γ.toUnitPath t`. -/
def arcStraighteningMap (hρ : IsPathInterpolation ρ U) (hr : 0 < r) :
    C(I × arcsWithin U r, MoorePath X) where
  toFun p := (ofUnitPath ((straightenArcsUnit hρ hr).curry p)).rescale (p.2 : MoorePath X).length
  continuous_toFun := by
    refine (continuous_ofUnitPath.comp (straightenArcsUnit hρ hr).curry.continuous)
      |>.moorePath_rescale_of_forall_eq_source (by fun_prop) fun p hp t ↦ ?_
    -- A Moore path of length zero is constant, and so is its straightening.
    obtain ⟨t', γ, hγ⟩ := p
    simp only [Function.comp_apply, ofUnitPath_apply, source_ofUnitPath,
      ContinuousMap.curry_apply, straightenArcsUnit_apply,
      straightenArcs_toUnitPath_of_length_eq_zero hρ hγ hr hp]

variable (hρ : IsPathInterpolation ρ U) (hr : 0 < r)

@[simp]
theorem length_arcStraighteningMap (t : I) (γ : arcsWithin U r) :
    (arcStraighteningMap hρ hr (t, γ)).length = (γ : MoorePath X).length := by
  simp [arcStraighteningMap]

/-- The straightening homotopy of Moore paths, reparametrized to the unit interval, is the
straightening homotopy of the reparametrized paths. -/
theorem toUnitPath_arcStraighteningMap (t : I) (γ : arcsWithin U r) (s : I) :
    (arcStraighteningMap hρ hr (t, γ)).toUnitPath s =
      straightenArcs ρ r (γ : MoorePath X).toUnitPath t s := by
  obtain ⟨γ, hγ⟩ := γ
  rcases eq_or_ne γ.length 0 with h | h
  · simp only [toUnitPath_apply, length_arcStraighteningMap, h, zero_mul]
    simp [arcStraighteningMap, h, straightenArcs_toUnitPath_of_length_eq_zero hρ hγ hr h,
      straightenArcsUnit_apply]
  · simp only [toUnitPath_apply, arcStraighteningMap, ContinuousMap.coe_mk, length_rescale,
      rescale_apply, length_ofUnitPath, one_mul, ofUnitPath_apply, ContinuousMap.curry_apply,
      straightenArcsUnit_apply]
    rw [mul_div_cancel_left₀ _ h, unitInterval.coe_toNNReal, projIcc_val]

/-- At time zero the straightening homotopy is the inclusion. -/
@[simp]
theorem arcStraighteningMap_zero (γ : arcsWithin U r) :
    arcStraighteningMap hρ hr (0, γ) = γ := by
  obtain ⟨γ, hγ⟩ := γ
  have h : (straightenArcsUnit hρ hr).curry (0, ⟨γ, hγ⟩) = γ.toUnitPath := by
    ext s
    exact straightenArcs_zero hρ hr hγ s
  simp only [arcStraighteningMap, ContinuousMap.coe_mk, h, ofUnitPath_toUnitPath_rescale_length]

@[simp]
theorem source_arcStraighteningMap (t : I) (γ : arcsWithin U r) :
    (arcStraighteningMap hρ hr (t, γ)).source = (γ : MoorePath X).source := by
  rw [← toUnitPath_zero, toUnitPath_arcStraighteningMap,
    straightenArcs_source hρ hr γ.property, toUnitPath_zero]

@[simp]
theorem target_arcStraighteningMap (t : I) (γ : arcsWithin U r) :
    (arcStraighteningMap hρ hr (t, γ)).target = (γ : MoorePath X).target := by
  rw [← toUnitPath_one, toUnitPath_arcStraighteningMap, straightenArcs_target hρ hr γ.property,
    toUnitPath_one]

/-- The straightening homotopy fixes the sampled vertices. -/
@[simp]
theorem sample_arcStraighteningMap (t : I) (γ : arcsWithin U r) :
    (arcStraighteningMap hρ hr (t, γ)).sample r = (γ : MoorePath X).sample r := by
  funext i
  rw [sample_eq_toUnitPath_arcPoint, sample_eq_toUnitPath_arcPoint, toUnitPath_arcStraighteningMap,
    straightenArcs_arcPoint_zero hρ γ.property i.isLt]

/-- The broken path through the sampled vertices of a Moore path whose arcs lie in `U`, of the
same length. -/
def brokenPathMap : C(arcsWithin U r, MoorePath X) :=
  (arcStraighteningMap hρ hr).comp ⟨fun γ ↦ (1, γ), by fun_prop⟩

@[simp]
theorem brokenPathMap_apply (γ : arcsWithin U r) :
    brokenPathMap hρ hr γ = arcStraighteningMap hρ hr (1, γ) :=
  (rfl)

/-- The broken path through the sampled vertices of a Moore path has the same length. -/
theorem length_brokenPathMap (γ : arcsWithin U r) :
    (brokenPathMap hρ hr γ).length = (γ : MoorePath X).length := by
  rw [brokenPathMap_apply, length_arcStraighteningMap]

/-- The broken path of a Moore path, reparametrized to the unit interval, is the broken path of
its reparametrization. -/
theorem toUnitPath_brokenPathMap (γ : arcsWithin U r) (s : I) :
    (brokenPathMap hρ hr γ).toUnitPath s = brokenPath ρ r (γ : MoorePath X).toUnitPath s := by
  rw [brokenPathMap_apply, toUnitPath_arcStraighteningMap, straightenArcs_one]

/-- **Straightening the arcs of Moore paths**: on the Moore paths whose arcs lie in `U`, a
homotopy from the inclusion to the broken paths through the sampled vertices, through Moore paths
of the same length, end points and sampled vertices. -/
def arcStraightening :
    ContinuousMap.Homotopy (ContinuousMap.subtypeVal _) (brokenPathMap hρ hr) where
  toContinuousMap := arcStraighteningMap hρ hr
  map_zero_left := arcStraighteningMap_zero hρ hr
  map_one_left _ := (rfl)

@[simp]
theorem arcStraightening_apply (t : I) (γ : arcsWithin U r) :
    arcStraightening hρ hr (t, γ) = arcStraighteningMap hρ hr (t, γ) :=
  (rfl)

end MoorePath

/-! ### Free Moore loops -/

namespace MooreFreeLoopSpace

variable {ρ : X × X → C(I, X)} {U : Set (X × X)} {r : ℕ}

variable (U r) in
/-- The free Moore loops whose reparametrization to the unit interval has its `r` arcs within
`U`. -/
def arcsWithin : Set (MooreFreeLoopSpace X) :=
  toMoorePath ⁻¹' MoorePath.arcsWithin U r

@[simp]
theorem mem_arcsWithin {γ : MooreFreeLoopSpace X} :
    γ ∈ arcsWithin U r ↔ ArcsWithin U r γ.toMoorePath.toUnitPath :=
  Iff.rfl

/-- The consecutive closed sampled vertices of a free Moore loop whose `r` arcs lie in `U` form
pairs in `U`. -/
theorem closedSample_mem_of_mem_arcsWithin {γ : MooreFreeLoopSpace X} (hγ : γ ∈ arcsWithin U r)
    (i : Fin r) : (γ.closedSample r i.castSucc, γ.closedSample r i.succ) ∈ U := by
  rw [closedSample_eq_toUnitPath γ i.pos, closedSample_eq_toUnitPath γ i.pos, Fin.val_castSucc,
    Fin.val_succ, ← unitInterval.arcPoint_one]
  exact mem_arcsWithin.1 hγ i i.isLt 1

/-- Each sampled vertex of a free Moore loop whose `n + 1` arcs lie in `U` forms a pair in `U`
with the preceding one, the last vertex preceding the first. -/
theorem sample_sub_one_mem_of_mem_arcsWithin {n : ℕ} {γ : MooreFreeLoopSpace X}
    (hγ : γ ∈ arcsWithin U (n + 1)) (i : Fin (n + 1)) :
    (γ.toMoorePath.sample (n + 1) (i - 1), γ.toMoorePath.sample (n + 1) i) ∈ U := by
  have h := closedSample_mem_of_mem_arcsWithin hγ (i - 1)
  rwa [closedSample_castSucc, closedSample_succ, sub_add_cancel] at h

/-- A free Moore loop whose arcs lie in `U`, as a Moore path whose arcs lie in `U`. -/
def toArcsWithin (γ : arcsWithin U r) : MoorePath.arcsWithin U r :=
  ⟨(γ : MooreFreeLoopSpace X).toMoorePath, MoorePath.mem_arcsWithin.2 (mem_arcsWithin.1 γ.property)⟩

@[simp]
theorem coe_toArcsWithin (γ : arcsWithin U r) :
    (toArcsWithin γ : MoorePath X) = (γ : MooreFreeLoopSpace X).toMoorePath :=
  (rfl)

@[fun_prop]
theorem continuous_toArcsWithin : Continuous (toArcsWithin : arcsWithin U r → _) :=
  (continuous_toMoorePath.comp continuous_subtypeVal).subtype_mk _

variable (hρ : IsPathInterpolation ρ U) (hr : 0 < r)

/-- The straightening homotopy of free Moore loops whose arcs lie in `U`; it keeps the loops
closed because it fixes the end points. -/
def arcStraighteningMap : C(I × arcsWithin U r, MooreFreeLoopSpace X) where
  toFun p := ⟨MoorePath.arcStraighteningMap hρ hr (p.1, toArcsWithin p.2), by
    rw [MoorePath.target_arcStraighteningMap, MoorePath.source_arcStraighteningMap,
      coe_toArcsWithin, p.2.val.target_eq_source]⟩
  continuous_toFun := isEmbedding_toMoorePath.continuous_iff.2 <|
    (MoorePath.arcStraighteningMap hρ hr).continuous.comp (by fun_prop)

@[simp]
theorem toMoorePath_arcStraighteningMap (t : I) (γ : arcsWithin U r) :
    (arcStraighteningMap hρ hr (t, γ)).toMoorePath =
      MoorePath.arcStraighteningMap hρ hr
        (t, toArcsWithin γ) :=
  (rfl)

/-- The straightening homotopy of free Moore loops keeps the base point. -/
@[simp]
theorem basepoint_arcStraighteningMap (t : I) (γ : arcsWithin U r) :
    (arcStraighteningMap hρ hr (t, γ)).basepoint = (γ : MooreFreeLoopSpace X).basepoint := by
  rw [← source_toMoorePath, toMoorePath_arcStraighteningMap, MoorePath.source_arcStraighteningMap,
    coe_toArcsWithin, source_toMoorePath]

/-- The broken loop through the sampled vertices of a free Moore loop whose arcs lie in `U`. -/
def brokenPathMap : C(arcsWithin U r, MooreFreeLoopSpace X) :=
  (arcStraighteningMap hρ hr).comp ⟨fun γ ↦ (1, γ), by fun_prop⟩

@[simp]
theorem toMoorePath_brokenPathMap (γ : arcsWithin U r) :
    (brokenPathMap hρ hr γ).toMoorePath =
      MoorePath.brokenPathMap hρ hr (toArcsWithin γ) :=
  (rfl)

/-- **Straightening the arcs of free Moore loops**: on the free Moore loops whose arcs lie in
`U`, a homotopy from the inclusion to the broken loops through the sampled vertices. -/
def arcStraightening :
    ContinuousMap.Homotopy (ContinuousMap.subtypeVal _) (brokenPathMap hρ hr) where
  toContinuousMap := arcStraighteningMap hρ hr
  map_zero_left _ := ext (MoorePath.arcStraighteningMap_zero hρ hr _)
  map_one_left _ := (rfl)

@[simp]
theorem arcStraightening_apply (t : I) (γ : arcsWithin U r) :
    arcStraightening hρ hr (t, γ) = arcStraighteningMap hρ hr (t, γ) :=
  (rfl)

end MooreFreeLoopSpace

/-! ### Compact families -/

namespace MoorePath

variable {X : Type*} [PseudoMetricSpace X]

/-- **Compact families have fine subdivisions with arcs within an entourage.** For a compact
family `K` of Moore paths and a neighbourhood `U` of the diagonal in the uniformity, there is
`N > 0` such that every Moore path of `K` has its `r` arcs within `U`, for every `r ≥ N`. -/
theorem exists_subset_arcsWithin {K : Set (MoorePath X)} (hK : IsCompact K) {U : Set (X × X)}
    (hU : U ∈ uniformity X) : ∃ N : ℕ, 0 < N ∧ ∀ r ≥ N, K ⊆ arcsWithin U r := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.1 hU
  obtain ⟨N, hN, h⟩ := exists_sample_arc_dist_lt hK hε
  refine ⟨N, hN, fun r hr γ hγ i hi a ↦ hεU ?_⟩
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (Nat.zero_le i).trans_lt hi
  rw [← sample_eq_toUnitPath_arcPoint γ ⟨i, hi⟩]
  refine h r hr γ hγ ⟨i, hi⟩ (arcPoint r i a) ?_ ?_ <;> rw [coe_arcPoint hi]
  · exact div_le_div_of_nonneg_right (le_add_of_nonneg_right a.property.1) hrpos.le
  · exact div_le_div_of_nonneg_right (by linarith [a.property.2]) hrpos.le

end MoorePath

namespace MooreFreeLoopSpace

variable {X : Type*} [PseudoMetricSpace X]

/-- The samples of a free Moore loop whose `n + 1` arcs are shorter than `r` are at distance less
than `r` from the preceding ones, the last one preceding the first one. -/
theorem dist_sample_sub_one_lt_of_mem_arcsWithin {n : ℕ} {r : ℝ} {γ : MooreFreeLoopSpace X}
    (hγ : γ ∈ arcsWithin {p : X × X | dist p.1 p.2 < r} (n + 1)) (i : Fin (n + 1)) :
    dist (γ.toMoorePath.sample (n + 1) i) (γ.toMoorePath.sample (n + 1) (i - 1)) < r := by
  rw [dist_comm]
  exact sample_sub_one_mem_of_mem_arcsWithin hγ i

end MooreFreeLoopSpace

end TauCeti
