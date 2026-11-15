/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Order.Lattice
public import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Deforming a simplex onto a horn

The horn opposite a vertex `a` is the union of the boundary facets other than the facet
opposite `a`. In barycentric coordinates, a point lies in this horn precisely when some
coordinate other than `a` vanishes. This file constructs a strong deformation retraction of
a finite simplex of positive dimension onto its horn.

Subtract the smallest non-apex coordinate from every non-apex coordinate, and transfer the
removed mass to the apex. At least one non-apex coordinate then vanishes. Interpolating the
amount transferred gives a deformation which fixes the horn pointwise. This is the local
geometric deformation used in an elementary simplicial collapse: the omitted facet is the
free face, and the horn is the part retained in the complex.

Horn retractions support the geometric construction of singular horn fillers. The endpoint
`hornRetraction a` extends any continuous map `f` defined on the horn to a map defined on the
simplex by composition; `hornRetraction_apply_coe` proves that this extension restricts to `f`.
For the simplex on `Fin (n + 2)`, whose facets are the images of the face maps
`StdSimplex.map j.succAbove`, continuous maps on the facets of a horn which agree wherever two
facets meet glue to a continuous map on the horn, and hence extend to the whole simplex
(`exists_continuousMap_comp_map_succAbove`).

The simplex and its topology are Mathlib's `Convexity.StdSimplex`; the deformation is bundled
as a `ContinuousMap.HomotopyRel`. No finiteness assumption on an ambient complex is involved.

## References

* C. Rourke and B. Sanderson, *Introduction to Piecewise-Linear Topology* (1972), Chapter 3,
  for elementary collapse and its geometric deformation retraction.
-/

public noncomputable section

namespace Convexity.StdSimplex

open Set unitInterval

variable {ι : Type*}

attribute [local instance] Classical.decEq

/-- The union of the facets of a simplex other than the facet opposite `a`. -/
def horn (a : ι) : Set (StdSimplex ℝ ι) :=
  {x | ∃ i, i ≠ a ∧ x.weights i = 0}

/-- Membership in the horn is vanishing of a non-apex barycentric coordinate. -/
@[simp]
theorem mem_horn_iff {a : ι} {x : StdSimplex ℝ ι} :
    x ∈ horn a ↔ ∃ i, i ≠ a ∧ x.weights i = 0 := (Iff.rfl)

variable [Fintype ι] [Nontrivial ι]

/-- The smallest barycentric coordinate away from the apex. -/
def hornDepth (a : ι) (x : StdSimplex ℝ ι) : ℝ := by
  classical
  exact (Finset.univ.erase a).inf' (Finset.univ_nontrivial.erase_nonempty (a := a))
    (fun i => x.weights i)

/-- Compute the horn depth as the finite minimum over the vertices other than the apex. -/
theorem hornDepth_def (a : ι) (x : StdSimplex ℝ ι) :
    hornDepth a x = (Finset.univ.erase a).inf'
      (Finset.univ_nontrivial.erase_nonempty (a := a)) (fun i => x.weights i) := (rfl)

/-- The minimum non-apex weight is nonnegative. -/
@[simp]
theorem hornDepth_nonneg (a : ι) (x : StdSimplex ℝ ι) : 0 ≤ hornDepth a x := by
  classical
  exact (Finset.le_inf'_iff _ _).2 fun i _ => x.weights_nonneg i

/-- The minimum non-apex weight is bounded by every non-apex weight. -/
theorem hornDepth_le (a : ι) (x : StdSimplex ℝ ι) {i : ι} (hi : i ≠ a) :
    hornDepth a x ≤ x.weights i := by
  classical
  exact Finset.inf'_le _ (by simp [hi])

/-- A point lies in the horn exactly when its minimum non-apex weight is zero. -/
@[simp]
theorem hornDepth_eq_zero_iff {a : ι} {x : StdSimplex ℝ ι} :
    hornDepth a x = 0 ↔ x ∈ horn a := by
  classical
  constructor
  · intro h
    obtain ⟨i, hi, hmin⟩ :=
      Finset.exists_mem_eq_inf' (Finset.univ_nontrivial.erase_nonempty (a := a))
        (fun i => x.weights i)
    exact ⟨i, (Finset.mem_erase.mp hi).1, hmin.symm.trans h⟩
  · rintro ⟨i, hi, hxi⟩
    exact le_antisymm (hxi ▸ hornDepth_le a x hi) (hornDepth_nonneg a x)

/-- The minimum non-apex weight varies continuously with the simplex point. -/
@[fun_prop]
theorem continuous_hornDepth (a : ι) : Continuous (hornDepth a) := by
  classical
  exact Continuous.finset_inf'_apply _ fun i _ => continuous_weights_apply ℝ i

/-- Move a fraction `t` of the least non-apex weight to the apex, equally from each of the
other coordinates. At time one this lands in the horn; points of the horn are stationary. -/
def hornDeformation (a : ι) (t : I) (x : StdSimplex ℝ ι) : StdSimplex ℝ ι := by
  classical
  let m := (t : ℝ) * hornDepth a x
  let w : ι → ℝ := fun i => if i = a then
    x.weights i + (Fintype.card ι - 1 : ℝ) * m else x.weights i - m
  have hm : 0 ≤ m := mul_nonneg t.2.1 (hornDepth_nonneg a x)
  have hmi {i : ι} (hi : i ≠ a) : m ≤ x.weights i :=
    (mul_le_of_le_one_left (hornDepth_nonneg a x) t.2.2).trans (hornDepth_le a x hi)
  have hcard : 0 ≤ (Fintype.card ι - 1 : ℝ) := by
    have hc : (1 : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
    linarith
  refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, ?_⟩
  · intro i
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    by_cases hi : i = a
    · simp only [w, hi, ite_true]
      exact add_nonneg (x.weights_nonneg a) (mul_nonneg hcard hm)
    · simp only [w, hi, ite_false]
      exact sub_nonneg.mpr (hmi hi)
  · rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    have hw : ∑ i, w i = x.weights a + (Fintype.card ι - 1 : ℝ) * m +
        ∑ i ∈ Finset.univ.erase a, (x.weights i - m) := by
      calc
        ∑ i, w i = (∑ i ∈ Finset.univ.erase a, w i) + w a :=
          (Finset.sum_erase_add _ _ (Finset.mem_univ a)).symm
        _ = _ := by
          have hsumw : (∑ i ∈ Finset.univ.erase a, w i) =
              ∑ i ∈ Finset.univ.erase a, (x.weights i - m) :=
            Finset.sum_congr rfl fun i hi => ite_eq_right (Finset.mem_erase.mp hi).1
          rw [hsumw]
          simp only [w, ite_true]
          ring
    rw [hw, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a)]
    have hx := x.total_of_fintype
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)] at hx
    have hc : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      simpa only [Nat.cast_one] using
        (Nat.cast_sub (R := ℝ) (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)))
    simp only [Finset.card_univ, nsmul_eq_mul, hc]
    linarith

/-- Barycentric coordinates of the horn deformation. -/
@[simp]
theorem hornDeformation_weights (a : ι) (t : I) (x : StdSimplex ℝ ι) (i : ι) :
    (hornDeformation a t x).weights i = if i = a then
      x.weights i + (Fintype.card ι - 1 : ℝ) * ((t : ℝ) * hornDepth a x)
    else x.weights i - (t : ℝ) * hornDepth a x := by
  classical
  rfl

/-- At time zero the horn deformation is the identity. -/
@[simp]
theorem hornDeformation_zero (a : ι) (x : StdSimplex ℝ ι) : hornDeformation a 0 x = x := by
  ext i
  simp

/-- The horn deformation fixes every point of the horn at every time. -/
@[simp]
theorem hornDeformation_of_mem {a : ι} {x : StdSimplex ℝ ι} (hx : x ∈ horn a) (t : I) :
    hornDeformation a t x = x := by
  ext i
  simp [hornDepth_eq_zero_iff.mpr hx]

/-- The endpoint of the horn deformation belongs to the horn. -/
theorem hornDeformation_one_mem (a : ι) (x : StdSimplex ℝ ι) :
    hornDeformation a 1 x ∈ horn a := by
  classical
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nontrivial.erase_nonempty (a := a))
      (fun i => x.weights i)
  refine ⟨i, (Finset.mem_erase.mp hi).1, ?_⟩
  simp [hornDeformation_weights, (Finset.mem_erase.mp hi).1, hornDepth_def, ← hmin]

/-- The horn deformation is jointly continuous in time and in the simplex point. -/
@[fun_prop]
theorem continuous_hornDeformation (a : ι) :
    Continuous (fun p : I × StdSimplex ℝ ι => hornDeformation a p.1 p.2) := by
  classical
  rw [(isEmbedding_toFun_comp_weights ℝ ι).continuous_iff]
  refine continuous_pi fun i => ?_
  simp only [Function.comp_apply, hornDeformation_weights]
  split_ifs
  · exact ((continuous_weights_apply ℝ i).comp continuous_snd).add
      (continuous_const.mul (continuous_subtype_val.comp continuous_fst |>.mul
        ((continuous_hornDepth a).comp continuous_snd)))
  · exact ((continuous_weights_apply ℝ i).comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst |>.mul
        ((continuous_hornDepth a).comp continuous_snd))

/-- The continuous retraction of a simplex onto its horn. -/
def hornRetraction (a : ι) : C(StdSimplex ℝ ι, horn a) :=
  ⟨fun x => ⟨hornDeformation a 1 x, hornDeformation_one_mem a x⟩,
    (continuous_hornDeformation a |>.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

/-- The horn retraction, viewed in the simplex, is the endpoint of the deformation. -/
@[simp]
theorem coe_hornRetraction (a : ι) (x : StdSimplex ℝ ι) :
    (hornRetraction a x : StdSimplex ℝ ι) = hornDeformation a 1 x := (rfl)

/-- The horn retraction fixes the horn pointwise. -/
@[simp]
theorem hornRetraction_apply_coe (a : ι) (x : horn a) : hornRetraction a x = x :=
  Subtype.ext (hornDeformation_of_mem x.2 1)

/-- A strong deformation retraction of the standard simplex onto its horn. -/
def hornDeformationRetraction (a : ι) :
    (ContinuousMap.id (StdSimplex ℝ ι)).HomotopyRel
      ((ContinuousMap.subtypeVal (horn a)).comp (hornRetraction a)) (horn a) where
  toFun p := hornDeformation a p.1 p.2
  continuous_toFun := continuous_hornDeformation a
  map_zero_left := hornDeformation_zero a
  map_one_left x := (coe_hornRetraction a x).symm
  prop' t _x hx := hornDeformation_of_mem hx t

/-- The strong deformation retraction evaluates by the barycentric horn deformation. -/
@[simp]
theorem hornDeformationRetraction_apply (a : ι) (t : I) (x : StdSimplex ℝ ι) :
    hornDeformationRetraction a (t, x) = hornDeformation a t x := (rfl)

section Facets

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- Continuous maps on the facets of the horn opposite `a` which agree wherever two facets meet
extend to a continuous map on the whole simplex: there is a continuous map on the simplex whose
composite with each face map `StdSimplex.map j.succAbove`, `j ≠ a`, is the given map on that
facet. -/
theorem exists_continuousMap_comp_map_succAbove (a : Fin (n + 2))
    (g : ∀ j : Fin (n + 2), j ≠ a → C(StdSimplex ℝ (Fin (n + 1)), X))
    (hg : ∀ j hj k hk (y z : StdSimplex ℝ (Fin (n + 1))),
      y.map j.succAbove = z.map k.succAbove → g j hj y = g k hk z) :
    ∃ F : C(StdSimplex ℝ (Fin (n + 2)), X),
      ∀ j hj, F.comp ⟨map j.succAbove, continuous_map ℝ _⟩ = g j hj := by
  -- The facets of the horn, as a disjoint union, map onto the horn by the face maps.
  let p : C(Σ j : {j : Fin (n + 2) // j ≠ a}, StdSimplex ℝ (Fin (n + 1)), horn a) :=
    ⟨fun s => ⟨s.2.map s.1.1.succAbove, s.1.1, s.1.2, weights_map_succAbove_self _ _⟩,
      continuous_sigma fun j => (continuous_map ℝ j.1.succAbove).subtype_mk _⟩
  have hsurj : Function.Surjective p := by
    rintro ⟨x, i, hi, hx⟩
    obtain ⟨y, rfl⟩ := (mem_range_map_succAbove_iff i x).2 hx
    exact ⟨⟨⟨i, hi⟩, y⟩, rfl⟩
  -- A continuous surjection from a compact space onto a Hausdorff space is a quotient map.
  have : T2Space (StdSimplex ℝ (Fin (n + 2))) :=
    (isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).t2Space
  have hq : Topology.IsQuotientMap p := p.continuous.isClosedMap.isQuotientMap p.continuous hsurj
  let G : C(Σ j : {j : Fin (n + 2) // j ≠ a}, StdSimplex ℝ (Fin (n + 1)), X) :=
    ⟨fun s => g s.1.1 s.1.2 s.2, continuous_sigma fun j => (g j.1 j.2).continuous⟩
  have hG : Function.FactorsThrough G p := fun s t hst =>
    hg _ _ _ _ _ _ (congrArg Subtype.val hst)
  refine ⟨(hq.lift G hG).comp (hornRetraction a), fun j hj => ?_⟩
  ext y
  have hy : hornRetraction a (y.map j.succAbove) = p ⟨⟨j, hj⟩, y⟩ :=
    hornRetraction_apply_coe a (p ⟨⟨j, hj⟩, y⟩)
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hy]
  exact DFunLike.congr_fun (hq.lift_comp G hG) ⟨⟨j, hj⟩, y⟩

end Facets

end Convexity.StdSimplex
