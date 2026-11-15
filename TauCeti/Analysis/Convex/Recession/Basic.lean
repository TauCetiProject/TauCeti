/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.AsymptoticCone
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# Recession cones of sets

The recession cone consists of vectors preserving a set under every nonnegative
translation. This definition gives the whole space for the empty set. For a
nonempty set defined by affine inequalities, its recession cone is given by the
corresponding homogeneous inequalities on their linear parts, over any ordered field.

The nonempty assumption matters for homogenization: the closed cone generated
by an empty height-one slice is the zero cone, whereas the recession cone of
the empty set is the whole space by its universal definition.

## Main results

* `Set.recessionCone_preimage_const_add` and `Set.recessionCone_vadd`: translation invariance.
* `AffineEquiv.recessionCone_image`: transport by the linear part of an affine equivalence.
* `PointedCone.recessionCone_coe`: the recession cone of a pointed cone is itself.
* `PointedCone.mem_iff_forall_linear_nonpos`: a cone cut out by affine inequalities is cut out by
  their linear parts.
* `Set.isClosed_recessionCone`: closed sets have closed recession cones.
* `Convex.recessionCone_eq_asymptoticCone`: agreement with asymptotic directions for
  nonempty closed convex sets.
* `AffineMap.eventually_mem_atBot_iff`: the backward-ray eventual-membership criterion.

Adapted from `Mei/Geometry/Convex/Recession.lean` at Mei commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`.
-/

public section

open scoped Pointwise

namespace Set

section Algebra

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid V] [Module R V]

/-- The directions preserving `P` under all nonnegative translations.
This forms a pointed cone even when the original set is neither convex nor closed. -/
def recessionCone (R : Type*) [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {V : Type*} [AddCommMonoid V] [Module R V] (P : Set V) : PointedCone R V where
  carrier := {v | ∀ x ∈ P, ∀ t : R, 0 ≤ t → x + t • v ∈ P}
  zero_mem' := by
    intro x hx t _
    simpa using hx
  add_mem' := by
    intro u v hu hv x hx t ht
    have h := hv (x + t • u) (hu x hx t ht) t ht
    simpa only [smul_add, add_assoc] using h
  smul_mem' := by
    intro c v hv x hx t ht
    -- Cone scalars act through their underlying nonnegative scalars.
    simp only [← Nonneg.coe_smul]
    rw [smul_smul]
    exact hv x hx (t * (c : R)) (mul_nonneg ht c.property)

/-- Membership is precisely preservation of all nonnegative rays based in the set. -/
@[simp]
theorem mem_recessionCone {P : Set V} {v : V} :
    v ∈ recessionCone R P ↔ ∀ x ∈ P, ∀ t : R, 0 ≤ t → x + t • v ∈ P := (Iff.rfl)

/-- The recession cone of the empty set is the whole space, by vacuity. -/
@[simp]
theorem recessionCone_empty : recessionCone R (∅ : Set V) = ⊤ := by
  ext v
  simp [mem_recessionCone]

/-- Every vector preserves the whole ambient space. -/
@[simp]
theorem recessionCone_univ : recessionCone R (Set.univ : Set V) = ⊤ := by
  ext v
  simp [mem_recessionCone]

end Algebra

section Translation

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup V] [Module R V]

/-- Translating a set does not change its recession directions. No convexity,
closedness or nonemptiness assumption is required. -/
@[simp]
theorem recessionCone_preimage_const_add (P : Set V) (a : V) :
    recessionCone R ((fun x => a + x) ⁻¹' P) = recessionCone R P := by
  ext v
  simp only [mem_recessionCone, mem_preimage]
  constructor
  · intro hv x hx t ht
    have he := hv (-a + x) (by simpa using hx) t ht
    simpa [add_assoc] using he
  · intro hv x hx t ht
    simpa only [add_assoc] using hv (a + x) hx t ht

/-- Translating a set leaves its recession cone unchanged. -/
@[simp]
theorem recessionCone_vadd (a : V) (P : Set V) :
    recessionCone R (a +ᵥ P) = recessionCone R P := by
  have he : a +ᵥ P = (fun x => -a + x) ⁻¹' P := by
    ext x
    simp [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  rw [he, recessionCone_preimage_const_add]

end Translation

section Inequalities

variable {R V ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V]

/-- For a nonempty set defined by affine inequalities, recession membership is equivalent
to the homogeneous inequalities. The index family may be infinite. -/
theorem mem_recessionCone_setOf_forall_iff {g : ι → (V →ᵃ[R] R)}
    (hP : {x : V | ∀ i, g i x ≤ 0}.Nonempty) {v : V} :
    v ∈ recessionCone R {x : V | ∀ i, g i x ≤ 0} ↔ ∀ i, (g i).linear v ≤ 0 := by
  constructor
  · intro hv i
    obtain ⟨x, hx⟩ := hP
    by_contra hi
    have hpos : 0 < (g i).linear v := lt_of_not_ge hi
    let t := (1 - g i x) / (g i).linear v
    have ht : 0 ≤ t := div_nonneg (by linarith [hx i]) hpos.le
    have hle := (hv x hx t ht) i
    have heval := (g i).map_vadd x (t • v)
    simp only [vadd_eq_add, map_smul, smul_eq_mul] at heval
    rw [add_comm x, heval] at hle
    dsimp [t] at hle
    rw [div_mul_cancel₀ _ hpos.ne'] at hle
    linarith
  · intro hv x hx t ht i
    have heval := (g i).map_vadd x (t • v)
    simp only [vadd_eq_add, map_smul, smul_eq_mul] at heval
    rw [add_comm x, heval]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ht (hv i)) (hx i)

/-- The exact recession carrier of a nonempty affine-inequality presentation. -/
theorem recessionCone_setOf_forall_eq (g : ι → (V →ᵃ[R] R))
    (hP : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    (recessionCone R {x : V | ∀ i, g i x ≤ 0} : Set V) =
      {v : V | ∀ i, (g i).linear v ≤ 0} := by
  ext v
  exact mem_recessionCone_setOf_forall_iff hP

end Inequalities

section Topology

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid V] [Module R V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousConstSMul R V]

/-- The recession cone of a closed set is closed. No convexity or nonemptiness is needed. -/
theorem isClosed_recessionCone {P : Set V} (hP : IsClosed P) :
    IsClosed (recessionCone R P : Set V) := by
  have he : (recessionCone R P : Set V) =
      ⋂ x : P, ⋂ t : {t : R // 0 ≤ t}, (fun v : V => (x : V) + (t : R) • v) ⁻¹' P := by
    ext v
    simp only [SetLike.mem_coe, mem_recessionCone, Set.mem_iInter, Set.mem_preimage,
      Subtype.forall]
  rw [he]
  exact isClosed_iInter fun x => isClosed_iInter fun t =>
    hP.preimage (continuous_const.add (continuous_id.const_smul (t : R)))

end Topology

section Asymptotic

open Filter

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- For a nonempty closed convex set, recession and asymptotic directions coincide. -/
theorem _root_.Convex.recessionCone_eq_asymptoticCone {P : Set V}
    (hconvex : Convex ℝ P) (hclosed : IsClosed P) (hne : P.Nonempty) :
    (recessionCone ℝ P : Set V) = asymptoticCone ℝ P := by
  ext v
  constructor
  · intro hv
    obtain ⟨p, hp⟩ := hne
    rw [mem_asymptoticCone_iff]
    refine tendsto_id.atTop_smul_const_tendsto_asymptoticNhds v
      |>.asymptoticNhds_vadd_const p |>.frequently (Eventually.frequently ?_)
    filter_upwards [eventually_ge_atTop 0] with t ht
    simpa [vadd_eq_add, add_comm] using (mem_recessionCone.mp hv) p hp t ht
  · intro hv
    rw [SetLike.mem_coe, mem_recessionCone]
    intro p hp t ht
    simpa [vadd_eq_add, add_comm] using
      hconvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hclosed ht hv hp

end Asymptotic

end Set

namespace AffineEquiv

variable {R V W : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- An affine equivalence transports recession directions by its linear part.
No convexity, closedness or nonemptiness assumption is needed. -/
theorem linear_mem_recessionCone_image (e : V ≃ᵃ[R] W) (P : Set V) (v : V) :
    e.linear v ∈ Set.recessionCone R (e '' P) ↔ v ∈ Set.recessionCone R P := by
  have he (x : V) (t : R) : e (x + t • v) = e x + t • e.linear v := by
    simpa only [vadd_eq_add, map_smul, add_comm] using e.map_vadd x (t • v)
  constructor
  · intro hv x hx t ht
    apply e.injective.mem_set_image.mp
    rw [he]
    exact hv (e x) ⟨x, hx, rfl⟩ t ht
  · intro hv y hy t ht
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← he]
    exact ⟨x + t • v, hv x hx t ht, rfl⟩

/-- An affine equivalence maps the recession cone by its linear part. -/
theorem recessionCone_image (e : V ≃ᵃ[R] W) (P : Set V) :
    Set.recessionCone R (e '' P) = (Set.recessionCone R P).map e.linear.toLinearMap := by
  ext w
  obtain ⟨v, rfl⟩ := e.linear.surjective w
  rw [e.linear_mem_recessionCone_image, PointedCone.mem_map]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨u, hu, he⟩
    exact e.linear.injective he ▸ hu

end AffineEquiv

namespace PointedCone

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid V] [Module R V]

/-- The recession cone of the carrier of a pointed cone is the cone itself. -/
@[simp]
theorem recessionCone_coe (C : PointedCone R V) : Set.recessionCone R (C : Set V) = C := by
  ext v
  rw [Set.mem_recessionCone]
  constructor
  · intro hv
    simpa using hv 0 C.zero_mem 1 zero_le_one
  · intro hv x hx t ht
    exact C.add_mem hx (PointedCone.smul_mem C ht hv)

end PointedCone

namespace PointedCone

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V]
  [Module R V] {C : PointedCone R V}

/-- A pointed cone over an ordered field cut out by affine inequalities is already cut out by
their linear parts. -/
theorem mem_iff_forall_linear_nonpos {ι : Type*} (g : ι → (V →ᵃ[R] R))
    (hC : (C : Set V) = {x | ∀ j, g j x ≤ 0}) (x : V) : x ∈ C ↔ ∀ j, (g j).linear x ≤ 0 := by
  have hne : {x : V | ∀ j, g j x ≤ 0}.Nonempty := ⟨0, hC ▸ C.zero_mem⟩
  have hmem := Set.mem_recessionCone_setOf_forall_iff hne (v := x)
  rwa [← hC, recessionCone_coe] at hmem

end PointedCone

namespace AffineMap

open Filter Set

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V]

variable {C : Set V} (f : R →ᵃ[R] V)

/-- A single intersection with a set admitting the backward velocity is equivalent
to membership eventually at negative infinity. No convexity, closedness or
nonemptiness is needed. -/
theorem eventually_mem_atBot_iff (hv : -f.linear 1 ∈ recessionCone R C) :
    (∀ᶠ t in atBot, f t ∈ C) ↔ ∃ t, f t ∈ C := by
  constructor
  · exact Filter.Eventually.exists
  · rintro ⟨a, ha⟩
    apply eventually_atBot.mpr
    refine ⟨a, fun t ht => ?_⟩
    have hm := (mem_recessionCone.mp hv) (f a) ha (a - t) (sub_nonneg.mpr ht)
    have he : f t = f a + (a - t) • (-f.linear 1) := by
      have hlin : f.linear (t - a) = (t - a) • f.linear 1 := by
        simpa only [smul_eq_mul, mul_one] using f.linear.map_smul (t - a) (1 : R)
      calc
        f t = f.linear (t - a) + f a := by
          simpa only [vadd_eq_add, sub_add_cancel] using f.map_vadd a (t - a)
        _ = f a + (a - t) • (-f.linear 1) := by rw [hlin]; module
    rwa [← he] at hm


end AffineMap
