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
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# Recession cones of sets

The recession cone consists of vectors preserving a set under every nonnegative
translation. This definition gives the whole space for the empty set. For a
nonempty set defined by affine inequalities, its recession cone is given by the
corresponding homogeneous inequalities on their linear parts. The necessity
uses arbitrarily large parameters, supplied by the Archimedean property of ℝ.

The nonempty assumption matters for homogenization: the closed cone generated
by an empty height-one slice is the zero cone, whereas the recession cone of
the empty set is the whole space by its universal definition.

Adapted from `Mei/Geometry/Convex/Recession.lean` at Mei commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`.
-/

public section

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
theorem recessionCone_preimage_add (P : Set V) (a : V) :
    recessionCone R ((fun x => a + x) ⁻¹' P) = recessionCone R P := by
  ext v
  simp only [mem_recessionCone, mem_preimage]
  constructor
  · intro hv x hx t ht
    have he := hv (-a + x) (by simpa using hx) t ht
    simpa [add_assoc] using he
  · intro hv x hx t ht
    simpa only [add_assoc] using hv (a + x) hx t ht

end Translation

section Inequalities

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V]

/-- For a nonempty set defined by affine inequalities, recession membership is equivalent
to the homogeneous inequalities. The index family may be infinite. -/
theorem mem_recessionCone_setOf_forall_iff {g : ι → (V →ᵃ[ℝ] ℝ)}
    (hP : {x : V | ∀ i, g i x ≤ 0}.Nonempty) {v : V} :
    v ∈ recessionCone ℝ {x : V | ∀ i, g i x ≤ 0} ↔ ∀ i, (g i).linear v ≤ 0 := by
  constructor
  · intro hv i
    obtain ⟨x, hx⟩ := hP
    by_contra hi
    have hpos : 0 < (g i).linear v := lt_of_not_ge hi
    obtain ⟨n, hn⟩ := exists_lt_nsmul hpos (-g i x)
    have hmem := hv x hx (n : ℝ) (Nat.cast_nonneg n)
    have hle := hmem i
    have heval := (g i).map_vadd x ((n : ℝ) • v)
    simp only [vadd_eq_add, map_smul, smul_eq_mul] at heval
    rw [add_comm x, heval] at hle
    simp only [nsmul_eq_mul] at hn
    linarith
  · intro hv x hx t ht i
    have heval := (g i).map_vadd x (t • v)
    simp only [vadd_eq_add, map_smul, smul_eq_mul] at heval
    rw [add_comm x, heval]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ht (hv i)) (hx i)

/-- The exact recession carrier of a nonempty affine-inequality presentation. -/
theorem recessionCone_setOf_forall_eq (g : ι → (V →ᵃ[ℝ] ℝ))
    (hP : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    (recessionCone ℝ {x : V | ∀ i, g i x ≤ 0} : Set V) =
      {v : V | ∀ i, (g i).linear v ≤ 0} := by
  ext v
  exact mem_recessionCone_setOf_forall_iff hP

end Inequalities

section Topology

variable {R V : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid V] [Module R V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousConstSMul R V]

/-- The recession cone of a closed set is closed, as an intersection of affine
preimages of the original set. No convexity or nonemptiness is needed. -/
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

namespace AffineMap

open Filter Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

variable {C : Set V} (f : ℝ →ᵃ[ℝ] V)

/-- A single intersection with a set admitting the backward velocity is equivalent
to membership eventually at negative infinity. No convexity, closedness or
nonemptiness is needed. -/
theorem eventually_mem_atBot_iff (hv : -f.linear 1 ∈ recessionCone ℝ C) :
    (∀ᶠ t in atBot, f t ∈ C) ↔ ∃ t, f t ∈ C := by
  constructor
  · exact Filter.Eventually.exists
  · rintro ⟨a, ha⟩
    apply eventually_atBot.mpr
    refine ⟨a, fun t ht => ?_⟩
    have hm := (mem_recessionCone.mp hv) (f a) ha (a - t) (sub_nonneg.mpr ht)
    have he : f t = f a + (a - t) • (-f.linear 1) := by
      have hlin : f.linear (t - a) = (t - a) • f.linear 1 := by
        simpa only [smul_eq_mul, mul_one] using f.linear.map_smul (t - a) (1 : ℝ)
      calc
        f t = f.linear (t - a) + f a := by
          simpa only [vadd_eq_add, sub_add_cancel] using f.map_vadd a (t - a)
        _ = f a + (a - t) • (-f.linear 1) := by rw [hlin]; module
    rwa [← he] at hm


end AffineMap
