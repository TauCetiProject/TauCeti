/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ElectricalNetwork.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Lattice

/-!
# The maximum principle for electrical networks

A function is harmonic at a vertex if its conductance-weighted increments there sum to zero.
At a harmonic vertex where the function has a maximum, every neighbour has the same value.
Consequently, if the function is harmonic off a boundary meeting each connected component, each
vertex value is bounded above by a boundary value. This controls the interior values of a Dirichlet
solution.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., Proposition 9.1.
* R. Lyons and Y. Peres, *Probability on Trees and Networks*, §2.1.
-/

public section

namespace TauCeti.ElectricalNetwork

variable {V : Type*} [Fintype V] (N : ElectricalNetwork V) {f : V → ℝ} {x y : V}

/-- A potential is harmonic at a vertex when its net current there is zero. -/
def IsHarmonicAt (f : V → ℝ) (x : V) : Prop :=
  ∑ y, N.cond x y * (f y - f x) = 0

/-- The zero-current equation at a harmonic vertex. -/
theorem isHarmonicAt_def : N.IsHarmonicAt f x ↔ ∑ y, N.cond x y * (f y - f x) = 0 := Iff.rfl

/-- Harmonicity in terms of the conductance-weighted sum of the potential. -/
theorem isHarmonicAt_iff : N.IsHarmonicAt f x ↔ ∑ y, N.cond x y * f y = N.weight x * f x := by
  simp [IsHarmonicAt, mul_sub, Finset.sum_sub_distrib, N.weight_def, Finset.sum_mul, sub_eq_zero]

/-- Every constant potential is harmonic. -/
@[simp] theorem isHarmonicAt_const (c : ℝ) (x : V) : N.IsHarmonicAt (fun _ => c) x := by
  simp [IsHarmonicAt]

/-- Every potential is harmonic at a vertex of weight zero. -/
theorem isHarmonicAt_of_weight_eq_zero (hx : N.weight x = 0) : N.IsHarmonicAt f x := by
  simp [IsHarmonicAt, N.weight_eq_zero_iff.mp hx]

variable {N}

/-- Negating a potential preserves harmonicity. -/
theorem IsHarmonicAt.neg (hf : N.IsHarmonicAt f x) : N.IsHarmonicAt (-f) x := by
  simpa [isHarmonicAt_iff, Finset.sum_neg_distrib] using hf

/-- At a harmonic vertex where no neighbour has a larger value, all neighbours have the same
value as the vertex. -/
theorem IsHarmonicAt.eq_of_adj_of_forall_le (hf : N.IsHarmonicAt f x)
    (hmax : ∀ z, N.graph.Adj x z → f z ≤ f x) (hxy : N.graph.Adj x y) : f y = f x := by
  have hterm (z : V) : N.cond x z * (f z - f x) ≤ 0 := by
    rcases eq_or_ne x z with rfl | hxz
    · simp
    rcases (N.nonneg x z).eq_or_lt with hz | hz
    · simp [← hz]
    exact mul_nonpos_of_nonneg_of_nonpos hz.le
      (sub_nonpos.mpr (hmax z (N.graph_adj.mpr ⟨hxz, hz⟩)))
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos (fun z _ => hterm z)).mp hf y (Finset.mem_univ y)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (N.cond_pos_of_adj hxy).ne')

variable (N)

/-- **Maximum principle.** If each component meets the boundary and a potential is harmonic
off the boundary, every vertex value is bounded above by a boundary value. -/
theorem exists_mem_le_of_isHarmonicAt {B : Set V} (hB : ∀ v, ∃ b ∈ B, N.graph.Reachable v b)
    (hf : ∀ v ∉ B, N.IsHarmonicAt f v) (x : V) : ∃ b ∈ B, f x ≤ f b := by
  let : Nonempty V := ⟨x⟩
  obtain ⟨m, hm⟩ := Finite.exists_max f
  obtain ⟨b, hb, ⟨p⟩⟩ := hB m
  by_contra! hlt
  have hout {v : V} (hv : f v = f m) : v ∉ B := fun hvB =>
    (hlt v hvB).not_ge (hv ▸ hm x)
  -- On the way to the boundary, the walk would have to leave the set of maximizers.
  obtain ⟨d, -, hd, hd'⟩ := p.exists_boundary_dart {v | f v = f m} rfl (fun h => hout h hb)
  exact hd' (((hf _ (hout hd)).eq_of_adj_of_forall_le (fun z _ => hd ▸ hm z) d.adj).trans hd)

end TauCeti.ElectricalNetwork
