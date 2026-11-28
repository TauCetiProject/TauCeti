/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ElectricalNetwork.Basic
public import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Data.Fintype.Lattice

/-!
# The maximum principle for electrical networks

A function is harmonic at a vertex if its conductance-weighted increments there sum to zero.
At a harmonic vertex where the function has a maximum, every neighbour has the same value.
Consequently, in a component meeting the boundary, a function harmonic at the interior vertices
of that component is bounded above there by a boundary value in the same component. If every
component meets the boundary, any two harmonic extensions of the same boundary values coincide.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., Proposition 9.1.
* R. Lyons and Y. Peres, *Probability on Trees and Networks*, §2.1.
-/

public section

namespace TauCeti.ElectricalNetwork

variable {V : Type*} [Fintype V] (N : ElectricalNetwork V) {f : V → ℝ} {x y : V}

/-- The net current flowing into a vertex, as a linear functional on potentials. -/
noncomputable def netInwardCurrent (x : V) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ y, N.cond x y • ((LinearMap.proj y : (V → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj x)

/-- The net inward current is the sum of the conductance-weighted potential differences. -/
theorem netInwardCurrent_apply (x : V) (f : V → ℝ) :
    N.netInwardCurrent x f = ∑ y, N.cond x y * (f y - f x) := by
  simp [netInwardCurrent, LinearMap.sum_apply]

/-- A potential is harmonic at a vertex when its net current there is zero. -/
def HarmonicAt (f : V → ℝ) (x : V) : Prop :=
  f ∈ (N.netInwardCurrent x).ker

/-- Harmonicity at a vertex is the vanishing of its net inward current. -/
theorem harmonicAt_iff_netInwardCurrent_eq_zero :
    N.HarmonicAt f x ↔ N.netInwardCurrent x f = 0 := by
  rw [HarmonicAt, LinearMap.mem_ker]

/-- The zero-current equation at a harmonic vertex. -/
theorem harmonicAt_def : N.HarmonicAt f x ↔ ∑ y, N.cond x y * (f y - f x) = 0 := by
  rw [harmonicAt_iff_netInwardCurrent_eq_zero, netInwardCurrent_apply]

/-- Harmonicity in terms of the conductance-weighted sum of the potential. -/
theorem harmonicAt_iff : N.HarmonicAt f x ↔ ∑ y, N.cond x y * f y = N.weight x * f x := by
  simp [harmonicAt_def, mul_sub, Finset.sum_sub_distrib, N.weight_def, Finset.sum_mul, sub_eq_zero]

/-- Every constant potential is harmonic. -/
@[simp] theorem harmonicAt_const (c : ℝ) (x : V) : N.HarmonicAt (fun _ => c) x := by
  simp [harmonicAt_def]

/-- Every potential is harmonic at a vertex of weight zero. -/
@[simp] theorem harmonicAt_of_weight_eq_zero (hx : N.weight x = 0) : N.HarmonicAt f x := by
  simp [harmonicAt_def, N.weight_eq_zero_iff.mp hx]

/-- A potential is harmonic at a vertex if and only if its negative is harmonic there. -/
@[simp] theorem harmonicAt_neg_iff : N.HarmonicAt (-f) x ↔ N.HarmonicAt f x := by
  unfold HarmonicAt
  exact (N.netInwardCurrent x).ker.neg_mem_iff

/-- Adding a constant to a potential does not change its harmonicity at a vertex. -/
@[simp] theorem harmonicAt_add_const_iff (c : ℝ) :
    N.HarmonicAt (fun v => f v + c) x ↔ N.HarmonicAt f x := by
  have hc := N.harmonicAt_const c x
  unfold HarmonicAt at hc ⊢
  exact (N.netInwardCurrent x).ker.add_mem_iff_left hc

/-- Multiplication by a nonzero scalar does not change harmonicity at a vertex. -/
@[simp] theorem harmonicAt_const_smul_iff {c : ℝ} (hc : c ≠ 0) :
    N.HarmonicAt (c • f) x ↔ N.HarmonicAt f x := by
  unfold HarmonicAt
  exact (N.netInwardCurrent x).ker.smul_mem_iff hc

variable {N}

/-- Negating a potential preserves harmonicity. -/
theorem HarmonicAt.neg (hf : N.HarmonicAt f x) : N.HarmonicAt (-f) x := by
  unfold HarmonicAt at *
  exact (N.netInwardCurrent x).ker.neg_mem hf

/-- The sum of two potentials harmonic at a vertex is harmonic there. -/
theorem HarmonicAt.add {g : V → ℝ} (hf : N.HarmonicAt f x) (hg : N.HarmonicAt g x) :
    N.HarmonicAt (f + g) x := by
  unfold HarmonicAt at *
  exact (N.netInwardCurrent x).ker.add_mem hf hg

/-- The difference of two potentials harmonic at a vertex is harmonic there. -/
theorem HarmonicAt.sub {g : V → ℝ} (hf : N.HarmonicAt f x) (hg : N.HarmonicAt g x) :
    N.HarmonicAt (f - g) x := by
  unfold HarmonicAt at *
  exact (N.netInwardCurrent x).ker.sub_mem hf hg

/-- A scalar multiple of a harmonic potential is harmonic. -/
theorem HarmonicAt.const_smul (hf : N.HarmonicAt f x) (c : ℝ) : N.HarmonicAt (c • f) x := by
  unfold HarmonicAt at *
  exact (N.netInwardCurrent x).ker.smul_mem c hf

/-- Adding a constant to a harmonic potential preserves harmonicity. -/
theorem HarmonicAt.add_const (hf : N.HarmonicAt f x) (c : ℝ) :
    N.HarmonicAt (fun y => f y + c) x :=
  hf.add (N.harmonicAt_const c x)

/-- At a harmonic vertex where no neighbour has a larger value, all neighbours have the same
value as the vertex. -/
theorem HarmonicAt.eq_of_forall_le_of_adj (hf : N.HarmonicAt f x)
    (hmax : ∀ z, N.graph.Adj x z → f z ≤ f x) (hxy : N.graph.Adj x y) : f y = f x := by
  have hterm (z : V) : N.cond x z * (f z - f x) ≤ 0 := by
    rcases eq_or_ne x z with rfl | hxz
    · simp
    rcases (N.nonneg x z).eq_or_lt with hz | hz
    · simp [← hz]
    exact mul_nonpos_of_nonneg_of_nonpos hz.le
      (sub_nonpos.mpr (hmax z (N.graph_adj.mpr ⟨hxz, hz⟩)))
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos (fun z _ => hterm z)).mp
    (N.harmonicAt_def.mp hf) y (Finset.mem_univ y)
  simpa only [mul_eq_zero, (N.cond_pos_of_adj hxy).ne', false_or, sub_eq_zero] using hzero

variable (N)

/-- **Maximum principle.** If the component of a vertex meets the boundary and the potential
is harmonic at the interior vertices of that component, the vertex value is bounded above by
a boundary value in the same component. -/
theorem exists_mem_le_of_harmonicAt {B : Set V} (x : V) (hB : ∃ b ∈ B, N.graph.Reachable x b)
    (hf : ∀ v, N.graph.Reachable x v → v ∉ B → N.HarmonicAt f v) :
    ∃ b ∈ B, N.graph.Reachable x b ∧ f x ≤ f b := by
  let : Nonempty {v // N.graph.Reachable x v} := ⟨⟨x, .rfl⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun v : {v // N.graph.Reachable x v} => f v)
  have hle {v : V} (hv : N.graph.Reachable x v) : f v ≤ f m := hm ⟨v, hv⟩
  obtain ⟨b, hb, hxb⟩ := hB
  obtain ⟨p⟩ := m.property.symm.trans hxb
  by_contra! hlt
  let S : Set V := {v | N.graph.Reachable x v ∧ f v = f m}
  have hout {v : V} (hv : v ∈ S) : v ∉ B := fun hvB =>
    (hlt v hvB hv.1).not_ge (hv.2 ▸ hle .rfl)
  -- On the way to the boundary, the walk would have to leave the set of maximizers.
  obtain ⟨d, -, hd, hd'⟩ := p.exists_boundary_dart S ⟨m.property, rfl⟩ (fun h => hout h hb)
  have heq := (hf _ hd.1 (hout hd)).eq_of_forall_le_of_adj
    (fun z hz => hd.2 ▸ hle (hd.1.trans hz.reachable)) d.adj
  exact hd' ⟨hd.1.trans d.adj.reachable, heq.trans hd.2⟩

/-- If the component of a vertex meets the boundary, two potentials harmonic at its interior
vertices have the same value at the vertex when they agree on its boundary vertices. -/
theorem apply_eq_of_eqOn_of_harmonicAt {B : Set V} {g : V → ℝ} (x : V)
    (hB : ∃ b ∈ B, N.graph.Reachable x b)
    (hfg : Set.EqOn f g (B ∩ {v | N.graph.Reachable x v}))
    (hf : ∀ v, N.graph.Reachable x v → v ∉ B → N.HarmonicAt f v)
    (hg : ∀ v, N.graph.Reachable x v → v ∉ B → N.HarmonicAt g v) : f x = g x := by
  have hdiff v hxv hv := (hf v hxv hv).sub (hg v hxv hv)
  obtain ⟨b, hb, hxb, hupper⟩ := N.exists_mem_le_of_harmonicAt x hB hdiff
  obtain ⟨c, hc, hxc, hlower⟩ :=
    N.exists_mem_le_of_harmonicAt x hB (fun v hxv hv => (hdiff v hxv hv).neg)
  exact le_antisymm (by simpa [Pi.sub_apply, hfg ⟨hb, hxb⟩] using hupper)
    (by simpa [Pi.sub_apply, hfg ⟨hc, hxc⟩] using hlower)

/-- Two potentials harmonic off a boundary that meets every component coincide if they agree
on the boundary. -/
theorem eq_of_eqOn_of_harmonicAt {B : Set V} {g : V → ℝ} (hfg : Set.EqOn f g B)
    (hf : ∀ v ∉ B, N.HarmonicAt f v) (hg : ∀ v ∉ B, N.HarmonicAt g v)
    (hB : ∀ v, ∃ b ∈ B, N.graph.Reachable v b) : f = g := by
  exact funext fun x => N.apply_eq_of_eqOn_of_harmonicAt x (hB x) (hfg.mono Set.inter_subset_left)
    (fun v _ hv => hf v hv) (fun v _ hv => hg v hv)

end TauCeti.ElectricalNetwork
