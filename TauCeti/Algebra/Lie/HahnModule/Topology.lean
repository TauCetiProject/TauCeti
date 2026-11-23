/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HahnModule.Basic
public import TauCeti.RingTheory.LaurentSeries.Lattice

/-!
# The topology of Lie-valued Laurent series

The convolution bracket on `HahnModule ℤ R L` is jointly continuous for the lattice topology,
without any finiteness assumption on the coefficient Lie ring `L`. In particular, for a Lie
algebra over a commutative ring, vector-valued Laurent series carry a continuous Lie bracket
even when they are larger than the scalar extension `R((t)) ⊗[R] L`.

The estimates retain integer orders: brackets of orders at least `r` and `s` have order at
least `r + s`. Perturbing these inputs by terms of orders `M` and `N` changes the bracket only
in orders at least `min (M + s) (min (r + N) (M + N))`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.1, for the order topology
  on formal currents.
-/

public section

noncomputable section

open Filter Topology
open _root_.HahnModule

namespace TauCeti.HahnModule

section Estimates

variable (R L : Type*) [Semiring R] [LieRing L] [Module R L]

/-- The convolution bracket adds lower bounds on the orders of its inputs. -/
theorem lie_mem_lattice {r s : ℤ} {x y : HahnModule ℤ R L}
    (hx : x ∈ lattice R L r) (hy : y ∈ lattice R L s) :
    ⁅x, y⁆ ∈ lattice R L (r + s) := by
  rw [mem_lattice_iff_le_orderTop] at hx hy ⊢
  have h : ((r + s : ℤ) : WithTop ℤ) ≤
      ((of R).symm x).orderTop + ((of R).symm y).orderTop := by
    simpa using add_le_add hx hy
  exact h.trans (orderTop_add_le_lie x y)

/-- The error in a bracket after perturbing both inputs satisfies the three-term order bound. -/
theorem lie_add_sub_lie_mem_lattice {r s M N : ℤ} {x y u v : HahnModule ℤ R L}
    (hx : x ∈ lattice R L r) (hy : y ∈ lattice R L s)
    (hu : u ∈ lattice R L M) (hv : v ∈ lattice R L N) :
    ⁅x + u, y + v⁆ - ⁅x, y⁆ ∈ lattice R L (min (M + s) (min (r + N) (M + N))) := by
  have heq : ⁅x + u, y + v⁆ - ⁅x, y⁆ = ⁅u, y⁆ + ⁅x, v⁆ + ⁅u, v⁆ := by
    simp only [add_lie, lie_add]
    abel
  rw [heq]
  exact add_mem (add_mem
    (lattice_antitone R L (min_le_left _ _) (lie_mem_lattice R L hu hy))
    (lattice_antitone R L ((min_le_right _ _).trans (min_le_left _ _))
      (lie_mem_lattice R L hx hv)))
    (lattice_antitone R L ((min_le_right _ _).trans (min_le_right _ _))
      (lie_mem_lattice R L hu hv))

end Estimates

variable (R L : Type*) [Ring R] [LieRing L] [Module R L]

/-- The convolution bracket of Lie-valued Laurent series is jointly continuous in the lattice
topology, including for infinite-dimensional coefficient Lie algebras. No compatibility between
the coefficient module structure and the Lie bracket is required. -/
theorem continuous_lie :
    Continuous fun p : HahnModule ℤ R L × HahnModule ℤ R L ↦ ⁅p.1, p.2⁆ := by
  let B : HahnModule ℤ R L →+ HahnModule ℤ R L →+ HahnModule ℤ R L :=
    AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ ⁅x, y⁆) (lie_add x)) fun x x' ↦ by
      ext y
      simp [add_lie]
  have h0 := hasBasis_nhds_zero_lattice R L
  refine continuous_of_continuousAt_zero₂ B ?_ (fun x ↦ ?_) (fun y ↦ ?_)
  · rw [ContinuousAt, nhds_prod_eq, map_zero, (h0.prod h0).tendsto_iff h0]
    refine fun N _ ↦ ⟨(max N 0, max N 0), ⟨trivial, trivial⟩, fun p hp ↦ ?_⟩
    simpa [B] using lattice_antitone R L (by omega : N ≤ max N 0 + max N 0)
      (lie_mem_lattice R L hp.1 hp.2)
  · rw [ContinuousAt, map_zero, h0.tendsto_iff h0]
    refine fun N _ ↦ ⟨N - ((of R).symm x).order, trivial, fun y hy ↦ ?_⟩
    simpa [B] using lie_mem_lattice R L (mem_lattice_order R L x) hy
  · rw [ContinuousAt, map_zero, AddMonoidHom.zero_apply, h0.tendsto_iff h0]
    refine fun N _ ↦ ⟨N - ((of R).symm y).order, trivial, fun x hx ↦ ?_⟩
    simpa [B] using lie_mem_lattice R L hx (mem_lattice_order R L y)

end TauCeti.HahnModule
