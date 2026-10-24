/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The germ kernel of a group action

For a group `G` acting on a topological space `X`, the germ kernel at a point `x` is the subgroup
`TauCeti.MulAction.germKernel G x` of the elements acting as the identity on some neighbourhood of
`x`, that is, the elements whose germ at `x` is the germ of the identity. Equivalently, `g` lies in
the germ kernel at `x` exactly when `x` is in the interior of the fixed set of `g`. The germ kernel
lies between the kernel of the action, made of the elements acting trivially on all of `X`, and
the stabilizer of `x`.

For the presentation `[X/G]` of an orbifold by a group action, the germ kernel at `x` is the
ineffective part of the isotropy at `x`: the isotropy elements whose action cannot be seen near
`x`. The effective reduction of the action discards these elements, while the orbifold keeps them.
Transport along the action conjugates germ kernels, as it does stabilizers.

## Main declarations

* `TauCeti.MulAction.germKernel G x`: the elements of `G` acting as the identity near `x`.
* `TauCeti.MulAction.mem_germKernel_iff_mem_interior_fixedBy`: `g` is in the germ kernel at `x`
  exactly when `x` is in the interior of the fixed set of `g`.
* `TauCeti.MulAction.ker_toPermHom_le_germKernel`, `TauCeti.MulAction.germKernel_le_stabilizer`:
  the germ kernel contains the kernel of the action and is contained in the stabilizer.
* `TauCeti.MulAction.germKernel_smul_eq_germKernel_map_conj`: the germ kernel at `h • x` is the
  conjugate by `h` of the germ kernel at `x`.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Ch. 1, for ineffective orbifolds and the
  ineffective kernel of their local group actions.
-/

public section

open Filter MulAction Set Topology

namespace TauCeti.MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]

/-- The germ kernel of the action of `G` at `x`: the subgroup of the elements of `G` that act as
the identity on a neighbourhood of `x`. -/
def germKernel (x : X) : Subgroup G where
  carrier := {g | ∀ᶠ y in 𝓝 x, g • y = y}
  one_mem' := Eventually.of_forall (one_smul G)
  mul_mem' {g h} hg hh := by
    filter_upwards [hg, hh] with y hgy hhy
    rw [mul_smul, hhy, hgy]
  inv_mem' {g} hg := by
    filter_upwards [hg] with y hy
    exact inv_smul_eq_iff.mpr hy.symm

variable {G}

@[simp]
theorem mem_germKernel {x : X} {g : G} : g ∈ germKernel G x ↔ ∀ᶠ y in 𝓝 x, g • y = y :=
  Iff.rfl

/-- An element is in the germ kernel at `x` exactly when `x` is in the interior of its fixed
set. -/
theorem mem_germKernel_iff_mem_interior_fixedBy {x : X} {g : G} :
    g ∈ germKernel G x ↔ x ∈ interior (fixedBy X g) := by
  rw [mem_interior_iff_mem_nhds, ← eventually_mem_set]
  simp only [mem_germKernel, mem_fixedBy]

/-- An element of the germ kernel at `x` fixes `x`. -/
theorem germKernel_le_stabilizer (x : X) : germKernel G x ≤ stabilizer G x :=
  fun _ hg ↦ hg.self_of_nhds

/-- An element acting trivially on all of `X` is in the germ kernel at every point. -/
theorem ker_toPermHom_le_germKernel (x : X) : (toPermHom G X).ker ≤ germKernel G x :=
  fun g hg ↦ Eventually.of_forall fun y ↦ by
    simpa using Equiv.Perm.ext_iff.mp (MonoidHom.mem_ker.mp hg) y

/-- The germ kernel at `h • x` is the conjugate by `h` of the germ kernel at `x`. -/
theorem germKernel_smul_eq_germKernel_map_conj [ContinuousConstSMul G X] (h : G) (x : X) :
    germKernel G (h • x) = (germKernel G x).map (MulAut.conj h).toMonoidHom := by
  have hmap : map (h • ·) (𝓝 x) = 𝓝 (h • x) := (Homeomorph.smul h).map_nhds_eq x
  ext g
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_germKernel, mem_germKernel, ← hmap,
    eventually_map]
  refine eventually_congr (Eventually.of_forall fun y ↦ ?_)
  rw [mul_smul, mul_smul, inv_smul_eq_iff]

end TauCeti.MulAction
