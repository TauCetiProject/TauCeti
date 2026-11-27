/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Endomorphisms on invariant subspaces and quotients

For an endomorphism `g` of a module `M` and a `g`-invariant submodule `W` (an element of Mathlib's
`g.invtSubmodule`), `g` induces endomorphisms of `W` and of `M ⧸ W`. A map intertwining two
endomorphisms pulls invariant submodules back to invariant submodules, and over any ring it
matches the invariant submodules containing its kernel with those in its range.
The annihilator of a `g`-invariant subspace is invariant under the transpose of `g`.

The block upper triangular endomorphism `Module.End.blockTriangular a b x` of `V × W`, the map
`(v, w) ↦ (a v + x w, b w)`, leaves `A × B` invariant when `a` preserves `A`, `b` preserves `B` and
`x` maps `B` into `A`.

## Main definitions

* `Module.End.invtRestrict g hW`, `Module.End.invtQuot g hW`: the endomorphisms that `g` induces on
  a `g`-invariant submodule `W` and on `M ⧸ W`.

## Main results

* `Submodule.comap_mem_invtSubmodule`: the preimage of an invariant submodule under an
  intertwining map is invariant.
* `LinearMap.sum_invtSubmodule_comap`: preimage under an intertwining map is a bijection from the
  invariant submodules in its range to those containing its kernel.
* `Submodule.dualAnnihilator_mem_invtSubmodule`,
  `Submodule.dualCoannihilator_mem_invtSubmodule`: annihilators exchange the submodules invariant
  under `g` and under its transpose.
* `Module.End.prod_mem_invtSubmodule_blockTriangular`: `A × B` is invariant under a block map
  whose diagonal blocks preserve `A` and `B` and whose upper right block maps `B` into `A`.

## References

* Adapted from `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.StableSubspace.endOnSub`, `New.StableSubspace.endOnQuot`, `New.StableSubspace.comap`,
  `New.StableSubspace.sum_comap` and `New.fintypeStableSubspace`, here
  stated for `Mathlib`'s `Module.End.invtSubmodule` and with the invariant block first. The
  annihilator lemmas are the invariance steps of the commutativity proof of the `CommRing`
  instance on `New.Hall` there.
-/

public section

open Module

section Semiring

variable {R M M' : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M']
  [Module R M'] {g : Module.End R M} {g' : Module.End R M'}

/-- The restriction of `g` to a `g`-invariant submodule `W`. -/
def Module.End.invtRestrict (g : Module.End R M) {W : Submodule R M}
    (hW : W ∈ g.invtSubmodule) : Module.End R W :=
  g.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem g).1 hW)

/-- The restriction of `g` to `W` acts as `g`. -/
@[simp]
theorem Module.End.coe_invtRestrict_apply {W : Submodule R M} (hW : W ∈ g.invtSubmodule)
    (x : W) : (g.invtRestrict hW x : M) = g x :=
  (rfl)

/-- The preimage of a `g'`-invariant submodule under a map intertwining `g` with `g'` is
`g`-invariant. -/
theorem Submodule.comap_mem_invtSubmodule (p : M →ₗ[R] M') (hp : ∀ x, p (g x) = g' (p x))
    {U : Submodule R M'} (hU : U ∈ g'.invtSubmodule) : U.comap p ∈ g.invtSubmodule :=
  (Module.End.mem_invtSubmodule _).2 fun x hx ↦ by
    simpa [hp] using (Module.End.mem_invtSubmodule _).1 hU hx

/-- Over a finite semiring, an endomorphism of a finite module has finitely many invariant
submodules. -/
instance Module.End.finite_invtSubmodule [Finite R] [Module.Finite R M] (g : Module.End R M) :
    Finite g.invtSubmodule :=
  have := Module.finite_of_finite R (M := M)
  have : Finite (Submodule R M) := _root_.Finite.of_injective _ SetLike.coe_injective
  _root_.Finite.of_injective _ Subtype.val_injective

end Semiring

section Ring

variable {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  {g : Module.End R M} {g' : Module.End R M'}

/-- The endomorphism of `M ⧸ W` induced by `g`, for a `g`-invariant submodule `W`. -/
def Module.End.invtQuot (g : Module.End R M) {W : Submodule R M}
    (hW : W ∈ g.invtSubmodule) : Module.End R (M ⧸ W) :=
  W.mapQ W g ((Module.End.mem_invtSubmodule g).1 hW)

/-- The map induced on `M ⧸ W` sends the class of `x` to the class of `g x`. -/
@[simp]
theorem Module.End.invtQuot_mk {W : Submodule R M} (hW : W ∈ g.invtSubmodule) (x : M) :
    g.invtQuot hW (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x) :=
  (rfl)

open scoped Classical in
/-- For a map `p` intertwining `g` with `g'`, preimage under `p` is a bijection from the
`g'`-invariant submodules in the range of `p` to the `g`-invariant submodules containing the kernel
of `p`. -/
theorem LinearMap.sum_invtSubmodule_comap {β : Type*} [AddCommMonoid β]
    [Fintype g.invtSubmodule] [Fintype g'.invtSubmodule]
    (p : M →ₗ[R] M') (hp : ∀ x, p (g x) = g' (p x)) (f : g.invtSubmodule → β) :
    ∑ W ∈ Finset.univ.filter (fun W : g.invtSubmodule ↦ LinearMap.ker p ≤ W.val), f W =
      ∑ U ∈ Finset.univ.filter (fun U : g'.invtSubmodule ↦ U.val ≤ LinearMap.range p),
        f ⟨_, Submodule.comap_mem_invtSubmodule p hp U.prop⟩ := by
  -- Image and preimage under `p` are inverse bijections between the two index sets.
  have h_map (W : g.invtSubmodule) : (W : Submodule R M).map p ∈ g'.invtSubmodule := by
    refine (Module.End.mem_invtSubmodule _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨g x, (Module.End.mem_invtSubmodule _).1 W.prop hx, hp x⟩
  refine Finset.sum_nbij' (fun W ↦ ⟨_, h_map W⟩)
    (fun U ↦ ⟨_, Submodule.comap_mem_invtSubmodule p hp U.prop⟩) ?_ ?_ ?_ ?_ ?_
  · simp [LinearMap.map_le_range]
  · simp [LinearMap.ker_le_comap]
  · simp +contextual [Submodule.comap_map_eq]
  · simp +contextual [Submodule.map_comap_eq]
  · simp +contextual [Submodule.comap_map_eq]

end Ring

section Dual

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {g : Module.End R M}

/-- The annihilator of a `g`-invariant submodule is invariant under the transpose of `g`. -/
theorem Submodule.dualAnnihilator_mem_invtSubmodule {W : Submodule R M}
    (hW : W ∈ g.invtSubmodule) : W.dualAnnihilator ∈ Module.End.invtSubmodule g.dualMap := by
  refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun φ hφ ↦
    (Submodule.mem_dualAnnihilator _).2 fun w hw ↦ ?_
  simpa using (Submodule.mem_dualAnnihilator _).1 hφ _
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 hW w hw)

/-- The common zeros of a submodule invariant under the transpose of `g` form a `g`-invariant
submodule. -/
theorem Submodule.dualCoannihilator_mem_invtSubmodule {W : Submodule R (Dual R M)}
    (hW : W ∈ Module.End.invtSubmodule g.dualMap) : W.dualCoannihilator ∈ g.invtSubmodule := by
  refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun v hv ↦
    (Submodule.mem_dualCoannihilator _).2 fun φ hφ ↦ ?_
  simpa using (Submodule.mem_dualCoannihilator _).1 hv _
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 hW φ hφ)

end Dual

/-! ### Block upper triangular endomorphisms -/

namespace Module.End

section BlockTriangular

variable {R V W : Type*} [Semiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid W]
  [Module R W]

/-- If `A` is `a`-invariant, `B` is `b`-invariant and `x` maps `B` into `A`, then `A × B` is
invariant under the block map `(v, w) ↦ (a v + x w, b w)`. -/
theorem prod_mem_invtSubmodule_blockTriangular {a : Module.End R V} {b : Module.End R W}
    {x : W →ₗ[R] V} {A : Submodule R V} {B : Submodule R W} (hA : A ∈ a.invtSubmodule)
    (hB : B ∈ b.invtSubmodule) (hx : B ≤ A.comap x) :
    A.prod B ∈ (a.blockTriangular b x).invtSubmodule := by
  refine (mem_invtSubmodule_iff_forall_mem_of_mem _).2 fun p hp ↦ ?_
  rw [Submodule.mem_prod] at hp ⊢
  have hA := (mem_invtSubmodule_iff_forall_mem_of_mem _).1 hA
  have hB := (mem_invtSubmodule_iff_forall_mem_of_mem _).1 hB
  exact ⟨by simpa using add_mem (hA _ hp.1) (hx hp.2), by simpa using hB _ hp.2⟩

end BlockTriangular

end Module.End
