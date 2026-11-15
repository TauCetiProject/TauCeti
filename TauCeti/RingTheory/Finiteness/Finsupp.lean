/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Noetherian.Basic
import TauCeti.LinearAlgebra.Exact

/-!
# Finiteness in exact sequences and composites

For linear maps `f : M → N` and `g : N → P`, the cokernels fit into an exact sequence
`N ⧸ range f → P ⧸ range (g ∘ f) → P ⧸ range g → 0` (`LinearMap.exact_cokerToCokerComp_factor`),
so the cokernel of `g ∘ f` is finitely generated when those of `f` and `g` are. Over a noetherian
ring, any module sitting in an exact sequence between two finitely generated modules is finitely
generated without assuming the right-hand map is surjective, and the kernel of `g ∘ f` is likewise
finitely generated when those of `f` and `g` are: it is an extension of a submodule of `ker g` by
`ker f`.

## Main results

* `Module.Finite.of_exact_of_isNoetherianRing`: over a noetherian ring, if `M → N → P` is exact and
  `M` and `P` are finite, then `N` is finite.
* `Module.Finite.quotient_range_comp`: the cokernel of `g ∘ f` is finite if those of `f` and `g`
  are.
* `Module.Finite.ker_comp`: over a noetherian ring, the kernel of `g ∘ f` is finite if those of `f`
  and `g` are.
-/

public section

open Submodule

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

namespace Module.Finite

open LinearMap (ker_le_ker_comp)

/-- Over a noetherian ring, a module sitting in an exact sequence between two finitely generated
modules is finitely generated (without assuming the right-hand map is surjective). -/
theorem of_exact_of_isNoetherianRing [IsNoetherianRing R] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) [Module.Finite R M] [Module.Finite R P] :
    Module.Finite R N :=
  of_exact (f := f) (g := g.rangeRestrict)
    (fun y ↦ Subtype.ext_iff.trans (hfg y)) g.surjective_rangeRestrict

/-- If the cokernels of `f : M → N` and `g : N → P` are finitely generated, then so is the
cokernel of `g ∘ f`. -/
theorem quotient_range_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    [Module.Finite R (N ⧸ LinearMap.range f)] [Module.Finite R (P ⧸ LinearMap.range g)] :
    Module.Finite R (P ⧸ LinearMap.range (g ∘ₗ f)) :=
  .of_exact (f.exact_cokerToCokerComp_factor g) (factor_surjective _)

/-- Over a noetherian ring, if the kernels of `f : M → N` and `g : N → P` are finitely generated,
then so is the kernel of `g ∘ f`. -/
theorem ker_comp [IsNoetherianRing R] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    [Module.Finite R (LinearMap.ker f)] [Module.Finite R (LinearMap.ker g)] :
    Module.Finite R (LinearMap.ker (g ∘ₗ f)) := by
  -- The kernel of `g ∘ f` is an extension of a submodule of `ker g` by `ker f`.
  refine Module.Finite.iff_fg.mpr (fg_of_fg_map_of_fg_inf_ker f ?_ ?_)
  · exact FG.of_le_of_isNoetherian (T := LinearMap.ker g)
      (map_le_iff_le_comap.mpr (LinearMap.ker_comp f g).le)
  · rw [inf_eq_right.mpr (ker_le_ker_comp f g)]
    exact Module.Finite.iff_fg.mp inferInstance

end Module.Finite
