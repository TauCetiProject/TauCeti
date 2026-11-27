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
# Finiteness of kernels and cokernels of composites

For linear maps `f : M → N` and `g : N → P`, the cokernels fit into an exact sequence
`N ⧸ range f → P ⧸ range (g ∘ f) → P ⧸ range g → 0` (`LinearMap.exact_cokerToCokerComp_factor`),
so the cokernel of `g ∘ f` is finitely generated when those of `f` and `g` are. Over a noetherian
ring, the kernel of `g ∘ f` is likewise finitely generated when those of `f` and `g` are: it is an
extension of a submodule of `ker g` by `ker f`.

## Main results

* `Module.Finite.quotient_range_comp`: the cokernel of `g ∘ f` is finite if those of `f` and `g`
  are.
* `Module.Finite.ker_comp`: over a noetherian ring, the kernel of `g ∘ f` is finite if those of `f`
  and `g` are.
* `TauCeti.Module.Finite.of_exact`: if `M → N → P → 0` is exact and `M` and `P` are finite
  over a semiring `R`, then `N` is finite over `R` whenever `N` is an additive commutative group.
-/

public section

open Submodule

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

namespace Module.Finite

open LinearMap (ker_le_ker_comp)

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

namespace TauCeti.Module.Finite

section Semiring

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommMonoid P] [Module R P]

/-- If `M → N → P → 0` is exact and `M` and `P` are finitely generated over a semiring `R`, then
so is `N`, provided `N` is an additive commutative group.

This generalizes Mathlib's `Module.Finite.of_exact` from `[Ring R]` to `[Semiring R]`. -/
theorem of_exact {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h_exact : Function.Exact f g) (h_surj : Function.Surjective g)
    [_root_.Module.Finite R M] [_root_.Module.Finite R P] : _root_.Module.Finite R N := by
  classical
  obtain ⟨t, ht⟩ := _root_.Module.finite_def.mp ‹_root_.Module.Finite R P›
  choose lift hlift using h_surj
  let P₁ : Submodule R N := Submodule.span R (lift '' (t : Set P))
  have hP₁ : P₁.map g = ⊤ := by
    rw [Submodule.map_span, ← Set.image_comp]
    simpa only [Function.comp_def, hlift, Set.image_id'] using ht
  have htop : P₁ ⊔ LinearMap.range f = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    have hx : g x ∈ P₁.map g := by rw [hP₁]; exact Submodule.mem_top
    obtain ⟨z, hz, hzx⟩ := hx
    have hker : x - z ∈ LinearMap.ker g := LinearMap.mem_ker.mpr <| by
      calc g (x - z) = g x + g (-z) := by rw [sub_eq_add_neg, map_add]
        _ = g (z + -z) := by rw [← hzx, ← map_add]
        _ = 0 := by simp
    rw [LinearMap.exact_iff.mp h_exact] at hker
    exact Submodule.mem_sup.mpr ⟨z, hz, x - z, hker, add_sub_cancel _ _⟩
  refine ⟨?_⟩
  rw [← htop, LinearMap.range_eq_map]
  exact (Submodule.fg_span (t.finite_toSet.image lift)).sup
    (_root_.Module.Finite.fg_top.map f)

end Semiring

end TauCeti.Module.Finite
