/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.End.Recursion
public import TauCeti.LinearAlgebra.Graded.History.Expansion
public import Mathlib.Combinatorics.Quiver.SingleObj

/-!
# Homogeneous histories of finite recursions

A finite geometric sum is the sum of its homogeneous histories with lengths strictly
below its cutoff. This truncated sum solves the recursion when the cutoff bounds
the nilpotence order. For a finitely generated input range the same finite supports
cover every input below any fixed cutoff, also after every linear output map.

Adapted from `Mei/LinearAlgebra/GradedModule/History/Recursion.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public noncomputable section

open Quiver TauCeti

namespace Module.End

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (U : Module.End R M)

variable [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- The truncated geometric sum is the sum of all contributing homogeneous
histories of lengths strictly below its cutoff; no nilpotence is required. -/
theorem sum_sum_homogeneousHistory_eq_finiteRecursion (r : ℕ) (x : M) :
    (∑ j ∈ Finset.range r,
      ∑ d ∈ ((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).historySupport
          (fun _ => U) (fun _ => ℳ) x,
        ((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).homogeneousHistory
          (fun _ => U) (fun _ => ℳ) d x) =
      U.finiteRecursion r x := by
  rw [finiteRecursion_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Path.sum_homogeneousHistory, Path.composeLinear_loopPow, Path.composeLinear_toPath]

/-- A complete family of supplied supports expands the truncated geometric sum after
linear input and output maps. Histories below the exclusive cutoff may be
omitted if they vanish after the output map. -/
theorem sum_sum_comp_homogeneousHistory_comp_eq_finiteRecursion {E O : Type*}
    [AddCommMonoid E] [Module R E] [AddCommMonoid O] [Module R O]
    (a : E →ₗ[R] M) (b : M →ₗ[R] O) (r : ℕ)
    (S : (j : ℕ) → Finset
      (((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).Degrees (fun _ => ι)))
    (hS : ∀ j < r, ∀ d ∉ S j,
      b.comp ((((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).homogeneousHistory
        (fun _ => U) (fun _ => ℳ) d).comp a) = 0) :
    (∑ j ∈ Finset.range r, ∑ d ∈ S j,
      b.comp ((((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).homogeneousHistory
        (fun _ => U) (fun _ => ℳ) d).comp a)) =
      b.comp ((U.finiteRecursion r).comp a) := by
  calc
    _ = ∑ j ∈ Finset.range r, b.comp ((U ^ j).comp a) := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [Path.composeLinear_loopPow, Path.composeLinear_toPath] using
        Path.sum_comp_homogeneousHistory_comp_eq (fun _ => U) (fun _ => ℳ)
          ((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j) a b (S j)
          (hS j (Finset.mem_range.mp hj))
    _ = b.comp ((U.finiteRecursion r).comp a) := by
      ext y
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, finiteRecursion_apply, map_sum]

/-- For any finite cutoff, a finitely generated input range admits common
finite history supports for all lengths below that cutoff. Their expansion of
the truncated geometric sum remains valid after every linear output map. -/
theorem exists_uniform_history_expansion {E : Type*}
    [AddCommMonoid E] [Module R E] (a : E →ₗ[R] M) (ha : (LinearMap.range a).FG)
    (r : ℕ) :
    ∃ S : (j : ℕ) → Finset
        (((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).Degrees (fun _ => ι)),
      (∀ j < r, ∀ d ∉ S j,
        (((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).homogeneousHistory
          (fun _ => U) (fun _ => ℳ) d).comp a = 0) ∧
      ∀ {O : Type*} [AddCommMonoid O] [Module R O] (b : M →ₗ[R] O),
        (∑ j ∈ Finset.range r, ∑ d ∈ S j,
          b.comp ((((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).homogeneousHistory
             (fun _ => U) (fun _ => ℳ) d).comp a)) =
          b.comp ((U.finiteRecursion r).comp a) := by
  classical
  have hs (j : ℕ) := Path.exists_uniform_historySupport (fun _ => U) (fun _ => ℳ)
    ((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j) a ha
  choose S hS using hs
  refine ⟨S, fun j _ => hS j, ?_⟩
  intro O _ _ b
  exact U.sum_sum_comp_homogeneousHistory_comp_eq_finiteRecursion ℳ a b r S
    (fun j _ d hd => by simp only [hS j d hd, LinearMap.comp_zero])

/-- With finitely generated range of the forcing map `a`, a family solving a
nilpotent recursion has common finite history supports for every input at lengths
below the nilpotency cutoff. The same supports give the solution after every
linear output map. -/
theorem exists_uniform_history_expansion_of_eq_add {E : Type*}
    [AddCommMonoid E] [Module R E] (a x : E →ₗ[R] M) (ha : (LinearMap.range a).FG)
    {r : ℕ} (hU : U ^ r = 0) (hx : x = a + U.comp x) :
    ∃ S : (j : ℕ) → Finset
        (((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).Degrees (fun _ => ι)),
      (∀ j < r, ∀ d ∉ S j,
        (((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).homogeneousHistory
          (fun _ => U) (fun _ => ℳ) d).comp a = 0) ∧
      ∀ {O : Type*} [AddCommMonoid O] [Module R O] (b : M →ₗ[R] O),
        (∑ j ∈ Finset.range r, ∑ d ∈ S j,
          b.comp ((((Hom.toPath (a := SingleObj.star Unit) ()).loopPow j).homogeneousHistory
             (fun _ => U) (fun _ => ℳ) d).comp a)) =
          b.comp x := by
  have hsol : x = (U.finiteRecursion r).comp a := by
    ext y
    have hy := LinearMap.congr_fun hx y
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at hy
    simpa only [LinearMap.comp_apply] using U.eq_finiteRecursion_of_eq_add hU hy
  obtain ⟨S, hS, hs⟩ := U.exists_uniform_history_expansion ℳ a ha r
  exact ⟨S, hS, fun b => by rw [hs, ← hsol]⟩

end Module.End
