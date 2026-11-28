/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Synonym
public import Mathlib.LinearAlgebra.Pi

/-!
# Coordinate identities for `C⋆ᵐᵒᵈ(A, Π i, E i)` and `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`

Mathlib computes the coordinates of `0`, `x + y`, `x - y`, `-x` and `c • x` in the type synonym
`C⋆ᵐᵒᵈ(A, Π i, E i)` (`WithCStarModule.add_apply` and its siblings). This file adds:

* `WithCStarModule.sum_apply`: coordinates of finite sums in `C⋆ᵐᵒᵈ(A, Π i, E i)`.
* `WithCStarModule.fstLinearMap`, `WithCStarModule.sndLinearMap`: bundled linear projections
  out of `C⋆ᵐᵒᵈ(A, E × F)`.
* `TauCeti.WithCStarModule.piOpLinearEquiv`: the right `A`-linear identification
  `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) ≃ₗ[Aᵐᵒᵖ] (ι → Aᵐᵒᵖ)`.
* `WithCStarModule.sum_op_smul_single_one`: finite standard-basis expansion in
  `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`.
-/

public section

open MulOpposite
open scoped WithCStarModule

namespace WithCStarModule

section Prod

variable (R A E F : Type*) [Semiring R] [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

/-- The first projection `C⋆ᵐᵒᵈ(A, E × F) →ₗ[R] E` as an `R`-linear map. -/
def fstLinearMap : C⋆ᵐᵒᵈ(A, E × F) →ₗ[R] E :=
  LinearMap.fst R E F ∘ₗ (WithCStarModule.linearEquiv R A (E × F)).toLinearMap

/-- The second projection `C⋆ᵐᵒᵈ(A, E × F) →ₗ[R] F` as an `R`-linear map. -/
def sndLinearMap : C⋆ᵐᵒᵈ(A, E × F) →ₗ[R] F :=
  LinearMap.snd R E F ∘ₗ (WithCStarModule.linearEquiv R A (E × F)).toLinearMap

@[simp]
theorem fstLinearMap_apply (x : C⋆ᵐᵒᵈ(A, E × F)) : fstLinearMap R A E F x = x.fst := (rfl)

@[simp]
theorem sndLinearMap_apply (x : C⋆ᵐᵒᵈ(A, E × F)) : sndLinearMap R A E F x = x.snd := (rfl)

end Prod

variable {A ι κ : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)]

/-- A coordinate of a finite sum in `C⋆ᵐᵒᵈ(A, Π i, E i)` is the sum of the coordinates. -/
@[simp]
theorem sum_apply (s : Finset κ) (x : κ → C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι) :
    (∑ k ∈ s, x k) i = ∑ k ∈ s, x k i :=
  Finset.sum_apply i s fun k ↦ equiv A (Π i, E i) (x k)

/-- Every vector in `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` expands in the standard basis `i ↦ Pi.single i 1`. -/
theorem sum_op_smul_single_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Ring A]
    (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    ∑ i : ι, op (v i) • (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)) = v := by
  apply (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (ι → A)).injective
  rw [map_sum]; ext j
  simpa [MulOpposite.smul_eq_mul_unop, Pi.single_apply] using Fintype.sum_ite_eq j fun i ↦ v i

end WithCStarModule

namespace TauCeti.WithCStarModule

/-- Right `A`-linear identification between the module synonym `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` and
`(ι → Aᵐᵒᵖ)`. -/
def piOpLinearEquiv (A ι : Type*) [Ring A] :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) ≃ₗ[Aᵐᵒᵖ] (ι → Aᵐᵒᵖ) :=
  _root_.WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (ι → A) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ ↦ MulOpposite.opLinearEquiv Aᵐᵒᵖ)

@[simp] theorem piOpLinearEquiv_apply {A ι : Type*} [Ring A] (w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (i : ι) :
    piOpLinearEquiv A ι w i = op (w i) := by
  simp [piOpLinearEquiv]

@[simp] theorem piOpLinearEquiv_symm_apply {A ι : Type*} [Ring A] (v : ι → Aᵐᵒᵖ) (i : ι) :
    (piOpLinearEquiv A ι).symm v i = unop (v i) := by
  simp [piOpLinearEquiv]

end TauCeti.WithCStarModule
