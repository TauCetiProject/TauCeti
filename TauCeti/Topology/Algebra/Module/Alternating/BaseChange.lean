/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import TauCeti.LinearAlgebra.BilinearMap.BaseChange

/-!
# Extension of scalars for alternating one- and two-forms

Let `E` and `F` be topological modules over a commutative ring `𝕜`, where `F` is also a module
over a commutative `𝕜`-algebra `A`. A continuous alternating one-form `α : E [⋀^Fin 1]→L[𝕜] F`
has an `A`-linear extension `A ⊗[𝕜] E →ₗ[A] F`, and a continuous alternating two-form
`ω : E [⋀^Fin 2]→L[𝕜] F` has an `A`-bilinear extension to `A ⊗[𝕜] E`, which is again
alternating. For `𝕜 = ℝ` and `A = ℂ` these are the complex-multilinear extensions of
complex-valued real forms to the complexification of `E`. They evaluate complex-valued
differential forms on complexified tangent vectors, such as those of type `(1,0)` and `(0,1)`.

## Main declarations

* `ContinuousAlternatingMap.liftBaseChangeFinOne`: the `A`-linear extension of a one-form.
* `ContinuousAlternatingMap.liftBaseChangeFinTwo`: the `A`-bilinear extension of a two-form,
  through `LinearMap.BilinMap.liftBaseChange`.
* `ContinuousAlternatingMap.liftBaseChangeFinTwo_apply_of_eq_smul`: a relation
  `ω(v, w) = c • α(N(v, w))` between a two-form and a one-form persists to their extensions.
* `ContinuousAlternatingMap.liftBaseChangeFinTwo_swap`,
  `ContinuousAlternatingMap.liftBaseChangeFinTwo_self`: the extension of a two-form is
  antisymmetric and alternating.
-/

public section

open TensorProduct
open LinearMap (BilinMap)

namespace ContinuousAlternatingMap

variable {𝕜 E F : Type*} [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  (A : Type*) [CommSemiring A] [Algebra 𝕜 A] [Module A F] [IsScalarTower 𝕜 A F]

/-- The `A`-linear extension `A ⊗[𝕜] E →ₗ[A] F` of a one-form `α : E [⋀^Fin 1]→L[𝕜] F` with
values in an `A`-module. -/
noncomputable def liftBaseChangeFinOne (α : E [⋀^Fin 1]→L[𝕜] F) : A ⊗[𝕜] E →ₗ[A] F :=
  ((ofSubsingleton 𝕜 E F (0 : Fin 1)).symm α).toLinearMap.liftBaseChange A

/-- The extension of a one-form is `LinearMap.liftBaseChange` of the underlying linear map. -/
theorem liftBaseChangeFinOne_def (α : E [⋀^Fin 1]→L[𝕜] F) :
    α.liftBaseChangeFinOne A =
      ((ofSubsingleton 𝕜 E F (0 : Fin 1)).symm α).toLinearMap.liftBaseChange A :=
  (rfl)

@[simp]
theorem liftBaseChangeFinOne_tmul (α : E [⋀^Fin 1]→L[𝕜] F) (a : A) (v : E) :
    α.liftBaseChangeFinOne A (a ⊗ₜ v) = a • α ![v] := by
  simp [liftBaseChangeFinOne, Matrix.vec_single_eq_const]

/-- The `A`-bilinear extension of a two-form `ω : E [⋀^Fin 2]→L[𝕜] F` with values in an
`A`-module: the extension `LinearMap.BilinMap.liftBaseChange` of `(v, w) ↦ ω ![v, w]`. -/
noncomputable def liftBaseChangeFinTwo (ω : E [⋀^Fin 2]→L[𝕜] F) : BilinMap A (A ⊗[𝕜] E) F :=
  BilinMap.liftBaseChange A <| LinearMap.mk₂ 𝕜 (fun v w ↦ ω ![v, w])
    (fun v₁ v₂ w ↦ ω.toAlternatingMap.map_vecCons_add ![w] v₁ v₂)
    (fun c v w ↦ ω.toAlternatingMap.map_vecCons_smul ![w] c v)
    (fun v w₁ w₂ ↦ (ω.toAlternatingMap.curryLeft v).map_vecCons_add ![] w₁ w₂)
    (fun c v w ↦ (ω.toAlternatingMap.curryLeft v).map_vecCons_smul ![] c w)

@[simp]
theorem liftBaseChangeFinTwo_tmul (ω : E [⋀^Fin 2]→L[𝕜] F) (a b : A) (v w : E) :
    ω.liftBaseChangeFinTwo A (a ⊗ₜ v) (b ⊗ₜ w) = (a * b) • ω ![v, w] := by
  simp only [liftBaseChangeFinTwo, BilinMap.liftBaseChange_tmul]
  -- `LinearMap.mk₂_apply` does not fire here; the bilinear map evaluates by definition.
  rfl

/-- An `A`-bilinear map on `A ⊗[𝕜] E` is the extension of a two-form `ω` exactly when it agrees
with `ω` on the vectors `1 ⊗ v`. -/
theorem eq_liftBaseChangeFinTwo_iff {B : BilinMap A (A ⊗[𝕜] E) F} {ω : E [⋀^Fin 2]→L[𝕜] F} :
    B = ω.liftBaseChangeFinTwo A ↔ ∀ v w, B (1 ⊗ₜ v) (1 ⊗ₜ w) = ω ![v, w] :=
  BilinMap.eq_liftBaseChange_iff

variable {E' : Type*} [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E'] in
/-- If a two-form `ω` and a one-form `α` satisfy `ω(v, w) = c • α(N(v, w))` for an `𝕜`-bilinear
map `N` and a scalar `c : A`, then so do their `A`-linear extensions, with `N` extended
`A`-bilinearly by `LinearMap.BilinMap.baseChange`. -/
theorem liftBaseChangeFinTwo_apply_of_eq_smul {ω : E [⋀^Fin 2]→L[𝕜] F}
    {α : E' [⋀^Fin 1]→L[𝕜] F} {N : BilinMap 𝕜 E E'} {c : A}
    (h : ∀ v w, ω ![v, w] = c • α ![N v w]) (X Y : A ⊗[𝕜] E) :
    ω.liftBaseChangeFinTwo A X Y =
      c • α.liftBaseChangeFinOne A (BilinMap.baseChange A N X Y) := by
  have h' : ω.liftBaseChangeFinTwo A =
      (BilinMap.baseChange A N).compr₂ (c • α.liftBaseChangeFinOne A) :=
    ((eq_liftBaseChangeFinTwo_iff A).2 fun v w ↦ by simp [h]).symm
  simpa using LinearMap.congr_fun₂ h' X Y

/-- The `A`-bilinear extension of a two-form is antisymmetric. -/
theorem liftBaseChangeFinTwo_swap (ω : E [⋀^Fin 2]→L[𝕜] F) (X Y : A ⊗[𝕜] E) :
    ω.liftBaseChangeFinTwo A Y X = -ω.liftBaseChangeFinTwo A X Y := by
  have h : (ω.liftBaseChangeFinTwo A).flip = -ω.liftBaseChangeFinTwo A := by
    ext v w
    simpa using ω.map_swap ![v, w] (i := 0) (j := 1) (by decide)
  simpa using LinearMap.congr_fun₂ h X Y

/-- The `A`-bilinear extension of a two-form is alternating: it vanishes on equal arguments. -/
@[simp]
theorem liftBaseChangeFinTwo_self (ω : E [⋀^Fin 2]→L[𝕜] F) (X : A ⊗[𝕜] E) :
    ω.liftBaseChangeFinTwo A X X = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul a v => simp [ω.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)]
  | add X Y hX hY => simp [hX, hY, liftBaseChangeFinTwo_swap A ω X Y]

end ContinuousAlternatingMap
