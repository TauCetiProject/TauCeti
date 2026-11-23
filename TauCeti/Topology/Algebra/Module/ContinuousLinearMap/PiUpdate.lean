/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.LinearAlgebra.Pi.Coordinates
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Replacing one coordinate by a continuous linear functional

Over a ring `R` with a topology, replacing the coordinate `i` of `v : ι → R` by the value `α v` of
a continuous linear functional `α` is the continuous linear map
`pi (Function.update (fun m ↦ proj m) i α)`, the derivative computed by
`HasFDerivAt.update_self`. It is a continuous linear equivalence when the coefficient
`c = α (Pi.single i 1)` is a unit and right multiplication by `-c⁻¹` is continuous on `R`.

## Main results

* `ContinuousLinearMap.exists_pi_update_equiv`: over a ring `R` with a topology, replacing one
  coordinate of `ι → R` by a continuous linear functional whose coefficient `c` at that coordinate
  is a unit is a continuous linear equivalence, provided right multiplication by `-c⁻¹` is
  continuous on `R`.

The coordinate replacement is adapted from
[KLS](https://github.com/human-ai-mathematics/kls-lean), commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/CoordinateChange.lean`. Its algebraic part is
Mathlib's `LinearEquiv.dilatransvection`.
-/

public section

namespace ContinuousLinearMap

/-- Replacing one coordinate by a continuous linear functional whose coefficient `c` at that
coordinate is a unit is a continuous linear equivalence, provided right multiplication by `-c⁻¹`
is continuous on `R`. No other continuity on `R` is needed. -/
theorem exists_pi_update_equiv {ι R : Type*} [DecidableEq ι] [Ring R] [TopologicalSpace R]
    (α : (ι → R) →L[R] R) (i : ι) (hα : IsUnit (α (Pi.single i 1)))
    (hcont : Continuous fun x : R ↦ x * -↑hα.unit⁻¹) :
    ∃ e : (ι → R) ≃L[R] (ι → R),
      (e : (ι → R) →L[R] (ι → R)) = pi (Function.update (fun m : ι ↦ proj m) i α) := by
  set f : (ι → R) →L[R] (ι → R) := pi (Function.update (fun m : ι ↦ proj m) i α)
  have hf (v : ι → R) : f v = Function.update v i (α v) := by
    ext j
    simp [f]
  -- The update is the dilatransvection `v ↦ v + (α v - v i) • Pi.single i 1`, whose
  -- dilation factor `1 + (α - proj i) (Pi.single i 1)` is the coefficient of `α`.
  have h : IsUnit (1 + ((α : (ι → R) →ₗ[R] R) - LinearMap.proj i : Module.Dual R (ι → R))
      (Pi.single i 1)) := by
    simpa using hα
  set e := LinearEquiv.dilatransvection h
  have he (v : ι → R) : e v = f v := by
    rw [hf, LinearEquiv.dilatransvection.apply, Pi.update_eq_sub_add_single]
    simp [Pi.single_sub, ← Pi.single_smul']
    abel
  -- With `d` the inverse of the coefficient, setting the coordinate `i` of `u` to `s * -d`
  -- lowers the value of `α` at `u` with that coordinate zeroed by `s`.
  set d : R := ↑hα.unit⁻¹
  have hd : d * α (Pi.single i 1) = 1 := hα.val_inv_mul
  have hupd (u : ι → R) (s : R) :
      α (Function.update u i (s * -d)) = α (Function.update u i 0) - s := by
    simpa [mul_assoc, hd, sub_eq_add_neg] using
      (α : (ι → R) →ₗ[R] R).apply_update_eq_add_smul u i (s * -d)
  -- Hence the inverse sets the coordinate `i` of `u` to `α (update u i (u i * -d)) * -d`. It is
  -- built from `α`, coordinate updates and right multiplication by `-d` only, so it is visibly
  -- continuous.
  have hinv : Continuous fun u : ι → R ↦
      Function.update u i (α (Function.update u i (u i * -d)) * -d) :=
    continuous_id.update i <| hcont.comp <| α.continuous.comp <|
      continuous_id.update i <| hcont.comp (continuous_apply i)
  refine ⟨⟨e, f.continuous.congr fun v ↦ (he v).symm, hinv.congr fun u ↦ ?_⟩, ?_⟩
  · refine (e.symm_apply_eq.2 ?_).symm
    rw [he, hf, Function.update_idem, Function.eq_update_iff]
    refine ⟨?_, fun m _ ↦ rfl⟩
    calc u i = α (Function.update u i 0) - (α (Function.update u i 0) - u i) :=
          (sub_sub_cancel _ _).symm
      _ = α (Function.update u i 0) - α (Function.update u i (u i * -d)) := by rw [hupd]
      _ = α (Function.update u i (α (Function.update u i (u i * -d)) * -d)) := (hupd _ _).symm
  · ext v : 1
    simpa only [ContinuousLinearEquiv.coe_apply, ContinuousLinearEquiv.coe_mk] using he v

end ContinuousLinearMap
