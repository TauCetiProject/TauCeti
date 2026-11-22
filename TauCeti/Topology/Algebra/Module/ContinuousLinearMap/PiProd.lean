/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.LinearAlgebra.Pi

/-!
# Continuous linear maps on products and Pi types

This file collects supplementary results about continuous linear maps on indexed products `ι → R`.

## Main results

* `ContinuousLinearMap.eq_smul_id_of_unique`: every continuous linear endomorphism of a
  one-coordinate space `ι → R` over a topological commutative semiring `R` with continuous scalar
  multiplication is a scalar multiple of the identity.
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

section CommSemiring

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- Every continuous linear endomorphism of a one-coordinate space `ι → R` is a scalar multiple of
the identity. -/
theorem eq_smul_id_of_unique {ι : Type*} [Unique ι] [ContinuousConstSMul R R]
    (T : (ι → R) →L[R] (ι → R)) :
    T = T (fun _ ↦ 1) default • ContinuousLinearMap.id R (ι → R) := by
  ext v i
  have hv : v = v default • (fun _ : ι ↦ (1 : R)) := by
    ext j
    simp [Unique.eq_default j]
  conv_lhs => rw [hv]
  simp [Unique.eq_default i, mul_comm]

end CommSemiring

/-- Replacing one coordinate by a functional whose coefficient `c` at that coordinate is a unit
is a continuous linear equivalence, provided right multiplication by `-c⁻¹` is continuous on `R`.
No other continuity on `R` is needed. -/
theorem exists_pi_update_equiv {ι R : Type*} [DecidableEq ι] [Ring R] [TopologicalSpace R]
    (α : (ι → R) →L[R] R) (i : ι) (hα : IsUnit (α (Pi.single i 1)))
    (hcont : Continuous fun x : R ↦ x * -↑hα.unit⁻¹) :
    ∃ e : (ι → R) ≃L[R] (ι → R),
      (e : (ι → R) →L[R] (ι → R)) = pi fun m : ι ↦ if m = i then α else proj m := by
  set f : (ι → R) →L[R] (ι → R) := pi fun m : ι ↦ if m = i then α else proj m
  have hf (v : ι → R) : f v = Function.update v i (α v) :=
    Function.eq_update_iff.2 ⟨by simp [f, pi_apply], fun m hm ↦ by simp [f, pi_apply, hm]⟩
  -- The update is the dilatransvection `v ↦ v + (α v - v i) • Pi.single i 1`, whose
  -- dilation factor `1 + (α - proj i) (Pi.single i 1)` is the coefficient of `α`.
  have h : IsUnit (1 + ((α : (ι → R) →ₗ[R] R) - LinearMap.proj i : Module.Dual R (ι → R))
      (Pi.single i 1)) := by
    simpa using hα
  set e := LinearEquiv.dilatransvection h
  have he (v : ι → R) : e v = f v := by
    rw [hf, Pi.update_eq_sub_add_single, LinearEquiv.dilatransvection.apply, ← Pi.single_smul',
      smul_eq_mul, mul_one]
    simp only [LinearMap.sub_apply, coe_coe, LinearMap.proj_apply, Pi.single_sub]
    abel
  -- With `d` the inverse of the coefficient, setting the coordinate `i` of `u` to `s * -d`
  -- lowers the value of `α` at `u` with that coordinate zeroed by `s`.
  set d : R := ↑hα.unit⁻¹
  have hd : d * α (Pi.single i 1) = 1 := hα.val_inv_mul
  have hupd (u : ι → R) (s : R) :
      α (Function.update u i (s * -d)) = α (Function.update u i 0) - s := by
    rw [← coe_coe, LinearMap.apply_update_eq_add_smul, coe_coe, smul_eq_mul, mul_assoc, neg_mul,
      hd, mul_neg_one, sub_eq_add_neg]
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
