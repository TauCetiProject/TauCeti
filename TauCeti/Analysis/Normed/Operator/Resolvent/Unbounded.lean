/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Module
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent

/-!
# The resolvent set of an unbounded operator

Mathlib's `resolventSet` and `resolvent` are Banach-algebra notions: they ask that
`algebraMap R A r - a` be a *unit* of the algebra, which only makes sense for an element `a`
of that algebra. The infinitesimal generator of a C₀-semigroup is not such an element — it is
an unbounded operator, carried here by `LinearPMap` — so it needs its own resolvent notion.

The continuous-inverse foundation is defined in
`TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent`. This file develops its normed theory
over an arbitrary nontrivially normed field. For `A : X →ₗ.[𝕜] X` and
`lambda : 𝕜` we say that a *bounded* operator
`R : X →L[𝕜] X` is a resolvent of `A` at `lambda` (`LinearPMap.IsResolventAt`)
when `R` takes values in `D(A)` and is a two-sided inverse of `lambda • I - A : D(A) → X`. Such
an `R` is unique when it exists, so the *resolvent set*
`LinearPMap.resolventSet` and the *resolvent*
`LinearPMap.resolvent` are well defined, and the resolvent obeys the usual
identities.

Nothing here mentions semigroups: the theory is stated for an arbitrary `A : X →ₗ.[𝕜] X`, which
is what makes it usable for an operator not yet known to generate anything — the situation of
the Hille--Yosida generation theorem, whose hypotheses read `(ω, ∞) ⊆ resolventSet A` together
with a bound on `‖resolvent A l ^ n‖`.

Two bridges keep this from being a parallel universe.

* **To Mathlib's bounded notion.** A bounded operator `T : X →L[𝕜] X`, read as the everywhere
  defined unbounded operator `(T : X →ₗ[𝕜] X).toPMap ⊤`, has exactly Mathlib's resolvent set
  and resolvent (`ContinuousLinearMap.mem_resolventSet_toPMap_top_iff`,
  `ContinuousLinearMap.resolvent_toPMap_top`), proved here.
* **To the Laplace-transform resolvent.** For a C₀-semigroup `S` with growth bound `(ω, M)`,
  every `lambda > ω` lies in the resolvent set of the generator and the resolvent there *is*
  the Laplace transform `∫₀^∞ e^{-λt} S(t) x dt`
  (`StronglyContinuousSemigroup.generator_resolvent_eq`). That bridge is proved downstream, in
  `TauCeti/Analysis/Semigroups/Resolvent/Identity.lean`, which then derives the semigroup
  resolvent identity from the abstract one below.

## Definitions from the continuous-inverse foundation

* `LinearPMap.IsResolventAt`: `R` inverts `lambda • I - A`.
* `LinearPMap.resolventSet`: the set of `lambda` at which such an `R` exists.
* `LinearPMap.resolvent`: that `R`, chosen by `Classical.choose`.

## Main results

* `LinearPMap.IsResolventAt.unique`: the inverse is unique, so the resolvent
  is well defined.
* `LinearPMap.isResolventAt_iff_forall_mem_graph`: the inverse condition read on the
  graph of `A`.
* `TauCeti.LinearPMap.resolvent_sub_resolvent`: the resolvent identity
  `R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`, and
  `TauCeti.LinearPMap.resolvent_comm`.
* `TauCeti.LinearPMap.mem_resolventSet_of_norm_mul_lt_one` and
  `LinearPMap.isOpen_resolventSet`: the Neumann-series perturbation of a
  resolvent point, and the openness of the resolvent set it gives.
* `TauCeti.LinearPMap.resolvent_eq_mul_inverse_one_sub`: the local Neumann formula for the
  resolvent itself.
* `LinearPMap.eq_of_le_of_mem_resolventSet`: an operator has no proper extension
  sharing a resolvent point.
* `ContinuousLinearMap.mem_resolventSet_toPMap_top_iff` and
  `ContinuousLinearMap.resolvent_toPMap_top`: the bounded bridge.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section IV.1 and
Theorem II.3.5; Pazy, *Semigroups of Linear Operators and Applications to Partial Differential
Equations*, Chapter 1.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace LinearPMap

open _root_.LinearPMap (
  IsResolventAt resolvent_eq_of_isResolventAt resolvent_mem_domain resolvent_smul_sub_apply
  smul_sub_apply_resolvent)

variable {A : X →ₗ.[𝕜] X} {lambda mu : 𝕜} {R : X →L[𝕜] X}

/-! ## The resolvent identity -/

/-- Pointwise form of the **resolvent identity**
`R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`. -/
theorem resolvent_sub_resolvent_apply (hl : lambda ∈ A.resolventSet)
    (hm : mu ∈ A.resolventSet) (y : X) :
    A.resolvent lambda y - A.resolvent mu y
      = (mu - lambda) • A.resolvent lambda (A.resolvent mu y) := by
  have hmem := resolvent_mem_domain hm y
  have hy : mu • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩ = y :=
    smul_sub_apply_resolvent hm y
  have hleft : A.resolvent lambda
      (lambda • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩) = A.resolvent mu y :=
    resolvent_smul_sub_apply hl ⟨A.resolvent mu y, hmem⟩
  have hkey : A.resolvent lambda (mu • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩)
      = A.resolvent mu y + (mu - lambda) • A.resolvent lambda (A.resolvent mu y) := by
    have hsplit : mu • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩
        = (lambda • A.resolvent mu y - A ⟨A.resolvent mu y, hmem⟩)
          + (mu - lambda) • A.resolvent mu y := by module
    rw [hsplit, map_add, map_smul, hleft]
  rw [hy] at hkey
  rw [hkey]
  abel

/-- The **resolvent identity** `R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`, as an
equality of bounded operators. -/
theorem resolvent_sub_resolvent (hl : lambda ∈ A.resolventSet) (hm : mu ∈ A.resolventSet) :
    A.resolvent lambda - A.resolvent mu
      = (mu - lambda) • (A.resolvent lambda ∘L A.resolvent mu) := by
  ext y
  simpa using resolvent_sub_resolvent_apply hl hm y

/-- Resolvents at two points of the resolvent set commute. -/
theorem resolvent_comm (hl : lambda ∈ A.resolventSet) (hm : mu ∈ A.resolventSet) :
    A.resolvent lambda ∘L A.resolvent mu = A.resolvent mu ∘L A.resolvent lambda := by
  rcases eq_or_ne lambda mu with rfl | hne
  · rfl
  · have hsub : (mu - lambda) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 := resolvent_sub_resolvent hl hm
    have h2 := resolvent_sub_resolvent hm hl
    have h3 : (mu - lambda) • (A.resolvent lambda ∘L A.resolvent mu)
        = (mu - lambda) • (A.resolvent mu ∘L A.resolvent lambda) := by
      rw [← h1, ← neg_sub lambda mu, neg_smul, ← h2]
      abel
    have h4 := congrArg (fun T : X →L[𝕜] X => (mu - lambda)⁻¹ • T) h3
    simpa only [smul_smul, inv_mul_cancel₀ hsub, one_smul] using h4

/-! ## Neumann perturbations and openness of the resolvent set -/

/-- **The common invertible perturbation witness.** If `lambda` lies in the resolvent set of `A`
and `I - B R(lambda, A)` is invertible, then
`R(lambda, A) (I - B R(lambda, A))⁻¹` inverts `lambda • I - (B + A)`.

This is the lower-level construction shared by bounded perturbations and perturbations of the
spectral parameter. -/
theorem _root_.ContinuousLinearMap.isResolventAt_vadd_of_isUnit_one_sub_mul_resolvent
    (B : X →L[𝕜] X)
    (h : lambda ∈ A.resolventSet) (hB : IsUnit (1 - B * A.resolvent lambda)) :
    IsResolventAt ((B : X →ₗ[𝕜] X) +ᵥ A) lambda
      (A.resolvent lambda * Ring.inverse (1 - B * A.resolvent lambda)) := by
  set R := A.resolvent lambda with hRdef
  have hunit : IsUnit (1 - B * R) := by simpa only [hRdef] using hB
  rw [ContinuousLinearMap.mul_def]
  set U : X →L[𝕜] X := Ring.inverse (1 - B * R) with hUdef
  have hcancel : ∀ y : X, U y - B (R (U y)) = y := by
    intro y
    have h1 : (1 - B * R) * U = 1 := by
      rw [hUdef, Ring.mul_inverse_cancel _ hunit]
    simpa using congrArg (fun S : X →L[𝕜] X => S y) h1
  have hsolve : ∀ y : X, U (y - B (R y)) = y := by
    intro y
    have h1 : U * (1 - B * R) = 1 := by
      rw [hUdef, Ring.inverse_mul_cancel _ hunit]
    simpa using congrArg (fun S : X →L[𝕜] X => S y) h1
  refine ⟨fun y => resolvent_mem_domain h (U y), fun y => ?_, fun x => ?_⟩
  · have hstep : lambda • (R ∘L U) y -
        ((B : X →ₗ[𝕜] X) +ᵥ A) ⟨(R ∘L U) y, resolvent_mem_domain h (U y)⟩
        = (lambda • R (U y) - A ⟨R (U y), resolvent_mem_domain h (U y)⟩) - B (R (U y)) := by
      rw [LinearPMap.vadd_apply]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      abel
    rw [hstep, smul_sub_apply_resolvent h (U y), hcancel y]
  · have hx : R (lambda • (x : X) - A x) = (x : X) :=
      resolvent_smul_sub_apply h ⟨(x : X), x.2⟩
    have hstep : lambda • (x : X) - ((B : X →ₗ[𝕜] X) +ᵥ A) x
        = (lambda • (x : X) - A x) - B (R (lambda • (x : X) - A x)) := by
      rw [LinearPMap.vadd_apply, hx]
      simp only [ContinuousLinearMap.coe_coe]
      abel
    rw [ContinuousLinearMap.comp_apply, hstep, hsolve, hx]

section CompleteSpace

variable [CompleteSpace X]

/-- If `lambda` lies in the resolvent set of `A` and `‖B R(lambda, A)‖ < 1`, then
`R(lambda, A) (I - B R(lambda, A))⁻¹` inverts `lambda • I - (B + A)`. -/
theorem _root_.ContinuousLinearMap.isResolventAt_vadd_of_norm_mul_resolvent_lt_one
    (B : X →L[𝕜] X)
    (h : lambda ∈ A.resolventSet) (hB : ‖B * A.resolvent lambda‖ < 1) :
    IsResolventAt ((B : X →ₗ[𝕜] X) +ᵥ A) lambda
      (A.resolvent lambda * Ring.inverse (1 - B * A.resolvent lambda)) :=
  ContinuousLinearMap.isResolventAt_vadd_of_isUnit_one_sub_mul_resolvent B h
    (isUnit_one_sub_of_norm_lt_one hB)

private theorem isResolventAt_of_norm_mul_lt_one (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) :
    IsResolventAt A mu
      (A.resolvent lambda * Ring.inverse (1 - (lambda - mu) • A.resolvent lambda)) := by
  let B : X →L[𝕜] X := (lambda - mu) • 1
  have hbound : ‖B‖ * ‖A.resolvent lambda‖ < 1 := by
    have hBnorm : ‖B‖ ≤ ‖lambda - mu‖ := by
      dsimp only [B]
      rw [norm_smul]
      calc ‖lambda - mu‖ * ‖(1 : X →L[𝕜] X)‖
          ≤ ‖lambda - mu‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ = ‖lambda - mu‖ := mul_one _
    exact (mul_le_mul_of_nonneg_right hBnorm (norm_nonneg _)).trans_lt (by rwa [norm_sub_rev])
  have hB : ‖B * A.resolvent lambda‖ < 1 :=
    lt_of_le_of_lt (norm_mul_le _ _) hbound
  have hBR : B * A.resolvent lambda = (lambda - mu) • A.resolvent lambda := by
    simp only [B, smul_mul_assoc, one_mul]
  let U : X →L[𝕜] X :=
    A.resolvent lambda * Ring.inverse (1 - (lambda - mu) • A.resolvent lambda)
  have hpert : IsResolventAt ((B : X →ₗ[𝕜] X) +ᵥ A) lambda U := by
    simpa only [U, hBR] using B.isResolventAt_vadd_of_norm_mul_resolvent_lt_one h hB
  suffices IsResolventAt A mu U by simpa only [U]
  refine ⟨hpert.mem_domain, fun y => ?_, fun x => ?_⟩
  · calc
      mu • _ - A ⟨_, hpert.mem_domain y⟩ =
          lambda • _ - ((B : X →ₗ[𝕜] X) +ᵥ A) ⟨_, hpert.mem_domain y⟩ := by
            rw [LinearPMap.vadd_apply]
            simp only [B, ContinuousLinearMap.coe_coe, one_apply_eq_self, smul_apply]
            module
      _ = y := hpert.smul_sub_apply y
  · calc
      U (mu • (x : X) - A x) =
          U (lambda • (x : X) - ((B : X →ₗ[𝕜] X) +ᵥ A) x) := by
            congr 1
            rw [LinearPMap.vadd_apply]
            simp only [B, ContinuousLinearMap.coe_coe, one_apply_eq_self, smul_apply]
            module
      _ = (x : X) := hpert.apply_smul_sub x

/-- **The Neumann perturbation of a resolvent point.** If `lambda` lies in the resolvent set and
`‖mu - lambda‖ * ‖R(lambda)‖ < 1`, then `mu` lies in it too. -/
theorem mem_resolventSet_of_norm_mul_lt_one (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) : mu ∈ A.resolventSet :=
  (isResolventAt_of_norm_mul_lt_one h hmu).mem_resolventSet

/-- **Local Neumann formula for the resolvent.** Inside the ball
`‖mu - lambda‖ * ‖R(lambda)‖ < 1`, the resolvent at `mu` is obtained by multiplying
`R(lambda)` by the ring inverse of `1 - (lambda - mu) R(lambda)`. -/
theorem resolvent_eq_mul_inverse_one_sub (h : lambda ∈ A.resolventSet)
    (hmu : ‖mu - lambda‖ * ‖A.resolvent lambda‖ < 1) :
    A.resolvent mu = A.resolvent lambda *
      Ring.inverse (1 - (lambda - mu) • A.resolvent lambda) :=
  resolvent_eq_of_isResolventAt (isResolventAt_of_norm_mul_lt_one h hmu)

/-- **The resolvent set is open.** -/
theorem _root_.LinearPMap.isOpen_resolventSet (A : X →ₗ.[𝕜] X) : IsOpen (A.resolventSet) := by
  rw [Metric.isOpen_iff]
  intro lambda h
  refine ⟨1 / (‖A.resolvent lambda‖ + 1), by positivity, fun mu hmu => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hmu
  refine mem_resolventSet_of_norm_mul_lt_one h ?_
  have hlt : ‖mu - lambda‖ * (‖A.resolvent lambda‖ + 1) < 1 :=
    (lt_div_iff₀ (by positivity)).mp (by simpa using hmu)
  calc ‖mu - lambda‖ * ‖A.resolvent lambda‖
      ≤ ‖mu - lambda‖ * (‖A.resolvent lambda‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ < 1 := hlt

end CompleteSpace

/-! ## The bridge to Mathlib's Banach-algebra resolvent

A bounded operator `T : X →L[𝕜] X` becomes an everywhere defined unbounded operator
`(T : X →ₗ[𝕜] X).toPMap ⊤`. Its resolvent set and resolvent in the sense above are Mathlib's
`resolventSet 𝕜 T` and `resolvent T`, computed in the Banach algebra `X →L[𝕜] X`. -/

section Bounded

variable {T : X →L[𝕜] X}

/-- An inverse of `lambda • I - T` in the unbounded sense is a two-sided inverse in the algebra
`X →L[𝕜] X`, so `lambda • I - T` is a unit there. -/
theorem _root_.LinearPMap.IsResolventAt.isUnit_toPMap_top
    (h : IsResolventAt ((T : X →ₗ[𝕜] X).toPMap ⊤) lambda R) :
    IsUnit (algebraMap 𝕜 (X →L[𝕜] X) lambda - T) := by
  have hright : (algebraMap 𝕜 (X →L[𝕜] X) lambda - T) * R = 1 := by
    ext y
    have h1 : lambda • R y - T (R y) = y := h.smul_sub_apply y
    simpa using h1
  have hleft : R * (algebraMap 𝕜 (X →L[𝕜] X) lambda - T) = 1 := by
    ext y
    have h1 : R (lambda • y - T y) = y := h.apply_smul_sub ⟨y, Submodule.mem_top⟩
    simpa using h1
  exact spectrum.mem_resolventSet_of_left_right_inverse hright hleft

/-- A unit `lambda • I - T` of the algebra `X →L[𝕜] X` inverts `lambda • I - T` in the
unbounded sense, with the algebra inverse as the resolvent. -/
theorem _root_.IsUnit.isResolventAt_toPMap_top
    (h : IsUnit (algebraMap 𝕜 (X →L[𝕜] X) lambda - T)) :
    IsResolventAt ((T : X →ₗ[𝕜] X).toPMap ⊤) lambda
      ((h.unit⁻¹ : (X →L[𝕜] X)ˣ) : X →L[𝕜] X) where
  mem_domain _ := Submodule.mem_top
  smul_sub_apply y := by
    have h1 : (algebraMap 𝕜 (X →L[𝕜] X) lambda - T)
        (((h.unit⁻¹ : (X →L[𝕜] X)ˣ) : X →L[𝕜] X) y) = y := by
      rw [← mul_apply_eq_comp, h.mul_val_inv, one_apply_eq_self]
    rwa [sub_apply, ContinuousLinearMap.algebraMap_apply] at h1
  apply_smul_sub x := by
    have h1 : ((h.unit⁻¹ : (X →L[𝕜] X)ˣ) : X →L[𝕜] X)
        ((algebraMap 𝕜 (X →L[𝕜] X) lambda - T) (x : X)) = (x : X) := by
      rw [← mul_apply_eq_comp, h.val_inv_mul, one_apply_eq_self]
    rwa [sub_apply, ContinuousLinearMap.algebraMap_apply] at h1

/-- **The bounded bridge, membership half.** For a bounded operator the unbounded resolvent set
of `T` and Mathlib's Banach-algebra resolvent set agree. -/
@[simp]
theorem _root_.ContinuousLinearMap.mem_resolventSet_toPMap_top_iff
    (T : X →L[𝕜] X) (lambda : 𝕜) :
    lambda ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).resolventSet ↔ lambda ∈ _root_.resolventSet 𝕜 T :=
  (_root_.LinearPMap.mem_resolventSet_iff).trans
    ⟨fun ⟨_, hR⟩ => hR.isUnit_toPMap_top,
      fun h => ⟨_, h.isResolventAt_toPMap_top⟩⟩

/-- **The bounded bridge, value half.** For a bounded operator the unbounded resolvent is
Mathlib's Banach-algebra resolvent. -/
@[simp]
theorem _root_.ContinuousLinearMap.resolvent_toPMap_top
    (T : X →L[𝕜] X) {lambda : 𝕜}
    (h : lambda ∈ _root_.resolventSet 𝕜 T) :
    ((T : X →ₗ[𝕜] X).toPMap ⊤).resolvent lambda = _root_.resolvent T lambda := by
  rw [resolvent_eq_of_isResolventAt (h.isResolventAt_toPMap_top),
    spectrum.resolvent_eq h]

end Bounded

end LinearPMap

end TauCeti

end
