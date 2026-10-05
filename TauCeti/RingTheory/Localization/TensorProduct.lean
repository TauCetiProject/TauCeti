/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Linear maps over a localization tensored with an algebra

Let `K` be a localization of `R` and let `A` be an `R`-algebra. Mathlib's
`IsLocalization.linearMap_compatibleSMul` says that an `R`-linear map between `K`-modules is
automatically `K`-linear. This file records the analogue for the ring `K ⊗[R] A`: on modules where
`q ⊗ₜ a` acts as `q • a • _`, every `A`-linear map is `K ⊗[R] A`-linear.

## Main results

* `TauCeti.IsLocalization.linearMap_compatibleSMul_tensorProduct`: `A`-linear maps between such
  modules commute with the action of `K ⊗[R] A`.
-/

public section

namespace TauCeti.IsLocalization

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] (S : Submonoid R) (K : Type*) [CommSemiring K]
  [Algebra R K] [IsLocalization S K] {A : Type*} [Semiring A] [Algebra R A]

include S in
/-- Let `K` be a localization of `R` and `A` an `R`-algebra. Between modules on which
`q ⊗ₜ a ∈ K ⊗[R] A` acts as `q • a • _`, an `A`-linear map is `K ⊗[R] A`-linear: it is `K`-linear
because `K` is a localization of `R` (`IsLocalization.linearMap_compatibleSMul`). -/
theorem linearMap_compatibleSMul_tensorProduct {V W : Type*} [AddCommMonoid V] [Module R V]
    [Module K V] [Module A V] [Module (K ⊗[R] A) V] [IsScalarTower R K V] [IsScalarTower R A V]
    [AddCommMonoid W] [Module R W] [Module K W] [Module A W] [Module (K ⊗[R] A) W]
    [IsScalarTower R K W] [IsScalarTower R A W]
    (hV : ∀ (q : K) (a : A) (v : V), (q ⊗ₜ[R] a) • v = q • a • v)
    (hW : ∀ (q : K) (a : A) (w : W), (q ⊗ₜ[R] a) • w = q • a • w) :
    LinearMap.CompatibleSMul V W (K ⊗[R] A) A where
  map_smul f b v := by
    have := _root_.IsLocalization.linearMap_compatibleSMul S K V W
    induction b using TensorProduct.inductionOn with
    | tmul q a =>
      rw [hV, hW, ← f.map_smul]
      exact (f.restrictScalars R).map_smul_of_tower q (a • v)
    | add b c hb hc => rw [add_smul, map_add, hb, hc, add_smul]

end TauCeti.IsLocalization
