/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Iterated quotients by a scalar and an ideal

For an `S`-module `N`, an ideal `I` of `S` and `y ∈ S`, the quotient map `N → N ⧸ y N` induces a
map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)`. Both sides are quotients of `N ⧸ (I N + y N)`; this file
records that the map is surjective with kernel `y (N ⧸ I N)`, so that quotienting by `I` and by
`y` may be done in either order.

## Main results

* `QuotSMulTop.ker_mapQ_mkQ`: the map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)` has kernel
  `y (N ⧸ I N)`.
* `QuotSMulTop.mapQ_mkQ_surjective`: the same map is surjective.
-/

public section

open LinearMap
open scoped Pointwise

namespace QuotSMulTop

variable {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N]

/-- For an ideal `I` of `S`, the map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)` has kernel
`y (N ⧸ I N)`: both are `N ⧸ (I N + y N)`. -/
theorem ker_mapQ_mkQ (I : Ideal S) (y : S) :
    ker (Submodule.mapQ (I • ⊤ : Submodule S N) _ (y • ⊤ : Submodule S N).mkQ
      (Submodule.smul_top_le_comap_smul_top I _)) =
      (y • ⊤ : Submodule S (N ⧸ (I • ⊤ : Submodule S N))) := by
  ext p
  rw [mem_ker]
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  have hleft : Submodule.Quotient.mk (Submodule.Quotient.mk n : QuotSMulTop y N) =
      (0 : QuotSMulTop y N ⧸ (I • ⊤ : Submodule S (QuotSMulTop y N))) ↔
      n ∈ (I • ⊤ : Submodule S N) ⊔ (y • ⊤ : Submodule S N) := by
    rw [Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← Submodule.mem_comap,
      Submodule.comap_smul_top_of_surjective _ _ (Submodule.mkQ_surjective _), Submodule.ker_mkQ]
  rw [Submodule.mapQ_apply, Submodule.mkQ_apply, hleft, ← Submodule.ideal_span_singleton_smul,
    ← Submodule.ideal_span_singleton_smul, ← Submodule.mkQ_apply, ← Submodule.mem_comap,
    Submodule.comap_smul_top_of_surjective _ _ (Submodule.mkQ_surjective _), Submodule.ker_mkQ,
    sup_comm]

/-- The map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)` is surjective. -/
theorem mapQ_mkQ_surjective (I : Ideal S) (y : S) :
    Function.Surjective (Submodule.mapQ (I • ⊤ : Submodule S N) _ (y • ⊤ : Submodule S N).mkQ
      (Submodule.smul_top_le_comap_smul_top I _)) := by
  intro q
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Submodule.Quotient.mk n, rfl⟩

end QuotSMulTop
