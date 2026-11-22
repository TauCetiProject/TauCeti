/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import TauCeti.RingTheory.Ideal.Operations.Pi
import TauCeti.RingTheory.Length

/-!
# Lengths of the quotients `M ⧸ I • N`

For an ideal `I` of a ring `A` and a submodule `N` of an `A`-module `M`, this file records how
the lengths of the quotients `M ⧸ I • N` behave: `M ⧸ I • N` is filtered by `N ⧸ I • N` and
`M ⧸ N`, the length of `M ⧸ I • M` is invariant under linear equivalence, and it is additive over
finite products, since there `I • ⊤` is the product of the `I • ⊤` of the factors
(`Submodule.smul_top_eq_pi`). For `N = I ^ k • ⊤`, the quotient `M ⧸ I • N` is the truncation
`M ⧸ I ^ (k + 1) M` of the `I`-adic filtration, and the first fact computes the length of the
graded piece `I ^ k M ⧸ I ^ (k + 1) M` from the lengths of these truncations. Over the quotient
ring, the base change `(A ⧸ I) ⊗[A] M` has the length of `M ⧸ I • M`; for `M` killed by `I` this is
the length of `M` itself, which over a field `A ⧸ I` is its rank.

## Main results

* `Submodule.comap_subtype_smul`: inside a submodule `N`, the preimage of `I • N` is `I • ⊤`.
* `TauCeti.length_quotient_smul_eq_length_quotient_smul_top_add`: `M ⧸ I • N` is filtered by
  `N ⧸ I • N` and `M ⧸ N`.
* `TauCeti.length_quotient_smul_top_congr`: the length of `M ⧸ I • M` is a linear-equivalence
  invariant.
* `TauCeti.length_pi_quotient_smul_top`: the length of `(∀ i, M i) ⧸ I • ⊤` is the sum of the
  lengths of the `M i ⧸ I • ⊤`.
* `TauCeti.length_quotient_tensor`: the length of `(A ⧸ I) ⊗[A] M` over `A ⧸ I` is the length of
  `M ⧸ I • M` over `A`.
* `TauCeti.rankAtStalk_quotient_tensor_eq_length`: for a maximal ideal `I` and `M` killed by `I`,
  the rank of `(A ⧸ I) ⊗[A] M` over the field `A ⧸ I` is the length of `M` over `A`.
-/

public section

/-- Inside a submodule `N`, the preimage of `I • N` is `I • ⊤`. -/
theorem Submodule.comap_subtype_smul {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (N : Submodule A M) : (I • N).comap N.subtype = I • ⊤ := by
  rw [← Submodule.comap_map_eq_of_injective N.subtype_injective (I • ⊤), Submodule.map_smul'',
    Submodule.map_top, Submodule.range_subtype]

namespace TauCeti

section Ring

variable {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- For an ideal `I` and a submodule `N`, the quotient `M ⧸ I • N` is filtered by `N ⧸ I • N` and
`M ⧸ N`. -/
theorem length_quotient_smul_eq_length_quotient_smul_top_add (I : Ideal A) (N : Submodule A M) :
    Module.length A (M ⧸ I • N) =
      Module.length A (↥N ⧸ I • (⊤ : Submodule A N)) + Module.length A (M ⧸ N) := by
  rw [length_quotient_eq_length_quotient_comap_subtype_add Submodule.smul_le_right,
    Submodule.comap_subtype_smul]

/-- The length of `M ⧸ I • M` is a linear-equivalence invariant. -/
theorem length_quotient_smul_top_congr {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (I : Ideal A) :
    Module.length A (M ⧸ I • (⊤ : Submodule A M)) =
      Module.length A (N ⧸ I • (⊤ : Submodule A N)) := by
  refine (Submodule.Quotient.equiv _ _ e ?_).length_eq
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

end Ring

/-- Over a finite product, the length of the quotient by `I • ⊤` is the sum of the lengths of the
quotients of the factors by `I • ⊤`. -/
theorem length_pi_quotient_smul_top {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (I : Ideal A) :
    Module.length A ((∀ i, M i) ⧸ I • (⊤ : Submodule A (∀ i, M i))) =
      ∑ i, Module.length A (M i ⧸ I • (⊤ : Submodule A (M i))) := by
  classical
  rw [Submodule.smul_top_eq_pi,
    (Submodule.quotientPi fun i ↦ I • (⊤ : Submodule A (M i))).length_eq,
    Module.length_pi_of_fintype]

section Tensor

open scoped TensorProduct

variable {A : Type*} [CommRing A] (I : Ideal A) {M : Type*} [AddCommGroup M] [Module A M]

variable (M) in
/-- The base change `(A ⧸ I) ⊗[A] M` has the same length over `A ⧸ I` as `M ⧸ I • M` over `A`. -/
theorem length_quotient_tensor :
    Module.length (A ⧸ I) ((A ⧸ I) ⊗[A] M) = Module.length A (M ⧸ I • (⊤ : Submodule A M)) := by
  rw [← Module.length_eq_of_surjective (S := A) Ideal.Quotient.mk_surjective,
    (TensorProduct.quotTensorEquivQuotSMul M I).length_eq]

/-- The base change to `A ⧸ I` of a module of finite length is finite over `A ⧸ I`. -/
theorem finite_quotient_tensor_of_length_ne_top (hM : Module.length A M ≠ ⊤) :
    Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] M) := by
  have h : Module.length (A ⧸ I) ((A ⧸ I) ⊗[A] M) ≠ ⊤ := by
    rw [length_quotient_tensor]
    exact ne_top_of_le_ne_top hM (Module.length_le_of_surjective _ (Submodule.mkQ_surjective _))
  have := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).1
  infer_instance

/-- For a maximal ideal `I` and a module `M` killed by `I`, the base change `(A ⧸ I) ⊗[A] M`, a
vector space over the field `A ⧸ I`, has rank the length of `M` over `A` at the unique prime. -/
theorem rankAtStalk_quotient_tensor_eq_length [I.IsMaximal] (hM : I • (⊤ : Submodule A M) = ⊥)
    [Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] M)] (𝔭 : PrimeSpectrum (A ⧸ I)) :
    (Module.rankAtStalk (R := A ⧸ I) ((A ⧸ I) ⊗[A] M) 𝔭 : ℕ∞) = Module.length A M := by
  let := Ideal.Quotient.field I
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id,
    ← Module.length_eq_finrank, length_quotient_tensor, (Submodule.quotEquivOfEqBot _ hM).length_eq]

end Tensor

end TauCeti
