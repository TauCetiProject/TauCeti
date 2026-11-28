/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Data.ENat.BigOperators
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Finiteness.Ideal
import TauCeti.LinearAlgebra.Quotient.Basic
import TauCeti.RingTheory.Ideal.Operations
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

* `TauCeti.length_quotient_smul_eq_length_quotient_smul_top_add`: `M ⧸ I • N` is filtered by
  `N ⧸ I • N` and `M ⧸ N`.
* `TauCeti.length_quotient_smul_top_congr`: the length of `M ⧸ I • M` is a linear-equivalence
  invariant.
* `TauCeti.length_quotient_pi`: the length of `(∀ i, M i) ⧸ ∏ i, p i` is the sum of the lengths
  of the `M i ⧸ p i`.
* `TauCeti.length_pi_quotient_smul_top`: the length of `(∀ i, M i) ⧸ I • ⊤` is the sum of the
  lengths of the `M i ⧸ I • ⊤`.
* `Ideal.length_quotient_pow_succ_smul_top`: the length of the next adic truncation is the sum of
  the current truncation length and the graded-piece length.
* `Ideal.isFiniteLength_smul_top_quotient_smul_top` and
  `Ideal.isFiniteLength_quotient_pow_smul_top`: finite colength of `IM` implies finite length of
  `(JM)/I(JM)` for finitely generated `J`, and finite colength of all powers of finitely generated
  `I`.
* `TauCeti.length_quotient_tensor`: the length of `(A ⧸ I) ⊗[A] M` over `A ⧸ I` is the length of
  `M ⧸ I • M` over `A`.
* `TauCeti.rankAtStalk_quotient_tensor_eq_length`: for a maximal ideal `I` and `M` killed by `I`,
  the rank of `(A ⧸ I) ⊗[A] M` over the field `A ⧸ I` is the length of `M` over `A`.
-/

public section

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

/-- Over a finite product, the length of the quotient by a product of submodules is the sum of the
lengths of the quotients of the factors. -/
theorem length_quotient_pi {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (p : ∀ i, Submodule A (M i)) :
    Module.length A ((∀ i, M i) ⧸ Submodule.pi Set.univ p) = ∑ i, Module.length A (M i ⧸ p i) := by
  classical
  rw [(Submodule.quotientPi p).length_eq, Module.length_pi_of_fintype]

/-- Over a finite product, the length of the quotient by `I • ⊤` is the sum of the lengths of the
quotients of the factors by `I • ⊤`. -/
theorem length_pi_quotient_smul_top {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (I : Ideal A) :
    Module.length A ((∀ i, M i) ⧸ I • (⊤ : Submodule A (∀ i, M i))) =
      ∑ i, Module.length A (M i ⧸ I • (⊤ : Submodule A (M i))) := by
  classical
  rw [Submodule.smul_top_eq_pi, length_quotient_pi]

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

namespace Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `M / IM` has finite length and `J` is finitely generated, then `JM / I(JM)` has finite
length. In particular this applies to `J = I ^ n` when `I` is finitely generated. -/
theorem isFiniteLength_smul_top_quotient_smul_top (I : Ideal R) {J : Ideal R} (hJ : J.FG)
    (hM : IsFiniteLength R (M ⧸ (I • (⊤ : Submodule R M)))) :
    IsFiniteLength R (↥(J • (⊤ : Submodule R M)) ⧸
      (I • ⊤ : Submodule R ↥(J • (⊤ : Submodule R M)))) := by
  classical
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hJ
  let := hs.fintype
  let f : (s →₀ M) →ₗ[R] M := Finsupp.lsum (S := R) fun i : s ↦ i.val • LinearMap.id
  have hrange : LinearMap.range f = J • (⊤ : Submodule R M) := by
    rw [← hspan, Submodule.span_smul_eq]
    exact (Submodule.smul_top_eq_range_lsum s).symm
  have hfin : IsFiniteLength R ((s →₀ M) ⧸ (I • ⊤ : Submodule R (s →₀ M))) := by
    rw [← Module.length_ne_top_iff,
      TauCeti.length_quotient_smul_top_congr (Finsupp.linearEquivFunOnFinite R M s),
      TauCeti.length_pi_quotient_smul_top]
    exact ENat.sum_ne_top.mpr fun _ _ ↦ Module.length_ne_top_iff.mpr hM
  let g := f.codRestrict (J • (⊤ : Submodule R M))
    (fun x ↦ hrange ▸ LinearMap.mem_range_self f x)
  have hf : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    dsimp only [g]
    rw [LinearMap.range_codRestrict, hrange, Submodule.comap_subtype_self]
  exact hfin.of_surjective (Submodule.mapQ_surjective _ _ g
    (Submodule.smul_top_le_comap_smul_top I g) hf)

/-- The length of `M / I ^ (n + 1) M` is the length of the degree-`n` adic graded piece plus
that of `M / I ^ n M`, also when these lengths are infinite. -/
theorem length_quotient_pow_succ_smul_top (I : Ideal R) (n : ℕ) :
    Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) =
      Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
        (I • ⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M)))) +
      Module.length R (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  rw [pow_succ', Submodule.mul_smul, TauCeti.length_quotient_smul_eq_length_quotient_smul_top_add]

/-- If `I` is finitely generated and `M / IM` has finite length, then `M / I ^ n M` has finite
length for every `n`. No finiteness assumption on `M` or on the ring is required. -/
theorem isFiniteLength_quotient_pow_smul_top (I : Ideal R) (hI : I.FG)
    (hM : IsFiniteLength R (M ⧸ (I • (⊤ : Submodule R M)))) (n : ℕ) :
    IsFiniteLength R (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
  induction n with
  | zero =>
    rw [pow_zero, one_smul]
    exact Module.length_ne_top_iff.mp (by simp)
  | succ n ih =>
    rw [← Module.length_ne_top_iff, I.length_quotient_pow_succ_smul_top]
    exact (ENat.add_lt_top.mpr
      ⟨(Module.length_ne_top_iff.mpr
          (I.isFiniteLength_smul_top_quotient_smul_top hI.pow hM)).lt_top,
        (Module.length_ne_top_iff.mpr ih).lt_top⟩).ne

end Ideal
