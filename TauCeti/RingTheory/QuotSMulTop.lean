/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Reducing linear maps modulo an ideal

An `R`-linear map `f : M → N` carries `I • M` into `I • N` for every ideal `I` of a commutative ring
`R`, so it induces an `R ⧸ I`-linear map `M ⧸ I • M → N ⧸ I • N`. This is Mathlib's
`QuotSMulTop.map`, which treats the principal case `M ⧸ x • M` as an `R`-linear map, made linear
over the quotient ring and extended to an arbitrary ideal.

Reduction modulo `I` is right exact. When `I = (x)` and `x` is regular on the last term, it also
preserves injectivity on the left, so it carries a short exact sequence `0 → K → P → M → 0` to a
short exact sequence `0 → K ⧸ x K → P ⧸ x P → M ⧸ x M → 0`.

## Main definitions

* `Ideal.mapQSMulTop`: the `R ⧸ I`-linear map `M ⧸ I • M → N ⧸ I • N` induced by `f : M →ₗ[R] N`.

## Main results

* `Ideal.mapQSMulTop_id` and `Ideal.mapQSMulTop_comp`: reduction modulo `I` is functorial.
* `Ideal.mapQSMulTop_surjective` and `Ideal.mapQSMulTop_exact`: reduction modulo `I` preserves
  surjectivity and exactness at the middle of `M → N → P → 0`.
* `QuotSMulTop.map_comp_quotEquivOfEq`: for `I = (x)`, the reduction is `QuotSMulTop.map x f`, up
  to the identification of `(x) • ⊤` with `x • ⊤`.
* `Ideal.mapQSMulTop_span_singleton_injective`: reduction modulo `(x)` preserves injectivity of the
  first map of a short exact sequence whose last term is `x`-regular.
-/

public section

open Function Pointwise

namespace Ideal

variable {R : Type*} [CommRing R] {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The `R ⧸ I`-linear map `M ⧸ I • M → N ⧸ I • N` induced by an `R`-linear map `M → N`. -/
noncomputable def mapQSMulTop (I : Ideal R) (f : M →ₗ[R] N) :
    M ⧸ I • (⊤ : Submodule R M) →ₗ[R ⧸ I] N ⧸ I • (⊤ : Submodule R N) :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f))

@[simp]
theorem mapQSMulTop_mk (I : Ideal R) (f : M →ₗ[R] N) (m : M) :
    I.mapQSMulTop f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) :=
  (rfl)

@[simp]
theorem mapQSMulTop_id (I : Ideal R) :
    I.mapQSMulTop (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  LinearMap.ext fun m ↦ Submodule.Quotient.induction_on _ m fun _ ↦ rfl

@[simp]
theorem mapQSMulTop_comp (I : Ideal R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    I.mapQSMulTop (g ∘ₗ f) = I.mapQSMulTop g ∘ₗ I.mapQSMulTop f :=
  LinearMap.ext fun m ↦ Submodule.Quotient.induction_on _ m fun _ ↦ rfl

/-- Reduction modulo an ideal preserves surjectivity. -/
theorem mapQSMulTop_surjective (I : Ideal R) {g : N →ₗ[R] P} (hg : Surjective g) :
    Surjective (I.mapQSMulTop g) := by
  intro p
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ p
  obtain ⟨n, rfl⟩ := hg p
  exact ⟨Submodule.Quotient.mk n, rfl⟩

/-- Reduction modulo an ideal is right exact: it carries an exact sequence `M → N → P → 0` to an
exact sequence `M ⧸ I • M → N ⧸ I • N → P ⧸ I • P → 0`. -/
theorem mapQSMulTop_exact (I : Ideal R) {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hfg : Exact f g)
    (hg : Surjective g) : Exact (I.mapQSMulTop f) (I.mapQSMulTop g) :=
  (hfg.exact_mapQ_iff (Submodule.smul_top_le_comap_smul_top I f)
    (Submodule.smul_top_le_comap_smul_top I g)).mpr (by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
      exact inf_le_right)

end Ideal

namespace QuotSMulTop

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- `Ideal.mapQSMulTop (x) f` is Mathlib's `QuotSMulTop.map x f`, up to the identification of
`(x) • ⊤` with `x • ⊤`. -/
theorem map_comp_quotEquivOfEq (x : R) (f : M →ₗ[R] N) :
    QuotSMulTop.map x f ∘ₗ
        (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤)).toLinearMap =
      (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤)).toLinearMap ∘ₗ
        ((Ideal.span {x}).mapQSMulTop f).restrictScalars R :=
  Submodule.linearMap_qext _ rfl

end QuotSMulTop

namespace Ideal

variable {R : Type*} [CommRing R] {K N M : Type*} [AddCommGroup K] [Module R K]
  [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]

/-- Reducing a short exact sequence `0 → K → N → M → 0` modulo an element `x` that is regular on
`M` keeps the first map injective: `K ⧸ x K → N ⧸ x N` is injective. -/
theorem mapQSMulTop_span_singleton_injective {x : R} {f : K →ₗ[R] N} {g : N →ₗ[R] M}
    (hfg : Exact f g) (hf : Injective f) (hM : IsSMulRegular M x) :
    Injective ((span {x}).mapQSMulTop f) := by
  -- Mathlib's four-term lemma, applied to `0 → K → N → M`.
  have := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    ((LinearMap.exact_zero_iff_injective PUnit.{1} f).mpr hf) hfg hM
  rw [map_zero, LinearMap.exact_zero_iff_injective] at this
  have h := congrArg DFunLike.coe (QuotSMulTop.map_comp_quotEquivOfEq x f)
  rw [LinearMap.coe_comp, LinearMap.coe_comp] at h
  exact (h ▸ this.comp (LinearEquiv.injective _)).of_comp

end Ideal
