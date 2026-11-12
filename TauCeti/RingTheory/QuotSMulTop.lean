/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Reducing modules and linear maps modulo an ideal

An `R`-linear map `f : M → N` carries `I • M` into `I • N` for every ideal `I` of a commutative ring
`R`, so it induces an `R ⧸ I`-linear map `M ⧸ I • M → N ⧸ I • N`. This is Mathlib's
`QuotSMulTop.map`, which treats the principal case `M ⧸ x • M` as an `R`-linear map, made linear
over the quotient ring and extended to an arbitrary ideal.

Reduction modulo `I` is right exact. When `I = (x)` and `x` is regular on the last term, it also
preserves injectivity on the left, so it carries a short exact sequence `0 → K → P → M → 0` to a
short exact sequence `0 → K ⧸ x K → P ⧸ x P → M ⧸ x M → 0`.

Mathlib makes `QuotSMulTop x M = M ⧸ x M` a module over `R ⧸ (x)`; this action is induced by the
`R`-action on `M`, the analogue for `x • ⊤` of Mathlib's `Module.Quotient.mk_smul_mk` for `I • ⊤`.

Reductions of cyclic modules commute: `(R ⧸ (s)) ⧸ r (R ⧸ (s))` and `(R ⧸ (r)) ⧸ s (R ⧸ (r))` are
both `R ⧸ (r, s)`. For an `R`-algebra `A` and an `A`-module `N`, reducing modulo the image of
`r : R` in `A` is reducing the underlying `R`-module modulo `r`. A finite free `R`-module of rank
`d` reduces modulo `r` to `(R ⧸ (r)) ^ d`, so it has `#(R ⧸ (r)) ^ d` elements. Finally, in a
domain, an element `r` not divisible by a prime `π` is regular on `R ⧸ (π ^ m)`.

## Main definitions

* `Ideal.mapQSMulTop`: the `R ⧸ I`-linear map `M ⧸ I • M → N ⧸ I • N` induced by `f : M →ₗ[R] N`.
* `QuotSMulTop.quotSpanSingletonComm`: `(R ⧸ (s)) ⧸ r (R ⧸ (s)) ≃ (R ⧸ (r)) ⧸ s (R ⧸ (r))`.
* `QuotSMulTop.restrictScalarsEquiv`: `N ⧸ (algebraMap R A r) N ≃ N ⧸ r N` as `R`-modules.

## Main results

* `QuotSMulTop.mk_smul_mk`: `[r] • [m] = [r • m]` in `M ⧸ x M`.
* `Ideal.mapQSMulTop_id` and `Ideal.mapQSMulTop_comp`: reduction modulo `I` is functorial.
* `Ideal.mapQSMulTop_surjective` and `Ideal.mapQSMulTop_exact`: reduction modulo `I` preserves
  surjectivity and exactness at the middle of `M → N → P → 0`.
* `QuotSMulTop.map_comp_quotEquivOfEq`: for `I = (x)`, the reduction is `QuotSMulTop.map x f`, up
  to the identification of `(x) • ⊤` with `x • ⊤`.
* `Ideal.mapQSMulTop_span_singleton_injective`: reduction modulo `(x)` preserves injectivity of the
  first map of a short exact sequence whose last term is `x`-regular.
* `QuotSMulTop.ker_mapQ_mkQ` and `QuotSMulTop.mapQ_mkQ_surjective`: for an ideal `I` and `y : R`,
  the map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)` is surjective with kernel `y (N ⧸ I N)`, so that
  quotienting by `I` and by `y` may be done in either order.
* `QuotSMulTop.natCard_eq_pow_finrank`: a finite free `R`-module `M` has
  `#(M ⧸ r M) = #(R ⧸ (r)) ^ finrank R M`.
* `Prime.isSMulRegular_quotient_span_pow`: in a domain, if the prime `π` does not divide `r`, then
  `r` is regular on `R ⧸ (π ^ m)`.
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

/-- The `R ⧸ (x)`-action on `M ⧸ x M` is induced by the `R`-action on `M`. -/
@[simp]
theorem mk_smul_mk {x : R} (r : R) (m : M) :
    Ideal.Quotient.mk (Ideal.span {x}) r • (Submodule.Quotient.mk m : QuotSMulTop x M) =
      Submodule.Quotient.mk (r • m) :=
  rfl

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

namespace QuotSMulTop

variable {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N]

/-- For an ideal `I` of `S`, the map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)` has kernel
`y (N ⧸ I N)`: both are `N ⧸ (I N + y N)`. -/
theorem ker_mapQ_mkQ (I : Ideal S) (y : S) :
    LinearMap.ker (Submodule.mapQ (I • ⊤ : Submodule S N) _ (y • ⊤ : Submodule S N).mkQ
      (Submodule.smul_top_le_comap_smul_top I _)) =
      (y • ⊤ : Submodule S (N ⧸ (I • ⊤ : Submodule S N))) := by
  rw [Submodule.ker_mapQ, Submodule.comap_smul_top_of_surjective _ _ (Submodule.mkQ_surjective _),
    Submodule.ker_mkQ, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq,
    Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]

/-- The map `N ⧸ I N → (N ⧸ y N) ⧸ I (N ⧸ y N)` is surjective. -/
theorem mapQ_mkQ_surjective (I : Ideal S) (y : S) :
    Surjective (Submodule.mapQ (I • ⊤ : Submodule S N) _ (y • ⊤ : Submodule S N).mkQ
      (Submodule.smul_top_le_comap_smul_top I _)) := by
  intro q
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Submodule.Quotient.mk n, rfl⟩

end QuotSMulTop

namespace QuotSMulTop

variable {R : Type*} [CommRing R]

/-- Reducing `R ⧸ (s)` modulo `r` is reducing `R ⧸ (r)` modulo `s`: both are `R ⧸ (r, s)`. -/
noncomputable def quotSpanSingletonComm (r s : R) :
    QuotSMulTop r (R ⧸ Ideal.span {s}) ≃ₗ[R] QuotSMulTop s (R ⧸ Ideal.span {r}) :=
  equivQuotTensor r _ ≪≫ₗ TensorProduct.comm R _ _ ≪≫ₗ (equivQuotTensor s _).symm

/-- `quotSpanSingletonComm` sends the class of `x` to the class of `x`. -/
@[simp]
theorem quotSpanSingletonComm_mk_mk (r s x : R) :
    quotSpanSingletonComm r s (Submodule.Quotient.mk (Ideal.Quotient.mk _ x)) =
      Submodule.Quotient.mk (Ideal.Quotient.mk _ x) := by
  simp [quotSpanSingletonComm, equivQuotTensor, LinearEquiv.symm_apply_eq, Algebra.smul_def]

variable {A N : Type*} [CommRing A] [Algebra R A] [AddCommGroup N] [Module A N] [Module R N]
  [IsScalarTower R A N]

/-- Reducing an `A`-module `N` modulo the image of `r : R` in `A` is reducing the underlying
`R`-module modulo `r`. -/
noncomputable def restrictScalarsEquiv (r : R) :
    QuotSMulTop (algebraMap R A r) N ≃ₗ[R] QuotSMulTop r N :=
  (Submodule.Quotient.restrictScalarsEquiv R _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _
      (by rw [element_smul_restrictScalars, Submodule.restrictScalars_top])

/-- `restrictScalarsEquiv` sends the class of `x` to the class of `x`. -/
@[simp]
theorem restrictScalarsEquiv_mk (r : R) (x : N) :
    restrictScalarsEquiv (A := A) r (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  simp [restrictScalarsEquiv]

/-- **The reduction of a finite free module.** A finite free `R`-module `M` reduces modulo `r` to
`(R ⧸ (r)) ^ finrank R M`, so `M ⧸ r M` has `#(R ⧸ (r)) ^ finrank R M` elements. -/
theorem natCard_eq_pow_finrank (r : R) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] :
    Nat.card (QuotSMulTop r M) = Nat.card (R ⧸ Ideal.span {r}) ^ Module.finrank R M := by
  nontriviality R
  let b := Module.Free.chooseBasis R M
  let e := QuotSMulTop.congr r b.equivFun ≪≫ₗ equivQuotTensor r _ ≪≫ₗ
    TensorProduct.piScalarRight R R (R ⧸ Ideal.span {r}) _
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Module.finrank_eq_card_chooseBasisIndex,
    Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex R M)]

end QuotSMulTop

/-- In a domain, if the prime `π` does not divide `r`, then `r` is regular on `R ⧸ (π ^ m)`:
`π ^ m ∣ r x` forces `π ^ m ∣ x`. -/
theorem Prime.isSMulRegular_quotient_span_pow {R : Type*} [CommRing R] [IsDomain R] {π r : R}
    (hπ : Prime π) (hr : ¬π ∣ r) (m : ℕ) : IsSMulRegular (R ⧸ Ideal.span {π ^ m}) r :=
  (isSMulRegular_quotient_iff_mem_of_smul_mem _ r).2 fun x hx ↦ by
    rw [smul_eq_mul, Ideal.mem_span_singleton] at hx
    exact Ideal.mem_span_singleton.2 (hπ.pow_dvd_of_dvd_mul_left m hr hx)
