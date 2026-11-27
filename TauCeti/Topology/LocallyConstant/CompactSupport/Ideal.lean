/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.Pure
public import TauCeti.Topology.LocallyConstant.CharFn
public import TauCeti.Topology.LocallyConstant.CompactSupport

/-!
# The ideal of compactly supported locally constant functions

For a topological space `X` and a semiring `R`, the locally constant functions `X → R` with compact
support form an ideal `C_c(X, R)` of the ring `C(X, R) = LocallyConstant X R`
(`LocallyConstant.compactlySupportedIdeal`): the product of any locally constant function with a
compactly supported one is compactly supported. Over a commutative semiring `R`, its underlying
`R`-module is the module `C_c^∞(X, R)` of test functions
(`LocallyConstant.restrictScalars_compactlySupportedIdeal`).

Every `f ∈ C_c(X, R)` is fixed by the characteristic function of its support, which is a compact
clopen set, so this characteristic function lies in `C_c(X, R)` as well
(`LocallyConstant.charFn_support_mul`). By the elementwise criterion for pure ideals
(`Ideal.pure_iff_forall_exists_eq_mul`), the ideal `C_c(X, R)` of a commutative ring `R` is pure:
`C(X, R) ⧸ C_c(X, R)` is flat over `C(X, R)`. Equivalently, `C_c(X, R) ⊗ M → M` is injective for
every `C(X, R)`-module `M`. This is what makes `C_c(X, R) ⊗ M` the smooth part of `M` when `X` is a
locally profinite set.

## Main definitions

* `LocallyConstant.compactlySupportedIdeal X R`: the ideal `C_c(X, R)` of `C(X, R)`.
* `LocallyConstant.compactlySupported.mulLeft φ`: multiplication by a locally constant function `φ`,
  as an `R`-linear endomorphism of `C_c^∞(X, R)`.

## Main results

* `LocallyConstant.charFn_support_mul`: a locally constant function is fixed by multiplication with
  the characteristic function of its support.
* `LocallyConstant.exists_charFn_mul_eq_of_mem_compactlySupportedIdeal`: in a Hausdorff space,
  every `f ∈ C_c(X, R)` is fixed by `1_U` for some compact open set `U`.
* `LocallyConstant.instPureCompactlySupportedIdeal`: the ideal `C_c(X, R)` is pure.

## References

* David Hansen, Tasho Kaletha and Jared Weinstein, *On the Kottwitz conjecture for local shtuka
  spaces*, Forum of Mathematics, Pi 10 (2022), Appendix B.2.
-/

public section

open Function Set TopologicalSpace

namespace LocallyConstant

variable {X R : Type*} [TopologicalSpace X]

section Semiring

variable [Semiring R]

variable (X R) in
/-- The ideal `C_c(X, R)` of the ring `C(X, R)` of locally constant functions, consisting of the
locally constant functions with compact support. -/
def compactlySupportedIdeal : Ideal (LocallyConstant X R) where
  carrier := {f | HasCompactSupport f}
  add_mem' hf hg := hf.add hg
  zero_mem' := HasCompactSupport.zero
  smul_mem' c _ hf := by
    rw [Set.mem_ofPred_eq, smul_eq_mul, coe_mul]
    exact hf.mul_left

@[simp]
theorem mem_compactlySupportedIdeal {f : LocallyConstant X R} :
    f ∈ compactlySupportedIdeal X R ↔ HasCompactSupport f :=
  Iff.rfl

/-- The characteristic function of a compact clopen set has compact support. -/
theorem charFn_mem_compactlySupportedIdeal {U : Set X} (hU : IsClopen U) (hUc : IsCompact U) :
    charFn R hU ∈ compactlySupportedIdeal X R :=
  mem_compactlySupported.1 (indicator_mem_compactlySupported (R := R) 1 hU hUc)

/-- A locally constant function is fixed by multiplication with the characteristic function of its
support, which is clopen. -/
theorem charFn_support_mul (f : LocallyConstant X R) : charFn R f.isClopen_support * f = f := by
  ext x
  by_cases hx : f x = 0
  · simp [hx]
  · simp [coe_charFn, Set.indicator_of_mem (show x ∈ support f from hx)]

/-- In a Hausdorff space, the characteristic function `1_U` of a compact open set `U` has compact
support. -/
theorem _root_.TopologicalSpace.CompactOpens.charFn_mem_compactlySupportedIdeal [T2Space X]
    (U : CompactOpens X) : U.charFn R ∈ compactlySupportedIdeal X R := by
  rw [CompactOpens.charFn_def]
  exact LocallyConstant.charFn_mem_compactlySupportedIdeal _ U.isCompact

/-- In a Hausdorff space, every `f ∈ C_c(X, R)` is fixed by `1_U` for some compact open `U`, for
instance its support. -/
theorem exists_charFn_mul_eq_of_mem_compactlySupportedIdeal [T2Space X] {f : LocallyConstant X R}
    (hf : f ∈ compactlySupportedIdeal X R) : ∃ U : CompactOpens X, U.charFn R * f = f := by
  let U : CompactOpens X :=
    ⟨⟨support f, hasCompactSupport_iff_isCompact_support.1 hf⟩, f.isClopen_support.isOpen⟩
  refine ⟨U, ?_⟩
  rw [CompactOpens.charFn_def]
  exact charFn_support_mul f

end Semiring

/-- Over a commutative semiring `R`, the `R`-module underlying the ideal `C_c(X, R)` is the module
`C_c^∞(X, R)` of locally constant functions with compact support. -/
theorem restrictScalars_compactlySupportedIdeal [CommSemiring R] :
    (compactlySupportedIdeal X R).restrictScalars R = compactlySupported R X R :=
  Submodule.ext fun _ => by
    rw [Submodule.restrictScalars_mem, mem_compactlySupportedIdeal, mem_compactlySupported]

/-- For a commutative ring `R`, the ideal `C_c(X, R)` is pure: `C(X, R) ⧸ C_c(X, R)` is flat over
`C(X, R)`. Equivalently, each `f ∈ C_c(X, R)` is `f * g` for some `g ∈ C_c(X, R)`. -/
instance instPureCompactlySupportedIdeal [CommRing R] : (compactlySupportedIdeal X R).Pure :=
  (Ideal.pure_iff_forall_exists_eq_mul _).2 fun f hf =>
    ⟨charFn R f.isClopen_support,
      charFn_mem_compactlySupportedIdeal _ (hasCompactSupport_iff_isCompact_support.1 hf),
      by rw [mul_comm, charFn_support_mul]⟩

/-- Multiplication by a locally constant function `φ`, as an `R`-linear endomorphism of the module
`C_c^∞(X, R)` of test functions: the product of `φ` with a test function is again one, since
`C_c(X, R)` is an ideal. -/
def compactlySupported.mulLeft [CommSemiring R] (φ : LocallyConstant X R) :
    compactlySupported R X R →ₗ[R] compactlySupported R X R :=
  (LinearMap.mulLeft R φ).restrict fun _ hf ↦
    mem_compactlySupported.2 (mem_compactlySupported.1 hf).mul_left

@[simp]
theorem compactlySupported.coe_mulLeft_apply [CommSemiring R] (φ : LocallyConstant X R)
    (f : compactlySupported R X R) :
    (compactlySupported.mulLeft φ f : LocallyConstant X R) = φ * f :=
  (rfl)

end LocallyConstant
