/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MahlerBasis
public import Mathlib.Algebra.Exact.Basic

/-!
# The forward-difference exact sequence on the p-adic integers

The continuous linear operator `fwdDiffCLM E` sends `f` to `x ↦ f (x + 1) - f x`.
Its kernel consists precisely of the constant functions. For complete ultrametric normed
`ℤ_[p]`-modules it is surjective, with an isometric linear right inverse `mahlerPrimitive E`:
prepend a zero to the Mahler coefficients. This primitive is uniquely specified by its
vanishing at zero and its prescribed translation difference.

Thus the sequence `0 → E → C(ℤ_[p], E) → C(ℤ_[p], E) → 0`, with the constant inclusion and
translation difference, is split exact as a sequence of continuous `ℤ_[p]`-linear maps.
The splitting uses translation by **+1**; no choice of a generator of a multiplicative
p-adic group is implicit in it.

The construction uses Mathlib's `PadicInt.mahlerEquiv`, whose coefficients are iterated
forward differences, and its binomial basis `mahler`. The coefficient shift is the elementary
translation-difference calculation used in Douglas–Francis–Henriques–Hill (eds.),
*Topological Modular Forms*, Chapter 6.
-/

public section

open scoped ZeroAtInfty

namespace TauCeti

open PadicInt

variable {p : ℕ} [Fact p.Prime]
variable (E : Type*) [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]

/-- Translation by `+1` minus the identity, on continuous functions on the p-adic integers. -/
noncomputable def fwdDiffCLM : C(ℤ_[p], E) →L[ℤ_[p]] C(ℤ_[p], E) :=
  ContinuousMap.compCLM ℤ_[p] E ⟨fun x ↦ x + 1, continuous_id.add continuous_const⟩ -
    ContinuousLinearMap.id ℤ_[p] _

@[simp]
theorem fwdDiffCLM_apply (f : C(ℤ_[p], E)) (x : ℤ_[p]) :
    fwdDiffCLM E f x = f (x + 1) - f x := (rfl)

/-- The continuous translation difference is the forward difference on underlying functions. -/
theorem coe_fwdDiffCLM (f : C(ℤ_[p], E)) :
    ⇑(fwdDiffCLM E f) = fwdDiff 1 f := (rfl)

@[simp]
theorem fwdDiffCLM_const (c : E) :
    fwdDiffCLM E (ContinuousMap.const ℤ_[p] c) = 0 := by
  ext x
  simp

/-- A continuous function with zero translation difference is constant, with value `f 0`.
This only uses density of the natural numbers, not completeness or the ultrametric inequality. -/
theorem fwdDiffCLM_eq_zero_iff (f : C(ℤ_[p], E)) :
    fwdDiffCLM E f = 0 ↔ f = ContinuousMap.const ℤ_[p] (f 0) := by
  constructor
  · intro hf
    apply ContinuousMap.coe_injective
    apply denseRange_natCast.equalizer f.continuous continuous_const
    funext n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := congrArg (fun g : C(ℤ_[p], E) ↦ g (n : ℤ_[p])) hf
      simp only [fwdDiffCLM_apply, ContinuousMap.zero_apply, sub_eq_zero] at h
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using h.trans ih
  · intro hf
    rw [hf]
    exact fwdDiffCLM_const E _

/-- The kernel of translation difference is the image of the constant inclusion. -/
theorem exact_const_fwdDiffCLM :
    Function.Exact (ContinuousLinearMap.const ℤ_[p] ℤ_[p] : E →L[ℤ_[p]] C(ℤ_[p], E))
      (fwdDiffCLM E) := by
  intro f
  rw [fwdDiffCLM_eq_zero_iff]
  constructor
  · intro h
    exact ⟨f 0, h.symm⟩
  · rintro ⟨c, rfl⟩
    rfl

section Ultrametric

variable [IsUltrametricDist E]

/-- Translation difference has norm at most one for ultrametric coefficients. -/
theorem norm_fwdDiffCLM_le (f : C(ℤ_[p], E)) :
    ‖fwdDiffCLM E f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  simpa only [coe_fwdDiffCLM, Function.iterate_one] using
    IsUltrametricDist.norm_fwdDiff_iter_apply_le 1 f x 1

variable [CompleteSpace E]

/-- Taking a translation difference shifts the Mahler coefficients one place to the left. -/
@[simp]
theorem mahlerEquiv_fwdDiffCLM (f : C(ℤ_[p], E)) (n : ℕ) :
    mahlerEquiv E (fwdDiffCLM E f) n = mahlerEquiv E f (n + 1) := by
  simp only [mahlerEquiv_apply, coe_fwdDiffCLM, Function.iterate_succ_apply]

/-- The normalized discrete primitive: insert a zero before the Mahler coefficients.
It is a linear isometry, rather than merely an algebraic choice of a preimage. -/
noncomputable def mahlerPrimitive : C(ℤ_[p], E) →ₗᵢ[ℤ_[p]] C(ℤ_[p], E) where
  toFun f := (mahlerEquiv E).symm (ZeroAtInftyContinuousMap.cons 0 (mahlerEquiv E f))
  map_add' f g := by
    simpa only [map_add, zero_add] using congrArg (mahlerEquiv E).symm
      (ZeroAtInftyContinuousMap.cons_add (0 : E) 0 (mahlerEquiv E f) (mahlerEquiv E g))
  map_smul' c f := by
    simpa only [map_smul, smul_zero, RingHom.id_apply] using
      congrArg (mahlerEquiv (p := p) E).symm
      (ZeroAtInftyContinuousMap.cons_smul c (0 : E) (mahlerEquiv E f))
  norm_map' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometryEquiv.norm_map,
      ZeroAtInftyContinuousMap.norm_cons, norm_zero, max_eq_right (norm_nonneg _)]

/-- The Mahler coefficients of the normalized primitive, including its zero initial coefficient. -/
@[simp]
theorem mahlerEquiv_mahlerPrimitive (f : C(ℤ_[p], E)) :
    mahlerEquiv E (mahlerPrimitive E f) =
      ZeroAtInftyContinuousMap.cons 0 (mahlerEquiv E f) :=
  (mahlerEquiv E).apply_symm_apply _

@[simp]
theorem mahlerPrimitive_apply_zero (f : C(ℤ_[p], E)) : mahlerPrimitive E f 0 = 0 := by
  have h := congrArg (fun a : C₀(ℕ, E) ↦ a 0) (mahlerEquiv_mahlerPrimitive E f)
  simpa only [mahlerEquiv_apply, Function.iterate_zero, id_eq,
    ZeroAtInftyContinuousMap.cons_apply_zero] using h

/-- The normalized primitive is a right inverse to translation difference. -/
@[simp]
theorem fwdDiffCLM_mahlerPrimitive (f : C(ℤ_[p], E)) :
    fwdDiffCLM E (mahlerPrimitive E f) = f := by
  apply (mahlerEquiv E).injective
  ext n
  rw [mahlerEquiv_fwdDiffCLM, mahlerEquiv_mahlerPrimitive,
    ZeroAtInftyContinuousMap.cons_apply_succ]

/-- Every continuous function has a continuous discrete primitive, for every prime. -/
theorem fwdDiffCLM_surjective :
    Function.Surjective (fwdDiffCLM (p := p) E) :=
  fun f ↦ ⟨mahlerPrimitive E f, fwdDiffCLM_mahlerPrimitive E f⟩

/-- A normalized solution of the difference equation is the Mahler primitive. -/
theorem eq_mahlerPrimitive_of_fwdDiffCLM_eq {f g : C(ℤ_[p], E)}
    (hd : fwdDiffCLM E g = f) (h₀ : g 0 = 0) : g = mahlerPrimitive E f := by
  have h : fwdDiffCLM E (g - mahlerPrimitive E f) = 0 := by
    rw [map_sub, hd, fwdDiffCLM_mahlerPrimitive, sub_self]
  have hc := (fwdDiffCLM_eq_zero_iff E _).mp h
  simp only [ContinuousMap.sub_apply, h₀, mahlerPrimitive_apply_zero, sub_self,
    ContinuousMap.const_zero] at hc
  exact sub_eq_zero.mp hc

/-- Discrete integration after differentiation recovers the function modulo its initial constant. -/
@[simp]
theorem mahlerPrimitive_fwdDiffCLM (f : C(ℤ_[p], E)) :
    mahlerPrimitive E (fwdDiffCLM E f) =
      f - ContinuousMap.const ℤ_[p] (f 0) := by
  apply Eq.symm
  apply eq_mahlerPrimitive_of_fwdDiffCLM_eq
  · simp
  · simp

/-- The translation-difference equation has a unique solution with value zero at the origin. -/
theorem existsUnique_fwdDiffCLM_eq (f : C(ℤ_[p], E)) :
    ∃! g : C(ℤ_[p], E), fwdDiffCLM E g = f ∧ g 0 = 0 := by
  exact ⟨mahlerPrimitive E f,
    ⟨fwdDiffCLM_mahlerPrimitive E f, mahlerPrimitive_apply_zero E f⟩,
    fun g hg ↦ eq_mahlerPrimitive_of_fwdDiffCLM_eq E hg.1 hg.2⟩

end Ultrametric

/-- Pascal's identity for a Mahler term with arbitrary module coefficients. -/
@[simp]
theorem fwdDiffCLM_mahlerTerm_succ (a : E) (n : ℕ) :
    fwdDiffCLM (p := p) E (mahlerTerm a (n + 1)) = mahlerTerm a n := by
  ext x
  simp only [fwdDiffCLM_apply, mahlerTerm_apply, mahler_apply, Ring.choose_succ_succ,
    add_smul, add_sub_cancel_right]

/-- A constant Mahler term has zero forward difference. -/
@[simp]
theorem fwdDiffCLM_mahlerTerm_zero (a : E) :
    fwdDiffCLM (p := p) E (mahlerTerm a 0) = 0 := by
  ext x
  simp [mahlerTerm_apply, mahler_apply]

/-- Pascal's identity: the difference of the `(n+1)`st binomial basis function is the `n`th. -/
@[simp]
theorem fwdDiffCLM_mahler_succ (n : ℕ) :
    fwdDiffCLM ℤ_[p] (mahler (n + 1)) = mahler n := by
  simpa only [mahlerTerm_one] using fwdDiffCLM_mahlerTerm_succ (p := p) ℤ_[p] 1 n

/-- The constant binomial basis function has zero forward difference. -/
@[simp]
theorem fwdDiffCLM_mahler_zero : fwdDiffCLM ℤ_[p] (mahler 0) = 0 := by
  simpa only [mahlerTerm_one] using fwdDiffCLM_mahlerTerm_zero (p := p) ℤ_[p] 1

end TauCeti
