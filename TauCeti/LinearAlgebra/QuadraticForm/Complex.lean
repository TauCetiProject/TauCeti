/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Quadratic forms over algebraically closed fields

Over an algebraically closed field of characteristic not two, a regular finite-dimensional
quadratic form is determined up to equivalence by its dimension.  In particular, every form on a
space of dimension at least two is isotropic, every nonzero form represents every scalar, and one
regular form is represented by another exactly when its dimension is not larger.  These facts
justify the omission of complex places from the local predicates used by the global
local-to-global theory.

The proofs use Mathlib's algebraically closed classification.  No separate complex quadratic-form
carrier is introduced.
-/

public section
noncomputable section

open QuadraticMap

namespace TauCeti.QuadraticForm

/-- A form over an algebraically closed field of characteristic not two has a nonzero isotropic
vector when its space has dimension at least two. -/
theorem _root_.QuadraticForm.not_anisotropic_of_isAlgClosed
    {K W : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (Q : QuadraticForm K W)
    (h : 2 ≤ Module.finrank K W) : ¬ Q.Anisotropic := by
  intro hQ
  obtain ⟨e⟩ := Q.equivalent_weightedSumSquares_of_isAlgClosed
    (QuadraticMap.separatingLeft_of_anisotropic Q hQ)
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : K)
  let k := Module.finrank K W - 2
  have hk : k + 1 + 1 = Module.finrank K W := by
    dsimp [k]
    omega
  have hn : 0 < Module.finrank K W := by omega
  let x₀ : Fin (k + 1 + 1) → K := Fin.cons 1 (Fin.cons i (fun _ : Fin k => 0))
  let x : Fin (Module.finrank K W) → K :=
    fun i => x₀ (Fin.cast hk.symm i)
  have hx : x ≠ 0 := by
    intro hx
    let i₀ : Fin (Module.finrank K W) := ⟨0, hn⟩
    have hi := congrArg (fun f => f i₀) hx
    simp [x, x₀, i₀] at hi
  have hzero : Q (e.symm x) = 0 := by
    rw [← e.map_app]
    rw [e.apply_symm_apply]
    simp only [weightedSumSquares_apply, Pi.one_apply, one_smul]
    rw [← (finCongr hk).sum_comp (fun i => x i * x i)]
    simp [x, x₀, Fin.sum_univ_succ, ← hi]
  apply hx
  rw [← e.apply_symm_apply x, hQ _ hzero]
  exact map_zero e

/-- Regular quadratic forms over an algebraically closed field on possibly different spaces are
equivalent when their dimensions agree. -/
theorem _root_.QuadraticForm.equivalent_of_finrank_eq_of_isAlgClosed
    {K W₁ W₂ : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)]
    [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁]
    [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]
    (Q : QuadraticForm K W₁) (R : QuadraticForm K W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate)
    (h : Module.finrank K W₁ = Module.finrank K W₂) : Q.Equivalent R := by
  let e : W₁ ≃ₗ[K] W₂ := LinearEquiv.ofFinrankEq W₁ W₂ h
  have hQ' : (QuadraticMap.associated Q).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  have hRsep : (QuadraticMap.associated R).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hR).1
  have hR' : (QuadraticMap.associated (R.comp (e : W₁ →ₗ[K] W₂))).SeparatingLeft := by
    rw [QuadraticMap.associated_comp]
    intro x hx
    apply e.injective
    simpa using hRsep (e x) (fun y ↦ by
      simpa [LinearMap.compl₁₂_apply] using hx (e.symm y))
  obtain ⟨e'⟩ := Q.equivalent_of_isAlgClosed (R.comp (e : W₁ →ₗ[K] W₂)) hQ' hR'
  exact ⟨e'.trans (R.isometryEquivOfCompLinearEquiv e).symm⟩

/-- Two regular quadratic forms over an algebraically closed field are equivalent precisely when
their dimensions agree. -/
@[simp] theorem _root_.QuadraticForm.equivalent_iff_finrank_eq_of_isAlgClosed
    {K W₁ W₂ : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)]
    [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁]
    [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]
    (Q : QuadraticForm K W₁) (R : QuadraticForm K W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.Equivalent R ↔ Module.finrank K W₁ = Module.finrank K W₂ := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · exact _root_.QuadraticForm.equivalent_of_finrank_eq_of_isAlgClosed Q R hQ hR

/-- A nonzero quadratic form over an algebraically closed field represents every scalar: a value
`Q v ≠ 0` can be rescaled to any scalar by a square root of the ratio. -/
theorem _root_.QuadraticForm.represents_of_ne_zero_of_isAlgClosed
    {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
    {Q : QuadraticForm K W} (hQ : Q ≠ 0) (a : K) : QuadraticMap.Represents Q a := by
  obtain ⟨v, hv⟩ : ∃ v, Q v ≠ 0 := by
    by_contra! h
    exact hQ (QuadraticMap.ext h)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_eq_mul_self (a / Q v)
  exact (QuadraticMap.represents_iff Q a).2
    ⟨t • v, by rw [QuadraticMap.map_smul, ← ht, smul_eq_mul, div_mul_cancel₀ _ hv]⟩

/-- A regular quadratic form over an algebraically closed field represents a nonzero scalar
precisely when its space is nonzero. -/
theorem _root_.QuadraticForm.represents_iff_finrank_pos_of_isAlgClosed
    {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {Q : QuadraticForm K W} (hQ : Q.Nondegenerate) {a : K}
    (ha : a ≠ 0) : QuadraticMap.Represents Q a ↔ 0 < Module.finrank K W := by
  rw [QuadraticMap.represents_iff]
  constructor
  · rintro ⟨v, rfl⟩
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, fun hv ↦ ha (by simp [hv])⟩
  · intro h
    have : Nontrivial W := Module.finrank_pos_iff.mp h
    exact (QuadraticMap.represents_iff Q a).1 <|
      _root_.QuadraticForm.represents_of_ne_zero_of_isAlgClosed hQ.ne_zero a

/-- One regular quadratic form over an algebraically closed field is represented by another
precisely when its dimension is at most the dimension of the other. -/
theorem _root_.QuadraticForm.isRepresentedBy_iff_finrank_le_of_isAlgClosed
    {K W₁ W₂ : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)]
    [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁]
    [AddCommGroup W₂] [Module K W₂] [FiniteDimensional K W₂]
    (Q : QuadraticForm K W₁) (R : QuadraticForm K W₂)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsRepresentedBy R ↔ Module.finrank K W₁ ≤ Module.finrank K W₂ := by
  constructor
  · rw [QuadraticMap.isRepresentedBy_iff]
    rintro ⟨f, hf, -⟩
    exact LinearMap.finrank_le_finrank_of_injective hf
  · intro h
    -- `R` is equivalent to `Q` extended orthogonally by a regular form of the missing dimension.
    let p : RegularFormPresentation K := ⟨Module.finrank K W₂ - Module.finrank K W₁, 1⟩
    have hQR : (Q.prod (presentedForm p)).Equivalent R :=
      _root_.QuadraticForm.equivalent_of_finrank_eq_of_isAlgClosed _ R
        (hQ.prod (nondegenerate_presentedForm p)) hR (by simp [p, Module.finrank_prod]; omega)
    refine QuadraticMap.IsRepresentedBy.trans ?_ hQR.isRepresentedBy
    exact (QuadraticMap.isRepresentedBy_iff _ _).2
      ⟨LinearMap.inl K W₁ _, LinearMap.inl_injective, fun x ↦ by simp⟩

end TauCeti.QuadraticForm
