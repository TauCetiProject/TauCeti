/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Ring.CompTypeclasses

/-!
# Renaming variables, and discarding the ones outside the range

Renaming the variables of a multivariable polynomial along an equivalence `e : σ ≃ τ` is a
ring equivalence. Mathlib's `RingHomInvPair.of_ringEquiv` and
`RingHomInvPair.of_ringEquiv_symm` are deliberately not instances, so this file registers them
for `MvPolynomial.renameEquiv`. This lets semilinear equivalences over variable renaming be used
and inverted without requiring downstream local instances.

Injective variable renaming reindexes the native coefficient vector along the induced embedding
of exponent vectors.

Along an injective renaming `f : σ → τ`, Mathlib's `MvPolynomial.killCompl` sets the variables
outside the range of `f` to zero. When exactly one variable `X a` is discarded, the polynomials
it kills are exactly the multiples of `X a`.

## Main definitions

* `TauCeti.renameRingHomInvPair`: variable renaming and its inverse form a `RingHomInvPair`.
* `TauCeti.renameRingHomInvPairSymm`: the same inverse pair in the reverse direction.

## Main results

* `MvPolynomial.coeff_rename_eq_embDomain`: injective renaming embeds the coefficient vector
  along the induced map of exponents.
* `MvPolynomial.killCompl_X_apply`, `MvPolynomial.killCompl_X_of_notMem_range`,
  `MvPolynomial.killCompl_eq_aeval`: action of `killCompl` on variables inside and outside the
  range of an injective renaming, and its characterization as an `aeval`.
* `MvPolynomial.eval_killCompl`: evaluating `killCompl hf p` at `x ∘ f` agrees with evaluating `p`
  at `x` when `x` vanishes outside the range of `f`.
* `MvPolynomial.killCompl_eq_zero_iff_X_dvd`: when the range of the renaming is the complement of
  a single variable `X a`, discarding that variable kills exactly the multiples of `X a`.
* `Polynomial.map_eval_map_rename`: for a polynomial family with coefficients in `MvPolynomial`,
  specializing after renaming the parameters along `f` is specializing at the composite point.
-/

public section

namespace MvPolynomial

variable {R σ τ : Type*} [CommSemiring R]

/-- Injective variable renaming reindexes the native coefficient vector by the induced
embedding of exponent vectors. -/
theorem coeff_rename_eq_embDomain (p : MvPolynomial σ R) {f : σ → τ}
    (hf : Function.Injective f) :
    AddMonoidAlgebra.coeff (rename f p) =
      (AddMonoidAlgebra.coeff p).embDomain
        ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective hf⟩ := by
  classical
  let e : (σ →₀ ℕ) ↪ (τ →₀ ℕ) :=
    ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective hf⟩
  ext d
  by_cases hd : ∃ a, e a = d
  · obtain ⟨a, rfl⟩ := hd
    rw [Finsupp.embDomain_apply_self]
    -- Since `MvPolynomial` abbreviates `AddMonoidAlgebra`, `.coeff` is its native coefficient
    -- evaluation, and `e a` reduces to `a.mapDomain f`. Expose this form to apply
    -- `coeff_rename_embDomain`.
    change (rename f p).coeff (a.mapDomain f) = p.coeff a
    simpa only [Finsupp.embDomain_eq_mapDomain, Function.Embedding.coeFn_mk] using
      coeff_rename_embDomain ⟨f, hf⟩ p a
  · rw [Finsupp.embDomain_of_notMem_range e _ d hd]
    exact coeff_rename_eq_zero f p d (fun a ha ↦ (hd ⟨a, ha⟩).elim)

variable {σ τ R : Type*} [CommSemiring R] {f : σ → τ} (hf : Function.Injective f) {a : τ}

/-- A variable in the range of an injective renaming maps to the corresponding variable under
`killCompl`. -/
@[simp]
theorem killCompl_X_apply (i : σ) : killCompl (R := R) hf (X (f i)) = X i := by
  rw [← rename_X (f := f), killCompl_rename_app]

/-- A variable outside the range of an injective renaming is killed by `killCompl`. -/
@[simp]
theorem killCompl_X_of_notMem_range (ha : a ∉ Set.range f) :
    killCompl (R := R) hf (X a) = 0 := by
  rw [X]
  exact killCompl_monomial_eq_zero_of_notMem_range hf (s := Finsupp.single a 1) 1
    (a := a) (by simp) ha

/-- Discarding variables outside the range of an injective renaming `f` is algebra evaluation at
`Function.extend f X 0`. -/
theorem killCompl_eq_aeval :
    killCompl (R := R) hf = aeval (Function.extend f X (0 : τ → MvPolynomial σ R)) := by
  classical
  apply algHom_ext
  intro j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    rw [killCompl_X_apply, aeval_X, hf.extend_apply]
  · rw [killCompl_X_of_notMem_range hf hj, aeval_X, Function.extend_apply' _ _ _ hj,
      Pi.zero_apply]

/-- Evaluating `killCompl hf p` at `x ∘ f` equals evaluating `p` at `x`, provided `x` vanishes
outside the range of `f`. -/
theorem eval_killCompl {x : τ → R} (hx : ∀ a ∉ Set.range f, x a = 0) (p : MvPolynomial τ R) :
    eval (x ∘ f) (killCompl (R := R) hf p) = eval x p := by
  classical
  have h : (aeval (x ∘ f)).comp (killCompl (R := R) hf) = aeval x := by
    apply algHom_ext
    intro j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      simp
    · rw [AlgHom.comp_apply, killCompl_X_of_notMem_range hf hj, map_zero, aeval_X, hx j hj]
  simpa only [← aeval_eq_eval, AlgHom.comp_apply] using AlgHom.congr_fun h p

/-- When the range of an injective renaming is the complement of a single variable `X a`,
discarding the variables outside the range kills exactly the multiples of `X a`. -/
theorem killCompl_eq_zero_iff_X_dvd (ha : Set.range f = {a}ᶜ) (p : MvPolynomial τ R) :
    killCompl hf p = 0 ↔ X a ∣ p := by
  have hna : a ∉ Set.range f := by simp [ha]
  constructor
  · intro h
    rw [X_dvd_iff_modMonomial_eq_zero]
    refine MvPolynomial.ext _ _ fun m => ?_
    rcases Nat.eq_zero_or_pos (m a) with hm | hm
    · -- A monomial avoiding `a` is renamed from a monomial in the source variables.
      have hsub : ↑m.support ⊆ Set.range f := by
        intro x hx
        rw [ha]
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl
        exact (Finsupp.mem_support_iff.mp hx) hm
      have hmd : Finsupp.mapDomain f (Finsupp.comapDomain f m hf.injOn) = m :=
        m.mapDomain_comapDomain f hf hsub
      rw [coeff_modMonomial_of_not_le _ (by rw [Finsupp.single_le_iff]; omega), ← hmd,
        ← coeff_killCompl hf, h]
      simp
    · rw [coeff_modMonomial_of_le _ (by rw [Finsupp.single_le_iff]; omega)]
      simp
  · rintro ⟨q, rfl⟩
    rw [map_mul, killCompl_X_of_notMem_range hf hna, zero_mul]

end MvPolynomial

namespace Polynomial

/-- Renaming the parameters of a polynomial family `P : (MvPolynomial σ R)[X]` along `f` and then
specializing them at `y` is specializing `P` at `y ∘ f`. -/
theorem map_eval_map_rename {σ τ R : Type*} [CommSemiring R] (f : σ → τ)
    (P : (MvPolynomial σ R)[X]) (y : τ → R) :
    (P.map (MvPolynomial.rename (R := R) f).toRingHom).map (MvPolynomial.eval y) =
      P.map (MvPolynomial.eval (y ∘ f)) := by
  rw [Polynomial.map_map]
  congr 1
  ext <;> simp

end Polynomial

namespace TauCeti

variable {σ τ : Type*} (R : Type*) [CommSemiring R]

/-- A polynomial variable-renaming ring equivalence and its inverse form a
`RingHomInvPair`. -/
noncomputable instance renameRingHomInvPair (e : σ ≃ τ) :
    RingHomInvPair
      ((MvPolynomial.renameEquiv R e).toRingEquiv :
        MvPolynomial σ R →+* MvPolynomial τ R)
      ((MvPolynomial.renameEquiv R e).toRingEquiv.symm :
        MvPolynomial τ R →+* MvPolynomial σ R) :=
  RingHomInvPair.of_ringEquiv (MvPolynomial.renameEquiv R e).toRingEquiv

/-- The inverse polynomial variable-renaming ring equivalence and the forward equivalence form a
`RingHomInvPair`. -/
noncomputable instance renameRingHomInvPairSymm (e : σ ≃ τ) :
    RingHomInvPair
      ((MvPolynomial.renameEquiv R e).toRingEquiv.symm :
        MvPolynomial τ R →+* MvPolynomial σ R)
      ((MvPolynomial.renameEquiv R e).toRingEquiv :
        MvPolynomial σ R →+* MvPolynomial τ R) :=
  RingHomInvPair.of_ringEquiv_symm (MvPolynomial.renameEquiv R e).toRingEquiv

end TauCeti
