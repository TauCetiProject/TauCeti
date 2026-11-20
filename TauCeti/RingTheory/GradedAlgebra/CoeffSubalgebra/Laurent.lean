/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Basic
public import TauCeti.Algebra.Polynomial.Laurent.TensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Inverting the parameter of a filtered coefficient algebra

For a multiplicative family `M` of submodules of an associative `R`-algebra `B` with
`1 ∈ M 1`, the coefficient subalgebra `coeffSubalgebra M ⊆ B[X]` is an algebra over the
parameter ring `R[X]`. This file shows that inverting the parameter forgets the filtration: if
the family is exhaustive, the scalar extension along `R[X] → R[T;T⁻¹]` is the constant family
`R[T;T⁻¹] ⊗[R] B`. The comparison sends `f ⊗ p` to `f` times the image
`TauCeti.toLaurentTensor p`: for `p = ∑ bₙ Xⁿ` this is `f * ∑ Tⁿ ⊗ bₙ`, so a monomial
`b Xⁿ` with `b ∈ M n` goes to `Tⁿ ⊗ b`. The algebra `B` need not be commutative.

The proof identifies `toLaurentTensor : coeffSubalgebra M → R[T;T⁻¹] ⊗[R] B` as the
localization of `coeffSubalgebra M` at the powers of the parameter, and uses that localization
of modules is base change to the localized ring.

This is the Rees construction with the parameter inverted; see J. Dixmier, *Enveloping
Algebras*, for filtered enveloping algebras and their Rees algebras.

## Main definitions

* `TauCeti.coeffSubalgebra.baseChangeLaurentEquiv`: for an exhaustive family, the
  `R[T;T⁻¹]`-algebra isomorphism `R[T;T⁻¹] ⊗[R[X]] coeffSubalgebra M ≃ R[T;T⁻¹] ⊗[R] B`.

## Main results

* `TauCeti.coeffSubalgebra.baseChangeLaurentEquiv_tmul`: the comparison multiplies the
  image of the second factor under `toLaurentTensor` by the first factor.
* `TauCeti.coeffSubalgebra.baseChangeLaurentEquiv_symm_tmul_of_mem`: the inverse comparison
  sends `f ⊗ b`, for `b ∈ M n`, to `f T⁻ⁿ ⊗ b Xⁿ`.
-/

public section

open Polynomial LaurentPolynomial
open scoped TensorProduct

namespace TauCeti.coeffSubalgebra

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

variable (M : ℕ → Submodule R B) [SetLike.GradedMonoid M] (h1 : (1 : B) ∈ M 1)

/-- `toLaurentTensor` on the coefficient subalgebra, as a map of algebras over the
parameter ring. -/
private noncomputable def laurentParamAlgHom :
    letI := algebra M h1
    coeffSubalgebra M →ₐ[R[X]] R[T;T⁻¹] ⊗[R] B :=
  letI := algebra M h1
  { __ := (toLaurentTensor R B).comp (coeffSubalgebra M).val
    commutes' p := by
      simp [toLaurentTensor_map_algebraMap, Algebra.TensorProduct.algebraMap_apply] }

private theorem laurentParamAlgHom_apply (p : coeffSubalgebra M) :
    letI := algebra M h1
    laurentParamAlgHom M h1 p = toLaurentTensor R B p :=
  rfl

include h1 in
/-- Some power of `T` carries every element of the constant family into the image of
`coeffSubalgebra M` under `toLaurentTensor`, when the family is exhaustive. -/
private theorem exists_T_pow_smul_eq_toLaurentTensor (hex : (⨆ n, M n) = ⊤)
    (y : R[T;T⁻¹] ⊗[R] B) :
    ∃ (k : ℕ) (p : coeffSubalgebra M), (T k : R[T;T⁻¹]) • y = toLaurentTensor R B p := by
  let := algebra M h1
  let N := LinearMap.range (laurentParamAlgHom M h1).toLinearMap
  have hone (b : B) : (1 : R[T;T⁻¹]) ⊗ₜ[R] b ∈ Submodule.span R[T;T⁻¹] (N : Set _) := by
    have hb : b ∈ ⨆ n, M n := hex ▸ Submodule.mem_top
    induction hb using Submodule.iSup_induction' with
    | mem n b hb =>
      have h : (T (-(n : ℤ)) : R[T;T⁻¹]) • laurentParamAlgHom M h1 (monomial M n b hb) =
          1 ⊗ₜ[R] b := by
        rw [laurentParamAlgHom_apply, coe_monomial, toLaurentTensor_monomial,
          TensorProduct.smul_tmul', smul_eq_mul, ← T_add, neg_add_cancel, T_zero]
      exact h ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨monomial M n b hb, rfl⟩)
    | zero => simp
    | add b c _ _ hb hc => simpa [TensorProduct.tmul_add] using add_mem hb hc
  have hy : y ∈ Submodule.span R[T;T⁻¹] (N : Set _) := by
    induction y using TensorProduct.inductionOn with
    | tmul f b => simpa [TensorProduct.smul_tmul'] using Submodule.smul_mem _ f (hone b)
    | add y z hy hz => exact add_mem hy hz
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    multiple_mem_span_of_mem_localization_span (Submonoid.powers (Polynomial.X : R[X]))
      R[T;T⁻¹] _ y hy
  rw [Submodule.span_eq] at hk
  obtain ⟨p, hp⟩ := hk
  refine ⟨k, p, ?_⟩
  rw [← algebraMap_X_pow, algebraMap_smul]
  exact hp.symm

/-- `toLaurentTensor` on `coeffSubalgebra M` is its localization at the powers of the
parameter, when the family is exhaustive. -/
private theorem isLocalizedModule_laurentParamAlgHom (hex : (⨆ n, M n) = ⊤) :
    letI := algebra M h1
    IsLocalizedModule (Submonoid.powers (Polynomial.X : R[X]))
      (laurentParamAlgHom M h1).toLinearMap := by
  let := algebra M h1
  refine ⟨?_, fun y ↦ ?_, fun {p q} h ↦ ⟨1, ?_⟩⟩
  · rintro ⟨_, k, rfl⟩
    refine (Module.End.isUnit_iff _).mpr ?_
    convert (isUnit_T (k : ℤ) (R := R)).smul_bijective (β := R[T;T⁻¹] ⊗[R] B) using 2 with y
    rw [Module.algebraMap_end_apply, ← algebraMap_smul R[T;T⁻¹], algebraMap_X_pow]
  · obtain ⟨k, p, hp⟩ := exists_T_pow_smul_eq_toLaurentTensor M h1 hex y
    refine ⟨(p, ⟨Polynomial.X ^ k, k, rfl⟩), ?_⟩
    rw [Submonoid.smul_def, ← algebraMap_smul R[T;T⁻¹], algebraMap_X_pow, hp,
      AlgHom.toLinearMap_apply, laurentParamAlgHom_apply]
  · rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, laurentParamAlgHom_apply,
      laurentParamAlgHom_apply] at h
    rw [Subtype.ext (toLaurentTensor_injective h)]

private theorem liftEquiv_laurentParamAlgHom_bijective (hex : (⨆ n, M n) = ⊤) :
    letI := algebra M h1
    Function.Bijective
      (AlgHom.liftEquiv R[X] R[T;T⁻¹] (coeffSubalgebra M) _ (laurentParamAlgHom M h1)) := by
  let := algebra M h1
  have := isLocalizedModule_laurentParamAlgHom M h1 hex
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers (Polynomial.X : R[X])) R[T;T⁻¹]
    (laurentParamAlgHom M h1).toLinearMap).equiv
  have he : ⇑(AlgHom.liftEquiv R[X] R[T;T⁻¹] (coeffSubalgebra M) _ (laurentParamAlgHom M h1)) =
      e := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul f p => rw [AlgHom.liftEquiv_tmul, IsBaseChange.equiv_tmul, AlgHom.toLinearMap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact he ▸ e.bijective

/-- **Inverting the parameter forgets the filtration.** For an exhaustive multiplicative family
`M` of submodules of `B` with `1 ∈ M 1`, the scalar extension of `coeffSubalgebra M` along
`R[X] → R[T;T⁻¹]` is the constant family `R[T;T⁻¹] ⊗[R] B`, via `toLaurentTensor`. -/
noncomputable def baseChangeLaurentEquiv (hex : (⨆ n, M n) = ⊤) :
    letI := algebra M h1
    (R[T;T⁻¹] ⊗[R[X]] coeffSubalgebra M) ≃ₐ[R[T;T⁻¹]] R[T;T⁻¹] ⊗[R] B :=
  AlgEquiv.ofBijective _ (liftEquiv_laurentParamAlgHom_bijective M h1 hex)

/-- The comparison multiplies the image of the second factor under `toLaurentTensor` by the
first. -/
@[simp]
theorem baseChangeLaurentEquiv_tmul (hex : (⨆ n, M n) = ⊤) (f : R[T;T⁻¹])
    (p : coeffSubalgebra M) :
    letI := algebra M h1
    baseChangeLaurentEquiv M h1 hex (f ⊗ₜ[R[X]] p) = f • toLaurentTensor R B p := by
  let := algebra M h1
  rw [baseChangeLaurentEquiv, AlgEquiv.ofBijective_apply, AlgHom.liftEquiv_tmul,
    laurentParamAlgHom_apply]

/-- The inverse comparison sends the image `toLaurentTensor p` to `1 ⊗ p`. -/
@[simp]
theorem baseChangeLaurentEquiv_symm_toLaurentTensor (hex : (⨆ n, M n) = ⊤)
    (p : coeffSubalgebra M) :
    letI := algebra M h1
    (baseChangeLaurentEquiv M h1 hex).symm (toLaurentTensor R B p) = 1 ⊗ₜ[R[X]] p := by
  let := algebra M h1
  rw [AlgEquiv.symm_apply_eq, baseChangeLaurentEquiv_tmul, one_smul]

/-- The inverse comparison sends `f ⊗ b`, for `b ∈ M n`, to `f T⁻ⁿ ⊗ b Xⁿ`. -/
theorem baseChangeLaurentEquiv_symm_tmul_of_mem (hex : (⨆ n, M n) = ⊤) (f : R[T;T⁻¹])
    {n : ℕ} {b : B} (hb : b ∈ M n) :
    letI := algebra M h1
    (baseChangeLaurentEquiv M h1 hex).symm (f ⊗ₜ[R] b) =
      (f * T (-n)) ⊗ₜ[R[X]] monomial M n b hb := by
  let := algebra M h1
  rw [AlgEquiv.symm_apply_eq, baseChangeLaurentEquiv_tmul, coe_monomial, toLaurentTensor_monomial,
    TensorProduct.smul_tmul', smul_eq_mul, mul_assoc, ← T_add, neg_add_cancel, T_zero, mul_one]

end TauCeti.coeffSubalgebra
