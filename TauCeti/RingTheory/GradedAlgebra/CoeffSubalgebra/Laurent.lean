/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Basic
public import TauCeti.Algebra.Polynomial.Laurent.TensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Inverting the parameter of a filtered coefficient algebra

For a multiplicative family `M` of submodules of an associative `R`-algebra `B` with
`1 ∈ M 1`, the coefficient subalgebra `coeffSubalgebra M ⊆ B[X]` is an algebra over the
parameter ring `R[X]`. This file shows that inverting the parameter forgets the filtration: if
the family is exhaustive, the scalar extension along `R[X] → R[T;T⁻¹]` is the constant family
`R[T;T⁻¹] ⊗[R] B`. The comparison sends `f ⊗ p` to `f` times the Laurent expansion
`TauCeti.laurentExpansion` of `p`: for `p = ∑ bₙ Xⁿ` this is `f * ∑ Tⁿ ⊗ bₙ`, so a monomial
`b Xⁿ` with `b ∈ M n` goes to `Tⁿ ⊗ b`. The algebra `B` need not be commutative.

The proof identifies the Laurent expansion `coeffSubalgebra M → R[T;T⁻¹] ⊗[R] B` as the
localization of `coeffSubalgebra M` at the powers of the parameter, and uses that localization
of modules is base change to the localized ring.

This is the generic fibre of the Rees construction; see J. Dixmier, *Enveloping Algebras*, for
filtered enveloping algebras and their Rees algebras.

## Main definitions

* `TauCeti.coeffSubalgebra.baseChangeLaurentEquiv`: for an exhaustive family, the
  `R[T;T⁻¹]`-algebra isomorphism `R[T;T⁻¹] ⊗[R[X]] coeffSubalgebra M ≃ R[T;T⁻¹] ⊗[R] B`.

## Main results

* `TauCeti.coeffSubalgebra.baseChangeLaurentEquiv_tmul`: the comparison multiplies the
  Laurent expansion of the second factor by the first factor.
-/

public section

open Polynomial LaurentPolynomial
open scoped TensorProduct

namespace TauCeti.coeffSubalgebra

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

variable (M : ℕ → Submodule R B) [SetLike.GradedMonoid M] (h1 : (1 : B) ∈ M 1)

/-- The Laurent expansion on the coefficient subalgebra, as a map of algebras over the
parameter ring. -/
private noncomputable def laurentParamAlgHom :
    letI := algebra M h1
    coeffSubalgebra M →ₐ[R[X]] R[T;T⁻¹] ⊗[R] B :=
  letI := algebra M h1
  { __ := (laurentExpansion R B).comp (coeffSubalgebra M).val
    commutes' p := by
      simp [laurentExpansion_map_algebraMap, Algebra.TensorProduct.algebraMap_apply] }

private theorem laurentParamAlgHom_apply (p : coeffSubalgebra M) :
    letI := algebra M h1
    laurentParamAlgHom M h1 p = laurentExpansion R B p :=
  rfl

include h1 in
/-- Some power of `T` carries every element of the constant family into the image of the
Laurent expansion of `coeffSubalgebra M`, when the family is exhaustive. -/
private theorem exists_T_pow_smul_eq_laurentExpansion (hex : (⨆ n, M n) = ⊤)
    (y : R[T;T⁻¹] ⊗[R] B) :
    ∃ (k : ℕ) (p : coeffSubalgebra M), (T k : R[T;T⁻¹]) • y = laurentExpansion R B p := by
  let := algebra M h1
  -- The elements carried into the image by a power of `T` form an `R[T;T⁻¹]`-submodule.
  let N : Submodule R[T;T⁻¹] (R[T;T⁻¹] ⊗[R] B) :=
    { carrier := {y | ∃ (k : ℕ) (p : coeffSubalgebra M),
        (T k : R[T;T⁻¹]) • y = laurentExpansion R B p}
      add_mem' := by
        rintro y z ⟨k, p, hp⟩ ⟨l, q, hq⟩
        refine ⟨k + l, X M h1 ^ l * p + X M h1 ^ k * q, ?_⟩
        rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow,
          Subalgebra.coe_pow, coe_X, map_add, laurentExpansion_X_pow_mul,
          laurentExpansion_X_pow_mul, ← hp, ← hq, smul_smul, smul_smul, smul_add, Nat.cast_add,
          T_add, mul_comm (T k : R[T;T⁻¹])]
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro f y ⟨k, p, hp⟩
        obtain ⟨l, g, hg⟩ := exists_T_pow f
        refine ⟨k + l, algebraMap R[X] (coeffSubalgebra M) g * p, ?_⟩
        rw [Subalgebra.coe_mul, coe_algebraMap, laurentExpansion_map_algebraMap_mul, hg, ← hp,
          smul_smul, smul_smul]
        congr 1
        rw [Nat.cast_add, T_add]
        ring }
  have hone (b : B) : (1 : R[T;T⁻¹]) ⊗ₜ[R] b ∈ N := by
    have hb : b ∈ ⨆ n, M n := hex ▸ Submodule.mem_top
    induction hb using Submodule.iSup_induction' with
    | mem n b hb =>
      refine ⟨n, monomial M n b hb, ?_⟩
      rw [coe_monomial, laurentExpansion_monomial, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | zero => simp
    | add b c _ _ hb hc => simpa [TensorProduct.tmul_add] using N.add_mem hb hc
  have hN : N = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun y ↦ ?_
    induction y using TensorProduct.inductionOn with
    | tmul f b => simpa [TensorProduct.smul_tmul'] using N.smul_mem f (hone b)
    | add y z hy hz => exact N.add_mem hy hz
  have hy : y ∈ N := hN ▸ Submodule.mem_top
  exact hy

/-- The Laurent expansion of `coeffSubalgebra M` is its localization at the powers of the
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
  · obtain ⟨k, p, hp⟩ := exists_T_pow_smul_eq_laurentExpansion M h1 hex y
    refine ⟨(p, ⟨Polynomial.X ^ k, k, rfl⟩), ?_⟩
    rw [Submonoid.smul_def, ← algebraMap_smul R[T;T⁻¹], algebraMap_X_pow, hp,
      AlgHom.toLinearMap_apply, laurentParamAlgHom_apply]
  · rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, laurentParamAlgHom_apply,
      laurentParamAlgHom_apply] at h
    rw [Subtype.ext (laurentExpansion_injective h)]

/-- The comparison map from the scalar extension along `R[X] → R[T;T⁻¹]` to the constant
family, before it is shown bijective. -/
private noncomputable def baseChangeLaurentAlgHom :
    letI := algebra M h1
    (R[T;T⁻¹] ⊗[R[X]] coeffSubalgebra M) →ₐ[R[T;T⁻¹]] R[T;T⁻¹] ⊗[R] B :=
  letI := algebra M h1
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (laurentParamAlgHom M h1)
    fun f _ ↦ by
      rw [Algebra.TensorProduct.includeLeft_apply, ← Algebra.algebraMap_self_apply f,
        ← Algebra.TensorProduct.algebraMap_apply]
      exact Algebra.commutes _ _

private theorem baseChangeLaurentAlgHom_tmul (f : R[T;T⁻¹]) (p : coeffSubalgebra M) :
    letI := algebra M h1
    baseChangeLaurentAlgHom M h1 (f ⊗ₜ[R[X]] p) = f • laurentExpansion R B p := by
  let := algebra M h1
  rw [baseChangeLaurentAlgHom, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.includeLeft_apply, laurentParamAlgHom_apply]
  conv_lhs => rw [← Algebra.algebraMap_self_apply f, ← Algebra.TensorProduct.algebraMap_apply]
  exact (Algebra.smul_def _ _).symm

private theorem baseChangeLaurentAlgHom_bijective (hex : (⨆ n, M n) = ⊤) :
    letI := algebra M h1
    Function.Bijective (baseChangeLaurentAlgHom M h1) := by
  let := algebra M h1
  have := isLocalizedModule_laurentParamAlgHom M h1 hex
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers (Polynomial.X : R[X])) R[T;T⁻¹]
    (laurentParamAlgHom M h1).toLinearMap).equiv
  have he : ⇑(baseChangeLaurentAlgHom M h1) = e := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul f p =>
      rw [baseChangeLaurentAlgHom_tmul, IsBaseChange.equiv_tmul, AlgHom.toLinearMap_apply,
        laurentParamAlgHom_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact he ▸ e.bijective

/-- **Inverting the parameter forgets the filtration.** For an exhaustive multiplicative family
`M` of submodules of `B` with `1 ∈ M 1`, the scalar extension of `coeffSubalgebra M` along
`R[X] → R[T;T⁻¹]` is the constant family `R[T;T⁻¹] ⊗[R] B`, by the Laurent expansion. -/
noncomputable def baseChangeLaurentEquiv (hex : (⨆ n, M n) = ⊤) :
    letI := algebra M h1
    (R[T;T⁻¹] ⊗[R[X]] coeffSubalgebra M) ≃ₐ[R[T;T⁻¹]] R[T;T⁻¹] ⊗[R] B :=
  AlgEquiv.ofBijective _ (baseChangeLaurentAlgHom_bijective M h1 hex)

/-- The comparison multiplies the Laurent expansion of the second factor by the first. -/
@[simp]
theorem baseChangeLaurentEquiv_tmul (hex : (⨆ n, M n) = ⊤) (f : R[T;T⁻¹])
    (p : coeffSubalgebra M) :
    letI := algebra M h1
    baseChangeLaurentEquiv M h1 hex (f ⊗ₜ[R[X]] p) = f • laurentExpansion R B p :=
  baseChangeLaurentAlgHom_tmul M h1 f p

/-- The inverse comparison sends the Laurent expansion of `p` to `1 ⊗ p`. -/
@[simp]
theorem baseChangeLaurentEquiv_symm_laurentExpansion (hex : (⨆ n, M n) = ⊤)
    (p : coeffSubalgebra M) :
    letI := algebra M h1
    (baseChangeLaurentEquiv M h1 hex).symm (laurentExpansion R B p) = 1 ⊗ₜ[R[X]] p := by
  let := algebra M h1
  rw [AlgEquiv.symm_apply_eq, baseChangeLaurentEquiv_tmul, one_smul]

end TauCeti.coeffSubalgebra
