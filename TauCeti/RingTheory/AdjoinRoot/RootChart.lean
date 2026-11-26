/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.RingTheory.AdjoinRoot.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.Basis.Diagonal

/-!
# The `μ_n`-coaction on the affine root chart and the action comparison

For a commutative ring `A`, an element `f ∈ A` and `n ∈ ℕ`, write `B = A[t]/(tⁿ - f)` for the
affine root chart and `H = A[h]/(hⁿ - 1)` for the coordinate ring of the group scheme `μ_n` of
`n`th roots of unity (`H` is `B` at `f = 1`). The group scheme `μ_n` acts on `Spec B` by scaling
the root, `ζ • t = ζ t`. In coordinates this action is the `A`-algebra map
`δ : B → H ⊗[A] B` with `δ(t) = h ⊗ t` (`TauCeti.rootChartCoaction`), and the action comparison
`μ_n ×_A Spec B → Spec B ×_A Spec B`, `(ζ, x) ↦ (ζ x, x)`, has coordinate ring map
`Θ : B ⊗[A] B → H ⊗[A] B`, `b ⊗ c ↦ δ(b) (1 ⊗ c)` (`TauCeti.rootChartComparison`).

The main results are the sharp criteria for `Θ` to be injective, surjective or bijective, over an
arbitrary commutative ring `A`, for arbitrary `f` and positive `n`; no reducedness of `A` and no
invertibility of `n` in `A` is assumed. In the monomial bases, `Θ(tⁱ ⊗ tʲ)` is
`f ^ ((i + j) / n) • (hⁱ ⊗ t^((i + j) % n))`, so `Θ` permutes the basis up to the weights `1`
(when `i + j < n`) and `f` (when `n ≤ i + j`). The weight `f` occurs exactly when `n ≥ 2`, so
`Θ` is injective if and only if `n = 1` or multiplication by `f` on `A` is injective, and
surjective if and only if `n = 1` or `f` is a unit. For instance over `A = ℤ` with `n = 2` and
`f = 2`, the comparison is injective but not surjective.

## Main definitions

* `TauCeti.rootChart`: the affine root chart `A[t]/(tⁿ - f)`.
* `TauCeti.rootChartCoaction`: the coaction `δ : B → H ⊗[A] B`, `t ↦ h ⊗ t`.
* `TauCeti.rootChartComparison`: the action comparison `Θ : B ⊗[A] B → H ⊗[A] B`.

## Main results

* `TauCeti.rootChartComparison_root_pow_tmul_root_pow`: the weighted permutation formula
  `Θ(tⁱ ⊗ tʲ) = f ^ ((i + j) / n) • (hⁱ ⊗ t^((i + j) % n))`.
* `TauCeti.rootChartComparison_basis_tensorProduct`: the same formula in the monomial bases,
  exhibiting `Θ` as diagonal against a cyclically reindexed target basis.
* `TauCeti.rootChartComparison_injective_iff`: for `n ≠ 0`, `Θ` is injective if and only if
  `n = 1` or `f` is left regular.
* `TauCeti.rootChartComparison_surjective_iff`: for `n ≠ 0`, `Θ` is surjective if and only if
  `n = 1` or `f` is a unit.
* `TauCeti.rootChartComparison_bijective_iff`: for `n ≠ 0`, `Θ` is bijective if and only if
  `n = 1` or `f` is a unit.

## References

* M. Talpo, A. Vistoli, *Infinite root stacks and quasi-coherent sheaves on logarithmic
  schemes*, Proc. Lond. Math. Soc. (3) 116 (2018), arXiv:1410.1164, §3.1: the character grading
  of the root chart.
* The Stacks Project, Lemma 59.28.3 (Tag 040N): the finite free cover `A[t]/(tⁿ - f)` of
  `Spec A` for a unit `f` and its `μ_n`-action.
-/

public section

open Polynomial TensorProduct

namespace TauCeti

/-- The affine root chart `A[t]/(tⁿ - f)`, for a commutative ring `A`, an arbitrary `f ∈ A` and
`n ∈ ℕ`. At `f = 1` it is `A[h]/(hⁿ - 1)`, the coordinate ring of `μ_n`. -/
abbrev rootChart (A : Type*) [CommRing A] (f : A) (n : ℕ) :=
  AdjoinRoot (X ^ n - C f : A[X])

variable (A : Type*) [CommRing A] (f : A) (n : ℕ)

/-- The coaction `δ : A[t]/(tⁿ - f) → A[h]/(hⁿ - 1) ⊗[A] A[t]/(tⁿ - f)` of the coordinate ring
of `μ_n` on the affine root chart: the `A`-algebra map with `δ(t) = h ⊗ t`. It is the coordinate
ring map of the action of `μ_n` on `Spec A[t]/(tⁿ - f)` scaling the root. -/
noncomputable def rootChartCoaction : rootChart A f n →ₐ[A] rootChart A 1 n ⊗[A] rootChart A f n :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (AdjoinRoot.root _ ⊗ₜ AdjoinRoot.root _) (by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, Algebra.TensorProduct.tmul_pow,
      AdjoinRoot.root_X_pow_sub_C_pow, map_one, sub_eq_zero]
    -- `AdjoinRoot.of` is `algebraMap` by definition (`AdjoinRoot.algebraMap_eq`).
    exact (Algebra.TensorProduct.algebraMap_apply' f).symm)

/-- The coaction sends the root `t` to `h ⊗ t`. -/
@[simp]
theorem rootChartCoaction_root :
    rootChartCoaction A f n (AdjoinRoot.root _) = AdjoinRoot.root _ ⊗ₜ AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The coaction fixes constants: `δ(a) = 1 ⊗ a`. -/
theorem rootChartCoaction_algebraMap (a : A) :
    rootChartCoaction A f n (algebraMap A _ a) = 1 ⊗ₜ algebraMap A _ a := by
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply']

/-- The coaction fixes constants, stated with `AdjoinRoot.of`, the simp normal form of
`algebraMap` (`AdjoinRoot.algebraMap_eq`): `δ(a) = 1 ⊗ a`. -/
@[simp]
theorem rootChartCoaction_of (a : A) :
    rootChartCoaction A f n (AdjoinRoot.of _ a) = 1 ⊗ₜ AdjoinRoot.of _ a := by
  simpa using rootChartCoaction_algebraMap A f n a

/-- The character weight of a root power: the coaction sends `tⁱ` to `hⁱ ⊗ tⁱ`. -/
theorem rootChartCoaction_root_pow (i : ℕ) :
    rootChartCoaction A f n (AdjoinRoot.root _ ^ i) =
      (AdjoinRoot.root _ ^ i) ⊗ₜ (AdjoinRoot.root _ ^ i) := by
  rw [map_pow, rootChartCoaction_root, Algebra.TensorProduct.tmul_pow]

/-- An `A`-algebra map `A[t]/(tⁿ - f) → A[h]/(hⁿ - 1) ⊗[A] A[t]/(tⁿ - f)` sending `t` to `h ⊗ t` is
the coaction. -/
theorem eq_rootChartCoaction_of_root
    {ψ : rootChart A f n →ₐ[A] rootChart A 1 n ⊗[A] rootChart A f n}
    (hψ : ψ (AdjoinRoot.root _) = AdjoinRoot.root _ ⊗ₜ AdjoinRoot.root _) :
    ψ = rootChartCoaction A f n :=
  AdjoinRoot.algHom_ext (by rw [hψ, rootChartCoaction_root])

/-- The action comparison `Θ : B ⊗[A] B → H ⊗[A] B`, `b ⊗ c ↦ δ(b) (1 ⊗ c)`, for the affine root
chart `B = A[t]/(tⁿ - f)` and `H = A[h]/(hⁿ - 1)`. It is the coordinate ring map of the action
comparison `μ_n ×_A Spec B → Spec B ×_A Spec B`, `(ζ, x) ↦ (ζ x, x)`. -/
noncomputable def rootChartComparison :
    rootChart A f n ⊗[A] rootChart A f n →ₐ[A] rootChart A 1 n ⊗[A] rootChart A f n :=
  Algebra.TensorProduct.lift (rootChartCoaction A f n) Algebra.TensorProduct.includeRight
    fun _ _ => Commute.all _ _

/-- The action comparison on a pure tensor: `Θ(b ⊗ c) = δ(b) (1 ⊗ c)`. -/
@[simp]
theorem rootChartComparison_tmul (b c : rootChart A f n) :
    rootChartComparison A f n (b ⊗ₜ c) = rootChartCoaction A f n b * (1 ⊗ₜ c) := by
  rw [rootChartComparison, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.includeRight_apply]

/-- The weighted permutation formula for the action comparison on monomials:
`Θ(tⁱ ⊗ tʲ) = f ^ ((i + j) / n) • (hⁱ ⊗ t^((i + j) % n))`. For `i, j < n` the weight is `f` when
`n ≤ i + j` and `1` otherwise. -/
theorem rootChartComparison_root_pow_tmul_root_pow (i j : ℕ) :
    rootChartComparison A f n ((AdjoinRoot.root _ ^ i) ⊗ₜ (AdjoinRoot.root _ ^ j)) =
      f ^ ((i + j) / n) •
        ((AdjoinRoot.root (X ^ n - C 1 : A[X]) ^ i) ⊗ₜ (AdjoinRoot.root _ ^ ((i + j) % n))) := by
  rw [rootChartComparison_tmul, rootChartCoaction_root_pow, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, ← pow_add, AdjoinRoot.root_X_pow_sub_C_pow_eq_mul_pow_mod n (i + j) f]
  -- Move the weight `f ^ ((i + j) / n)` out of the second factor as a scalar.
  rw [← tmul_smul, Algebra.smul_def, AdjoinRoot.algebraMap_eq, map_pow]

section Criteria

variable [NeZero n]

/-- For `p : Fin n × Fin n`, the weight `f ^ ((p.1 + p.2) / n)` lies in a class of elements
closed under powers of `f` and containing `1` for every `p` exactly when `n = 1` or `f` lies in
the class: the weight is `f` at `p = (1, n - 1)` once `n ≥ 2`, and `1` throughout when `n = 1`. -/
private theorem forall_pow_div_iff {P : A → Prop} (hpow : ∀ k, P f → P (f ^ k)) (hone : P 1) :
    (∀ p : Fin n × Fin n, P (f ^ (((p.1 : ℕ) + p.2) / n))) ↔ n = 1 ∨ P f := by
  have hn := NeZero.ne n
  refine ⟨fun h => or_iff_not_imp_left.2 fun hn1 => ?_, ?_⟩
  · have := h (⟨1, by omega⟩, ⟨n - 1, by omega⟩)
    rwa [show (1 + (n - 1)) / n = 1 by rw [Nat.add_sub_cancel' (by omega), Nat.div_self (by omega)],
      pow_one] at this
  · rintro (rfl | hf) p
    · have h1 := p.1.isLt
      have h2 := p.2.isLt
      rwa [show ((p.1 : ℕ) + p.2) / 1 = 0 by omega, pow_zero]
    · exact hpow _ hf

/-- The action comparison sends each monomial `tⁱ ⊗ tʲ` of the source basis to
`f ^ ((i + j) / n)` times the monomial `hⁱ ⊗ t^(i + j)` of the target basis, the exponent of `t`
read modulo `n`. -/
theorem rootChartComparison_basis_tensorProduct [Nontrivial A] (p : Fin n × Fin n) :
    rootChartComparison A f n ((AdjoinRoot.basisXPowSubC n f).tensorProduct
        (AdjoinRoot.basisXPowSubC n f) p) =
      f ^ (((p.1 : ℕ) + p.2) / n) • (((AdjoinRoot.basisXPowSubC n (1 : A)).tensorProduct
        (AdjoinRoot.basisXPowSubC n f)).reindex
          (Equiv.prodShear (Equiv.refl _) Equiv.addLeft).symm p) := by
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.tensorProduct_apply',
    Module.Basis.tensorProduct_apply']
  simp only [AdjoinRoot.basisXPowSubC_apply, Equiv.prodShear_apply, Equiv.refl_apply,
    Equiv.coe_addLeft, Fin.val_add]
  exact rootChartComparison_root_pow_tmul_root_pow A f n _ _

/-- **Sharp injectivity criterion.** For `n ≠ 0`, the action comparison
`A[t]/(tⁿ - f) ⊗[A] A[t]/(tⁿ - f) → A[h]/(hⁿ - 1) ⊗[A] A[t]/(tⁿ - f)` is injective if and only if
`n = 1` or multiplication by `f` on `A` is injective. -/
theorem rootChartComparison_injective_iff :
    Function.Injective (rootChartComparison A f n) ↔ n = 1 ∨ IsLeftRegular f := by
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    have := Module.subsingleton A (rootChart A f n ⊗[A] rootChart A f n)
    exact iff_of_true (Function.injective_of_subsingleton _)
      (Or.inr fun _ _ _ => Subsingleton.elim _ _)
  | inr _ =>
    rw [← forall_pow_div_iff A f n (fun k hf => hf.pow k) isRegular_one.left]
    exact Module.Basis.injective_iff_forall_isLeftRegular_of_apply_eq_smul _ _
      (g := (rootChartComparison A f n).toLinearMap)
      (rootChartComparison_basis_tensorProduct A f n)

/-- **Sharp surjectivity criterion.** For `n ≠ 0`, the action comparison
`A[t]/(tⁿ - f) ⊗[A] A[t]/(tⁿ - f) → A[h]/(hⁿ - 1) ⊗[A] A[t]/(tⁿ - f)` is surjective if and only if
`n = 1` or `f` is a unit. -/
theorem rootChartComparison_surjective_iff :
    Function.Surjective (rootChartComparison A f n) ↔ n = 1 ∨ IsUnit f := by
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    have := Module.subsingleton A (rootChart A 1 n ⊗[A] rootChart A f n)
    exact iff_of_true (Function.surjective_to_subsingleton _) (Or.inr (isUnit_of_subsingleton f))
  | inr _ =>
    rw [← forall_pow_div_iff A f n (fun k hf => hf.pow k) isUnit_one]
    exact Module.Basis.surjective_iff_forall_isUnit_of_apply_eq_smul _ _
      (g := (rootChartComparison A f n).toLinearMap)
      (rootChartComparison_basis_tensorProduct A f n)

/-- **Sharp bijectivity criterion.** For `n ≠ 0`, the action comparison
`A[t]/(tⁿ - f) ⊗[A] A[t]/(tⁿ - f) → A[h]/(hⁿ - 1) ⊗[A] A[t]/(tⁿ - f)` is bijective if and only if
`n = 1` or `f` is a unit; invertibility of `n` in `A` is not needed. -/
theorem rootChartComparison_bijective_iff :
    Function.Bijective (rootChartComparison A f n) ↔ n = 1 ∨ IsUnit f := by
  rw [Function.Bijective, rootChartComparison_injective_iff, rootChartComparison_surjective_iff]
  exact ⟨And.right, fun h => ⟨h.imp_right IsUnit.isRegular |>.imp_right IsRegular.left, h⟩⟩

end Criteria

end TauCeti
