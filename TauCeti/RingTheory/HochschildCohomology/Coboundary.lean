/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.BilinearMap
public import TauCeti.LinearAlgebra.Multilinear.Curry
public import TauCeti.RingTheory.CyclicCohomology.Cochain
public import TauCeti.RingTheory.Derivation.Bimodule
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.AlternatingSum
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The Hochschild coboundary with coefficients in a bimodule

Let `A` be an algebra over a commutative semiring `R` and `M` an `A`-bimodule, written as a left
`A`-module and a left `Aᵐᵒᵖ`-module whose actions commute, the right action of `x` being
`op x • m`. A Hochschild `n`-cochain of `A` with coefficients in `M` is an `R`-multilinear map
`ψ : Aⁿ → M`; the `0`-cochains are the constant maps, i.e. the elements of `M`. This file
constructs the Hochschild coboundary `δ : Cⁿ(A, M) → Cⁿ⁺¹(A, M)`,

`(δψ)(a₀, …, aₙ) = a₀ ψ(a₁, …, aₙ) + ∑_{j < n} (-1)ʲ⁺¹ ψ(a₀, …, aⱼaⱼ₊₁, …, aₙ)`
`  + (-1)ⁿ⁺¹ ψ(a₀, …, aₙ₋₁) aₙ`,

as the alternating sum of its cofaces `∂ᵢ`, proves the cosimplicial identities between the
cofaces, and deduces `δ ∘ δ = 0`. The degree-zero cocycles are the central elements of `M`, the
coboundary of `m : M` is the inner derivation `a ↦ a m - m a`, and the degree-one cocycles are the
derivations `A → M`.

The degree of a cochain here is its number of arguments. The scalar cochains of
`TauCeti.RingTheory.CyclicCohomology.Cochain`, whose coboundary `b` closes with the cyclic face
`(aₙ₊₁ a₀, a₁, …, aₙ)`, are instead indexed by one less than their number of arguments; they are
the cochains with coefficients in the dual bimodule, see
`TauCeti.RingTheory.HochschildCohomology.Dual`.

## Main definitions

* `TauCeti.hochschildBimoduleCoface`: the cofaces `∂ᵢ`.
* `TauCeti.hochschildBimoduleCoboundary`: the Hochschild coboundary `δ = ∑ᵢ (-1)ⁱ ∂ᵢ`.

## Main results

* `TauCeti.hochschildBimoduleCoface_hochschildBimoduleCoface`: the cosimplicial identities
  `∂_{j+1} ∘ ∂ᵢ = ∂ᵢ ∘ ∂_j` for `i ≤ j`.
* `TauCeti.hochschildBimoduleCoboundary_hochschildBimoduleCoboundary`: `δ (δ ψ) = 0`.
* `TauCeti.hochschildBimoduleCoboundary_apply_eq_add_sum_add`: the explicit formula for `δ`.
* `TauCeti.hochschildBimoduleCoboundary_constOfIsEmpty_eq_zero_iff`: the degree-zero cocycles
  are the central elements.
* `TauCeti.hochschildBimoduleCoboundary_ofSubsingleton_eq_zero_iff`: the degree-one cocycles
  are the derivations.
* `TauCeti.BimoduleDerivation.hochschildBimoduleCoboundary_ofSubsingleton_eq_zero`: a
  `TauCeti.BimoduleDerivation` is a degree-one cocycle.

## References

* G. Hochschild, *On the cohomology groups of an associative algebra*, Ann. of Math. 46 (1945).
* J.-L. Loday, *Cyclic Homology*, §1.5.
-/

public section

open MulOpposite

namespace TauCeti

section Coface

variable (R A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]
  {n : ℕ}

/-- The zeroth coface `(∂₀ψ)(a₀, …, aₙ) = a₀ • ψ(a₁, …, aₙ)`. -/
private def leftCoface :
    MultilinearMap R (fun _ : Fin n ↦ A) M →ₗ[R] MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M :=
  (multilinearCurryFirstEquiv R (fun _ : Fin (n + 1) ↦ A) M).symm.toLinearMap ∘ₗ
    LinearMap.compMultilinearMapₗ R (Algebra.lsmul R R M).toLinearMap.flip

/-- The last coface `(∂ₙ₊₁ψ)(a₀, …, aₙ) = ψ(a₀, …, aₙ₋₁) • aₙ`. -/
private def rightCoface :
    MultilinearMap R (fun _ : Fin n ↦ A) M →ₗ[R] MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M :=
  (multilinearCurryRightEquiv R (fun _ : Fin (n + 1) ↦ A) M).symm.toLinearMap ∘ₗ
    LinearMap.compMultilinearMapₗ R
      ((Algebra.lsmul R R M).toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap).flip

/-- The inner cofaces, precomposition with the multiplication of two adjacent entries. -/
private def innerCoface : ∀ {n : ℕ}, Fin n →
    MultilinearMap R (fun _ : Fin n ↦ A) M →ₗ[R] MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M
  | 0, j => j.elim0
  | _ + 1, j => hochschildCoface R A M j.castSucc

/-- The `i`-th coface of a cochain with coefficients in a bimodule, sending a multilinear map
`ψ` in `n` arguments to a multilinear map in `n + 1` arguments: the zeroth coface multiplies by
the first entry on the left, the last coface multiplies by the last entry on the right, and the
others multiply two adjacent entries. -/
def hochschildBimoduleCoface (i : Fin (n + 2)) :
    MultilinearMap R (fun _ : Fin n ↦ A) M →ₗ[R] MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M :=
  Fin.cases (leftCoface R A M) (Fin.lastCases (rightCoface R A M) (innerCoface R A M)) i

variable {R A M}

/-- The zeroth coface multiplies by the first entry on the left. -/
@[simp]
theorem hochschildBimoduleCoface_zero_apply (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M)
    (a : Fin (n + 1) → A) :
    hochschildBimoduleCoface R A M 0 ψ a = a 0 • ψ (Fin.tail a) := by
  simp [hochschildBimoduleCoface, leftCoface]

/-- The last coface multiplies by the last entry on the right. -/
@[simp]
theorem hochschildBimoduleCoface_last_apply (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M)
    (a : Fin (n + 1) → A) :
    hochschildBimoduleCoface R A M (Fin.last (n + 1)) ψ a =
      op (a (Fin.last n)) • ψ (Fin.init a) := by
  rw [hochschildBimoduleCoface, ← Fin.succ_last, Fin.cases_succ, Fin.lastCases_last]
  simp [rightCoface, multilinearCurryRightEquiv]

/-- The inner cofaces multiply two adjacent entries. -/
@[simp]
theorem hochschildBimoduleCoface_castSucc_succ_apply (j : Fin n)
    (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoface R A M j.castSucc.succ ψ a =
      ψ (Fin.contractNth j.castSucc (· * ·) a) := by
  cases n with
  | zero => exact j.elim0
  | succ n => simp [hochschildBimoduleCoface, innerCoface]

/-- The inner cofaces multiply two adjacent entries, with the index written as `j.succ.castSucc`
rather than `j.castSucc.succ`. -/
theorem hochschildBimoduleCoface_succ_castSucc_apply (j : Fin n)
    (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoface R A M j.succ.castSucc ψ a =
      ψ (Fin.contractNth j.castSucc (· * ·) a) := by
  rw [← Fin.succ_castSucc, hochschildBimoduleCoface_castSucc_succ_apply]

/-- The cosimplicial identity `∂_{j+1} ∘ ∂ᵢ = ∂ᵢ ∘ ∂_j` for `i ≤ j`. -/
theorem hochschildBimoduleCoface_hochschildBimoduleCoface [SMulCommClass A Aᵐᵒᵖ M]
    {i j : Fin (n + 2)} (hij : i ≤ j) (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) :
    hochschildBimoduleCoface R A M j.succ (hochschildBimoduleCoface R A M i ψ) =
      hochschildBimoduleCoface R A M i.castSucc (hochschildBimoduleCoface R A M j ψ) := by
  -- Each of `i` and `j` is the left coface `0`, an inner coface `k.castSucc.succ` or the right
  -- coface `Fin.last`; the six cases with `i ≤ j` reduce to identities between tuples, after
  -- rewriting each inner index into the shape `k.castSucc.succ` of
  -- `hochschildBimoduleCoface_castSucc_succ_apply`.
  ext a
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero =>
      -- `(a₀ a₁) • ψ(a₂, …) = a₀ • a₁ • ψ(a₂, …)`
      rw [← Fin.castSucc_zero (n := n + 1), hochschildBimoduleCoface_castSucc_succ_apply]
      simp only [Fin.castSucc_zero, hochschildBimoduleCoface_zero_apply]
      rw [← Fin.cons_self_tail a, Fin.contractNth_zero_cons]
      simp only [Fin.cons_zero, Fin.tail_cons, mul_smul]
    | succ j =>
      induction j using Fin.lastCases with
      | last =>
        -- the left and right actions commute
        simp only [Fin.succ_last, hochschildBimoduleCoface_last_apply,
          Fin.castSucc_zero, hochschildBimoduleCoface_zero_apply]
        rw [Fin.tail_init_eq_init_tail]
        exact (smul_comm _ _ _).symm
      | cast j =>
        -- an inner contraction commutes with dropping the first entry
        rw [Fin.succ_castSucc, hochschildBimoduleCoface_castSucc_succ_apply]
        simp only [Fin.castSucc_zero, hochschildBimoduleCoface_zero_apply,
          hochschildBimoduleCoface_succ_castSucc_apply]
        rw [Fin.contractNth_apply_of_lt _ _ _ _ (Nat.succ_pos _), Fin.castSucc_zero,
          ← Fin.succ_castSucc, Fin.tail_contractNth_succ]
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      -- `ψ(…) • (aₙ aₙ₊₁) = (ψ(…) • aₙ) • aₙ₊₁`
      rw [Fin.succ_last] at hij ⊢
      obtain rfl : j = Fin.last (n + 1) := le_antisymm (Fin.le_last _) hij
      rw [Fin.succ_last, show (Fin.last (n + 1)).castSucc = (Fin.last n).castSucc.succ by
        rw [Fin.succ_castSucc, Fin.succ_last], hochschildBimoduleCoface_castSucc_succ_apply]
      simp only [hochschildBimoduleCoface_last_apply]
      rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, Fin.init_contractNth_castSucc_last, op_mul,
        mul_smul, Fin.succ_last, Fin.init_def]
    | cast i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (not_le.2 (Fin.succ_pos _))
      | succ j =>
        induction j using Fin.lastCases with
        | last =>
          -- an inner contraction commutes with dropping the last entry
          rw [Fin.succ_last, Fin.succ_last, hochschildBimoduleCoface_succ_castSucc_apply]
          simp only [hochschildBimoduleCoface_last_apply,
            hochschildBimoduleCoface_castSucc_succ_apply]
          rw [Fin.contractNth_apply_of_gt _ _ _ _ i.2, Fin.init_contractNth_castSucc,
            Fin.succ_last]
        | cast j =>
          -- two inner contractions: the simplicial identity of `hochschildFace`
          rw [Fin.succ_castSucc j]
          simp only [hochschildBimoduleCoface_castSucc_succ_apply,
            hochschildBimoduleCoface_succ_castSucc_apply]
          cases n with
          | zero => exact i.elim0
          | succ n =>
            have h := hochschildFace_hochschildFace (i := i.castSucc) (j := j.castSucc)
              (by simpa using hij) a
            simp only [Fin.succ_castSucc, hochschildFace_castSucc] at h
            rw [h]

end Coface

section Coboundary

variable (R A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [AddCommGroup M]
  [Module R M] [Module A M] [Module Aᵐᵒᵖ M] [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M]

/-- The Hochschild coboundary `δ` on cochains with coefficients in a bimodule `M`, the alternating
sum `∑ᵢ (-1)ⁱ ∂ᵢ` of the cofaces. Explicitly
(`hochschildBimoduleCoboundary_apply_eq_add_sum_add`),
`(δψ)(a₀, …, aₙ) = a₀ ψ(a₁, …, aₙ) + ∑_{j < n} (-1)ʲ⁺¹ ψ(a₀, …, aⱼaⱼ₊₁, …, aₙ)
  + (-1)ⁿ⁺¹ ψ(a₀, …, aₙ₋₁) aₙ`. -/
def hochschildBimoduleCoboundary (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ A) M →ₗ[R] MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildBimoduleCoface R A M i

variable {R A M} {n : ℕ}

/-- The coboundary evaluates as the alternating sum of the cofaces. -/
@[simp]
theorem hochschildBimoduleCoboundary_apply (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M)
    (a : Fin (n + 1) → A) :
    hochschildBimoduleCoboundary R A M n ψ a =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • hochschildBimoduleCoface R A M i ψ a := by
  simp [hochschildBimoduleCoboundary]

/-- The Hochschild coboundary with coefficients in a bimodule, in explicit form. -/
theorem hochschildBimoduleCoboundary_apply_eq_add_sum_add
    (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) (a : Fin (n + 1) → A) :
    hochschildBimoduleCoboundary R A M n ψ a =
      a 0 • ψ (Fin.tail a) +
        ∑ j : Fin n, (-1 : ℤ) ^ ((j : ℕ) + 1) • ψ (Fin.contractNth j.castSucc (· * ·) a) +
          (-1 : ℤ) ^ (n + 1) • op (a (Fin.last n)) • ψ (Fin.init a) := by
  rw [hochschildBimoduleCoboundary_apply, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp [add_assoc]

/-- The Hochschild coboundary with coefficients in a bimodule squares to zero. -/
@[simp]
theorem hochschildBimoduleCoboundary_hochschildBimoduleCoboundary [SMulCommClass A Aᵐᵒᵖ M]
    (ψ : MultilinearMap R (fun _ : Fin n ↦ A) M) :
    hochschildBimoduleCoboundary R A M (n + 1) (hochschildBimoduleCoboundary R A M n ψ) = 0 := by
  ext a
  have h : hochschildBimoduleCoboundary R A M n ψ =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • hochschildBimoduleCoface R A M j ψ := by
    simp [hochschildBimoduleCoboundary]
  rw [hochschildBimoduleCoboundary_apply, zero_apply, h]
  simp only [map_sum, map_zsmul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply]
  exact sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
    (fun i j ↦ hochschildBimoduleCoface R A M i (hochschildBimoduleCoface R A M j ψ) a)
    fun i j hij ↦ by simp only [hochschildBimoduleCoface_hochschildBimoduleCoface hij]

/-- The Hochschild coboundary with coefficients in a bimodule squares to zero, as a composite of
linear maps. -/
theorem hochschildBimoduleCoboundary_comp_hochschildBimoduleCoboundary [SMulCommClass A Aᵐᵒᵖ M] :
    hochschildBimoduleCoboundary R A M (n + 1) ∘ₗ hochschildBimoduleCoboundary R A M n = 0 :=
  LinearMap.ext hochschildBimoduleCoboundary_hochschildBimoduleCoboundary

/-- The coboundary of the degree-zero cochain with value `m` is the inner derivation
`a ↦ a • m - m • a`. -/
theorem hochschildBimoduleCoboundary_constOfIsEmpty (m : M) (a : Fin 1 → A) :
    hochschildBimoduleCoboundary R A M 0 (MultilinearMap.constOfIsEmpty R _ m) a =
      a 0 • m - op (a 0) • m := by
  rw [hochschildBimoduleCoboundary_apply_eq_add_sum_add]
  simp [sub_eq_add_neg]

/-- A degree-zero cochain is a cocycle exactly when its value lies in the centre of the
bimodule. -/
theorem hochschildBimoduleCoboundary_constOfIsEmpty_eq_zero_iff (m : M) :
    hochschildBimoduleCoboundary R A M 0 (MultilinearMap.constOfIsEmpty R _ m) = 0 ↔
      ∀ x : A, x • m = op x • m := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · have hx := DFunLike.congr_fun h fun _ ↦ x
    rwa [hochschildBimoduleCoboundary_constOfIsEmpty, zero_apply,
      sub_eq_zero] at hx
  · ext a
    rw [hochschildBimoduleCoboundary_constOfIsEmpty, h, sub_self, zero_apply]

/-- The coboundary of a degree-one cochain `f`:
`(δf)(a₀, a₁) = a₀ • f a₁ - f (a₀ a₁) + f a₀ • a₁`. -/
theorem hochschildBimoduleCoboundary_ofSubsingleton (f : A →ₗ[R] M) (a : Fin 2 → A) :
    hochschildBimoduleCoboundary R A M 1 (MultilinearMap.ofSubsingleton R A M 0 f) a =
      a 0 • f (a 1) - f (a 0 * a 1) + op (a 1) • f (a 0) := by
  rw [hochschildBimoduleCoboundary_apply_eq_add_sum_add, Fin.sum_univ_one]
  simp only [MultilinearMap.ofSubsingleton_apply_apply, Fin.tail_def, Fin.init_def,
    Fin.castSucc_zero, Fin.contractNth_apply_of_eq (0 : Fin 2) (· * ·) a 0 rfl]
  simp [sub_eq_add_neg]

/-- A degree-one cochain is a cocycle exactly when it satisfies the Leibniz rule
`f (x y) = x • f y + f x • y`, i.e. when it is a derivation into the bimodule in the sense of
`TauCeti.BimoduleDerivation`. -/
theorem hochschildBimoduleCoboundary_ofSubsingleton_eq_zero_iff (f : A →ₗ[R] M) :
    hochschildBimoduleCoboundary R A M 1 (MultilinearMap.ofSubsingleton R A M 0 f) = 0 ↔
      ∀ x y : A, f (x * y) = x • f y + op y • f x := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ?_⟩
  · have hxy := DFunLike.congr_fun h ![x, y]
    rw [hochschildBimoduleCoboundary_ofSubsingleton, zero_apply] at hxy
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hxy
    rw [sub_add_eq_add_sub, sub_eq_zero] at hxy
    exact hxy.symm
  · ext a
    rw [hochschildBimoduleCoboundary_ofSubsingleton, h, zero_apply]
    abel

/-- A derivation into the bimodule is a degree-one Hochschild cocycle. -/
theorem BimoduleDerivation.hochschildBimoduleCoboundary_ofSubsingleton_eq_zero
    [SMulCommClass A Aᵐᵒᵖ M] (D : BimoduleDerivation R A M) :
    hochschildBimoduleCoboundary R A M 1 (MultilinearMap.ofSubsingleton R A M 0 D) = 0 :=
  (hochschildBimoduleCoboundary_ofSubsingleton_eq_zero_iff _).2 D.leibniz

end Coboundary

end TauCeti
