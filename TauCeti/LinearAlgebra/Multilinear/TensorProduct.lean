/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.Multilinear.Span

/-!
# Multilinear maps of tensor product arguments

For multilinear maps `μ : Aⁿ → P` and `ν : Bⁿ → Q`, there is a unique multilinear map
`(A ⊗ B)ⁿ → P ⊗ Q` sending `(a₁ ⊗ b₁, …, aₙ ⊗ bₙ)` to `μ (a₁, …, aₙ) ⊗ ν (b₁, …, bₙ)`
(`MultilinearMap.tensorMap`, `MultilinearMap.tensorMap_apply_tmul`). It is constructed by
induction on `n`, separating the first argument with `MultilinearMap.curryLeft`: a linear map out
of `A ⊗ B` is determined by a bilinear map on `A × B`. The construction is bilinear in `μ` and
`ν` (`MultilinearMap.tensorMapₗ`).

Uniqueness is the statement that a multilinear map whose arguments lie in `A ⊗ B` is determined
by its values when every argument is a pure tensor (`MultilinearMap.ext_tmul`), since the pure
tensors span `A ⊗ B`. This reduces identities between multilinear expressions in tensor product
arguments to the case of pure tensors.

## Main definitions

* `MultilinearMap.tensorMapₗ`: the bilinear map `(μ, ν) ↦ ((aᵢ ⊗ bᵢ)ᵢ ↦ μ a ⊗ ν b)`.
* `MultilinearMap.tensorMap`: its value at `μ` and `ν`.

## Main results

* `MultilinearMap.tensorMap_apply_tmul`: the value of `tensorMap μ ν` on pure tensors.
* `MultilinearMap.tensorMap_apply_eq_zero`: `tensorMap μ ν` vanishes when one of its arguments is
  a pure tensor `u ⊗ v` such that `μ` vanishes whenever the same argument is `u`.
* `MultilinearMap.ext_tmul`: multilinear maps of tensor product arguments agreeing on pure tensors
  are equal.
-/

public section

open scoped TensorProduct

namespace MultilinearMap

section TensorMap

variable {R A B P Q : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B]
  [Module R B] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- The bilinear map sending multilinear maps `μ : Aⁿ → P` and `ν : Bⁿ → Q` to the multilinear map
`(A ⊗ B)ⁿ → P ⊗ Q` with `(a₁ ⊗ b₁, …, aₙ ⊗ bₙ) ↦ μ a ⊗ ν b`
(`MultilinearMap.tensorMap_apply_tmul`). For `n + 1` arguments it separates the first one, on
which it is the linear map out of `A ⊗ B` of the bilinear map
`(a, b) ↦ tensorMapₗ n (μ.curryLeft a) (ν.curryLeft b)`. -/
noncomputable def tensorMapₗ : (n : ℕ) →
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A) P →ₗ[R]
      MultilinearMap (RingHom.id R) (fun _ : Fin n => B) Q →ₗ[R]
        MultilinearMap (RingHom.id R) (fun _ : Fin n => A ⊗[R] B) (P ⊗[R] Q)
  | 0 => LinearMap.mk₂ R (fun μ ν => constOfIsEmpty (RingHom.id R) _ (μ 0 ⊗ₜ ν 0))
      (fun _ _ _ => by ext; simp [TensorProduct.add_tmul])
      (fun _ _ _ => by ext; simp [TensorProduct.smul_tmul'])
      (fun _ _ _ => by ext; simp [TensorProduct.tmul_add])
      (fun _ _ _ => by ext; simp [TensorProduct.tmul_smul])
  -- In the bilinearity proofs, `curryLeft` is additive and homogeneous by definition (it is the
  -- linear equivalence `multilinearCurryLeftEquiv`), and a linear map out of `A ⊗ B` is
  -- determined by its values on pure tensors (`TensorProduct.ext'`).
  | n + 1 => LinearMap.mk₂ R
      (fun μ ν => LinearMap.uncurryLeft
        (TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ.curryLeft ν.curryLeft)))
      (fun μ μ' ν => by
        rw [show TensorProduct.lift ((tensorMapₗ n).compl₁₂ (μ + μ').curryLeft ν.curryLeft) =
            TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ.curryLeft ν.curryLeft) +
              TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ'.curryLeft ν.curryLeft) from
          TensorProduct.ext' fun a b => by
            simp only [LinearMap.add_apply, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
            rw [show (μ + μ').curryLeft a = μ.curryLeft a + μ'.curryLeft a from rfl, map_add,
              LinearMap.add_apply]]
        rfl)
      (fun c μ ν => by
        rw [show TensorProduct.lift ((tensorMapₗ n).compl₁₂ (c • μ).curryLeft ν.curryLeft) =
            c • TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ.curryLeft ν.curryLeft) from
          TensorProduct.ext' fun a b => by
            simp only [LinearMap.smul_apply, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
            rw [show (c • μ).curryLeft a = c • μ.curryLeft a from rfl, map_smul,
              LinearMap.smul_apply]]
        rfl)
      (fun μ ν ν' => by
        rw [show TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ.curryLeft (ν + ν').curryLeft) =
            TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ.curryLeft ν.curryLeft) +
              TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ.curryLeft ν'.curryLeft) from
          TensorProduct.ext' fun a b => by
            simp only [LinearMap.add_apply, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
            rw [show (ν + ν').curryLeft b = ν.curryLeft b + ν'.curryLeft b from rfl, map_add]]
        rfl)
      (fun c μ ν => by
        rw [show TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ.curryLeft (c • ν).curryLeft) =
            c • TensorProduct.lift ((tensorMapₗ n).compl₁₂ μ.curryLeft ν.curryLeft) from
          TensorProduct.ext' fun a b => by
            simp only [LinearMap.smul_apply, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
            rw [show (c • ν).curryLeft b = c • ν.curryLeft b from rfl, map_smul]]
        rfl)

/-- The multilinear map `(A ⊗ B)ⁿ → P ⊗ Q` of multilinear maps `μ : Aⁿ → P` and `ν : Bⁿ → Q`,
sending `(a₁ ⊗ b₁, …, aₙ ⊗ bₙ)` to `μ a ⊗ ν b` (`MultilinearMap.tensorMap_apply_tmul`); it is the
only such multilinear map (`MultilinearMap.ext_tmul`). -/
noncomputable def tensorMap {n : ℕ} (μ : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) P)
    (ν : MultilinearMap (RingHom.id R) (fun _ : Fin n => B) Q) :
    MultilinearMap (RingHom.id R) (fun _ : Fin n => A ⊗[R] B) (P ⊗[R] Q) :=
  tensorMapₗ n μ ν

theorem tensorMap_def {n : ℕ} (μ : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) P)
    (ν : MultilinearMap (RingHom.id R) (fun _ : Fin n => B) Q) :
    tensorMap μ ν = tensorMapₗ n μ ν :=
  (rfl)

/-- **The tensor map on pure tensors**: `tensorMap μ ν (a₁ ⊗ b₁, …, aₙ ⊗ bₙ) = μ a ⊗ ν b`. -/
@[simp]
theorem tensorMap_apply_tmul {n : ℕ} (μ : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) P)
    (ν : MultilinearMap (RingHom.id R) (fun _ : Fin n => B) Q) (a : Fin n → A) (b : Fin n → B) :
    tensorMap μ ν (fun i => a i ⊗ₜ[R] b i) = μ a ⊗ₜ[R] ν b := by
  induction n with
  | zero =>
    rw [tensorMap_def, tensorMapₗ, LinearMap.mk₂_apply, constOfIsEmpty_apply,
      Function.const_apply, Subsingleton.elim a 0, Subsingleton.elim b 0]
  | succ n ih =>
    rw [tensorMap_def, tensorMapₗ, LinearMap.mk₂_apply, LinearMap.uncurryLeft_apply,
      TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, ← tensorMap_def]
    -- The tail of a tuple of pure tensors is the tuple of pure tensors of the tails.
    rw [show Fin.tail (fun i => a i ⊗ₜ[R] b i) = fun i => Fin.tail a i ⊗ₜ[R] Fin.tail b i from rfl,
      ih, curryLeft_apply, curryLeft_apply, Fin.cons_self_tail, Fin.cons_self_tail]

/-- The tensor map vanishes when its first input does. -/
@[simp]
theorem tensorMap_zero_left {n : ℕ} (ν : MultilinearMap (RingHom.id R) (fun _ : Fin n => B) Q) :
    tensorMap (0 : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) P) ν = 0 := by
  rw [tensorMap_def, LinearMap.map_zero₂]

/-- **The tensor map vanishes along a factor on which `μ` vanishes.** If `μ` vanishes whenever
its argument `i` is `u`, then `tensorMap μ ν` vanishes whenever its argument `i` is a pure tensor
`u ⊗ v`, whatever its other arguments. -/
theorem tensorMap_apply_eq_zero {n : ℕ}
    {μ : MultilinearMap (RingHom.id R) (fun _ : Fin n => A) P}
    (ν : MultilinearMap (RingHom.id R) (fun _ : Fin n => B) Q) {i : Fin n} {u : A}
    (hμ : ∀ a : Fin n → A, a i = u → μ a = 0) {v : B} {x : Fin n → A ⊗[R] B}
    (hx : x i = u ⊗ₜ[R] v) : tensorMap μ ν x = 0 := by
  classical
  let s : Fin n → Set (A ⊗[R] B) := fun j =>
    if j = i then {u ⊗ₜ[R] v} else {t | ∃ a b, a ⊗ₜ[R] b = t}
  have hm := map_mem_span_image_pi (tensorMap μ ν) s (m := x) fun j => by
    by_cases hj : j = i
    · subst hj
      exact Submodule.subset_span (by simp [s, hx])
    · simp only [s, hj, ite_false, TensorProduct.span_tmul_eq_top, Submodule.mem_top]
  have hzero : tensorMap μ ν '' Set.univ.pi s ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    have hpure : ∀ j, ∃ a b, y j = a ⊗ₜ[R] b ∧ (j = i → a = u) := fun j => by
      by_cases hj : j = i
      · subst hj
        have : y j = u ⊗ₜ[R] v := by simpa [s] using hy j (Set.mem_univ j)
        exact ⟨u, v, this, fun _ => rfl⟩
      · obtain ⟨a, b, hab⟩ : ∃ a b, a ⊗ₜ[R] b = y j := by
          simpa [s, hj] using hy j (Set.mem_univ j)
        exact ⟨a, b, hab.symm, fun h => (hj h).elim⟩
    choose a b hab hai using hpure
    obtain rfl : y = fun j => a j ⊗ₜ[R] b j := funext fun j => hab j
    rw [tensorMap_apply_tmul, hμ a (hai i rfl), TensorProduct.zero_tmul, Set.mem_singleton_iff]
  have := Submodule.span_mono hzero hm
  rwa [Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this

end TensorMap

section Ext

variable {R A B N ι : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup N] [Module R N] [Finite ι]

/-- **Multilinear maps of tensor product arguments are determined by their values on pure
tensors**, since the pure tensors span `A ⊗ B`. -/
theorem ext_tmul {f g : MultilinearMap (RingHom.id R) (fun _ : ι => A ⊗[R] B) N}
    (h : ∀ (a : ι → A) (b : ι → B), f (fun i => a i ⊗ₜ[R] b i) = g (fun i => a i ⊗ₜ[R] b i)) :
    f = g := by
  rw [← sub_eq_zero]
  ext m
  have hm := map_mem_span_image_pi (f - g) (fun _ => {t | ∃ a b, a ⊗ₜ[R] b = t})
    (m := m) fun i => by rw [TensorProduct.span_tmul_eq_top]; trivial
  have hzero : (f - g) '' Set.univ.pi (fun _ => {t : A ⊗[R] B | ∃ a b, a ⊗ₜ[R] b = t}) ⊆ {0} := by
    rintro _ ⟨m', hm', rfl⟩
    choose a b hab using fun i => hm' i (Set.mem_univ i)
    obtain rfl : m' = fun i => a i ⊗ₜ[R] b i := funext fun i => (hab i).symm
    rw [Set.mem_singleton_iff, sub_apply, h, sub_self]
  have := Submodule.span_mono hzero hm
  rwa [Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this

end Ext

end MultilinearMap
