/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic

/-!
# Cofree lifts into tensor words

For modules `M` and `N`, a linear map `F : M ⊗ Tᶜ(A) → N` has a cofree lift
`M ⊗ Tᶜ(A) → N ⊗ Tᶜ(A)`, a morphism of cofree `Tᶜ(A)`-comodules.  On a pure word it applies `F` to
every prefix and retains the corresponding suffix.  Consequently, when `N = M` and `F` vanishes on
the empty word, the cofree lift strictly shortens words, so it is locally nilpotent.

## Main results

* `TauCeti.TensorWords.cofreeLift_tmul_of_tprod`: the cofree lift of a map, expanded over the cuts
  of a pure word.
* `TauCeti.TensorWords.exists_pow_apply_eq_zero_of_forall_tmul_of_tprod`: an endomorphism of
  `M ⊗ Tᶜ(A)` is locally nilpotent once each pure word is killed by a power of it.
* `TauCeti.TensorWords.exists_pow_cofreeLift_apply_eq_zero`: the cofree lift of a map vanishing on
  the empty word is locally nilpotent.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uM uN

attribute [local instance] Comodule.cofree

namespace TensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {M : Type uM} {N : Type uN} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- On a pure word, the cofree lift of `F` applies `F` to every prefix and retains the
corresponding suffix. -/
theorem cofreeLift_tmul_of_tprod (F : (M ⊗[R] TensorWords R A) →ₗ[R] N) (n : ℕ) (x : M)
    (a : Fin n → A) :
    (Comodule.Hom.cofreeLift (C := TensorWords R A) F).toLinearMap
        (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) =
      ∑ k ∈ Finset.range (n + 1), F (x ⊗ₜ[R] subword R a 0 k) ⊗ₜ[R] subword R a k (n - k) := by
  rw [Comodule.Hom.cofreeLift_toLinearMap, LinearMap.comp_apply, Comodule.cofree_coact_tmul,
    comul_eq_deconcatenation, of_tprod_eq_subword, deconcatenation_subword]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.assoc_symm_tmul,
    LinearMap.rTensor_tmul, Nat.zero_add]

/-- **Local nilpotence from pure words.**  An endomorphism of `M ⊗ Tᶜ(A)` is locally nilpotent as
soon as some power of it kills each pure word `x ⊗ a₀ ⊗ ⋯ ⊗ aₙ₋₁`. -/
theorem exists_pow_apply_eq_zero_of_forall_tmul_of_tprod
    (f : Module.End R (M ⊗[R] TensorWords R A))
    (hf : ∀ (n : ℕ) (x : M) (a : Fin n → A),
      ∃ k, (f ^ k) (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) = 0)
    (z : M ⊗[R] TensorWords R A) : ∃ k, (f ^ k) z = 0 := by
  -- The vectors killed by a power of `f` form the submodule `S`.
  let S := Module.End.maxGenEigenspace f 0
  have hmem (z) : z ∈ S ↔ ∃ k, (f ^ k) z = 0 := by
    simp only [S, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]
  have hS : ∀ z, z ∈ S := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => exact S.add_mem hz hz'
    | tmul x w =>
      have h : S.mkQ ∘ₗ TensorProduct.mk R M (TensorWords R A) x = 0 :=
        TensorWords.linearMap_ext R A fun n a ↦ by
          rw [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.zero_apply,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
          exact hf n x a
      have hw := LinearMap.congr_fun h w
      rwa [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.zero_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw
  exact (hmem z).1 (hS z)

/-- On a pure word of length `n`, the cofree lift of a map vanishing on the empty word only
produces shorter words, so by strong induction its `(n + 1)`-st power kills the word. -/
private theorem pow_succ_cofreeLift_tmul_of_tprod (ψ : (M ⊗[R] TensorWords R A) →ₗ[R] M)
    (hψ : ∀ x : M, ψ (x ⊗ₜ[R] (1 : TensorWords R A)) = 0) (n : ℕ) (x : M) (a : Fin n → A) :
    ((Comodule.Hom.cofreeLift (C := TensorWords R A) ψ).toLinearMap ^ (n + 1))
      (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) = 0 := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rw [pow_succ, mul_apply_eq_comp, cofreeLift_tmul_of_tprod,
      Finset.sum_range_succ', subword_length_zero R a (Nat.zero_le n), hψ,
      TensorProduct.zero_tmul, add_zero, map_sum]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk : k < n := Finset.mem_range.1 hk
    have hcut : k + 1 + (n - (k + 1)) ≤ n := by omega
    rw [subword_eq_of_tprod R a hcut]
    exact Module.End.pow_map_zero_of_le (k := n - (k + 1) + 1) (by omega)
      (ih (n - (k + 1)) (by omega) _ _)

/-- **Local nilpotence of cofree lifts.**  The cofree lift `M ⊗ Tᶜ(A) ⟶ M ⊗ Tᶜ(A)` of a linear
map `ψ` vanishing on the empty word is locally nilpotent: it strictly shortens the word. -/
theorem exists_pow_cofreeLift_apply_eq_zero (ψ : (M ⊗[R] TensorWords R A) →ₗ[R] M)
    (hψ : ∀ x : M, ψ (x ⊗ₜ[R] (1 : TensorWords R A)) = 0) (z : M ⊗[R] TensorWords R A) :
    ∃ n, ((Comodule.Hom.cofreeLift (C := TensorWords R A) ψ).toLinearMap ^ n) z = 0 :=
  exists_pow_apply_eq_zero_of_forall_tmul_of_tprod _
    (fun n x a ↦ ⟨n + 1, pow_succ_cofreeLift_tmul_of_tprod ψ hψ n x a⟩) z

end TensorWords

end TauCeti
