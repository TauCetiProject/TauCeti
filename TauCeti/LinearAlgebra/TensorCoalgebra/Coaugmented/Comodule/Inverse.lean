/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic
public import TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# Invertibility of maps of cofree tensor comodules

A map of cofree comodules over the tensor coalgebra is invertible if its component on the
empty word is invertible. After correcting by that component, the map differs from the identity
by a locally nilpotent endomorphism: every application consumes at least one algebra input.
This gives inverses without a global word-length bound or a completeness hypothesis.

The argument is the comodule counterpart of the length-triangular inversion in
`TauCeti.LinearAlgebra.TensorCoalgebra.CoalgHom`. It supplies the bar-map inversion used for
morphisms of A-infinity modules.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 4.
-/

public section

open scoped TensorProduct

namespace TauCeti.TensorWords

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN}

attribute [local instance] Comodule.cofree

section Expansion

variable [CommSemiring R] [AddCommMonoid A] [Module R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The cofree lift sums over cuts: the prefix enters the Taylor map and the suffix remains. -/
theorem cofreeLift_tmul_subword (φ : M ⊗[R] TensorWords R A →ₗ[R] N)
    (m : M) {n : ℕ} (x : Fin n → A) (a b : ℕ) :
    (Comodule.Hom.cofreeLift (C := TensorWords R A) φ)
        (m ⊗ₜ[R] subword R x a b) =
      ∑ c ∈ Finset.range (b + 1),
        φ (m ⊗ₜ[R] subword R x a c) ⊗ₜ[R] subword R x (a + c) (b - c) := by
  simp only [Comodule.Hom.cofreeLift_apply, Comodule.cofree_coact_tmul,
    comul_eq_deconcatenation, deconcatenation_subword, TensorProduct.tmul_sum, map_sum,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul]

/-- A cofree lift with zero empty-word component is locally nilpotent. Each application
strictly shortens the surviving word; no common exponent on all words is required. -/
theorem exists_pow_cofreeLift_apply_eq_zero
    (φ : M ⊗[R] TensorWords R A →ₗ[R] M)
    (hφ : ∀ m, φ (m ⊗ₜ[R] (1 : TensorWords R A)) = 0)
    (z : M ⊗[R] TensorWords R A) :
    ∃ k, ((Comodule.Hom.cofreeLift (C := TensorWords R A) φ).toLinearMap ^ k) z = 0 := by
  let F : Module.End R (M ⊗[R] TensorWords R A) :=
    (Comodule.Hom.cofreeLift (C := TensorWords R A) φ).toLinearMap
  let S := F.nilpotentSubmodule
  -- The empty prefix contributes zero, and all other cuts have a shorter suffix.
  have hword : ∀ b (m : M) {n : ℕ} (x : Fin n → A) (a : ℕ),
      a + b ≤ n → m ⊗ₜ[R] subword R x a b ∈ S := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro m n x a hab
      apply (F.apply_mem_nilpotentSubmodule_iff _).1
      dsimp only [F]
      rw [Comodule.Hom.coe_toLinearMap, cofreeLift_tmul_subword]
      refine S.sum_mem fun c hc ↦ ?_
      rcases Nat.eq_zero_or_pos c with rfl | hcpos
      · rw [subword_length_zero R x (by omega), hφ, TensorProduct.zero_tmul]
        exact S.zero_mem
      · have hc' := Finset.mem_range.1 hc
        exact ih (b - c) (by omega) _ x (a + c) (by omega)
  -- Pure tensors of words span the entire cofree comodule.
  have hall (m : M) : ⊤ ≤ S.comap (TensorProduct.mk R M (TensorWords R A) m) := by
    rw [← iSup_range_of R A]
    refine iSup_le fun n ↦ ?_
    rintro _ ⟨w, rfl⟩
    have hn : ⊤ ≤ S.comap (TensorProduct.mk R M (TensorWords R A) m ∘ₗ of R A n) := by
      rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have hx := hword n m x 0 (by omega)
      rw [← of_tprod_eq_subword] at hx
      exact hx
    exact hn (Submodule.mem_top : w ∈ (⊤ : Submodule R (TensorPower R n A)))
  have hz : z ∈ S := by
    induction z using TensorProduct.inductionOn with
    | tmul m w => exact hall m Submodule.mem_top
    | add x y hx hy => exact S.add_mem hx hy
  exact (F.mem_nilpotentSubmodule_iff z).1 hz

end Expansion

variable [CommSemiring R] [AddCommGroup A] [Module R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A cofree-comodule endomorphism which is the identity on empty words is bijective. -/
theorem bijective_of_tmul_one_eq_self
    (F : Comodule.Hom R (TensorWords R A)
      (M ⊗[R] TensorWords R A) (M ⊗[R] TensorWords R A))
    (hF : ∀ m, F (m ⊗ₜ[R] (1 : TensorWords R A)) = m ⊗ₜ[R] 1) :
    Function.Bijective F := by
  let π := (TensorProduct.rid R M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M
  let φ := π ∘ₗ F.toLinearMap - π
  have hφ : ∀ m, φ (m ⊗ₜ[R] (1 : TensorWords R A)) = 0 := by
    intro m
    simp only [φ, LinearMap.sub_apply, LinearMap.comp_apply,
      Comodule.Hom.coe_toLinearMap, hF, sub_self]
  have hlin : (Comodule.Hom.cofreeLift (C := TensorWords R A) φ).toLinearMap =
      F.toLinearMap - LinearMap.id := by
    have hF' := congrArg Comodule.Hom.toLinearMap
      (Comodule.Hom.cofreeLift_rid_comp_lTensor_counit_comp F)
    have hid := Comodule.rTensor_rid_comp_lTensor_counit_comp_cofreeCoact
      (R := R) (C := TensorWords R A) (M := M)
    simp only [Comodule.Hom.cofreeLift_toLinearMap] at hF'
    dsimp only [φ]
    rw [Comodule.Hom.cofreeLift_toLinearMap, LinearMap.rTensor_sub, LinearMap.sub_comp]
    exact congrArg₂ (· - ·) hF' hid
  have hunit := Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero
    (F.toLinearMap - LinearMap.id) (fun z ↦ by
      rw [← hlin]
      exact exists_pow_cofreeLift_apply_eq_zero φ hφ z)
  simpa only [Module.End.one_eq_id, add_sub_cancel, Comodule.Hom.coe_toLinearMap] using
    (Module.End.isUnit_iff _).1 hunit

/-- A cofree-comodule map is bijective if its empty-word component is bijective. -/
theorem bijective_of_tmul_one_eq
    (F : Comodule.Hom R (TensorWords R A)
      (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A))
    (f : M →ₗ[R] N) (hf : Function.Bijective f)
    (hF : ∀ m, F (m ⊗ₜ[R] (1 : TensorWords R A)) = f m ⊗ₜ[R] 1) :
    Function.Bijective F := by
  let e := LinearEquiv.ofBijective f hf
  have hG : Function.Bijective ((Comodule.Hom.cofreeMap (C := TensorWords R A)
      e.symm.toLinearMap).comp F) :=
    bijective_of_tmul_one_eq_self _ fun m ↦ by
      simp only [Comodule.Hom.comp_apply, hF, Comodule.Hom.cofreeMap_apply,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
      exact congrArg (fun x ↦ x ⊗ₜ[R] (1 : TensorWords R A)) (e.symm_apply_apply m)
  have he : Function.Bijective (e.symm.toLinearMap.rTensor (TensorWords R A)) :=
    (e.symm.rTensor (TensorWords R A)).bijective
  exact (Function.Bijective.of_comp_iff' he _).1 hG

end TauCeti.TensorWords
