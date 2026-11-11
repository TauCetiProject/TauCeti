/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree
public import TauCeti.LinearAlgebra.End.LocallyNilpotent
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic

/-!
# Bijective morphisms of cofree comodules over tensor words

Let `Tᶜ(A)` be the coaugmented tensor coalgebra with deconcatenation.  A morphism of cofree right
comodules `F : M ⊗ Tᶜ(A) ⟶ N ⊗ Tᶜ(A)` is the cofree lift of its counit component `T`, so
`F (x ⊗ a₁ ⋯ aₙ) = ∑ᵢ T (x ⊗ a₁ ⋯ aᵢ) ⊗ aᵢ₊₁ ⋯ aₙ`.  The summand with the empty prefix is
`g x ⊗ a₁ ⋯ aₙ`, where `F (x ⊗ 1) = g x ⊗ 1`, and every other summand has a strictly shorter
word.  Thus `F` is `g ⊗ 1` up to a map lowering the length of words, and it is bijective as soon
as `g` is (`TauCeti.Comodule.Hom.bijective_of_apply_tmul_one`).

This is the conilpotence argument behind the invertibility of morphisms of `A∞` modules with
bijective linear part: the bar construction of a right `A∞` module is the cofree comodule
`sM ⊗ Tᶜ(sA)`.

## Main results

* `TauCeti.Comodule.Hom.bijective_of_apply_tmul_one`: a morphism of cofree `Tᶜ(A)`-comodules
  is bijective when its restriction to the empty word is.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* K. Lefèvre-Hasegawa, *Sur les A∞-catégories*, thèse de doctorat, Université Paris 7 (2003),
  Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]

attribute [local instance] Comodule.cofree

namespace TensorWords

variable (R A M) in
/-- The elements of `M ⊗ Tᶜ(A)` built from words of length less than `n`. -/
private noncomputable def cofreeFiltration (n : ℕ) : Submodule R (M ⊗[R] TensorWords R A) :=
  ⨆ k ∈ Finset.range n, LinearMap.range ((of R A k).lTensor M)

private theorem lTensor_of_mem_cofreeFiltration {k n : ℕ} (hk : k < n)
    (y : M ⊗[R] TensorPower R k A) :
    (of R A k).lTensor M y ∈ cofreeFiltration R A M n :=
  le_biSup (fun k ↦ LinearMap.range ((of R A k).lTensor M)) (Finset.mem_range.2 hk)
    (LinearMap.mem_range_self _ y)

private theorem cofreeFiltration_zero : cofreeFiltration R A M 0 = ⊥ := by
  simp [cofreeFiltration]

private theorem cofreeFiltration_mono {m n : ℕ} (h : m ≤ n) :
    cofreeFiltration R A M m ≤ cofreeFiltration R A M n :=
  biSup_mono fun _ hk ↦ Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le h)

private theorem tmul_subword_mem_cofreeFiltration {m : ℕ} (y : M) (a : Fin m → A) (b : ℕ)
    {l n : ℕ} (hl : l < n) : y ⊗ₜ[R] subword R a b l ∈ cofreeFiltration R A M n := by
  by_cases h : b + l ≤ m
  · rw [subword_eq_of_tprod R a h, ← LinearMap.lTensor_tmul]
    exact lTensor_of_mem_cofreeFiltration hl _
  · rw [subword_eq_zero_of_lt_add R a (by omega), TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

private theorem exists_mem_cofreeFiltration (z : M ⊗[R] TensorWords R A) :
    ∃ n, z ∈ cofreeFiltration R A M n := by
  induction z using TensorProduct.inductionOn with
  | tmul x c =>
    induction c using DirectSum.induction_on with
    | zero => exact ⟨0, by rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _⟩
    | of k w =>
      refine ⟨k + 1, ?_⟩
      have h := lTensor_of_mem_cofreeFiltration (M := M) (Nat.lt_succ_self k) (x ⊗ₜ w)
      rwa [LinearMap.lTensor_tmul, of_def, DirectSum.lof_eq_of] at h
    | add c c' hc hc' =>
      obtain ⟨n, hn⟩ := hc
      obtain ⟨n', hn'⟩ := hc'
      exact ⟨max n n', by
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ (cofreeFiltration_mono (le_max_left _ _) hn)
          (cofreeFiltration_mono (le_max_right _ _) hn')⟩
  | add z z' hz hz' =>
    obtain ⟨n, hn⟩ := hz
    obtain ⟨n', hn'⟩ := hz'
    exact ⟨max n n', Submodule.add_mem _ (cofreeFiltration_mono (le_max_left _ _) hn)
      (cofreeFiltration_mono (le_max_right _ _) hn')⟩

/-- A cofree comodule morphism expands a word by cutting it at every position. -/
private theorem apply_tmul_subword
    (F : Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A))
    (x : M) {m : ℕ} (a : Fin m → A) (b l : ℕ) :
    F (x ⊗ₜ subword R a b l) = ∑ c ∈ Finset.range (l + 1),
      ((TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ F.toLinearMap)
          (x ⊗ₜ subword R a b c) ⊗ₜ[R] subword R a (b + c) (l - c) := by
  conv_lhs => rw [← Comodule.Hom.cofreeLift_rid_comp_lTensor_counit_comp F]
  rw [Comodule.Hom.cofreeLift_apply, Comodule.cofree_coact_tmul, comul_eq_deconcatenation,
    deconcatenation_subword, TensorProduct.tmul_sum, map_sum, map_sum]
  simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul]

/-- A cofree comodule endomorphism fixing the empty words moves a word of length at most `n` by
words of length less than `n`. -/
private theorem sub_mem_cofreeFiltration
    {G : Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (M ⊗[R] TensorWords R A)}
    (hG : ∀ x : M, G (x ⊗ₜ 1) = x ⊗ₜ 1) {n : ℕ} {z : M ⊗[R] TensorWords R A}
    (hz : z ∈ cofreeFiltration R A M (n + 1)) : G z - z ∈ cofreeFiltration R A M n := by
  have key (x : M) {k : ℕ} (hk : k ≤ n) (a : Fin k → A) :
      G (x ⊗ₜ subword R a 0 k) - x ⊗ₜ subword R a 0 k ∈ cofreeFiltration R A M n := by
    have hx : ((TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ G.toLinearMap)
          (x ⊗ₜ 1) = x := by
      simp [hG]
    rw [apply_tmul_subword, Finset.sum_range_succ', subword_length_zero R a (Nat.zero_le k), hx,
      zero_add, Nat.sub_zero, add_sub_cancel_right]
    exact Submodule.sum_mem _ fun c hc ↦
      tmul_subword_mem_cofreeFiltration _ a _ (by rw [Finset.mem_range] at hc; omega)
  have h : cofreeFiltration R A M (n + 1) ≤
      (cofreeFiltration R A M n).comap (G.toLinearMap - LinearMap.id) := by
    refine iSup₂_le fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_comap]
    induction y using TensorProduct.inductionOn with
    | tmul x w =>
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        rw [TensorProduct.tmul_smul, map_smul, map_smul, LinearMap.lTensor_tmul,
          of_tprod_eq_subword, LinearMap.sub_apply, LinearMap.id_apply,
          Comodule.Hom.coe_toLinearMap]
        exact Submodule.smul_mem _ _ (key x (by omega) a)
      | add w w' hw hw' =>
        rw [TensorProduct.tmul_add, map_add, map_add]
        exact Submodule.add_mem _ hw hw'
    | add y y' hy hy' =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hy hy'
  simpa using h hz

/-- A cofree comodule endomorphism fixing the empty words is bijective. -/
private theorem bijective_of_apply_tmul_one_eq
    {G : Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (M ⊗[R] TensorWords R A)}
    (hG : ∀ x : M, G (x ⊗ₜ 1) = x ⊗ₜ 1) : Function.Bijective G :=
  Module.End.bijective_of_sub_mem_filtration cofreeFiltration_zero exists_mem_cofreeFiltration
    fun _ _ hz ↦ sub_mem_cofreeFiltration hG hz

end TensorWords

namespace Comodule.Hom

/-- A morphism of cofree comodules over the tensor coalgebra `Tᶜ(A)` is bijective when its
restriction to the empty word, `x ⊗ 1 ↦ g x ⊗ 1`, is given by a bijective linear map `g`. -/
theorem bijective_of_apply_tmul_one
    (F : Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A))
    {g : M →ₗ[R] N} (hg : Function.Bijective g) (hF : ∀ x : M, F (x ⊗ₜ 1) = g x ⊗ₜ 1) :
    Function.Bijective F := by
  set e := LinearEquiv.ofBijective g hg
  set G := (cofreeMap (C := TensorWords R A) e.symm.toLinearMap).comp F
  have hG : ∀ x : M, G (x ⊗ₜ 1) = x ⊗ₜ 1 := fun x ↦ by
    simp [G, hF, e]
  have hFG : ⇑F = ⇑(e.rTensor (TensorWords R A)) ∘ ⇑G := by
    funext z
    simp only [G, Function.comp_apply, Comodule.Hom.comp_apply, Comodule.Hom.cofreeMap_apply]
    exact ((e.rTensor _).apply_symm_apply _).symm
  rw [hFG]
  exact (e.rTensor _).bijective.comp (TensorWords.bijective_of_apply_tmul_one_eq hG)

end Comodule.Hom

end TauCeti
