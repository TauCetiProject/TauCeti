/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.Sum.Order
public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum

/-!
# Slot sums and slot homotopies on a tensor product indexed by a sum

A tensor product indexed by `ι ⊕ ι₂` is the tensor product of the tensor products over `ι` and
over `ι₂` (`PiTensorProduct.tmulEquivDep`). This file records how the slot constructions of
`TauCeti.LinearAlgebra.PiTensorProduct.SlotSum` split along that identification:

* factorwise maps act block by block (`TauCeti.PiTensorProduct.map_tmulEquivDep`);
* the slot sum over `ι ⊕ ι₂` is the slot sum over `ι` on the left plus the slot sum over `ι₂` on
  the right (`TauCeti.PiTensorProduct.slotSum_tmulEquivDep`), the unsigned Leibniz rule of a
  tensor product of complexes in characteristic two;
* total degrees add (`TauCeti.PiTensorProduct.tmulEquivDep_mem_totalDegreePiece`).

The slot homotopy depends on an order of the factors. Indexing the factors by the lexicographic
sum `ι ⊕ₗ ι₂`, in which every index of `ι` precedes every index of `ι₂`, gives the
**lexicographic tensor** `TauCeti.PiTensorProduct.tmulLex` of the two blocks. For it the slot
homotopy is the slot homotopy over `ι` on the left, plus `e ⊗ ⋯ ⊗ e` on the left tensored with
the slot homotopy over `ι₂` on the right (`TauCeti.PiTensorProduct.slotHomotopy_tmulLex`).

This is the tensor trick for two blocks of factors. When `e` fixes and `h` kills the left factor,
it says that the slot homotopy commutes with multiplying on the left by that factor, which is
what identifies a class on a tensor product of contracted resolutions with a cup product
(`TauCeti.gradedCohomologyClass_smoothPiTensorProductLexPairing`).

## Main definitions

* `TauCeti.PiTensorProduct.tmulLex`: the tensor of a tensor over `ι` with a tensor over `ι₂`,
  indexed by `ι ⊕ₗ ι₂`.

## Main results

* `TauCeti.PiTensorProduct.ext_tprod_tmul_tprod`: linear maps out of a tensor product of two
  tensor products are determined on tensors of pure tensors.
* `TauCeti.PiTensorProduct.map_tmulEquivDep`, `TauCeti.PiTensorProduct.map_tmulLex`: factorwise
  maps act block by block.
* `TauCeti.PiTensorProduct.slotSum_tmulEquivDep`, `TauCeti.PiTensorProduct.slotSum_tmulLex`: the
  slot sum satisfies the Leibniz rule.
* `TauCeti.PiTensorProduct.tmulEquivDep_mem_totalDegreePiece`,
  `TauCeti.PiTensorProduct.tmulLex_mem_totalDegreePiece`: total degrees add.
* `TauCeti.PiTensorProduct.slotHomotopy_tmulLex`: the lexicographic slot homotopy splits.
-/

public section

open Function
open scoped TensorProduct

namespace TauCeti.PiTensorProduct

variable {ι ι₂ R A : Type*} [CommSemiring R]
  {N P : ι ⊕ ι₂ → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- Linear maps out of a tensor product of two tensor products agree once they agree on the
tensors `(⨂ₜ i, a i) ⊗ₜ (⨂ₜ j, b j)` of pure tensors. -/
theorem ext_tprod_tmul_tprod {M : ι → Type*} {M' : ι₂ → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [∀ j, AddCommMonoid (M' j)] [∀ j, Module R (M' j)]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    {F F' : (⨂[R] i, M i) ⊗[R] (⨂[R] j, M' j) →ₗ[R] Q}
    (h : ∀ (a : ∀ i, M i) (b : ∀ j, M' j),
      F (PiTensorProduct.tprod R a ⊗ₜ PiTensorProduct.tprod R b) =
        F' (PiTensorProduct.tprod R a ⊗ₜ PiTensorProduct.tprod R b)) : F = F' :=
  TensorProduct.ext <| PiTensorProduct.ext <| MultilinearMap.ext fun a ↦
    PiTensorProduct.ext <| MultilinearMap.ext fun b ↦ h a b

/-- Factorwise maps on a tensor product indexed by `ι ⊕ ι₂` act separately on the two blocks of
`tmulEquivDep`. -/
theorem map_tmulEquivDep (g : ∀ i, N i →ₗ[R] P i) (x : ⨂[R] i, N (.inl i))
    (y : ⨂[R] j, N (.inr j)) :
    PiTensorProduct.map g (PiTensorProduct.tmulEquivDep R N (x ⊗ₜ y)) =
      PiTensorProduct.tmulEquivDep R P
        (PiTensorProduct.map (fun i ↦ g (.inl i)) x ⊗ₜ
          PiTensorProduct.map (fun j ↦ g (.inr j)) y) :=
  LinearMap.congr_fun (ext_tprod_tmul_tprod
    (F := PiTensorProduct.map g ∘ₗ (PiTensorProduct.tmulEquivDep R N).toLinearMap)
    (F' := (PiTensorProduct.tmulEquivDep R P).toLinearMap ∘ₗ
      TensorProduct.map (PiTensorProduct.map fun i ↦ g (.inl i))
        (PiTensorProduct.map fun j ↦ g (.inr j)))
    fun a b ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
        PiTensorProduct.tmulEquivDep_apply, PiTensorProduct.map_tprod]
      congr 1
      funext k
      rcases k with i | j <;> rfl) (x ⊗ₜ y)

variable (R N) in
/-- **The lexicographic tensor of two blocks**: a tensor over `ι` and a tensor over `ι₂` give a
tensor over `ι ⊕ ι₂` (`PiTensorProduct.tmulEquivDep`), whose factors are then indexed by the
lexicographic sum `ι ⊕ₗ ι₂`, in which every index of `ι` precedes every index of `ι₂`. -/
noncomputable def tmulLex :
    (⨂[R] i, N (.inl i)) →ₗ[R] (⨂[R] j, N (.inr j)) →ₗ[R] ⨂[R] k : ι ⊕ₗ ι₂, N (ofLex k) :=
  (TensorProduct.mk R _ _).compr₂ ((PiTensorProduct.reindex R N toLex).toLinearMap ∘ₗ
    (PiTensorProduct.tmulEquivDep R N).toLinearMap)

/-- The lexicographic tensor reindexes the tensor of the two blocks along `toLex`. -/
theorem tmulLex_apply (x : ⨂[R] i, N (.inl i)) (y : ⨂[R] j, N (.inr j)) :
    tmulLex R N x y =
      PiTensorProduct.reindex R N toLex (PiTensorProduct.tmulEquivDep R N (x ⊗ₜ y)) :=
  (rfl)

/-- The lexicographic tensor of two pure tensors is the pure tensor of the joined family. -/
@[simp]
theorem tmulLex_tprod_tprod (a : ∀ i, N (.inl i)) (b : ∀ j, N (.inr j)) :
    tmulLex R N (PiTensorProduct.tprod R a) (PiTensorProduct.tprod R b) =
      PiTensorProduct.tprod R fun k ↦ Sum.rec a b (ofLex k) := by
  rw [tmulLex_apply, PiTensorProduct.tmulEquivDep_apply, PiTensorProduct.reindex_tprod]
  -- `toLex.symm` is `ofLex` by definition (`toLex_symm_eq`).
  rfl

/-- Factorwise maps act on the lexicographic tensor block by block. -/
theorem map_tmulLex (g : ∀ i, N i →ₗ[R] P i) (x : ⨂[R] i, N (.inl i))
    (y : ⨂[R] j, N (.inr j)) :
    PiTensorProduct.map (fun k ↦ g (ofLex k)) (tmulLex R N x y) =
      tmulLex R P (PiTensorProduct.map (fun i ↦ g (.inl i)) x)
        (PiTensorProduct.map (fun j ↦ g (.inr j)) y) :=
  -- The factors of `tmulLex` are indexed through `toLex.symm`, which is `ofLex` by definition.
  (PiTensorProduct.map_reindex g toLex _).trans
    (congrArg (PiTensorProduct.reindex R P toLex) (map_tmulEquivDep g x y))

variable [Fintype ι] [Fintype ι₂]

/-- **The Leibniz rule for slot sums.** On a tensor product indexed by `ι ⊕ ι₂`, the slot sum
applies the slot sum over `ι` on the left block plus the slot sum over `ι₂` on the right block. -/
theorem slotSum_tmulEquivDep [DecidableEq ι] [DecidableEq ι₂] (f : ∀ i, Module.End R (N i))
    (x : ⨂[R] i, N (.inl i)) (y : ⨂[R] j, N (.inr j)) :
    slotSum (ι ⊕ ι₂) f (PiTensorProduct.tmulEquivDep R N (x ⊗ₜ y)) =
      PiTensorProduct.tmulEquivDep R N (slotSum ι (fun i ↦ f (.inl i)) x ⊗ₜ y) +
        PiTensorProduct.tmulEquivDep R N (x ⊗ₜ slotSum ι₂ (fun j ↦ f (.inr j)) y) := by
  have key := LinearMap.congr_fun (ext_tprod_tmul_tprod
    (F := slotSum (ι ⊕ ι₂) f ∘ₗ (PiTensorProduct.tmulEquivDep R N).toLinearMap)
    (F' := (PiTensorProduct.tmulEquivDep R N).toLinearMap ∘ₗ
        TensorProduct.map (slotSum ι fun i ↦ f (.inl i)) LinearMap.id +
      (PiTensorProduct.tmulEquivDep R N).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id (slotSum ι₂ fun j ↦ f (.inr j)))
    fun a b ↦ by
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.tmulEquivDep_apply,
        slotSum_tprod, Fintype.sum_sum_type, ← Sum.rec_update_left, ← Sum.rec_update_right,
        TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum]) (x ⊗ₜ y)
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_tmul, LinearMap.id_apply] using key

/-- **Total degrees add along `tmulEquivDep`.** For gradings of the factors, the tensor of an
element of total degree `p` over `ι` with one of total degree `q` over `ι₂` has total degree
`p + q` over `ι ⊕ ι₂`. -/
theorem tmulEquivDep_mem_totalDegreePiece [AddCommMonoid A] {ℳ : ∀ i, A → Submodule R (N i)}
    {p q : A} {x : ⨂[R] i, N (.inl i)} {y : ⨂[R] j, N (.inr j)}
    (hx : x ∈ totalDegreePiece ι (fun i ↦ ℳ (.inl i)) p)
    (hy : y ∈ totalDegreePiece ι₂ (fun j ↦ ℳ (.inr j)) q) :
    PiTensorProduct.tmulEquivDep R N (x ⊗ₜ y) ∈ totalDegreePiece (ι ⊕ ι₂) ℳ (p + q) := by
  -- Reduce to pure tensors of homogeneous factors, first on the left and then on the right.
  let T : (⨂[R] i, N (.inl i)) →ₗ[R] (⨂[R] j, N (.inr j)) →ₗ[R] ⨂[R] k, N k :=
    (TensorProduct.mk R _ _).compr₂ (PiTensorProduct.tmulEquivDep R N).toLinearMap
  refine (totalDegreePiece_le_iff (P := (totalDegreePiece (ι ⊕ ι₂) ℳ (p + q)).comap
    (T.flip y)).2 ?_) hx
  rintro pa a ha rfl
  refine (totalDegreePiece_le_iff (P := (totalDegreePiece (ι ⊕ ι₂) ℳ (∑ i, pa i + q)).comap
    (T (PiTensorProduct.tprod R a))).2 ?_) hy
  rintro pb b hb rfl
  simp only [Submodule.mem_comap, T, LinearMap.compr₂_apply,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, PiTensorProduct.tmulEquivDep_apply]
  have h := tprod_mem_totalDegreePiece (R := R) (ℳ := ℳ) (p := Sum.elim pa pb)
    (m := fun k ↦ Sum.rec (motive := N) a b k) (fun k ↦ by rcases k with i | j; exacts [ha i, hb j])
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at h
  exact h

/-- **The Leibniz rule for the lexicographic tensor.** The slot sum over `ι ⊕ₗ ι₂` of the
lexicographic tensor of `x` and `y` is the tensor of the slot sum of `x` with `y`, plus the tensor
of `x` with the slot sum of `y`. -/
theorem slotSum_tmulLex [DecidableEq ι] [DecidableEq ι₂] (f : ∀ i, Module.End R (N i))
    (x : ⨂[R] i, N (.inl i)) (y : ⨂[R] j, N (.inr j)) :
    slotSum (ι ⊕ₗ ι₂) (fun k ↦ f (ofLex k)) (tmulLex R N x y) =
      tmulLex R N (slotSum ι (fun i ↦ f (.inl i)) x) y +
        tmulLex R N x (slotSum ι₂ (fun j ↦ f (.inr j)) y) :=
  -- The factors of `tmulLex` are indexed through `toLex.symm`, which is `ofLex` by definition.
  (LinearMap.congr_fun (slotSum_comp_reindex f toLex) _).trans <|
    (congrArg (PiTensorProduct.reindex R N toLex) (slotSum_tmulEquivDep f x y)).trans
      (map_add _ _ _)

/-- Total degrees add along the lexicographic tensor. -/
theorem tmulLex_mem_totalDegreePiece [AddCommMonoid A] {ℳ : ∀ i, A → Submodule R (N i)}
    {p q : A} {x : ⨂[R] i, N (.inl i)} {y : ⨂[R] j, N (.inr j)}
    (hx : x ∈ totalDegreePiece ι (fun i ↦ ℳ (.inl i)) p)
    (hy : y ∈ totalDegreePiece ι₂ (fun j ↦ ℳ (.inr j)) q) :
    tmulLex R N x y ∈ totalDegreePiece (ι ⊕ₗ ι₂) (fun k ↦ ℳ (ofLex k)) (p + q) :=
  -- As for `slotSum_tmulLex`, `toLex.symm` is `ofLex` by definition.
  (reindex_mem_totalDegreePiece_iff ℳ toLex _ _).2 (tmulEquivDep_mem_totalDegreePiece hx hy)

variable [LinearOrder ι] [LinearOrder ι₂]

/-- The tensor trick for two blocks on pure tensors: in a slot of the left block the factors of
the right block are untouched, and in a slot of the right block every factor of the left block
precedes it and so carries `e`. -/
private theorem slotHomotopy_tmulLex_tprod (e h : ∀ i, Module.End R (N i))
    (a : ∀ i, N (.inl i)) (b : ∀ j, N (.inr j)) :
    slotHomotopy (ι ⊕ₗ ι₂) (fun k ↦ e (ofLex k)) (fun k ↦ h (ofLex k))
        (tmulLex R N (PiTensorProduct.tprod R a) (PiTensorProduct.tprod R b)) =
      tmulLex R N (slotHomotopy ι (fun i ↦ e (.inl i)) (fun i ↦ h (.inl i))
          (PiTensorProduct.tprod R a)) (PiTensorProduct.tprod R b) +
        tmulLex R N (PiTensorProduct.map (fun i ↦ e (.inl i)) (PiTensorProduct.tprod R a))
          (slotHomotopy ι₂ (fun j ↦ e (.inr j)) (fun j ↦ h (.inr j))
            (PiTensorProduct.tprod R b)) := by
  simp only [tmulLex_tprod_tprod, slotHomotopy_tprod, PiTensorProduct.map_tprod, map_sum,
    LinearMap.sum_apply]
  -- Split the sum over the lexicographic slots into the left and the right block.
  rw [← toLex.sum_comp, Fintype.sum_sum_type]
  -- Compare the pure tensors slot by slot and factor by factor. The factor at `toLex k` lives in
  -- `N (ofLex (toLex k))`, which is `N k` by the definitional equation
  -- `ofLex (toLex k) = k`; the closing `rfl`s use it.
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (funext fun k ↦ ?_)
    obtain ⟨k, rfl⟩ := toLex.surjective k
    rcases k with i' | j
    · rcases eq_or_ne i' i with rfl | hi
      · rw [update_self]
        dsimp only [ofLex_toLex]
        rw [update_self]
        rfl
      · rw [update_of_ne (toLex.injective.ne (Sum.inl_injective.ne hi))]
        simp only [ofLex_toLex, Sum.Lex.toLex_lt_toLex, Sum.lex_inl_inl,
          update_of_ne hi]
        rfl
    · rw [update_of_ne (toLex.injective.ne Sum.inr_ne_inl)]
      simp only [ofLex_toLex, Sum.Lex.toLex_lt_toLex, Sum.lex_inr_inl, ↓reduceIte]
  · refine Finset.sum_congr rfl fun j _ ↦ congrArg _ (funext fun k ↦ ?_)
    obtain ⟨k, rfl⟩ := toLex.surjective k
    rcases k with i | j'
    · rw [update_of_ne (toLex.injective.ne Sum.inl_ne_inr)]
      simp only [ofLex_toLex, Sum.Lex.toLex_lt_toLex, Sum.Lex.sep, ↓reduceIte]
      rfl
    · rcases eq_or_ne j' j with rfl | hj
      · rw [update_self]
        dsimp only [ofLex_toLex]
        rw [update_self]
        rfl
      · rw [update_of_ne (toLex.injective.ne (Sum.inr_injective.ne hj))]
        simp only [ofLex_toLex, Sum.Lex.toLex_lt_toLex, Sum.lex_inr_inr,
          update_of_ne hj]
        rfl

/-- **The tensor trick for two blocks.** For the lexicographic order on `ι ⊕ₗ ι₂`, in which every
index of `ι` precedes every index of `ι₂`, the slot homotopy of `e` and `h` on the lexicographic
tensor of `x` and `y` is the tensor of the slot homotopy of `x` with `y`, plus the tensor of
`e ⊗ ⋯ ⊗ e` applied to `x` with the slot homotopy of `y`. -/
theorem slotHomotopy_tmulLex (e h : ∀ i, Module.End R (N i))
    (x : ⨂[R] i, N (.inl i)) (y : ⨂[R] j, N (.inr j)) :
    slotHomotopy (ι ⊕ₗ ι₂) (fun k ↦ e (ofLex k)) (fun k ↦ h (ofLex k))
        (tmulLex R N x y) =
      tmulLex R N (slotHomotopy ι (fun i ↦ e (.inl i)) (fun i ↦ h (.inl i)) x) y +
        tmulLex R N (PiTensorProduct.map (fun i ↦ e (.inl i)) x)
          (slotHomotopy ι₂ (fun j ↦ e (.inr j)) (fun j ↦ h (.inr j)) y) := by
  -- Both sides are bilinear in `x` and `y`; compare them on pure tensors.
  have key := LinearMap.congr_fun (ext_tprod_tmul_tprod
    (F := slotHomotopy (ι ⊕ₗ ι₂) (fun k ↦ e (ofLex k)) (fun k ↦ h (ofLex k)) ∘ₗ
      TensorProduct.lift (tmulLex R N))
    (F' := TensorProduct.lift (tmulLex R N) ∘ₗ
        TensorProduct.map (slotHomotopy ι (fun i ↦ e (.inl i)) (fun i ↦ h (.inl i)))
          LinearMap.id +
      TensorProduct.lift (tmulLex R N) ∘ₗ
        TensorProduct.map (PiTensorProduct.map fun i ↦ e (.inl i))
          (slotHomotopy ι₂ (fun j ↦ e (.inr j)) (fun j ↦ h (.inr j))))
    fun a b ↦ by
      simpa only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, TensorProduct.lift.tmul] using slotHomotopy_tmulLex_tprod e h a b)
    (x ⊗ₜ y)
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.lift.tmul] using key

end TauCeti.PiTensorProduct
