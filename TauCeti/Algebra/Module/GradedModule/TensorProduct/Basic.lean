/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Module.GradedModule.Coarsen
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.LinearAlgebra.Graded.LinearMap
public import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Tensor products of internally graded modules

The tensor product of internally `ι`-graded modules is graded by total degree whenever `ι` has
addition (`[DecidableEq ι] [Add ι]`). Its degree-`n` piece is the sum of the images of

`G.piece p ⊗ H.piece q`

over all pairs `(p, q)` with `p + q = n` (which, when `ι` is an additive commutative group such as
`ℤ`, simplifies to the sum over `p` of `G.piece p ⊗ H.piece (n - p)`). These pieces form an
internal direct sum: first use `DirectSum.IsInternal.tensorProduct` for the bidegree decomposition,
then collect bidegrees with the same sum.

The resulting grading has the expected API on pure tensors. In particular, a tensor of elements
of degrees `p` and `q` has degree `p + q`, and tensoring homogeneous linear maps adds their
degrees. This grading is used by tensor products of differential graded objects and graded algebras.

## Main definitions

* `TauCeti.InternalGrading.tensorProduct`: the internal total-degree grading.

## Main results

* `TauCeti.InternalGrading.tmul_mem_tensorProduct` and
  `TauCeti.InternalGrading.tmul_mem_tensorProduct_ofDecomposition`: degrees add on pure tensors.
* `TauCeti.InternalGrading.tensorProduct_piece_le_of_add_eq`: a submodule containing every
  homogeneous pure tensor `x ⊗ₜ y` with `p + q = n` contains the degree-`n` piece.
* `TauCeti.InternalGrading.tensorProduct_piece_eq_iSup` and
  `TauCeti.InternalGrading.tensorProduct_piece_le`: for an additive commutative group `ι`, the
  degree-`n` piece is the sum over `G.piece p ⊗ H.piece (n - p)`.
* `TauCeti.InternalGrading.shift_tensorProduct_piece`: shifting the first factor shifts the total
  grading.
* `TauCeti.InternalGrading.span_range_tmul_piece_eq_top`: pure tensors of homogeneous elements
  span the tensor product.
* `TauCeti.InternalGrading.piTensorProduct_ext`: linear maps from a finite tensor product agree
  when they agree on pure tensors of homogeneous elements.
* `LinearMap.IsHomogeneous.tensorProduct`: tensoring homogeneous maps adds their degrees.
* `TauCeti.InternalGrading.isHomogeneous_assoc`,
  `TauCeti.InternalGrading.isHomogeneous_assoc_symm`, and
  `TauCeti.InternalGrading.isHomogeneous_tensorTensorTensorComm`: reassociating and interchanging
  tensor factors preserve total degree.
* `TauCeti.InternalGrading.koszulTwist_tensorProduct`: the Koszul twist of the total grading is
  the tensor product of the Koszul twists of the factors.
* `TauCeti.parityGrading_tensorProduct_one_eq_bot` and
  `TauCeti.parityGrading_baseChange_one_eq_bot`: tensor products and base change preserve even
  support.

The construction reuses `DirectSum.IsInternal.tensorProduct` for the bidegree decomposition
and `DirectSum.IsInternal.iSup_fiber` to collect equal total degrees.
-/

public section

open scoped DirectSum TensorProduct

universe u v w v' w'

namespace TauCeti

namespace InternalGrading

section PiTensorProduct

variable {R : Type u} [CommSemiring R] {ι : Type*} [Finite ι]
variable {M : ι → Type v} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Two linear maps from a tensor product of a finite family of internally graded modules agree
if they agree on pure tensors of homogeneous elements. -/
theorem piTensorProduct_ext (G : ∀ i, InternalGrading R (M i) ℤ)
    {f g : PiTensorProduct R M →ₗ[R] N}
    (h : ∀ q : ∀ i, Σ d : ℤ, (G i).piece d,
      f (PiTensorProduct.tprod R fun i ↦ (q i).2) =
        g (PiTensorProduct.tprod R fun i ↦ (q i).2)) : f = g := by
  apply PiTensorProduct.ext_of_span_eq_top
    (g := fun i (q : Σ d : ℤ, (G i).piece d) ↦ (q.2 : M i))
  · intro i
    convert (G i).span_setOf_exists_mem_piece_eq_top R using 2
    ext x
    simp
  · exact h

end PiTensorProduct

section Pieces

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The bidegree-`(p, q)` submodule in a tensor product of internally graded modules. -/
private def tensorProductBidegreePiece {ι : Type*} [DecidableEq ι]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι)
    (d : ι × ι) : Submodule R (M ⊗[R] N) :=
  Submodule.map₂ (TensorProduct.mk R M N) (G.piece d.1) (H.piece d.2)

private def tensorProductPiece {ι : Type*} [DecidableEq ι] [Add ι]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι) (n : ι) :
    Submodule R (M ⊗[R] N) :=
  ⨆ d : ι × ι, ⨆ _ : d.1 + d.2 = n, tensorProductBidegreePiece G H d

private theorem tensorProductPiece_eq_iSup {ι : Type*} [DecidableEq ι] [AddCommGroup ι]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι) (n : ι) :
    tensorProductPiece G H n =
      ⨆ p : ι, Submodule.map₂ (TensorProduct.mk R M N) (G.piece p) (H.piece (n - p)) := by
  apply le_antisymm
  · refine iSup_le fun d ↦ iSup_le fun hd ↦ ?_
    refine le_iSup_of_le d.1 ?_
    have hdeg : d.2 = n - d.1 := by rw [← hd, add_sub_cancel_left]
    simpa only [tensorProductBidegreePiece, hdeg] using
      (le_rfl : Submodule.map₂ (TensorProduct.mk R M N) (G.piece d.1)
        (H.piece (n - d.1)) ≤ _)
  · refine iSup_le fun p ↦ ?_
    refine le_iSup_of_le (p, n - p) ?_
    refine le_iSup_of_le (add_sub_cancel p n) ?_
    rfl

end Pieces

section Internal

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The tensor product of internally graded modules, graded by total degree. -/
noncomputable def tensorProduct {ι : Type*} [DecidableEq ι] [Add ι]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι) :
    InternalGrading R (M ⊗[R] N) ι where
  piece := tensorProductPiece G H
  -- `tensorProductPiece` is by definition the supremum of the bidegree pieces over each fiber of
  -- the total-degree map, which is the form produced by `DirectSum.IsInternal.iSup_fiber`.
  isInternal :=
    (DirectSum.IsInternal.tensorProduct G.piece H.piece G.isInternal H.isInternal).iSup_fiber
      fun d ↦ d.1 + d.2

/-- A pure tensor of elements of degrees `p` and `q` is homogeneous of degree `p + q` in the
tensor-product grading. -/
theorem tmul_mem_tensorProduct {ι : Type*} [DecidableEq ι] [Add ι]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι)
    {p q : ι} {x : M} {y : N} (hx : x ∈ G.piece p) (hy : y ∈ H.piece q) :
    x ⊗ₜ[R] y ∈ (G.tensorProduct H).piece (p + q) :=
  Submodule.mem_iSup_of_mem (p, q) <| Submodule.mem_iSup_of_mem rfl <| by
    simpa only [tensorProductBidegreePiece, TensorProduct.mk_apply] using
      Submodule.apply_mem_map₂ (TensorProduct.mk R M N) hx hy

/-- For gradings given by decompositions `ℳ` and `𝒩`, a pure tensor of elements of `ℳ p` and
`𝒩 q` is homogeneous of degree `p + q` in the tensor-product grading. -/
theorem tmul_mem_tensorProduct_ofDecomposition {ι : Type*} [DecidableEq ι] [Add ι]
    (ℳ : ι → Submodule R M) (𝒩 : ι → Submodule R N) [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition 𝒩] {p q : ι} {x : M} {y : N} (hx : x ∈ ℳ p) (hy : y ∈ 𝒩 q) :
    x ⊗ₜ[R] y ∈ ((ofDecomposition ℳ).tensorProduct (ofDecomposition 𝒩)).piece (p + q) :=
  tmul_mem_tensorProduct _ _ (by rwa [ofDecomposition_piece]) (by rwa [ofDecomposition_piece])

/-- A submodule containing every pure tensor of homogeneous elements whose degrees sum to `n`
contains the whole degree-`n` piece of the tensor-product grading. -/
theorem tensorProduct_piece_le_of_add_eq {ι : Type*} [DecidableEq ι] [Add ι]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι) {n : ι}
    {C : Submodule R (M ⊗[R] N)}
    (h : ∀ p q : ι, p + q = n → ∀ x ∈ G.piece p, ∀ y ∈ H.piece q, x ⊗ₜ[R] y ∈ C) :
    (G.tensorProduct H).piece n ≤ C :=
  iSup_le fun d ↦ iSup_le fun hd ↦ Submodule.map₂_le.2 fun x hx y hy ↦ h d.1 d.2 hd x hx y hy

/-- The degree-`n` piece of the tensor-product grading is the sum of the tensor-product images
whose first degree is `p` and whose second degree is `n - p`. -/
theorem tensorProduct_piece_eq_iSup {ι : Type*} [DecidableEq ι] [AddCommGroup ι]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι) (n : ι) :
    (G.tensorProduct H).piece n =
      ⨆ p : ι, Submodule.map₂ (TensorProduct.mk R M N) (G.piece p) (H.piece (n - p)) :=
  tensorProductPiece_eq_iSup G H n

/-- A submodule containing every pure tensor of homogeneous elements of total degree `n` contains
the whole degree-`n` piece of the tensor-product grading. -/
theorem tensorProduct_piece_le {ι : Type*} [DecidableEq ι] [AddCommGroup ι]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι) {n : ι}
    {C : Submodule R (M ⊗[R] N)}
    (h : ∀ p : ι, ∀ x ∈ G.piece p, ∀ y ∈ H.piece (n - p), x ⊗ₜ[R] y ∈ C) :
    (G.tensorProduct H).piece n ≤ C := by
  rw [tensorProduct_piece_eq_iSup]
  exact iSup_le fun p ↦ Submodule.map₂_le.2 fun x hx y hy ↦ h p x hx y hy

/-- Shifting the grading of the first factor by `c` shifts the total grading of the tensor product
by `c`. -/
theorem shift_tensorProduct_piece (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ) (c : ℤ) :
    ((G.shift c).tensorProduct H).piece = ((G.tensorProduct H).shift c).piece := by
  funext d
  refine le_antisymm (tensorProduct_piece_le _ _ fun p x hx y hy ↦ ?_) ?_
  · rw [shift_piece] at hx ⊢
    simpa [show p + c + (d - p) = d + c by ring] using tmul_mem_tensorProduct G H hx hy
  · rw [shift_piece]
    refine tensorProduct_piece_le _ _ fun p x hx y hy ↦ ?_
    have hx' : x ∈ (G.shift c).piece (p - c) := by
      rwa [shift_piece, sub_add_cancel]
    simpa [show p - c + (d + c - p) = d by ring] using tmul_mem_tensorProduct (G.shift c) H hx' hy

/-- Pure tensors of homogeneous elements span the tensor product of internally graded modules. -/
theorem span_range_tmul_piece_eq_top (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ) :
    Submodule.span R (Set.range fun z : Σ pq : ℤ × ℤ, G.piece pq.1 × H.piece pq.2 ↦
      (z.2.1 : M) ⊗ₜ[R] (z.2.2 : N)) = ⊤ := by
  refine top_unique ?_
  rw [← TensorProduct.map₂_mk_top_top_eq_top, ← G.span_setOf_exists_mem_piece_eq_top R,
    ← H.span_setOf_exists_mem_piece_eq_top R, Submodule.map₂_span_span, Submodule.span_le]
  rintro _ ⟨x, ⟨p, hx⟩, y, ⟨q, hy⟩, rfl⟩
  exact Submodule.subset_span ⟨⟨(p, q), ⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩

/-- Reassociating a triple tensor product preserves total degree. -/
theorem isHomogeneous_assoc_symm {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    {P : Type w'} [AddCommMonoid P] [Module R P]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι) (K : InternalGrading R P ι) :
    LinearMap.IsHomogeneous (TensorProduct.assoc R M N P).symm.toLinearMap
      (G.tensorProduct (H.tensorProduct K)).piece ((G.tensorProduct H).tensorProduct K).piece
      0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine G.tensorProduct_piece_le_of_add_eq (H.tensorProduct K)
    (C := (((G.tensorProduct H).tensorProduct K).piece (n + 0)).comap
      (TensorProduct.assoc R M N P).symm.toLinearMap) (fun p s hps x hx t ht ↦ ?_) hz
  refine H.tensorProduct_piece_le_of_add_eq K
    (C := (((G.tensorProduct H).tensorProduct K).piece (n + 0)).comap
      ((TensorProduct.assoc R M N P).symm.toLinearMap ∘ₗ TensorProduct.mk R M (N ⊗[R] P) x))
    (fun r u hru y hy v hv ↦ ?_) ht
  rw [Submodule.mem_comap, LinearMap.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul]
  have hdeg : n + 0 = p + r + u := by rw [add_zero, ← hps, ← hru, add_assoc]
  rw [hdeg]
  exact tmul_mem_tensorProduct _ _ (tmul_mem_tensorProduct G H hx hy) hv

/-- Reassociating a triple tensor product preserves total degree. -/
theorem isHomogeneous_assoc {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    {P : Type w'} [AddCommMonoid P] [Module R P]
    (G : InternalGrading R M ι) (H : InternalGrading R N ι) (K : InternalGrading R P ι) :
    LinearMap.IsHomogeneous (TensorProduct.assoc R M N P).toLinearMap
      ((G.tensorProduct H).tensorProduct K).piece (G.tensorProduct (H.tensorProduct K)).piece
      0 := by
  exact (isHomogeneous_assoc_symm G H K).linearEquiv_symm

/-- The fourfold tensor-product interchange `tensorTensorTensorComm` preserves total degree. -/
theorem isHomogeneous_tensorTensorTensorComm {M' : Type v'} {N' : Type w'}
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (G : InternalGrading R M ℤ) (G' : InternalGrading R M' ℤ)
    (H : InternalGrading R N ℤ) (H' : InternalGrading R N' ℤ) :
    LinearMap.IsHomogeneous (TensorProduct.tensorTensorTensorComm R M M' N N').toLinearMap
      ((G.tensorProduct G').tensorProduct (H.tensorProduct H')).piece
      ((G.tensorProduct H).tensorProduct (G'.tensorProduct H')).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  set target := ((G.tensorProduct H).tensorProduct (G'.tensorProduct H')).piece (n + 0) with htarget
  refine (G.tensorProduct G').tensorProduct_piece_le (H.tensorProduct H')
    (C := target.comap (TensorProduct.tensorTensorTensorComm R M M' N N').toLinearMap)
    (fun p t₁ ht₁ t₂ ht₂ ↦ G.tensorProduct_piece_le G'
      (C := target.comap ((TensorProduct.tensorTensorTensorComm R M M' N N').toLinearMap ∘ₗ
        (TensorProduct.mk R (M ⊗[R] M') (N ⊗[R] N')).flip t₂))
      (fun q x₁ hx₁ x₂ hx₂ ↦ H.tensorProduct_piece_le H'
        (C := target.comap ((TensorProduct.tensorTensorTensorComm R M M' N N').toLinearMap ∘ₗ
          TensorProduct.mk R (M ⊗[R] M') (N ⊗[R] N') (x₁ ⊗ₜ[R] x₂)))
        (fun r y₁ hy₁ y₂ hy₂ ↦ ?_) ht₂) ht₁) hz
  rw [Submodule.mem_comap, LinearMap.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
    TensorProduct.tensorTensorTensorComm_tmul]
  have hdeg : n + 0 = (q + r) + ((p - q) + (n - p - r)) := by ring
  rw [htarget, hdeg]
  exact tmul_mem_tensorProduct _ _ (tmul_mem_tensorProduct G H hx₁ hy₁)
    (tmul_mem_tensorProduct G' H' hx₂ hy₂)

end Internal

section KoszulTwist

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The Koszul twist for the total grading of a tensor product is the tensor product of the
Koszul twists of the factors. -/
theorem koszulTwist_tensorProduct (G : InternalGrading R M ℤ) (H : InternalGrading R N ℤ) (q : ℤ) :
    (G.tensorProduct H).koszulTwist q = TensorProduct.map (G.koszulTwist q) (H.koszulTwist q) := by
  refine TensorProduct.ext (G.linearMap_ext fun p x hx ↦ H.linearMap_ext fun r y hy ↦ ?_)
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, TensorProduct.map_tmul,
    (G.tensorProduct H).koszulTwist_apply_of_mem (tmul_mem_tensorProduct G H hx hy),
    G.koszulTwist_apply_of_mem hx, H.koszulTwist_apply_of_mem hy, TensorProduct.smul_tmul_smul,
    mul_add, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

end KoszulTwist

end InternalGrading

end TauCeti

namespace LinearMap.IsHomogeneous

open TauCeti (InternalGrading)

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w} {M' : Type v'} {N' : Type w'}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- Tensoring homogeneous linear maps adds their degrees for the total tensor-product gradings. -/
@[grind →]
theorem tensorProduct {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {G : InternalGrading R M ι} {H : InternalGrading R N ι}
    {G' : InternalGrading R M' ι} {H' : InternalGrading R N' ι} {f : M →ₗ[R] M'} {g : N →ₗ[R] N'}
    {a b : ι} (hf : LinearMap.IsHomogeneous f G.piece G'.piece a)
    (hg : LinearMap.IsHomogeneous g H.piece H'.piece b) :
    LinearMap.IsHomogeneous (TensorProduct.map f g) (G.tensorProduct H).piece
      (G'.tensorProduct H').piece (a + b) := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine G.tensorProduct_piece_le_of_add_eq H
    (C := ((G'.tensorProduct H').piece (n + (a + b))).comap (TensorProduct.map f g))
    (fun p q hpq x hx y hy ↦ ?_) hz
  rw [Submodule.mem_comap, TensorProduct.map_tmul]
  have hdeg : n + (a + b) = (p + a) + (q + b) := by rw [← hpq, add_add_add_comm]
  rw [hdeg]
  exact InternalGrading.tmul_mem_tensorProduct G' H' (hf.map_mem hx) (hg.map_mem hy)

/-- Tensoring a homogeneous map with the identity on the right preserves its degree. -/
theorem rTensor {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {G : InternalGrading R M ι} {G' : InternalGrading R M' ι} {f : M →ₗ[R] M'}
    {a : ι} (hf : LinearMap.IsHomogeneous f G.piece G'.piece a) (H : InternalGrading R N ι) :
    LinearMap.IsHomogeneous (f.rTensor N) (G.tensorProduct H).piece
      (G'.tensorProduct H).piece a := by
  simpa only [LinearMap.rTensor_def, add_zero] using
    hf.tensorProduct (LinearMap.isHomogeneous_id (R := R) H.piece)

end LinearMap.IsHomogeneous

namespace TauCeti

/-- The tensor product of two even-supported internally `ℤ`-graded modules is even-supported. -/
theorem parityGrading_tensorProduct_one_eq_bot {R : Type u} {M : Type v} {N : Type w}
    [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}
    (hG : parityGrading G.piece 1 = ⊥) (hH : parityGrading H.piece 1 = ⊥) :
    parityGrading (G.tensorProduct H).piece 1 = ⊥ :=
  parityGrading_one_eq_bot_iff.mpr fun k => le_bot_iff.mp <|
    G.tensorProduct_piece_le H fun p x hx y hy => by
      rcases Int.even_or_odd p with ⟨m, rfl⟩ | hp
      · rw [eq_bot_of_parityGrading_one_eq_bot_of_odd hH ⟨k - m, by ring⟩, Submodule.mem_bot] at hy
        simp [hy]
      · rw [eq_bot_of_parityGrading_one_eq_bot_of_odd hG hp, Submodule.mem_bot] at hx
        simp [hx]

/-- Base change preserves even support of an integer-indexed family of submodules. -/
theorem parityGrading_baseChange_one_eq_bot {R : Type u} {S : Type*} {M : Type v}
    [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
    {ℳ : ℤ → Submodule R M} (h : parityGrading ℳ 1 = ⊥) :
    parityGrading (fun i : ℤ => (ℳ i).baseChange S) 1 = ⊥ := by
  rw [parityGrading_one_eq_bot_iff] at h ⊢; intro k; simp [h k]

end TauCeti
