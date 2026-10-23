/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.Graded.LinearMap
public import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Tensor products of internally graded modules

The tensor product of internally `ℤ`-graded modules is graded by total degree. Its degree-`n`
piece is the sum of the images of

`G.piece p ⊗ H.piece (n - p)`

inside the ambient tensor product. These pieces form an internal direct sum: first use
`DirectSum.IsInternal.tensorProduct` for the bidegree decomposition, then collect bidegrees with
the same sum.

The resulting grading has the expected API on pure tensors. In particular, a tensor of elements
of degrees `p` and `q` has degree `p + q`, and tensoring homogeneous linear maps adds their
degrees. This grading is used by tensor products of differential graded objects.

## Main definitions

* `TauCeti.InternalGrading.tensorProduct`: the internal total-degree grading.

## Main results

* `TauCeti.InternalGrading.tensorProduct_piece_eq_iSup`: the degree-`n` piece is the sum over
  `G.piece p ⊗ H.piece (n - p)`.
* `TauCeti.InternalGrading.tmul_mem_tensorProduct`: degrees add on pure tensors.
* `TauCeti.InternalGrading.tensorProduct_piece_le`: a submodule containing every homogeneous pure
  tensor of total degree `n` contains the degree-`n` piece.
* `TauCeti.InternalGrading.piTensorProduct_ext`: linear maps from a finite tensor product agree
  when they agree on pure tensors of homogeneous elements.
* `TauCeti.LinearMap.IsHomogeneous.tensorProduct`: tensoring homogeneous maps adds their degrees.
* `TauCeti.InternalGrading.isHomogeneous_assoc` and
  `TauCeti.InternalGrading.isHomogeneous_assoc_symm`: reassociation preserves total degree.
* `TauCeti.InternalGrading.koszulTwist_tensorProduct`: the Koszul twist of the total grading is
  the tensor product of the Koszul twists of the factors.

The construction reuses `DirectSum.IsInternal.tensorProduct` for the bidegree decomposition
and `DirectSum.IsInternal.iSup_fiber` to collect equal total degrees.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe u v w v' w'

namespace InternalGrading

section PiTensorProduct

variable {R : Type u} [CommSemiring R] {ι : Type*} [Finite ι]
variable {M : ι → Type v} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Two linear maps from a tensor product of a finite family of internally graded modules agree
if they agree on pure tensors of homogeneous elements. -/
theorem piTensorProduct_ext (G : ∀ i, InternalGrading R (M i))
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
private def tensorProductBidegreePiece (G : InternalGrading R M) (H : InternalGrading R N)
    (d : ℤ × ℤ) : Submodule R (M ⊗[R] N) :=
  Submodule.map₂ (TensorProduct.mk R M N) (G.piece d.1) (H.piece d.2)

private def tensorProductPiece (G : InternalGrading R M) (H : InternalGrading R N) (n : ℤ) :
    Submodule R (M ⊗[R] N) :=
  ⨆ d : ℤ × ℤ, ⨆ _ : d.1 + d.2 = n, tensorProductBidegreePiece G H d

private theorem tensorProductPiece_eq_iSup (G : InternalGrading R M)
    (H : InternalGrading R N) (n : ℤ) :
    tensorProductPiece G H n =
      ⨆ p : ℤ, Submodule.map₂ (TensorProduct.mk R M N) (G.piece p) (H.piece (n - p)) := by
  apply le_antisymm
  · refine iSup_le fun d ↦ iSup_le fun hd ↦ ?_
    refine le_iSup_of_le d.1 ?_
    have hdeg : d.2 = n - d.1 := by omega
    simpa only [tensorProductBidegreePiece, hdeg] using
      (le_rfl : Submodule.map₂ (TensorProduct.mk R M N) (G.piece d.1)
        (H.piece (n - d.1)) ≤ _)
  · refine iSup_le fun p ↦ ?_
    refine le_iSup_of_le (p, n - p) ?_
    refine le_iSup_of_le (by omega) ?_
    rfl

end Pieces

section Internal

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The tensor product of internally graded modules, graded by total degree. -/
noncomputable def tensorProduct (G : InternalGrading R M) (H : InternalGrading R N) :
    InternalGrading R (M ⊗[R] N) where
  piece := tensorProductPiece G H
  isInternal := by
    classical
    apply DirectSum.IsInternal.iSup_fiber
    -- Unfold the private bidegree wrapper to match the tensor-product decomposition.
    change DirectSum.IsInternal fun d : ℤ × ℤ ↦
      Submodule.map₂ (TensorProduct.mk R M N) (G.piece d.1) (H.piece d.2)
    -- The reused theorem uses classical decidable equality; `convert` transports the
    -- decompositions across the proof-irrelevant choice of decidable equality on `ℤ`.
    convert DirectSum.IsInternal.tensorProduct G.piece H.piece ?_ ?_ using 1
    · convert G.isInternal
    · convert H.isInternal

/-- The degree-`n` piece of the tensor-product grading is the sum of the tensor-product images
whose first degree is `p` and whose second degree is `n - p`. -/
theorem tensorProduct_piece_eq_iSup (G : InternalGrading R M) (H : InternalGrading R N) (n : ℤ) :
    (G.tensorProduct H).piece n =
      ⨆ p : ℤ, Submodule.map₂ (TensorProduct.mk R M N) (G.piece p) (H.piece (n - p)) :=
  tensorProductPiece_eq_iSup G H n

/-- A pure tensor of elements of degrees `p` and `q` is homogeneous of degree `p + q` in the
tensor-product grading. -/
theorem tmul_mem_tensorProduct (G : InternalGrading R M) (H : InternalGrading R N)
    {p q : ℤ} {x : M} {y : N} (hx : x ∈ G.piece p) (hy : y ∈ H.piece q) :
    x ⊗ₜ[R] y ∈ (G.tensorProduct H).piece (p + q) := by
  rw [tensorProduct_piece_eq_iSup]
  refine Submodule.mem_iSup_of_mem p ?_
  simpa only [add_sub_cancel_left, TensorProduct.mk_apply] using
    Submodule.apply_mem_map₂ (TensorProduct.mk R M N) hx hy

/-- A submodule containing every pure tensor of homogeneous elements of total degree `n` contains
the whole degree-`n` piece of the tensor-product grading. -/
theorem tensorProduct_piece_le (G : InternalGrading R M) (H : InternalGrading R N) {n : ℤ}
    {C : Submodule R (M ⊗[R] N)}
    (h : ∀ p : ℤ, ∀ x ∈ G.piece p, ∀ y ∈ H.piece (n - p), x ⊗ₜ[R] y ∈ C) :
    (G.tensorProduct H).piece n ≤ C := by
  rw [tensorProduct_piece_eq_iSup]
  exact iSup_le fun p ↦ Submodule.map₂_le.2 fun x hx y hy ↦ h p x hx y hy

/-- Reassociating a triple tensor product preserves total degree. -/
theorem isHomogeneous_assoc_symm {P : Type w'} [AddCommMonoid P] [Module R P]
    (G : InternalGrading R M) (H : InternalGrading R N) (K : InternalGrading R P) :
    LinearMap.IsHomogeneous (TensorProduct.assoc R M N P).symm.toLinearMap
      (G.tensorProduct (H.tensorProduct K)).piece ((G.tensorProduct H).tensorProduct K).piece
      0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine G.tensorProduct_piece_le (H.tensorProduct K)
    (C := (((G.tensorProduct H).tensorProduct K).piece (n + 0)).comap
      (TensorProduct.assoc R M N P).symm.toLinearMap) (fun p x hx t ht ↦ ?_) hz
  refine H.tensorProduct_piece_le K
    (C := (((G.tensorProduct H).tensorProduct K).piece (n + 0)).comap
      ((TensorProduct.assoc R M N P).symm.toLinearMap ∘ₗ TensorProduct.mk R M (N ⊗[R] P) x))
    (fun r y hy u hu ↦ ?_) ht
  rw [Submodule.mem_comap, LinearMap.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul]
  have hdeg : n + 0 = p + r + (n - p - r) := by ring
  rw [hdeg]
  exact tmul_mem_tensorProduct _ _ (tmul_mem_tensorProduct G H hx hy) hu

/-- Reassociating a triple tensor product preserves total degree. -/
theorem isHomogeneous_assoc {P : Type w'} [AddCommMonoid P] [Module R P]
    (G : InternalGrading R M) (H : InternalGrading R N) (K : InternalGrading R P) :
    LinearMap.IsHomogeneous (TensorProduct.assoc R M N P).toLinearMap
      ((G.tensorProduct H).tensorProduct K).piece (G.tensorProduct (H.tensorProduct K)).piece
      0 := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (G.tensorProduct H).tensorProduct_piece_le K
    (C := ((G.tensorProduct (H.tensorProduct K)).piece (n + 0)).comap
      (TensorProduct.assoc R M N P).toLinearMap) (fun p t ht u hu ↦ ?_) hz
  refine G.tensorProduct_piece_le H
    (C := ((G.tensorProduct (H.tensorProduct K)).piece (n + 0)).comap
      ((TensorProduct.assoc R M N P).toLinearMap ∘ₗ (TensorProduct.mk R (M ⊗[R] N) P).flip u))
    (fun r x hx y hy ↦ ?_) ht
  rw [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearEquiv.coe_coe, TensorProduct.assoc_tmul]
  have hdeg : n + 0 = r + (p - r + (n - p)) := by ring
  rw [hdeg]
  exact tmul_mem_tensorProduct _ _ hx (tmul_mem_tensorProduct H K hy hu)

end Internal

section KoszulTwist

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The Koszul twist for the total grading of a tensor product is the tensor product of the
Koszul twists of the factors. -/
theorem koszulTwist_tensorProduct (G : InternalGrading R M) (H : InternalGrading R N) (q : ℤ) :
    (G.tensorProduct H).koszulTwist q = TensorProduct.map (G.koszulTwist q) (H.koszulTwist q) := by
  refine TensorProduct.ext (G.linearMap_ext fun p x hx ↦ H.linearMap_ext fun r y hy ↦ ?_)
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, TensorProduct.map_tmul,
    (G.tensorProduct H).koszulTwist_apply_of_mem (tmul_mem_tensorProduct G H hx hy),
    G.koszulTwist_apply_of_mem hx, H.koszulTwist_apply_of_mem hy, TensorProduct.smul_tmul_smul,
    mul_add, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

end KoszulTwist

end InternalGrading

namespace LinearMap.IsHomogeneous

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w} {M' : Type v'} {N' : Type w'}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- Tensoring homogeneous linear maps adds their degrees for the total tensor-product gradings. -/
@[grind →]
theorem tensorProduct {G : InternalGrading R M} {H : InternalGrading R N}
    {G' : InternalGrading R M'} {H' : InternalGrading R N'} {f : M →ₗ[R] M'} {g : N →ₗ[R] N'}
    {a b : ℤ} (hf : LinearMap.IsHomogeneous f G.piece G'.piece a)
    (hg : LinearMap.IsHomogeneous g H.piece H'.piece b) :
    LinearMap.IsHomogeneous (TensorProduct.map f g) (G.tensorProduct H).piece
      (G'.tensorProduct H').piece (a + b) := by
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  rw [InternalGrading.tensorProduct_piece_eq_iSup] at hz
  rw [InternalGrading.tensorProduct_piece_eq_iSup]
  let target := ⨆ p : ℤ,
    Submodule.map₂ (TensorProduct.mk R M' N') (G'.piece p)
      (H'.piece (n + (a + b) - p))
  suffices hmap : z ∈ (target.comap (TensorProduct.map f g)) by
    exact hmap
  have hle :
      (⨆ p : ℤ, Submodule.map₂ (TensorProduct.mk R M N) (G.piece p) (H.piece (n - p))) ≤
        target.comap (TensorProduct.map f g) := by
    refine iSup_le fun p ↦ Submodule.map₂_le.mpr fun x hx y hy ↦ ?_
    rw [Submodule.mem_comap, TensorProduct.mk_apply, TensorProduct.map_tmul]
    refine Submodule.mem_iSup_of_mem (p + a) ?_
    have hfx := hf.map_mem hx
    have hgy := hg.map_mem hy
    have hxy := Submodule.apply_mem_map₂ (TensorProduct.mk R M' N') hfx hgy
    have hdeg : n + (a + b) - (p + a) = n - p + b := by ring
    rw [hdeg]
    simpa only [TensorProduct.mk_apply] using hxy
  exact hle hz

end LinearMap.IsHomogeneous

end TauCeti
