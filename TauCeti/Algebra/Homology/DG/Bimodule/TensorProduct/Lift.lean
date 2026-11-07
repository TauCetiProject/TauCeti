/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Functor

/-!
# Morphisms out of a tensor product of DG bimodules

For a DG `(A, B)`-bimodule `M`, a DG `(B, C)`-bimodule `N` and a DG `(A, C)`-bimodule `P`, a
ground-ring bilinear map `φ : M × N → P` induces a morphism of DG bimodules
`M ⊗_B N ⟶ P`, `m ⊗ n ↦ φ m n`, once it is

* balanced over `B`: `φ (m b) n = φ m (b n)`;
* equivariant for the outer actions: `φ (a m) n = a φ m n` and `φ m (n c) = (φ m n) c`;
* of degree zero: `φ` sends `M^p × N^q` to `P^{p + q}`;
* a derivation: `d (φ m n) = φ (d m) n + (-1)^p φ m (d n)` for `m` of degree `p`.

This is the universal property of the ordinary balanced tensor product, in the category of DG
bimodules; the induced morphism is unique, since morphisms out of a tensor product are
determined by their values on pure tensors (`TauCeti.DGBimoduleCat.tensorObj_hom_ext`).

## Main definitions

* `TauCeti.DGBimoduleCat.tensorLift`: the morphism `M ⊗_B N ⟶ P` induced by `φ`.

## Main results

* `TauCeti.DGBimoduleCat.tensorLift_tmul`: the induced morphism sends `m ⊗ n` to `φ m n`.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGBimoduleCat

universe uR uA uB uC uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  outerSMulCommClass

attribute [local instance] tensorGradedOuterLeft tensorGradedOuterRight

variable {M : DGBimoduleCat.{uR, uA, uB, uM} hA hB} {N : DGBimoduleCat.{uR, uB, uC, uN} hB hC}
  {P : DGBimoduleCat.{uR, uA, uC, uP} hA hC}

-- Transport the graded actions to the internal gradings used by balanced tensors.
local instance tensorLiftGradedSMulModuleRight (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece
      (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance tensorLiftGradedSMulModuleLeft (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    SetLike.GradedSMul ℬ (InternalGrading.ofDecomposition N.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- **The morphism of DG bimodules out of a tensor product** induced by a balanced, outer
equivariant bilinear map of degree zero that is a derivation for the differentials:
`m ⊗ n ↦ φ m n`. -/
def tensorLift (φ : M →ₗ[R] N →ₗ[R] P)
    (hφ : ∀ (b : B) (m : M) (n : N), φ (op b • m) n = φ m (b • n))
    (hφA : ∀ (a : A) (m : M) (n : N), φ (a • m) n = a • φ m n)
    (hφC : ∀ (c : C) (m : M) (n : N), φ m (op c • n) = op c • φ m n)
    (hφmem : ∀ {p q : ℤ} {m : M} {n : N}, m ∈ M.grading p → n ∈ N.grading q →
      φ m n ∈ P.grading (p + q))
    (hφd : ∀ {p : ℤ} {m : M}, m ∈ M.grading p → ∀ n : N,
      P.differential (φ m n) = φ (M.differential m) n + p.negOnePow • φ m (N.differential n)) :
    DGBimoduleHom (tensorObj M N).isDGBimodule P.isDGBimodule := by
  let L := lift φ hφ
  let T : tensorObj M N →ₗ[Cᵐᵒᵖ] P :=
    { toFun := L
      map_add' := map_add L
      map_smul' := fun c z ↦ lift_smul_right Cᵐᵒᵖ φ hφ (fun c m n ↦ by
        rw [← op_unop c]
        exact hφC c.unop m n) c z }
  have hT (z) : T z = L z := rfl
  refine ⟨{ toLinearMap := T, map_mem' := ?_, map_d' := ?_ }, ?_⟩
  · intro p z hz
    rw [hT]
    simpa only [add_zero] using map_mem_of_tmul (𝒜 := ℬ)
      (InternalGrading.ofDecomposition M.grading) (InternalGrading.ofDecomposition N.grading)
      P.grading L 0 (fun {q r m n} hm hn ↦ by
        rw [add_zero, lift_tmul]
        exact hφmem (by simpa only [InternalGrading.ofDecomposition_piece] using hm)
          (by simpa only [InternalGrading.ofDecomposition_piece] using hn))
      (by simpa only [InternalGrading.ofDecomposition_piece] using hz)
  · intro z
    rw [hT, hT]
    induction z using BalancedTensorProduct.induction_on with
    | ha x y hx hy => simp only [map_add, hx, hy]
    | ht m n =>
      induction m using DirectSum.Decomposition.inductionOn M.grading with
      | zero => simp
      | add m m' hm hm' => simp only [add_tmul, map_add, hm, hm']
      | @homogeneous p m =>
        rw [tensorObj_differential_tmul m.2, map_add, map_zsmul_unit]
        simp only [L, lift_tmul]
        exact hφd m.2 n
  · rw [mem_dgBimoduleHomSubmodule]
    intro a z
    exact lift_smul_left A φ hφ hφA a z

/-- The induced morphism on a pure tensor is the bilinear map. -/
@[simp]
theorem tensorLift_tmul (φ : M →ₗ[R] N →ₗ[R] P)
    (hφ : ∀ (b : B) (m : M) (n : N), φ (op b • m) n = φ m (b • n))
    (hφA : ∀ (a : A) (m : M) (n : N), φ (a • m) n = a • φ m n)
    (hφC : ∀ (c : C) (m : M) (n : N), φ m (op c • n) = op c • φ m n)
    (hφmem : ∀ {p q : ℤ} {m : M} {n : N}, m ∈ M.grading p → n ∈ N.grading q →
      φ m n ∈ P.grading (p + q))
    (hφd : ∀ {p : ℤ} {m : M}, m ∈ M.grading p → ∀ n : N,
      P.differential (φ m n) = φ (M.differential m) n + p.negOnePow • φ m (N.differential n))
    (m : M) (n : N) :
    tensorLift φ hφ hφA hφC hφmem hφd (tmul R B m n) = φ m n :=
  lift_tmul φ hφ m n

end TauCeti.DGBimoduleCat

end
