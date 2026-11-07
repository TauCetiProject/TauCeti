/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Functor

/-!
# Maps out of a tensor product of DG bimodules

A balanced bilinear map which respects the outer actions, total degree, and tensor differential
induces a closed degree-zero bimodule morphism. This is the elementwise universal property of
the ordinary DG bimodule tensor product; no flatness or derived-tensor assertion is involved.

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
  {M : DGBimoduleCat.{uR, uA, uB, uM} hA hB}
  {N : DGBimoduleCat.{uR, uB, uC, uN} hB hC}
  {P : DGBimoduleCat.{uR, uA, uC, uP} hA hC}

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  outerSMulCommClass
attribute [local instance] tensorGradedOuterLeft tensorGradedOuterRight

local instance tensorLiftGradedSMulRight :
    SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece
    (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance tensorLiftGradedSMulLeft :
    SetLike.GradedSMul ℬ (InternalGrading.ofDecomposition N.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Lift a balanced bilinear map respecting the outer actions, degrees, and differential
through the ordinary DG tensor product. The differential condition only needs a homogeneous
first input, as in the tensor Leibniz formula. -/
def tensorLift (f : M →ₗ[R] N →ₗ[R] P)
    (hb : ∀ (b : B) m n, f (op b • m) n = f m (b • n))
    (ha : ∀ (a : A) m n, f (a • m) n = a • f m n)
    (hc : ∀ (c : C) m n, f m (op c • n) = op c • f m n)
    (hg : ∀ {p q : ℤ} {m n}, m ∈ M.grading p → n ∈ N.grading q →
      f m n ∈ P.grading (p + q))
    (hd : ∀ {p : ℤ} {m}, m ∈ M.grading p → ∀ n,
      P.differential (f m n) = f (M.differential m) n +
        p.negOnePow • f m (N.differential n)) :
    DGBimoduleHom (tensorObj M N).isDGBimodule P.isDGBimodule := by
  let F : tensorObj M N →ₗ[Cᵐᵒᵖ] P :=
    { toFun := lift f hb
      map_add' := map_add _
      map_smul' c z := lift_smul_right Cᵐᵒᵖ f hb (fun c m n ↦ hc c.unop m n) c z }
  have hF (z) : F z = lift f hb z := rfl
  refine ⟨{ toLinearMap := F, map_mem' := ?_, map_d' := ?_ }, ?_⟩
  · intro p z hz
    rw [hF]
    have h := map_mem_of_tmul (𝒜 := ℬ)
      (InternalGrading.ofDecomposition M.grading) (InternalGrading.ofDecomposition N.grading)
      P.grading (lift f hb) 0 (fun hm hn ↦ by
        rw [InternalGrading.ofDecomposition_piece] at hm hn
        rw [lift_tmul]
        simpa only [add_zero] using hg hm hn) hz
    simpa only [add_zero] using h
  · intro z
    rw [hF, hF]
    induction z using BalancedTensorProduct.induction_on with
    | ht m n =>
      induction m using DirectSum.Decomposition.inductionOn M.grading with
      | zero => simp
      | @homogeneous p m =>
        rw [lift_tmul, tensorObj_differential_tmul m.2, map_add, map_zsmul_unit,
          lift_tmul, lift_tmul]
        exact hd m.2 n
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | ha x y hx hy => simp only [map_add, hx, hy]
  · rw [mem_dgBimoduleHomSubmodule]
    intro a z
    exact lift_smul_left A f hb ha a z

/-- The induced DG bimodule map evaluates a pure tensor by the given bilinear map. -/
@[simp↓]
theorem tensorLift_tmul (f : M →ₗ[R] N →ₗ[R] P) (hb ha hc hg hd) (m : M) (n : N) :
    tensorLift f hb ha hc hg hd (tmul R B m n) = f m n := by
  exact lift_tmul f hb m n

end TauCeti.DGBimoduleCat
