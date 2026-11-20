/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import TauCeti.Algebra.HopfAlgebra.Frobenius
public import TauCeti.Algebra.HopfAlgebra.HopfModule
public import TauCeti.Algebra.HopfAlgebra.Module.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul

/-!
# Existence of cointegrals

The Larson–Sweedler theorem: on a finite-dimensional Hopf algebra `H` over a field, the right
cointegrals form a line. In particular a nonzero right cointegral exists, so the consequences of
one proved in `TauCeti.Algebra.HopfAlgebra.Frobenius` hold unconditionally: the antipode is
bijective, and the left and right integrals of `H` form lines. Applied to the finite dual, the left
cointegrals form a line as well.

The proof makes `H*` a left Hopf module over `H`. The action is `(h • f)(x) = f(S(h) x)`, and
the coaction `f ↦ ∑ f₋₁ ⊗ f₀` is determined by `∑ f₀(x) f₋₁ = ∑ f(x₁) x₂`, so its
coinvariants are exactly the right cointegrals. The fundamental theorem of Hopf modules then
identifies `H ⊗ ∫` with `H*`, and comparing dimensions gives `dim ∫ = 1`.

## Main declarations

* `TauCeti.finrank_rightCointegrals`: the right cointegrals form a line.
* `TauCeti.exists_isRightCointegral_ne_zero`: a nonzero right cointegral exists.
* `TauCeti.HopfAlgebra.antipode_bijective_of_finiteDimensional`: the antipode is bijective.
* `TauCeti.finrank_leftIntegral`, `TauCeti.finrank_rightIntegral`: the integrals form lines.
* `TauCeti.finrank_leftCointegrals`: the left cointegrals form a line.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Theorem 2.1.3.
* M. E. Sweedler, *Hopf Algebras*, Corollary 5.1.6.
-/

public section

open scoped TensorProduct
open Coalgebra

namespace TauCeti

namespace DualHopfModule

variable {k H : Type*} [Field k] [Ring H] [HopfAlgebra k H]

/-- Evaluation of the `H*`-factor of `V ⊗ H*` at `x : H`. -/
private noncomputable def evalAt (V : Type*) [AddCommGroup V] [Module k V] (x : H) :
    V ⊗[k] Module.Dual k H →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap ∘ₗ (Module.Dual.eval k H x).lTensor V

private theorem evalAt_tmul {V : Type*} [AddCommGroup V] [Module k V] (x : H) (v : V)
    (f : Module.Dual k H) : evalAt V x (v ⊗ₜ f) = f x • v := by
  simp [evalAt]

private theorem evalAt_comm {V : Type*} [AddCommGroup V] [Module k V] (x : H)
    (w : Module.Dual k H ⊗[k] V) :
    evalAt V x (TensorProduct.comm k _ V w) = dualTensorHom k H V w x := by
  induction w with
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  | tmul f v => simp [evalAt_tmul]

private theorem evalAt_rTensor {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (g : V →ₗ[k] W) (x : H) (u : V ⊗[k] Module.Dual k H) :
    evalAt W x (g.rTensor _ u) = g (evalAt V x u) := by
  induction u with
  | add u w hu hw => simp only [map_add, hu, hw]
  | tmul v f => simp [evalAt_tmul]

/-- Matrix coefficients of the regular comodule are the contractions `∑ f(x₁) x₂`. -/
private theorem matrixCoefficient_self (f : Module.Dual k H) (x : H) :
    Comodule.matrixCoefficient (R := k) (C := H) f x =
      TensorProduct.lid k H (f.rTensor H (comul x)) :=
  Comodule.matrixCoefficient_def f x

/-- The `H`-identity behind `H`-linearity of the coaction on `H*`:
`∑ h₁ (∑ f(S(h₂) x)₁ (S(h₂) x)₂) = ∑ f(S(h) x₁) x₂`. -/
private theorem sum_mul_matrixCoefficient_antipode_mul (f : Module.Dual k H) (h x : H) :
    ∑ i ∈ (ℛ k h).index, (ℛ k h).left i *
      Comodule.matrixCoefficient (R := k) (C := H) f
        (HopfAlgebra.antipode k ((ℛ k h).right i) * x) =
      Comodule.matrixCoefficient (R := k) (C := H) ((Algebra.lsmul k k H).hopfDual h f) x := by
  set r := ℛ k h
  set q := ℛ k x
  -- `Γ (p ⊗ u ⊗ y) = ∑ f(S(y) x₁) • p S(u) x₂` turns both sides into coassociativity of `Δ`.
  let Γ : H ⊗[k] (H ⊗[k] H) →ₗ[k] H := ∑ m ∈ q.index,
    (TensorProduct.rid k H).toLinearMap ∘ₗ
      TensorProduct.map
        (LinearMap.mul' k H ∘ₗ
          (LinearMap.mulRight k (q.right m) ∘ₗ HopfAlgebra.antipode k).lTensor H)
        (f ∘ₗ LinearMap.mulRight k (q.left m) ∘ₗ HopfAlgebra.antipode k) ∘ₗ
      (TensorProduct.assoc k H H H).symm.toLinearMap
  have hΓ (p u y : H) : Γ (p ⊗ₜ (u ⊗ₜ y)) = ∑ m ∈ q.index,
      f (HopfAlgebra.antipode k y * q.left m) •
        (p * (HopfAlgebra.antipode k u * q.right m)) := by
    simp [Γ]
  calc _ = ∑ i ∈ r.index, ∑ j ∈ (ℛ k (r.right i)).index,
        Γ (r.left i ⊗ₜ ((ℛ k (r.right i)).left j ⊗ₜ (ℛ k (r.right i)).right j)) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [matrixCoefficient_self, Bialgebra.comul_mul,
          TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, ← (ℛ k (r.right i)).eq, ← q.eq]
        simp only [map_sum, hΓ]
        simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, Finset.mul_sum, Finset.sum_mul,
          Algebra.TensorProduct.tmul_mul_tmul, map_sum, LinearMap.rTensor_tmul,
          TensorProduct.lid_tmul, Algebra.mul_smul_comm]
        exact Finset.sum_comm
    _ = ∑ i ∈ r.index, ∑ j ∈ (ℛ k (r.left i)).index,
        Γ ((ℛ k (r.left i)).left j ⊗ₜ ((ℛ k (r.left i)).right j ⊗ₜ r.right i)) := by
        simpa only [map_sum] using (congrArg Γ (sum_tmul_tmul_eq r (fun i ↦ ℛ k (r.left i))
          (fun i ↦ ℛ k (r.right i)))).symm
    _ = ∑ i ∈ r.index, ∑ m ∈ q.index,
        f (HopfAlgebra.antipode k (r.right i) * q.left m) •
          (counit (R := k) (r.left i) • q.right m) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [hΓ]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        simp_rw [← mul_assoc, ← Finset.smul_sum, ← Finset.sum_mul,
          HopfAlgebra.sum_mul_antipode_eq_smul, smul_one_mul]
    _ = _ := by
        rw [matrixCoefficient_self, ← q.eq]
        conv_rhs => rw [← Coalgebra.sum_counit_smul r]
        simp only [smul_smul, mul_comm, map_sum, map_smul, LinearMap.coe_sum, LinearMap.coe_smul,
          Finset.sum_apply, Pi.smul_apply, LinearMap.rTensor_tmul, AlgHom.hopfDual_apply,
          Algebra.lsmul_coe, smul_eq_mul,
          TensorProduct.lid_tmul]
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_smul]

/-- `H*` as a left `H`-module through the contragredient of the regular representation,
`(h • f)(x) = f(S(h) x)`. The action involves the antipode and is not canonical, so it is
only a local instance, used to apply the fundamental theorem of Hopf modules. -/
private noncomputable abbrev instModule : Module H (Module.Dual k H) :=
  Module.compHom _ (Algebra.lsmul k k H).hopfDual.toRingHom

attribute [local instance] instModule

private theorem smul_def (h : H) (f : Module.Dual k H) :
    h • f = (Algebra.lsmul k k H).hopfDual h f :=
  (rfl)

private theorem isScalarTower : IsScalarTower k H (Module.Dual k H) :=
  ⟨fun c h f ↦ by simp [smul_def]⟩

attribute [local instance] isScalarTower

private theorem evalAt_tensorAction (h x : H) (u : H ⊗[k] Module.Dual k H) :
    evalAt H x (BialgebraModule.tensorAction k H H (Module.Dual k H) h u) =
      ∑ i ∈ (ℛ k h).index, (ℛ k h).left i *
        evalAt H (HopfAlgebra.antipode k ((ℛ k h).right i) * x) u := by
  induction u with
  | add u w hu hw => simp only [map_add, hu, hw, mul_add, Finset.sum_add_distrib]
  | tmul a g =>
    rw [BialgebraModule.tensorAction_apply, ← (ℛ k h).eq]
    simp [map_sum, evalAt_tmul, smul_def, AlgHom.hopfDual_apply, Algebra.lsmul_coe]

variable [FiniteDimensional k H]

/-- Tensors in `V ⊗ H*` are determined by their evaluations at all `x : H`. -/
private theorem eq_of_evalAt {V : Type*} [AddCommGroup V] [Module k V]
    {u u' : V ⊗[k] Module.Dual k H} (h : ∀ x, evalAt V x u = evalAt V x u') : u = u' := by
  apply (TensorProduct.comm k (Module.Dual k H) V).symm.injective
  apply dualTensorHom_bijective.1
  ext x
  simpa [← evalAt_comm] using h x

/-- The coaction `f ↦ ∑ f₋₁ ⊗ f₀` on `H*`, characterized by `∑ f₀(x) f₋₁ = ∑ f(x₁) x₂`. -/
private noncomputable def coact : Module.Dual k H →ₗ[k] H ⊗[k] Module.Dual k H :=
  (TensorProduct.comm k (Module.Dual k H) H).toLinearMap ∘ₗ
    (dualTensorHomEquiv k H H).symm.toLinearMap ∘ₗ
    Comodule.matrixCoefficientBilinear (R := k) (C := H) (M := H)

private theorem evalAt_coact (f : Module.Dual k H) (x : H) :
    evalAt H x (coact f) = Comodule.matrixCoefficient (R := k) (C := H) f x := by
  simp [coact, evalAt_comm]

private theorem comm_symm_coact (f : Module.Dual k H) :
    dualTensorHom k H H ((TensorProduct.comm k (Module.Dual k H) H).symm (coact f)) =
      Comodule.matrixCoefficientLinear (R := k) (C := H) f := by
  simp [coact]

private theorem evalAt_assoc_symm_lTensor_coact (x : H) (u : H ⊗[k] Module.Dual k H) :
    evalAt (H ⊗[k] H) x ((TensorProduct.assoc k H H (Module.Dual k H)).symm
      (coact.lTensor H u)) =
      (dualTensorHom k H H ((TensorProduct.comm k (Module.Dual k H) H).symm u)).rTensor H
        (comul x) := by
  induction u with
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, LinearMap.rTensor_add, hu, hw]
  | tmul a g =>
    have hassoc (w : H ⊗[k] Module.Dual k H) :
        evalAt (H ⊗[k] H) x ((TensorProduct.assoc k H H (Module.Dual k H)).symm (a ⊗ₜ w)) =
          a ⊗ₜ evalAt H x w := by
      induction w with
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
      | tmul b f => simp [evalAt_tmul]
    rw [LinearMap.lTensor_tmul, hassoc, evalAt_coact, matrixCoefficient_self]
    generalize comul (R := k) x = z
    induction z with
    | add z z' hz hz' => simp only [map_add, TensorProduct.tmul_add, hz, hz']
    | tmul p q => simp [TensorProduct.smul_tmul]

private theorem coact_coassoc :
    TensorProduct.assoc k H H (Module.Dual k H) ∘ₗ comul.rTensor (Module.Dual k H) ∘ₗ coact =
      coact.lTensor H ∘ₗ coact := by
  ext f : 1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← LinearEquiv.eq_symm_apply]
  refine eq_of_evalAt fun x ↦ ?_
  rw [evalAt_assoc_symm_lTensor_coact, evalAt_rTensor, evalAt_coact, comm_symm_coact,
    Comodule.comul_matrixCoefficient, Comodule.instSelf_coact, LinearMap.rTensor_def]

private theorem coact_counit :
    TensorProduct.lid k (Module.Dual k H) ∘ₗ counit.rTensor (Module.Dual k H) ∘ₗ coact =
      LinearMap.id := by
  have key (u : H ⊗[k] Module.Dual k H) (x : H) :
      TensorProduct.lid k (Module.Dual k H) (counit.rTensor (Module.Dual k H) u) x =
        counit (R := k) (evalAt H x u) := by
    induction u with
    | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
    | tmul a g => simp [evalAt_tmul, mul_comm]
  ext f x
  simp [key, evalAt_coact, Comodule.counit_matrixCoefficient]

/-- `H*` is a left Hopf module over `H`. -/
private theorem isHopfModule_coact : IsHopfModule (coact (k := k) (H := H)) where
  coassoc := coact_coassoc
  lid_rTensor_counit := coact_counit
  map_smul h f := eq_of_evalAt fun x ↦ by
    rw [evalAt_tensorAction, evalAt_coact, smul_def]
    simp only [evalAt_coact]
    exact (sum_mul_matrixCoefficient_antipode_mul f h x).symm

/-- The coinvariants of `H*` are the right cointegrals. -/
private theorem coinvariants_coact :
    HopfModule.coinvariants (coact (k := k) (H := H)) = rightCointegrals k H := by
  ext f
  rw [HopfModule.mem_coinvariants, mem_rightCointegrals, isRightCointegral_def]
  constructor
  · intro hf x
    have := congrArg (evalAt H x) hf
    rwa [evalAt_coact, evalAt_tmul, matrixCoefficient_self] at this
  · intro hf
    refine eq_of_evalAt fun x ↦ ?_
    rw [evalAt_coact, evalAt_tmul, matrixCoefficient_self, hf x]

/-- The fundamental theorem of Hopf modules for `H*`: `H ⊗ ∫ ≃ H*`, where `∫` is the space of
right cointegrals. -/
private noncomputable def tensorRightCointegralsEquiv :
    H ⊗[k] rightCointegrals k H ≃ₗ[k] Module.Dual k H :=
  (LinearEquiv.ofEq _ _ coinvariants_coact).symm.lTensor H ≪≫ₗ
    isHopfModule_coact.tensorCoinvariantsEquiv

end DualHopfModule

variable {k H : Type*} [Field k] [Ring H] [HopfAlgebra k H]

open DualHopfModule in
/-- **Larson–Sweedler**: the right cointegrals of a finite-dimensional Hopf algebra over a field
form a line. -/
theorem finrank_rightCointegrals [FiniteDimensional k H] :
    Module.finrank k (rightCointegrals k H) = 1 := by
  -- Generalize the submodule: `Module.Free` is found for an arbitrary subspace of `H*`.
  suffices ∀ p : Submodule k (Module.Dual k H), (H ⊗[k] p ≃ₗ[k] Module.Dual k H) →
      Module.finrank k p = 1 from this _ tensorRightCointegralsEquiv
  intro p e
  have := Module.Free.of_divisionRing k p
  have h := e.finrank_eq
  rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq] at h
  have : Nontrivial H := Bialgebra.nontrivial k
  have hpos : 0 < Module.finrank k H := Module.finrank_pos
  nlinarith [h]

/-- A nonzero right cointegral exists on every finite-dimensional Hopf algebra over a field. -/
theorem exists_isRightCointegral_ne_zero [FiniteDimensional k H] :
    ∃ φ : Module.Dual k H, IsRightCointegral φ ∧ φ ≠ 0 := by
  have hne : rightCointegrals k H ≠ ⊥ := by
    intro h
    have h1 := finrank_rightCointegrals (k := k) (H := H)
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨φ, (mem_rightCointegrals φ).mp hφ, h0⟩

/-- **Larson–Sweedler**: the antipode of a finite-dimensional Hopf algebra over a field is
bijective. -/
theorem HopfAlgebra.antipode_bijective_of_finiteDimensional [FiniteDimensional k H] :
    Function.Bijective (HopfAlgebra.antipode k : H → H) := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero (k := k) (H := H)
  exact (isRightCointegral_iff_isRightInvariantIntegral.mp hφ).antipode_bijective h0

/-- **Larson–Sweedler**: the left integrals of a finite-dimensional Hopf algebra over a field
form a line. -/
theorem finrank_leftIntegral [FiniteDimensional k H] :
    Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero (k := k) (H := H)
  exact ((isRightCointegral_iff_isRightInvariantIntegral.mp hφ).isFrobeniusFunctional
    h0).finrank_leftIntegral

/-- **Larson–Sweedler**: the right integrals of a finite-dimensional Hopf algebra over a field
form a line. -/
theorem finrank_rightIntegral [FiniteDimensional k H] :
    Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero (k := k) (H := H)
  exact ((isRightCointegral_iff_isRightInvariantIntegral.mp hφ).isFrobeniusFunctional
    h0).finrank_rightIntegral

/-- **Larson–Sweedler**: the left cointegrals of a finite-dimensional Hopf algebra over a field
form a line. They are the left integrals of the finite dual. -/
theorem finrank_leftCointegrals [FiniteDimensional k H] :
    Module.finrank k (leftCointegrals k H) = 1 := by
  let e : leftCointegrals k H ≃ₗ[k] leftIntegral k (ConvolutionDual k H) :=
    (WithConv.linearEquiv k (Module.Dual k H)).symm.ofSubmodules _ _ (by
      ext t
      rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_leftIntegral_iff]
      simp [isLeftCointegral_iff_convMul])
  rw [e.finrank_eq]
  exact finrank_leftIntegral

end TauCeti
