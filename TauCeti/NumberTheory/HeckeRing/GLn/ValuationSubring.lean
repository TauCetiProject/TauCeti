/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan.ValuationSubring
public import TauCeti.NumberTheory.HeckeRing.GLn.FractionRing
public import TauCeti.RepresentationTheory.HeckeAlgebra.GelfandTrick

/-!
# Gelfand's trick for `GL_n` over a valuation subring

Let `O : ValuationSubring F` be a valuation subring of a field `F`, and let
`K = HeckeRing.GLn.integralGL O F n` be the subgroup of `O`-integral matrices in `GL n F`.
Combining Cartan diagonalization over `O` (`ValuationSubring.exists_mul_diagonal_mul`) with
inverse transpose (`Matrix.GeneralLinearGroup.inverseTranspose`), we establish:

* `ValuationSubring.exists_inverseTranspose_inv_eq`: every `g : GL n F` satisfies
  `inverseTranspose g⁻¹ = inverseTranspose k * g * k` for some `k ∈ integralGL O F n`.
* `ValuationSubring.exists_inverseTranspose_inv_mem_doubleCoset`: every `g : GL n F` satisfies
  `inverseTranspose g⁻¹ ∈ integralGL O F n * g * integralGL O F n`.
* `Subgroup.IsHeckeFunction.dual_integralGL`: the dual `g ↦ σ (f g⁻¹)` of a Hecke function for
  `integralGL O F n` is again a Hecke function.
* `Subgroup.IsHeckeFunction.heckeOp_adjoint_integralGL`: adjointness of spherical Hecke operators
  for `(GL n F, integralGL O F n)`.
* `Subgroup.IsHeckeFunction.heckeConv_comm_integralGL`: commutativity of Hecke convolution for
  `(GL n F, integralGL O F n)`.
* `Subgroup.IsHeckeFunction.heckeOp_comm_integralGL`: commutativity of spherical Hecke operators
  on `integralGL O F n`-fixed vectors.

## References

* J. Tits, *Reductive groups over local fields*, Automorphic Forms, Representations and
  L-Functions, Proc. Sympos. Pure Math. 33 (1979), §3.3.3.
* T. Tamagawa, *On the ζ-functions of a division algebra*, Ann. of Math. **77** (1963), 387–405.
* Adapted from `src/Lib/General/LinearAlgebra/IntegralLattices.lean` in `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup HeckeRing.GLn

universe u

namespace ValuationSubring

/-- **Gelfand's double-coset condition for `GL_n(F)` over a valuation subring `O`.**
For every `g ∈ GL n F`, there is `k ∈ integralGL O F n` such that `gᵀ = (kᵀ)⁻¹ * g * k`
(written via `inverseTranspose g⁻¹ = inverseTranspose k * g * k`). -/
theorem exists_inverseTranspose_inv_eq {n : Type u} [Fintype n] [DecidableEq n] {F : Type*}
    [Field F] (O : ValuationSubring F) (g : GL n F) :
    ∃ k ∈ integralGL O F n, inverseTranspose g⁻¹ = inverseTranspose k * g * k := by
  obtain ⟨k₀, l₀, d, h_smith⟩ := O.exists_mul_diagonal_mul g.val
  set k : GL n F := GeneralLinearGroup.map (algebraMap O F) k₀
  set l : GL n F := GeneralLinearGroup.map (algebraMap O F) l₀
  have hk : k ∈ integralGL O F n := ⟨k₀, rfl⟩
  have hl : l ∈ integralGL O F n := ⟨l₀, rfl⟩
  refine ⟨l⁻¹ * (transposeMulEquiv n k).unop,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) (transposeMulEquiv_mem_integralGL hk), Units.ext ?_⟩
  simp only [map_mul, unop_transposeMulEquiv_eq_inverseTranspose_inv,
    inverseTranspose_inverseTranspose, Units.val_mul, coe_inverseTranspose, inv_inv, h_smith,
    transpose_mul, diagonal_transpose, Matrix.mul_assoc]
  have hcancel : (k⁻¹).val * (k.val * (diagonal d * (l.val * ((l⁻¹).val * k.valᵀ)))) =
      diagonal d * k.valᵀ := by
    calc (k⁻¹).val * (k.val * (diagonal d * (l.val * ((l⁻¹).val * k.valᵀ))))
        = ((k⁻¹).val * k.val) * (diagonal d * ((l.val * (l⁻¹).val) * k.valᵀ)) := by
            simp only [Matrix.mul_assoc]
      _ = diagonal d * k.valᵀ := by simp
  rw [hcancel]

/-- For every `g ∈ GL n F`, `inverseTranspose g⁻¹` lies in the double coset
`integralGL O F n * g * integralGL O F n`. -/
theorem exists_inverseTranspose_inv_mem_doubleCoset {n : Type u} [Fintype n] [DecidableEq n]
    {F : Type*} [Field F] (O : ValuationSubring F) (g : GL n F) :
    ∃ a ∈ integralGL O F n, ∃ b ∈ integralGL O F n, inverseTranspose g⁻¹ = a * g * b := by
  obtain ⟨k, hk, h⟩ := O.exists_inverseTranspose_inv_eq g
  exact ⟨inverseTranspose k, inverseTranspose_mem_integralGL_iff.2 hk, k, hk, h⟩

end ValuationSubring

section GLnValuation

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The dual `g ↦ σ (f g⁻¹)` of a Hecke function for `(GL n F, integralGL O F n)` is again a
Hecke function. -/
theorem Subgroup.IsHeckeFunction.dual_integralGL {A F : Type*} [CommSemiring A] [Field F]
    (O : ValuationSubring F) {f : GL n F → A} (hf : (integralGL O F n).IsHeckeFunction f)
    (σ : A →+* A) :
    (integralGL O F n).IsHeckeFunction (fun g ↦ σ (f g⁻¹)) :=
  hf.dual σ inverseTranspose O.exists_inverseTranspose_inv_mem_doubleCoset

/-- **Gelfand's trick (adjointness) for `GL_n(F)` over a valuation subring `O`.** -/
theorem Subgroup.IsHeckeFunction.heckeOp_adjoint_integralGL {A W W' Z F : Type*} [CommSemiring A]
    [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W'] [AddCommMonoid Z] [Module A Z]
    [Field F] (O : ValuationSubring F) {f : GL n F → A}
    (hf : (integralGL O F n).IsHeckeFunction f) {σ : A →+* A}
    {π : Representation A (GL n F) W} {π' : Representation A (GL n F) W'}
    (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v : W} {v' : W'}
    (hv : ∀ k ∈ integralGL O F n, π k v = v)
    (hv' : ∀ k ∈ integralGL O F n, π' k v' = v')
    (hB : ∀ (g : GL n F) (x : W) (y : W'), B (π g x) (π' g y) = B x y) :
    B (π.heckeOp (integralGL O F n) f v) v' =
      B v (π'.heckeOp (integralGL O F n) (fun g ↦ σ (f g⁻¹)) v') :=
  hf.heckeOp_adjoint inverseTranspose O.exists_inverseTranspose_inv_mem_doubleCoset B hv hv' hB

/-- **Gelfand's trick (commutativity of convolution) for `GL_n(F)` over a valuation subring `O`.**
-/
theorem Subgroup.IsHeckeFunction.heckeConv_comm_integralGL {A F : Type*} [CommSemiring A] [Field F]
    (O : ValuationSubring F) {f f' : GL n F → A}
    (hf : (integralGL O F n).IsHeckeFunction f)
    (hf' : (integralGL O F n).IsHeckeFunction f') :
    (integralGL O F n).heckeConv f f' = (integralGL O F n).heckeConv f' f :=
  hf.heckeConv_comm hf' inverseTranspose O.exists_inverseTranspose_inv_mem_doubleCoset

/-- **Gelfand's trick (commutativity) for `GL_n(F)` over a valuation subring `O`.** -/
theorem Subgroup.IsHeckeFunction.heckeOp_comm_integralGL {A W F : Type*} [CommSemiring A]
    [AddCommMonoid W] [Module A W] [Field F] (O : ValuationSubring F) {f f' : GL n F → A}
    {π : Representation A (GL n F) W} {v : W}
    (hf : (integralGL O F n).IsHeckeFunction f)
    (hf' : (integralGL O F n).IsHeckeFunction f')
    (hv : ∀ k ∈ integralGL O F n, π k v = v) :
    π.heckeOp (integralGL O F n) f (π.heckeOp (integralGL O F n) f' v) =
      π.heckeOp (integralGL O F n) f' (π.heckeOp (integralGL O F n) f v) :=
  hf.heckeOp_comm hf' hv inverseTranspose O.exists_inverseTranspose_inv_mem_doubleCoset

end GLnValuation

end
