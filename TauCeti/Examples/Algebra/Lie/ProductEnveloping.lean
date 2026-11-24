/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Abelian
public import TauCeti.Algebra.Lie.Sl2.Center
public import TauCeti.Algebra.Lie.UniversalEnveloping.Product.Center
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# Checks for the enveloping algebra of a product with an abelian factor

Checks for `TauCeti.UniversalEnvelopingAlgebra.productEnveloping` and
`TauCeti.UniversalEnvelopingAlgebra.productCenterEquiv`, with abelian factors given by
`TauCeti.AbelianLieAlgebra`:

* for `Z = S = 0`, every element of `U(Z × S)` is a scalar, and `1` maps to `1 ⊗ 1`;
* for `Z = K` and `S = 0`, the degree-one generator `t` maps to `t ⊗ 1`, which is nonzero;
* for `Z = K` and `S = sl₂` over a field of characteristic zero, `t` maps to `t ⊗ 1`, the element
  `Ω = h² + 2h + 4fe` of the second factor maps to `1 ⊗ Ω`, and the centre is `K[t] ⊗ K[Ω]`, with
  `X ⊗ 1 ↦ t` and `1 ⊗ X ↦ Ω`.
-/

public section

open scoped TensorProduct Polynomial
open TauCeti TauCeti.UniversalEnvelopingAlgebra Polynomial

namespace TauCeti.Examples.ProductEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type) [Field K]

local notation "Z0" => AbelianLieAlgebra (PUnit : Type)
local notation "ZK" => AbelianLieAlgebra K
local notation "sl₂" => LieAlgebra.SpecialLinear.sl (Fin 2) K

-- The coordinate `t` on the abelian Lie algebra `K`.
local notation "t" => (LinearEquiv.symm (AbelianLieAlgebra.equiv K K) 1 : ZK)

/-! ### `Z = S = 0` -/

example : productEnveloping K Z0 Z0 1 = 1 ⊗ₜ[K] 1 := map_one _

example (x : UniversalEnvelopingAlgebra K (Z0 × Z0)) : ∃ c : K, x = algebraMap K _ c := by
  have h := adjoin_image_ι_eq_top K (Z0 × Z0) (S := ∅) <| by
    refine eq_top_iff.2 fun x _ ↦ ?_
    have hx : x = 0 := ((AbelianLieAlgebra.equiv K PUnit).prodCongr
      (AbelianLieAlgebra.equiv K PUnit)).injective (Subsingleton.elim _ _)
    exact hx ▸ zero_mem _
  rw [Set.image_empty, Algebra.adjoin_empty] at h
  have hx : x ∈ (⊥ : Subalgebra K _) := h ▸ Algebra.mem_top
  exact (Algebra.mem_bot.1 hx).imp fun _ h ↦ h.symm

/-! ### `Z = K`, `S = 0` -/

example : productEnveloping K ZK Z0 (UniversalEnvelopingAlgebra.ι K (t, 0)) =
    SymmetricAlgebra.ι K ZK t ⊗ₜ[K] 1 := by
  rw [productEnveloping_ι]
  simp

example : SymmetricAlgebra.ι K ZK t ⊗ₜ[K] (1 : UniversalEnvelopingAlgebra K Z0) ≠ 0 := by
  intro h
  let ε : UniversalEnvelopingAlgebra K Z0 →ₐ[K] K := UniversalEnvelopingAlgebra.lift K 0
  have h' := congrArg (Algebra.TensorProduct.rid K K (SymmetricAlgebra K ZK) ∘
    Algebra.TensorProduct.map (AlgHom.id K _) ε) h
  simp only [Function.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one,
    Algebra.TensorProduct.rid_tmul, one_smul, map_zero] at h'
  let b : Module.Basis PUnit.{1} K ZK :=
    (Module.Basis.singleton PUnit.{1} K).map (AbelianLieAlgebra.equiv K K).symm
  have hb : b PUnit.unit.{1} = t := by simp [b]
  have := SymmetricAlgebra.equivMvPolynomial_ι_apply b PUnit.unit.{1}
  rw [hb, h', map_zero] at this
  exact MvPolynomial.X_ne_zero _ this.symm

/-! ### `Z = K`, `S = sl₂` -/

example : productEnveloping K ZK sl₂ (UniversalEnvelopingAlgebra.ι K (t, 0)) =
    SymmetricAlgebra.ι K ZK t ⊗ₜ[K] 1 := by
  rw [productEnveloping_ι]
  simp

example : productEnveloping K ZK sl₂ (map K (LieHom.inr K ZK sl₂) (slTwoOmega K)) =
    1 ⊗ₜ[K] slTwoOmega K :=
  productEnveloping_map_inr K ZK sl₂ _

/-- Over a field of characteristic zero, the centre of `U(K × sl₂)` is `K[t] ⊗ K[Ω]`: an algebra
isomorphism from `K[X] ⊗ K[X]` sending `X ⊗ 1` to the central generator `t` and `1 ⊗ X` to
`Ω = h² + 2h + 4fe` in the second factor. -/
theorem exists_algEquiv_center_prod_slTwo [CharZero K] : ∃ e : K[X] ⊗[K] K[X] ≃ₐ[K]
      Subalgebra.center K (UniversalEnvelopingAlgebra K (ZK × sl₂)),
    (e (X ⊗ₜ[K] 1) : UniversalEnvelopingAlgebra K (ZK × sl₂)) =
        UniversalEnvelopingAlgebra.ι K (t, 0) ∧
      (e (1 ⊗ₜ[K] X) : UniversalEnvelopingAlgebra K (ZK × sl₂)) =
        map K (LieHom.inr K ZK sl₂) (slTwoOmega K) := by
  let b : Module.Basis PUnit.{1} K ZK :=
    (Module.Basis.singleton PUnit.{1} K).map (AbelianLieAlgebra.equiv K K).symm
  let σ : SymmetricAlgebra K ZK ≃ₐ[K] K[X] :=
    (SymmetricAlgebra.equivMvPolynomial b).trans (MvPolynomial.uniqueAlgEquiv K PUnit.{1})
  have hσ : σ.symm X = SymmetricAlgebra.ι K ZK t := by
    have hb : b PUnit.unit.{1} = t := by simp [b]
    rw [AlgEquiv.symm_apply_eq, ← hb]
    simp [σ]
  refine ⟨(Algebra.TensorProduct.congr σ.symm slTwoCenterEquiv).trans
    (productCenterEquiv K ZK sl₂).symm, ?_, ?_⟩
  · simp [productCenterEquiv_symm_tmul, hσ]
  · simp [productCenterEquiv_symm_tmul]

end TauCeti.Examples.ProductEnveloping
