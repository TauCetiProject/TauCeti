/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ModuleAlgebra.Basic

/-!
# Covariance and compatible actions for left module algebras

Let `H` be an `R`-bialgebra and `A` a left `H`-module algebra (`TauCeti.LeftModuleAlgebra R H A`).
An `R`-algebra map `fA : A →ₐ[R] C` and an `R`-algebra map `fH : H →ₐ[R] C` form a covariant
pair (`TauCeti.LeftModuleAlgebra.SmashCompatible`) when they satisfy the smash-product commutation
relation

`fH h * fA a = ∑ fA (h₁ · a) * fH h₂`.

Specializing `C` to `Module.End R M` gives the notion of compatible `A`- and `H`-module
structures on an `R`-module `M` (`TauCeti.LeftModuleAlgebra.IsCompatibleAction`), expressing the
smash-product Leibniz law `h • (a • m) = ∑ (h₁ · a) • (h₂ • m)` independently of the smash-product
construction.

## Main definitions

* `TauCeti.LeftModuleAlgebra.SmashCompatible`: covariance relation between `R`-algebra maps out of
  `A` and `H` into a common `R`-algebra `C`.
* `TauCeti.LeftModuleAlgebra.IsCompatibleAction`: predicate on `R`-compatible `Module A M` and
  `Module H M` instances expressing the smash-product Leibniz law via `SmashCompatible`.

## Main results

* `TauCeti.LeftModuleAlgebra.SmashCompatible.mul_eq_sum` and
  `TauCeti.LeftModuleAlgebra.smashCompatible_iff_sum`: Sweedler-form characterizations of
  `SmashCompatible` in any `Coalgebra.Repr`.
* `TauCeti.LeftModuleAlgebra.SmashCompatible.comp` and
  `TauCeti.LeftModuleAlgebra.SmashCompatible.includeLeft_map_comul`: closure of `SmashCompatible`
  under post-composition and right tensoring with `H` via comultiplication.
* `TauCeti.LeftModuleAlgebra.smashCompatible_lsmul_action`: left multiplication by `A` and
  `μ.action` form a `SmashCompatible` pair in `Module.End R A`.
* `TauCeti.LeftModuleAlgebra.IsCompatibleAction.smul_smul_eq_sum` and
  `TauCeti.LeftModuleAlgebra.isCompatibleAction_iff_sum`: Sweedler-form characterizations of
  `IsCompatibleAction` in any `Coalgebra.Repr`.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §4.1.
* Y. Qi, *Hopfological algebra*, Example 2.8 and §5.1.
-/

public section

open scoped TensorProduct Coalgebra
open Coalgebra

namespace TauCeti

namespace LeftModuleAlgebra

universe u v w

section Semiring

variable {R : Type u} {H : Type v} {A : Type w}
  [CommSemiring R] [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A]

/-! ### Covariant pairs of algebra homomorphisms -/

/-- Compatibility of algebra maps `fA : A →ₐ[R] C` and `fH : H →ₐ[R] C` for descending to
the smash product `A # H`: for every `h : H` and `a : A`,
`fH h * fA a = ∑ fA (h₁ · a) * fH h₂`. -/
def SmashCompatible (μ : LeftModuleAlgebra R H A) {C : Type*} [Semiring C] [Algebra R C]
    (fA : A →ₐ[R] C) (fH : H →ₐ[R] C) : Prop :=
  ∀ h a, fH h * fA a =
    LinearMap.mul' R C
      (TensorProduct.map (fA.toLinearMap ∘ₗ μ.action.toLinearMap.flip a) fH.toLinearMap
        (Coalgebra.comul (R := R) h))

/-- The covariance relation in any finite representation of `comul h`. -/
theorem SmashCompatible.mul_eq_sum {μ : LeftModuleAlgebra R H A} {C : Type*}
    [Semiring C] [Algebra R C] {fA : A →ₐ[R] C} {fH : H →ₐ[R] C}
    (hf : μ.SmashCompatible fA fH) {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) :
    fH h * fA a = ∑ i ∈ r.index, fA (μ.action (r.left i) a) * fH (r.right i) := by
  rw [hf h a, ← r.eq, map_sum, map_sum]
  simp

/-- Characterization of `SmashCompatible` using a family of finite coproduct representations. -/
theorem smashCompatible_iff_sum (μ : LeftModuleAlgebra R H A) {C : Type*}
    [Semiring C] [Algebra R C] (fA : A →ₐ[R] C) (fH : H →ₐ[R] C)
    {ι : H → Type*} (r : ∀ h, Coalgebra.Repr R h (ι h)) :
    μ.SmashCompatible fA fH ↔ ∀ h a,
      fH h * fA a = ∑ i ∈ (r h).index, fA (μ.action ((r h).left i) a) * fH ((r h).right i) := by
  refine ⟨fun hf h a => hf.mul_eq_sum (r h) a, fun hf h a => ?_⟩
  rw [hf h a, ← (r h).eq, map_sum, map_sum]
  simp

/-- Post-composing a `SmashCompatible` pair with an `R`-algebra homomorphism yields a
`SmashCompatible` pair. -/
theorem SmashCompatible.comp {μ : LeftModuleAlgebra R H A} {C D : Type*}
    [Semiring C] [Algebra R C] [Semiring D] [Algebra R D] {fA : A →ₐ[R] C} {fH : H →ₐ[R] C}
    (hf : μ.SmashCompatible fA fH) (φ : C →ₐ[R] D) :
    μ.SmashCompatible (φ.comp fA) (φ.comp fH) := by
  rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
  intro h a
  simpa only [AlgHom.comp_apply, map_mul, map_sum] using congrArg φ (hf.mul_eq_sum (ℛ R h) a)

/-- Tensoring a `SmashCompatible` pair `(fA, fH)` on the right with an `R`-algebra homomorphism
`gH : H →ₐ[R] D` via the comultiplication of `H` yields a `SmashCompatible` pair in `C ⊗[R] D`. -/
theorem SmashCompatible.includeLeft_map_comul {μ : LeftModuleAlgebra R H A} {C D : Type*}
    [Semiring C] [Algebra R C] [Semiring D] [Algebra R D] {fA : A →ₐ[R] C} {fH : H →ₐ[R] C}
    (hf : μ.SmashCompatible fA fH) (gH : H →ₐ[R] D) :
    μ.SmashCompatible (Algebra.TensorProduct.includeLeft.comp fA)
      ((Algebra.TensorProduct.map fH gH).comp (Bialgebra.comulAlgHom R H)) := by
  rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
  intro h a
  set r := ℛ R h
  let r₁ := fun i => ℛ R (r.left i)
  let r₂ := fun i => ℛ R (r.right i)
  let Φ : H ⊗[R] (H ⊗[R] H) →ₗ[R] C ⊗[R] D :=
    TensorProduct.map
      (LinearMap.mul' R C ∘ₗ
        TensorProduct.map (fA.toLinearMap ∘ₗ μ.action.toLinearMap.flip a) fH.toLinearMap)
      gH.toLinearMap ∘ₗ (TensorProduct.assoc R H H H).symm.toLinearMap
  have hco := congrArg Φ (Coalgebra.sum_tmul_tmul_eq r r₁ r₂)
  simp only [Φ, map_sum, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul, LinearMap.flip_apply,
    AlgHom.toLinearMap_apply, LinearMap.mul'_apply] at hco
  calc ((Algebra.TensorProduct.map fH gH).comp (Bialgebra.comulAlgHom R H)) h *
          (Algebra.TensorProduct.includeLeft.comp fA) a
      = (∑ i ∈ r.index, fH (r.left i) ⊗ₜ[R] gH (r.right i)) * (fA a ⊗ₜ[R] 1) := by
          simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← r.eq, map_sum,
            Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeft_apply]
    _ = ∑ i ∈ r.index, ∑ j ∈ (r₁ i).index,
          (fA (μ.action ((r₁ i).left j) a) * fH ((r₁ i).right j)) ⊗ₜ[R] gH (r.right i) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hf.mul_eq_sum (r₁ i) a,
            TensorProduct.sum_tmul]
    _ = ∑ i ∈ r.index, ∑ j ∈ (r₂ i).index,
          (fA (μ.action (r.left i) a) * fH ((r₂ i).left j)) ⊗ₜ[R] gH ((r₂ i).right j) := hco
    _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
            Bialgebra.comulAlgHom_apply, ← (r₂ i).eq, map_sum, Algebra.TensorProduct.map_tmul,
            Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- Left multiplication by `A` and `μ.action` form a `SmashCompatible` pair in `Module.End R A`. -/
theorem smashCompatible_lsmul_action (μ : LeftModuleAlgebra R H A) :
    μ.SmashCompatible (Algebra.lsmul R R A) μ.action := by
  rw [μ.smashCompatible_iff_sum _ _ (ℛ R)]
  intro h a
  ext b
  simpa [LinearMap.sum_apply] using μ.action_mul_eq_sum (ℛ R h) a b

/-! ### Compatible `A`- and `H`-actions -/

/-- Predicate expressing that `R`-compatible `A`- and `H`-module structures on `M` satisfy the
smash-product Leibniz law `h • (a • m) = ∑ (h₁ · a) • (h₂ • m)`, formulated without choosing a
coproduct representation. -/
@[mk_iff]
class IsCompatibleAction (μ : LeftModuleAlgebra R H A) (M : Type*)
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module H M] [IsScalarTower R H M] : Prop where
  /-- The `A`-action and `H`-action form a `SmashCompatible` pair in `Module.End R M`. -/
  smashCompatible : μ.SmashCompatible (Algebra.lsmul R (A := A) R M) (Algebra.lsmul R (A := H) R M)

/-- The smash-product Leibniz law in any finite representation of `comul h`. -/
theorem IsCompatibleAction.smul_smul_eq_sum {μ : LeftModuleAlgebra R H A} {M : Type*}
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module H M] [IsScalarTower R H M] [hc : μ.IsCompatibleAction M]
    {h : H} {ι : Type*} (r : Coalgebra.Repr R h ι) (a : A) (m : M) :
    h • (a • m) = ∑ i ∈ r.index, μ.action (r.left i) a • (r.right i • m) := by
  simpa [LinearMap.sum_apply] using DFunLike.congr_fun (hc.smashCompatible.mul_eq_sum r a) m

/-- Characterization of `IsCompatibleAction` using a family of finite coproduct representations. -/
theorem isCompatibleAction_iff_sum (μ : LeftModuleAlgebra R H A) (M : Type*)
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module H M] [IsScalarTower R H M] {ι : H → Type*} (r : ∀ h, Coalgebra.Repr R h (ι h)) :
    μ.IsCompatibleAction M ↔ ∀ h a (m : M),
      h • (a • m) = ∑ i ∈ (r h).index, μ.action ((r h).left i) a • ((r h).right i • m) := by
  rw [isCompatibleAction_iff, μ.smashCompatible_iff_sum _ _ r]
  refine ⟨fun hf h a m => by simpa [LinearMap.sum_apply] using DFunLike.congr_fun (hf h a) m,
    fun hf h a => ?_⟩
  ext m
  simpa [LinearMap.sum_apply] using hf h a m

end Semiring

end LeftModuleAlgebra

end TauCeti
