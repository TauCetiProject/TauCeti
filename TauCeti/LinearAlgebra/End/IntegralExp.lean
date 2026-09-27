/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Nilpotent.BaseChangeAction
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Integral exponentials on product lattices

The product of two additive subgroups stable under divided powers is stable under the
componentwise operator. After scalar extension to any commutative ring, its divided-power
exponential is the product of the two exponentials. This allows integral representations to be
combined without changing the root subgroup actions on their summands.
-/

public section

open TensorProduct TauCeti TauCeti.Associative

namespace Module.End

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- Divided powers of a componentwise endomorphism act componentwise. -/
@[simp]
theorem dividedPower_prodMap (x : Module.End ℚ V) (y : Module.End ℚ W) (n : ℕ) :
    dividedPower n (x.prodMap y) = (dividedPower n x).prodMap (dividedPower n y) := by
  have h := map_dividedPower (LinearMap.prodMapAlgHom ℚ V W) n (x, y)
  have hfst := map_dividedPower (AlgHom.fst ℚ (Module.End ℚ V) (Module.End ℚ W)) n (x, y)
  have hsnd := map_dividedPower (AlgHom.snd ℚ (Module.End ℚ V) (Module.End ℚ W)) n (x, y)
  calc
    dividedPower n (x.prodMap y) =
        (LinearMap.prodMapAlgHom ℚ V W) (dividedPower n (x, y)) := h.symm
    _ = (dividedPower n x).prodMap (dividedPower n y) := by
      have hp : dividedPower n (x, y) = (dividedPower n x, dividedPower n y) :=
        Prod.ext hfst hsnd
      rw [hp]
      rfl

/-- A product of divided-power-stable additive subgroups is divided-power-stable. -/
theorem dividedPower_prodMap_mem_prod (x : Module.End ℚ V) (y : Module.End ℚ W)
    (M : AddSubgroup V) (N : AddSubgroup W)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hN : ∀ n, ∀ w ∈ N, Associative.dividedPower n y • w ∈ N)
    (n : ℕ) (v : V × W) (hv : v ∈ M.prod N) :
    Associative.dividedPower n (x.prodMap y) • v ∈ M.prod N := by
  rw [dividedPower_prodMap]
  exact ⟨hM n v.1 hv.1, hN n v.2 hv.2⟩

-- Use the module structure of the supplied integer algebra when forming scalar extensions.
attribute [local instance high] Algebra.toModule

/-- Scalar extension identifies the integral exponential on a product lattice with the
componentwise exponentials. The coefficient ring may have arbitrary characteristic. -/
@[simp]
theorem prodRight_baseChangeExp
    {R : Type*} [CommRing R] [Algebra ℤ R]
    (x : Module.End ℚ V) (y : Module.End ℚ W)
    (M : AddSubgroup V) (N : AddSubgroup W)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hN : ∀ n, ∀ w ∈ N, Associative.dividedPower n y • w ∈ N)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (t : R) (z : R ⊗[ℤ] M.prod N) :
    let E := fun z => TensorProduct.prodRight ℤ R R M N
      (((M.prodEquiv N).toIntLinearEquiv.baseChange ℤ R _ _) z)
    E (baseChangeExp (x.prodMap y) (M.prod N)
      (dividedPower_prodMap_mem_prod x y M N hM hN) t z) =
      (baseChangeExp x M hM t (E z).1, baseChangeExp y N hN t (E z).2) := by
  dsimp only
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  have hx' : x ^ (m + n) = 0 := pow_eq_zero_of_le (Nat.le_add_right m n) hm
  have hy' : y ^ (m + n) = 0 := pow_eq_zero_of_le (Nat.le_add_left n m) hn
  have hxy : (x.prodMap y) ^ (m + n) = 0 := by
    have h := map_pow (LinearMap.prodMapRingHom ℚ V W) (x, y) (m + n)
    simpa [hx', hy'] using h.symm
  have hfst (v : M.prod N) : (((M.prodEquiv N) v).1 : V) = (v : V × W).1 := rfl
  have hsnd (v : M.prod N) : (((M.prodEquiv N) v).2 : W) = (v : V × W).2 := rfl
  induction z using TensorProduct.inductionOn with
  | tmul r v =>
      simp only [LinearEquiv.baseChange_tmul, TensorProduct.prodRight_tmul]
      rw [baseChangeExp_tmul_of_pow_eq_zero _ _ _ hxy,
        baseChangeExp_tmul_of_pow_eq_zero _ _ _ hx',
        baseChangeExp_tmul_of_pow_eq_zero _ _ _ hy']
      simp only [map_sum, LinearEquiv.baseChange_tmul, TensorProduct.prodRight_tmul]
      -- The two carrier projections reduce the integral operators to their ambient values.
      apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum] <;>
        apply Finset.sum_congr rfl <;> intro k hk <;>
        congr 1 <;> apply Subtype.ext <;>
        simp only [AddEquiv.coe_toIntLinearEquiv, hfst, hsnd,
          coe_integralDividedPower_apply, dividedPower_prodMap,
          Module.End.smul_def, LinearMap.prodMap_apply]
  | add z z' hz hz' =>
      simp only [map_add, hz, hz', Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

end Module.End
