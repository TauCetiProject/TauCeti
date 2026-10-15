/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Unsuspended

/-!
# Component equations for right A-infinity module morphisms

A morphism `f : M ⟶ N` of right `A∞` modules is stored as a degree-zero map of suspended bar
comodules commuting with their bar differentials.  This file expands that condition first on a
pure bar word and then in the unsuspended components of `f`, `M`, `N`, and the algebra.

For a cut after `k` of `n` algebra inputs, the target-module term has sign
`(-1) ^ (k * (n - k))`, while the source-module term has sign
`(-1) ^ ((k + 1) * (n - k))`.  The difference records that a morphism component has degree `-k`
and a module operation has degree `1 - k`.  Terms in which an algebra operation collapses a block
carry the same insertion sign as in the module Stasheff equation.

## Main results

* `TauCeti.AInfinityRightModuleHom.barMap_tmul_of_tprod`: the bar map expanded over all cuts.
* `TauCeti.AInfinityRightModuleHom.suspendedComponentEquation`: the suspended component equation.
* `TauCeti.AInfinityRightModuleHom.componentEquation`: the full unsuspended component equation on
  homogeneous inputs.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open scoped BigOperators TensorProduct
open _root_.MultilinearMap (evalNat suspExp)

namespace TauCeti

universe uR uA uM uN

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

attribute [local instance] Comodule.cofree

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}

/-- On a pure word, the bar map of a module morphism applies its Taylor map to every prefix and
retains the corresponding suffix. -/
theorem barMap_tmul_of_tprod (f : AInfinityRightModuleHom MM NN) (n : ℕ) (x : M)
    (a : Fin n → A) :
    f.barMap (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a)) =
      ∑ k ∈ Finset.range (n + 1),
        f.taylor (x ⊗ₜ[R] TensorWords.subword R a 0 k) ⊗ₜ[R]
          TensorWords.subword R a k (n - k) := by
  rw [barMap_eq_cofreeLift, AInfinityRightModule.cofreeLift_tmul_of_tprod]

/-- The suspended component equation on a word with `n` algebra inputs.  The target Taylor map
after the morphism bar map equals the morphism Taylor map after the source bar differential. -/
theorem suspendedComponentEquation (f : AInfinityRightModuleHom MM NN) (n : ℕ) (x : M)
    (a : Fin n → A) :
    ∑ k ∈ Finset.range (n + 1),
        NN.taylor (f.taylor (x ⊗ₜ[R] TensorWords.subword R a 0 k) ⊗ₜ[R]
          TensorWords.subword R a k (n - k)) =
      ∑ k ∈ Finset.range (n + 1),
          f.taylor (MM.taylor (x ⊗ₜ[R] TensorWords.subword R a 0 k) ⊗ₜ[R]
            TensorWords.subword R a k (n - k)) +
        f.taylor ((MM.grading.shift 1).koszulTwist 1 x ⊗ₜ[R]
          AA.coaugmentedBarDifferential
            (TensorWords.of R A n (PiTensorProduct.tprod R a))) := by
  have h := LinearMap.congr_fun f.taylor_comp_barMap
    (x ⊗ₜ[R] TensorWords.of R A n (PiTensorProduct.tprod R a))
  rw [LinearMap.comp_apply, barMap_tmul_of_tprod, map_sum, LinearMap.comp_apply,
    AInfinityRightModule.barDifferential_eq,
    AInfinityRightModule.gradedCoderiv_tmul_of_tprod, map_add, map_sum] at h
  exact h

/-- **The unsuspended module-morphism equation** with `n` algebra inputs.  The module input `x`
has degree `e`, and `a 0, …, a (n - 1)` have degrees `d 0, …, d (n - 1)`.

The first sum applies a component of `f` and then an operation of the target module.  The second
applies an operation of the source module and then a component of `f`.  The final sum applies an
algebra operation to a nonempty block before applying a component of `f`. -/
theorem componentEquation (f : AInfinityRightModuleHom MM NN) (n : ℕ)
    {x : M} {e : ℤ} (hx : x ∈ MM.grading.piece e) (d : ℕ → ℤ) (a : ℕ → A)
    (ha : ∀ i < n, a i ∈ AA.grading.piece (d i)) :
    ∑ k ∈ Finset.range (n + 1),
        negOnePowCast R ((k : ℤ) * ((n : ℤ) - k)) •
          evalNat (NN.m (n - k + 1) (evalNat (f.component k x) a))
            (fun j ↦ a (k + j)) =
      ∑ k ∈ Finset.range (n + 1),
          negOnePowCast R (((k : ℤ) + 1) * ((n : ℤ) - k)) •
            evalNat (f.component (n - k) (evalNat (MM.m (k + 1) x) a))
              (fun j ↦ a (k + j)) +
        ∑ p ∈ Finset.range n, ∑ s ∈ Finset.Icc 1 (n - p),
          negOnePowCast R ((p : ℤ) + 1 + s * ((n : ℤ) - p - s) +
              (2 - s) * (e + ∑ i ∈ Finset.range p, d i)) •
            evalNat (f.component (p + 1 + (n - p - s)) x)
              (replaceBlock a p s (evalNat (AA.m s) fun j ↦ a (p + j))) := by
  have h := f.suspendedComponentEquation n x (fun i : Fin n ↦ a i)
  rw [Finset.sum_congr rfl fun k hk ↦
      AInfinityRightModule.apply_comp_subword_of_mem
        (f := fun r ↦ f.component r) (h := fun r ↦ NN.m (r + 1))
        f.taylor_tmul_of_tprod
        (fun r y p hy b db hb ↦ by
          simpa only [zero_sub, sub_eq_add_neg, zero_add] using
            f.component_mem_piece r hy b db hb)
        NN.taylor_tmul_of_tprod (q := 0)
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hx d a ha,
    Finset.sum_congr rfl fun k hk ↦
      AInfinityRightModule.apply_comp_subword_of_mem
        (f := fun r ↦ MM.m (r + 1)) (h := fun r ↦ f.component r)
        MM.taylor_tmul_of_tprod
        (fun r y p hy b db hb ↦ MM.m_mem_piece r hy b db hb)
        f.taylor_tmul_of_tprod (q := 1)
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hx d a ha] at h
  rw [AInfinityRightModule.apply_coaugmentedBarDifferential_of_tprod f.taylor n
      ((MM.grading.shift 1).koszulTwist 1 x) (fun i : Fin n ↦ a i),
    Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun s hs ↦
      AInfinityRightModule.apply_algebra_splice_of_mem
        (f := fun r ↦ f.component r) f.taylor_tmul_of_tprod
        (Finset.mem_Icc.1 hs).1
        (by
          have := (Finset.mem_Icc.1 hs).2
          have := Finset.mem_range.1 hp
          omega) hx d a ha] at h
  simp only [← Finset.smul_sum, ← smul_add] at h
  -- Both sides carry the global suspension sign, which is an involution.
  simpa only [add_zero, Nat.succ_eq_add_one, negOnePowCast_smul_negOnePowCast_smul] using
    congrArg (negOnePowCast R (n * e + suspExp n d) • ·) h

end AInfinityRightModuleHom
end TauCeti
