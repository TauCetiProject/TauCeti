/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.LeftOrder

import TauCeti.LinearAlgebra.End.Restrict
import TauCeti.RingTheory.Ideal.Extended

/-!
# The multiplier ring of a submodule of an algebra

Let `B` be an `R`-algebra, not necessarily commutative, and `M` an `R`-submodule of `B`. The left
order `O_l(M) = {b ∈ B | b M ⊆ M}` of `M` (`Submodule.leftOrder`) is an `R`-subalgebra of `B`.
When `R` and `B` are rings, its underlying subring is the *multiplier ring* `B₀` of the underlying
additive subgroup of `M` (`AddSubgroup.multiplierRing`, see `Submodule.toSubring_leftOrder`). For
an ideal `I` of `R`, the `R`-submodule `I • M` of `B` lies in `O_l(M)` only under a hypothesis such
as `I • (M * M) ≤ M` (see `Submodule.smul_subset_leftOrder`). If `M` is finitely generated and
contains `1`, every element of `B₀` is integral over `R`
(`Submodule.FG.isIntegral_of_mem_multiplierRing`), and so is every right multiplier `b`, with
`M b ⊆ M` (`Submodule.FG.isIntegral_of_forall_mul_mem`).

The file also compares `I • M` with the extension `J = I O_l(M)` of `I` along the structure map
`R → O_l(M)`, whose `n`-th power is `Iⁿ • O_l(M)` (`Ideal.pow_smul_top_eq_restrictScalars_map_pow`).
These comparisons are how a lattice in a finite algebra over a Huber ring yields a pair of
definition.

## Main results

* `Submodule.smul_subset_leftOrder`: if `I` carries `M * M` into `M`, then `I • M ⊆ O_l(M)`.
* `Submodule.coe_map_pow_subset`: if `1 ∈ M`, the powers of the extension `J = I O_l(M)` satisfy
  `Jⁿ ⊆ Iⁿ • M`.
* `Submodule.smul_subset_coe_map_pow`: if `Iʲ • M ⊆ O_l(M)`, then `I^(n + j) • M ⊆ Jⁿ`.
* `Submodule.FG.isIntegral_of_mem_multiplierRing`: if `M` is finitely generated and contains `1`,
  every element of `B₀` is integral over `R`.
* `Submodule.FG.isIntegral_of_forall_mul_mem`: if `M` is finitely generated and contains `1`,
  every `b` with `M b ⊆ M` is integral over `R`.
-/

public section

open scoped Pointwise

namespace Submodule

section Semiring

variable {R : Type*} [CommSemiring R] {B : Type*} [Semiring B] [Algebra R B]

/-- If an ideal `I` carries `M * M` into `M`, then `I • M` lies in the left order of `M`. -/
theorem smul_subset_leftOrder {M : Submodule R B} {I : Ideal R} (h : I • (M * M) ≤ M) :
    ((I • M : Submodule R B) : Set B) ⊆ M.leftOrder := fun x hx ↦
  -- The product of submodules is their pointwise scalar action, so `smul_assoc` applies.
  mem_leftOrder_iff.mpr fun m hm ↦
    Submodule.mul_le.mp ((Submodule.smul_assoc I M M).trans_le h) x hx m hm

/-- The powers of the extension `J = I O_l(M)` of an ideal `I` of `R` to the left order lie in
`Iⁿ • M` when `1 ∈ M`. -/
theorem coe_map_pow_subset {M : Submodule R B} (h1 : (1 : B) ∈ M) (I : Ideal R) (n : ℕ) :
    Subtype.val '' ((I.map (algebraMap R M.leftOrder) ^ n : Ideal M.leftOrder) :
      Set M.leftOrder) ⊆ ((I ^ n • M : Submodule R B) : Set B) := by
  rintro _ ⟨x, hx, rfl⟩
  -- `Jⁿ` is `Iⁿ • O_l(M)`, and `O_l(M) ⊆ M` because its elements carry `1 ∈ M` into `M`.
  rw [SetLike.mem_coe, ← Submodule.restrictScalars_mem R,
    ← Ideal.pow_smul_top_eq_restrictScalars_map_pow] at hx
  have hx' := Submodule.mem_map_of_mem (f := M.leftOrder.val.toLinearMap) hx
  rw [Submodule.map_smul'', Submodule.map_top] at hx'
  refine Submodule.smul_mono le_rfl ?_ hx'
  rintro _ ⟨y, rfl⟩
  simpa only [AlgHom.toLinearMap_apply, Subalgebra.coe_val, mul_one] using
    mem_leftOrder_iff.mp y.property 1 h1

/-- If `Iʲ • M` lies in the left order, then `I^(n + j) • M` lies in the `n`-th power of the
extension `J = I O_l(M)` of `I` to the left order. -/
theorem smul_subset_coe_map_pow {M : Submodule R B} {I : Ideal R} {j : ℕ}
    (hj : ((I ^ j • M : Submodule R B) : Set B) ⊆ M.leftOrder) (n : ℕ) :
    ((I ^ (n + j) • M : Submodule R B) : Set B) ⊆
      Subtype.val '' ((I.map (algebraMap R M.leftOrder) ^ n : Ideal M.leftOrder) :
        Set M.leftOrder) := by
  intro x hx
  -- `I^(n + j) • M = Iⁿ • (Iʲ • M) ⊆ Iⁿ • O_l(M)`, which is `Jⁿ`.
  rw [SetLike.mem_coe, pow_add, Submodule.mul_smul] at hx
  have hx' : x ∈ (I ^ n • ⊤ : Submodule R M.leftOrder).map M.leftOrder.val.toLinearMap := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl (fun y hy ↦ LinearMap.mem_range.mpr ⟨⟨y, hj hy⟩, rfl⟩) hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx'
  rw [Ideal.pow_smul_top_eq_restrictScalars_map_pow, Submodule.restrictScalars_mem] at hy
  exact ⟨y, hy, rfl⟩

end Semiring

section Ring

variable {R : Type*} [CommRing R] {B : Type*} [Ring B] [Algebra R B]

/-- **The multiplier ring of a finitely generated submodule containing `1` is integral.** If `M`
is a finitely generated `R`-submodule of an `R`-algebra `B` with `1 ∈ M`, every `b ∈ B` with
`b M ⊆ M` is integral over `R`. The algebra `B` need not be commutative. -/
theorem FG.isIntegral_of_mem_multiplierRing {M : Submodule R B} (hM : M.FG) (h1 : (1 : B) ∈ M)
    {b : B} (hb : b ∈ M.toAddSubgroup.multiplierRing) : IsIntegral R b := by
  have : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  -- The left order `O_l(M)`, which is `B₀` as an `R`-subalgebra, acts on `M` by left
  -- multiplication. By Cayley–Hamilton (Mathlib's instance `Module.End.isIntegral`),
  -- `Module.End R M` is integral over `R`.
  let φ : M.leftOrder →ₐ[R] Module.End R M :=
    ((Algebra.lmul R B).comp M.leftOrder.val).restrictEnd M fun x m hm ↦ by
      rw [AlgHom.comp_apply, Subalgebra.coe_val, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
      exact mem_leftOrder_iff.mp x.property m hm
  -- The action is faithful, since evaluating at `1 ∈ M` recovers the multiplier.
  have hφ : Function.Injective φ := fun x y hxy ↦ by
    have h := congr_arg Subtype.val (LinearMap.congr_fun hxy ⟨1, h1⟩)
    simp only [φ, AlgHom.coe_restrictEnd_apply, AlgHom.comp_apply, Subalgebra.coe_val,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one] at h
    exact Subtype.ext h
  have hbO : b ∈ M.leftOrder := by rwa [← Subalgebra.mem_toSubring, toSubring_leftOrder]
  have h : IsIntegral R (⟨b, hbO⟩ : M.leftOrder) :=
    (isIntegral_algHom_iff (B := Module.End R M) φ hφ).mp (Algebra.IsIntegral.isIntegral _)
  simpa only [Subalgebra.coe_val] using h.map M.leftOrder.val

/-- **Right multipliers of a finitely generated submodule containing `1` are integral.** If `M`
is a finitely generated `R`-submodule of an `R`-algebra `B` with `1 ∈ M`, every `b ∈ B` with
`M b ⊆ M` is integral over `R`. This is the right-multiplier counterpart of
`Submodule.FG.isIntegral_of_mem_multiplierRing`. -/
theorem FG.isIntegral_of_forall_mul_mem {M : Submodule R B} (hM : M.FG) (h1 : (1 : B) ∈ M)
    {b : B} (hb : ∀ m ∈ M, m * b ∈ M) : IsIntegral R b := by
  -- In the opposite algebra `Bᵐᵒᵖ`, right multiplication by `b` becomes left multiplication by
  -- `op b`, so `op b` is a left multiplier of the image `N` of `M`.
  let N : Submodule R Bᵐᵒᵖ := M.map (MulOpposite.opLinearEquiv R).toLinearMap
  have hN : MulOpposite.op b ∈ N.toAddSubgroup.multiplierRing := by
    refine AddSubgroup.mem_multiplierRing.mpr fun z hz ↦ ?_
    simp only [N, Submodule.mem_toAddSubgroup, Submodule.mem_map_equiv,
      MulOpposite.coe_opLinearEquiv_symm, MulOpposite.unop_mul, MulOpposite.unop_op] at hz ⊢
    exact hb _ hz
  have h1N : (1 : Bᵐᵒᵖ) ∈ N := by simpa [N] using h1
  obtain ⟨p, hp, hpb⟩ := (hM.map _).isIntegral_of_mem_multiplierRing h1N hN
  rw [← Polynomial.aeval_def, Polynomial.aeval_op_apply, MulOpposite.op_eq_zero_iff] at hpb
  exact ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩

end Ring

end Submodule
