/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import TauCeti.Algebra.Ring.Subgroup

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.LinearAlgebra.End.Restrict
import TauCeti.RingTheory.Ideal.Extended
import TauCeti.RingTheory.IntegralOrder.LeftOrder

/-!
# The multiplier ring of a submodule of an algebra

Let `B` be an `R`-algebra, not necessarily commutative, and `M` an `R`-submodule of `B`. The
*multiplier ring* `B₀ = {b ∈ B | b M ⊆ M}` of the underlying additive subgroup of `M`
(`AddSubgroup.multiplierRing`) is the subring of left multipliers of `M`. It contains the image
of `R`, so the structure map of `B` corestricts to a ring map `R → B₀`. For an ideal `I` of `R`,
the `R`-submodule `I • M` of `B` lies in `B₀` only under a hypothesis such as `I • (M * M) ≤ M`
(see `Submodule.smul_subset_multiplierRing`). If `M` is finitely generated and contains `1`, every
element of `B₀` is integral over `R` (`Submodule.FG.isIntegral_of_mem_multiplierRing`), and so
is every right multiplier `b`, with `M b ⊆ M` (`Submodule.FG.isIntegral_of_forall_mul_mem`).

The image of `R` is central in `B₀`, so the powers of the extension `J = I B₀` of an ideal `I` of
`R` along the structure map `R → B₀` are the extensions of the powers of `I`. The last part of the
file compares `I • M` with `J`. These comparisons are how a lattice in a finite algebra over a
Huber ring yields a pair of definition.

## Main results

* `Submodule.toMultiplierRing`: the structure map `R → B₀`.
* `Submodule.map_toMultiplierRing_pow`: extension of ideals along `R → B₀` commutes with powers.
* `Submodule.smul_subset_multiplierRing`: if `I` carries `M * M` into `M`, then `I • M ⊆ B₀`.
* `Submodule.FG.isIntegral_of_mem_multiplierRing`: if `M` is finitely generated and contains `1`,
  every element of `B₀` is integral over `R`.
* `Submodule.FG.isIntegral_of_forall_mul_mem`: if `M` is finitely generated and contains `1`,
  every `b` with `M b ⊆ M` is integral over `R`.
* `Submodule.coe_map_pow_subset`: if `1 ∈ M`, the powers of the extension `J = I B₀` satisfy
  `Jⁿ ⊆ Iⁿ • M`.
* `Submodule.smul_subset_coe_map_pow`: if `Iʲ • M ⊆ B₀`, then `I^(n + j) • M ⊆ Jⁿ`.
-/

public section

open scoped Pointwise

namespace Submodule

variable {R : Type*} [CommRing R]

section Ring

variable {B : Type*} [Ring B] [Algebra R B]

/-- The image of `R` lies in the multiplier ring of an `R`-submodule. -/
@[simp high]
theorem algebraMap_mem_multiplierRing (M : Submodule R B) (a : R) :
    algebraMap R B a ∈ M.toAddSubgroup.multiplierRing := by
  refine AddSubgroup.mem_multiplierRing.mpr fun m hm ↦ ?_
  rw [Submodule.mem_toAddSubgroup] at hm ⊢
  rw [← Algebra.smul_def]
  exact M.smul_mem a hm

/-- If an ideal `I` carries `M * M` into `M`, then `I • M` lies in the multiplier ring of `M`. -/
theorem smul_subset_multiplierRing {M : Submodule R B} {I : Ideal R} (h : I • (M * M) ≤ M) :
    ((I • M : Submodule R B) : Set B) ⊆ M.toAddSubgroup.multiplierRing := fun x hx ↦ by
  -- The product of submodules is their pointwise scalar action, so `smul_assoc` applies.
  have h' : (I • M) * M ≤ M := (Submodule.smul_assoc I M M).trans_le h
  refine AddSubgroup.mem_multiplierRing.mpr fun m hm ↦ ?_
  rw [Submodule.mem_toAddSubgroup] at hm ⊢
  exact Submodule.mul_le.mp h' x hx m hm

/-- The structure map `R → B₀` into the multiplier ring of an `R`-submodule. -/
noncomputable def toMultiplierRing (M : Submodule R B) : R →+* M.toAddSubgroup.multiplierRing :=
  (algebraMap R B).codRestrict _ M.algebraMap_mem_multiplierRing

/-- The structure map `R → B₀` agrees with the structure map `R → B`. -/
@[simp]
theorem coe_toMultiplierRing (M : Submodule R B) (a : R) :
    (M.toMultiplierRing a : B) = algebraMap R B a := by
  rw [toMultiplierRing, RingHom.codRestrict_apply]

/-- Extension of ideals along the structure map `R → B₀` commutes with powers. -/
theorem map_toMultiplierRing_pow (M : Submodule R B) (I : Ideal R) (n : ℕ) :
    (I ^ n).map M.toMultiplierRing = I.map M.toMultiplierRing ^ n := by
  -- The image of `R` is central in `B₀`, so `toMultiplierRing` makes `B₀` an `R`-algebra and
  -- `Ideal.map_algebraMap_pow` applies.
  have hc (a : R) (x : M.toAddSubgroup.multiplierRing) :
      M.toMultiplierRing a * x = x * M.toMultiplierRing a :=
    Subtype.ext <| by
      rw [Subring.coe_mul, Subring.coe_mul, coe_toMultiplierRing]
      exact Algebra.commutes a _
  have h := @Ideal.map_algebraMap_pow R _ _ _ (M.toMultiplierRing.toAlgebra' hc) I n
  rwa [RingHom.algebraMap_toAlgebra'] at h

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

/-- The powers of the extension `J = I B₀` of an ideal `I` of `R` to the multiplier ring lie in
`Iⁿ • M` when `1 ∈ M`. -/
theorem coe_map_pow_subset {M : Submodule R B} (h1 : (1 : B) ∈ M) (I : Ideal R) (n : ℕ) :
    Subtype.val '' ((I.map M.toMultiplierRing ^ n : Ideal M.toAddSubgroup.multiplierRing) :
      Set M.toAddSubgroup.multiplierRing) ⊆ ((I ^ n • M : Submodule R B) : Set B) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, ← map_toMultiplierRing_pow, Ideal.map] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    rw [SetLike.mem_coe, coe_toMultiplierRing, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem_smul ha h1
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    -- Left multiplication by `r ∈ B₀` maps `M` into itself, hence also `Iⁿ • M`.
    have hr : M.map (LinearMap.mulLeft R (r : B)) ≤ M := Submodule.map_le_iff_le_comap.mpr
      fun m hm ↦ by
        rw [Submodule.mem_comap, LinearMap.mulLeft_apply, ← Submodule.mem_toAddSubgroup]
        exact AddSubgroup.mem_multiplierRing.mp r.property m (M.mem_toAddSubgroup.mpr hm)
    rw [smul_eq_mul, Subring.coe_mul, ← LinearMap.mulLeft_apply R]
    exact (Submodule.map_smul'' _ _ _).trans_le (Submodule.smul_mono le_rfl hr)
      (Submodule.mem_map_of_mem hy)

/-- If `Iʲ • M` lies in the multiplier ring, then `I^(n + j) • M` lies in the `n`-th power of the
extension `J = I B₀` of `I` to the multiplier ring. -/
theorem smul_subset_coe_map_pow {M : Submodule R B} {I : Ideal R} {j : ℕ}
    (hj : ((I ^ j • M : Submodule R B) : Set B) ⊆ M.toAddSubgroup.multiplierRing) (n : ℕ) :
    ((I ^ (n + j) • M : Submodule R B) : Set B) ⊆
      Subtype.val '' ((I.map M.toMultiplierRing ^ n : Ideal M.toAddSubgroup.multiplierRing) :
        Set M.toAddSubgroup.multiplierRing) := by
  intro x hx
  rw [pow_add, Submodule.mul_smul] at hx
  refine Submodule.smul_induction_on hx (fun a ha y hy ↦ ?_) ?_
  · refine ⟨⟨y, hj hy⟩ * M.toMultiplierRing a, ?_, ?_⟩
    · rw [← map_toMultiplierRing_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)
    · rw [Subring.coe_mul, coe_toMultiplierRing, ← Algebra.commutes, ← Algebra.smul_def]
  · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, Ideal.add_mem _ hx hy, rfl⟩

end Ring

end Submodule
