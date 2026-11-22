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

import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import TauCeti.LinearAlgebra.End.Aeval

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

The image of `R` is central in `B₀`, so the extension `J = I B₀` of an ideal `I` of `R` along the
structure map `R → B₀` is a two-sided ideal whose powers are the extensions of the powers of `I`.
The last part of the file compares `I • M` with `J`. These comparisons are how a lattice in a
finite algebra over a Huber ring yields a pair of definition.

## Main results

* `Submodule.toMultiplierRing`: the structure map `R → B₀`.
* `Submodule.commute_toMultiplierRing`: the image of `R` in `B₀` is central.
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

/-- The extension of an ideal along a ring map whose image is central is two-sided. -/
private theorem isTwoSided_map_of_commute {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S}
    (hf : ∀ a y, Commute (f a) y) (I : Ideal R) : (I.map f).IsTwoSided where
  mul_mem_of_left b hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [(hf a b).eq]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem f ha)
    | zero => rw [zero_mul]; exact Ideal.zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact Ideal.add_mem _ hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ hx

/-- Extension of ideals along a ring map whose image is central commutes with powers. This is
Mathlib's `Ideal.map_pow` without assuming the target commutative. -/
private theorem map_pow_of_commute {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S}
    (hf : ∀ a y, Commute (f a) y) (I : Ideal R) (n : ℕ) : (I ^ n).map f = I.map f ^ n := by
  induction n with
  | zero =>
    rw [Submodule.pow_zero, Submodule.pow_zero, Ideal.one_eq_top, Ideal.one_eq_top, Ideal.map_top]
  | succ n ih =>
    rw [Submodule.pow_succ, Submodule.pow_succ, ← ih]
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr <| Ideal.mul_le.mpr fun r hr s hs ↦ ?_) ?_
    · rw [Ideal.mem_comap, map_mul]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem f hr) (Ideal.mem_map_of_mem f hs)
    · -- The product of two spans is the span of the products, as the first factor is two-sided.
      have : (Ideal.span (f '' (I ^ n : Ideal R))).IsTwoSided :=
        isTwoSided_map_of_commute hf (I ^ n)
      rw [Ideal.map, Ideal.map, Ideal.span_mul_span, Ideal.span_le]
      rintro _ ⟨_, ⟨r, hr, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
      simpa only [map_mul, SetLike.mem_coe] using Ideal.mem_map_of_mem f (Ideal.mul_mem_mul hr hs)

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

/-- The image of the structure map `R → B₀` is central in the multiplier ring `B₀`. -/
theorem commute_toMultiplierRing (M : Submodule R B) (a : R)
    (x : M.toAddSubgroup.multiplierRing) : Commute (M.toMultiplierRing a) x :=
  Subtype.ext <| by
    rw [Subring.coe_mul, Subring.coe_mul, coe_toMultiplierRing]
    exact Algebra.commutes a _

/-- **The multiplier ring of a finitely generated submodule containing `1` is integral.** If `M`
is a finitely generated `R`-submodule of an `R`-algebra `B` with `1 ∈ M`, every `b ∈ B` with
`b M ⊆ M` is integral over `R`. The algebra `B` need not be commutative. -/
theorem FG.isIntegral_of_mem_multiplierRing {M : Submodule R B} (hM : M.FG) (h1 : (1 : B) ∈ M)
    {b : B} (hb : b ∈ M.toAddSubgroup.multiplierRing) : IsIntegral R b := by
  have : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  have hbM (m : B) (hm : m ∈ M) : Algebra.lmul R B b m ∈ M := by
    rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', ← M.mem_toAddSubgroup]
    exact AddSubgroup.mem_multiplierRing.mp hb m (M.mem_toAddSubgroup.mpr hm)
  -- By Cayley–Hamilton, left multiplication by `b` on `M` satisfies a monic polynomial `p`.
  let f : Module.End R M := (Algebra.lmul R B b).restrict hbM
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  refine ⟨p, hp, ?_⟩
  -- The inclusion `M → B` intertwines `f` with left multiplication by `b`, so evaluating `p`
  -- at `f` and applying it to `1 ∈ M` is evaluating `p` at `b`.
  have hcomp : (Algebra.lmul R B b).comp M.subtype = M.subtype.comp f :=
    (LinearMap.subtype_comp_restrict hbM).symm
  have hb1 : Polynomial.aeval b p = 0 := by
    have := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hcomp p) ⟨1, h1⟩
    rw [Polynomial.aeval_algHom_apply] at this
    simpa [hpf] using this
  rwa [← Polynomial.aeval_def]

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
  rw [SetLike.mem_coe, ← map_pow_of_commute M.commute_toMultiplierRing] at hx
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
      fun m hm ↦ AddSubgroup.mem_multiplierRing.mp r.property m hm
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
  · refine ⟨M.toMultiplierRing a * ⟨y, hj hy⟩, ?_, ?_⟩
    · rw [← map_pow_of_commute M.commute_toMultiplierRing, (M.commute_toMultiplierRing _ _).eq]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)
    · rw [Subring.coe_mul, coe_toMultiplierRing, ← Algebra.smul_def]
  · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, Ideal.add_mem _ hx hy, rfl⟩

end Ring

end Submodule
