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

/-!
# The multiplier ring of a submodule of an algebra

Let `B` be a commutative `R`-algebra and `M` an `R`-submodule of `B`. The *multiplier ring*
`B₀ = {b ∈ B | b M ⊆ M}` of the underlying additive subgroup of `M`
(`AddSubgroup.multiplierRing`) is a subring of `B` containing the image of `R`. This file
compares the `R`-submodule `I • M` of `B` coming from an ideal `I` of `R` with the extension of
`I` to `B₀`. The submodule `I • M` lies in `B₀` only under a hypothesis such as
`I • (M * M) ≤ M` (see `Submodule.smul_subset_multiplierRing`). These comparisons are how a
lattice in a finite algebra over a Huber ring yields a pair of definition.

## Main results

* `Submodule.toMultiplierRing`: the structure map `R → B₀`.
* `Submodule.smul_subset_multiplierRing`: if `I` carries `M * M` into `M`, then `I • M ⊆ B₀`.
* `Submodule.coe_map_pow_subset`: if `1 ∈ M`, the powers of the extension `J = I B₀` satisfy
  `Jⁿ ⊆ Iⁿ • M`.
* `Submodule.smul_subset_coe_map_pow`: if `Iʲ • M ⊆ B₀`, then `I^(n + j) • M ⊆ Jⁿ`.
* `Submodule.isIntegral_of_mem_multiplierRing`: if `M` is finitely generated and contains `1`,
  every element of `B₀` is integral over `R`.
-/

public section

open scoped Pointwise

namespace Submodule

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]

/-- The image of `R` lies in the multiplier ring of an `R`-submodule. -/
theorem algebraMap_mem_multiplierRing (M : Submodule R B) (a : R) :
    algebraMap R B a ∈ M.toAddSubgroup.multiplierRing := by
  refine AddSubgroup.mem_multiplierRing.mpr fun m hm ↦ ?_
  rw [← Algebra.smul_def]
  exact M.smul_mem a hm

/-- If an ideal `I` carries `M * M` into `M`, then `I • M` lies in the multiplier ring of `M`. -/
theorem smul_subset_multiplierRing {M : Submodule R B} {I : Ideal R} (h : I • (M * M) ≤ M) :
    ((I • M : Submodule R B) : Set B) ⊆ M.toAddSubgroup.multiplierRing := fun x hx ↦ by
  refine Submodule.smul_induction_on hx (fun t ht n hn ↦ ?_) fun x y hx hy ↦ ?_
  · refine AddSubgroup.mem_multiplierRing.mpr fun m hm ↦ ?_
    rw [smul_mul_assoc]
    exact h (Submodule.smul_mem_smul ht (Submodule.mul_mem_mul hn hm))
  · exact M.toAddSubgroup.multiplierRing.add_mem hx hy

/-- The structure map `R → B₀` into the multiplier ring of an `R`-submodule. -/
noncomputable def toMultiplierRing (M : Submodule R B) : R →+* M.toAddSubgroup.multiplierRing :=
  (algebraMap R B).codRestrict _ M.algebraMap_mem_multiplierRing

/-- The structure map `R → B₀` sends `a` to `a • 1`. -/
@[simp]
theorem coe_toMultiplierRing (M : Submodule R B) (a : R) :
    (M.toMultiplierRing a : B) = a • (1 : B) := by
  rw [toMultiplierRing, RingHom.codRestrict_apply, Algebra.smul_def, mul_one]

/-- The powers of the extension `J = I B₀` of an ideal `I` of `R` to the multiplier ring lie in
`Iⁿ • M` when `1 ∈ M`. -/
theorem coe_map_pow_subset {M : Submodule R B} (h1 : (1 : B) ∈ M) (I : Ideal R) (n : ℕ) :
    Subtype.val '' ((I.map M.toMultiplierRing ^ n : Ideal M.toAddSubgroup.multiplierRing) :
      Set M.toAddSubgroup.multiplierRing) ⊆ ((I ^ n • M : Submodule R B) : Set B) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, ← Ideal.map_pow] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    rw [SetLike.mem_coe, coe_toMultiplierRing]
    exact Submodule.smul_mem_smul ha h1
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [smul_eq_mul, Subring.coe_mul]
    refine Submodule.smul_induction_on' hy (fun t ht m hm ↦ ?_) fun _ _ _ _ h₁ h₂ ↦ ?_
    · rw [mul_smul_comm]
      exact Submodule.smul_mem_smul ht (AddSubgroup.mem_multiplierRing.mp r.2 m hm)
    · rw [mul_add]
      exact Submodule.add_mem _ h₁ h₂

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
    · rw [← Ideal.map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    · rw [Subring.coe_mul, coe_toMultiplierRing, smul_one_mul]
  · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, Ideal.add_mem _ hx hy, rfl⟩

/-- **The multiplier ring of a finitely generated submodule containing `1` is integral.** If `M`
is a finitely generated `R`-submodule of `B` with `1 ∈ M`, every `b ∈ B` with `b M ⊆ M` is
integral over `R`: by Cayley–Hamilton, multiplication by `b` on `M` satisfies a monic polynomial,
and evaluating at `1` shows that `b` satisfies it too. -/
theorem isIntegral_of_mem_multiplierRing {M : Submodule R B} (hM : M.FG) (h1 : (1 : B) ∈ M)
    {b : B} (hb : b ∈ M.toAddSubgroup.multiplierRing) : IsIntegral R b := by
  have : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  let f : Module.End R M :=
    (LinearMap.mulLeft R b).restrict fun m hm ↦ AddSubgroup.mem_multiplierRing.mp hb m hm
  have hpow (n : ℕ) (v : M) : ((f ^ n) v : B) = b ^ n * v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', mul_assoc, ← ih]
      exact LinearMap.coe_restrict_apply _ _
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  refine ⟨p, hp, ?_⟩
  -- evaluating a polynomial in `f` at `1 ∈ M` is evaluating it at `b`
  have heval (q : Polynomial R) : ((Polynomial.aeval f q) ⟨1, h1⟩ : B) =
      Polynomial.aeval b q := by
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
    | monomial n a => simp [Polynomial.aeval_monomial, hpow, Algebra.smul_def]
  rw [← Polynomial.aeval_def, ← heval, hpf, LinearMap.zero_apply, Submodule.coe_zero]

end Submodule
