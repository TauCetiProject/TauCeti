/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.Bialgebra.Primitive
public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap

import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Primitive elements of a symmetric algebra

Over a commutative rational algebra, the primitive elements of a symmetric
algebra are exactly its degree-one elements, without a basis assumption on the
module.

Use `SymmetricAlgebra.isPrimitiveElem_iff_mem_range_ι` to recover an element
`m : M` with `ι R M m = p` from a primitive symmetric-algebra element `p`.
Conversely, the same equivalence proves that every image of `ι` is primitive.

This calculation identifies primitives before applying coalgebra comparisons with
universal enveloping algebras. The argument uses the doubling endomorphism: on
symmetric degree `n` it acts by `2 ^ n`, and on primitive elements it acts by `2`.

Adapted from `Mei/LinearAlgebra/SymmetricAlgebra/Primitive.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`97304cc1bd51a202db1a705709fb4763f61e190a`, licensed under Apache 2.0.
-/

public section

namespace SymmetricAlgebra

variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommMonoid M] [Module R M]

local notation "S" => _root_.SymmetricAlgebra R M
local notation "𝒮" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M

/-- Over a commutative rational algebra, an element of a symmetric algebra is
primitive exactly when it is a generator. -/
theorem isPrimitiveElem_iff_mem_range_ι (p : S) :
    Bialgebra.IsPrimitiveElem R p ↔ p ∈ Set.range (_root_.SymmetricAlgebra.ι R M) := by
  /- Multiplication after comultiplication doubles each generator and acts on
  homogeneous degree `n` by `2 ^ n`, while a primitive element is doubled.
  The homogeneous eigenvalue computation uses `AlgHom.apply_eq_pow_mul_of_forall_ι_eq`;
  degree-one reconstruction uses `TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv`. -/
  constructor
  · intro hp
    -- Multiplication after the coproduct is the degree-preserving doubling map.
    let D : S →ₐ[R] S := _root_.SymmetricAlgebra.map R
      ((2 : R) • (LinearMap.id : M →ₗ[R] M))
    have hD : D = (Algebra.TensorProduct.lmul' R).comp (Bialgebra.comulAlgHom R S) := by
      ext m
      simp [D, Bialgebra.comulAlgHom_apply, two_smul]
    have hDp : D p = (2 : R) • p := by
      rw [hD, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, hp.comul_eq_tmul_add_tmul]
      simp [two_smul]
    have heigen {n : ℕ} {q : S} (hq : q ∈ 𝒮 n) : D q = (2 : R) ^ n • q := by
      have h := AlgHom.apply_eq_pow_mul_of_forall_ι_eq (AlgHom.id R S) D (2 : S)
        (fun m => by simp [D, two_smul, two_mul]) hq
      simpa only [AlgHom.id_apply, Algebra.smul_def, map_pow, map_ofNat] using h
    -- Comparing the two eigenvalues kills every component except degree one.
    have hzero (n : ℕ) (hn : n ≠ 1) : (DirectSum.decompose 𝒮 p n : S) = 0 := by
      have hd := map_directSumDecompose 𝒮 𝒮
        (_root_.SymmetricAlgebra.gradedMap R ((2 : R) • (LinearMap.id : M →ₗ[R] M)))
        (x := p) (i := n)
      simp only [_root_.SymmetricAlgebra.gradedMap_apply] at hd
      have he : (2 : R) ^ n • (DirectSum.decompose 𝒮 p n : S) =
          (2 : R) • (DirectSum.decompose 𝒮 p n : S) := by
        rw [← heigen (DirectSum.decompose 𝒮 p n).property]
        rw [hd, hDp, DirectSum.decompose_smul]
        rfl
      have he0 : ((2 : R) ^ n - 2) • (DirectSum.decompose 𝒮 p n : S) = 0 := by
        rw [sub_smul, he, sub_self]
      have hq : (2 : ℚ) ^ n - 2 ≠ 0 := by
        intro h
        have hn' : (2 : ℕ) ^ n = 2 ^ 1 := by
          exact_mod_cast (sub_eq_zero.mp h)
        exact hn (Nat.pow_right_injective (by decide) hn')
      have hu : IsUnit ((2 : R) ^ n - 2) := by
        -- Map a rational unit instead of assuming that the scalar map is injective.
        simpa only [map_sub, map_pow, map_ofNat] using
          (isUnit_iff_ne_zero.mpr hq).map (algebraMap ℚ R)
      exact hu.smul_eq_zero.mp he0
    -- Recompose the sole surviving component, then use the degree-one equivalence.
    have hp1 : p = (DirectSum.decompose 𝒮 p 1 : S) := by
      apply (DirectSum.decomposeLinearEquiv 𝒮).injective
      apply DirectSum.ext
      intro n
      apply Subtype.ext
      by_cases hn : n = 1
      · subst n
        simp only [DirectSum.decomposeLinearEquiv_apply]
        exact (DirectSum.decompose_of_mem_same 𝒮 (DirectSum.decompose 𝒮 p 1).property).symm
      · simp only [DirectSum.decomposeLinearEquiv_apply,
          DirectSum.decompose_of_mem_ne 𝒮 (DirectSum.decompose 𝒮 p 1).property (Ne.symm hn),
          hzero n hn]
    refine ⟨TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv R M
      (DirectSum.decompose 𝒮 p 1), ?_⟩
    rw [TauCeti.SymmetricAlgebra.ι_homogeneousSubmoduleOneEquiv_apply]
    exact hp1.symm
  · rintro ⟨m, rfl⟩
    apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr
    simpa only [add_comm] using _root_.SymmetricAlgebra.comul_ι R M m

end SymmetricAlgebra
