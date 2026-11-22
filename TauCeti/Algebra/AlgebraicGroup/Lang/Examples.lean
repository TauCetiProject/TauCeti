/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.AlgebraicGroup.Lang.Basic
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
import TauCeti.FieldTheory.Finite.Card

/-!
# Specializations and counterexamples for Lang's theorem

This file records two concrete illustrations of Lang's theorem:

* **The general linear group**
  (`TauCeti.Lang.surjective_inv_mul_generalLinearGroup_map_frobeniusAlgHom`):
  for any finite field `F`, algebraically closed extension `K / F`, and `n : ℕ`, the Lang map
  `g ↦ g⁻¹ * Frob(g)` induced by the entrywise `|F|`-power Frobenius is surjective on
  `GL_n(K)`.
* **Failure without connectedness**
  (`TauCeti.Lang.inv_mul_frobeniusPoints_zmod_two_eq_one_of_odd_card`,
  `TauCeti.Lang.not_surjective_inv_mul_frobeniusPoints_zmod_two_of_odd_card`):
  for a finite field `F` of odd cardinality, any nontrivial commutative `F`-algebra `K`, and any
  `n : ℕ`, the `|F|^n`-Frobenius acts trivially on `μ₂(K)`, so the Lang map on `μ₂(K)` is
  constantly `1` and misses the point `-1`.

## References

* J. S. Milne, *Algebraic Groups*, version 2.00 (2015), Corollary 27.55 and the remark after
  Corollary 27.56, p. 488.
-/

public section

open WithConv

universe u w

namespace TauCeti.Lang

/-- **Lang's theorem for `GL_n`**: for a finite field `F`, an algebraically closed extension
`K / F`, and any `n : ℕ`, the Lang map `g ↦ g⁻¹ * Frob(g)` of the entrywise `|F|`-power
Frobenius is surjective on `GL_n(K)`. -/
theorem surjective_inv_mul_generalLinearGroup_map_frobeniusAlgHom
    {F : Type u} [Field F] [Fintype F]
    {K : Type w} [Field K] [Algebra F K] [IsAlgClosed K] (n : ℕ) :
    Function.Surjective fun g : Matrix.GeneralLinearGroup (Fin n) K =>
      g⁻¹ * Matrix.GeneralLinearGroup.map
        (_root_.FiniteField.frobeniusAlgHom F K : K →+* K) g := by
  let e := GeneralLinear.pointsMulEquiv (R := F) (A := K) n
  have hsurj := surjective_inv_mul_frobeniusPoints (F := F) (K := K)
    (H := GeneralLinear.coordinateHopfAlgebra F n) one_ne_zero
    (GeneralLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra F n)
  intro a
  obtain ⟨f, hf⟩ := hsurj (e.symm a)
  refine ⟨e f, ?_⟩
  have hmap : Matrix.GeneralLinearGroup.map
      (_root_.FiniteField.frobeniusAlgHom F K : K →+* K) (e f) =
      e (FiniteField.frobeniusPoints F 1 f) := by
    rw [FiniteField.frobeniusPoints_one, GeneralLinear.pointsMulEquiv_mapValue]
  dsimp only at hf ⊢
  rw [hmap, ← map_inv, ← map_mul, hf, e.apply_symm_apply]

/-- Over a finite field `F` of odd cardinality, every iterate of the `|F|`-Frobenius acts trivially
on the points of `μ₂` in any commutative `F`-algebra, so the Lang map is identically `1`. -/
theorem inv_mul_frobeniusPoints_zmod_two_eq_one_of_odd_card
    {F : Type u} [Field F] [Fintype F] (hodd : Odd (Fintype.card F))
    {K : Type w} [CommRing K] [Algebra F K] (n : ℕ)
    (g : WithConv (MonoidAlgebra F (Multiplicative (ZMod 2)) →ₐ[F] K)) :
    g⁻¹ * FiniteField.frobeniusPoints F n g = 1 := by
  have hfix : FiniteField.frobeniusPoints F n g = g := by
    apply ofConv_injective
    apply RootsOfUnityGroup.algHom_ext 2
    rw [FiniteField.frobeniusPoints_apply_apply, Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hodd.pow (n := n)
    have hsq : g.ofConv (MonoidAlgebra.single (RootsOfUnityGroup.generator 2) 1) ^ 2 = 1 := by
      rw [← map_pow, RootsOfUnityGroup.single_generator_pow_eq_one, map_one]
    rw [hk, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]
  rw [hfix]
  exact inv_mul_cancel g

/-- **Connectedness is essential for Lang's theorem**: for a finite field `F` of odd cardinality,
any nontrivial commutative `F`-algebra `K` (in particular any algebraically closed extension), and
any `n : ℕ`, the Lang map of the `|F|^n`-Frobenius on `μ₂(K)` is not surjective, as it misses
`-1`. -/
theorem not_surjective_inv_mul_frobeniusPoints_zmod_two_of_odd_card
    {F : Type u} [Field F] [Fintype F] (hodd : Odd (Fintype.card F))
    {K : Type w} [CommRing K] [Nontrivial K] [Algebra F K] (n : ℕ) :
    ¬ Function.Surjective
        fun g : WithConv (MonoidAlgebra F (Multiplicative (ZMod 2)) →ₐ[F] K) =>
          g⁻¹ * FiniteField.frobeniusPoints F n g := by
  have hneg_ne_one : (-1 : K) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two
      (Algebra.ringChar_eq F K ▸
        FiniteField.ringChar_ne_two_of_odd_card
          ((Nat.card_eq_fintype_card (α := F)).symm ▸ hodd))
  let negOne : rootsOfUnity 2 K := ⟨-1, by simp⟩
  let a : WithConv (MonoidAlgebra F (Multiplicative (ZMod 2)) →ₐ[F] K) :=
    (RootsOfUnityGroup.pointsMulEquiv (R := F) (A := K) 2).symm negOne
  intro hsurj
  obtain ⟨g, hg⟩ := hsurj a
  have ha1 : a = 1 :=
    hg.symm.trans (inv_mul_frobeniusPoints_zmod_two_eq_one_of_odd_card hodd n g)
  have hval := congrArg (fun p =>
    ((RootsOfUnityGroup.pointsMulEquiv (R := F) (A := K) 2 p : Kˣ) : K)) ha1
  simp only [a, negOne, MulEquiv.apply_symm_apply, map_one, OneMemClass.coe_one, Units.val_one,
    Units.val_neg] at hval
  exact hneg_ne_one hval

end TauCeti.Lang
