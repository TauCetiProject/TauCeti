/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.AlgebraicGroup.Lang.Basic
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected

/-!
# Specializations and counterexamples for Lang's theorem

This file records two concrete illustrations of Lang's theorem:

* **The general linear group** (`TauCeti.Lang.surjective_inv_mul_generalLinear`): for any finite
  field `F`, algebraically closed extension `K / F`, and `n : ℕ`, the Lang map
  `g ↦ g⁻¹ * Frob(g)` induced by the entrywise `|F|`-power Frobenius is surjective on
  `GL_n(K)`.
* **Failure without connectedness** (`TauCeti.Lang.not_surjective_inv_mul_rootsOfUnity_two`):
  for a finite field `F` of odd cardinality and any nontrivial commutative `F`-algebra `K`, the
  `|F|`-Frobenius acts trivially on `μ₂(K)`, so the Lang map on `μ₂(K)` is constantly `1` and
  misses the point `-1`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 27.55 and the remark after Corollary 27.56.
-/

public section

open WithConv

universe u w

namespace TauCeti.Lang

/-- **Lang's theorem for `GL_n`**: for a finite field `F`, an algebraically closed extension
`K / F`, and any `n : ℕ`, the Lang map `g ↦ g⁻¹ * Frob(g)` of the entrywise `|F|`-power
Frobenius is surjective on `GL_n(K)`. -/
theorem surjective_inv_mul_generalLinear
    {F : Type u} [Field F] [Fintype F]
    {K : Type w} [Field K] [Algebra F K] [IsAlgClosed K] (n : ℕ) :
    Function.Surjective fun g : Matrix.GeneralLinearGroup (Fin n) K =>
      g⁻¹ * Matrix.GeneralLinearGroup.map
        (_root_.FiniteField.frobeniusAlgHom F K : K →+* K) g := by
  let e := GeneralLinear.pointsMulEquiv (R := F) (A := K) n
  have hsurj := surjective_inv_mul_frobeniusPoints (F := F) (K := K)
    (H := GeneralLinear.coordinateHopfAlgebra F n)
    (GeneralLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra F n)
  intro a
  obtain ⟨f, hf⟩ := hsurj (e.symm a)
  refine ⟨e f, ?_⟩
  have hmap : Matrix.GeneralLinearGroup.map
      (_root_.FiniteField.frobeniusAlgHom F K : K →+* K) (e f) =
      e (FiniteField.frobeniusPoints F 1 f) := by
    have hpow : FiniteField.frobeniusPoints F 1 f =
        AlgHom.mapValue (H := GeneralLinear.coordinateHopfAlgebra F n)
          (_root_.FiniteField.frobeniusAlgHom F K) f := by
      apply ofConv_injective
      ext h
      simp [FiniteField.frobeniusPoints_apply_apply, Nat.card_eq_fintype_card]
    rw [hpow, GeneralLinear.pointsMulEquiv_mapValue]
  dsimp only at hf ⊢
  rw [hmap, ← map_inv, ← map_mul, hf, e.apply_symm_apply]

/-- Over a finite field `F` of odd cardinality, the `|F|`-Frobenius acts trivially on the points of
`μ₂` in any commutative `F`-algebra, so the Lang map is identically `1`. -/
theorem inv_mul_frobeniusPoints_rootsOfUnity_two_eq_one
    {F : Type u} [Field F] [Fintype F] (hodd : Odd (Fintype.card F))
    {K : Type w} [CommRing K] [Algebra F K]
    (g : WithConv (MonoidAlgebra F (Multiplicative (ZMod 2)) →ₐ[F] K)) :
    g⁻¹ * FiniteField.frobeniusPoints F 1 g = 1 := by
  have hfix : FiniteField.frobeniusPoints F 1 g = g := by
    apply ofConv_injective
    apply RootsOfUnityGroup.algHom_ext 2
    rw [FiniteField.frobeniusPoints_apply_apply, pow_one, Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hodd
    have hsq : g.ofConv (MonoidAlgebra.single (RootsOfUnityGroup.generator 2) 1) ^ 2 = 1 := by
      rw [← map_pow, RootsOfUnityGroup.single_generator_pow_eq_one, map_one]
    rw [hk, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]
  rw [hfix]
  exact inv_mul_cancel g

/-- **Connectedness is essential for Lang's theorem**: for a finite field `F` of odd cardinality and
any nontrivial commutative `F`-algebra `K` (in particular any algebraically closed extension), the
Lang map of the `|F|`-Frobenius on `μ₂(K)` is not surjective, as it misses `-1`. -/
theorem not_surjective_inv_mul_rootsOfUnity_two
    {F : Type u} [Field F] [Fintype F] (hodd : Odd (Fintype.card F))
    {K : Type w} [CommRing K] [Nontrivial K] [Algebra F K] :
    ¬ Function.Surjective
        fun g : WithConv (MonoidAlgebra F (Multiplicative (ZMod 2)) →ₐ[F] K) =>
          g⁻¹ * FiniteField.frobeniusPoints F 1 g := by
  have htwoF : (2 : F) ≠ 0 := by
    have : CharP F (ringChar F) := ringChar.charP F
    obtain ⟨n, _, hq⟩ := _root_.FiniteField.card F (ringChar F)
    intro h2
    have hp : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F (ringChar F) 2).mp (by simpa using h2)
    have hpeven : Even (Fintype.card F) := by
      rw [hq]
      have hchar_eq : ringChar F = 2 := by
        have hprime := CharP.char_is_prime F (ringChar F)
        exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hp
      rw [hchar_eq]
      exact even_two.pow_of_ne_zero n.pos.ne'
    exact (Nat.not_even_iff_odd.mpr hodd) hpeven
  have hneg_ne_one : (-1 : K) ≠ 1 := by
    intro h
    have h2K : (2 : K) = 0 := by
      have h1 : (1 : K) + 1 = 0 := by
        calc
          (1 : K) + 1 = (-1 : K) + 1 := by rw [h]
          _ = 0 := neg_add_cancel 1
      simpa only [one_add_one_eq_two] using h1
    have h2F' : algebraMap F K 2 = 0 := by simpa only [map_ofNat] using h2K
    exact htwoF ((algebraMap F K).injective (h2F'.trans (map_zero _).symm))
  let negOne : rootsOfUnity 2 K := ⟨-1, by simp⟩
  let a : WithConv (MonoidAlgebra F (Multiplicative (ZMod 2)) →ₐ[F] K) :=
    (RootsOfUnityGroup.pointsMulEquiv (R := F) (A := K) 2).symm negOne
  intro hsurj
  obtain ⟨g, hg⟩ := hsurj a
  have ha1 : a = 1 := hg.symm.trans (inv_mul_frobeniusPoints_rootsOfUnity_two_eq_one hodd g)
  have hval := congrArg (fun p =>
    ((RootsOfUnityGroup.pointsMulEquiv (R := F) (A := K) 2 p : Kˣ) : K)) ha1
  simp only [a, MulEquiv.apply_symm_apply, map_one, OneMemClass.coe_one, Units.val_one] at hval
  exact hneg_ne_one hval

end TauCeti.Lang
