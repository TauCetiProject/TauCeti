/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Expand
import TauCeti.AlgebraicGeometry.AffineSpace.Linear

/-!
# Examples and counterexamples for linear Noether normalization

* **Polynomial rings:** `MvPolynomial (Fin n) k` is normalized in its standard generators `X` by
  the identity matrix `1 : Matrix (Fin n) (Fin n) k` with `d = n`.
* **Zero-dimensional presentations:** a field `k` presented by a single generator `![0] : Fin 1 → k`
  is normalized with `d = 0` and the unique `0 × 1` matrix over `k`.
* **Nonreduced algebras:** `k[X₀, X₁] ⧸ (X₁²)` is nonreduced (`X₁ ≠ 0`, `X₁² = 0`) and is
  normalized by the projection matrix `!![1, 0] : Matrix (Fin 1) (Fin 2) k` onto `X₀` (`d = 1`).
* **Failure of linearity over finite fields:** over `𝔽₂ = ZMod 2`, the coordinate ring
  `A = 𝔽₂[X₀, X₁] ⧸ (X₀ X₁ (X₀ + X₁))` of the union of the three `𝔽₂`-rational lines through the
  origin admits *no* `𝔽₂`-linear normalizing parameter `c₀ x₀ + c₁ x₁`, because every `𝔽₂`-linear
  form vanishes identically along one of the three lines `X₀ = 0`, `X₁ = 0`, or `X₀ + X₁ = 0`.
  By contrast, the quadratic polynomial `z = x₀² + x₀ x₁ + x₁²` is algebraically independent over
  `𝔽₂` and makes `A` module-finite over `𝔽₂[Z]` (since `xᵢ³ - z xᵢ = 0` for `i = 0, 1`).

## References

* J. S. Milne, *Algebraic Geometry*, Remark 2.47.
* J. S. Milne, *A Primer of Commutative Algebra*, Remark 8.4.
-/

namespace TauCeti.NoetherNormalizationExamples

open CategoryTheory MvPolynomial TauCeti

-- A polynomial ring `k[X₀, …, Xₙ₋₁]` is normalized by the identity matrix `1` with `d = n`.
example (k : Type*) [Field k] (n : ℕ) :
    let y : Fin n → MvPolynomial (Fin n) k :=
      fun i ↦ ∑ j, (1 : Matrix (Fin n) (Fin n) k) i j • X j
    AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧
      ringKrullDim (MvPolynomial (Fin n) k) = n := by
  dsimp only
  have hy : (fun i : Fin n ↦ ∑ j : Fin n,
      (1 : Matrix (Fin n) (Fin n) k) i j • (X j : MvPolynomial (Fin n) k)) = X := by
    funext i
    simp [Matrix.one_apply]
  have hind : AlgebraicIndependent k (X : Fin n → MvPolynomial (Fin n) k) :=
    algebraicIndependent_iff_injective_aeval.mpr
      (by simpa [aeval_X_left] using Function.injective_id)
  have hfin : (aeval (R := k) (X : Fin n → MvPolynomial (Fin n) k)).Finite := by
    change (aeval (R := k) (X : Fin n → MvPolynomial (Fin n) k)).toRingHom.Finite
    rw [aeval_X_left]
    exact RingHom.Finite.of_surjective _ Function.surjective_id
  rw [hy]
  exact ⟨hind, hfin, by simp⟩

-- A zero-dimensional presentation of `k` by `![0] : Fin 1 → k` normalizes with `d = 0`.
example (k : Type*) [Field k] :
    let x : Fin 1 → k := ![0]
    let y : Fin 0 → k := fun i ↦ ∑ j, (0 : Matrix (Fin 0) (Fin 1) k) i j • x j
    Algebra.adjoin k (Set.range x) = ⊤ ∧
      AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧ ringKrullDim k = (0 : ℕ) := by
  dsimp only
  have hadj : Algebra.adjoin k (Set.range (![0] : Fin 1 → k)) = ⊤ :=
    eq_top_iff.mpr fun a _ ↦ by simp
  have hind : AlgebraicIndependent k
      (fun i : Fin 0 ↦ ∑ j : Fin 1, (0 : Matrix (Fin 0) (Fin 1) k) i j • (![0] : Fin 1 → k) j) :=
    algebraicIndependent_empty_type_iff.mpr (algebraMap k k).injective
  have hsurj : Function.Surjective (aeval (R := k)
      (fun i : Fin 0 ↦ ∑ j : Fin 1, (0 : Matrix (Fin 0) (Fin 1) k) i j • (![0] : Fin 1 → k) j)) :=
    fun a ↦ ⟨MvPolynomial.C a, by simp⟩
  exact ⟨hadj, hind, RingHom.Finite.of_surjective _ hsurj, by simp⟩

-- The nonreduced algebra `k[X₀, X₁] ⧸ (X₁²)` is normalized by `C = !![1, 0]` (`d = 1`) while
-- retaining nonzero nilpotents.
example (k : Type*) [Field k] :
    ¬ IsReduced (MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2}) ∧
      Algebra.adjoin k (Set.range fun j : Fin 2 ↦
        Ideal.Quotient.mk (Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2}) (X j)) = ⊤ ∧
      AlgebraicIndependent k (fun i : Fin 1 ↦
        ∑ j : Fin 2, (!![1, 0] : Matrix (Fin 1) (Fin 2) k) i j •
          Ideal.Quotient.mk (Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2}) (X j)) ∧
      (aeval (R := k) fun i : Fin 1 ↦
        ∑ j : Fin 2, (!![1, 0] : Matrix (Fin 1) (Fin 2) k) i j •
          Ideal.Quotient.mk (Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2}) (X j)).Finite ∧
      ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 1 : MvPolynomial (Fin 2) k) ^ 2}) =
        (1 : ℕ) := by
  set I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 1 ^ 2}
  set x : Fin 2 → MvPolynomial (Fin 2) k ⧸ I := fun j ↦ Ideal.Quotient.mk I (X j)
  set y : Fin 1 → MvPolynomial (Fin 2) k ⧸ I :=
    fun i ↦ ∑ j, (!![1, 0] : Matrix (Fin 1) (Fin 2) k) i j • x j
  have hx1_sq : x 1 ^ 2 = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hnot_red : ¬ IsReduced (MvPolynomial (Fin 2) k ⧸ I) := by
    intro hred
    let toDual : (MvPolynomial (Fin 2) k ⧸ I) →+* DualNumber k :=
      Ideal.Quotient.lift I (aeval (R := k) ![0, DualNumber.eps]).toRingHom fun p hp ↦
        RingHom.mem_ker.mp <| Ideal.span_le.mpr
          (by rintro _ rfl; simp [DualNumber.eps_mul_eps, sq]) hp
    have heps : (DualNumber.eps : DualNumber k) = 0 := by
      have h0 := congrArg toDual (hred.eq_zero (x 1) ⟨2, hx1_sq⟩)
      simpa [toDual, x, Ideal.Quotient.lift_mk] using h0
    exact one_ne_zero (α := k) (by simpa using congrArg TrivSqZeroExt.snd heps)
  have hadj : Algebra.adjoin k (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    have hmk : aeval (R := k) x = Ideal.Quotient.mkₐ k I :=
      MvPolynomial.algHom_ext fun j ↦ by simp [x, Ideal.Quotient.mkₐ_eq_mk]
    exact hmk ▸ Ideal.Quotient.mk_surjective
  have hy0 : y = ![x 0] := funext <| Fin.forall_fin_one.mpr (by simp [y, Fin.sum_univ_two])
  let proj : (MvPolynomial (Fin 2) k ⧸ I) →+* MvPolynomial (Fin 1) k :=
    Ideal.Quotient.lift I (aeval (R := k) ![X 0, 0]).toRingHom fun p hp ↦
      RingHom.mem_ker.mp <| Ideal.span_le.mpr (by rintro _ rfl; simp) hp
  have hind : AlgebraicIndependent k y := by
    rw [algebraicIndependent_iff_injective_aeval]
    have hleft : proj.comp (aeval (R := k) y).toRingHom = RingHom.id _ :=
      MvPolynomial.ringHom_ext
        (fun r ↦ by
          simp [proj, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k),
            Ideal.Quotient.algebraMap_eq]) <|
        Fin.forall_fin_one.mpr (by simp [proj, hy0, x])
    exact Function.LeftInverse.injective fun p ↦ congr($hleft p)
  have hfin : (aeval (R := k) y).Finite := by
    refine finite_aeval_of_adjoin_eq_top hadj <| Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simpa [hy0] using RingHom.isIntegralElem_map (aeval (R := k) y).toRingHom (x := X 0)
    · exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [hx1_sq]⟩
  have : Nontrivial (MvPolynomial (Fin 2) k ⧸ I) :=
    ⟨⟨1, 0, fun h ↦ by simpa using congrArg proj h⟩⟩
  have hint : (aeval (R := k) y).toRingHom.IsIntegral := hfin.to_isIntegral
  exact ⟨hnot_red, hadj, hind, hfin, by
    simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial
      (aeval (R := k) y).toRingHom (algebraicIndependent_iff_injective_aeval.mp hind) hint⟩

-- Over `𝔽₂ = ZMod 2`, NO linear combination `c 0 • x 0 + c 1 • x 1` of the coordinate generators
-- makes `𝔽₂[X₀, X₁] ⧸ (X₀ X₁ (X₀ + X₁))` integral (hence nor module-finite) over `𝔽₂[Y]`.
example (c : Fin 2 → ZMod 2) :
    ¬ (aeval (R := ZMod 2) (![c 0 • Ideal.Quotient.mk
        (Ideal.span {(X 0 : MvPolynomial (Fin 2) (ZMod 2)) * X 1 * (X 0 + X 1)}) (X 0) +
      c 1 • Ideal.Quotient.mk
        (Ideal.span {(X 0 : MvPolynomial (Fin 2) (ZMod 2)) * X 1 * (X 0 + X 1)}) (X 1)] :
      Fin 1 → _)).toRingHom.IsIntegral := by
  set I : Ideal (MvPolynomial (Fin 2) (ZMod 2)) := Ideal.span {X 0 * X 1 * (X 0 + X 1)}
  set x : Fin 2 → MvPolynomial (Fin 2) (ZMod 2) ⧸ I := fun j ↦ Ideal.Quotient.mk I (X j)
  set y : Fin 1 → MvPolynomial (Fin 2) (ZMod 2) ⧸ I := ![c 0 • x 0 + c 1 • x 1]
  have hdir : ∃ (u : Fin 2 → ZMod 2) (i₀ : Fin 2),
      u 0 * u 1 * (u 0 + u 1) = 0 ∧ c 0 * u 0 + c 1 * u 1 = 0 ∧ u i₀ = 1 := by
    by_cases hc0 : c 0 = 0
    · exact ⟨![1, 0], 0, by simp, by simp [hc0], rfl⟩
    · by_cases hc1 : c 1 = 0
      · exact ⟨![0, 1], 1, by simp, by simp [hc1], rfl⟩
      · have hne : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
        exact ⟨![1, 1], 0, by decide, by rw [hne _ hc0, hne _ hc1]; decide, rfl⟩
  obtain ⟨u, i₀, hu_rel, hu_orth, hui₀⟩ := hdir
  let lineHom : (MvPolynomial (Fin 2) (ZMod 2) ⧸ I) →+* Polynomial (ZMod 2) :=
    Ideal.Quotient.lift I
      (aeval (R := ZMod 2) fun j ↦ Polynomial.C (u j) * Polynomial.X).toRingHom fun p hp ↦
        RingHom.mem_ker.mp <| Ideal.span_le.mpr (by
          rintro _ rfl
          have hcalc : (Polynomial.C (u 0) * Polynomial.X) * (Polynomial.C (u 1) * Polynomial.X) *
              (Polynomial.C (u 0) * Polynomial.X + Polynomial.C (u 1) * Polynomial.X) =
              Polynomial.C (u 0 * u 1 * (u 0 + u 1)) * Polynomial.X ^ 3 := by
            simp only [map_add, map_mul]; ring
          simp [hcalc, hu_rel]) hp
  have hy0 : lineHom (y 0) = 0 := by
    have hsmul (j : Fin 2) :
        lineHom (c j • x j) = Polynomial.C (c j) * (Polynomial.C (u j) * Polynomial.X) := by
      change lineHom (Ideal.Quotient.mk I (c j • X j)) = _
      simp [lineHom, Algebra.smul_def, Polynomial.algebraMap_eq]
    have hlin : Polynomial.C (c 0) * (Polynomial.C (u 0) * Polynomial.X) +
        Polynomial.C (c 1) * (Polynomial.C (u 1) * Polynomial.X) =
        Polynomial.C (c 0 * u 0 + c 1 * u 1) * Polynomial.X := by
      simp only [map_add, map_mul]; ring
    simp only [y, Matrix.cons_val_zero, map_add, hsmul, hlin, hu_orth, map_zero, zero_mul]
  intro hint
  obtain ⟨P, hP_monic, hP_eval⟩ := hint (x i₀)
  have hcomp : lineHom.comp (aeval (R := ZMod 2) y).toRingHom =
      Polynomial.C.comp (MvPolynomial.eval 0) :=
    MvPolynomial.ringHom_ext
      (fun r ↦ by
        simp [lineHom, IsScalarTower.algebraMap_apply (ZMod 2) (MvPolynomial (Fin 2) (ZMod 2)),
          Ideal.Quotient.algebraMap_eq, Polynomial.algebraMap_eq]) <|
      Fin.forall_fin_one.mpr (by simp [hy0])
  have hmap : P.map (MvPolynomial.eval (0 : Fin 1 → ZMod 2)) = 0 := by
    have h0 := congrArg lineHom hP_eval
    rw [Polynomial.hom_eval₂, hcomp, map_zero] at h0
    have hxi₀ : lineHom (x i₀) = Polynomial.X := by simp [lineHom, x, hui₀]
    rwa [hxi₀, ← Polynomial.eval₂_map, Polynomial.eval₂_C_X] at h0
  exact (hP_monic.map (MvPolynomial.eval (0 : Fin 1 → ZMod 2))).ne_zero hmap

-- Over `𝔽₂ = ZMod 2`, the nonlinear quadratic element `z = x₀² + x₀ x₁ + x₁²` DOES normalize
-- `𝔽₂[X₀, X₁] ⧸ (X₀ X₁ (X₀ + X₁))` (`d = 1`).
example :
    let I : Ideal (MvPolynomial (Fin 2) (ZMod 2)) := Ideal.span {X 0 * X 1 * (X 0 + X 1)}
    let x : Fin 2 → MvPolynomial (Fin 2) (ZMod 2) ⧸ I := fun j ↦ Ideal.Quotient.mk I (X j)
    let y : Fin 1 → MvPolynomial (Fin 2) (ZMod 2) ⧸ I := ![x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2]
    Algebra.adjoin (ZMod 2) (Set.range x) = ⊤ ∧
      AlgebraicIndependent (ZMod 2) y ∧ (aeval (R := ZMod 2) y).Finite ∧
        ringKrullDim (MvPolynomial (Fin 2) (ZMod 2) ⧸ I) = (1 : ℕ) := by
  dsimp only
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Ideal (MvPolynomial (Fin 2) (ZMod 2)) := Ideal.span {X 0 * X 1 * (X 0 + X 1)}
  set x : Fin 2 → MvPolynomial (Fin 2) (ZMod 2) ⧸ I := fun j ↦ Ideal.Quotient.mk I (X j)
  set y : Fin 1 → MvPolynomial (Fin 2) (ZMod 2) ⧸ I := ![x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2]
  have hadj : Algebra.adjoin (ZMod 2) (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    have hmk : aeval (R := ZMod 2) x = Ideal.Quotient.mkₐ (ZMod 2) I :=
      MvPolynomial.algHom_ext fun j ↦ by simp [x, Ideal.Quotient.mkₐ_eq_mk]
    exact hmk ▸ Ideal.Quotient.mk_surjective
  let axisHom : (MvPolynomial (Fin 2) (ZMod 2) ⧸ I) →+* MvPolynomial (Fin 1) (ZMod 2) :=
    Ideal.Quotient.lift I (aeval (R := ZMod 2) ![X 0, 0]).toRingHom fun p hp ↦
      RingHom.mem_ker.mp <| Ideal.span_le.mpr (by rintro _ rfl; simp) hp
  have hind : AlgebraicIndependent (ZMod 2) y := by
    rw [algebraicIndependent_iff_injective_aeval]
    have hexp : axisHom.comp (aeval (R := ZMod 2) y).toRingHom =
        (MvPolynomial.expand 2).toRingHom :=
      MvPolynomial.ringHom_ext
        (fun r ↦ by
          simp [axisHom, IsScalarTower.algebraMap_apply (ZMod 2) (MvPolynomial (Fin 2) (ZMod 2)),
            Ideal.Quotient.algebraMap_eq]) <|
        Fin.forall_fin_one.mpr (by simp [axisHom, y, x, expand_X])
    exact Function.Injective.of_comp (f := axisHom) <| by
      change Function.Injective (axisHom.comp (aeval (R := ZMod 2) y).toRingHom)
      rw [hexp]
      exact MvPolynomial.expand_injective (by positivity)
  have hpoly : ∀ j : Fin 2, (X j : MvPolynomial (Fin 2) (ZMod 2)) ^ 3 -
      (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2) * X j = -(X 0 * X 1 * (X 0 + X 1)) :=
    Fin.forall_fin_two.mpr ⟨by ring, by ring⟩
  have hcubic (j : Fin 2) : x j ^ 3 - y 0 * x j = 0 := by
    have hmk : Ideal.Quotient.mk I
        ((X j : MvPolynomial (Fin 2) (ZMod 2)) ^ 3 -
          (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2) * X j) = 0 := by
      rw [hpoly j, map_neg, neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    simpa [y, x, map_sub, map_add, map_mul, map_pow] using hmk
  have hfin : (aeval (R := ZMod 2) y).Finite := by
    refine finite_aeval_of_adjoin_eq_top hadj fun j ↦ ?_
    refine ⟨Polynomial.X ^ 3 - Polynomial.C (X 0) * Polynomial.X,
      Polynomial.monic_X_pow_sub ((Polynomial.degree_C_mul_X_le _).trans_lt (by norm_num)), ?_⟩
    simpa using hcubic j
  have : Nontrivial (MvPolynomial (Fin 2) (ZMod 2) ⧸ I) :=
    ⟨⟨1, 0, fun h ↦ by simpa using congrArg axisHom h⟩⟩
  have hint : (aeval (R := ZMod 2) y).toRingHom.IsIntegral := hfin.to_isIntegral
  exact ⟨hadj, hind, hfin, by
    simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial (k := ZMod 2)
      (aeval (R := ZMod 2) y).toRingHom
      (algebraicIndependent_iff_injective_aeval.mp hind) hint⟩

-- Geometric linear Noether normalization specializes cleanly to closed subschemes of `𝔸ⁿ_k`.
universe u in
example (k A : Type u) [Field k] [Infinite k] [CommRing A] [Nontrivial A] [Algebra k A]
    (n : ℕ) (x : Fin n → A) (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    AlgebraicGeometry.IsClosedImmersion
        (AlgebraicGeometry.AffineSpace.homOfAlgebra (R := k) (x ∘ ULift.down)) ∧
      ∃ (d : ℕ) (_ : d ≤ n) (C : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin n)) k),
        let π := AlgebraicGeometry.AffineSpace.homOfAlgebra (R := k) (x ∘ ULift.down) ≫
          AlgebraicGeometry.AffineSpace.linearMap (AlgebraicGeometry.Spec (.of k))
            (C.map (AlgebraicGeometry.Scheme.ΓSpecIso (.of k)).inv)
        AlgebraicGeometry.IsFinite π ∧ AlgebraicGeometry.Surjective π ∧
          (∀ q, (π ⁻¹' {q}).Finite) ∧ ringKrullDim A = d :=
  AlgebraicGeometry.AffineSpace.exists_linear_normalization x hx

end TauCeti.NoetherNormalizationExamples
