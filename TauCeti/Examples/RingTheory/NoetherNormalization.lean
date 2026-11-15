/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.RingTheory.NoetherNormalization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import TauCeti.AlgebraicGeometry.AffineSpace.NoetherNormalization

/-!
# Examples and counterexamples for linear Noether normalization

This file illustrates `TauCeti.exists_linear_normalization` and its geometric counterpart
`AlgebraicGeometry.AffineSpace.exists_linear_normalization`, together with concrete examples
showing that each hypothesis is sharp:

* **Coordinate tuple (`MvPolynomial (Fin n) k`).** The standard coordinates are linearly
  normalized by `d = n` and `C = 1`, whereas no matrix with a zero row yields algebraically
  independent linear combinations over a nontrivial base ring.
* **Nonreduced thickened line (`k[X₀, X₁] ⧸ (X₁²)`).** Projection onto the reduced coordinate
  `C = !![1, 0]` linearly normalizes the algebra with `d = 1`, whereas projection onto the
  nilpotent coordinate `C = !![0, 1]` is not algebraically independent.
* **Finite-field obstruction (`𝔽₂[X₀, X₁] ⧸ (X₀ X₁ (X₀ + X₁))`).** The union `F2LineUnion` of the
  three `𝔽₂`-rational lines through the origin in `𝔸²_{𝔽₂}` admits *no* linear Noether
  normalization over `𝔽₂` (`not_exists_linear_normalization_f2LineUnion`), certifying that
  `[Infinite k]` cannot be omitted, whereas the nonlinear homogeneous quadratic element
  `z = x₀² + x₀ x₁ + x₁²` normalizes the same algebra over `𝔽₂`
  (`nonlinear_normalization_f2LineUnion`).
* **Degenerate cases.** A subsingleton `k`-algebra over a nontrivial ring `k` admits no
  algebraically independent tuple (certifying `[Nontrivial A]`), while `A = k` with generator
  `![0]` (`n = 1`) is normalized solely at `d = 0 < n`.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped Matrix Polynomial

namespace TauCeti.Examples.NoetherNormalization

noncomputable section

-- The coordinate tuple `X : Fin n → MvPolynomial (Fin n) k` over any nontrivial commutative ring
-- is linearly normalized by `d = n` and `C = 1`, while any matrix with a zero row fails algebraic
-- independence.
example (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ) :
    (let y : Fin n → MvPolynomial (Fin n) k :=
        fun i ↦ ∑ j, (1 : Matrix (Fin n) (Fin n) k) i j • MvPolynomial.X j;
      AlgebraicIndependent k y ∧
        (MvPolynomial.aeval y : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k).Finite) ∧
    ∀ (d : ℕ) (C : Matrix (Fin d) (Fin n) k) (i : Fin d), C i = 0 →
      ¬ AlgebraicIndependent k
        (fun l ↦ ∑ j, C l j • (MvPolynomial.X j : MvPolynomial (Fin n) k)) := by
  refine ⟨?_, fun d C i hi hy ↦ hy.linearIndependent_of_sum_smul.ne_zero i hi⟩
  have hy : (fun i ↦ ∑ j, (1 : Matrix (Fin n) (Fin n) k) i j •
      (MvPolynomial.X j : MvPolynomial (Fin n) k)) = MvPolynomial.X := by
    ext i; simp [Matrix.one_apply]
  refine ⟨hy.symm ▸ MvPolynomial.algebraicIndependent_X (Fin n) k, ?_⟩
  rw [hy]
  exact RingHom.Finite.of_surjective _ fun p ↦ ⟨p, MvPolynomial.aeval_X_left_apply p⟩

/-- Integral-over-finite-type criterion for `AlgHom.Finite` into a quotient of a multivariate
polynomial algebra over a commutative ring `k`. -/
private theorem algHom_finite_of_quotient {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    {n : ℕ} {I : Ideal (MvPolynomial (Fin n) k)} (g : B →ₐ[k] MvPolynomial (Fin n) k ⧸ I)
    (hX : ∀ j : Fin n, g.toRingHom.IsIntegralElem (Ideal.Quotient.mk I (MvPolynomial.X j))) :
    g.Finite := by
  refine RingHom.IsIntegral.to_finite (fun a ↦ ?_)
    (.of_comp_finiteType (f := algebraMap k B) ?_)
  · refine Quotient.inductionOn' a fun p ↦ ?_
    induction p using MvPolynomial.induction_on with
    | C c =>
      change g.toRingHom.IsIntegralElem (Ideal.Quotient.mk I (MvPolynomial.C c))
      rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I),
        ← g.commutes]
      exact g.toRingHom.isIntegralElem_map
    | add p q hp hq =>
      change g.toRingHom.IsIntegralElem (Ideal.Quotient.mk I (p + q))
      rw [map_add]
      exact hp.add _ hq
    | mul_X p j hp =>
      change g.toRingHom.IsIntegralElem (Ideal.Quotient.mk I (p * MvPolynomial.X j))
      rw [map_mul]
      exact hp.mul _ (hX j)
  · convert (RingHom.finiteType_algebraMap (A := k) (B := MvPolynomial (Fin n) k ⧸ I)).mpr
      inferInstance
    exact RingHom.ext g.commutes

-- On the nonreduced thickened line `A = k[X₀, X₁] ⧸ (X₁²)` over a nontrivial commutative ring `k`,
-- `C = !![1, 0]` linearly normalizes `A` with `d = 1`, whereas `C = !![0, 1]` selects a nilpotent
-- element and is not algebraically independent.
example (k : Type*) [CommRing k] [Nontrivial k] :
    let I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {MvPolynomial.X 1 ^ 2}
    let A := MvPolynomial (Fin 2) k ⧸ I
    let x : Fin 2 → A := fun j ↦ Ideal.Quotient.mk I (MvPolynomial.X j)
    let y₀ : Fin 1 → A := fun i ↦ ∑ j, !![(1 : k), 0] i j • x j
    let y₁ : Fin 1 → A := fun i ↦ ∑ j, !![(0 : k), 1] i j • x j
    AlgebraicIndependent k y₀ ∧
      (MvPolynomial.aeval y₀ : MvPolynomial (Fin 1) k →ₐ[k] A).Finite ∧
      ¬ AlgebraicIndependent k y₁ := by
  intro I A x y₀ y₁
  have hx1_sq : x 1 ^ 2 = 0 := by
    dsimp only [x]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hy₀ : y₀ = ![x 0] := by ext i; fin_cases i; simp [y₀, Fin.sum_univ_two]
  have hy₁ : y₁ = ![x 1] := by ext i; fin_cases i; simp [y₁, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · let π : A →ₐ[k] MvPolynomial (Fin 1) k :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![MvPolynomial.X 0, 0]) fun p hp ↦
        RingHom.mem_ker.mp <| Ideal.span_le.mpr (by rintro _ ⟨rfl⟩; simp) hp
    have hπ : π (x 0) = MvPolynomial.X 0 := by
      simpa [x] using DFunLike.congr_fun
        (Ideal.Quotient.liftₐ_comp (R₁ := k) I (MvPolynomial.aeval ![MvPolynomial.X 0, 0]) _)
        (MvPolynomial.X 0)
    have hcomp : π.comp (MvPolynomial.aeval y₀) = AlgHom.id k (MvPolynomial (Fin 1) k) := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      rw [Subsingleton.elim i 0]
      simp [hy₀, hπ]
    exact Function.LeftInverse.injective (DFunLike.congr_fun hcomp)
  · refine algHom_finite_of_quotient _ fun j ↦ ?_
    fin_cases j
    · simpa [hy₀, x] using
        (MvPolynomial.aeval y₀ : MvPolynomial (Fin 1) k →ₐ[k] A).toRingHom.isIntegralElem_map
          (x := MvPolynomial.X 0)
    · exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simpa using hx1_sq⟩
  · intro hind
    have hzero : MvPolynomial.aeval y₁ (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) k) = 0 := by
      simpa [hy₁] using hx1_sq
    have hX2 := hind (hzero.trans (map_zero _).symm)
    exact (one_ne_zero (α := k)) (by simpa using congrArg (MvPolynomial.eval (1 : Fin 1 → k)) hX2)

/-- Defining polynomial `X₀ X₁ (X₀ + X₁)` of the three `𝔽₂`-rational lines through the origin. -/
abbrev f2Rel : MvPolynomial (Fin 2) (ZMod 2) :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1)

/-- Coordinate ring `𝔽₂[X₀, X₁] ⧸ (X₀ X₁ (X₀ + X₁))` of the union of three lines over `𝔽₂`. -/
abbrev F2LineUnion : Type :=
  MvPolynomial (Fin 2) (ZMod 2) ⧸ Ideal.span ({f2Rel} : Set (MvPolynomial (Fin 2) (ZMod 2)))

/-- Prescribed coordinate generators of `F2LineUnion`. -/
def f2Coord (j : Fin 2) : F2LineUnion :=
  Ideal.Quotient.mk _ (MvPolynomial.X j)

/-- For every vector `u : Fin 2 → ZMod 2`, substituting `Xⱼ ↦ uⱼ T` annihilates `f2Rel` and hence
descends to an `𝔽₂`-algebra homomorphism `F2LineUnion →ₐ[ZMod 2] (ZMod 2)[T]`. -/
private def f2LineProj (u : Fin 2 → ZMod 2) :
    F2LineUnion →ₐ[ZMod 2] Polynomial (ZMod 2) :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun j ↦ u j • Polynomial.X) fun p hp ↦ by
    refine RingHom.mem_ker.mp (Ideal.span_le.mpr ?_ hp)
    rintro _ ⟨rfl⟩
    have hu : u 0 * u 1 * (u 0 + u 1) = 0 := by
      revert u; decide
    simp only [SetLike.mem_coe, RingHom.mem_ker, f2Rel, map_mul, map_add, MvPolynomial.aeval_X,
      Algebra.smul_def]
    calc
      algebraMap (ZMod 2) _ (u 0) * Polynomial.X *
          (algebraMap (ZMod 2) _ (u 1) * Polynomial.X) *
          (algebraMap (ZMod 2) _ (u 0) * Polynomial.X +
            algebraMap (ZMod 2) _ (u 1) * Polynomial.X)
        = algebraMap (ZMod 2) _ (u 0 * u 1 * (u 0 + u 1)) * Polynomial.X ^ 3 := by
          simp only [map_mul, map_add]; ring
      _ = 0 := by simp [hu]

@[simp]
private theorem f2LineProj_f2Coord (u : Fin 2 → ZMod 2) (j : Fin 2) :
    f2LineProj u (f2Coord j) = u j • Polynomial.X := by
  rw [f2Coord, ← Ideal.Quotient.mkₐ_eq_mk (ZMod 2)]
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X, f2LineProj] using DFunLike.congr_fun
    (Ideal.Quotient.liftₐ_comp (R₁ := ZMod 2) _ (MvPolynomial.aeval fun j ↦ u j • Polynomial.X) _)
    (MvPolynomial.X j)

instance nontrivial_f2LineUnion : Nontrivial F2LineUnion :=
  (f2LineProj ![1, 0]).toRingHom.domain_nontrivial

/-- The coordinate classes `f2Coord` generate `F2LineUnion` as an `𝔽₂`-algebra. -/
theorem adjoin_range_f2Coord : Algebra.adjoin (ZMod 2) (Set.range f2Coord) = ⊤ := by
  rw [show Set.range f2Coord =
      Ideal.Quotient.mkₐ (ZMod 2) _ '' Set.range MvPolynomial.X by ext; simp [f2Coord],
    ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective _ _

private theorem exists_f2KernelVec_one (c : Fin 2 → ZMod 2) :
    ∃ u : Fin 2 → ZMod 2, (∃ j, u j = 1) ∧ dotProduct c u = 0 := by
  revert c; decide

/-- Every matrix `C : Matrix (Fin d) (Fin 2) (ZMod 2)` with `d < 2` kills a vector `u` that has an
entry equal to `1`. -/
private theorem exists_f2KernelVec {d : ℕ} (hd : d < 2) (C : Matrix (Fin d) (Fin 2) (ZMod 2)) :
    ∃ u : Fin 2 → ZMod 2, (∃ j, u j = 1) ∧ C *ᵥ u = 0 := by
  obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hd)
  · exact ⟨![1, 0], ⟨0, rfl⟩, Subsingleton.elim _ _⟩
  · obtain ⟨u, hj, hdot⟩ := exists_f2KernelVec_one (C 0)
    refine ⟨u, hj, ?_⟩
    ext i; fin_cases i; exact hdot

/-- A `2 × 2` matrix over `𝔽₂` cannot make the linear combinations of `f2Coord` algebraically
independent, because `f2Coord` satisfies the cubic relation `f2Rel = 0`. -/
private theorem not_algebraicIndependent_f2Coord_two (C : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    ¬ AlgebraicIndependent (ZMod 2) (fun i ↦ ∑ j, C i j • f2Coord j) := by
  intro hy
  obtain ⟨u, rfl⟩ : IsUnit C :=
    Matrix.linearIndependent_row_iff_isUnit.mp hy.linearIndependent_of_sum_smul
  let y : Fin 2 → F2LineUnion := fun i ↦ ∑ j, (↑u : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j • f2Coord j
  have hy_vec : (↑u : Matrix (Fin 2) (Fin 2) (ZMod 2)).map (algebraMap (ZMod 2) F2LineUnion) *ᵥ
      f2Coord = y := by
    ext i; simp [y, Matrix.mulVec, dotProduct, ← Algebra.smul_def]
  have hrel0 : MvPolynomial.aeval f2Coord f2Rel = 0 := by
    have hmk : MvPolynomial.aeval f2Coord = Ideal.Quotient.mkₐ (ZMod 2) _ :=
      MvPolynomial.algHom_ext fun j ↦ by simp [f2Coord]
    rw [hmk, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hy_rel : MvPolynomial.aeval y (MvPolynomial.linearSubst (↑u⁻¹) f2Rel) = 0 := by
    rw [MvPolynomial.aeval_linearSubst, ← hy_vec, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      u.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, hrel0]
  have hsub0 : MvPolynomial.linearSubst (↑u⁻¹) f2Rel = 0 :=
    hy (hy_rel.trans (map_zero _).symm)
  have hf2_zero : f2Rel = 0 := by
    have h := congrArg (MvPolynomial.linearSubst (↑u)) hsub0
    rwa [← MvPolynomial.linearSubst_mul_apply, u.inv_mul, MvPolynomial.linearSubst_one,
      AlgHom.id_apply, map_zero] at h
  have hcoeff : (1 : ZMod 2) = 0 := by
    simpa [f2Rel, mul_add] using congrArg
      (fun p ↦ (MvPolynomial.aeval (![Polynomial.X, 1] : Fin 2 → Polynomial (ZMod 2)) p).coeff 1)
      hf2_zero
  exact one_ne_zero hcoeff

/-- **Finite-field obstruction to linear Noether normalization.** The nontrivial `𝔽₂`-algebra
`F2LineUnion = 𝔽₂[X₀, X₁] ⧸ (X₀ X₁ (X₀ + X₁))` generated by `f2Coord` admits *no* `(d, C)` such
that the `𝔽₂`-linear combinations `yᵢ = ∑ⱼ Cᵢⱼ f2Coordⱼ` are algebraically independent over `𝔽₂`
and `F2LineUnion` is finite over `𝔽₂[y₁, …, y_d]`. -/
theorem not_exists_linear_normalization_f2LineUnion :
    ¬ ∃ (d : ℕ) (C : Matrix (Fin d) (Fin 2) (ZMod 2)),
      let y : Fin d → F2LineUnion := fun i ↦ ∑ j, C i j • f2Coord j
      AlgebraicIndependent (ZMod 2) y ∧
        (MvPolynomial.aeval y : MvPolynomial (Fin d) (ZMod 2) →ₐ[ZMod 2] F2LineUnion).Finite := by
  rintro ⟨d, C, hy, hfin⟩
  have hd2 : d ≤ 2 := by simpa using card_le_of_algebraicIndependent_sum_smul hy
  obtain hd_lt | rfl := lt_or_eq_of_le hd2
  · obtain ⟨u, ⟨j₀, hj₀⟩, hu⟩ := exists_f2KernelVec hd_lt C
    have hπ_surj : Function.Surjective (f2LineProj u) := by
      rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X (R := ZMod 2),
        Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨f2Coord j₀, by simp [hj₀]⟩
    have hπy (i : Fin d) : f2LineProj u (∑ j, C i j • f2Coord j) = 0 := by
      have hval : (C *ᵥ u) i = 0 := congrFun hu i
      rw [map_sum]
      simp_rw [map_smul, f2LineProj_f2Coord, smul_smul, ← Finset.sum_smul]
      simpa [Matrix.mulVec, dotProduct] using
        congrArg (· • (Polynomial.X : Polynomial (ZMod 2))) hval
    have hcomp : (f2LineProj u).comp (MvPolynomial.aeval fun i ↦ ∑ j, C i j • f2Coord j) =
        (Algebra.ofId (ZMod 2) (Polynomial (ZMod 2))).comp (MvPolynomial.aeval 0) := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Pi.zero_apply, map_zero]
      exact hπy i
    have hint : ((f2LineProj u).comp
        (MvPolynomial.aeval fun i ↦ ∑ j, C i j • f2Coord j)).toRingHom.IsIntegralElem
        Polynomial.X :=
      (hfin.to_isIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ hπ_surj)) Polynomial.X
    rw [congrArg AlgHom.toRingHom hcomp] at hint
    obtain ⟨q, hmonic, hq⟩ := RingHom.IsIntegralElem.of_comp hint
    exact hmonic.ne_zero (by simpa [Polynomial.eval₂_C_X] using hq)
  · exact not_algebraicIndependent_f2Coord_two C hy

/-- **Nonlinear Noether normalization over `𝔽₂`.** On `F2LineUnion`, the nonlinear homogeneous
quadratic element `z = x₀² + x₀ x₁ + x₁²` is algebraically independent over `𝔽₂` and `F2LineUnion`
is finite over `𝔽₂[z]`. -/
theorem nonlinear_normalization_f2LineUnion :
    let z : F2LineUnion := f2Coord 0 ^ 2 + f2Coord 0 * f2Coord 1 + f2Coord 1 ^ 2
    AlgebraicIndependent (ZMod 2) ![z] ∧
      (MvPolynomial.aeval ![z] : MvPolynomial (Fin 1) (ZMod 2) →ₐ[ZMod 2] F2LineUnion).Finite := by
  intro z
  have hrel0 : f2Coord 0 * f2Coord 1 * (f2Coord 0 + f2Coord 1) = 0 := by
    change Ideal.Quotient.mk _ f2Rel = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  refine ⟨?_, ?_⟩
  · rw [algebraicIndependent_iff_transcendental, transcendental_iff_injective]
    have hX2 : Function.Injective
        (Polynomial.aeval (Polynomial.X ^ 2 : Polynomial (ZMod 2))) :=
      transcendental_iff_injective.mp <|
        Polynomial.transcendental (Polynomial.X ^ 2) (by simp) (by simp)
    have hπz : f2LineProj ![1, 0] z = Polynomial.X ^ 2 := by simp [z]
    have hcomp : ⇑(f2LineProj ![1, 0]) ∘ ⇑(Polynomial.aeval (R := ZMod 2) z) =
        ⇑(Polynomial.aeval (Polynomial.X ^ 2 : Polynomial (ZMod 2))) := by
      have halg : (f2LineProj ![1, 0]).comp (Polynomial.aeval (R := ZMod 2) z) =
          Polynomial.aeval (Polynomial.X ^ 2 : Polynomial (ZMod 2)) := by
        ext; simp [hπz]
      exact congrArg DFunLike.coe halg
    exact Function.Injective.of_comp (f := f2LineProj ![1, 0]) (hcomp.symm ▸ hX2)
  · refine algHom_finite_of_quotient _ fun j ↦ ?_
    refine ⟨Polynomial.X ^ 3 - Polynomial.C (MvPolynomial.X 0) * Polynomial.X, ?_, ?_⟩
    · refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 3) ?_
      calc
        (Polynomial.C (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 2)) *
            Polynomial.X).degree
          ≤ ↑((Polynomial.C (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 2)) *
              Polynomial.X).natDegree) := Polynomial.degree_le_natDegree
        _ ≤ (1 : WithBot ℕ) := WithBot.coe_le_coe.mpr
            (le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le)
        _ < (Polynomial.X ^ 3 : (MvPolynomial (Fin 1) (ZMod 2))[X]).degree := by simp
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.aeval_X, Matrix.cons_val_zero]
      change f2Coord j ^ 3 - z * f2Coord j = 0
      fin_cases j
      · calc
          f2Coord 0 ^ 3 - (f2Coord 0 ^ 2 + f2Coord 0 * f2Coord 1 + f2Coord 1 ^ 2) * f2Coord 0
            = -(f2Coord 0 * f2Coord 1 * (f2Coord 0 + f2Coord 1)) := by ring
          _ = 0 := by simp [hrel0]
      · calc
          f2Coord 1 ^ 3 - (f2Coord 0 ^ 2 + f2Coord 0 * f2Coord 1 + f2Coord 1 ^ 2) * f2Coord 1
            = -(f2Coord 0 * f2Coord 1 * (f2Coord 0 + f2Coord 1)) := by ring
          _ = 0 := by simp [hrel0]

-- Sharpness of `[Nontrivial A]`: a subsingleton `k`-algebra over a nontrivial commutative ring `k`
-- admits no algebraically independent family of any arity `d`.
example (k A : Type*) [CommRing k] [Nontrivial k] [CommRing A] [Subsingleton A] [Algebra k A]
    (d : ℕ) (y : Fin d → A) : ¬ AlgebraicIndependent k y := fun hy ↦
  zero_ne_one (hy (Subsingleton.elim (MvPolynomial.aeval y (0 : MvPolynomial (Fin d) k))
    (MvPolynomial.aeval y 1)))

-- Strict dimension drop (`d = 0 < n`): `A = k` with generator `x = ![0]` (`n = 1`) over a
-- nontrivial commutative ring `k` is normalized at `d = 0`, whereas no `d ≥ 1` gives algebraically
-- independent linear combinations.
example (k : Type*) [CommRing k] [Nontrivial k] :
    let x : Fin 1 → k := ![0]
    Algebra.adjoin k (Set.range x) = ⊤ ∧
      (let y : Fin 0 → k := fun i ↦ ∑ j, (0 : Matrix (Fin 0) (Fin 1) k) i j • x j;
        AlgebraicIndependent k y ∧
          (MvPolynomial.aeval y : MvPolynomial (Fin 0) k →ₐ[k] k).Finite) ∧
      ∀ (d : ℕ), 0 < d → ∀ C : Matrix (Fin d) (Fin 1) k,
        ¬ AlgebraicIndependent k (fun i ↦ ∑ j, C i j • x j) := by
  intro x
  refine ⟨eq_top_iff.mpr fun a _ ↦ Subalgebra.algebraMap_mem _ a, ⟨?_, ?_⟩, ?_⟩
  · exact algebraicIndependent_empty_type_iff.mpr Function.injective_id
  · exact RingHom.Finite.of_surjective _ fun a ↦ ⟨MvPolynomial.C a, MvPolynomial.aeval_C _ a⟩
  · intro d hd C hy
    let i₀ : Fin d := ⟨0, hd⟩
    have hzero : MvPolynomial.aeval (fun i ↦ ∑ j, C i j • x j)
        (MvPolynomial.X i₀ : MvPolynomial (Fin d) k) = 0 := by
      simp [x]
    exact MvPolynomial.X_ne_zero i₀ (hy (hzero.trans (map_zero _).symm))

-- Geometric linear Noether normalization on the coordinate axes `V(X₀ X₁) ⊂ 𝔸²_ℚ`: the coordinate
-- embedding into `𝔸(ULift (Fin 2); Spec ℚ)` is a closed immersion whose composition with a
-- `ℚ`-linear projection to `𝔸(ULift (Fin d); Spec ℚ)` (`d ≤ 2`) is finite and surjective.
example :
    let I : Ideal (MvPolynomial (Fin 2) ℚ) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    let A := MvPolynomial (Fin 2) ℚ ⧸ I
    let x : Fin 2 → A := fun j ↦ Ideal.Quotient.mk I (MvPolynomial.X j)
    IsClosedImmersion (AffineSpace.specHomOfTuple ℚ (x ∘ ULift.down : ULift.{0} (Fin 2) → A)) ∧
      ∃ (d : ℕ) (_ : d ≤ 2)
        (C : Matrix (ULift.{0} (Fin d)) (ULift.{0} (Fin 2)) Γ(Spec (.of ℚ), ⊤)),
        let π := AffineSpace.specHomOfTuple ℚ (x ∘ ULift.down : ULift.{0} (Fin 2) → A) ≫
          AffineSpace.linearMap (Spec (.of ℚ)) C
        IsFinite π ∧ Surjective π ∧ ringKrullDim A = (d : WithBot ℕ∞) := by
  intro I A x
  have : Nontrivial A :=
    (Ideal.Quotient.lift I (MvPolynomial.eval 0) fun p hp ↦
      RingHom.mem_ker.mp <| Ideal.span_le.mpr (by rintro _ ⟨rfl⟩; simp) hp).domain_nontrivial
  have hx : Algebra.adjoin ℚ (Set.range x) = ⊤ := by
    rw [show Set.range x = Ideal.Quotient.mkₐ ℚ I '' Set.range MvPolynomial.X by ext; simp [x],
      ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective ℚ I
  exact AffineSpace.exists_linear_normalization x hx

end

end TauCeti.Examples.NoetherNormalization
