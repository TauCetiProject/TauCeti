/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.RingTheory.NoetherNormalization
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Expand
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Examples and counterexamples for linear Noether normalization

* **Polynomial rings:** `MvPolynomial (Fin n) k` is normalized in its standard generators `X` by
  the identity matrix `1 : Matrix (Fin n) (Fin n) k` with `d = n`.
* **Zero-dimensional presentations:** a field `k` presented by a single generator `![0] : Fin 1 → k`
  is normalized with `d = 0` and the unique `0 × 1` matrix over `k`.
* **Nonreduced algebras:** `k[X₀, X₁] ⧸ (X₁²)` is nonreduced (`X₁ ≠ 0`, `X₁² = 0`) and is
  normalized by the projection matrix `!![1, 0] : Matrix (Fin 1) (Fin 2) k` onto `X₀` (`d = 1`;
  `algebraicIndependent_mk_span_X_one_sq`, `finite_aeval_mk_span_X_one_sq`).
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

public section

namespace TauCeti.NoetherNormalizationExamples

open MvPolynomial TauCeti

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
  have hfin : (aeval (R := k) (X : Fin n → MvPolynomial (Fin n) k)).Finite := by
    rw [aeval_X_left]
    exact AlgHom.Finite.id k _
  rw [hy]
  exact ⟨MvPolynomial.algebraicIndependent_X (Fin n) k, hfin, by simp⟩

-- A zero-dimensional presentation of `k` by `![0] : Fin 1 → k` normalizes with `d = 0`.
example (k : Type*) [Field k] :
    let x : Fin 1 → k := ![0]
    let y : Fin 0 → k := fun i ↦ ∑ j, (0 : Matrix (Fin 0) (Fin 1) k) i j • x j
    Algebra.adjoin k (Set.range x) = ⊤ ∧
      AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧ ringKrullDim k = (0 : ℕ) := by
  dsimp only
  have hadj : Algebra.adjoin k (Set.range (![0] : Fin 1 → k)) = ⊤ :=
    eq_top_iff.mpr fun a _ ↦ by
      simpa using (Algebra.adjoin k (Set.range (![0] : Fin 1 → k))).algebraMap_mem a
  have hind : AlgebraicIndependent k
      (fun i : Fin 0 ↦ ∑ j : Fin 1, (0 : Matrix (Fin 0) (Fin 1) k) i j • (![0] : Fin 1 → k) j) :=
    algebraicIndependent_empty_type_iff.mpr (algebraMap k k).injective
  have hsurj : Function.Surjective (aeval (R := k)
      (fun i : Fin 0 ↦ ∑ j : Fin 1, (0 : Matrix (Fin 0) (Fin 1) k) i j • (![0] : Fin 1 → k) j)) :=
    fun a ↦ ⟨MvPolynomial.C a, by simp⟩
  exact ⟨hadj, hind, AlgHom.Finite.of_surjective _ hsurj, by simp⟩

/-- In `R[X₀, X₁] ⧸ (X₁²)`, the residue class of `X₀` indexed by `Fin 1` is algebraically
independent over `R`. -/
theorem algebraicIndependent_mk_span_X_one_sq (R : Type*) [CommRing R] :
    AlgebraicIndependent R (fun _ : Fin 1 ↦
      Ideal.Quotient.mk (Ideal.span {(X 1 : MvPolynomial (Fin 2) R) ^ 2}) (X 0)) := by
  set I : Ideal (MvPolynomial (Fin 2) R) := Ideal.span {X 1 ^ 2}
  have hproj_ker :
      ∀ p ∈ I, (aeval (R := R) (![X 0, 0] : Fin 2 → MvPolynomial (Fin 1) R)) p = 0 :=
    fun p hp ↦ RingHom.mem_ker.mp <| Ideal.span_le.mpr (by rintro _ rfl; simp) hp
  let proj : (MvPolynomial (Fin 2) R ⧸ I) →ₐ[R] MvPolynomial (Fin 1) R :=
    Ideal.Quotient.liftₐ I (aeval (R := R) ![X 0, 0]) hproj_ker
  have hproj : proj (Ideal.Quotient.mk I (X 0)) = X 0 := by
    simpa [proj] using congr($(Ideal.Quotient.liftₐ_comp I _ hproj_ker) (X 0))
  rw [algebraicIndependent_iff_injective_aeval]
  have hleft : proj.comp (aeval (R := R) fun _ : Fin 1 ↦ Ideal.Quotient.mk I (X 0)) =
      AlgHom.id R _ :=
    MvPolynomial.algHom_ext <| Fin.forall_fin_one.mpr (by simp [hproj])
  exact Function.LeftInverse.injective fun p ↦ congr($hleft p)

/-- Evaluating `R[Y₀]` at the residue class of `X₀` makes `R[X₀, X₁] ⧸ (X₁²)` module-finite. -/
theorem finite_aeval_mk_span_X_one_sq (R : Type*) [CommRing R] :
    (aeval (R := R) fun _ : Fin 1 ↦
      Ideal.Quotient.mk (Ideal.span {(X 1 : MvPolynomial (Fin 2) R) ^ 2}) (X 0)).Finite := by
  set I : Ideal (MvPolynomial (Fin 2) R) := Ideal.span {X 1 ^ 2}
  set x : Fin 2 → MvPolynomial (Fin 2) R ⧸ I := fun j ↦ Ideal.Quotient.mk I (X j)
  set y : Fin 1 → MvPolynomial (Fin 2) R ⧸ I := fun _ ↦ x 0
  refine (aeval (R := R) y).finite_of_adjoin_eq_top (Set.finite_range x)
    I.adjoin_range_quotient_mk_X_eq_top <| Set.forall_mem_range.mpr <|
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · simpa [y] using RingHom.isIntegralElem_map (aeval (R := R) y).toRingHom (x := X 0)
  · have hx1_sq : x 1 ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [hx1_sq]⟩

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
    have hker : ∀ p ∈ I, (aeval (R := k) (![0, DualNumber.eps] : Fin 2 → DualNumber k)) p = 0 :=
      fun p hp ↦ RingHom.mem_ker.mp <| Ideal.span_le.mpr
        (by rintro _ rfl; simp [DualNumber.eps_mul_eps, sq]) hp
    let toDual : (MvPolynomial (Fin 2) k ⧸ I) →ₐ[k] DualNumber k :=
      Ideal.Quotient.liftₐ I (aeval (R := k) ![0, DualNumber.eps]) hker
    have htoDual : toDual (x 1) = DualNumber.eps := by
      simpa [toDual, x] using congr($(Ideal.Quotient.liftₐ_comp I _ hker) (X 1))
    have heps : (DualNumber.eps : DualNumber k) = 0 := by
      rw [← htoDual, hred.eq_zero (x 1) ⟨2, hx1_sq⟩, map_zero]
    exact one_ne_zero (α := k) (by simpa using congrArg TrivSqZeroExt.snd heps)
  have hy0 : y = fun _ ↦ x 0 := funext <| Fin.forall_fin_one.mpr (by simp [y, Fin.sum_univ_two])
  have hind : AlgebraicIndependent k y := hy0 ▸ algebraicIndependent_mk_span_X_one_sq k
  have hfin : (aeval (R := k) y).Finite := hy0 ▸ finite_aeval_mk_span_X_one_sq k
  exact ⟨hnot_red, I.adjoin_range_quotient_mk_X_eq_top, hind, hfin, by
    simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial
      (aeval (R := k) y).toRingHom (algebraicIndependent_iff_injective_aeval.mp hind)
      hfin.to_isIntegral⟩

section ThreeLines

private noncomputable def threeLinesIdeal : Ideal (MvPolynomial (Fin 2) (ZMod 2)) :=
  Ideal.span {X 0 * X 1 * (X 0 + X 1)}

private noncomputable def threeLinesGen (j : Fin 2) :
    MvPolynomial (Fin 2) (ZMod 2) ⧸ threeLinesIdeal :=
  Ideal.Quotient.mk threeLinesIdeal (X j)

private noncomputable def threeLinesLineHom (u : Fin 2 → ZMod 2)
    (hu : u 0 * u 1 * (u 0 + u 1) = 0) :
    (MvPolynomial (Fin 2) (ZMod 2) ⧸ threeLinesIdeal) →ₐ[ZMod 2] Polynomial (ZMod 2) :=
  Ideal.Quotient.liftₐ threeLinesIdeal
    (aeval (R := ZMod 2) fun j ↦ Polynomial.C (u j) * Polynomial.X) fun p hp ↦
    RingHom.mem_ker.mp <| Ideal.span_le.mpr (by
      rintro _ rfl
      have hcalc : (Polynomial.C (u 0) * Polynomial.X) * (Polynomial.C (u 1) * Polynomial.X) *
          (Polynomial.C (u 0) * Polynomial.X + Polynomial.C (u 1) * Polynomial.X) =
          Polynomial.C (u 0 * u 1 * (u 0 + u 1)) * Polynomial.X ^ 3 := by
        simp only [map_add, map_mul]; ring
      simp [hcalc, hu]) hp

private lemma threeLinesLineHom_gen (u : Fin 2 → ZMod 2) (hu : u 0 * u 1 * (u 0 + u 1) = 0)
    (j : Fin 2) :
    threeLinesLineHom u hu (threeLinesGen j) = Polynomial.C (u j) * Polynomial.X := by
  rw [threeLinesLineHom, threeLinesGen, ← Ideal.Quotient.mkₐ_eq_mk (ZMod 2), ← AlgHom.comp_apply,
    Ideal.Quotient.liftₐ_comp, aeval_X]

-- Over `𝔽₂ = ZMod 2`, NO linear combination `c 0 • x 0 + c 1 • x 1` of the coordinate generators
-- makes `𝔽₂[X₀, X₁] ⧸ (X₀ X₁ (X₀ + X₁))` integral (hence nor module-finite) over `𝔽₂[Y]`.
example (c : Fin 2 → ZMod 2) :
    ¬ (aeval (R := ZMod 2) (![c 0 • threeLinesGen 0 + c 1 • threeLinesGen 1] :
      Fin 1 → _)).toRingHom.IsIntegral := by
  let y : Fin 1 → MvPolynomial (Fin 2) (ZMod 2) ⧸ threeLinesIdeal :=
    ![c 0 • threeLinesGen 0 + c 1 • threeLinesGen 1]
  -- Pick one of the three lines `X₀ = 0`, `X₁ = 0`, `X₀ + X₁ = 0` on which `c 0 X₀ + c 1 X₁ = 0`.
  obtain ⟨u, i₀, hu_rel, hu_orth, hui₀⟩ : ∃ (u : Fin 2 → ZMod 2) (i₀ : Fin 2),
      u 0 * u 1 * (u 0 + u 1) = 0 ∧ c 0 * u 0 + c 1 * u 1 = 0 ∧ u i₀ = 1 := by
    by_cases hc0 : c 0 = 0
    · exact ⟨![1, 0], 0, by simp, by simp [hc0], rfl⟩
    · by_cases hc1 : c 1 = 0
      · exact ⟨![0, 1], 1, by simp, by simp [hc1], rfl⟩
      · have hne : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
        exact ⟨![1, 1], 0, by decide, by rw [hne _ hc0, hne _ hc1]; decide, rfl⟩
  -- Restrict along the chosen line; `y 0` maps to `0`, while `threeLinesGen i₀` maps to `X`.
  let lineHom := threeLinesLineHom u hu_rel
  have hy0 : lineHom (y 0) = 0 := by
    simp only [y, lineHom, Matrix.cons_val_zero, map_add, map_smul,
      threeLinesLineHom_gen u hu_rel, Algebra.smul_def, Polynomial.algebraMap_eq]
    calc Polynomial.C (c 0) * (Polynomial.C (u 0) * Polynomial.X) +
          Polynomial.C (c 1) * (Polynomial.C (u 1) * Polynomial.X)
        = Polynomial.C (c 0 * u 0 + c 1 * u 1) * Polynomial.X := by
          simp only [map_add, map_mul]; ring
      _ = 0 := by rw [hu_orth, map_zero, zero_mul]
  -- Any monic integral equation for `threeLinesGen i₀` over `𝔽₂[y 0]` specializes to `P_0(X) = 0`.
  intro hint
  obtain ⟨P, hP_monic, hP_eval⟩ := hint (threeLinesGen i₀)
  have hcomp : lineHom.toRingHom.comp (aeval (R := ZMod 2) y).toRingHom =
      Polynomial.C.comp (MvPolynomial.eval 0) := by
    have halg : lineHom.comp (aeval (R := ZMod 2) y) =
        (Polynomial.CAlgHom (R := ZMod 2)).comp (MvPolynomial.aeval (R := ZMod 2) 0) :=
      MvPolynomial.algHom_ext <| Fin.forall_fin_one.mpr (by simp [hy0])
    refine RingHom.ext fun p ↦ ?_
    simpa [aeval_eq_eval] using congr($halg p)
  have hmap : P.map (MvPolynomial.eval (0 : Fin 1 → ZMod 2)) = 0 := by
    have h0 := congrArg lineHom.toRingHom hP_eval
    rw [Polynomial.hom_eval₂, hcomp, map_zero] at h0
    have hxi₀ : lineHom.toRingHom (threeLinesGen i₀) = Polynomial.X := by
      simp [lineHom, threeLinesLineHom_gen u hu_rel i₀, hui₀]
    rwa [hxi₀, ← Polynomial.eval₂_map, Polynomial.eval₂_C_X] at h0
  exact (hP_monic.map (MvPolynomial.eval (0 : Fin 1 → ZMod 2))).ne_zero hmap

-- Over `𝔽₂ = ZMod 2`, the nonlinear quadratic element `z = x₀² + x₀ x₁ + x₁²` DOES normalize
-- `𝔽₂[X₀, X₁] ⧸ (X₀ X₁ (X₀ + X₁))` (`d = 1`).
example :
    let y : Fin 1 → MvPolynomial (Fin 2) (ZMod 2) ⧸ threeLinesIdeal :=
      ![threeLinesGen 0 ^ 2 + threeLinesGen 0 * threeLinesGen 1 + threeLinesGen 1 ^ 2]
    Algebra.adjoin (ZMod 2) (Set.range threeLinesGen) = ⊤ ∧
      AlgebraicIndependent (ZMod 2) y ∧ (aeval (R := ZMod 2) y).Finite ∧
        ringKrullDim (MvPolynomial (Fin 2) (ZMod 2) ⧸ threeLinesIdeal) = (1 : ℕ) := by
  dsimp only
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y : Fin 1 → MvPolynomial (Fin 2) (ZMod 2) ⧸ threeLinesIdeal :=
    ![threeLinesGen 0 ^ 2 + threeLinesGen 0 * threeLinesGen 1 + threeLinesGen 1 ^ 2]
  have hadj : Algebra.adjoin (ZMod 2) (Set.range threeLinesGen) = ⊤ :=
    threeLinesIdeal.adjoin_range_quotient_mk_X_eq_top
  have haxis_ker : ∀ p ∈ threeLinesIdeal,
      (aeval (R := ZMod 2) (![X 0, 0] : Fin 2 → MvPolynomial (Fin 1) (ZMod 2))) p = 0 :=
    fun p hp ↦ RingHom.mem_ker.mp <| Ideal.span_le.mpr (by rintro _ rfl; simp) hp
  let axisHom : (MvPolynomial (Fin 2) (ZMod 2) ⧸ threeLinesIdeal) →ₐ[ZMod 2]
      MvPolynomial (Fin 1) (ZMod 2) :=
    Ideal.Quotient.liftₐ threeLinesIdeal (aeval (R := ZMod 2) ![X 0, 0]) haxis_ker
  have haxis (j : Fin 2) :
      axisHom (threeLinesGen j) = (![X 0, 0] : Fin 2 → MvPolynomial (Fin 1) (ZMod 2)) j := by
    simpa [axisHom, threeLinesGen] using
      congr($(Ideal.Quotient.liftₐ_comp threeLinesIdeal _ haxis_ker) (X j))
  have hind : AlgebraicIndependent (ZMod 2) y := by
    rw [algebraicIndependent_iff_injective_aeval]
    have hexp : axisHom.comp (aeval (R := ZMod 2) y) = MvPolynomial.expand 2 :=
      MvPolynomial.algHom_ext <|
        Fin.forall_fin_one.mpr (by simp [y, haxis, expand_X])
    refine Function.Injective.of_comp (f := axisHom) ?_
    rw [← AlgHom.coe_comp, hexp]
    exact MvPolynomial.expand_injective (by positivity)
  have hpoly : ∀ j : Fin 2, (X j : MvPolynomial (Fin 2) (ZMod 2)) ^ 3 -
      (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2) * X j = -(X 0 * X 1 * (X 0 + X 1)) :=
    Fin.forall_fin_two.mpr ⟨by ring, by ring⟩
  have hcubic (j : Fin 2) : threeLinesGen j ^ 3 - y 0 * threeLinesGen j = 0 := by
    have hmk : Ideal.Quotient.mk threeLinesIdeal
        ((X j : MvPolynomial (Fin 2) (ZMod 2)) ^ 3 -
          (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2) * X j) = 0 := by
      rw [hpoly j, map_neg, neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    simpa [y, threeLinesGen, map_sub, map_add, map_mul, map_pow] using hmk
  have hfin : (aeval (R := ZMod 2) y).Finite := by
    refine (aeval (R := ZMod 2) y).finite_of_adjoin_eq_top (Set.finite_range threeLinesGen) hadj <|
      Set.forall_mem_range.mpr fun j ↦ ?_
    refine ⟨Polynomial.X ^ 3 - Polynomial.C (X 0) * Polynomial.X,
      Polynomial.monic_X_pow_sub ((Polynomial.degree_C_mul_X_le _).trans_lt (by norm_num)), ?_⟩
    simpa using hcubic j
  exact ⟨hadj, hind, hfin, by
    simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial (k := ZMod 2)
      (aeval (R := ZMod 2) y).toRingHom
      (algebraicIndependent_iff_injective_aeval.mp hind) hfin.to_isIntegral⟩

end ThreeLines

end TauCeti.NoetherNormalizationExamples
