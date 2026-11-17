/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.LinearAlgebra.Matrix.BlockSucc
public import TauCeti.RingTheory.MvPolynomial.Harmonic.Fischer
public import TauCeti.RingTheory.MvPolynomial.Harmonic.Orthogonal
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.BlockSucc
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Orbit

/-!
# Irreducibility of harmonic polynomials under the special orthogonal group

In dimension `N ≥ 3`, the representation of the real special orthogonal group `SO(N)` on the space
`H_d` of degree-`d` harmonic homogeneous polynomials over `ℝ` or `ℂ` (more generally, any `𝕜` with
`[RCLike 𝕜]`) is irreducible. The proof uses only zonal harmonics and orthogonality with respect to
the Fischer inner product, without highest-weight theory:

1. **Invariant homogeneous polynomials.** For `n ≥ 2`, `SO(n)` acts transitively on every sphere in
   `ℝⁿ` (`TauCeti.exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_eq`). Consequently, an
   `SO(n)`-invariant homogeneous polynomial of odd degree vanishes
   (`MvPolynomial.eq_zero_of_isHomogeneous_odd_of_specialOrthogonalGroup_invariant`), and one of
   even degree `2k` is a scalar multiple of `(r²)^k`
   (`exists_eq_C_mul_normSq_pow_of_isHomogeneous_even_of_specialOrthogonalGroup_invariant`).
2. **Uniqueness of zonal harmonics.** For `n ≥ 2`, expanding a polynomial in `Fin (n + 1)` variables
   in powers of the last variable `Xₙ` expresses `Δ p = 0` as the recurrence
   `Δ' qᵣ + (r + 1)(r + 2) qᵣ₊₂ = 0`. If `p ∈ H_d` is invariant under the upper-left block subgroup
   `SO(n) ↪ SO(n + 1)` (`Matrix.blockSucc`) and vanishes at the north pole `eₙ`, downward induction
   together with `MvPolynomial.eq_zero_of_laplacian_normSq_mul_eq_zero` forces every `qᵣ` to vanish
   (`eq_zero_of_mem_harmonicSubmodule_of_blockSucc_invariant_of_eval_last_eq_zero`). Hence the
   `SO(n)`-invariant subspace of `H_d` has dimension at most one.
3. **Irreducibility.** Equipping `H_d` with the `SO(N)`-invariant Fischer inner product
   (`MvPolynomial.fischerInnerCore`), the Riesz representer of evaluation at `eₙ` is an
   `SO(N - 1)`-invariant harmonic polynomial. For any `SO(N)`-invariant decomposition
   `H_d = W ⊕ Wᗮ`, both orthogonal components of this representer are `SO(N - 1)`-invariant; if
   both `W` and `Wᗮ` were nonzero, transitivity of `SO(N)` on the sphere would make both components
   nonzero, contradicting uniqueness of zonal harmonics.

The dimension hypothesis `3 ≤ Fintype.card σ` is sharp: for `N = 2` and `d ≥ 1`, `H_d` over `ℂ`
splits into the two one-dimensional eigenspaces spanned by `(X₀ ± i X₁)^d`.

## Main definitions

* `MvPolynomial.harmonicSpecialOrthogonalRep`: the representation of
  `Matrix.specialOrthogonalGroup σ R` on `harmonicSubmodule σ 𝕜 d` for any `R`-algebra `𝕜`.

## Main results

* `MvPolynomial.fischerInner_harmonicSpecialOrthogonalRep`: the `SO(σ, ℝ)`-action preserves the
  Fischer inner product over any `[RCLike 𝕜]`.
* `MvPolynomial.eq_zero_of_isHomogeneous_odd_of_specialOrthogonalGroup_invariant`: in at least two
  variables, every `SO(σ, ℝ)`-invariant homogeneous polynomial of odd degree is zero.
* `exists_eq_C_mul_normSq_pow_of_isHomogeneous_even_of_specialOrthogonalGroup_invariant`: in at
  least two variables, every `SO(σ, ℝ)`-invariant homogeneous polynomial of even degree `2k` is a
  constant multiple of `(normSq σ 𝕜)^k`.
* `MvPolynomial.eq_zero_of_mem_harmonicSubmodule_of_blockSucc_invariant_of_eval_last_eq_zero` and
  `MvPolynomial.eval_last_smul_eq_of_mem_harmonicSubmodule_of_blockSucc_invariant`: uniqueness of
  zonal harmonics on `Fin (n + 1)` for `2 ≤ n`.
* `MvPolynomial.eq_bot_or_eq_harmonicSubmodule_of_specialOrthogonalGroup_invariant`: every
  `SO(σ, ℝ)`-invariant submodule of `harmonicSubmodule σ 𝕜 d` (`3 ≤ Fintype.card σ`, `[RCLike 𝕜]`)
  is either `⊥` or `harmonicSubmodule σ 𝕜 d`.
* `MvPolynomial.isIrreducible_harmonicSpecialOrthogonalRep` and
  `MvPolynomial.isIrreducible_harmonicRep`: irreducibility (`Representation.IsIrreducible`) of the
  `SO(σ, ℝ)`- and `O(σ, 𝕜)`-representations on `harmonicSubmodule σ 𝕜 d` for `3 ≤ Fintype.card σ`
  and `[RCLike 𝕜]`.

## References

* M. E. Taylor, *Introduction to Lie Groups*, University of North Carolina lecture notes (2021),
  Chapter 8, Propositions 8.4.2 and 8.5.1.
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press (1971), Chapter IV, Section 2.
-/

public section

open Matrix
open scoped InnerProductSpace

namespace MvPolynomial

section Representation

variable (σ R 𝕜 : Type*) [Fintype σ] [DecidableEq σ] [CommRing R] [CommRing 𝕜] [Algebra R 𝕜]

/-- The special orthogonal group `SO(σ, R)` acts on the harmonic homogeneous polynomials of degree
`d` over any `R`-algebra `𝕜` by `(g • p)(x) = p (g⁻¹ x)`
(`MvPolynomial.eval_harmonicSpecialOrthogonalRep_apply`). Since `g⁻¹ = gᵀ`, the element `g` acts by
the substitution `linearSubst ((g : Matrix σ σ R)ᵀ.map (algebraMap R 𝕜))`. -/
noncomputable def harmonicSpecialOrthogonalRep (d : ℕ) :
    Representation 𝕜 (Matrix.specialOrthogonalGroup σ R) (harmonicSubmodule σ 𝕜 d) :=
  (harmonicRep σ 𝕜 d).comp <|
    (Submonoid.inclusion (show specialOrthogonalGroup σ 𝕜 ≤ orthogonalGroup σ 𝕜 from
      fun _ h ↦ h.1)).comp (SpecialOrthogonalGroup.map (algebraMap R 𝕜))

variable {σ R 𝕜}

@[simp]
theorem coe_harmonicSpecialOrthogonalRep_apply {d : ℕ} (g : Matrix.specialOrthogonalGroup σ R)
    (p : harmonicSubmodule σ 𝕜 d) :
    (harmonicSpecialOrthogonalRep σ R 𝕜 d g p : MvPolynomial σ 𝕜) =
      linearSubst ((g : Matrix σ σ R)ᵀ.map (algebraMap R 𝕜)) p := by
  simp [harmonicSpecialOrthogonalRep, coe_harmonicRep_apply, transpose_map]

/-- The special orthogonal group acts on harmonic polynomials by `(g • p)(x) = p (g⁻¹ x)`. -/
theorem eval_harmonicSpecialOrthogonalRep_apply {d : ℕ} (g : Matrix.specialOrthogonalGroup σ R)
    (p : harmonicSubmodule σ 𝕜 d) (x : σ → 𝕜) :
    eval x (harmonicSpecialOrthogonalRep σ R 𝕜 d g p : MvPolynomial σ 𝕜) =
      eval (((g⁻¹ : Matrix.specialOrthogonalGroup σ R) : Matrix σ σ R).map (algebraMap R 𝕜) *ᵥ x)
        (p : MvPolynomial σ 𝕜) := by
  rw [coe_harmonicSpecialOrthogonalRep_apply, eval_linearSubst]
  rfl

/-- The action of `SO(σ, ℝ)` on harmonic polynomials over `ℝ` or `ℂ` is unitary for the Fischer
inner product. -/
theorem fischerInner_harmonicSpecialOrthogonalRep {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ]
    [RCLike 𝕜] {d : ℕ} (g : Matrix.specialOrthogonalGroup σ ℝ)
    (p q : harmonicSubmodule σ 𝕜 d) :
    fischerInner (harmonicSpecialOrthogonalRep σ ℝ 𝕜 d g p : MvPolynomial σ 𝕜)
        (harmonicSpecialOrthogonalRep σ ℝ 𝕜 d g q : MvPolynomial σ 𝕜) =
      fischerInner (p : MvPolynomial σ 𝕜) (q : MvPolynomial σ 𝕜) := by
  rw [coe_harmonicSpecialOrthogonalRep_apply, coe_harmonicSpecialOrthogonalRep_apply]
  refine fischerInner_linearSubst_of_mul_conjTranspose_eq_one ?_
    (p : MvPolynomial σ 𝕜) (q : MvPolynomial σ 𝕜)
  have hH :
      ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜))ᴴ = (g : Matrix σ σ ℝ).map (algebraMap ℝ 𝕜) := by
    ext i j
    simp [Matrix.conjTranspose_apply, RCLike.star_def]
  rw [hH, ← Matrix.map_mul, (mem_orthogonalGroup_iff' σ ℝ).mp g.2.1,
    Matrix.map_one _ (map_zero _) (map_one _)]

end Representation

section InvariantHomogeneous

/-- Two polynomials over an `ℝ`-algebra field that agree on all real points are equal. -/
private theorem eq_of_eval_algebraMap_eq {σ 𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜]
    {p q : MvPolynomial σ 𝕜}
    (h : ∀ x : σ → ℝ, eval (algebraMap ℝ 𝕜 ∘ x) p = eval (algebraMap ℝ 𝕜 ∘ x) q) : p = q := by
  have hinf : (Set.range (algebraMap ℝ 𝕜)).Infinite :=
    Set.infinite_range_of_injective (algebraMap ℝ 𝕜).injective
  refine funext_set (s := fun _ ↦ Set.range (algebraMap ℝ 𝕜)) (fun _ ↦ hinf) fun y hy ↦ ?_
  have hmem : ∀ i, ∃ r : ℝ, algebraMap ℝ 𝕜 r = y i := fun i ↦ hy i (Set.mem_univ i)
  choose x hx using hmem
  have hxy : y = algebraMap ℝ 𝕜 ∘ x := by
    ext i
    exact (hx i).symm
  rw [hxy]
  exact h x

/-- A homogeneous polynomial of positive degree vanishes at `0`. -/
private theorem eval_zero_of_isHomogeneous_of_ne_zero {σ R : Type*} [CommSemiring R]
    {q : MvPolynomial σ R} {m : ℕ} (hq : q.IsHomogeneous m) (hm : m ≠ 0) :
    eval (0 : σ → R) q = 0 := by
  have h := hq.eval_smul (0 : R) (0 : σ → R)
  simpa [zero_pow hm] using h

variable {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ] [Field 𝕜] [Algebra ℝ 𝕜]

/-- Every nonzero real vector `x` in dimension at least two is a positive multiple of `gᵀ *ᵥ u`
for a prescribed unit vector `u` and some `g ∈ SO(σ, ℝ)`. -/
private theorem exists_specialOrthogonalGroup_transpose_mulVec_eq_normalize
    (hσ : 2 ≤ Fintype.card σ) {u x : σ → ℝ} (hu : u ⬝ᵥ u = 1) (hx : x ≠ 0) :
    ∃ g : Matrix.specialOrthogonalGroup σ ℝ,
      x = Real.sqrt (x ⬝ᵥ x) • ((g : Matrix σ σ ℝ)ᵀ *ᵥ u) := by
  have hxx : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hx))
  have hr : 0 < Real.sqrt (x ⬝ᵥ x) := Real.sqrt_pos.mpr hxx
  set y : σ → ℝ := (Real.sqrt (x ⬝ᵥ x))⁻¹ • x
  have hyy : y ⬝ᵥ y = 1 := by
    simp only [y, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [← mul_assoc, ← mul_inv, ← sq, Real.sq_sqrt hxx.le, inv_mul_cancel₀ hxx.ne']
  obtain ⟨g, hg⟩ :=
    TauCeti.exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_eq hσ (hyy.trans hu.symm)
  refine ⟨g, ?_⟩
  have hgu : (g : Matrix σ σ ℝ)ᵀ *ᵥ u = y := by
    rw [← hg, mulVec_mulVec, (mem_orthogonalGroup_iff' σ ℝ).mp g.2.1, one_mulVec]
  rw [hgu, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- An `SO(σ, ℝ)`-invariant homogeneous polynomial of degree `m` on `ℝˢ` (`|σ| ≥ 2`) satisfies
`q(x) = ‖x‖ᵐ q(u)` for every nonzero `x` and every unit vector `u`. -/
private theorem eval_eq_sqrt_dotProduct_pow_mul_of_specialOrthogonalGroup_invariant
    (hσ : 2 ≤ Fintype.card σ) {q : MvPolynomial σ 𝕜} {m : ℕ} (hq : q.IsHomogeneous m)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ,
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q = q)
    {u x : σ → ℝ} (hu : u ⬝ᵥ u = 1) (hx : x ≠ 0) :
    eval (algebraMap ℝ 𝕜 ∘ x) q =
      algebraMap ℝ 𝕜 (Real.sqrt (x ⬝ᵥ x)) ^ m * eval (algebraMap ℝ 𝕜 ∘ u) q := by
  obtain ⟨g, hgx⟩ := exists_specialOrthogonalGroup_transpose_mulVec_eq_normalize hσ hu hx
  have hscaled :
      algebraMap ℝ 𝕜 ∘ x =
        algebraMap ℝ 𝕜 (Real.sqrt (x ⬝ᵥ x)) •
          (((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) *ᵥ (algebraMap ℝ 𝕜 ∘ u)) := by
    ext i
    have hi := congrFun hgx i
    simp [hi, mulVec, dotProduct, map_sum, map_mul]
  rw [hscaled, hq.eval_smul, ← eval_linearSubst, hinv g]

/-- In at least two variables, every `SO(σ, ℝ)`-invariant homogeneous polynomial of odd degree is
zero. -/
theorem eq_zero_of_isHomogeneous_odd_of_specialOrthogonalGroup_invariant
    (hσ : 2 ≤ Fintype.card σ) {q : MvPolynomial σ 𝕜} {m : ℕ} (hq : q.IsHomogeneous m)
    (hm : Odd m)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ,
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q = q) :
    q = 0 := by
  have : CharZero 𝕜 := charZero_of_injective_algebraMap (algebraMap ℝ 𝕜).injective
  obtain ⟨i₀⟩ : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  let u : σ → ℝ := Pi.single i₀ 1
  have hu : u ⬝ᵥ u = 1 := by simp [u]
  have hnu : -u ≠ 0 := by
    intro h
    have h0 := congrFun h i₀
    simp [u] at h0
  have h1 := eval_eq_sqrt_dotProduct_pow_mul_of_specialOrthogonalGroup_invariant hσ hq hinv hu hnu
  have hneg : algebraMap ℝ 𝕜 ∘ (-u) = (-1 : 𝕜) • (algebraMap ℝ 𝕜 ∘ u) := by
    ext i
    simp
  rw [hneg, hq.eval_smul, hm.neg_one_pow] at h1
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, hu, Real.sqrt_one, map_one, one_pow,
    one_mul, neg_one_mul] at h1
  have hcu : eval (algebraMap ℝ 𝕜 ∘ u) q = 0 := by
    have h2 : (2 : 𝕜) * eval (algebraMap ℝ 𝕜 ∘ u) q = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h1.symm
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  refine eq_of_eval_algebraMap_eq fun x ↦ ?_
  rw [map_zero]
  by_cases hx : x = 0
  · subst hx
    have h0 : algebraMap ℝ 𝕜 ∘ (0 : σ → ℝ) = 0 := by ext i; simp
    rw [h0]
    exact eval_zero_of_isHomogeneous_of_ne_zero hq hm.pos.ne'
  · rw [eval_eq_sqrt_dotProduct_pow_mul_of_specialOrthogonalGroup_invariant hσ hq hinv hu hx, hcu,
      mul_zero]

/-- In at least two variables, every `SO(σ, ℝ)`-invariant homogeneous polynomial of even degree
`2k` is a constant multiple of `(normSq σ 𝕜)^k`. -/
theorem exists_eq_C_mul_normSq_pow_of_isHomogeneous_even_of_specialOrthogonalGroup_invariant
    (hσ : 2 ≤ Fintype.card σ) {q : MvPolynomial σ 𝕜} {k : ℕ} (hq : q.IsHomogeneous (2 * k))
    (hinv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ,
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q = q) :
    ∃ c : 𝕜, q = C c * normSq σ 𝕜 ^ k := by
  obtain ⟨i₀⟩ : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  let u : σ → ℝ := Pi.single i₀ 1
  have hu : u ⬝ᵥ u = 1 := by simp [u]
  refine ⟨eval (algebraMap ℝ 𝕜 ∘ u) q, eq_of_eval_algebraMap_eq fun x ↦ ?_⟩
  by_cases hx : x = 0
  · subst hx
    have h0 : algebraMap ℝ 𝕜 ∘ (0 : σ → ℝ) = 0 := by ext i; simp
    rw [h0]
    rcases eq_or_ne k 0 with rfl | hk
    · have hC : q = C (q.coeff 0) :=
        totalDegree_eq_zero_iff_eq_C.mp
          ((totalDegree_zero_iff_isHomogeneous _).mpr (by simpa using hq))
      conv_lhs => rw [hC]
      conv_rhs => rw [hC]
      simp
    · rw [eval_zero_of_isHomogeneous_of_ne_zero hq (by omega), map_mul, map_pow, eval_normSq]
      simp [zero_pow hk]
  · rw [eval_eq_sqrt_dotProduct_pow_mul_of_specialOrthogonalGroup_invariant hσ hq hinv hu hx]
    have hns : eval (algebraMap ℝ 𝕜 ∘ x) (normSq σ 𝕜) = algebraMap ℝ 𝕜 (x ⬝ᵥ x) := by
      simp [normSq_def, dotProduct, sq, map_sum, map_mul]
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i)
    rw [map_mul, eval_C, map_pow, hns, pow_mul, ← map_pow, Real.sq_sqrt hxx, mul_comm]

end InvariantHomogeneous

section ZonalHarmonics

/-- Separating out the last variable `Xₙ` of `MvPolynomial (Fin (n + 1)) R`. -/
private noncomputable def finLastEquiv (R : Type*) [CommSemiring R] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R finSuccEquivLast).trans (optionEquivLeft R (Fin n))

private theorem finLastEquiv_C {R : Type*} [CommSemiring R] (n : ℕ) (a : R) :
    finLastEquiv R n (C a) = Polynomial.C (C a) := by
  simp [finLastEquiv]

private theorem finLastEquiv_X_castSucc {R : Type*} [CommSemiring R] (n : ℕ) (i : Fin n) :
    finLastEquiv R n (X i.castSucc) = Polynomial.C (X i) := by
  simp [finLastEquiv]

private theorem finLastEquiv_X_last {R : Type*} [CommSemiring R] (n : ℕ) :
    finLastEquiv R n (X (Fin.last n)) = Polynomial.X := by
  simp [finLastEquiv]

private theorem finLastEquiv_linearSubst_blockSucc {R : Type*} [CommSemiring R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (p : MvPolynomial (Fin (n + 1)) R) :
    finLastEquiv R n (linearSubst (Matrix.blockSucc M) p) =
      (finLastEquiv R n p).map (linearSubst M).toRingHom := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [finLastEquiv_C]
  | add p q hp hq =>
    simp [map_add, Polynomial.map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, map_mul, Polynomial.map_mul, hp]
    congr 1
    induction j using Fin.lastCases with
    | last =>
      have hX : linearSubst (Matrix.blockSucc M) (X (Fin.last n)) = X (Fin.last n) := by
        rw [linearSubst_X, Fin.sum_univ_castSucc]
        simp
      rw [hX, finLastEquiv_X_last, Polynomial.map_X]
    | cast i =>
      have hX : linearSubst (Matrix.blockSucc M) (X i.castSucc) =
          ∑ j : Fin n, C (M i j) * X j.castSucc := by
        rw [linearSubst_X, Fin.sum_univ_castSucc]
        simp
      have hcoe (q : MvPolynomial (Fin n) R) : (linearSubst M).toRingHom q = linearSubst M q := rfl
      rw [hX, map_sum, finLastEquiv_X_castSucc, Polynomial.map_C, hcoe, linearSubst_X, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [finLastEquiv_C, finLastEquiv_X_castSucc]

private theorem coeff_finLastEquiv_linearSubst_blockSucc {R : Type*} [CommSemiring R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (p : MvPolynomial (Fin (n + 1)) R) (r : ℕ) :
    (finLastEquiv R n (linearSubst (Matrix.blockSucc M) p)).coeff r =
      linearSubst M ((finLastEquiv R n p).coeff r) := by
  rw [finLastEquiv_linearSubst_blockSucc, Polynomial.coeff_map]
  rfl

private theorem coeff_finLastEquiv_pderiv_castSucc {R : Type*} [CommSemiring R] {n : ℕ}
    (i : Fin n) (p : MvPolynomial (Fin (n + 1)) R) (r : ℕ) :
    (finLastEquiv R n (pderiv i.castSucc p)).coeff r =
      pderiv i ((finLastEquiv R n p).coeff r) := by
  induction p using MvPolynomial.induction_on generalizing r with
  | C a =>
    rw [pderiv_C, map_zero, Polynomial.coeff_zero, finLastEquiv_C, Polynomial.coeff_C]
    split_ifs <;> simp
  | add p q hp hq =>
    simp [map_add, hp, hq]
  | mul_X p j hp =>
    induction j using Fin.lastCases with
    | last =>
      have hne : i.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last i).ne
      rw [pderiv_mul, pderiv_X_of_ne hne.symm, mul_zero, add_zero, map_mul, map_mul,
        finLastEquiv_X_last]
      cases r with
      | zero => simp
      | succ k => simp [hp k]
    | cast k =>
      rw [pderiv_mul, map_add, map_mul, map_mul, map_mul, finLastEquiv_X_castSucc,
        Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C, hp r, pderiv_mul]
      by_cases hik : i = k
      · subst hik
        simp
      · have hne : i.castSucc ≠ k.castSucc := fun h ↦ hik (Fin.castSucc_inj.mp h)
        simp [pderiv_X_of_ne (Ne.symm hne), pderiv_X_of_ne (Ne.symm hik)]

private theorem finLastEquiv_pderiv_last {R : Type*} [CommSemiring R] {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) R) :
    finLastEquiv R n (pderiv (Fin.last n) p) = (finLastEquiv R n p).derivative := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [finLastEquiv_C]
  | add p q hp hq =>
    simp [map_add, hp, hq]
  | mul_X p j hp =>
    induction j using Fin.lastCases with
    | last =>
      rw [pderiv_mul, pderiv_X_self, mul_one, map_add, map_mul, map_mul, finLastEquiv_X_last, hp,
        Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
    | cast k =>
      have hne : Fin.last n ≠ k.castSucc := (Fin.castSucc_lt_last k).ne'
      rw [pderiv_mul, pderiv_X_of_ne hne.symm, mul_zero, add_zero, map_mul, map_mul,
        finLastEquiv_X_castSucc, hp, Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero,
        add_zero]

private theorem coeff_finLastEquiv_laplacian {R : Type*} [CommSemiring R] {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) R) (r : ℕ) :
    (finLastEquiv R n (laplacian p)).coeff r =
      laplacian ((finLastEquiv R n p).coeff r) +
        ((r + 1) * (r + 2)) • (finLastEquiv R n p).coeff (r + 2) := by
  rw [laplacian_apply, Fin.sum_univ_castSucc, map_add, Polynomial.coeff_add, map_sum,
    Polynomial.finsetSum_coeff, laplacian_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeff_finLastEquiv_pderiv_castSucc, coeff_finLastEquiv_pderiv_castSucc]
  · rw [finLastEquiv_pderiv_last, finLastEquiv_pderiv_last, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative, nsmul_eq_mul]
    push_cast
    ring

private theorem finLastEquiv_monomial {R : Type*} [CommSemiring R] {n : ℕ}
    (m : Fin (n + 1) →₀ ℕ) (a : R) :
    finLastEquiv R n (monomial m a) =
      Polynomial.monomial (m (Fin.last n)) (monomial (m.mapDomain finSuccEquivLast).some a) := by
  rw [finLastEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_monomial,
    optionEquivLeft_monomial]
  have hnone : (m.mapDomain finSuccEquivLast) none = m (Fin.last n) := by
    rw [← finSuccEquivLast_last, Finsupp.mapDomain_apply_of_injective finSuccEquivLast.injective]
  rw [hnone]

private theorem coeff_finLastEquiv_eq_zero_of_lt {R : Type*} [CommSemiring R] {n d r : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} (hp : p.IsHomogeneous d) (hr : d < r) :
    (finLastEquiv R n p).coeff r = 0 := by
  rw [p.as_sum, map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [finLastEquiv_monomial, Polynomial.coeff_monomial]
  have hdeg : ∑ i : Fin (n + 1), m i = d := by
    have h := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype] using h
  have hle : m (Fin.last n) ≤ d := by
    rw [← hdeg, Fin.sum_univ_castSucc]
    exact Nat.le_add_left _ _
  exact Finsupp.single_eq_of_ne (by omega)

private theorem isHomogeneous_coeff_finLastEquiv {R : Type*} [CommSemiring R] {n d r : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} (hp : p.IsHomogeneous d) (hr : r ≤ d) :
    ((finLastEquiv R n p).coeff r).IsHomogeneous (d - r) := by
  rw [p.as_sum, map_sum, Polynomial.finsetSum_coeff]
  refine IsHomogeneous.sum _ _ _ fun m hm ↦ ?_
  rw [finLastEquiv_monomial, Polynomial.coeff_monomial, Finsupp.single_apply]
  split_ifs with hmr
  · refine isHomogeneous_monomial _ ?_
    have hdeg : ∑ i : Fin (n + 1), m i = d := by
      have h := hp (mem_support_iff.mp hm)
      simpa [Finsupp.weight_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype] using h
    rw [Fin.sum_univ_castSucc, hmr] at hdeg
    have hsome (i : Fin n) : (m.mapDomain finSuccEquivLast).some i = m i.castSucc := by
      -- `Finsupp.some` evaluates the underlying `Option (Fin n) →₀ ℕ` at `some i`.
      change (m.mapDomain finSuccEquivLast) (some i) = m i.castSucc
      rw [← finSuccEquivLast_castSucc i,
        Finsupp.mapDomain_apply_of_injective finSuccEquivLast.injective]
    rw [Finsupp.degree_apply,
      Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ Finsupp.notMem_support_iff.mp hi]
    simp_rw [hsome]
    omega
  · exact isHomogeneous_zero _ _ _

private theorem eval_single_last_eq_eval_one {R : Type*} [CommSemiring R] {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) R) :
    eval (Pi.single (Fin.last n) 1) p =
      Polynomial.eval 1 ((finLastEquiv R n p).map (eval 0)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [finLastEquiv_C]
  | add p q hp hq =>
    simp [map_add, Polynomial.map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, Polynomial.map_mul, Polynomial.eval_mul, hp]
    congr 1
    induction j using Fin.lastCases with
    | last =>
      simp [finLastEquiv_X_last]
    | cast i =>
      simp [finLastEquiv_X_castSucc, (Fin.castSucc_lt_last i).ne]

private theorem coeff_finLastEquiv_top {𝕜 : Type*} [Field 𝕜] {n d : ℕ}
    {p : MvPolynomial (Fin (n + 1)) 𝕜} (hp : p.IsHomogeneous d) :
    (finLastEquiv 𝕜 n p).coeff d = C (eval (Pi.single (Fin.last n) 1) p) := by
  have htop0 : ((finLastEquiv 𝕜 n p).coeff d).IsHomogeneous 0 := by
    simpa using isHomogeneous_coeff_finLastEquiv hp le_rfl
  have hC : (finLastEquiv 𝕜 n p).coeff d = C (((finLastEquiv 𝕜 n p).coeff d).coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr htop0)
  have heval : eval (Pi.single (Fin.last n) 1) p = eval 0 ((finLastEquiv 𝕜 n p).coeff d) := by
    rw [eval_single_last_eq_eval_one]
    have hdeg : ((finLastEquiv 𝕜 n p).map (eval 0)).natDegree < d + 1 := by
      refine lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun r hr ↦ ?_)
        (Nat.lt_succ_self d)
      rw [Polynomial.coeff_map, coeff_finLastEquiv_eq_zero_of_lt hp hr, map_zero]
    rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_eq_single d]
    · simp
    · intro r hr hne
      have hlt : r < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) hne
      have hr0 : eval (0 : Fin n → 𝕜) ((finLastEquiv 𝕜 n p).coeff r) = 0 :=
        eval_zero_of_isHomogeneous_of_ne_zero (isHomogeneous_coeff_finLastEquiv hp hlt.le)
          (by omega)
      rw [Polynomial.coeff_map, hr0, zero_mul]
    · simp
  rw [heval]
  conv_lhs => rw [hC]
  conv_rhs => rw [hC]
  simp

/-- **Uniqueness of zonal harmonics**: for `n ≥ 2`, a harmonic homogeneous polynomial in `n + 1`
variables that is invariant under the upper-left block subgroup `SO(n, ℝ)` and vanishes at the last
coordinate basis vector is identically zero. -/
theorem eq_zero_of_mem_harmonicSubmodule_of_blockSucc_invariant_of_eval_last_eq_zero
    {n d : ℕ} {𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜] (hn : 2 ≤ n)
    {p : MvPolynomial (Fin (n + 1)) 𝕜} (hp : p ∈ harmonicSubmodule (Fin (n + 1)) 𝕜 d)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup (Fin n) ℝ,
      linearSubst ((Matrix.blockSucc (g : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)) p = p)
    (heval : eval (Pi.single (Fin.last n) 1) p = 0) :
    p = 0 := by
  have : CharZero 𝕜 := charZero_of_injective_algebraMap (algebraMap ℝ 𝕜).injective
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hp_hom, hp_lap⟩ := mem_harmonicSubmodule_iff.mp hp
  let q : ℕ → MvPolynomial (Fin n) 𝕜 := fun r ↦ (finLastEquiv 𝕜 n p).coeff r
  have hq_inv : ∀ r, ∀ g : Matrix.specialOrthogonalGroup (Fin n) ℝ,
      linearSubst ((g : Matrix (Fin n) (Fin n) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) (q r) = q r := by
    intro r g
    have h := congrArg (fun f ↦ (finLastEquiv 𝕜 n f).coeff r) (hinv g)
    rwa [Matrix.transpose_blockSucc, Matrix.map_blockSucc,
      coeff_finLastEquiv_linearSubst_blockSucc] at h
  have hq_rec : ∀ r, laplacian (q r) + ((r + 1) * (r + 2)) • q (r + 2) = 0 := by
    intro r
    have h := congrArg (fun f ↦ (finLastEquiv 𝕜 n f).coeff r) hp_lap
    rwa [coeff_finLastEquiv_laplacian, map_zero, Polynomial.coeff_zero] at h
  -- Downward induction on `m = d - r` forces every coefficient `q r` to vanish.
  have hq_down : ∀ m, m ≤ d → q (d - m) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hmd
      rcases lt_or_ge m 2 with hm2 | hm2
      · interval_cases m
        · simp [q, coeff_finLastEquiv_top hp_hom, heval]
        · have hhom : (q (d - 1)).IsHomogeneous 1 := by
            simpa [Nat.sub_sub_self hmd] using
              isHomogeneous_coeff_finLastEquiv hp_hom (Nat.sub_le d 1)
          exact eq_zero_of_isHomogeneous_odd_of_specialOrthogonalGroup_invariant
            (by simpa using hn) hhom odd_one (hq_inv (d - 1))
      · set r := d - m
        have hr2 : r + 2 = d - (m - 2) := by omega
        have hq2 : q (r + 2) = 0 := hr2 ▸ ih (m - 2) (by omega) (by omega)
        have hΔ : laplacian (q r) = 0 := by simpa [hq2] using hq_rec r
        have hhom : (q r).IsHomogeneous m := by
          simpa [r, Nat.sub_sub_self hmd] using
            isHomogeneous_coeff_finLastEquiv hp_hom (Nat.sub_le d m)
        rcases Nat.even_or_odd m with ⟨k, hk⟩ | hodd
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hhom' : (q r).IsHomogeneous (2 * (k' + 1)) := by
            simpa [two_mul] using hk ▸ hhom
          obtain ⟨c, hc⟩ :=
            exists_eq_C_mul_normSq_pow_of_isHomogeneous_even_of_specialOrthogonalGroup_invariant
              (by simpa using hn) hhom' (hq_inv r)
          have hfac : q r = normSq (Fin n) 𝕜 * (C c * normSq (Fin n) 𝕜 ^ k') := by
            rw [hc, pow_succ']
            ring
          rw [hfac] at hΔ ⊢
          rw [eq_zero_of_laplacian_normSq_mul_eq_zero hΔ, mul_zero]
        · exact eq_zero_of_isHomogeneous_odd_of_specialOrthogonalGroup_invariant
            (by simpa using hn) hhom hodd (hq_inv r)
  apply (finLastEquiv 𝕜 n).injective
  refine AddMonoidAlgebra.ext (Finsupp.ext fun r ↦ ?_)
  rw [map_zero, Polynomial.coeff_zero]
  by_cases hrd : r ≤ d
  · simpa [q, Nat.sub_sub_self hrd] using hq_down (d - r) (Nat.sub_le d r)
  · exact coeff_finLastEquiv_eq_zero_of_lt hp_hom (by omega)

/-- Any two `SO(n, ℝ)`-invariant harmonic homogeneous polynomials of the same degree in `n + 1`
variables (`n ≥ 2`) are proportional via their values at the last coordinate basis vector. -/
theorem eval_last_smul_eq_of_mem_harmonicSubmodule_of_blockSucc_invariant
    {n d : ℕ} {𝕜 : Type*} [Field 𝕜] [Algebra ℝ 𝕜] (hn : 2 ≤ n)
    {p q : MvPolynomial (Fin (n + 1)) 𝕜}
    (hp : p ∈ harmonicSubmodule (Fin (n + 1)) 𝕜 d)
    (hq : q ∈ harmonicSubmodule (Fin (n + 1)) 𝕜 d)
    (hpinv : ∀ g : Matrix.specialOrthogonalGroup (Fin n) ℝ,
      linearSubst ((Matrix.blockSucc (g : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)) p = p)
    (hqinv : ∀ g : Matrix.specialOrthogonalGroup (Fin n) ℝ,
      linearSubst ((Matrix.blockSucc (g : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)) q = q) :
    eval (Pi.single (Fin.last n) 1) q • p = eval (Pi.single (Fin.last n) 1) p • q := by
  refine sub_eq_zero.mp <|
    eq_zero_of_mem_harmonicSubmodule_of_blockSucc_invariant_of_eval_last_eq_zero hn
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ hq))
      (fun g ↦ by simp only [map_sub, map_smul, hpinv g, hqinv g]) ?_
  simp [mul_comm]

end ZonalHarmonics

section Irreducible

/-- Any nonzero `SO(σ, ℝ)`-invariant subspace of homogeneous polynomials (`|σ| ≥ 2`) contains a
polynomial that does not vanish at a given coordinate basis vector. -/
private theorem exists_mem_eval_single_ne_zero {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ]
    [Field 𝕜] [Algebra ℝ 𝕜] (hσ : 2 ≤ Fintype.card σ) {d : ℕ} (i₀ : σ)
    {W : Submodule 𝕜 (MvPolynomial σ 𝕜)} (hW : W ≤ homogeneousSubmodule σ 𝕜 d)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ, ∀ p ∈ W,
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W)
    (hne : W ≠ ⊥) :
    ∃ p ∈ W, eval (Pi.single i₀ 1) p ≠ 0 := by
  obtain ⟨q, hqW, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hq : q.IsHomogeneous d := hW hqW
  have hex : ∃ x : σ → ℝ, eval (algebraMap ℝ 𝕜 ∘ x) q ≠ 0 := by
    by_contra h
    push Not at h
    exact hq0 (eq_of_eval_algebraMap_eq fun x ↦ by rw [map_zero]; exact h x)
  obtain ⟨x, hx⟩ := hex
  let u : σ → ℝ := Pi.single i₀ 1
  have hu_map : algebraMap ℝ 𝕜 ∘ u = Pi.single i₀ 1 := by
    ext j
    by_cases hj : j = i₀
    · subst hj; simp [u]
    · simp [u, hj]
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : algebraMap ℝ 𝕜 ∘ (0 : σ → ℝ) = 0 := by ext j; simp
    rw [h0] at hx
    have hd0 : d = 0 := by
      by_contra hd
      exact hx (eval_zero_of_isHomogeneous_of_ne_zero hq hd)
    subst hd0
    have hC : q = C (q.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr hq)
    refine ⟨q, hqW, ?_⟩
    rw [hC] at hx ⊢
    simpa using hx
  · have hu : u ⬝ᵥ u = 1 := by simp [u]
    obtain ⟨g, hgx⟩ := exists_specialOrthogonalGroup_transpose_mulVec_eq_normalize hσ hu hx0
    refine ⟨linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q, hinv g q hqW, ?_⟩
    have hscaled :
        algebraMap ℝ 𝕜 ∘ x =
          algebraMap ℝ 𝕜 (Real.sqrt (x ⬝ᵥ x)) •
            (((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) *ᵥ (Pi.single i₀ 1 : σ → 𝕜)) := by
      ext i
      have hi := congrFun hgx i
      rw [← hu_map]
      simp [hi, mulVec, dotProduct, map_sum, map_mul]
    rw [hscaled, hq.eval_smul, ← eval_linearSubst] at hx
    exact right_ne_zero_of_mul hx

/-- Every `SO(σ, ℝ)`-invariant subspace `W ≤ harmonicSubmodule σ 𝕜 d` over `[RCLike 𝕜]` admits an
`SO(σ, ℝ)`-invariant Fischer-orthogonal complement inside `harmonicSubmodule σ 𝕜 d`. -/
private theorem exists_fischerInner_orthogonal_compl {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ]
    [RCLike 𝕜] {d : ℕ} {W : Submodule 𝕜 (MvPolynomial σ 𝕜)}
    (hW : W ≤ harmonicSubmodule σ 𝕜 d)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ, ∀ p ∈ W,
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W) :
    ∃ W_orth : Submodule 𝕜 (MvPolynomial σ 𝕜),
      W_orth ≤ harmonicSubmodule σ 𝕜 d ∧
      (∀ g : Matrix.specialOrthogonalGroup σ ℝ, ∀ p ∈ W_orth,
        linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W_orth) ∧
      W ⊔ W_orth = harmonicSubmodule σ 𝕜 d ∧
      Disjoint W W_orth ∧
      (∀ w ∈ W, ∀ z ∈ W_orth, fischerInner w z = 0) := by
  let H := harmonicSubmodule σ 𝕜 d
  let : NormedAddCommGroup (MvPolynomial σ 𝕜) := (fischerInnerCore σ 𝕜).toNormedAddCommGroup
  let : InnerProductSpace 𝕜 (MvPolynomial σ 𝕜) :=
    InnerProductSpace.ofCore (fischerInnerCore σ 𝕜).toCore
  have hinner_eq (a b : H) : ⟪a, b⟫_𝕜 = fischerInner a.1 b.1 :=
    fischerInnerCore_inner σ 𝕜 a.1 b.1
  let ρ := harmonicSpecialOrthogonalRep σ ℝ 𝕜 d
  let W' : Submodule 𝕜 H := W.comap H.subtype
  have hW'_map : W'.map H.subtype = W := Submodule.map_comap_eq_of_le (by simpa using hW)
  have hW'orth_inv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ, ∀ y ∈ W'ᗮ, ρ g y ∈ W'ᗮ := by
    intro g y hy
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hunit : ⟪ρ g⁻¹ x, ρ g⁻¹ (ρ g y)⟫_𝕜 = ⟪x, ρ g y⟫_𝕜 := by
      rw [hinner_eq, hinner_eq]
      exact fischerInner_harmonicSpecialOrthogonalRep g⁻¹ x (ρ g y)
    have hcancel : ρ g⁻¹ (ρ g y) = y := by
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [← hunit, hcancel]
    exact (Submodule.mem_orthogonal W' y).mp hy _ (by simpa [W', ρ] using hinv g⁻¹ x.1 hx)
  have hcompl : IsCompl W' W'ᗮ := W'.isCompl_orthogonal
  refine ⟨W'ᗮ.map H.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · rintro g _ ⟨y, hy, rfl⟩
    exact ⟨ρ g y, hW'orth_inv g y hy, coe_harmonicSpecialOrthogonalRep_apply g y⟩
  · rw [← hW'_map, ← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_top,
      Submodule.range_subtype]
  · rw [← hW'_map, Submodule.disjoint_def]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hx0 : x = 0 :=
      (Submodule.mem_bot 𝕜).mp (hcompl.disjoint.eq_bot ▸ ⟨hx, Subtype.ext hxy ▸ hy⟩)
    simp [hx0]
  · rintro w hw _ ⟨z, hz, rfl⟩
    exact (hinner_eq ⟨w, hW hw⟩ z).symm.trans ((Submodule.mem_orthogonal W' z).mp hz ⟨w, hW hw⟩ hw)

/-- The Riesz representer of evaluation at the last basis vector inside
`harmonicSubmodule (Fin (n + 1)) 𝕜 d` with respect to `fischerInner` is `SO(n, ℝ)`-invariant. -/
private theorem exists_fischerInner_eq_eval_single_last {n d : ℕ} {𝕜 : Type*} [RCLike 𝕜] :
    ∃ v ∈ harmonicSubmodule (Fin (n + 1)) 𝕜 d,
      (∀ p ∈ harmonicSubmodule (Fin (n + 1)) 𝕜 d,
        fischerInner v p = eval (Pi.single (Fin.last n) 1) p) ∧
      (∀ h : Matrix.specialOrthogonalGroup (Fin n) ℝ,
        linearSubst ((Matrix.blockSucc (h : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)) v =
          v) := by
  let H := harmonicSubmodule (Fin (n + 1)) 𝕜 d
  let : NormedAddCommGroup (MvPolynomial (Fin (n + 1)) 𝕜) :=
    (fischerInnerCore (Fin (n + 1)) 𝕜).toNormedAddCommGroup
  let : InnerProductSpace 𝕜 (MvPolynomial (Fin (n + 1)) 𝕜) :=
    InnerProductSpace.ofCore (fischerInnerCore (Fin (n + 1)) 𝕜).toCore
  have hinner_eq (a b : H) : ⟪a, b⟫_𝕜 = fischerInner a.1 b.1 :=
    fischerInnerCore_inner (Fin (n + 1)) 𝕜 a.1 b.1
  let ρ := harmonicSpecialOrthogonalRep (Fin (n + 1)) ℝ 𝕜 d
  let e : Fin (n + 1) → 𝕜 := Pi.single (Fin.last n) 1
  let L : H →ₗ[𝕜] 𝕜 := (aeval e).toLinearMap.comp H.subtype
  let v : H := (InnerProductSpace.toDual 𝕜 H).symm L.toContinuousLinearMap
  have hv_inner : ∀ p : H, ⟪v, p⟫_𝕜 = eval e p.1 := fun p ↦ by simp [v, L, aeval_eq_eval]
  refine ⟨v.1, v.2, fun p hp ↦ (hinner_eq v ⟨p, hp⟩).symm.trans (hv_inner ⟨p, hp⟩), fun h ↦ ?_⟩
  let h' : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ :=
    ⟨Matrix.blockSucc h.1, Matrix.blockSucc_mem_orthogonalGroup_iff.mpr h.2.1,
      (Matrix.det_blockSucc _).trans h.2.2⟩
  rw [← coe_harmonicSpecialOrthogonalRep_apply h' v]
  refine congrArg Subtype.val (ext_inner_right 𝕜 fun p ↦ ?_ : ρ h' v = v)
  have hunit : ⟪ρ h'⁻¹ (ρ h' v), ρ h'⁻¹ p⟫_𝕜 = ⟪ρ h' v, p⟫_𝕜 := by
    rw [hinner_eq, hinner_eq]
    exact fischerInner_harmonicSpecialOrthogonalRep h'⁻¹ (ρ h' v) p
  have hcancel : ρ h'⁻¹ (ρ h' v) = v := by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [← hunit, hcancel, hv_inner, hv_inner, eval_harmonicSpecialOrthogonalRep_apply, inv_inv]
  have hfix_e : (h'.1.map (algebraMap ℝ 𝕜)) *ᵥ e = e := by
    ext i
    rw [Matrix.map_blockSucc, Matrix.blockSucc_mulVec]
    induction i using Fin.lastCases with
    | last => simp [e]
    | cast j =>
      have hinit : Fin.init e = 0 := by
        ext k
        simp [e, Fin.init, (Fin.castSucc_lt_last k).ne]
      simp [e, hinit, (Fin.castSucc_lt_last j).ne]
  rw [hfix_e]

/-- Irreducibility of `harmonicSubmodule (Fin (n + 1)) 𝕜 d` under `SO(n + 1, ℝ)` for `n ≥ 2` and
`[RCLike 𝕜]`. -/
private theorem eq_bot_or_eq_harmonicSubmodule_fin {n d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (hn : 2 ≤ n) (W : Submodule 𝕜 (MvPolynomial (Fin (n + 1)) 𝕜))
    (hW : W ≤ harmonicSubmodule (Fin (n + 1)) 𝕜 d)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ, ∀ p ∈ W,
      linearSubst ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W) :
    W = ⊥ ∨ W = harmonicSubmodule (Fin (n + 1)) 𝕜 d := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨W_orth, hW_orth_le, hW_orth_inv, hsup, hdisj, horth⟩ :=
    exists_fischerInner_orthogonal_compl hW hinv
  have hW_orth_ne_bot : W_orth ≠ ⊥ := fun h ↦ hcontra.2 (by simpa [h] using hsup)
  obtain ⟨v, hvH, hv_eval, hv_fix⟩ :=
    exists_fischerInner_eq_eval_single_last (n := n) (d := d) (𝕜 := 𝕜)
  obtain ⟨v₁, hv₁, v₂, hv₂, hv_eq⟩ := Submodule.mem_sup.mp (hsup.symm ▸ hvH)
  -- Both components `v₁ ∈ W` and `v₂ ∈ W_orth` are `SO(n, ℝ)`-invariant by disjointness.
  have hfix_pair (h : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
      let M := (Matrix.blockSucc (h : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)
      linearSubst M v₁ = v₁ ∧ linearSubst M v₂ = v₂ := by
    let h' : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ :=
      ⟨Matrix.blockSucc h.1, Matrix.blockSucc_mem_orthogonalGroup_iff.mpr h.2.1,
        (Matrix.det_blockSucc _).trans h.2.2⟩
    set M := (Matrix.blockSucc (h : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)
    have hsum : linearSubst M v₁ + linearSubst M v₂ = v₁ + v₂ := by
      rw [← map_add, hv_eq, hv_fix h]
    have hdiff : linearSubst M v₁ - v₁ = v₂ - linearSubst M v₂ :=
      sub_eq_sub_iff_add_eq_add.mpr (by rw [hsum, add_comm v₁ v₂])
    have hmem : linearSubst M v₁ - v₁ ∈ W ⊓ W_orth :=
      ⟨W.sub_mem (hinv h' v₁ hv₁) hv₁, hdiff ▸ W_orth.sub_mem hv₂ (hW_orth_inv h' v₂ hv₂)⟩
    have hzero : linearSubst M v₁ - v₁ = 0 := by
      rwa [hdisj.eq_bot, Submodule.mem_bot] at hmem
    exact ⟨sub_eq_zero.mp hzero, (sub_eq_zero.mp (hdiff.symm.trans hzero)).symm⟩
  -- Both `v₁` and `v₂` are nonzero since `W` and `W_orth` each contain an element nonzero at `eₙ`.
  have hv₁_ne : v₁ ≠ 0 := by
    obtain ⟨w, hwW, hw_eval⟩ := exists_mem_eval_single_ne_zero (by simp; omega) (Fin.last n)
      (hW.trans (harmonicSubmodule_le_homogeneousSubmodule d)) hinv hcontra.1
    intro h0
    have h12 : fischerInner v₂ w = 0 := by
      rw [← star_fischerInner, horth w hwW v₂ hv₂, star_zero]
    have hfw := hv_eval w (hW hwW)
    rw [← hv_eq, h0, zero_add, h12] at hfw
    exact hw_eval hfw.symm
  have hv₂_ne : v₂ ≠ 0 := by
    obtain ⟨z, hzW, hz_eval⟩ := exists_mem_eval_single_ne_zero (by simp; omega) (Fin.last n)
      (hW_orth_le.trans (harmonicSubmodule_le_homogeneousSubmodule d)) hW_orth_inv hW_orth_ne_bot
    intro h0
    have hfw := hv_eval z (hW_orth_le hzW)
    rw [← hv_eq, h0, add_zero, horth v₁ hv₁ z hzW] at hfw
    exact hz_eval hfw.symm
  -- Uniqueness of zonal harmonics makes `v₁` and `v₂` proportional, contradicting `W ⊓ W_orth = ⊥`.
  have hv₂_eval : eval (Pi.single (Fin.last n) 1) v₂ ≠ 0 := fun h0 ↦
    hv₂_ne (eq_zero_of_mem_harmonicSubmodule_of_blockSucc_invariant_of_eval_last_eq_zero hn
      (hW_orth_le hv₂) (fun h ↦ (hfix_pair h).2) h0)
  have hprop := eval_last_smul_eq_of_mem_harmonicSubmodule_of_blockSucc_invariant hn
    (hW hv₁) (hW_orth_le hv₂) (fun h ↦ (hfix_pair h).1) (fun h ↦ (hfix_pair h).2)
  have hmem_inf : eval (Pi.single (Fin.last n) 1) v₂ • v₁ ∈ W ⊓ W_orth :=
    ⟨W.smul_mem _ hv₁, hprop ▸ W_orth.smul_mem _ hv₂⟩
  rw [hdisj.eq_bot, Submodule.mem_bot, smul_eq_zero] at hmem_inf
  exact hmem_inf.elim hv₂_eval hv₁_ne

/-- Relabeling variables conjugates `linearSubst` by `Matrix.submatrix`. -/
private theorem rename_linearSubst_submatrix {σ τ R : Type*} [Fintype σ] [Fintype τ]
    [CommSemiring R] (e : σ ≃ τ) (M : Matrix τ τ R) (p : MvPolynomial σ R) :
    rename e (linearSubst (M.submatrix e e) p) = linearSubst M (rename e p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, map_mul, rename_X, hp, linearSubst_X, linearSubst_X, map_sum,
      ← Equiv.sum_comp e]
    refine congrArg (_ * ·) (Finset.sum_congr rfl fun j _ ↦ ?_)
    simp [Matrix.submatrix_apply]

/-- **Irreducibility of harmonic polynomials under `SO(N)`**: in dimension at least three over `ℝ`
or `ℂ` (any `[RCLike 𝕜]`), every `SO(σ, ℝ)`-invariant submodule of `harmonicSubmodule σ 𝕜 d` is
either `⊥` or the whole space `harmonicSubmodule σ 𝕜 d`. -/
theorem eq_bot_or_eq_harmonicSubmodule_of_specialOrthogonalGroup_invariant
    {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ] [RCLike 𝕜]
    (hσ : 3 ≤ Fintype.card σ) (d : ℕ)
    (W : Submodule 𝕜 (MvPolynomial σ 𝕜)) (hW : W ≤ harmonicSubmodule σ 𝕜 d)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ, ∀ p ∈ W,
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W) :
    W = ⊥ ∨ W = harmonicSubmodule σ 𝕜 d := by
  let n : ℕ := Fintype.card σ - 1
  have hn : 2 ≤ n := by omega
  have hcard : Fintype.card σ = n + 1 := by omega
  let e : σ ≃ Fin (n + 1) := (Fintype.equivFin σ).trans (finCongr hcard)
  let φ : MvPolynomial σ 𝕜 ≃ₗ[𝕜] MvPolynomial (Fin (n + 1)) 𝕜 := (renameEquiv 𝕜 e).toLinearEquiv
  have hφ_apply (p : MvPolynomial σ 𝕜) : φ p = rename e p := rfl
  have hφ_harm : (harmonicSubmodule σ 𝕜 d).map φ.toLinearMap =
      harmonicSubmodule (Fin (n + 1)) 𝕜 d := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp_hom, hp_lap⟩ := mem_harmonicSubmodule_iff.mp hp
      exact mem_harmonicSubmodule_iff.mpr
        ⟨(IsHomogeneous.rename_isHomogeneous_iff e.injective).mpr hp_hom, by
          rw [LinearEquiv.coe_coe, hφ_apply, laplacian_rename, hp_lap, map_zero]⟩
    · intro hq
      obtain ⟨hq_hom, hq_lap⟩ := mem_harmonicSubmodule_iff.mp hq
      refine ⟨rename e.symm q, mem_harmonicSubmodule_iff.mpr ⟨?_, ?_⟩, ?_⟩
      · exact (IsHomogeneous.rename_isHomogeneous_iff e.symm.injective).mpr hq_hom
      · rw [laplacian_rename, hq_lap, map_zero]
      · rw [LinearEquiv.coe_coe, hφ_apply, rename_rename]
        simp
  have hW_map_le : W.map φ.toLinearMap ≤ harmonicSubmodule (Fin (n + 1)) 𝕜 d :=
    (Submodule.map_mono hW).trans hφ_harm.le
  have hW_map_inv : ∀ g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
      ∀ q ∈ W.map φ.toLinearMap,
        linearSubst ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q ∈
          W.map φ.toLinearMap := by
    rintro g _ ⟨p, hp, rfl⟩
    let g' : Matrix.specialOrthogonalGroup σ ℝ := ⟨g.1.submatrix e e, by
      rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
      refine ⟨?_, ?_⟩
      · rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv _ _ _ e,
          (mem_orthogonalGroup_iff _ _).mp g.2.1, Matrix.submatrix_one_equiv]
      · simpa [Matrix.reindex_apply] using
          (Matrix.det_reindex_self e.symm g.1).trans g.2.2⟩
    refine ⟨linearSubst ((g' : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p, hinv g' p hp, ?_⟩
    exact rename_linearSubst_submatrix e ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map
      (algebraMap ℝ 𝕜)) p
  have hinj := Submodule.map_injective_of_injective φ.injective
  rcases eq_bot_or_eq_harmonicSubmodule_fin hn (W.map φ.toLinearMap) hW_map_le hW_map_inv with
    hbot | htop
  · left
    exact hinj (hbot.trans (Submodule.map_bot _).symm)
  · right
    exact hinj (htop.trans hφ_harm.symm)

/-- In dimension at least three over `ℝ` or `ℂ` (any `[RCLike 𝕜]`), the representation of
`SO(σ, ℝ)` on the degree-`d` harmonic homogeneous polynomials is irreducible. -/
theorem isIrreducible_harmonicSpecialOrthogonalRep {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ]
    [RCLike 𝕜] (hσ : 3 ≤ Fintype.card σ) (d : ℕ) :
    (harmonicSpecialOrthogonalRep σ ℝ 𝕜 d).IsIrreducible := by
  let ρ := harmonicSpecialOrthogonalRep σ ℝ 𝕜 d
  have hpos : 0 < Module.finrank 𝕜 (harmonicSubmodule σ 𝕜 d) :=
    finrank_harmonicSubmodule_pos (by omega) d
  have : Nontrivial (harmonicSubmodule σ 𝕜 d) := Module.nontrivial_of_finrank_pos hpos
  have : Nontrivial (Subrepresentation ρ) := by
    obtain ⟨x, hx⟩ := exists_ne (0 : harmonicSubmodule σ 𝕜 d)
    refine ⟨⟨⊥, ⊤, fun h ↦ hx ?_⟩⟩
    have hmem : x ∈ (⊥ : Subrepresentation ρ).toSubmodule := h ▸ trivial
    exact (Submodule.mem_bot 𝕜).mp hmem
  refine ⟨fun W ↦ ?_⟩
  let H := harmonicSubmodule σ 𝕜 d
  let W' : Submodule 𝕜 (MvPolynomial σ 𝕜) := W.toSubmodule.map H.subtype
  have hW'_le : W' ≤ H := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hW'_inv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ, ∀ p ∈ W',
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W' := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, W.apply_mem_toSubmodule g hx, coe_harmonicSpecialOrthogonalRep_apply g x⟩
  have hinj := Submodule.map_injective_of_injective H.injective_subtype
  rcases eq_bot_or_eq_harmonicSubmodule_of_specialOrthogonalGroup_invariant hσ d W' hW'_le hW'_inv
    with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    exact hinj (hbot.trans (Submodule.map_bot _).symm)
  · right
    apply Subrepresentation.toSubmodule_injective
    refine hinj ?_
    have htop' : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
    rw [htop', Submodule.map_top, Submodule.range_subtype]
    exact htop

/-- In dimension at least three over `ℝ` or `ℂ` (any `[RCLike 𝕜]`), the orthogonal-group
representation `harmonicRep σ 𝕜 d` on the degree-`d` harmonic homogeneous polynomials is
irreducible. -/
theorem isIrreducible_harmonicRep {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ] [RCLike 𝕜]
    (hσ : 3 ≤ Fintype.card σ) (d : ℕ) : (harmonicRep σ 𝕜 d).IsIrreducible := by
  have hirr := isIrreducible_harmonicSpecialOrthogonalRep (σ := σ) (𝕜 := 𝕜) hσ d
  have hne : (⊥ : Submodule 𝕜 (harmonicSubmodule σ 𝕜 d)) ≠ ⊤ := fun h ↦
    bot_ne_top (α := Subrepresentation (harmonicSpecialOrthogonalRep σ ℝ 𝕜 d))
      (Subrepresentation.toSubmodule_injective h)
  have : Nontrivial (Subrepresentation (harmonicRep σ 𝕜 d)) :=
    ⟨⟨⊥, ⊤, fun h ↦ hne (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine ⟨fun W ↦ ?_⟩
  let W' : Subrepresentation (harmonicSpecialOrthogonalRep σ ℝ 𝕜 d) :=
    ⟨W.toSubmodule, fun g _ hx ↦ W.apply_mem_toSubmodule _ hx⟩
  rcases hirr.eq_bot_or_eq_top W' with h | h
  · left
    exact Subrepresentation.toSubmodule_injective (by
      have h' := congrArg Subrepresentation.toSubmodule h
      exact h')
  · right
    exact Subrepresentation.toSubmodule_injective (by
      have h' := congrArg Subrepresentation.toSubmodule h
      exact h')

end Irreducible

end MvPolynomial
