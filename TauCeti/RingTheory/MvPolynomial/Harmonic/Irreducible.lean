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
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Algebra.MvPolynomial.Funext
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.BlockSucc
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Orbit
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Irreducibility of harmonic polynomials under the special orthogonal group

In dimension `N ≥ 3`, the representation `MvPolynomial.harmonicSpecialOrthogonalRep` of the real
special orthogonal group `SO(N)` on the space `H_d` of degree-`d` harmonic homogeneous polynomials
over `ℝ` or `ℂ` (more generally, any `𝕜` with `[RCLike 𝕜]`) is irreducible. The proof uses only
zonal harmonics and orthogonality with respect to the Fischer inner product, without highest-weight
theory:

1. **Invariant homogeneous polynomials.** For `n ≥ 2`, `SO(n)` acts transitively on every sphere in
   `ℝⁿ` (`TauCeti.exists_specialOrthogonalGroup_mulVec_eq_of_dotProduct_eq`). Consequently, an
   `SO(n)`-invariant homogeneous polynomial of odd degree vanishes
   (`MvPolynomial.eq_zero_of_isHomogeneous_odd_of_specialOrthogonalGroup_invariant`), one of even
   degree `2k` is a scalar multiple of `(r²)^k`
   (`exists_eq_C_mul_normSq_pow_of_isHomogeneous_even_of_specialOrthogonalGroup_invariant`), and
   every `SO(n)`-invariant harmonic homogeneous polynomial of positive degree vanishes
   (`MvPolynomial.eq_zero_of_mem_harmonicSubmodule_of_specialOrthogonalGroup_invariant_of_ne_zero`).
2. **Uniqueness of zonal harmonics.** For `n ≥ 2`, expanding a polynomial in `Fin (n + 1)` variables
   in powers of the last variable `Xₙ` (`MvPolynomial.finSuccEquiv'`) expresses `Δ p = 0` as the
   recurrence `Δ' qᵣ + (r + 1)(r + 2) qᵣ₊₂ = 0` (`MvPolynomial.coeff_finSuccEquiv'_laplacian`). If
   `p ∈ H_d` is invariant under the upper-left block subgroup `SO(n) ↪ SO(n + 1)`
   (`TauCeti.specialOrthogonalBlockSucc`) and vanishes at the north pole `eₙ`, downward induction
   together with `MvPolynomial.eq_zero_of_laplacian_normSq_mul_eq_zero` forces every `qᵣ` to vanish
   (`MvPolynomial.eq_zero_of_mem_harmonicSubmodule_of_blockSucc_invariant_of_eval_last_eq_zero`).
   Hence the `SO(n)`-invariant subspace of `H_d` has dimension at most one.
3. **Irreducibility.** Equipping `H_d` with the `SO(N)`-invariant Fischer inner product
   (`MvPolynomial.fischerInnerCore`), the Riesz representer of evaluation at `eₙ` is an
   `SO(N - 1)`-invariant harmonic polynomial. For any `SO(N)`-invariant decomposition
   `H_d = W ⊕ Wᗮ`, both orthogonal components of this representer are `SO(N - 1)`-invariant; if
   both `W` and `Wᗮ` were nonzero, transitivity of `SO(N)` on the sphere would make both components
   nonzero, contradicting uniqueness of zonal harmonics.

The dimension hypothesis `3 ≤ Fintype.card σ` is sharp over `ℂ`: for `N = 2` and `d ≥ 1`, `H_d`
over `ℂ` splits into the two one-dimensional eigenspaces spanned by `(X₀ ± i X₁)^d` (over `ℝ` the
`N = 2` representation is irreducible).

## Main results

* `MvPolynomial.fischerInner_harmonicSpecialOrthogonalRep`: the `SO(σ, ℝ)`-action preserves the
  Fischer inner product over any `[RCLike 𝕜]`.
* `MvPolynomial.eq_zero_of_isHomogeneous_odd_of_specialOrthogonalGroup_invariant`: in at least two
  variables, every `SO(σ, ℝ)`-invariant homogeneous polynomial of odd degree is zero.
* `exists_eq_C_mul_normSq_pow_of_isHomogeneous_even_of_specialOrthogonalGroup_invariant`:
  in at least two variables, every `SO(σ, ℝ)`-invariant homogeneous polynomial of even degree `2k`
  is a constant multiple of `(normSq σ 𝕜)^k`.
* `MvPolynomial.eq_zero_of_mem_harmonicSubmodule_of_specialOrthogonalGroup_invariant_of_ne_zero`:
  in at least two variables, every `SO(σ, ℝ)`-invariant harmonic homogeneous polynomial of positive
  degree is zero.
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
  rw [hH, ← Matrix.map_mul, (mem_orthogonalGroup_iff' σ ℝ).mp g.property.1,
    Matrix.map_one _ (map_zero _) (map_one _)]

section InvariantHomogeneous

variable {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ] [Field 𝕜] [Algebra ℝ 𝕜]

/-- An `SO(σ, ℝ)`-invariant homogeneous polynomial of degree `m` on `ℝˢ` (`|σ| ≥ 2`) satisfies
`q(x) = ‖x‖ᵐ q(u)` for every `x` and every unit vector `u`. -/
private theorem eval_eq_sqrt_dotProduct_pow_mul_of_specialOrthogonalGroup_invariant
    (hσ : 2 ≤ Fintype.card σ) {q : MvPolynomial σ 𝕜} {m : ℕ} (hq : q.IsHomogeneous m)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ,
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q = q)
    {u : σ → ℝ} (hu : u ⬝ᵥ u = 1) (x : σ → ℝ) :
    eval (algebraMap ℝ 𝕜 ∘ x) q =
      algebraMap ℝ 𝕜 (Real.sqrt (x ⬝ᵥ x)) ^ m * eval (algebraMap ℝ 𝕜 ∘ u) q := by
  obtain ⟨g, hgx⟩ := TauCeti.exists_specialOrthogonalGroup_sqrt_dotProduct_smul_mulVec_eq hσ hu x
  have hscaled :
      algebraMap ℝ 𝕜 ∘ x =
        algebraMap ℝ 𝕜 (Real.sqrt (x ⬝ᵥ x)) •
          ((((g⁻¹ : Matrix.specialOrthogonalGroup σ ℝ) : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) *ᵥ
            (algebraMap ℝ 𝕜 ∘ u)) := by
    ext i
    rw [Function.comp_apply, ← congrFun hgx i]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec,
      coe_specialOrthogonalGroup_inv, transpose_transpose]
  rw [hscaled, hq.eval_smul, ← eval_linearSubst, hinv g⁻¹]

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
  have h1 := eval_eq_sqrt_dotProduct_pow_mul_of_specialOrthogonalGroup_invariant hσ hq hinv hu (-u)
  have hneg : algebraMap ℝ 𝕜 ∘ (-u) = (-1 : 𝕜) • (algebraMap ℝ 𝕜 ∘ u) := by ext i; simp
  rw [hneg, hq.eval_smul, hm.neg_one_pow] at h1
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, hu, Real.sqrt_one, map_one, one_pow,
    one_mul, neg_one_mul] at h1
  have hcu : eval (algebraMap ℝ 𝕜 ∘ u) q = 0 :=
    (mul_eq_zero.mp (by rw [two_mul]; exact eq_neg_iff_add_eq_zero.mp h1.symm)).resolve_left
      two_ne_zero
  refine funext_of_injective (algebraMap ℝ 𝕜).injective fun x ↦ ?_
  rw [eval_eq_sqrt_dotProduct_pow_mul_of_specialOrthogonalGroup_invariant hσ hq hinv hu x, hcu,
    mul_zero, map_zero]

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
  refine ⟨eval (algebraMap ℝ 𝕜 ∘ u) q, funext_of_injective (algebraMap ℝ 𝕜).injective fun x ↦ ?_⟩
  rw [eval_eq_sqrt_dotProduct_pow_mul_of_specialOrthogonalGroup_invariant hσ hq hinv hu x]
  have hns : eval (algebraMap ℝ 𝕜 ∘ x) (normSq σ 𝕜) = algebraMap ℝ 𝕜 (x ⬝ᵥ x) := by
    simp [normSq_def, dotProduct, sq, map_sum, map_mul]
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i)
  rw [map_mul, eval_C, map_pow, hns, pow_mul, ← map_pow, Real.sq_sqrt hxx, mul_comm]

/-- In at least two variables, every `SO(σ, ℝ)`-invariant harmonic homogeneous polynomial of
positive degree is zero. -/
theorem eq_zero_of_mem_harmonicSubmodule_of_specialOrthogonalGroup_invariant_of_ne_zero
    (hσ : 2 ≤ Fintype.card σ) {q : MvPolynomial σ 𝕜} {m : ℕ}
    (hq : q ∈ harmonicSubmodule σ 𝕜 m) (hm : m ≠ 0)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ,
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q = q) :
    q = 0 := by
  have : CharZero 𝕜 := charZero_of_injective_algebraMap (algebraMap ℝ 𝕜).injective
  have : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hq_hom, hq_lap⟩ := mem_harmonicSubmodule_iff.mp hq
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | hodd
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hhom' : q.IsHomogeneous (2 * (k' + 1)) := by simpa [two_mul] using hq_hom
    obtain ⟨c, hc⟩ :=
      exists_eq_C_mul_normSq_pow_of_isHomogeneous_even_of_specialOrthogonalGroup_invariant hσ
        hhom' hinv
    have hfac : q = normSq σ 𝕜 * (C c * normSq σ 𝕜 ^ k') := by rw [hc, pow_succ']; ring
    rw [hfac] at hq_lap ⊢
    rw [eq_zero_of_laplacian_normSq_mul_eq_zero hq_lap, mul_zero]
  · exact eq_zero_of_isHomogeneous_odd_of_specialOrthogonalGroup_invariant hσ hq_hom hodd hinv

end InvariantHomogeneous

section ZonalHarmonics

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
  obtain ⟨hp_hom, hp_lap⟩ := mem_harmonicSubmodule_iff.mp hp
  let q : ℕ → MvPolynomial (Fin n) 𝕜 := fun r ↦ (finSuccEquiv' 𝕜 (Fin.last n) p).coeff r
  have hq_inv (r : ℕ) (g : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
      linearSubst ((g : Matrix (Fin n) (Fin n) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) (q r) = q r := by
    have h := congrArg (fun f ↦ (finSuccEquiv' 𝕜 (Fin.last n) f).coeff r) (hinv g)
    rwa [Matrix.transpose_blockSucc, Matrix.map_blockSucc,
      coeff_finSuccEquiv'_last_linearSubst_blockSucc] at h
  have hq_rec (r : ℕ) : laplacian (q r) + ((r + 1) * (r + 2)) • q (r + 2) = 0 := by
    have h := congrArg (fun f ↦ (finSuccEquiv' 𝕜 (Fin.last n) f).coeff r) hp_lap
    rwa [coeff_finSuccEquiv'_laplacian, map_zero, Polynomial.coeff_zero] at h
  -- Downward induction on `m = d - r` forces every coefficient `q r` to vanish.
  have hq_down : ∀ m, m ≤ d → q (d - m) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hmd
      rcases eq_or_ne m 0 with rfl | hm0
      · simp [q, hp_hom.coeff_finSuccEquiv'_self (Fin.last n), heval]
      · have hq2 : q (d - m + 2) = 0 := by
          rcases eq_or_ne m 1 with rfl | hm1
          · exact hp_hom.coeff_finSuccEquiv'_eq_zero_of_lt (Fin.last n) (by omega)
          · have hr2 : d - m + 2 = d - (m - 2) := by omega
            rw [hr2]
            exact ih (m - 2) (by omega) (by omega)
        have hmem : q (d - m) ∈ harmonicSubmodule (Fin n) 𝕜 m :=
          mem_harmonicSubmodule_iff.mpr
            ⟨by simpa [Nat.sub_sub_self hmd] using
                hp_hom.coeff_finSuccEquiv' (Fin.last n) (Nat.sub_le d m),
              by simpa [hq2] using hq_rec (d - m)⟩
        exact eq_zero_of_mem_harmonicSubmodule_of_specialOrthogonalGroup_invariant_of_ne_zero
          (by simpa using hn) hmem hm0 (hq_inv (d - m))
  apply (finSuccEquiv' 𝕜 (Fin.last n)).injective
  refine AddMonoidAlgebra.ext (Finsupp.ext fun r ↦ ?_)
  rw [map_zero, Polynomial.coeff_zero]
  by_cases hrd : r ≤ d
  · simpa [q, Nat.sub_sub_self hrd] using hq_down (d - r) (Nat.sub_le d r)
  · exact hp_hom.coeff_finSuccEquiv'_eq_zero_of_lt (Fin.last n) (by omega)

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

section FischerInnerProduct

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
    by_contra! h
    exact hq0 (funext_of_injective (algebraMap ℝ 𝕜).injective fun x ↦ by rw [map_zero]; exact h x)
  obtain ⟨x, hx⟩ := hex
  let u : σ → ℝ := Pi.single i₀ 1
  have hu_map : algebraMap ℝ 𝕜 ∘ u = Pi.single i₀ 1 := by
    ext j
    by_cases hj : j = i₀ <;> simp [u, hj]
  obtain ⟨g, hgx⟩ := TauCeti.exists_specialOrthogonalGroup_sqrt_dotProduct_smul_mulVec_eq hσ
    (by simp [u] : u ⬝ᵥ u = 1) x
  refine ⟨linearSubst
      (((g⁻¹ : Matrix.specialOrthogonalGroup σ ℝ) : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q,
    hinv g⁻¹ q hqW, ?_⟩
  have hscaled :
      algebraMap ℝ 𝕜 ∘ x =
        algebraMap ℝ 𝕜 (Real.sqrt (x ⬝ᵥ x)) •
          ((((g⁻¹ : Matrix.specialOrthogonalGroup σ ℝ) : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) *ᵥ
            (Pi.single i₀ 1 : σ → 𝕜)) := by
    rw [← hu_map]
    ext i
    rw [Function.comp_apply, ← congrFun hgx i]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec,
      coe_specialOrthogonalGroup_inv, transpose_transpose]
  rw [hscaled, hq.eval_smul, ← eval_linearSubst] at hx
  exact right_ne_zero_of_mul hx

section InnerSpace

variable {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ] [RCLike 𝕜]

private noncomputable local instance : NormedAddCommGroup (MvPolynomial σ 𝕜) :=
  (fischerInnerCore σ 𝕜).toNormedAddCommGroup

private noncomputable local instance : InnerProductSpace 𝕜 (MvPolynomial σ 𝕜) :=
  InnerProductSpace.ofCore (fischerInnerCore σ 𝕜).toCore

omit [DecidableEq σ] in
private theorem inner_harmonicSubmodule_eq_fischerInner {d : ℕ}
    (a b : harmonicSubmodule σ 𝕜 d) : ⟪a, b⟫_𝕜 = fischerInner a.val b.val :=
  fischerInnerCore_inner σ 𝕜 a.val b.val

private theorem inner_harmonicSpecialOrthogonalRep_left {d : ℕ}
    (g : Matrix.specialOrthogonalGroup σ ℝ) (a b : harmonicSubmodule σ 𝕜 d) :
    ⟪harmonicSpecialOrthogonalRep σ ℝ 𝕜 d g a, b⟫_𝕜 =
      ⟪a, harmonicSpecialOrthogonalRep σ ℝ 𝕜 d g⁻¹ b⟫_𝕜 := by
  rw [inner_harmonicSubmodule_eq_fischerInner, inner_harmonicSubmodule_eq_fischerInner,
    ← fischerInner_harmonicSpecialOrthogonalRep g⁻¹ (harmonicSpecialOrthogonalRep σ ℝ 𝕜 d g a) b,
    Representation.inv_self_apply]

private theorem inner_harmonicSpecialOrthogonalRep_right {d : ℕ}
    (g : Matrix.specialOrthogonalGroup σ ℝ) (a b : harmonicSubmodule σ 𝕜 d) :
    ⟪a, harmonicSpecialOrthogonalRep σ ℝ 𝕜 d g b⟫_𝕜 =
      ⟪harmonicSpecialOrthogonalRep σ ℝ 𝕜 d g⁻¹ a, b⟫_𝕜 := by
  simpa only [inv_inv] using (inner_harmonicSpecialOrthogonalRep_left g⁻¹ a b).symm

/-- Every `SO(σ, ℝ)`-invariant subspace `W ≤ harmonicSubmodule σ 𝕜 d` over `[RCLike 𝕜]` admits an
`SO(σ, ℝ)`-invariant Fischer-orthogonal complement inside `harmonicSubmodule σ 𝕜 d`. -/
private theorem exists_fischerInner_orthogonal_compl {d : ℕ}
    {W : Submodule 𝕜 (MvPolynomial σ 𝕜)} (hW : W ≤ harmonicSubmodule σ 𝕜 d)
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
  let ρ := harmonicSpecialOrthogonalRep σ ℝ 𝕜 d
  let W' : Submodule 𝕜 H := W.comap H.subtype
  have hW'_map : W'.map H.subtype = W := Submodule.map_comap_eq_of_le (by simpa using hW)
  have hW'orth_inv (g : Matrix.specialOrthogonalGroup σ ℝ) (y : H) (hy : y ∈ W'ᗮ) :
      ρ g y ∈ W'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [inner_harmonicSpecialOrthogonalRep_right]
    exact (Submodule.mem_orthogonal W' y).mp hy _ (by simpa [W', ρ] using hinv g⁻¹ x.val hx)
  have hcompl : IsCompl W' W'ᗮ := W'.isCompl_orthogonal
  refine ⟨W'ᗮ.map H.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
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
    exact (inner_harmonicSubmodule_eq_fischerInner ⟨w, hW hw⟩ z).symm.trans
      ((Submodule.mem_orthogonal W' z).mp hz ⟨w, hW hw⟩ hw)

/-- The Riesz representer of evaluation at the last basis vector inside
`harmonicSubmodule (Fin (n + 1)) 𝕜 d` with respect to `fischerInner` is `SO(n, ℝ)`-invariant. -/
private theorem exists_fischerInner_eq_eval_single_last {n d : ℕ} :
    ∃ v ∈ harmonicSubmodule (Fin (n + 1)) 𝕜 d,
      (∀ p ∈ harmonicSubmodule (Fin (n + 1)) 𝕜 d,
        fischerInner v p = eval (Pi.single (Fin.last n) 1) p) ∧
      (∀ h : Matrix.specialOrthogonalGroup (Fin n) ℝ,
        linearSubst ((Matrix.blockSucc (h : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)) v =
          v) := by
  let H := harmonicSubmodule (Fin (n + 1)) 𝕜 d
  let ρ := harmonicSpecialOrthogonalRep (Fin (n + 1)) ℝ 𝕜 d
  let e : Fin (n + 1) → 𝕜 := Pi.single (Fin.last n) 1
  let L : H →ₗ[𝕜] 𝕜 := (aeval e).toLinearMap.comp H.subtype
  let v : H := (InnerProductSpace.toDual 𝕜 H).symm L.toContinuousLinearMap
  have hv_inner (p : H) : ⟪v, p⟫_𝕜 = eval e p.val := by simp [v, L, aeval_eq_eval]
  refine ⟨v.val, v.property,
    fun p hp ↦ (inner_harmonicSubmodule_eq_fischerInner v ⟨p, hp⟩).symm.trans (hv_inner ⟨p, hp⟩),
    fun h ↦ ?_⟩
  let h' := TauCeti.specialOrthogonalBlockSucc ℝ n h
  rw [← TauCeti.coe_specialOrthogonalBlockSucc, ← coe_harmonicSpecialOrthogonalRep_apply h' v]
  refine congrArg Subtype.val (ext_inner_right 𝕜 fun p ↦ ?_ : ρ h' v = v)
  rw [inner_harmonicSpecialOrthogonalRep_left, hv_inner, hv_inner,
    eval_harmonicSpecialOrthogonalRep_apply, inv_inv]
  have hfixR : (h' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) *ᵥ Pi.single (Fin.last n) 1 =
      Pi.single (Fin.last n) 1 :=
    (TauCeti.exists_specialOrthogonalBlockSucc_eq_iff_mulVec_single ℝ n h').mp ⟨h, rfl⟩
  have he_map : e = algebraMap ℝ 𝕜 ∘ (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ) := by
    ext i
    by_cases hi : i = Fin.last n <;> simp [e, hi]
  have hfix : (h' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).map (algebraMap ℝ 𝕜) *ᵥ e = e := by
    rw [he_map]
    ext i
    rw [← RingHom.map_mulVec, hfixR, Function.comp_apply]
  rw [hfix]

end InnerSpace

end FischerInnerProduct

section Irreducible

/-- If `v = v₁ + v₂` with `v₁ ∈ W`, `v₂ ∈ W_orth`, `Disjoint W W_orth`, both subspaces invariant
under `SO(n + 1, ℝ)`, and `v` invariant under `SO(n, ℝ)` via `Matrix.blockSucc`, then both `v₁` and
`v₂` are invariant under `SO(n, ℝ)`. -/
private theorem blockSucc_invariant_of_eq_add_of_disjoint {n : ℕ} {𝕜 : Type*} [CommRing 𝕜]
    [Algebra ℝ 𝕜] {W W_orth : Submodule 𝕜 (MvPolynomial (Fin (n + 1)) 𝕜)}
    (hdisj : Disjoint W W_orth)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ, ∀ p ∈ W,
      linearSubst ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W)
    (hW_orth_inv : ∀ g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ, ∀ p ∈ W_orth,
      linearSubst ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W_orth)
    {v v₁ v₂ : MvPolynomial (Fin (n + 1)) 𝕜} (hv₁ : v₁ ∈ W) (hv₂ : v₂ ∈ W_orth)
    (hv_eq : v₁ + v₂ = v)
    (hv_fix : ∀ h : Matrix.specialOrthogonalGroup (Fin n) ℝ,
      linearSubst ((Matrix.blockSucc (h : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)) v = v)
    (h : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    let M := (Matrix.blockSucc (h : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)
    linearSubst M v₁ = v₁ ∧ linearSubst M v₂ = v₂ := by
  let h' := TauCeti.specialOrthogonalBlockSucc ℝ n h
  set M := (Matrix.blockSucc (h : Matrix (Fin n) (Fin n) ℝ))ᵀ.map (algebraMap ℝ 𝕜)
  have hM : ((h' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) = M := by
    rw [TauCeti.coe_specialOrthogonalBlockSucc]
  have hsum : linearSubst M v₁ + linearSubst M v₂ = v₁ + v₂ := by
    rw [← map_add, hv_eq, hv_fix h]
  have hdiff : linearSubst M v₁ - v₁ = v₂ - linearSubst M v₂ :=
    sub_eq_sub_iff_add_eq_add.mpr (by rw [hsum, add_comm v₁ v₂])
  have hmem : linearSubst M v₁ - v₁ ∈ W ⊓ W_orth :=
    ⟨W.sub_mem (hM ▸ hinv h' v₁ hv₁) hv₁, hdiff ▸ W_orth.sub_mem hv₂ (hM ▸ hW_orth_inv h' v₂ hv₂)⟩
  have hzero : linearSubst M v₁ - v₁ = 0 := by
    rwa [hdisj.eq_bot, Submodule.mem_bot] at hmem
  exact ⟨sub_eq_zero.mp hzero, (sub_eq_zero.mp (hdiff.symm.trans hzero)).symm⟩

/-- Irreducibility of `harmonicSubmodule (Fin (n + 1)) 𝕜 d` under `SO(n + 1, ℝ)` for `n ≥ 2` and
`[RCLike 𝕜]`. -/
private theorem eq_bot_or_eq_harmonicSubmodule_fin {n d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (hn : 2 ≤ n) (W : Submodule 𝕜 (MvPolynomial (Fin (n + 1)) 𝕜))
    (hW : W ≤ harmonicSubmodule (Fin (n + 1)) 𝕜 d)
    (hinv : ∀ g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ, ∀ p ∈ W,
      linearSubst ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W) :
    W = ⊥ ∨ W = harmonicSubmodule (Fin (n + 1)) 𝕜 d := by
  by_contra! hcontra
  obtain ⟨W_orth, hW_orth_le, hW_orth_inv, hsup, hdisj, horth⟩ :=
    exists_fischerInner_orthogonal_compl hW hinv
  have hW_orth_ne_bot : W_orth ≠ ⊥ := fun h ↦ hcontra.2 (by simpa [h] using hsup)
  obtain ⟨v, hvH, hv_eval, hv_fix⟩ :=
    exists_fischerInner_eq_eval_single_last (n := n) (d := d) (𝕜 := 𝕜)
  obtain ⟨v₁, hv₁, v₂, hv₂, hv_eq⟩ := Submodule.mem_sup.mp (hsup.symm ▸ hvH)
  have hfix_pair := blockSucc_invariant_of_eq_add_of_disjoint hdisj hinv hW_orth_inv
    hv₁ hv₂ hv_eq hv_fix
  have hv₁_ne : v₁ ≠ 0 := by
    obtain ⟨w, hwW, hw_eval⟩ := exists_mem_eval_single_ne_zero (by simp; omega) (Fin.last n)
      (hW.trans (harmonicSubmodule_le_homogeneousSubmodule d)) hinv hcontra.1
    intro h0
    have h12 : fischerInner v₂ w = 0 := by
      rw [← star_fischerInner, horth w hwW v₂ hv₂, star_zero]
    exact hw_eval ((hv_eval w (hW hwW)).symm.trans (by rw [← hv_eq, h0, zero_add, h12]))
  have hv₂_ne : v₂ ≠ 0 := by
    obtain ⟨z, hzW, hz_eval⟩ := exists_mem_eval_single_ne_zero (by simp; omega) (Fin.last n)
      (hW_orth_le.trans (harmonicSubmodule_le_homogeneousSubmodule d)) hW_orth_inv hW_orth_ne_bot
    intro h0
    exact hz_eval ((hv_eval z (hW_orth_le hzW)).symm.trans
      (by rw [← hv_eq, h0, add_zero, horth v₁ hv₁ z hzW]))
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
  let e : σ ≃ Fin (n + 1) := (Fintype.equivFin σ).trans (finCongr (by omega))
  let φ := (renameEquiv 𝕜 e).toLinearMap
  have hW_map_le : W.map φ ≤ harmonicSubmodule (Fin (n + 1)) 𝕜 d :=
    (Submodule.map_mono hW).trans (map_rename_harmonicSubmodule e d).le
  have hW_map_inv : ∀ g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
      ∀ q ∈ W.map φ,
        linearSubst ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) q ∈
          W.map φ := by
    rintro g _ ⟨p, hp, rfl⟩
    let g' : Matrix.specialOrthogonalGroup σ ℝ := ⟨g.val.submatrix e e,
      letI := starRingOfComm (R := ℝ); Matrix.submatrix_equiv_mem_unitary.mpr g.property.1,
      by simpa [Matrix.reindex_apply] using
        (Matrix.det_reindex_self e.symm g.val).trans g.property.2⟩
    exact ⟨linearSubst ((g' : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p, hinv g' p hp,
      rename_linearSubst_submatrix e
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p⟩
  have hinj := Submodule.map_injective_of_injective (renameEquiv 𝕜 e).toLinearEquiv.injective
  rcases eq_bot_or_eq_harmonicSubmodule_fin hn (W.map φ) hW_map_le hW_map_inv with hbot | htop
  · exact Or.inl (hinj (hbot.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hinj (htop.trans (map_rename_harmonicSubmodule e d).symm))

/-- In dimension at least three over `ℝ` or `ℂ` (any `[RCLike 𝕜]`), the representation of
`SO(σ, ℝ)` on the degree-`d` harmonic homogeneous polynomials is irreducible. -/
theorem isIrreducible_harmonicSpecialOrthogonalRep {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ]
    [RCLike 𝕜] (hσ : 3 ≤ Fintype.card σ) (d : ℕ) :
    (harmonicSpecialOrthogonalRep σ ℝ 𝕜 d).IsIrreducible := by
  let ρ := harmonicSpecialOrthogonalRep σ ℝ 𝕜 d
  have : Nontrivial (harmonicSubmodule σ 𝕜 d) :=
    Module.nontrivial_of_finrank_pos (finrank_harmonicSubmodule_pos (by omega) d)
  refine ⟨fun W ↦ ?_⟩
  let H := harmonicSubmodule σ 𝕜 d
  let W' : Submodule 𝕜 (MvPolynomial σ 𝕜) := W.toSubmodule.map H.subtype
  have hW'_le : W' ≤ H := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hW'_inv : ∀ g : Matrix.specialOrthogonalGroup σ ℝ, ∀ p ∈ W',
      linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ 𝕜)) p ∈ W' := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, W.apply_mem_toSubmodule g hx, coe_harmonicSpecialOrthogonalRep_apply g x⟩
  have hinj := Submodule.map_injective_of_injective H.injective_subtype
  rcases eq_bot_or_eq_harmonicSubmodule_of_specialOrthogonalGroup_invariant hσ d W' hW'_le hW'_inv
    with hbot | htop
  · exact Or.inl <| Subrepresentation.toSubmodule_injective <|
      (hinj (hbot.trans (Submodule.map_bot _).symm)).trans Subrepresentation.toSubmodule_bot.symm
  · refine Or.inr <| Subrepresentation.toSubmodule_injective <| hinj ?_
    rw [Subrepresentation.toSubmodule_top, Submodule.map_top, Submodule.range_subtype]
    exact htop

/-- In dimension at least three over `ℝ` or `ℂ` (any `[RCLike 𝕜]`), the orthogonal-group
representation `harmonicRep σ 𝕜 d` on the degree-`d` harmonic homogeneous polynomials is
irreducible. -/
theorem isIrreducible_harmonicRep {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ] [RCLike 𝕜]
    (hσ : 3 ≤ Fintype.card σ) (d : ℕ) : (harmonicRep σ 𝕜 d).IsIrreducible := by
  have hirr := isIrreducible_harmonicSpecialOrthogonalRep (σ := σ) (𝕜 := 𝕜) hσ d
  have : Nontrivial (harmonicSubmodule σ 𝕜 d) :=
    Module.nontrivial_of_finrank_pos (finrank_harmonicSubmodule_pos (by omega) d)
  refine ⟨fun W ↦ ?_⟩
  let W' : Subrepresentation (harmonicSpecialOrthogonalRep σ ℝ 𝕜 d) :=
    ⟨W.toSubmodule, fun g _ hx ↦ by
      rw [harmonicSpecialOrthogonalRep_def, MonoidHom.comp_apply, MonoidHom.comp_apply]
      exact W.apply_mem_toSubmodule _ hx⟩
  rcases hirr.eq_bot_or_eq_top W' with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      ((congrArg Subrepresentation.toSubmodule h).trans Subrepresentation.toSubmodule_bot.symm))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      ((congrArg Subrepresentation.toSubmodule h).trans Subrepresentation.toSubmodule_top.symm))

end Irreducible

end MvPolynomial
