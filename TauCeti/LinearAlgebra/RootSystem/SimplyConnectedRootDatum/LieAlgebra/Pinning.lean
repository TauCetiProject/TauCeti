/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Chevalley
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# Uniform Chevalley pinning for the Demazure construction

The pinned rational Lie algebra of a valid Dynkin type carries Bourbaki-numbered generators
(`TauCeti.DynkinType.lieBasis`): raising generators `e i` and lowering generators `f i` that
are nilpotent matrices, Cartan generators `h i`, satisfying the Cartan-matrix relations
(`TauCeti.DynkinType.lie_lieBasis_h_e`, `TauCeti.DynkinType.lie_lieBasis_h_f`) and exchanged
by the Chevalley involution (`TauCeti.DynkinType.chevalleyInvolution_lieBasis_e`).

This module packages the uniform exponential `exp(u • e i)`, the pinning isomorphism
`𝔾_a → U_i` that is the input to the Chevalley-Demazure group-scheme construction. The
nilpotency makes the exponential a finite sum, hence a polynomial map over any `ℚ`-algebra.

## Main definitions

* `TauCeti.DynkinType.pinnedExp`: the uniform exponential `u ↦ exp(u • e_i)` as a matrix
  over any `ℚ`-algebra, defined as a finite sum using the matrix dimension as bound.

## Main results

* `TauCeti.DynkinType.pinnedExp_zero`: the exponential at zero is the identity matrix.
* `TauCeti.DynkinType.pinnedExpNeg`: the uniform lowering exponential `u ↦ exp(u • f_i)`.
* `TauCeti.DynkinType.pinnedExpNeg_zero`: its value at zero.
* `TauCeti.DynkinType.pinnedExp_comm_of_matrix_comm`: commuting generators give commuting
  exponentials, the group-level form of a vanishing Lie bracket.
* `TauCeti.DynkinType.pinnedExp_comm_of_cartan_eq_zero`: the Chevalley commutator relation
  (commuting case) — when the Cartan matrix entry is zero (i.e., `α_i + α_j` is not a root),
  the root subgroups commute, via the Serre relation.
* `TauCeti.DynkinType.lie_lieBasis_e_e_e_of_cartan_eq_neg_one`: for a length-one root
  string (`A_{ji} = -1`), the double bracket `⁅e_i, ⁅e_i, e_j⁆⁆` vanishes — the Heisenberg
  Lie-algebra structure underlying the non-commuting Chevalley commutator formula.
* `TauCeti.DynkinType.pinnedExp_mul_pinnedExp_neg`: the uniform exponential is inverted by
  negating the parameter, via the binomial theorem and sharp nilpotency.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

Roadmap: ReductiveGroups (Layer 9, uniform pinned Chevalley-Demazure construction).
-/

public section

/-! ## Sharp nilpotency bound -/

/-- A nilpotent matrix over `ℚ` vanishes when raised to the matrix dimension. By
Cayley-Hamilton the characteristic polynomial annihilates the matrix; for a nilpotent
matrix the difference `charpoly - X ^ N` is nilpotent, hence zero over a domain, so the
characteristic polynomial is `X ^ N`. -/
theorem Matrix.IsNilpotent.pow_card_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℚ} (h : IsNilpotent A) : A ^ Fintype.card n = 0 := by
  have hq : IsNilpotent (A.charpoly - Polynomial.X ^ Fintype.card n) :=
    Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have hchar : A.charpoly = Polynomial.X ^ Fintype.card n := sub_eq_zero.mp hq.eq_zero
  have hCH := Matrix.aeval_self_charpoly A
  rw [hchar, map_pow] at hCH
  simpa using hCH

namespace TauCeti.DynkinType

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-! ## The uniform exponential -/

/-- The uniform exponential of the `i`-th simple raising generator: `exp(u • e_i)` as a
finite sum over `k < Fintype.card (t.GeckIndex ht)`. Since `e_i` is nilpotent
(`TauCeti.DynkinType.isNilpotent_coe_lieBasis_e`), terms beyond the nilpotency index vanish,
so the matrix-dimension bound is safe. -/
def pinnedExp (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  ∑ k ∈ Finset.range (Fintype.card (t.GeckIndex ht)),
    (u ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹) •
      (((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) ^ k).map
        (algebraMap ℚ R)

/-- The exponential at `u = 0` is the identity matrix: only the `k = 0` term survives. -/
theorem pinnedExp_zero (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) :
    t.pinnedExp ht R i 0 = 1 := by
  unfold pinnedExp
  have h0mem : (0 : ℕ) ∈ Finset.range (Fintype.card (t.GeckIndex ht)) := by
    simp only [Finset.mem_range]
    have hpos : 0 < t.numRoots := t.numRoots_pos ht
    have hcard : Fintype.card (t.GeckIndex ht)
        = Fintype.card (t.rationalBase ht).support + t.numRoots := by
      simp [GeckIndex, Fintype.card_sum]
    omega
  rw [Finset.sum_eq_single_of_mem _ h0mem]
  · simp
  · intro k _ hk
    rw [zero_pow hk]
    simp

/-- The uniform lowering exponential `u ↦ exp(u • f_i)`, defined as the same finite sum with
the lowering generator. -/
def pinnedExpNeg (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) (u : R) :
    Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
  ∑ k ∈ Finset.range (Fintype.card (t.GeckIndex ht)),
    (u ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹) •
      (((t.lieBasis ht).f i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) ^ k).map
        (algebraMap ℚ R)

/-- The lowering exponential at `u = 0` is the identity matrix. -/
theorem pinnedExpNeg_zero (R : Type*) [CommRing R] [Algebra ℚ R] (i : Fin t.rank) :
    t.pinnedExpNeg ht R i 0 = 1 := by
  unfold pinnedExpNeg
  have h0mem : (0 : ℕ) ∈ Finset.range (Fintype.card (t.GeckIndex ht)) := by
    simp only [Finset.mem_range]
    have hpos : 0 < t.numRoots := t.numRoots_pos ht
    have hcard : Fintype.card (t.GeckIndex ht)
        = Fintype.card (t.rationalBase ht).support + t.numRoots := by
      simp [GeckIndex, Fintype.card_sum]
    omega
  rw [Finset.sum_eq_single_of_mem _ h0mem]
  · simp
  · intro k _ hk
    rw [zero_pow hk]
    simp

/-! ## Commutator relations -/

/-- If the simple raising generators commute as matrices, their uniform exponentials commute.
This is the group-level reflection of a vanishing Lie bracket: when `⁅e_i, e_j⁆ = 0`, the
corresponding root subgroups commute. -/
theorem pinnedExp_comm_of_matrix_comm (R : Type*) [CommRing R] [Algebra ℚ R]
    (i j : Fin t.rank) (u v : R)
    (hcomm : ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
             ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
             ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
             ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)) :
    t.pinnedExp ht R i u * t.pinnedExp ht R j v =
      t.pinnedExp ht R j v * t.pinnedExp ht R i u := by
  unfold pinnedExp
  -- Expand both products as double sums
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  -- Swap summation order on the left to match the right
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  -- Term-wise: (c_k • A^k) * (d_l • B^l) = (d_l • B^l) * (c_k • A^k)
  -- Scalars commute (commutative ring), matrices commute by hypothesis
  let Ei : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ := (t.lieBasis ht).e i
  let Ej : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ := (t.lieBasis ht).e j
  have hmat : ((Ei ^ k).map (algebraMap ℚ R)) * ((Ej ^ l).map (algebraMap ℚ R)) =
      ((Ej ^ l).map (algebraMap ℚ R)) * ((Ei ^ k).map (algebraMap ℚ R)) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    have hcomm' : Commute Ei Ej := hcomm
    exact (hcomm'.pow_pow k l).eq
  -- Distribute scalars: (c • A) * (d • B) = (c * d) • (A * B)
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Use matrix commutativity to align the matrix factors
  rw [hmat]
  -- Now both sides have (B^l * A^k); scalars commute
  rw [mul_comm (u ^ k * _) (v ^ l * _)]

/-- The Lie bracket of distinct simple raising generators vanishes when the corresponding
Cartan matrix entry is zero. This is the Serre relation: when `A_{ji} = 0`, the exponent
`(-Aᵀ_{ij}).toNat = 0`, so `(ad e_i)^0 [e_i, e_j] = [e_i, e_j] = 0`. -/
theorem lie_lieBasis_e_e_of_cartan_eq_zero (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = 0) :
    ⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆ = 0 := by
  have hserre := (t.isSerreSystem_lieBasis ht).ad_pow_lie_E_E i j
  -- The Cartan matrix in the Serre system is the transpose: (Aᵀ)_{ij} = A_{ji}
  have hCM : (-(t.cartanMatrix.transpose i j)).toNat = 0 := by
    rw [Matrix.transpose_apply, hA]
    simp
  rw [hCM, pow_zero] at hserre
  simpa using hserre

/-- When the Cartan matrix entry vanishes, the simple raising generators commute as matrices.
The Lie bracket in the matrix Lie algebra is the commutator, so a vanishing bracket gives
commuting matrices. -/
theorem coe_lieBasis_e_comm_of_cartan_eq_zero (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = 0) :
    ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
     ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
    ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
     ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) := by
  have hbracket := t.lie_lieBasis_e_e_of_cartan_eq_zero ht i j hA
  -- The inclusion of the Lie subalgebra preserves brackets
  have hcoe : ((((⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆ : t.lieAlgebra ht))) :
      Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      ⁅(((t.lieBasis ht).e i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ),
       (((t.lieBasis ht).e j) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)⁆ :=
    LieSubalgebra.coe_bracket (t.lieAlgebra ht) _ _
  rw [hbracket] at hcoe
  -- The coercion of 0 is 0
  simp only [ZeroMemClass.coe_zero] at hcoe
  -- For matrices, ⁅A, B⁆ = A * B - B * A
  have hcomm : ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
      ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) -
      ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
      ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) = 0 := by
    have h := hcoe
    rw [LieRing.of_associative_ring_bracket] at h
    exact h.symm
  exact sub_eq_zero.mp hcomm

/-- The Chevalley commutator relation (commuting case): when the Cartan matrix entry is zero
— i.e., when `α_i + α_j` is not a root — the corresponding root subgroups commute. This
connects the root-theoretic hypothesis to the group-level commutativity via the Serre
relation and the matrix commutator. -/
theorem pinnedExp_comm_of_cartan_eq_zero (R : Type*) [CommRing R] [Algebra ℚ R]
    (i j : Fin t.rank) (hA : t.cartanMatrix j i = 0) (u v : R) :
    t.pinnedExp ht R i u * t.pinnedExp ht R j v =
      t.pinnedExp ht R j v * t.pinnedExp ht R i u := by
  apply t.pinnedExp_comm_of_matrix_comm ht R i j u v
  exact t.coe_lieBasis_e_comm_of_cartan_eq_zero ht i j hA

/-! ## Length-one root strings: Heisenberg Lie algebra structure -/

/-- For a length-one root string (`A_{ji} = -1`, i.e., `α_i + α_j` is a root but
`2α_i + α_j` is not), the double bracket `⁅e_i, ⁅e_i, e_j⁆⁆` vanishes. This is the Serre
relation: `(ad e_i)^{-A_{ji}}(⁅e_i, e_j⁆) = (ad e_i)(⁅e_i, e_j⁆) = 0`. Together with the symmetric
statement, this says the subalgebra generated by `e_i, e_j` is Heisenberg, the Lie-algebra
input to the Chevalley commutator formula
`[x_{α_i}(u), x_{α_j}(v)] = x_{α_i+α_j}(N_{ij} uv)`. -/
theorem lie_lieBasis_e_e_e_of_cartan_eq_neg_one (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = -1) :
    ⁅(t.lieBasis ht).e i, ⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆⁆ = 0 := by
  have hserre := (t.isSerreSystem_lieBasis ht).ad_pow_lie_E_E i j
  -- The Cartan matrix in the Serre system is the transpose: (Aᵀ)_{ij} = A_{ji} = -1
  -- So (-(Aᵀ)_{ij}).toNat = (-(-1)).toNat = 1
  have hCM : (-(t.cartanMatrix.transpose i j)).toNat = 1 := by
    rw [Matrix.transpose_apply, hA]
    simp
  rw [hCM] at hserre
  -- (ad e_i)^1(⁅e_i, e_j⁆) = ⁅e_i, ⁅e_i, e_j⁆⁆
  simpa using hserre

/-- Symmetric version: for `A_{ij} = -1`, the bracket `⁅e_j, ⁅e_j, e_i⁆⁆` vanishes.
By antisymmetry of the bracket, this is `⁅e_j, ⁅e_i, e_j⁆⁆ = 0` up to sign, the other
Heisenberg centrality needed for the length-one commutator formula. -/
theorem lie_lieBasis_e_e_e_of_cartan_eq_neg_one' (i j : Fin t.rank)
    (hA : t.cartanMatrix i j = -1) :
    ⁅(t.lieBasis ht).e j, ⁅(t.lieBasis ht).e j, (t.lieBasis ht).e i⁆⁆ = 0 :=
  t.lie_lieBasis_e_e_e_of_cartan_eq_neg_one ht j i hA

/-! ## Exponential inverse -/

/-- Scalar coefficient of the uniform exponential: `w^k / k!` in `R`. -/
private noncomputable def expCoeff (R : Type*) [CommRing R] [Algebra ℚ R] (k : ℕ) (w : R) : R :=
  w ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹

/-- The convolution of exponential coefficients is binomial:
`∑_{k ≤ n} (u^k/k!) (v^{n-k}/(n-k)!) = (u+v)^n / n!`. -/
private theorem expCoeff_binomial (R : Type*) [CommRing R] [Algebra ℚ R]
    (n : ℕ) (u v : R) :
    ∑ k ∈ Finset.range (n+1), expCoeff R k u * expCoeff R (n-k) v
      = algebraMap ℚ R ((n.factorial : ℚ))⁻¹ * (u + v) ^ n := by
  unfold expCoeff
  have hterm : ∀ k ∈ Finset.range (n+1),
      (u ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹) *
        (v ^ (n-k) * algebraMap ℚ R (((n-k).factorial : ℚ))⁻¹)
      = algebraMap ℚ R ((n.factorial : ℚ))⁻¹ *
          ((n.choose k : R) * (u ^ k * v ^ (n-k))) := by
    intro k hk
    have hkn : k ≤ n := by simpa using hk
    have hk0 : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hnk0 : (((n-k).factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-k)
    have hn0 : ((n.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hfact : ((k.factorial : ℚ))⁻¹ * (((n-k).factorial : ℚ))⁻¹
        = ((n.factorial : ℚ))⁻¹ * (n.choose k : ℚ) := by
      have hchoose : (n.choose k : ℚ) * (k.factorial : ℚ) * (((n-k).factorial : ℚ))
          = (n.factorial : ℚ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
      have hk0 : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      have hnk0 : (((n-k).factorial : ℚ)) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n-k)
      have hn0 : ((n.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      rw [← mul_inv]
      have h1 : ((k.factorial:ℚ) * (((n-k).factorial:ℚ)))⁻¹ * (n.factorial:ℚ)
          = (n.choose k:ℚ) := by
        have hkk : ((k.factorial:ℚ) * (((n-k).factorial:ℚ))) ≠ 0 :=
          mul_ne_zero hk0 hnk0
        field_simp
        calc (n.factorial:ℚ)
            = (n.choose k:ℚ) * (k.factorial:ℚ) * (((n-k).factorial:ℚ)) := hchoose.symm
          _ = (k.factorial:ℚ) * (((n-k).factorial:ℚ)) * (n.choose k:ℚ) := by ring
      conv_rhs => rw [← h1]
      rw [mul_comm ((n.factorial:ℚ))⁻¹ _, mul_assoc, mul_inv_cancel₀ hn0, mul_one]
    calc (u ^ k * algebraMap ℚ R ((k.factorial : ℚ))⁻¹) *
            (v ^ (n-k) * algebraMap ℚ R (((n-k).factorial : ℚ))⁻¹)
        = (u ^ k * v ^ (n-k)) *
            (algebraMap ℚ R ((k.factorial : ℚ))⁻¹ *
              algebraMap ℚ R (((n-k).factorial : ℚ))⁻¹) := by ring
      _ = (u ^ k * v ^ (n-k)) *
            algebraMap ℚ R (((k.factorial : ℚ))⁻¹ * (((n-k).factorial : ℚ))⁻¹) := by
          rw [map_mul]
      _ = (u ^ k * v ^ (n-k)) *
            algebraMap ℚ R (((n.factorial : ℚ))⁻¹ * (n.choose k : ℚ)) := by rw [hfact]
      _ = (u ^ k * v ^ (n-k)) *
            (algebraMap ℚ R ((n.factorial : ℚ))⁻¹ * ((n.choose k : R))) := by
          rw [map_mul, map_natCast]
      _ = algebraMap ℚ R ((n.factorial : ℚ))⁻¹ *
            ((n.choose k : R) * (u ^ k * v ^ (n-k))) := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hsum : ∑ k ∈ Finset.range (n+1), (n.choose k : R) * (u ^ k * v ^ (n-k))
      = (u + v) ^ n := by
    have h := add_pow u v n
    rw [h]
    apply Finset.sum_congr rfl
    intro k _
    ring
  exact hsum

/-- A double sum over a square regroups as a sum over antidiagonal fibers. -/
private theorem double_sum_fiber (m : Type*) (R : Type*) [CommRing R]
    (N : ℕ) (F : ℕ × ℕ → Matrix m m R) :
    (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, F (k, l))
    = ∑ n ∈ Finset.range (2*N),
        ∑ p ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 + p.2 = n),
          F p := by
  have hmaps : ∀ p ∈ (Finset.range N) ×ˢ (Finset.range N),
      p.1 + p.2 ∈ Finset.range (2*N) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  rw [← Finset.sum_product, ← Finset.sum_fiberwise_of_maps_to hmaps]

/-- Abstract exponential inverse: for `E'^N = 0`, the truncated exponential sums multiply
to 1 when the parameters negate. -/
private theorem exp_mul_exp_neg_aux (m : Type*) [DecidableEq m] [Fintype m]
    (R : Type*) [CommRing R] [Algebra ℚ R]
    (N : ℕ) (hN : 0 < N) (E' : Matrix m m R)
    (hE' : E' ^ N = 0) (u : R) :
    (∑ k ∈ Finset.range N, (expCoeff R k u) • E'^k)
      * (∑ l ∈ Finset.range N, (expCoeff R l (-u)) • E'^l) = 1 := by
  rw [Finset.sum_mul_sum]
  have hterm : ∀ k ∈ Finset.range N, ∀ l ∈ Finset.range N,
      ((expCoeff R k u) • E'^k) * ((expCoeff R l (-u)) • E'^l)
      = ((expCoeff R k u) * (expCoeff R l (-u))) • E'^(k+l) := by
    intro k _ l _
    rw [smul_mul_assoc, mul_smul_comm, ← mul_smul, pow_add]
  rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => hterm k hk l hl))]
  rw [double_sum_fiber m R N
    (fun p => ((expCoeff R p.1 u) * (expCoeff R p.2 (-u))) • E'^(p.1+p.2))]
  have hfib : ∀ n ∈ Finset.range (2*N),
      (∑ p ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 + p.2 = n),
        ((expCoeff R p.1 u) * (expCoeff R p.2 (-u))) • E'^(p.1+p.2))
      = if n = 0 then 1 else 0 := by
    intro n hn
    simp only [Finset.mem_range] at hn
    by_cases hn0 : n = 0
    · subst hn0
      have hfilter : ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 + p.2 = 0)
          = {(0, 0)} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_singleton, Prod.ext_iff]
        constructor
        · intro h
          obtain ⟨⟨h1, h2⟩, h3⟩ := h
          have hp1 : p.1 = 0 := by omega
          have hp2 : p.2 = 0 := by omega
          exact ⟨hp1, hp2⟩
        · intro h
          obtain ⟨hp1, hp2⟩ := h
          rw [hp1, hp2]
          exact ⟨⟨hN, hN⟩, rfl⟩
      rw [hfilter]
      simp [expCoeff]
    · simp only [hn0, ite_false]
      by_cases hnN : n < N
      · have hfilter : ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 + p.2 = n)
            = Finset.antidiagonal n := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            Finset.mem_antidiagonal]
          constructor
          · intro h
            exact h.2
          · intro h
            have hp1 : p.1 < N := by omega
            have hp2 : p.2 < N := by omega
            exact ⟨⟨hp1, hp2⟩, h⟩
        rw [hfilter]
        have hpull : ∀ p ∈ Finset.antidiagonal n,
            ((expCoeff R p.1 u) * (expCoeff R p.2 (-u))) • E'^(p.1+p.2)
            = ((expCoeff R p.1 u) * (expCoeff R p.2 (-u))) • E'^n := by
          intro p hp
          rw [Finset.mem_antidiagonal.mp hp]
        rw [Finset.sum_congr rfl hpull, ← Finset.sum_smul]
        have hscalar : ∑ p ∈ Finset.antidiagonal n,
            (expCoeff R p.1 u) * (expCoeff R p.2 (-u)) = 0 := by
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => (expCoeff R a u) * (expCoeff R b (-u))) n]
          rw [expCoeff_binomial R n u (-u)]
          simp [hn0]
        rw [hscalar, zero_smul]
      · have hnN' : N ≤ n := Nat.le_of_not_lt hnN
        have hpow : E'^n = 0 := by
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnN'
          rw [pow_add, hE', zero_mul]
        have hpull : ∀ p ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter
            (fun p => p.1 + p.2 = n),
            ((expCoeff R p.1 u) * (expCoeff R p.2 (-u))) • E'^(p.1+p.2)
            = ((expCoeff R p.1 u) * (expCoeff R p.2 (-u))) • (0 : Matrix _ _ R) := by
          intro p hp
          have hpn : p.1 + p.2 = n := by
            simpa using (Finset.mem_filter.mp hp).2
          rw [hpn, hpow]
        rw [Finset.sum_congr rfl hpull]
        simp
  rw [Finset.sum_congr rfl hfib]
  have h0mem : (0:ℕ) ∈ Finset.range (2*N) := by simp; omega
  rw [Finset.sum_ite_eq' _ 0]
  simp [h0mem]

/-- The uniform exponential is inverted by negating the parameter:
`exp(u • e_i) * exp(-u • e_i) = 1`. The product expands as a double sum; collecting
terms by total degree, the binomial theorem kills all positive-degree terms with
`n < N` (giving `(u - u)^n = 0`), while terms with `n ≥ N` vanish by the sharp
nilpotency bound `E^N = 0`. -/
theorem pinnedExp_mul_pinnedExp_neg (R : Type*) [CommRing R] [Algebra ℚ R]
    (i : Fin t.rank) (u : R) :
    t.pinnedExp ht R i u * t.pinnedExp ht R i (-u) = 1 := by
  have hNpos : 0 < Fintype.card (t.GeckIndex ht) := by
    have hpos : 0 < t.numRoots := t.numRoots_pos ht
    have hcard : Fintype.card (t.GeckIndex ht)
        = Fintype.card (t.rationalBase ht).support + t.numRoots := by
      simp [GeckIndex, Fintype.card_sum]
    omega
  set E' : Matrix (t.GeckIndex ht) (t.GeckIndex ht) R :=
    ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ).map
      (algebraMap ℚ R) with hE'def
  have hE'N : E' ^ Fintype.card (t.GeckIndex ht) = 0 := by
    rw [hE'def, ← Matrix.map_pow,
      Matrix.IsNilpotent.pow_card_eq_zero (t.isNilpotent_coe_lieBasis_e ht i)]
    simp
  have hident : ∀ (w : R), t.pinnedExp ht R i w
      = ∑ k ∈ Finset.range (Fintype.card (t.GeckIndex ht)),
          (expCoeff R k w) • E'^k := by
    intro w
    unfold pinnedExp expCoeff
    apply Finset.sum_congr rfl
    intro k _
    rw [hE'def, ← Matrix.map_pow]
  rw [hident u, hident (-u)]
  exact exp_mul_exp_neg_aux (t.GeckIndex ht) R _ hNpos E' hE'N u

/-- The exponential coefficient satisfies `c_k(u) * k = u * c_{k-1}(u)` for `k ≥ 1`.
This is `u^k/k! * k = u * u^(k-1)/(k-1)!`, using `k! = k * (k-1)!`. -/
private theorem expCoeff_mul_nat (R : Type*) [CommRing R] [Algebra ℚ R]
    (k : ℕ) (hk : 1 ≤ k) (u : R) :
    (expCoeff R k u) * (k : R) = u * (expCoeff R (k - 1) u) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold expCoeff
  have hpow : u ^ (m + 1) = u * u ^ m := pow_succ' u m
  rw [hpow]
  have h2 : ((m + 1).factorial : ℚ)⁻¹ * ((m + 1 : ℕ) : ℚ) = (m.factorial : ℚ)⁻¹ := by
    have hm1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
    have hfact : ((m + 1).factorial : ℚ) = ((m + 1 : ℕ) : ℚ) * (m.factorial : ℚ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    rw [hfact, mul_inv]
    calc ((m + 1 : ℕ) : ℚ)⁻¹ * (m.factorial : ℚ)⁻¹ * ((m + 1 : ℕ) : ℚ)
        = (m.factorial : ℚ)⁻¹ * (((m + 1 : ℕ) : ℚ)⁻¹ * ((m + 1 : ℕ) : ℚ)) := by ring
      _ = (m.factorial : ℚ)⁻¹ * 1 := by
          congr 1
          exact inv_mul_cancel₀ hm1
      _ = (m.factorial : ℚ)⁻¹ := by rw [mul_one]
  have h1 : (algebraMap ℚ R (((m + 1).factorial : ℚ)⁻¹)) * (((m + 1 : ℕ)) : R)
      = algebraMap ℚ R ((m.factorial : ℚ)⁻¹) := by
    rw [← map_natCast (algebraMap ℚ R) (m + 1), ← map_mul, h2]
  calc ((u * u ^ m) * (algebraMap ℚ R (((m + 1).factorial : ℚ)⁻¹))) * (((m + 1 : ℕ)) : R)
      = (u * u ^ m) * ((algebraMap ℚ R (((m + 1).factorial : ℚ)⁻¹)) * (((m + 1 : ℕ)) : R)) := by
          ring
    _ = (u * u ^ m) * (algebraMap ℚ R ((m.factorial : ℚ)⁻¹)) := by rw [h1]
    _ = u * (u ^ m * (algebraMap ℚ R ((m.factorial : ℚ)⁻¹))) := by ring

/-! ## Exponential conjugation (Heisenberg case) -/

/-- Moving a power of `X` past `Y` in the Heisenberg case:
`X^k * Y = Y * X^k + k • ([X,Y] * X^(k-1))`.
By induction on `k`, using that `[X, [X,Y]] = 0` (so `X` commutes with `[X,Y]`). -/
private theorem move_past_pow {n : Type*} [Fintype n] [DecidableEq n]
    (R : Type*) [CommRing R]
    (X Y : Matrix n n R)
    (hdouble : X * (X * Y - Y * X) = (X * Y - Y * X) * X)
    (k : ℕ) :
    X ^ k * Y = Y * X ^ k + (k : R) • ((X * Y - Y * X) * X ^ (k - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    set C := X * Y - Y * X with hCdef
    have hXY : X * Y = Y * X + C := by rw [hCdef]; abel
    have hXpow : (k : R) • (C * (X * X ^ (k - 1))) = (k : R) • (C * X ^ k) := by
      by_cases hk : k = 0
      · subst hk; simp
      · congr 1
        congr 1
        have hkk : k - 1 + 1 = k := by omega
        calc X * X ^ (k - 1) = X ^ ((k - 1) + 1) := (pow_succ' X (k - 1)).symm
          _ = X ^ k := by rw [hkk]
    have hY : Y * X * X ^ k = Y * X ^ (k + 1) := by
      rw [mul_assoc, ← pow_succ']
    -- Main computation
    calc X ^ (k + 1) * Y
        = X * (X ^ k * Y) := by rw [pow_succ', mul_assoc]
      _ = X * (Y * X ^ k + (k : R) • (C * X ^ (k - 1))) := by rw [ih]
      _ = X * (Y * X ^ k) + X * ((k : R) • (C * X ^ (k - 1))) := by rw [mul_add]
      _ = (X * Y) * X ^ k + (k : R) • (X * (C * X ^ (k - 1))) := by
          rw [← mul_assoc X Y (X ^ k), mul_smul_comm]
      _ = (Y * X + C) * X ^ k + (k : R) • ((X * C) * X ^ (k - 1)) := by
          rw [hXY, ← mul_assoc X C (X ^ (k - 1))]
      _ = (Y * X + C) * X ^ k + (k : R) • ((C * X) * X ^ (k - 1)) := by rw [hdouble]
      _ = Y * X * X ^ k + C * X ^ k + (k : R) • (C * X ^ k) := by
          rw [add_mul, mul_assoc C X (X ^ (k - 1)), hXpow]
      _ = Y * X ^ (k + 1) + C * X ^ k + (k : R) • (C * X ^ k) := by rw [hY]
      _ = Y * X ^ (k + 1) + ((k + 1 : ℕ) : R) • (C * X ^ k) := by
          have h2 : C * X ^ k + (k : R) • (C * X ^ k)
              = ((k + 1 : ℕ) : R) • (C * X ^ k) := by
            nth_rewrite 1 [← one_smul R (C * X ^ k)]
            rw [← add_smul]
            congr 1
            push_cast
            ring
          rw [add_assoc (Y * X ^ (k + 1)) (C * X ^ k) ((k : R) • (C * X ^ k)), h2]
      _ = Y * X ^ (k + 1) + ((k + 1 : ℕ) : R) • (C * X ^ ((k + 1) - 1)) := by
          rw [Nat.add_sub_cancel]

end

end TauCeti.DynkinType
