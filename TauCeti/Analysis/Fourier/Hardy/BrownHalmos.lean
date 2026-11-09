/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Toeplitz
public import TauCeti.Analysis.Fourier.LaurentOperator

/-!
# The Brown–Halmos characterization of Toeplitz operators

The forward shift on boundary Hardy space is the Toeplitz operator `S = T_z` of the Fourier
monomial `z = e₁`; it sends the Hardy basis vector `eₙ` to `eₙ₊₁`. A bounded operator `T` on
`H²` is a Toeplitz operator `T_a` for an essentially bounded symbol `a` exactly when its matrix
in the Hardy basis is constant along diagonals, that is, exactly when `S† T S = T`; the symbol
is then unique. This is the theorem of Brown and Halmos, and it is the way an abstractly given
operator is recognized as a Toeplitz operator.

* `TauCeti.exists_toeplitz_eq_iff_inner_hardyBasis_succ`: `T` is a Toeplitz operator if and
  only if `⟪e_{i+1}, T e_{j+1}⟫ = ⟪e_i, T e_j⟫` for all `i, j`.
* `TauCeti.existsUnique_toeplitz_eq_iff_adjoint_comp_comp_eq`: **Brown–Halmos.** `T = T_a` for a
  unique essentially bounded symbol `a` if and only if `S† T S = T`.

For the converse direction, write `c_{i-j} = ⟪e_i, T e_j⟫`. The circle function
`b = T e₀ + conj (T† e₀) - c₀`, built from the first column and the first row of the matrix, has
Fourier coefficients `b̂(k) = c_k` for every `k ∈ ℤ`. For trigonometric polynomials `f` and `q`,
multiplying both by a sufficiently high Fourier mode `e_N` moves them into `H²`, and then
`⟪f, b q⟫ = ⟪e_N f, T (e_N q)⟫`, so `‖b q‖₂ ≤ ‖T‖ ‖q‖₂`. The multiplier criterion
`TauCeti.eLpNorm_top_le_of_forall_mem_span_fourier` therefore makes `b` essentially bounded, and
`T_b` has the same matrix as `T`.

## References

* A. Brown and P. R. Halmos, *Algebraic properties of Toeplitz operators*, J. Reine Angew. Math.
  213 (1964), 89–102, Theorem 6.
* A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators*, second edition, §2.
-/

public section

noncomputable section

open MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- Along each diagonal, a Hardy matrix invariant under the shift `(i, j) ↦ (i + 1, j + 1)` is
invariant under every translation `(i, j) ↦ (i + k, j + k)`. -/
private theorem inner_hardyBasis_add_eq {T : HardySpace →L[ℂ] HardySpace}
    (h : ∀ i j : ℕ, ⟪hardyBasis (i + 1), T (hardyBasis (j + 1))⟫_ℂ =
      ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ) (i j k : ℕ) :
    ⟪hardyBasis (i + k), T (hardyBasis (j + k))⟫_ℂ = ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← add_assoc, ← add_assoc, h, ih]

/-- A Hardy matrix that is constant along diagonals is the matrix of Fourier coefficients
`b̂(i - j)` of a square-integrable circle function `b`, namely
`b = T e₀ + conj (T† e₀) - ⟪e₀, T e₀⟫`. -/
private theorem exists_fourierCoeff_eq_inner {T : HardySpace →L[ℂ] HardySpace}
    (h : ∀ i j : ℕ, ⟪hardyBasis (i + 1), T (hardyBasis (j + 1))⟫_ℂ =
      ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ) :
    ∃ b : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)), ∀ i j : ℕ,
      fourierCoeff b ((i : ℤ) - j) = ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ := by
  set c := ⟪hardyBasis 0, T (hardyBasis 0)⟫_ℂ
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
    (T (hardyBasis 0) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) +
      star (ContinuousLinearMap.adjoint T (hardyBasis 0) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) - c • fourierBasis 0
  -- The Fourier coefficients of the three summands, through the linear Fourier representation.
  have hb (k : ℤ) : fourierCoeff b k =
      fourierCoeff (T (hardyBasis 0) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) k +
        fourierCoeff (star (ContinuousLinearMap.adjoint T (hardyBasis 0) :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))
          k - c * fourierCoeff (fourierBasis (T := 1) 0) k := by
    simp only [b, ← fourierBasis_repr, map_sub, map_add, map_smul]
    rfl
  -- The first column of `T` and the conjugated first column of `T†`, the first row of `T`.
  have hT (d : ℕ) : fourierCoeff (T (hardyBasis 0) : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))
      d = ⟪hardyBasis d, T (hardyBasis 0)⟫_ℂ := by
    rw [← hardyBasis_repr, HilbertBasis.repr_apply_apply]
  have hA (d : ℕ) : starRingEnd ℂ (fourierCoeff (ContinuousLinearMap.adjoint T (hardyBasis 0) :
      Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) d) = ⟪hardyBasis 0, T (hardyBasis d)⟫_ℂ := by
    rw [← hardyBasis_repr, HilbertBasis.repr_apply_apply, inner_conj_symm,
      ContinuousLinearMap.adjoint_inner_left]
  -- Off the diagonal one summand vanishes; on it, the correction `c` cancels the double count.
  have hcol (d : ℕ) : fourierCoeff b d = ⟪hardyBasis d, T (hardyBasis 0)⟫_ℂ := by
    rw [hb, fourierCoeff_star, coe_fourierBasis, fourierCoeff_fourierLp, hT]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa [c] using hA 0
    · simp [HardySpace.fourierCoeff_eq_zero _ (by omega : -(d : ℤ) < 0), hd.ne']
  have hrow (d : ℕ) : fourierCoeff b (-d) = ⟪hardyBasis 0, T (hardyBasis d)⟫_ℂ := by
    rw [hb, fourierCoeff_star, coe_fourierBasis, fourierCoeff_fourierLp, neg_neg, hA]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simpa [c] using hT 0
    · simp [HardySpace.fourierCoeff_eq_zero _ (by omega : -(d : ℤ) < 0), hd.ne']
  refine ⟨b, fun i j ↦ ?_⟩
  rcases le_total j i with hji | hij
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
    have hd : ((j + d : ℕ) : ℤ) - j = d := by omega
    rw [hd, hcol, ← inner_hardyBasis_add_eq h d 0 j, add_comm, zero_add]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hd : (i : ℤ) - ((i + d : ℕ) : ℤ) = -d := by omega
    rw [hd, hrow, ← inner_hardyBasis_add_eq h 0 d i, zero_add, add_comm]

/-- The operator `T` acting on circle `L²` through the Hardy projection. -/
private abbrev ambient (T : HardySpace →L[ℂ] HardySpace) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) →L[ℂ] Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
  hardySubmodule.subtypeL ∘L T ∘L hardySubmodule.orthogonalProjectionOnto

/-- On the Hardy basis, `T` acting through the Hardy projection is `T` itself. -/
private theorem ambient_coe_hardyBasis (T : HardySpace →L[ℂ] HardySpace) (j : ℕ) :
    ambient T (hardyBasis j) = T (hardyBasis j) := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    orthogonalProjectionOnto_mem_subspace_eq_self, subtypeL_apply]

/-- For trigonometric polynomials `f` and `q`, the matrix coefficient of multiplication by a
symbol `b` of the shift-invariant Hardy matrix of `T` is the matrix coefficient of `T` at the
translates `e_N f` and `e_N q`, for all sufficiently large `N`. -/
private theorem eventually_inner_multiplicationOperator_eq {T : HardySpace →L[ℂ] HardySpace}
    {b : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))}
    (hb : ∀ i j : ℕ, fourierCoeff b ((i : ℤ) - j) = ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ)
    {f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))}
    (hf : f ∈ span ℂ (Set.range (fourierBasis (T := 1))))
    {q : C(UnitAddCircle, ℂ)} (hq : q ∈ span ℂ (Set.range (fourier (T := 1)))) :
    ∀ᶠ N : ℤ in Filter.atTop,
      ⟪f, Lp.multiplicationOperator (ContinuousMap.toLp (E := ℂ) ∞ AddCircle.haarAddCircle ℂ q)
        b⟫_ℂ =
      ⟪Lp.multiplicationOperator (fourierLp (T := 1) ∞ N) f,
        ambient T (Lp.multiplicationOperator (fourierLp (T := 1) ∞ N)
          (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ q))⟫_ℂ := by
  induction hq using span_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    induction hf using span_induction with
    | mem f hf =>
      obtain ⟨m, rfl⟩ := hf
      filter_upwards [Filter.eventually_ge_atTop (-m), Filter.eventually_ge_atTop (-n)]
        with N hm hn
      obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ N + m)
      obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ N + n)
      have hq₂ : ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ (fourier n) =
          fourierBasis (T := 1) n := by
        rw [coe_fourierBasis]
      -- Both sides are the matrix entry `b̂(m - n) = ⟪e_{N+m}, T e_{N+n}⟫`.
      -- `ContinuousMap.toLp ∞` of `fourier n` is the abbreviation `fourierLp ∞ n`.
      rw [hq₂, inner_fourierBasis_multiplicationOperator_fourierLp]
      simp only [Lp.multiplicationOperator_apply, fourierLp_smul_fourierBasis]
      rw [hi, hj, ← coe_hardyBasis, ← coe_hardyBasis, ambient_coe_hardyBasis, ← coe_inner, ← hb]
      congr 1
      omega
    | zero => exact Filter.Eventually.of_forall fun N ↦ by simp
    | add f g _ _ hf hg =>
      filter_upwards [hf, hg] with N hf hg
      rw [map_add, inner_add_left, inner_add_left, hf, hg]
    | smul c f _ hf =>
      filter_upwards [hf] with N hf
      rw [map_smul, inner_smul_left, inner_smul_left, hf]
  | zero => exact Filter.Eventually.of_forall fun N ↦ by simp
  | add q r _ _ hq hr =>
    filter_upwards [hq, hr] with N hq hr
    rw [map_add, Lp.multiplicationOperator_add, FunLike.coe_add, Pi.add_apply,
      inner_add_right,
      hq, hr, map_add, map_add, map_add, inner_add_right]
  | smul c q _ hq =>
    filter_upwards [hq] with N hq
    rw [map_smul, Lp.multiplicationOperator_smul, FunLike.coe_smul, Pi.smul_apply,
      inner_smul_right,
      hq, map_smul, map_smul, map_smul, inner_smul_right]

/-- Multiplication by a symbol `b` of the shift-invariant Hardy matrix of `T` is bounded by `‖T‖`
on trigonometric polynomials. -/
private theorem norm_multiplicationOperator_toLp_apply_le {T : HardySpace →L[ℂ] HardySpace}
    {b : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))}
    (hb : ∀ i j : ℕ, fourierCoeff b ((i : ℤ) - j) = ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ)
    {q : C(UnitAddCircle, ℂ)} (hq : q ∈ span ℂ (Set.range (fourier (T := 1)))) :
    ‖Lp.multiplicationOperator (ContinuousMap.toLp (E := ℂ) ∞ AddCircle.haarAddCircle ℂ q) b‖ ≤
      ‖T‖ * ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ q‖ := by
  set v := Lp.multiplicationOperator (ContinuousMap.toLp (E := ℂ) ∞ AddCircle.haarAddCircle ℂ q) b
  set C := ‖T‖ * ‖ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ q‖
  have hU (N : ℤ) (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
      ‖Lp.multiplicationOperator (fourierLp (T := 1) ∞ N) g‖ = ‖g‖ :=
    Lp.norm_multiplicationOperator_apply_of_ae_norm_eq_one (ae_norm_fourierLp_eq_one ∞ N) g
  have hT : ‖ambient T‖ ≤ ‖T‖ := by
    calc ‖ambient T‖ ≤ ‖hardySubmodule.subtypeL‖ *
          (‖T‖ * ‖hardySubmodule.orthogonalProjectionOnto‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖T‖ * 1) := by
          gcongr
          · exact Submodule.norm_subtypeL_le _
          · exact hardySubmodule.orthogonalProjectionOnto_norm_le
      _ = ‖T‖ := by ring
  have hD : Dense (span ℂ (Set.range (fourierBasis (T := 1))) :
      Set (Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) :=
    dense_iff_topologicalClosure_eq_top.2 (fourierBasis (T := 1)).dense_span
  -- The functional `⟪·, v⟫` is bounded by `C` on trigonometric polynomials, hence everywhere.
  have hbound : ∀ f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)), ‖⟪f, v⟫_ℂ‖ ≤ C * ‖f‖ := by
    refine hD.induction (fun f hf ↦ ?_) (isClosed_le (by fun_prop) (by fun_prop))
    obtain ⟨N, hN⟩ := (eventually_inner_multiplicationOperator_eq hb hf hq).exists
    rw [hN]
    calc _ ≤ ‖Lp.multiplicationOperator (fourierLp (T := 1) ∞ N) f‖ *
          (‖ambient T‖ * ‖Lp.multiplicationOperator (fourierLp (T := 1) ∞ N)
            (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ q)‖) :=
          (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ ‖f‖ * C := by
          rw [hU, hU]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
            (norm_nonneg _)
      _ = C * ‖f‖ := mul_comm _ _
  have hv := hbound v
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq] at hv
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_right hv hpos

/-- An operator on Hardy space whose matrix in the Hardy basis is constant along diagonals is a
Toeplitz operator: there is an essentially bounded symbol `a` with `T = T_a`. -/
private theorem exists_toeplitz_eq_of_inner_hardyBasis_succ {T : HardySpace →L[ℂ] HardySpace}
    (h : ∀ i j : ℕ, ⟪hardyBasis (i + 1), T (hardyBasis (j + 1))⟫_ℂ =
      ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ) :
    ∃ a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)), toeplitz a = T := by
  obtain ⟨b, hb⟩ := exists_fourierCoeff_eq_inner h
  -- The multiplier criterion makes `b` essentially bounded by `‖T‖`.
  have hbT : eLpNorm (⇑b) ∞ AddCircle.haarAddCircle ≤ ‖T‖ₑ := by
    refine eLpNorm_top_le_of_forall_mem_span_fourier (p := 2) ENNReal.ofNat_ne_top
      (Lp.aestronglyMeasurable b) fun q hq ↦ ?_
    have hae : ⇑(Lp.multiplicationOperator
        (ContinuousMap.toLp (E := ℂ) ∞ AddCircle.haarAddCircle ℂ q) b) =ᵐ[AddCircle.haarAddCircle]
          ⇑b * ⇑q := by
      filter_upwards [Lp.multiplicationOperator_ae
          (ContinuousMap.toLp (E := ℂ) ∞ AddCircle.haarAddCircle ℂ q) b,
        ContinuousMap.coeFn_toLp (E := ℂ) (p := ∞) (𝕜 := ℂ) AddCircle.haarAddCircle q]
        with x hx hqx
      rw [hx, hqx, Pi.mul_apply, smul_eq_mul, mul_comm]
    rw [← eLpNorm_congr_ae hae, ← Lp.enorm_def,
      ← eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
        AddCircle.haarAddCircle q), ← Lp.enorm_def, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_multiplicationOperator_toLp_apply_le hb hq)
  have hb_mem : MemLp (⇑b) ∞ AddCircle.haarAddCircle :=
    memLp_iff.2 (hbT.trans_lt enorm_lt_top)
  refine ⟨hb_mem.toLp b, HilbertBasis.ext_inner_apply hardyBasis hardyBasis fun i j ↦ ?_⟩
  rw [inner_hardyBasis_toeplitz_hardyBasis, fourierCoeff_congr_ae hb_mem.coeFn_toLp, hb]

/-- An operator on Hardy space is a Toeplitz operator `T_a` for an essentially bounded symbol `a`
if and only if its matrix in the Hardy basis is constant along diagonals. -/
theorem exists_toeplitz_eq_iff_inner_hardyBasis_succ (T : HardySpace →L[ℂ] HardySpace) :
    (∃ a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)), toeplitz a = T) ↔
      ∀ i j : ℕ, ⟪hardyBasis (i + 1), T (hardyBasis (j + 1))⟫_ℂ =
        ⟪hardyBasis i, T (hardyBasis j)⟫_ℂ := by
  refine ⟨?_, exists_toeplitz_eq_of_inner_hardyBasis_succ⟩
  rintro ⟨a, rfl⟩ i j
  rw [inner_hardyBasis_toeplitz_hardyBasis, inner_hardyBasis_toeplitz_hardyBasis]
  congr 1
  push_cast
  ring

/-- **Brown–Halmos theorem.** A bounded operator `T` on Hardy space is a Toeplitz operator `T_a`
for a unique essentially bounded symbol `a` if and only if `S† T S = T`, where `S = T_z` is the
forward shift. -/
theorem existsUnique_toeplitz_eq_iff_adjoint_comp_comp_eq (T : HardySpace →L[ℂ] HardySpace) :
    (∃! a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)), toeplitz a = T) ↔
      ContinuousLinearMap.adjoint (toeplitz (fourierLp (T := 1) ∞ 1)) ∘L T ∘L
        toeplitz (fourierLp (T := 1) ∞ 1) = T := by
  have hshift (i j : ℕ) : ⟪hardyBasis i, (ContinuousLinearMap.adjoint
      (toeplitz (fourierLp (T := 1) ∞ 1)) ∘L T ∘L toeplitz (fourierLp (T := 1) ∞ 1))
        (hardyBasis j)⟫_ℂ = ⟪hardyBasis (i + 1), T (hardyBasis (j + 1))⟫_ℂ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, toeplitz_fourierLp_one_hardyBasis,
      toeplitz_fourierLp_one_hardyBasis]
  have hexists : (∃ a, toeplitz a = T) ↔ ContinuousLinearMap.adjoint
      (toeplitz (fourierLp (T := 1) ∞ 1)) ∘L T ∘L toeplitz (fourierLp (T := 1) ∞ 1) = T := by
    rw [exists_toeplitz_eq_iff_inner_hardyBasis_succ]
    refine ⟨fun h ↦ HilbertBasis.ext_inner_apply hardyBasis hardyBasis fun i j ↦ ?_,
      fun h i j ↦ ?_⟩
    · rw [hshift, h]
    · rw [← hshift, h]
  refine ⟨fun ⟨a, ha, _⟩ ↦ hexists.1 ⟨a, ha⟩, fun h ↦ ?_⟩
  obtain ⟨a, ha⟩ := hexists.2 h
  exact ⟨a, ha, fun a' ha' ↦ toeplitz_injective (ha'.trans ha.symm)⟩

end TauCeti
