/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SuccessiveMinima
import TauCeti.LinearAlgebra.Dual.AbsoluteValue
import TauCeti.NumberTheory.Height.FundamentalInequality

/-!
# Successive minima of an approximation domain

Let `K` be a number field of degree `d`, and let `μ l` be the successive minima over `K` of the
approximation domain `TauCeti.NumberField.approxDomain S₀ L c Q`, that is, of the lattice
`approxModule S₀ L c Q` with respect to the body `approxBody L c Q`. The product of their `d`-th
powers is `Q ^ (-approxWeight S₀ c)` up to two constants that do not depend on `Q` or on the
exponents `c`:

```text
2 ^ N / (N! · c_K ^ N · C) · Q ^ (-w)  ≤  ∏ l, μ l ^ d,
∏ l, μ l ^ d  ≤  2 ^ N · (∏ v ∈ S₀, N 𝔭_v ^ n) / C · Q ^ (-w),
```

where `n = card ι`, `N = d n`, `w = approxWeight S₀ c`, `C = approxConst S₀ L` and
`c_K = integralBasisHouse K`. Taking `d`-th roots, the product of the minima themselves is
`Q ^ (-approxWeight S₀ c / d)` up to constants.

Both bounds combine Minkowski's second theorem over `K` with the comparison of the volume of the
body with the covolume of the lattice. The lower bound uses the half of that comparison which
holds without rounding (`TauCeti.NumberField.volume_div_covolume_le`), so it loses nothing at the
finite places. The upper bound uses the other half, and pays the factor `∏ v ∈ S₀, N 𝔭_v ^ n`
lost when the finite-place bounds `Q ^ c v i` are rounded down to values of `v`.

These bounds are what makes the geometry of numbers of approximation domains uniform in the level
`Q`: in particular, when the weight is negative, the product of the minima grows like a positive
power of `Q`, so some minimum eventually exceeds `1`.

Each minimum separately is confined as well. Fix a bound `A` on the absolute weight
`approxAbsWeight S₀ c` and put `B = n · (A + 1) / d`. Then above a level `Q₀` that depends on `A`
but not on `c`, every minimum lies between `Q ^ (-B)` and `Q ^ B`. The lower bound is the product
formula: a nonzero point of the lattice whose embedding lies in `t • approxBody L c Q` has a
nonzero coordinate, bounded at each place in terms of the values of the forms, so
`t ^ d ≥ C · Q ^ (-approxAbsWeight S₀ c)` with `C > 0` independent of `c` and `Q`. The upper bound
on one minimum is the upper bound on the product with every other minimum replaced by this lower
bound. The uniformity in `c` is what lets exponent families that move with `Q` be treated at once.

## Main definitions

* `TauCeti.NumberField.approxLowerConst` and `TauCeti.NumberField.approxUpperConst`: the two
  constants of the displayed bounds.

## Main results

* `TauCeti.NumberField.le_prod_successiveMinimum_approx`: the lower bound on `∏ l, μ l ^ d`.
* `TauCeti.NumberField.prod_successiveMinimum_approx_le`: the upper bound on `∏ l, μ l ^ d`.
* `TauCeti.NumberField.exists_pos_forall_rpow_le_successiveMinimum`: every minimum is at least
  `Q ^ (-B)` for `Q ≥ Q₀`, uniformly in the exponents of absolute weight at most `A`.
* `TauCeti.NumberField.exists_pos_forall_rpow_le_successiveMinimum_le`: every minimum lies
  between `Q ^ (-B)` and `Q ^ B` for `Q ≥ Q₀`, uniformly in the same exponents.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Theorem C.2.11, Corollary 7.5.8 and §7.5.
* A version of these bounds is formalized in Ralf Stephan's `rwst/Subspace-Theorems`
  (Apache 2.0): the product bounds in `DiophantineApproximation/FieldMinkowski.lean`, and the
  confinement of each minimum in `DiophantineApproximation/MinimaBounds.lean`.
-/

public section

open MeasureTheory Module NumberField NumberField.mixedEmbedding

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **The constant of the lower Minkowski bound for an approximation domain**:
`2 ^ N / (N! · c_K ^ N · approxConst S₀ L)`, where `N = [K : ℚ] · card ι` and
`c_K = integralBasisHouse K` (`TauCeti.NumberField.le_prod_successiveMinimum_approx`). -/
noncomputable def approxLowerConst (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) : ℝ :=
  2 ^ (finrank ℚ K * Fintype.card ι) /
    (((finrank ℚ K * Fintype.card ι).factorial : ℝ) *
      integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) * approxConst S₀ L)

/-- **The constant of the upper Minkowski bound for an approximation domain**:
`2 ^ N · ∏ v ∈ S₀, N 𝔭_v ^ card ι / approxConst S₀ L`, where `N = [K : ℚ] · card ι`
(`TauCeti.NumberField.prod_successiveMinimum_approx_le`). -/
noncomputable def approxUpperConst (S₀ : Finset (FinitePlace K))
    (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)) : ℝ :=
  2 ^ (finrank ℚ K * Fintype.card ι) *
    (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι) / approxConst S₀ L

/-- The constant of the lower Minkowski bound is positive for forms independent at the infinite
places and at `S₀`. -/
theorem approxLowerConst_pos {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) :
    0 < approxLowerConst S₀ L :=
  div_pos (by positivity) (mul_pos (mul_pos (by positivity) (pow_pos integralBasisHouse_pos _))
    (approxConst_pos hLInf hLFin))

/-- The constant of the upper Minkowski bound is positive for forms independent at the infinite
places and at `S₀`. -/
theorem approxUpperConst_pos {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) :
    0 < approxUpperConst S₀ L :=
  div_pos (mul_pos (by positivity) (Finset.prod_pos fun v _ ↦ pow_pos (by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).pos) _))
    (approxConst_pos hLInf hLFin)

/-- **The successive minima of an approximation domain, lower bound** (Bombieri–Gubler, Theorem
C.2.11 with Corollary 7.5.8): for `0 < Q` and linearly independent forms at the infinite places and
at `S₀`, the product of the `[K : ℚ]`-th powers of the successive minima over `K` of
`approxDomain S₀ L c Q` is at least `approxLowerConst S₀ L · Q ^ (-weight)`, where
`approxLowerConst S₀ L = 2 ^ N / (N! · c_K ^ N · approxConst S₀ L)`, `N = [K : ℚ] · card ι` and
`c_K = integralBasisHouse K`. -/
theorem le_prod_successiveMinimum_approx {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    approxLowerConst S₀ L * Q ^ (-approxWeight S₀ c) ≤
      ∏ l : Fin (Fintype.card ι),
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ^ finrank ℚ K := by
  classical
  let _ := discreteTopology_mixedImage_approxModule hLFin c Q
  let _ := isZLattice_mixedImage_approxModule hLFin c hQ.ne'
  set N := finrank ℚ K * Fintype.card ι
  set P := ∏ l : Fin (Fintype.card ι),
    (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ^ finrank ℚ K
  set A : ℝ := 2 ^ N / ((N.factorial : ℝ) * integralBasisHouse K ^ N)
  set C := ZLattice.covolume (approxModule S₀ L c Q).mixedImage
  set V := volume.real (approxBody L c Q)
  have hC : 0 < C := covolume_approxLattice_pos hLFin c hQ.ne'
  have hconst : 0 < approxConst S₀ L := approxConst_pos hLInf hLFin
  have hQw : 0 < Q ^ approxWeight S₀ c := Real.rpow_pos_of_pos hQ _
  -- Minkowski's second theorem over `K`, lower bound: `A · C ≤ P · V`.
  have hmink : A * C ≤ P * V :=
    Submodule.two_pow_div_factorial_mul_covolume_le_prod_successiveMinimum_pow_mul_measureReal _
      volume (convex_approxBody L c Q) (isCompact_approxBody hLInf c Q)
      (approxBody_mem_nhds_zero L c hQ) fun _ hz _ ha ↦ mul_mem_approxBody hz ha
  -- The volume of the body is at most `approxConst S₀ L · Q ^ weight` covolumes of the lattice.
  have hV : V ≤ approxConst S₀ L * Q ^ approxWeight S₀ c * C :=
    (div_le_iff₀ hC).1 (volume_div_covolume_le hLInf hLFin c hQ)
  have hP : 0 ≤ P :=
    Finset.prod_nonneg fun _ _ ↦ pow_nonneg (Submodule.successiveMinimum_nonneg _ _ _) _
  have hA : A ≤ P * (approxConst S₀ L * Q ^ approxWeight S₀ c) := by
    refine le_of_mul_le_mul_right ?_ hC
    calc A * C ≤ P * V := hmink
      _ ≤ P * (approxConst S₀ L * Q ^ approxWeight S₀ c * C) := mul_le_mul_of_nonneg_left hV hP
      _ = P * (approxConst S₀ L * Q ^ approxWeight S₀ c) * C := by ring
  calc approxLowerConst S₀ L * Q ^ (-approxWeight S₀ c)
      = A / (approxConst S₀ L * Q ^ approxWeight S₀ c) := by
        rw [Real.rpow_neg hQ.le, approxLowerConst]
        simp only [A, N]
        ring
    _ ≤ P := (div_le_iff₀ (mul_pos hconst hQw)).2 hA

/-- **The successive minima of an approximation domain, upper bound** (Bombieri–Gubler, Theorem
C.2.11 with Corollary 7.5.8): for `0 < Q` and linearly independent forms at the infinite places and
at `S₀`, the product of the `[K : ℚ]`-th powers of the successive minima over `K` of
`approxDomain S₀ L c Q` is at most `approxUpperConst S₀ L · Q ^ (-weight)`, where
`approxUpperConst S₀ L = 2 ^ N · ∏ v ∈ S₀, N 𝔭_v ^ card ι / approxConst S₀ L` and
`N = [K : ℚ] · card ι`. -/
theorem prod_successiveMinimum_approx_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ∏ l : Fin (Fintype.card ι),
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ^ finrank ℚ K ≤
      approxUpperConst S₀ L * Q ^ (-approxWeight S₀ c) := by
  classical
  let _ := discreteTopology_mixedImage_approxModule hLFin c Q
  let _ := isZLattice_mixedImage_approxModule hLFin c hQ.ne'
  set N := finrank ℚ K * Fintype.card ι
  set P := ∏ l : Fin (Fintype.card ι),
    (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ^ finrank ℚ K
  set D := ∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι
  set C := ZLattice.covolume (approxModule S₀ L c Q).mixedImage
  set V := volume.real (approxBody L c Q)
  have hC : 0 < C := covolume_approxLattice_pos hLFin c hQ.ne'
  have hD : 0 < D := Finset.prod_pos fun v _ ↦ pow_pos (by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).pos) _
  have hk : 0 < approxConst S₀ L / D * Q ^ approxWeight S₀ c :=
    mul_pos (div_pos (approxConst_pos hLInf hLFin) hD) (Real.rpow_pos_of_pos hQ _)
  -- Minkowski's second theorem over `K`, upper bound: `P · V ≤ 2 ^ N · C`.
  have hmink : P * V ≤ 2 ^ N * C :=
    (approxModule S₀ L c Q).prod_successiveMinimum_pow_mul_measureReal_le_two_pow_mul_covolume
      volume (convex_approxBody L c Q) (isCompact_approxBody hLInf c Q)
      fun _ hz ↦ neg_mem_approxBody hz
  -- The volume of the body is at least `approxConst S₀ L / D · Q ^ weight` covolumes.
  have hV : approxConst S₀ L / D * Q ^ approxWeight S₀ c * C ≤ V :=
    (le_div_iff₀ hC).1 (le_volume_div_covolume hLInf hLFin c hQ)
  have hP : 0 ≤ P :=
    Finset.prod_nonneg fun _ _ ↦ pow_nonneg (Submodule.successiveMinimum_nonneg _ _ _) _
  have hPk : P * (approxConst S₀ L / D * Q ^ approxWeight S₀ c) ≤ 2 ^ N := by
    refine le_of_mul_le_mul_right ?_ hC
    calc P * (approxConst S₀ L / D * Q ^ approxWeight S₀ c) * C
        = P * (approxConst S₀ L / D * Q ^ approxWeight S₀ c * C) := by ring
      _ ≤ P * V := mul_le_mul_of_nonneg_left hV hP
      _ ≤ 2 ^ N * C := hmink
  calc P ≤ 2 ^ N / (approxConst S₀ L / D * Q ^ approxWeight S₀ c) := (le_div_iff₀ hk).2 hPk
    _ = approxUpperConst S₀ L * Q ^ (-approxWeight S₀ c) := by
      rw [Real.rpow_neg hQ.le, show approxUpperConst S₀ L = 2 ^ N * D / approxConst S₀ L from rfl]
      field_simp

/-! ### Bounds on each successive minimum -/

/-- **The product formula for a nonzero point of a dilated approximation domain.** Suppose that at
each place with independent forms every coordinate is at most `D v` times any common bound on the
values of the forms. Then a nonzero point of `approxModule S₀ L c Q`, `Q ≥ 1`, whose values at the
infinite places are at most `t` times the bounds of the domain has
`1 ≤ (∏ v, D v ^ mult v · ∏ v ∈ S₀, D v) · Q ^ approxAbsWeight S₀ c · t ^ d`: a nonzero
coordinate of the point cannot be small at every place. -/
private theorem one_le_mul_rpow_approxAbsWeight_mul_pow {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (D : AbsoluteValue K ℝ → ℝ)
    (hD : ∀ v : AbsoluteValue K ℝ, LinearIndependent K (L v) → ∀ (x : ι → K) (j : ι) (M : ℝ),
      (∀ i, v (L v i x) ≤ M) → v (x j) ≤ D v * M)
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q t : ℝ} (hQ : 1 ≤ Q) (ht : 0 ≤ t)
    {x : ι → K} (hxΛ : x ∈ approxModule S₀ L c Q) (hx : x ≠ 0)
    (hxB : ∀ (w : InfinitePlace K) (i : ι), w (L w.val i x) ≤ t * Q ^ c w.val i) :
    1 ≤ ((∏ v : InfinitePlace K, D v.val ^ v.mult) * ∏ v ∈ S₀, D v.val) *
      Q ^ approxAbsWeight S₀ c * t ^ finrank ℚ K := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  -- `P v` bounds `Q ^ c v i` for every `i`, and the `P v` multiply to `Q ^ approxAbsWeight S₀ c`.
  set P : AbsoluteValue K ℝ → ℝ := fun v ↦ ∏ i, Q ^ |c v i|
  have hP (v : AbsoluteValue K ℝ) (i : ι) : Q ^ c v i ≤ P v := by
    simp only [P, ← Real.rpow_sum_of_pos hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i ↦ |c v i|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)))
  have hweight : Q ^ approxAbsWeight S₀ c =
      (∏ v : InfinitePlace K, P v.val ^ v.mult) * ∏ v ∈ S₀, P v.val := by
    rw [approxAbsWeight_eq_approxWeight_abs, rpow_approxWeight S₀ _ hQ0]
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  rw [mem_approxModule, abs_of_pos hQ0] at hxΛ
  have hinf (v : InfinitePlace K) : v (x j) ≤ D v.val * (t * P v.val) :=
    hD v.val (hLInf v) x j _ fun i ↦ (hxB v i).trans (by gcongr; exact hP _ i)
  have hfin (v : FinitePlace K) (hv : v ∈ S₀) : v (x j) ≤ D v.val * P v.val :=
    hD v.val (hLFin v hv) x j _ fun i ↦ (hxΛ.1 v hv i).trans (hP _ i)
  calc 1 ≤ (∏ v : InfinitePlace K, v (x j) ^ v.mult) * ∏ v ∈ S₀, v (x j) :=
        NumberField.one_le_prod_apply_of_forall_le_one S₀ hj fun v hv ↦ hxΛ.2 v hv j
    _ ≤ (∏ v : InfinitePlace K, (D v.val * (t * P v.val)) ^ v.mult) * ∏ v ∈ S₀, D v.val * P v.val
        := by
        refine mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ by positivity)
          fun v _ ↦ pow_le_pow_left₀ (apply_nonneg _ _) (hinf v) _)
          (Finset.prod_le_prod₀ (fun v _ ↦ apply_nonneg _ _) hfin)
          (Finset.prod_nonneg fun v _ ↦ apply_nonneg _ _) ?_
        exact Finset.prod_nonneg fun v _ ↦ pow_nonneg ((apply_nonneg _ _).trans (hinf v)) _
    _ = _ := by
        rw [hweight, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
        simp only [mul_pow, Finset.prod_mul_distrib]
        ring

/-- **A lower bound for the nonzero points of a dilated approximation domain.** There is `C > 0`,
depending only on `K`, `S₀` and the forms, such that for every exponent family `c`, every level
`Q ≥ 1` and every `t > 0`, a nonzero point of `approxModule S₀ L c Q` whose values at the infinite
places are at most `t` times the bounds of the domain has `C * Q ^ (-approxAbsWeight S₀ c) ≤ t ^ d`.
-/
private theorem exists_pos_forall_mul_rpow_le_pow {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q t : ℝ}, 1 ≤ Q → 0 < t →
      ∀ x ∈ approxModule S₀ L c Q, x ≠ 0 →
        (∀ (w : InfinitePlace K) (i : ι), w (L w.val i x) ≤ t * Q ^ c w.val i) →
        C * Q ^ (-approxAbsWeight S₀ c) ≤ t ^ finrank ℚ K := by
  classical
  -- At each place with independent forms, a coordinate is at most `D v` times a common bound on
  -- the values of the forms.
  have hcoord (v : AbsoluteValue K ℝ) : ∃ D : ℝ, 0 < D ∧ (LinearIndependent K (L v) →
      ∀ (x : ι → K) (j : ι) (M : ℝ), (∀ i, v (L v i x) ≤ M) → v (x j) ≤ D * M) := by
    by_cases hv : LinearIndependent K (L v)
    · obtain ⟨D, hD0, hD⟩ := hv.exists_forall_abv_apply_le_mul v
      refine ⟨1 + D, by positivity, fun _ x j M hM ↦ (hD x M hM j).trans ?_⟩
      have hM0 : 0 ≤ M := (apply_nonneg v _).trans (hM j)
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    · exact ⟨1, one_pos, fun h ↦ (hv h).elim⟩
  choose D hD0 hD using hcoord
  set C' : ℝ := (∏ v : InfinitePlace K, D v.val ^ v.mult) * ∏ v ∈ S₀, D v.val
  have hC' : 0 < C' :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (hD0 _) _) (Finset.prod_pos fun v _ ↦ hD0 _)
  refine ⟨C'⁻¹, inv_pos.2 hC', fun c Q t hQ ht x hxΛ hx hxB ↦ ?_⟩
  rw [Real.rpow_neg (zero_le_one.trans hQ), ← mul_inv,
    inv_le_iff_one_le_mul₀' (mul_pos hC' (Real.rpow_pos_of_pos (zero_lt_one.trans_le hQ) _))]
  exact one_le_mul_rpow_approxAbsWeight_mul_pow hLInf hLFin D hD c hQ ht.le hxΛ hx hxB

open scoped Classical Pointwise in
/-- Below `#ι`, the `l`-th successive minimum over `K` of an approximation domain of positive level
is positive, and its dilate of the body contains the mixed embedding of a nonzero point of the
module. -/
private theorem exists_ne_zero_mem_smul_approxBody {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) {l : ℕ} (hl : l < Fintype.card ι) :
    0 < (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ∧
      ∃ x ∈ approxModule S₀ L c Q, x ≠ 0 ∧ (fun j ↦ mixedEmbedding K (x j)) ∈
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l • approxBody L c Q := by
  let _ := discreteTopology_mixedImage_approxModule hLFin c Q
  let _ := isZLattice_mixedImage_approxModule hLFin c hQ.ne'
  let B : ConvexBody (ι → mixedSpace K) :=
    ⟨approxBody L c Q, convex_approxBody L c Q, isCompact_approxBody hLInf c Q,
      ⟨0, mem_of_mem_nhds (approxBody_mem_nhds_zero L c hQ)⟩⟩
  have hcoe : (B : Set (ι → mixedSpace K)) = approxBody L c Q := ConvexBody.coe_mk _ _ _ _
  have hB : 0 ∈ interior (B : Set (ι → mixedSpace K)) := by
    rw [hcoe]
    exact mem_interior_iff_mem_nhds.2 (approxBody_mem_nhds_zero L c hQ)
  have hpos := Submodule.successiveMinimum_pos (Λ := approxModule S₀ L c Q) hB hl
  obtain ⟨x, hx, hxB⟩ := (Submodule.successiveMinimum_le_iff hB hl hpos).1 le_rfl
  rw [hcoe] at hpos hxB
  exact ⟨hpos, x 0, (hxB 0).1, hx.ne_zero 0, (hxB 0).2⟩

/-- Each successive minimum over `K` of an approximation domain has `d`-th power at least
`C * Q ^ (-approxAbsWeight S₀ c)`, with `C > 0` independent of `c` and of `Q ≥ 1`. -/
private theorem exists_pos_forall_mul_rpow_le_successiveMinimum_pow
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 1 ≤ Q →
      ∀ {l : ℕ}, l < Fintype.card ι → C * Q ^ (-approxAbsWeight S₀ c) ≤
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ^ finrank ℚ K := by
  obtain ⟨C, hC, h⟩ := exists_pos_forall_mul_rpow_le_pow hLInf hLFin
  refine ⟨C, hC, fun c Q hQ l hl ↦ ?_⟩
  obtain ⟨hpos, x, hxΛ, hx, hxB⟩ :=
    exists_ne_zero_mem_smul_approxBody hLInf hLFin c (zero_lt_one.trans_le hQ) hl
  exact h c hQ hpos x hxΛ hx ((mixedEmbedding_mem_smul_approxBody_iff hpos).1 hxB)

/-- Each successive minimum over `K` of an approximation domain has `d`-th power at most
`C * Q ^ (#ι * approxAbsWeight S₀ c)`, with `C > 0` independent of `c` and of `Q ≥ 1`: Minkowski's
upper bound on the product of all the minima, with every other minimum replaced by its lower
bound. -/
private theorem exists_pos_forall_successiveMinimum_pow_le_mul_rpow
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 1 ≤ Q →
      ∀ {l : ℕ}, l < Fintype.card ι →
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ^ finrank ℚ K ≤
          C * Q ^ ((Fintype.card ι : ℝ) * approxAbsWeight S₀ c) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_pos_forall_mul_rpow_le_successiveMinimum_pow hLInf hLFin
  set n := Fintype.card ι
  set C₂ := approxUpperConst S₀ L
  have hC₂ : 0 < C₂ := approxUpperConst_pos hLInf hLFin
  refine ⟨C₂ / C₁ ^ (n - 1), by positivity, fun c Q hQ l hl ↦ ?_⟩
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  set y := Q ^ approxAbsWeight S₀ c
  set f : Fin n → ℝ := fun k ↦
    (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k ^ finrank ℚ K
  have hf (k : Fin n) : C₁ * y⁻¹ ≤ f k := by
    rw [← Real.rpow_neg hQ0.le]
    exact h₁ c hQ k.isLt
  -- Minkowski's upper bound on the product, with `Q ^ (-weight) ≤ Q ^ approxAbsWeight`.
  have hprod : ∏ k, f k ≤ C₂ * y := by
    refine (prod_successiveMinimum_approx_le hLInf hLFin c hQ0).trans ?_
    gcongr
    exact Real.rpow_le_rpow_of_exponent_le hQ
      ((neg_le_abs _).trans (abs_approxWeight_le_approxAbsWeight S₀ c))
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_add_one_of_ne_zero (by omega)
  -- The other `m` minima are each at least `C₁ * y⁻¹`.
  have herase : (C₁ * y⁻¹) ^ m ≤ ∏ k ∈ Finset.univ.erase (⟨l, hl⟩ : Fin n), f k := by
    calc (C₁ * y⁻¹) ^ m = ∏ _k ∈ Finset.univ.erase (⟨l, hl⟩ : Fin n), (C₁ * y⁻¹) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, hm, Nat.add_sub_cancel]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun k _ ↦ hf k
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ ⟨l, hl⟩)] at hprod
  have key : f ⟨l, hl⟩ * (C₁ ^ m * (y ^ m)⁻¹) ≤ C₂ * y := by
    rw [← inv_pow, ← mul_pow]
    exact (mul_le_mul_of_nonneg_left herase
      (pow_nonneg (Submodule.successiveMinimum_nonneg _ _ _) _)).trans hprod
  have hyn : Q ^ ((n : ℝ) * approxAbsWeight S₀ c) = y ^ n := by
    rw [mul_comm, Real.rpow_mul_natCast hQ0.le]
  rw [hyn, hm, Nat.add_sub_cancel]
  calc _ = f ⟨l, hl⟩ := by simp only [f]
    _ ≤ C₂ * y / (C₁ ^ m * (y ^ m)⁻¹) := (le_div_iff₀ (by positivity)).2 key
    _ = C₂ / C₁ ^ m * y ^ (m + 1) := by
      field_simp
      ring

/-- **The successive minima of approximation domains are confined, lower bound.** For forms
linearly independent at every infinite place and at every place of `S₀`, and a bound `A`, there is
a level `Q₀ > 0` such that for every exponent family `c` with `approxAbsWeight S₀ c ≤ A`, every
`Q ≥ Q₀` and every `l < #ι`, the `l`-th successive minimum over `K` of `approxDomain S₀ L c Q` is at
least `Q ^ (-B)`, where `B = #ι · (A + 1) / [K : ℚ]`. The level `Q₀` depends on `A` but not on `c`.
-/
theorem exists_pos_forall_rpow_le_successiveMinimum {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (A : ℝ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ c : AbsoluteValue K ℝ → ι → ℝ, approxAbsWeight S₀ c ≤ A →
      ∀ {Q : ℝ}, Q₀ ≤ Q → ∀ {l : ℕ}, l < Fintype.card ι →
        Q ^ (-((Fintype.card ι : ℝ) * (A + 1) / finrank ℚ K)) ≤
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l := by
  obtain ⟨C, hC, h⟩ := exists_pos_forall_mul_rpow_le_successiveMinimum_pow hLInf hLFin
  refine ⟨max 1 C⁻¹, lt_max_of_lt_left one_pos, fun c hc Q hQ l hl ↦ ?_⟩
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hd : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  have hA : 0 ≤ A := (approxAbsWeight_nonneg S₀ c).trans hc
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast (show 1 ≤ Fintype.card ι by omega)
  refine (pow_le_pow_iff_left₀ (Real.rpow_nonneg hQ0.le _)
    (Submodule.successiveMinimum_nonneg _ _ _) hd).1 ?_
  have hexp : -((Fintype.card ι : ℝ) * (A + 1) / finrank ℚ K) * finrank ℚ K =
      -((Fintype.card ι : ℝ) * (A + 1)) := by
    field_simp
  rw [← Real.rpow_mul_natCast hQ0.le, hexp]
  calc Q ^ (-((Fintype.card ι : ℝ) * (A + 1))) ≤ Q ^ (-1 + -A) :=
        Real.rpow_le_rpow_of_exponent_le hQ1 (by nlinarith)
    _ = Q⁻¹ * Q ^ (-A) := by rw [Real.rpow_add hQ0, Real.rpow_neg_one]
    _ ≤ C * Q ^ (-approxAbsWeight S₀ c) :=
        mul_le_mul (inv_le_of_inv_le₀ hC ((le_max_right _ _).trans hQ))
          (Real.rpow_le_rpow_of_exponent_le hQ1 (neg_le_neg hc)) (by positivity) hC.le
    _ ≤ _ := h c hQ1 hl

/-- **The successive minima of approximation domains are confined.** For forms linearly
independent at every infinite place and at every place of `S₀`, and a bound `A`, there is a level
`Q₀ > 0` such that for every exponent family `c` with `approxAbsWeight S₀ c ≤ A`, every `Q ≥ Q₀`
and every `l < #ι`, the `l`-th successive minimum over `K` of `approxDomain S₀ L c Q` lies between
`Q ^ (-B)` and `Q ^ B`, where `B = #ι · (A + 1) / [K : ℚ]`. The level `Q₀` depends on `A` but not
on `c`. -/
theorem exists_pos_forall_rpow_le_successiveMinimum_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (A : ℝ) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ c : AbsoluteValue K ℝ → ι → ℝ, approxAbsWeight S₀ c ≤ A →
      ∀ {Q : ℝ}, Q₀ ≤ Q → ∀ {l : ℕ}, l < Fintype.card ι →
        Q ^ (-((Fintype.card ι : ℝ) * (A + 1) / finrank ℚ K)) ≤
            (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ∧
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ≤
            Q ^ ((Fintype.card ι : ℝ) * (A + 1) / finrank ℚ K) := by
  obtain ⟨Q₁, -, h₁⟩ := exists_pos_forall_rpow_le_successiveMinimum hLInf hLFin A
  obtain ⟨C, -, h⟩ := exists_pos_forall_successiveMinimum_pow_le_mul_rpow hLInf hLFin
  refine ⟨max (max 1 Q₁) C, lt_max_of_lt_left (lt_max_of_lt_left one_pos),
    fun c hc Q hQ l hl ↦ ⟨h₁ c hc ((le_max_right _ _).trans ((le_max_left _ _).trans hQ)) hl, ?_⟩⟩
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans ((le_max_left _ _).trans hQ)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hd : finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast (show 1 ≤ Fintype.card ι by omega)
  refine (pow_le_pow_iff_left₀ (Submodule.successiveMinimum_nonneg _ _ _)
    (Real.rpow_nonneg hQ0.le _) hd).1 ?_
  have hexp : (Fintype.card ι : ℝ) * (A + 1) / finrank ℚ K * finrank ℚ K =
      (Fintype.card ι : ℝ) * (A + 1) := by
    field_simp
  rw [← Real.rpow_mul_natCast hQ0.le, hexp]
  calc _ ≤ C * Q ^ ((Fintype.card ι : ℝ) * approxAbsWeight S₀ c) := h c hQ1 hl
    _ ≤ Q ^ (1 : ℝ) * Q ^ ((Fintype.card ι : ℝ) * A) := by
        gcongr
        rw [Real.rpow_one]
        exact (le_max_right _ _).trans hQ
    _ = Q ^ (1 + (Fintype.card ι : ℝ) * A) := (Real.rpow_add hQ0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ1 (by nlinarith)

end TauCeti.NumberField
