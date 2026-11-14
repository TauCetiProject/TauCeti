/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.SuccessiveMinima

/-!
# Successive minima of an approximation domain

Let `K` be a number field of degree `d`, and let `μ l` be the successive minima over `K` of the
approximation domain `TauCeti.NumberField.approxDomain S₀ L c Q`, that is, of the lattice
`approxModule S₀ L c Q` with respect to the body `approxBody L c Q`. Their product is
`Q ^ (-approxWeight S₀ c)` up to two constants that do not depend on `Q` or on the exponents `c`:

```text
2 ^ N / (N! · c_K ^ N · C) · Q ^ (-w)  ≤  ∏ l, μ l ^ d,
∏ l, μ l ^ d  ≤  2 ^ N · (∏ v ∈ S₀, N 𝔭_v ^ n) / C · Q ^ (-w),
```

where `n = card ι`, `N = d n`, `w = approxWeight S₀ c`, `C = approxConst S₀ L` and
`c_K = integralBasisHouse K`.

Both bounds combine Minkowski's second theorem over `K` with the comparison of the volume of the
body with the covolume of the lattice. The lower bound uses the half of that comparison which
holds without rounding (`TauCeti.NumberField.volume_div_covolume_le`), so it loses nothing at the
finite places. The upper bound uses the other half, and pays the factor `∏ v ∈ S₀, N 𝔭_v ^ n`
lost when the finite-place bounds `Q ^ c v i` are rounded down to values of `v`.

These bounds are what makes the geometry of numbers of approximation domains uniform in the level
`Q`: in particular, when the weight is negative, the product of the minima grows like a positive
power of `Q`, so some minimum eventually exceeds `1`.

## Main results

* `TauCeti.NumberField.le_prod_successiveMinimum_approx`: the lower bound on `∏ l, μ l ^ d`.
* `TauCeti.NumberField.prod_successiveMinimum_approx_le`: the upper bound on `∏ l, μ l ^ d`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Theorem C.2.11 and Corollary 7.5.8.
* A version of these bounds is formalized in Ralf Stephan's `rwst/Subspace-Theorems`
  (Apache 2.0), file `DiophantineApproximation/FieldMinkowski.lean`.
-/

public section

open MeasureTheory Module NumberField NumberField.mixedEmbedding

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- **The successive minima of an approximation domain, lower bound** (Bombieri–Gubler, Theorem
C.2.11 with Corollary 7.5.8): for `0 < Q` and linearly independent forms at the infinite places and
at `S₀`, the product of the `[K : ℚ]`-th powers of the successive minima over `K` of
`approxDomain S₀ L c Q` is at least `2 ^ N / (N! · c_K ^ N · approxConst S₀ L) · Q ^ (-weight)`,
where `N = [K : ℚ] · card ι` and `c_K = integralBasisHouse K`. -/
theorem le_prod_successiveMinimum_approx {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    (2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) /
        (((finrank ℚ K * Fintype.card ι).factorial : ℝ) *
          integralBasisHouse K ^ (finrank ℚ K * Fintype.card ι) * approxConst S₀ L) *
        Q ^ (-approxWeight S₀ c) ≤
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
  calc (2 : ℝ) ^ N / ((N.factorial : ℝ) * integralBasisHouse K ^ N * approxConst S₀ L) *
        Q ^ (-approxWeight S₀ c)
      = A / (approxConst S₀ L * Q ^ approxWeight S₀ c) := by
        rw [Real.rpow_neg hQ.le]
        simp only [A]
        ring
    _ ≤ P := (div_le_iff₀ (mul_pos hconst hQw)).2 hA

/-- **The successive minima of an approximation domain, upper bound** (Bombieri–Gubler, Theorem
C.2.11 with Corollary 7.5.8): for `0 < Q` and linearly independent forms at the infinite places and
at `S₀`, the product of the `[K : ℚ]`-th powers of the successive minima over `K` of
`approxDomain S₀ L c Q` is at most
`2 ^ N · ∏ v ∈ S₀, N 𝔭_v ^ card ι / approxConst S₀ L · Q ^ (-weight)`, where
`N = [K : ℚ] · card ι`. -/
theorem prod_successiveMinimum_approx_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ∏ l : Fin (Fintype.card ι),
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ^ finrank ℚ K ≤
      (2 : ℝ) ^ (finrank ℚ K * Fintype.card ι) *
          (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι) /
          approxConst S₀ L *
        Q ^ (-approxWeight S₀ c) := by
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
    _ = 2 ^ N * D / approxConst S₀ L * Q ^ (-approxWeight S₀ c) := by
      rw [Real.rpow_neg hQ.le]
      field_simp

end TauCeti.NumberField
