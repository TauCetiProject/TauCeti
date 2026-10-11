/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.SuccessiveMinima
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Minkowski's theorems on the minima of a positive definite lattice

Let `L` be a positive definite integral lattice of rank `n`, with successive minima
`λ₀ ≤ ⋯ ≤ λ_{n-1}` measured as norms `B(x, x)`, so that `λ₀ = min L`. Minkowski's convex body
theorem, applied to a realization of `L` in `ℝⁿ`, bounds their product by the determinant:

```text
λ₀ ⋯ λ_{n-1} ≤ cₙⁿ · det L,   cₙ = (4 / π) · Γ(n / 2 + 1) ^ (2 / n).
```

This is Minkowski's second theorem, with the explicit constant `cₙ` of the convex body theorem for
the Euclidean ball; `cₙ` is an upper bound for the Hermite constant `γₙ`. Since every `λᵢ` is at
least `min L`, it contains Minkowski's bound for the minimum (his first theorem),

```text
min L ≤ (4 / π) · Γ(n / 2 + 1) ^ (2 / n) · (det L) ^ (1 / n).
```

For the proof, let `x₀, …, x_{n-1}` be independent lattice vectors with `B(xᵢ, xᵢ) = λᵢ`, let
`φ : L → ℝⁿ` be a realization, and let `e₀, …, e_{n-1}` be the Gram–Schmidt orthonormalization of
`φ x₀, …, φ x_{n-1}`. If the last nonzero coordinate of `φ y` in the basis `e` is the `k`-th, then
`y` is independent of `x₀, …, x_{k-1}`, so `B(y, y) ≥ λₖ` and hence `∑ⱼ ⟪eⱼ, φ y⟫² / λⱼ ≥ 1`. The
open ellipsoid `∑ⱼ ⟪eⱼ, v⟫² / λⱼ < 1` thus contains no nonzero vector of `φ(L)`, and by the convex
body theorem its volume `√(λ₀ ⋯ λ_{n-1}) · π^(n/2) / Γ(n/2 + 1)` is at most `2ⁿ` times the covolume
`√(det L)`.

The bounds are stated without real powers, as `(∏ᵢ λᵢ) · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L` and
`(min L)ⁿ · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L`, and the bound for the minimum also in the root form
displayed above. None needs a rank hypothesis: in rank zero the product is empty, the minimum is
`0`, and all statements hold trivially.

## Main results

* `TauCeti.IntegralLattice.exists_ne_zero_mem_of_two_pow_mul_sqrt_determinant_lt`: the convex body
  theorem for a realization of a nondegenerate lattice: a symmetric convex set of volume greater
  than `2ⁿ √(det L)` contains a nonzero lattice vector.
* `TauCeti.IntegralLattice.IsPosDef.prod_successiveMinimum_mul_pi_pow_le`: Minkowski's second
  theorem, `(∏ᵢ λᵢ) · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L`.
* `TauCeti.IntegralLattice.IsPosDef.minimum_pow_mul_pi_pow_le`:
  `(min L)ⁿ · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L`.
* `TauCeti.IntegralLattice.IsPosDef.minimum_le_mul_determinant_rpow`:
  `min L ≤ (4 / π) · Γ(n/2 + 1) ^ (2/n) · (det L) ^ (1/n)`.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Chapter III, §2, Chapter VIII,
  and Chapter X.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §1.5.
-/

public section

open Module MeasureTheory
open scoped InnerProductSpace

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- **Minkowski's convex body theorem for a realized lattice.** Let `φ` realize a nondegenerate
integral lattice `L` in a real inner product space `E` of dimension `n`. A convex set `K ⊆ E`,
symmetric about the origin, of volume greater than `2ⁿ · √(det L)` contains `φ y` for some
nonzero `y ∈ L`. -/
theorem exists_ne_zero_mem_of_two_pow_mul_sqrt_determinant_lt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [L.IsNondegenerate] {φ : L →ₗ[ℤ] E}
    (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y)
    (hspan : Submodule.span ℝ (Set.range φ) = ⊤) {K : Set E} (hsymm : ∀ v ∈ K, -v ∈ K)
    (hconv : Convex ℝ K)
    (hK : ENNReal.ofReal (2 ^ finrank ℝ E * √(L.determinant : ℝ)) < volume K) :
    ∃ y : L, y ≠ 0 ∧ φ y ∈ K := by
  have := discreteTopology_range hφ
  have : IsZLattice ℝ (LinearMap.range φ) := ⟨by rw [LinearMap.coe_range, hspan]⟩
  set Λ := LinearMap.range φ
  have hc : √(L.determinant : ℝ) = ZLattice.covolume Λ := by
    rw [← covolume_range_sq_eq_determinant hφ hspan, Real.sqrt_sq (ZLattice.covolume_pos _ _).le]
  let b := Free.chooseBasis ℤ Λ
  have hfund := ZLattice.isAddFundamentalDomain b volume
  have : Countable Λ.toAddSubgroup := (inferInstance : Countable Λ)
  -- Convert the `ENNReal` power in the geometry-of-numbers theorem to the `ofReal` form in `hK`.
  have htwo_pow : (2 : ENNReal) ^ finrank ℝ E = ENNReal.ofReal (2 ^ finrank ℝ E) := by
    simp [ENNReal.ofReal_pow]
  have hvol : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) * 2 ^ finrank ℝ E <
      volume K := by
    rwa [← ofReal_measureReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne,
      ← ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfund, ← hc, htwo_pow,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm]
  obtain ⟨⟨_, ⟨y, rfl⟩⟩, hy0, hyK⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (L := Λ.toAddSubgroup) hfund
      hsymm hconv hvol
  refine ⟨y, ?_, hyK⟩
  rintro rfl
  exact hy0 (by simp)

section SecondTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let `φ` carry the form of a positive definite lattice `L` to the inner product, and let `e` be
the Gram–Schmidt orthonormalization of the images of independent vectors `x₀, …, x_{n-1}`
attaining the successive minima `λ₀, …, λ_{n-1}`. Every nonzero `y ∈ L` satisfies
`∑ⱼ ⟪eⱼ, φ y⟫² / λⱼ ≥ 1`: if the last nonzero coordinate of `φ y` is the `k`-th, then `y` is
independent of `x₀, …, x_{k-1}`, so `B(y, y) ≥ λₖ ≥ λⱼ` for every `j ≤ k`. -/
private lemma one_le_sum_inner_sq_div_successiveMinimum [FiniteDimensional ℝ E] (hL : L.IsPosDef)
    {φ : L →ₗ[ℤ] E}
    (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y) {x : Fin (finrank ℤ L) → L}
    (hx : LinearIndependent ℤ x) (hnorm : ∀ i, L.integralNorm (x i) = L.successiveMinimum i)
    (hE : finrank ℝ E = Fintype.card (Fin (finrank ℤ L))) {y : L} (hy : y ≠ 0) :
    1 ≤ ∑ j, ⟪InnerProductSpace.gramSchmidtOrthonormalBasis hE (fun i ↦ φ (x i)) j, φ y⟫_ℝ ^ 2 /
      L.successiveMinimum j := by
  have : L.IsNondegenerate := ⟨(L.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hL).2⟩
  set e := InnerProductSpace.gramSchmidtOrthonormalBasis hE (fun i ↦ φ (x i))
  set μ : Fin (finrank ℤ L) → ℝ := fun i ↦ L.successiveMinimum i
  have hμ (i : Fin (finrank ℤ L)) : 0 < μ i := by
    simpa [μ] using hL.successiveMinimum_pos i
  have hφy : φ y ≠ 0 := fun h ↦ hy (injective_of_inner_eq hφ (h.trans (map_zero φ).symm))
  have hne : (Finset.univ.filter fun j ↦ ⟪e j, φ y⟫_ℝ ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hφy
    rw [← e.sum_repr' (φ y)]
    simp_all
  -- `k` is the last index at which `φ y` has a nonzero coordinate.
  set k := (Finset.univ.filter fun j ↦ ⟪e j, φ y⟫_ℝ ≠ 0).max' hne
  have hk : ⟪e k, φ y⟫_ℝ ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  have hzero (j : Fin (finrank ℤ L)) (hj : k < j) : ⟪e j, φ y⟫_ℝ = 0 := by
    by_contra h
    exact (Finset.le_max' _ j (by simp [h])).not_gt hj
  -- Since `e k` is orthogonal to `φ x₀, …, φ x_{k-1}`, `y` is independent of `x₀, …, x_{k-1}`.
  have hind : LinearIndependent ℤ
      (Fin.snoc (fun j : Fin k.val ↦ x (Fin.castLE k.isLt.le j)) y : Fin (k.val + 1) → L) := by
    refine (hx.comp _ (Fin.castLE_injective _)).finSnoc' _ y fun a w hw hsum ↦ ?_
    let f : L →ₗ[ℤ] ℝ := ((innerSL ℝ (e k)).toLinearMap.restrictScalars ℤ).comp φ
    have hfw : f w = 0 := by
      refine (Submodule.span_le (p := LinearMap.ker f)).mpr ?_ hw
      rintro _ ⟨j, rfl⟩
      exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hE
        (fun i ↦ φ (x i)) (i := Fin.castLE k.isLt.le j) (j := k) j.isLt
    have h := congrArg f hsum
    rw [map_add, map_zsmul, hfw, add_zero, map_zero, zsmul_eq_mul] at h
    simpa [f, hk] using h
  have hle := hL.isPosSemidef.successiveMinimum_le_integralNorm_of_linearIndependent k
    (x := fun j ↦ x (Fin.castLE k.isLt.le j)) (fun j ↦ (hnorm _).le) hind
  have hNy : (L.integralNorm y : ℝ) = ∑ j, ⟪e j, φ y⟫_ℝ ^ 2 := by
    rw [integralNorm_apply, ← hφ, real_inner_self_eq_norm_sq, ← e.sum_sq_norm_inner_right]
    simp [Real.norm_eq_abs, sq_abs]
  calc 1 ≤ (∑ j, ⟪e j, φ y⟫_ℝ ^ 2) / μ k := by
        rw [le_div_iff₀ (hμ k), one_mul, ← hNy]
        simpa [μ] using (Int.cast_le (R := ℝ)).mpr hle
    _ = ∑ j, ⟪e j, φ y⟫_ℝ ^ 2 / μ k := Finset.sum_div _ _ _
    _ ≤ ∑ j, ⟪e j, φ y⟫_ℝ ^ 2 / μ j := Finset.sum_le_sum fun j _ ↦ by
        rcases le_or_gt j k with hjk | hjk
        · exact div_le_div_of_nonneg_left (sq_nonneg _) (hμ j)
            (by simpa [μ] using L.monotone_successiveMinimum hjk)
        · simp [hzero j hjk]

/-- Let `φ` carry the form of a positive definite lattice `L` of rank `n` to the inner product of
an `n`-dimensional space `E`. There is a linear map `T : E → E` with `|det T|⁻¹ = √(λ₀ ⋯ λ_{n-1})`
sending every nonzero vector of `φ(L)` outside the open unit ball. In the Gram–Schmidt
orthonormalization `e` of the images of independent vectors attaining the successive minima, it
scales the `j`-th coordinate by `1 / √λⱼ`, so that `T⁻¹(ball 0 1)` is the open ellipsoid
`∑ⱼ ⟪eⱼ, v⟫² / λⱼ < 1`. -/
private lemma exists_linearMap_one_le_norm [FiniteDimensional ℝ E] (hL : L.IsPosDef)
    {φ : L →ₗ[ℤ] E} (hφ : ∀ x y : L, ⟪φ x, φ y⟫_ℝ = L.integralForm x y)
    (hE : finrank ℝ E = Fintype.card (Fin (finrank ℤ L))) :
    ∃ T : E →ₗ[ℝ] E, LinearMap.det T ≠ 0 ∧
      |(LinearMap.det T)⁻¹| = √(∏ i, (L.successiveMinimum i : ℝ)) ∧
      ∀ y : L, y ≠ 0 → 1 ≤ ‖T (φ y)‖ := by
  classical
  obtain ⟨x, hx, hnorm⟩ :=
    hL.isPosSemidef.exists_linearIndependent_integralNorm_eq_successiveMinimum
  set e := InnerProductSpace.gramSchmidtOrthonormalBasis hE (fun i ↦ φ (x i))
  set μ : Fin (finrank ℤ L) → ℝ := fun i ↦ L.successiveMinimum i
  have hμ (i : Fin (finrank ℤ L)) : 0 < μ i := by
    simpa [μ] using hL.successiveMinimum_pos i
  let T : E →ₗ[ℝ] E := Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal fun j ↦ (√(μ j))⁻¹)
  have hdet : LinearMap.det T = ∏ j, (√(μ j))⁻¹ := by
    simp [T, LinearMap.det_toLin, Matrix.det_diagonal]
  have hpos : 0 < ∏ j, √(μ j) := Finset.prod_pos fun j _ ↦ Real.sqrt_pos.mpr (hμ j)
  have hT (v : E) : ‖T v‖ ^ 2 = ∑ j, ⟪e j, v⟫_ℝ ^ 2 / μ j := by
    rw [← e.sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have : ⟪e j, T v⟫_ℝ = (√(μ j))⁻¹ * ⟪e j, v⟫_ℝ := by
      simp only [T, Matrix.toLin_apply, Matrix.mulVec_diagonal, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      exact e.orthonormal.inner_right_fintype _ j
    rw [this, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, Real.sq_sqrt (hμ j).le, inv_mul_eq_div]
  refine ⟨T, ?_, ?_, fun y hy ↦ ?_⟩
  · rw [hdet, Finset.prod_inv_distrib]
    exact inv_ne_zero hpos.ne'
  · rw [hdet, Finset.prod_inv_distrib, inv_inv, abs_of_pos hpos,
      Real.sqrt_prod _ fun j _ ↦ (hμ j).le]
  have h1 := one_le_sum_inner_sq_div_successiveMinimum hL hφ hx hnorm hE hy
  rw [← hT] at h1
  nlinarith [norm_nonneg (T (φ y))]

end SecondTheorem

/-- **Minkowski's second theorem.** The successive minima `λ₀, …, λ_{n-1}` of a positive definite
integral lattice of rank `n` satisfy `(∏ᵢ λᵢ) · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L`, that is,
`∏ᵢ λᵢ ≤ cₙⁿ · det L` with `cₙ = (4 / π) · Γ(n/2 + 1) ^ (2/n)` the constant of Minkowski's bound for
the minimum. -/
theorem IsPosDef.prod_successiveMinimum_mul_pi_pow_le (hL : L.IsPosDef) :
    (∏ i, (L.successiveMinimum i : ℝ)) * Real.pi ^ finrank ℤ L ≤
      4 ^ finrank ℤ L * Real.Gamma (finrank ℤ L / 2 + 1) ^ 2 * L.determinant := by
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · have hn : finrank ℤ L = 0 := finrank_zero_of_subsingleton
    have : IsEmpty (Fin (finrank ℤ L)) := by rw [hn]; infer_instance
    rw [Finset.univ_eq_empty, Finset.prod_empty, hn]
    simpa [Real.Gamma_one] using (Int.cast_le (R := ℝ)).mpr hL.determinant_pos
  set n := finrank ℤ L
  have : L.IsNondegenerate := ⟨(L.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hL).2⟩
  obtain ⟨φ, hφ, hspan⟩ := hL.exists_realization
  set E := EuclideanSpace ℝ (Fin n)
  have hE : finrank ℝ E = n := by simp [E]
  have : Nontrivial E := by
    rw [← finrank_pos_iff (R := ℝ), hE]
    exact finrank_pos
  set Γ := Real.Gamma (n / 2 + 1)
  have hΓ : 0 < Γ := Real.Gamma_pos_of_pos (by positivity)
  set P := ∏ i, (L.successiveMinimum i : ℝ)
  have hμ (i : Fin n) : (0 : ℝ) < L.successiveMinimum i := by
    exact_mod_cast hL.successiveMinimum_pos i
  have hP : 0 < P := Finset.prod_pos fun i _ ↦ hμ i
  -- The open ellipsoid `T⁻¹(ball 0 1)` has volume `√P` times that of the unit ball and contains
  -- no nonzero vector of `φ(L)`.
  obtain ⟨T, hT0, hTdet, hT⟩ := exists_linearMap_one_le_norm hL hφ (by simp)
  by_contra! h
  -- Suppose the bound fails. Then the ellipsoid has volume larger than `2ⁿ √(det L)`.
  have hball : 2 ^ n * √(L.determinant : ℝ) < √P * (√Real.pi ^ n / Γ) := by
    rw [← mul_div_assoc, lt_div_iff₀ hΓ]
    refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
    have hr : (√P * √Real.pi ^ n) ^ 2 = P * Real.pi ^ n := by
      calc (√P * √Real.pi ^ n) ^ 2 = √P ^ 2 * (√Real.pi ^ 2) ^ n := by ring
        _ = P * Real.pi ^ n := by rw [Real.sq_sqrt hP.le, Real.sq_sqrt Real.pi_pos.le]
    have hl : (2 ^ n * √(L.determinant : ℝ) * Γ) ^ 2 = 4 ^ n * Γ ^ 2 * L.determinant := by
      have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
      rw [h4, mul_pow, mul_pow, Real.sq_sqrt (by exact_mod_cast hL.determinant_pos.le)]
      ring
    rw [hr, hl]
    exact h
  have hvol : ENNReal.ofReal (2 ^ finrank ℝ E * √(L.determinant : ℝ)) <
      volume (T ⁻¹' Metric.ball 0 1) := by
    rw [Measure.addHaar_preimage_linearMap _ hT0, hTdet, InnerProductSpace.volume_ball, hE,
      ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ENNReal.ofReal_lt_ofReal_iff ((by positivity : (0 : ℝ) ≤ _).trans_lt hball)]
    exact hball
  -- The convex body theorem then gives a nonzero lattice vector in the ellipsoid, which is
  -- impossible.
  obtain ⟨y, hy, hyK⟩ := exists_ne_zero_mem_of_two_pow_mul_sqrt_determinant_lt hφ hspan
    (fun v hv ↦ by simpa using hv) ((convex_ball 0 1).linear_preimage T) hvol
  exact (hT y hy).not_gt (by simpa using hyK)

/-- **Minkowski's bound for the minimum, without roots.** A positive definite integral lattice of
rank `n` satisfies `(min L)ⁿ · πⁿ ≤ 4ⁿ · Γ(n/2 + 1)² · det L`. -/
theorem IsPosDef.minimum_pow_mul_pi_pow_le (hL : L.IsPosDef) :
    (L.minimum : ℝ) ^ finrank ℤ L * Real.pi ^ finrank ℤ L ≤
      4 ^ finrank ℤ L * Real.Gamma (finrank ℤ L / 2 + 1) ^ 2 * L.determinant := by
  refine le_trans ?_ hL.prod_successiveMinimum_mul_pi_pow_le
  gcongr
  -- Every successive minimum is at least the first one, which is the minimum.
  rw [← Fin.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ ?_
  rw [← hL.isPosSemidef.successiveMinimum_zero i.pos]
  exact_mod_cast L.monotone_successiveMinimum (Nat.zero_le i.val)

/-- **Minkowski's bound for the minimum.** A positive definite integral lattice of rank `n`
satisfies `min L ≤ (4 / π) · Γ(n/2 + 1) ^ (2/n) · (det L) ^ (1/n)`. -/
theorem IsPosDef.minimum_le_mul_determinant_rpow (hL : L.IsPosDef) :
    (L.minimum : ℝ) ≤ 4 / Real.pi * Real.Gamma (finrank ℤ L / 2 + 1) ^ (2 / finrank ℤ L : ℝ) *
      (L.determinant : ℝ) ^ (1 / finrank ℤ L : ℝ) := by
  set n := finrank ℤ L
  have hdet : (0 : ℝ) ≤ L.determinant := by exact_mod_cast hL.determinant_pos.le
  have key := hL.minimum_pow_mul_pi_pow_le
  set Γ := Real.Gamma (n / 2 + 1)
  have hΓ : 0 ≤ Γ := (Real.Gamma_pos_of_pos (by positivity)).le
  rcases subsingleton_or_nontrivial L with hL0 | hL0
  · rw [minimum_eq_zero_of_subsingleton, Nat.cast_zero]
    positivity
  have hn : n ≠ 0 := finrank_pos.ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  -- The analytic identities: the `n`-th powers of the two real powers.
  have hΓn : (Γ ^ (2 / n : ℝ)) ^ n = Γ ^ 2 := by
    rw [← Real.rpow_mul_natCast hΓ, div_mul_cancel₀ _ hn', Real.rpow_two]
  have hdetn : ((L.determinant : ℝ) ^ (1 / n : ℝ)) ^ n = L.determinant := by
    rw [← Real.rpow_mul_natCast hdet, div_mul_cancel₀ _ hn', Real.rpow_one]
  refine le_of_pow_le_pow_left₀ hn (by positivity) ?_
  rw [mul_pow, mul_pow, div_pow, hΓn, hdetn]
  field_simp
  exact key

end TauCeti.IntegralLattice
