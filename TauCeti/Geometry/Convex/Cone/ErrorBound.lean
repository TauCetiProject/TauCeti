/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Alternative
public import TauCeti.LinearAlgebra.LinearMap.PseudoInverse

/-!
# An error bound for homogeneous linear inequalities

Let `a j` be finitely many linear functionals on a finite-dimensional vector space `V` over a
linearly ordered field, cutting out the polyhedral cone `{w | ∀ j, 0 ≤ a j w}`. If a vector `w`
violates each of these inequalities by at most `c`, that is `-c ≤ a j w` for every `j`, then `w`
is within `O(c)` of the cone: there is `w'` in the cone such that `b (w - w')` is bounded by
`C * c` for any prescribed finite family of functionals `b`, with a constant `C` that depends
only on the two families. This is the homogeneous case of Hoffman's error bound. It is stated
with the test functionals `b` instead of a norm, so that it needs no topology on `V`.

The proof splits the inequalities with Tucker's theorem
(`TauCeti.exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos`). The functionals `a j`
occurring in a nonnegative relation `∑ x j • a j = 0` with `x j > 0` vanish on the cone, and on
`w` they are bounded in absolute value by a multiple of `c`. Projecting `w` linearly onto their
common kernel moves it by `O(c)`. The remaining functionals are strictly positive at a single
vector `v₀` of that kernel, so adding a multiple `O(c)` of `v₀` lands in the cone.

In toric geometry the bound is applied to the logarithms of absolute values of torus points: a
point that nearly satisfies the inequalities cutting out the inverse image of a cone under a
linear map is boundedly far from that inverse image. This is what makes analytic toric maps that
satisfy the cone-by-cone support condition proper.

## Main declarations

* `TauCeti.exists_forall_abs_apply_sub_le_of_forall_neg_le`: the homogeneous error bound.

## References

* A. J. Hoffman, *On approximate solutions of systems of linear inequalities*, Journal of Research
  of the National Bureau of Standards 49 (1952), 263–265.
* A. W. Tucker, *Dual systems of homogeneous linear relations*, in *Linear Inequalities and
  Related Systems*, Annals of Mathematics Studies 38, 1956.
-/

public section

namespace TauCeti

variable {ι κ K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [LinearOrder K] [IsStrictOrderedRing K]

/-- If `x` is a nonnegative linear relation among the functionals `a j`, there is a linear map
`P` that fixes the functionals in the support of `x` and moves every `w` violating the
inequalities `0 ≤ a j w` by at most `c` by an amount `O(c)`, as measured by any functional `φ`. -/
private theorem exists_linearMap_forall_abs_apply_le [Fintype ι] (a : ι → Module.Dual K V)
    {x : ι → K} (hx : 0 ≤ x) (hsum : ∑ j, x j • a j = 0) :
    ∃ P : V →ₗ[K] V, (∀ w j, 0 < x j → a j (P w) = a j w) ∧
      ∀ φ : Module.Dual K V, ∃ D : K, 0 ≤ D ∧
        ∀ c : K, 0 ≤ c → ∀ w : V, (∀ j, -c ≤ a j w) → |φ (P w)| ≤ D * c := by
  classical
  -- Compose `A = (x j • a j)_j` with a pseudo-inverse `g`; then `φ ∘ P` factors through `A`, so
  -- it is a linear combination of the coordinates of `A`.
  set A : V →ₗ[K] ι → K := LinearMap.pi fun j ↦ x j • a j
  obtain ⟨g, hg⟩ := A.exists_comp_comp_eq_self
  set P := g ∘ₗ A with hP
  have hAP (w : V) : A (P w) = A w := LinearMap.congr_fun hg w
  have hfac (φ : Module.Dual K V) : ∃ L : ι → K, ∀ w, φ (P w) = ∑ j, L j * (x j * a j w) := by
    refine ⟨fun j ↦ φ (g fun i ↦ if j = i then 1 else 0), fun w ↦ ?_⟩
    rw [hP, LinearMap.comp_apply, ← LinearMap.comp_apply φ g,
      LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ g) (A w)]
    simp [A, mul_comm]
  refine ⟨P, fun w j hj ↦ mul_left_cancel₀ hj.ne' (by simpa [A] using congrFun (hAP w) j),
    fun φ ↦ ?_⟩
  obtain ⟨L, hL⟩ := hfac φ
  set S := ∑ j, x j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ hx j
  refine ⟨(∑ i, |L i|) * S, mul_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hS,
    fun c hc w hw ↦ ?_⟩
  -- The coordinates `x j * a j w` are at least `-x j * c` and sum to zero, so they are bounded
  -- in absolute value by `S * c`.
  have hA (j : ι) : |x j * a j w| ≤ S * c := by
    have hrel : ∑ j, x j * a j w = 0 := by simpa using LinearMap.congr_fun hsum w
    have hle : x j * a j w + x j * c ≤ S * c := by
      have h := Finset.single_le_sum (f := fun i ↦ x i * a i w + x i * c)
        (fun i _ ↦ by rw [← mul_add]; exact mul_nonneg (hx i) (by linarith [hw i]))
        (Finset.mem_univ j)
      simpa [Finset.sum_add_distrib, hrel, ← Finset.sum_mul, S] using h
    have hxS : x j * c ≤ S * c := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ ↦ hx i) (Finset.mem_univ j)) hc
    have hxc : 0 ≤ x j * (a j w + c) := mul_nonneg (hx j) (by linarith [hw j])
    have hxc' : 0 ≤ x j * c := mul_nonneg (hx j) hc
    rw [abs_le]
    constructor <;> nlinarith
  rw [hL, mul_assoc, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hA i) (abs_nonneg _)

/-- **Hoffman's error bound for a polyhedral cone.** Let `a j` be finitely many functionals on a
finite-dimensional space. There is a constant `C` such that every `w` with `-c ≤ a j w` for all
`j`, where `0 ≤ c`, lies within `C * c` of the cone `{w' | ∀ j, 0 ≤ a j w'}`, as measured by
finitely many prescribed functionals `b k`. The constant `C` is nonnegative. -/
theorem exists_forall_abs_apply_sub_le_of_forall_neg_le [Finite ι] [Finite κ]
    [FiniteDimensional K V] (a : ι → Module.Dual K V) (b : κ → Module.Dual K V) :
    ∃ C : K, 0 ≤ C ∧ ∀ c : K, 0 ≤ c → ∀ w : V, (∀ j, -c ≤ a j w) →
      ∃ w' : V, (∀ j, 0 ≤ a j w') ∧ ∀ k, |b k (w - w')| ≤ C * c := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  -- Tucker's theorem: a nonnegative relation `x` and a vector `v₀` with `x j + a j v₀ > 0`.
  obtain ⟨x, y, hx, hsum, hy, hpos⟩ :=
    exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos (K := K) a
  set v₀ := (Module.evalEquiv K V).symm y
  have hv₀ (φ : Module.Dual K V) : φ v₀ = y φ := Module.apply_evalEquiv_symm_apply K V φ y
  simp only [← hv₀] at hy hpos
  -- The functionals in the support of `x` vanish at `v₀`; the others are positive there.
  have hxv (j : ι) (hj : 0 < x j) : a j v₀ = 0 := by
    have h : ∑ j, x j * y (a j) = 0 := by simpa using congrArg y hsum
    simp only [← hv₀] at h
    exact (mul_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      mul_nonneg (hx j) (hy j)).1 h j (Finset.mem_univ j))).resolve_left hj.ne'
  -- First project onto the common kernel of the functionals in the support of `x`, then add a
  -- multiple `T * c` of `v₀`.
  obtain ⟨P, hP, hPb⟩ := exists_linearMap_forall_abs_apply_le a hx hsum
  choose Da hDa0 hDa using fun j ↦ hPb (a j)
  choose Db hDb0 hDb using fun k ↦ hPb (b k)
  set T := ∑ j, (1 + Da j) / (x j + a j v₀)
  have hT (j : ι) : (1 + Da j) / (x j + a j v₀) ≤ T :=
    Finset.single_le_sum (f := fun j ↦ (1 + Da j) / (x j + a j v₀))
      (fun i _ ↦ div_nonneg (by linarith [hDa0 i]) (hpos i).le) (Finset.mem_univ j)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ ↦ div_nonneg (by linarith [hDa0 i]) (hpos i).le
  refine ⟨∑ k, (Db k + T * |b k v₀|),
    Finset.sum_nonneg fun k _ ↦ add_nonneg (hDb0 k) (mul_nonneg hT0 (abs_nonneg _)),
    fun c hc w hw ↦ ⟨w - P w + (T * c) • v₀, fun j ↦ ?_, fun k ↦ ?_⟩⟩
  · simp only [map_add, map_sub, map_smul, smul_eq_mul]
    rcases (hx j).eq_or_lt with hxj | hxj
    · -- Away from the support of `x`, `a j v₀` is positive and the shift by `T * c` suffices.
      have hpos' : 0 < a j v₀ := by simpa [← hxj] using hpos j
      have h1 := (abs_le.1 (hDa j c hc w hw)).2
      have h2 : (1 + Da j) * c ≤ T * c * a j v₀ := by
        have h : (1 + Da j) / a j v₀ ≤ T := by simpa [← hxj] using hT j
        rw [div_le_iff₀ hpos'] at h
        nlinarith
      nlinarith [hw j]
    · -- On the support of `x`, both `a j (w - P w)` and `a j v₀` vanish.
      rw [hP w j hxj, hxv j hxj]
      simp
  · have hk : b k (w - (w - P w + (T * c) • v₀)) = b k (P w) - T * c * b k v₀ := by
      simp only [map_sub, map_add, map_smul, smul_eq_mul]
      ring
    have h2 : |T * c * b k v₀| = T * |b k v₀| * c := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hT0]
      ring
    have h3 : Db k + T * |b k v₀| ≤ ∑ k, (Db k + T * |b k v₀|) :=
      Finset.single_le_sum (f := fun k ↦ Db k + T * |b k v₀|)
        (fun k _ ↦ add_nonneg (hDb0 k) (mul_nonneg hT0 (abs_nonneg _))) (Finset.mem_univ k)
    rw [hk]
    calc |b k (P w) - T * c * b k v₀| ≤ |b k (P w)| + |T * c * b k v₀| := abs_sub _ _
      _ ≤ (Db k + T * |b k v₀|) * c := by rw [h2]; nlinarith [hDb k c hc w hw]
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hc

end TauCeti
