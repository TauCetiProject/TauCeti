/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.Algebra.Module.ZLattice.Covolume
import TauCeti.Algebra.Module.ZLattice.RiemannSum
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.MulVolume
import TauCeti.NumberTheory.NumberField.Global.Adeles.GeneralizedIndex
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.FractionalIdeal

/-!
# Idelic theta sums as Riemann sums

Let `K` be a number field. An idele `x` of `K` has an infinite component `x_∞`, a unit of
`K ⊗ ℝ`, read here in the mixed space `ℝ^{r₁} × ℂ^{r₂}` with its sup norm, and a finite component
`x_f`, a finite idele. For a finite idele `d` and a real `r`, the **adelic tent** is

```text
tent_{d,r}(x) = max (r - dist (x_∞, 1)) 0   if d (x_f - 1) ∈ Ô_K,   and 0 otherwise,
```

and the **theta sum** of an idele `b` is the sum of the tent over the coset of `b` modulo the
principal ideles, `Θ_r(b) = ∑_{γ ∈ Kˣ} tent_{d,r}(γ b)`. Only finitely many terms are nonzero, and
`Θ_r` is invariant under the principal ideles, so it is a function on the idele class group.

The main theorem says that for `r ≤ 1` the theta sum depends, up to an error, only on the module
`|b| = |N_{K ⊗ ℝ/ℝ}(b_∞)| · |b_f|` of `b` (`TauCeti.GlobalNumberFields.ideleNorm`): there are
`δ > 0` and `C > 0` such that for every `l > 0` some real `i` satisfies

```text
|i - Θ_{r/3}(b)| ≤ C · l ^ δ · Θ_r(b)      for every idele b with |b| = l.
```

The proof reads `Θ_r(b)` as a lattice sum. The elements `γ ∈ K` with `d (γ b_f - 1) ∈ Ô_K` form a
coset of the fractional ideal `𝔞` of `(d b_f)⁻¹`, so the points `γ b_∞` form a translate of the
lattice `Λ = b_∞ 𝔞` of the mixed space, of covolume `|b| · [d]⁻¹ · 2^{-r₂} √|d_K|`; `γ = 0` does not
contribute because the tent vanishes at `0` when `r ≤ 1`. By Minkowski's theorem `Λ` contains a
nonzero vector `b_∞ a` of norm `O(|b| ^ (1/n))`, `n = [K : ℚ]`, and multiplying it by an integral
basis gives `n` independent vectors of `Λ` of the same size, so `Λ` has a fundamental domain of
radius `h = O(|b| ^ (1/n))`, whatever the shape of `b_∞`. The theta sum at radius `r/3` is then a
Riemann sum for an integral that depends only on `|b|`, with an error of `h` times the number of
points of the lattice coset in the `h`-neighbourhood of the ball of radius `r/3`; once `h ≤ r/3`
these points lie in the ball of radius `2r/3`, where the tent of radius `r` is at least `r/3`, so
the error is at most `3h/r · Θ_r(b)`.

## Main definitions

* `TauCeti.GlobalNumberFields.adelicTent`: the adelic tent `tent_{d,r}`.
* `TauCeti.GlobalNumberFields.thetaSum`: the theta sum `Θ_r`.

## Main results

* `TauCeti.GlobalNumberFields.adelicTent_pos_iff`: where the tent is positive.
* `TauCeti.GlobalNumberFields.hasFiniteSupport_adelicTent_unitEmbedding_mul`: the theta sum has
  finitely many nonzero terms.
* `TauCeti.GlobalNumberFields.thetaSum_unitEmbedding_mul`: the theta sum is invariant under the
  principal ideles.
* `TauCeti.GlobalNumberFields.exists_abs_sub_thetaSum_le_mul_rpow`: the theta sum at radius
  `r/3` depends only on the module, up to `C · |b| ^ δ` times the theta sum at radius `r`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions* (1950), in
  Cassels–Fröhlich, *Algebraic Number Theory*, Chapter XV, §4.
* S. Lang, *Algebraic Number Theory*, 2nd ed., Chapters V and VI (Minkowski's first theorem,
  lattice points in expanding domains).
* The route of the proof, a Riemann sum whose boundary terms at radius `r/3` are bounded by the
  sum at radius `r`, is that of the formal proof in grh-lean (https://github.com/lsernau/grh-lean,
  folder `grh` at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `src/Lib/ClassField/HeckeL/IdelicThetaSum`; Apache 2.0, Copyright 2026 Anthropic, PBC). The
  definitions and proofs here are written independently of that code.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Metric Module Set
  Function
open scoped NNReal nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The adelic tent and the theta sum -/

open scoped Classical in
/-- **The adelic tent** of a finite idele `d` and a radius `r`: at an idele `x` it is
`max (r - dist (x_∞, 1)) 0` if `d (x_f - 1)` is integral at every finite place, and `0` otherwise.
The infinite component `x_∞` is read in the mixed space `ℝ^{r₁} × ℂ^{r₂}`, with its sup norm. -/
def adelicTent (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ) (x : IdeleGroup (𝓞 K) K) : ℝ :=
  if (d : FiniteAdeleRing (𝓞 K) K) * ((x : AdeleRing (𝓞 K) K).2 - 1) ∈
      FiniteAdeleRing.integralAdeles (𝓞 K) K then
    max (r - dist (InfiniteAdeleRing.ringEquiv_mixedSpace K (x : AdeleRing (𝓞 K) K).1) 1) 0
  else 0

open scoped Classical in
/-- The defining formula of the adelic tent. -/
theorem adelicTent_def (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ) (x : IdeleGroup (𝓞 K) K) :
    adelicTent d r x =
      if (d : FiniteAdeleRing (𝓞 K) K) * ((x : AdeleRing (𝓞 K) K).2 - 1) ∈
          FiniteAdeleRing.integralAdeles (𝓞 K) K then
        max (r - dist (InfiniteAdeleRing.ringEquiv_mixedSpace K (x : AdeleRing (𝓞 K) K).1) 1) 0
      else 0 :=
  (rfl)

/-- The adelic tent is nonnegative. -/
theorem adelicTent_nonneg (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ) (x : IdeleGroup (𝓞 K) K) :
    0 ≤ adelicTent d r x := by
  rw [adelicTent_def]
  split_ifs
  exacts [le_max_right _ _, le_rfl]

/-- The adelic tent increases with the radius. -/
theorem adelicTent_mono (d : (FiniteAdeleRing (𝓞 K) K)ˣ) {r r' : ℝ} (h : r ≤ r')
    (x : IdeleGroup (𝓞 K) K) : adelicTent d r x ≤ adelicTent d r' x := by
  simp only [adelicTent_def]
  split_ifs
  exacts [max_le_max (by linarith) le_rfl, le_rfl]

open scoped Classical in
/-- **Where the adelic tent is positive**: exactly at the ideles `x` with `d (x_f - 1)` integral
and `x_∞` at distance less than `r` from `1`. -/
theorem adelicTent_pos_iff {d : (FiniteAdeleRing (𝓞 K) K)ˣ} {r : ℝ} {x : IdeleGroup (𝓞 K) K} :
    0 < adelicTent d r x ↔
      (d : FiniteAdeleRing (𝓞 K) K) * ((x : AdeleRing (𝓞 K) K).2 - 1) ∈
          FiniteAdeleRing.integralAdeles (𝓞 K) K ∧
        dist (InfiniteAdeleRing.ringEquiv_mixedSpace K (x : AdeleRing (𝓞 K) K).1) 1 < r := by
  rw [adelicTent_def]
  split_ifs with h <;> simp [h]

open scoped Classical in
/-- The adelic tent of a nonpositive radius vanishes. -/
theorem adelicTent_of_nonpos (d : (FiniteAdeleRing (𝓞 K) K)ˣ) {r : ℝ} (hr : r ≤ 0)
    (x : IdeleGroup (𝓞 K) K) : adelicTent d r x = 0 :=
  (adelicTent_nonneg d r x).antisymm' <| not_lt.1 fun h ↦
    (adelicTent_pos_iff.1 h).2.not_ge (hr.trans dist_nonneg)

/-- **The idelic theta sum** `Θ_r(b) = ∑_{γ ∈ Kˣ} tent_{d,r}(γ b)`: the sum of the adelic tent over
the coset of `b` modulo the principal ideles. Only finitely many terms are nonzero
(`TauCeti.GlobalNumberFields.hasFiniteSupport_adelicTent_unitEmbedding_mul`). -/
def thetaSum (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ) (b : IdeleGroup (𝓞 K) K) : ℝ :=
  ∑' γ : Kˣ, adelicTent d r (IdeleGroup.unitEmbedding (𝓞 K) K γ * b)

/-- The defining formula of the theta sum. -/
theorem thetaSum_def (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ) (b : IdeleGroup (𝓞 K) K) :
    thetaSum d r b = ∑' γ : Kˣ, adelicTent d r (IdeleGroup.unitEmbedding (𝓞 K) K γ * b) :=
  (rfl)

/-- The theta sum is nonnegative. -/
theorem thetaSum_nonneg (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ) (b : IdeleGroup (𝓞 K) K) :
    0 ≤ thetaSum d r b :=
  tsum_nonneg fun _ ↦ adelicTent_nonneg _ _ _

/-- The theta sum of a nonpositive radius vanishes. -/
theorem thetaSum_of_nonpos (d : (FiniteAdeleRing (𝓞 K) K)ˣ) {r : ℝ} (hr : r ≤ 0)
    (b : IdeleGroup (𝓞 K) K) : thetaSum d r b = 0 := by
  simp [thetaSum_def, adelicTent_of_nonpos d hr]

/-- **The theta sum is invariant under the principal ideles.** -/
@[simp]
theorem thetaSum_unitEmbedding_mul (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ) (a : Kˣ)
    (b : IdeleGroup (𝓞 K) K) :
    thetaSum d r (IdeleGroup.unitEmbedding (𝓞 K) K a * b) = thetaSum d r b := by
  simp only [thetaSum_def, ← mul_assoc, ← map_mul]
  exact (Equiv.mulRight a).tsum_eq fun γ ↦ adelicTent d r (IdeleGroup.unitEmbedding (𝓞 K) K γ * b)

/-! ### The lattice of a theta sum -/

open scoped Classical in
/-- The tent of radius `r` around `1` in the mixed space. -/
private def tent (r : ℝ) (y : mixedSpace K) : ℝ := max (r - dist y 1) 0

open scoped Classical in
private theorem tent_def (r : ℝ) (y : mixedSpace K) : tent r y = max (r - dist y 1) 0 := (rfl)

private theorem tent_nonneg (r : ℝ) (y : mixedSpace K) : 0 ≤ tent r y :=
  le_max_right _ _

/-- The tent of radius `r ≤ 1` vanishes at `0`, which lies at distance `1` from `1`. -/
private theorem tent_zero {r : ℝ} (hr : r ≤ 1) : tent r (0 : mixedSpace K) = 0 := by
  classical
  simp [tent_def, hr]

open scoped Classical in
private theorem lipschitzWith_tent (r : ℝ) : LipschitzWith 1 (tent (K := K) r) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [tent_def, tent_def, Real.dist_eq, NNReal.coe_one, one_mul]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [sub_sub_sub_cancel_left, dist_comm x y]
  exact abs_dist_sub_le y x 1

open scoped Classical in
private theorem support_tent (r : ℝ) : support (tent (K := K) r) = ball 1 r := by
  ext y
  simp [tent_def, mem_ball, not_le]

private theorem hasCompactSupport_tent (r : ℝ) : HasCompactSupport (tent (K := K) r) := by
  classical
  exact HasCompactSupport.intro (isCompact_closedBall (1 : mixedSpace K) r) fun y hy ↦
    by_contra fun h ↦ hy (ball_subset_closedBall ((support_tent (K := K) r) ▸ h : y ∈ ball 1 r))

open scoped Classical in
/-- On the ball of radius `2r/3` the tent of radius `r` is at least `r/3`. -/
private theorem div_three_le_tent {r : ℝ} {y : mixedSpace K} (hy : dist y 1 ≤ 2 * r / 3) :
    r / 3 ≤ tent r y :=
  le_max_of_le_left (by linarith)

/-- The infinite component of an idele, as a unit of the mixed space. -/
private def infUnit (b : IdeleGroup (𝓞 K) K) : (mixedSpace K)ˣ :=
  Units.map ((InfiniteAdeleRing.ringEquiv_mixedSpace K).toMonoidHom.comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) b

private theorem coe_infUnit (b : IdeleGroup (𝓞 K) K) :
    (infUnit b : mixedSpace K) =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (b : AdeleRing (𝓞 K) K).1 :=
  (rfl)

/-- The elements `γ ∈ K` whose idele `γ b` satisfies the finite condition of the tent,
`d (γ b_f - 1) = d b_f γ - d ∈ Ô`. -/
private def thetaCoset (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (b : IdeleGroup (𝓞 K) K) : Set K :=
  {γ | ((d * IdeleGroup.toFiniteIdele (𝓞 K) K b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    FiniteAdeleRing (𝓞 K) K) * algebraMap K _ γ - d ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K}

private theorem mem_thetaCoset {d : (FiniteAdeleRing (𝓞 K) K)ˣ} {b : IdeleGroup (𝓞 K) K}
    {γ : K} : γ ∈ thetaCoset d b ↔
      ((d * IdeleGroup.toFiniteIdele (𝓞 K) K b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K) * algebraMap K _ γ - d ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K :=
  Iff.rfl

/-- The fractional ideal `𝔞` of the finite idele `(d b_f)⁻¹`: the elements `α ∈ K` with
`d b_f α` integral. -/
private def thetaIdeal (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (b : IdeleGroup (𝓞 K) K) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FiniteAdeleRing.toFractionalIdeal (d * IdeleGroup.toFiniteIdele (𝓞 K) K b)⁻¹

private theorem mem_thetaIdeal {d : (FiniteAdeleRing (𝓞 K) K)ˣ} {b : IdeleGroup (𝓞 K) K} {α : K} :
    α ∈ (thetaIdeal d b : FractionalIdeal (𝓞 K)⁰ K) ↔
      ((d * IdeleGroup.toFiniteIdele (𝓞 K) K b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K) * algebraMap K _ α ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K := by
  rw [thetaIdeal, ← FiniteAdeleRing.algebraMap_mem_finiteAdelicIdeal_iff,
    FiniteAdeleRing.mem_finiteAdelicIdeal_iff _ rfl, inv_inv]

/-- The set `thetaCoset d b` is a coset of `𝔞`: differences of its elements lie in `𝔞`. -/
private theorem sub_mem_thetaIdeal {d : (FiniteAdeleRing (𝓞 K) K)ˣ} {b : IdeleGroup (𝓞 K) K}
    {γ γ₀ : K} (hγ : γ ∈ thetaCoset d b) (hγ₀ : γ₀ ∈ thetaCoset d b) :
    γ - γ₀ ∈ (thetaIdeal d b : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_thetaIdeal, map_sub, mul_sub,
    ← sub_sub_sub_cancel_right _ _ (d : FiniteAdeleRing (𝓞 K) K)]
  exact sub_mem hγ hγ₀

/-- The set `thetaCoset d b` is stable under translation by `𝔞`. -/
private theorem add_mem_thetaCoset {d : (FiniteAdeleRing (𝓞 K) K)ˣ} {b : IdeleGroup (𝓞 K) K}
    {γ₀ α : K} (hγ₀ : γ₀ ∈ thetaCoset d b)
    (hα : α ∈ (thetaIdeal d b : FractionalIdeal (𝓞 K)⁰ K)) : γ₀ + α ∈ thetaCoset d b := by
  rw [mem_thetaCoset, map_add, mul_add, add_sub_right_comm]
  exact add_mem hγ₀ (mem_thetaIdeal.1 hα)

/-- By strong approximation the set `thetaCoset d b` is nonempty. -/
private theorem nonempty_thetaCoset (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (b : IdeleGroup (𝓞 K) K) :
    (thetaCoset d b).Nonempty := by
  set e := d * IdeleGroup.toFiniteIdele (𝓞 K) K b
  obtain ⟨γ, hγ⟩ := FiniteAdeleRing.exists_sub_algebraMap_mem_finiteAdelicIdeal
    (FiniteAdeleRing.toFractionalIdeal e⁻¹)
    (((e⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) * d)
  rw [FiniteAdeleRing.mem_finiteAdelicIdeal_iff _ rfl, inv_inv, mul_sub,
    Units.mul_inv_cancel_left] at hγ
  refine ⟨γ, ?_⟩
  rw [mem_thetaCoset, ← neg_sub]
  exact neg_mem hγ

open scoped Classical in
/-- The tent of `γ b` is read off from `γ`: the finite condition is `γ ∈ thetaCoset d b` and the
infinite component is `b_∞ σ(γ)`. -/
private theorem adelicTent_unitEmbedding_mul (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ) (γ : Kˣ)
    (b : IdeleGroup (𝓞 K) K) :
    adelicTent d r (IdeleGroup.unitEmbedding (𝓞 K) K γ * b) =
      (thetaCoset d b).indicator (fun γ ↦ tent r ((infUnit b : mixedSpace K) * mixedEmbedding K γ))
        γ := by
  have hf : (d : FiniteAdeleRing (𝓞 K) K) *
      (((IdeleGroup.unitEmbedding (𝓞 K) K γ * b : IdeleGroup (𝓞 K) K) :
        AdeleRing (𝓞 K) K).2 - 1) =
      ((d * IdeleGroup.toFiniteIdele (𝓞 K) K b : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K) * algebraMap K _ γ - d := by
    rw [Units.val_mul, IdeleGroup.val_unitEmbedding_apply, Prod.snd_mul,
      AdeleRing.algebraMap_snd_def, Units.val_mul, IdeleGroup.coe_toFiniteIdele]
    ring
  have hi : InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((IdeleGroup.unitEmbedding (𝓞 K) K γ * b : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 =
      (infUnit b : mixedSpace K) * mixedEmbedding K γ := by
    rw [Units.val_mul, IdeleGroup.val_unitEmbedding_apply, Prod.fst_mul, map_mul,
      AdeleRing.algebraMap_fst_def, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      coe_infUnit, mul_comm]
  rw [adelicTent_def, hf, hi, Set.indicator_apply, mem_thetaCoset, tent_def]

/-- Multiplication by the inverse of a unit of the mixed space. -/
private def mulInv (u : (mixedSpace K)ˣ) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (Units.mulLeftLinearEquiv ℝ (mixedSpace K) u⁻¹).toContinuousLinearEquiv

private theorem mulInv_apply (u : (mixedSpace K)ˣ) (y : mixedSpace K) :
    (mulInv u).toLinearMap y = ((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) * y :=
  (rfl)

open scoped Classical in
/-- The lattice `Λ = b_∞ 𝔞` of the mixed space, whose translate carries the theta sum of `b`. -/
private def thetaLattice (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (b : IdeleGroup (𝓞 K) K) :
    Submodule ℤ (mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K (thetaIdeal d b)) (mulInv (infUnit b)).toLinearMap

open scoped Classical in
private instance (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (b : IdeleGroup (𝓞 K) K) :
    DiscreteTopology (thetaLattice d b) := by
  unfold thetaLattice
  infer_instance

open scoped Classical in
private instance (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (b : IdeleGroup (𝓞 K) K) :
    IsZLattice ℝ (thetaLattice d b) := by
  unfold thetaLattice
  infer_instance

private theorem mem_thetaLattice {d : (FiniteAdeleRing (𝓞 K) K)ˣ} {b : IdeleGroup (𝓞 K) K}
    {y : mixedSpace K} :
    y ∈ thetaLattice d b ↔ ∃ α ∈ (thetaIdeal d b : FractionalIdeal (𝓞 K)⁰ K),
      (infUnit b : mixedSpace K) * mixedEmbedding K α = y := by
  classical
  rw [thetaLattice, ← SetLike.mem_coe, ZLattice.coe_comap, mem_preimage, SetLike.mem_coe,
    mem_idealLattice]
  refine exists_congr fun α ↦ and_congr_right fun _ ↦ ?_
  rw [mulInv_apply]
  constructor
  · rintro h
    rw [h, Units.mul_inv_cancel_left]
  · rintro rfl
    rw [Units.inv_mul_cancel_left]

/-- The bijection `α ↦ b_∞ σ(α)` from `𝔞` onto `Λ`. -/
private theorem bijective_mul_mixedEmbedding (d : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (b : IdeleGroup (𝓞 K) K) :
    Bijective fun α : (thetaIdeal d b : FractionalIdeal (𝓞 K)⁰ K) ↦ (⟨_,
      mem_thetaLattice.2 ⟨α, α.property, rfl⟩⟩ : thetaLattice d b) :=
  ⟨fun _ _ h ↦ Subtype.ext <| mixedEmbedding_injective K <|
    (infUnit b).isUnit.mul_right_injective (congrArg Subtype.val h), fun ⟨_, hy⟩ ↦
      let ⟨α, hα, hαy⟩ := mem_thetaLattice.1 hy
      ⟨⟨α, hα⟩, Subtype.ext hαy⟩⟩

/-- **The theta sum as a lattice sum.** For `r ≤ 1` and `γ₀ ∈ thetaCoset d b`, `Θ_r(b)` is the sum
of the tent of radius `r` over the translate `b_∞ σ(γ₀) + Λ` of the lattice `Λ = b_∞ 𝔞`; the
point `0`, which comes from `γ = 0`, does not contribute since `r ≤ 1`. -/
private theorem thetaSum_eq_tsum_tent (d : (FiniteAdeleRing (𝓞 K) K)ˣ) {r : ℝ} (hr : r ≤ 1)
    (b : IdeleGroup (𝓞 K) K) {γ₀ : K} (hγ₀ : γ₀ ∈ thetaCoset d b) :
    thetaSum d r b = ∑' ℓ : thetaLattice d b,
      tent r ((infUnit b : mixedSpace K) * mixedEmbedding K γ₀ + (ℓ : mixedSpace K)) := by
  set u : mixedSpace K := (infUnit b : mixedSpace K)
  set G := (thetaCoset d b).indicator fun γ ↦ tent r (u * mixedEmbedding K γ)
  -- Pass from `Kˣ` to `K`, where the term at `γ = 0` vanishes since `tent r 0 = 0`.
  have h₁ : thetaSum d r b = ∑' γ : K, G γ := by
    rw [thetaSum_def, ← Units.val_injective.tsum_eq (f := G)]
    · exact tsum_congr fun γ ↦ adelicTent_unitEmbedding_mul d r γ b
    · intro γ hγ
      rcases eq_or_ne γ 0 with rfl | h0
      · exact absurd hγ (by simp [G, tent_zero hr])
      · exact ⟨Units.mk0 γ h0, rfl⟩
  -- Then to the coset `γ₀ + 𝔞`, which contains the support of `G`.
  have h₂ : ∑' γ : K, G γ = ∑' α : (thetaIdeal d b : FractionalIdeal (𝓞 K)⁰ K),
      tent r (u * mixedEmbedding K γ₀ + u * mixedEmbedding K α) := by
    rw [← ((add_right_injective γ₀).comp Subtype.val_injective).tsum_eq (f := G)]
    · refine tsum_congr fun α ↦ ?_
      simp only [G, comp_apply, Set.indicator_of_mem (add_mem_thetaCoset hγ₀ α.property), map_add,
        mul_add]
    · intro γ hγ
      exact ⟨⟨γ - γ₀, sub_mem_thetaIdeal (Set.mem_of_indicator_ne_zero hγ) hγ₀⟩,
        add_sub_cancel _ _⟩
  -- Finally to the lattice `Λ`, through the bijection `𝔞 → Λ`.
  rw [h₁, h₂, ← (bijective_mul_mixedEmbedding d b).injective.tsum_eq]
  rw [(bijective_mul_mixedEmbedding d b).surjective.range_eq]
  exact subset_univ _

/-- The constant `[d]⁻¹ · 2^{-r₂} √|d_K|`: the covolume of `Λ = b_∞ 𝔞` is `|b|` times it. -/
private def thetaCovolumeConst (d : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℝ :=
  (FiniteAdeleRing.genIndex K d : ℝ)⁻¹ *
    ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)|)

private theorem thetaCovolumeConst_pos (d : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    0 < thetaCovolumeConst d := by
  have h₁ : (0 : ℝ) < FiniteAdeleRing.genIndex K d := by
    exact_mod_cast FiniteAdeleRing.genIndex_units_pos d
  have h₂ : 0 < |(discr K : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  unfold thetaCovolumeConst
  positivity

open scoped Classical in
/-- **The covolume of `Λ = b_∞ 𝔞`** is `|b| · [d]⁻¹ · 2^{-r₂} √|d_K|`: multiplication by `b_∞`
scales volumes by `|N(b_∞)|`, the lattice of `𝔞` has covolume `N(𝔞) · 2^{-r₂} √|d_K|`, and
`N(𝔞) = [d]⁻¹ · |b_f|`. -/
private theorem covolume_thetaLattice (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (b : IdeleGroup (𝓞 K) K) :
    ZLattice.covolume (thetaLattice d b) = ((ideleNorm b : ℝ≥0) : ℝ) * thetaCovolumeConst d := by
  have hdet : |(mulInv (infUnit b)).toLinearMap.det| =
      (mixedEmbedding.norm (infUnit b : mixedSpace K))⁻¹ := by
    have : (mulInv (infUnit b)).toLinearMap =
        Algebra.lmul ℝ (mixedSpace K) ((infUnit b)⁻¹ : (mixedSpace K)ˣ) :=
      LinearMap.ext fun y ↦ (mulInv_apply _ y).trans rfl
    rw [this, ← Algebra.norm_apply, abs_algebraNorm, map_units_inv]
  have hN : (FractionalIdeal.absNorm (thetaIdeal d b : FractionalIdeal (𝓞 K)⁰ K) : ℝ) =
      (FiniteAdeleRing.genIndex K d : ℝ)⁻¹ *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(v.ideleFiniteCoord b : v.adicCompletion K)‖ := by
    rw [thetaIdeal, ← FiniteAdeleRing.genIndex_units, mul_inv, Units.val_mul, map_mul,
      map_units_inv, map_units_inv, Rat.cast_mul, Rat.cast_inv, Rat.cast_inv,
      FiniteAdeleRing.genIndex_units_eq_inv_finprod_norm (IdeleGroup.toFiniteIdele (𝓞 K) K b),
      inv_inv]
    simp [HeightOneSpectrum.coe_ideleFiniteCoord]
  refine (ZLattice.covolume_comap_continuousLinearEquiv (idealLattice K (thetaIdeal d b))
    (mulInv (infUnit b)) volume).trans ?_
  rw [covolume_idealLattice, hdet, inv_inv, hN, coe_ideleNorm_eq_mixedEmbedding_norm_mul,
    ← coe_infUnit, thetaCovolumeConst]
  ring

/-- The `ℝ`-basis of the mixed space given by an integral basis of `K`, indexed by `Fin n`. -/
private def finLatticeBasis (K : Type*) [Field K] [NumberField K] :
    Basis (Fin (finrank ℝ (mixedSpace K))) ℝ (mixedSpace K) :=
  (latticeBasis K).reindex ((latticeBasis K).indexEquiv (Module.finBasis ℝ (mixedSpace K)))

/-- The vectors of `finLatticeBasis K` are images of algebraic integers. -/
private theorem exists_finLatticeBasis_eq (j : Fin (finrank ℝ (mixedSpace K))) :
    ∃ ω : 𝓞 K, finLatticeBasis K j = mixedEmbedding K (ω : K) :=
  ⟨_, by rw [finLatticeBasis, Basis.reindex_apply, latticeBasis_apply, integralBasis_apply]⟩

open scoped Classical in
/-- **Independent vectors of `Λ` as short as a given one.** The products of a nonzero vector
`x = b_∞ σ(a)` of `Λ = b_∞ 𝔞` with an integral basis are `n = [K : ℚ]` linearly independent vectors
of `Λ`, of norm at most `‖x‖` times the sum of the norms of the basis, since `a 𝓞_K ⊆ 𝔞`. -/
private theorem exists_linearIndependent_mem_thetaLattice {d : (FiniteAdeleRing (𝓞 K) K)ˣ}
    {b : IdeleGroup (𝓞 K) K} {x : mixedSpace K} (hxL : x ∈ thetaLattice d b) (hx0 : x ≠ 0) :
    ∃ v : Fin (finrank ℝ (mixedSpace K)) → mixedSpace K, (∀ j, v j ∈ thetaLattice d b) ∧
      LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ ‖x‖ * ∑ i, ‖finLatticeBasis K i‖ := by
  obtain ⟨a, ha, rfl⟩ := mem_thetaLattice.1 hxL
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx0
  have hunit : IsUnit ((infUnit b : mixedSpace K) * mixedEmbedding K a) :=
    (infUnit b).isUnit.mul ((Ne.isUnit ha0).map (mixedEmbedding K))
  refine ⟨fun j ↦ ((infUnit b : mixedSpace K) * mixedEmbedding K a) * finLatticeBasis K j,
    fun j ↦ ?_, (finLatticeBasis K).linearIndependent.map' (LinearMap.mulLeft ℝ _)
      (LinearMap.ker_eq_bot.2 hunit.mul_right_injective), fun j ↦ ?_⟩
  · obtain ⟨ω, hω⟩ := exists_finLatticeBasis_eq (K := K) j
    refine mem_thetaLattice.2 ⟨a * ω, ?_, by simp only [hω, map_mul, mul_assoc]⟩
    simpa [Algebra.smul_def, mul_comm] using
      (thetaIdeal d b : FractionalIdeal (𝓞 K)⁰ K).coeToSubmodule.smul_mem ω ha
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun i _ ↦ norm_nonneg (finLatticeBasis K i)) (Finset.mem_univ j))
      (norm_nonneg _))

open scoped Classical in
/-- **A fundamental domain of `Λ = b_∞ 𝔞` of radius `O(|b| ^ (1/n))`**, `n = [K : ℚ]`. By
Minkowski's theorem `Λ` has a nonzero vector of norm `O(|b| ^ (1/n))`, and its products with an
integral basis are `n` independent vectors of `Λ` of the same size, whatever the shape of `b_∞`. -/
private theorem exists_isAddFundamentalDomain_thetaLattice (d : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ∃ c₀ > 0, ∀ b : IdeleGroup (𝓞 K) K, ∃ F : Set (mixedSpace K),
      IsAddFundamentalDomain (thetaLattice d b) F volume ∧
        F ⊆ closedBall 0 (c₀ * ((ideleNorm b : ℝ≥0) : ℝ) ^ (finrank ℝ (mixedSpace K) : ℝ)⁻¹) := by
  set n := finrank ℝ (mixedSpace K)
  have hn : 0 < n := finrank_pos
  set W := ∑ j, ‖finLatticeBasis K j‖
  have hW : 0 < W := Finset.sum_pos (fun j _ ↦ norm_pos_iff.2 ((finLatticeBasis K).ne_zero j))
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set vB := volume.real (closedBall (0 : mixedSpace K) 1)
  have hvB : 0 < vB :=
    ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne
  set A := 2 ^ n * thetaCovolumeConst d / vB
  have hA : 0 < A := by have := thetaCovolumeConst_pos d; positivity
  refine ⟨n ^ 2 * W * A ^ (n : ℝ)⁻¹, by positivity, fun b ↦ ?_⟩
  set l := ((ideleNorm b : ℝ≥0) : ℝ)
  have hl : 0 < l := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (ideleNorm b).ne_zero)
  set ρ := (A * l) ^ (n : ℝ)⁻¹
  have hρ : 0 ≤ ρ := by positivity
  -- Minkowski: a nonzero vector of `Λ` of norm at most `ρ`, since `covolume Λ = l κ`.
  obtain ⟨x, hxL, hx0, hxρ⟩ := ZLattice.exists_ne_zero_mem_norm_le (thetaLattice d b) volume hn hρ
    (by
      rw [covolume_thetaLattice, Real.rpow_inv_natCast_pow (by positivity) hn.ne']
      have hvB' : volume.real (closedBall (0 : mixedSpace K) 1) ≠ 0 := hvB.ne'
      exact le_of_eq (by simp only [A, n, l, vB]; field_simp))
  obtain ⟨v, hvL, hv, hvs⟩ := exists_linearIndependent_mem_thetaLattice hxL hx0
  obtain ⟨F, hF, hFs⟩ := ZLattice.exists_isAddFundamentalDomain_subset_closedBall _ volume hvL hv
    fun j ↦ (hvs j).trans (mul_le_mul_of_nonneg_right hxρ hW.le)
  refine ⟨F, hF, hFs.trans (closedBall_subset_closedBall (le_of_eq ?_))⟩
  simp only [ρ, n, W, Real.mul_rpow hA.le hl.le]
  ring

/-! ### Finiteness, monotonicity and the Riemann-sum estimate -/

open scoped Classical in
/-- **The theta sum has finitely many nonzero terms**: only finitely many `γ ∈ Kˣ` have
`tent_{d,r}(γ b) ≠ 0`, because the points `b_∞ σ(γ)` of those `γ` lie in a translate of a discrete
lattice and in the ball of radius `r` about `1`. -/
theorem hasFiniteSupport_adelicTent_unitEmbedding_mul (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ)
    (b : IdeleGroup (𝓞 K) K) :
    HasFiniteSupport fun γ : Kˣ ↦ adelicTent d r (IdeleGroup.unitEmbedding (𝓞 K) K γ * b) := by
  obtain ⟨γ₀, hγ₀⟩ := nonempty_thetaCoset d b
  set u : mixedSpace K := (infUnit b : mixedSpace K)
  set t : mixedSpace K := u * mixedEmbedding K γ₀
  have hψ : Injective fun γ : Kˣ ↦ u * mixedEmbedding K γ := fun γ γ' h ↦ Units.ext <|
    mixedEmbedding_injective K ((infUnit b).isUnit.mul_right_injective h)
  refine (((ZLattice.finite_setOf_add_mem (thetaLattice d b)
    (isBounded_ball (x := (1 : mixedSpace K)) (r := r)) t).image
    fun ℓ : thetaLattice d b ↦ t + ℓ).preimage hψ.injOn).subset fun γ hγ ↦ ?_
  rw [mem_support, adelicTent_unitEmbedding_mul] at hγ
  have hmem := sub_mem_thetaIdeal (Set.mem_of_indicator_ne_zero hγ) hγ₀
  have ht : t + u * mixedEmbedding K ((γ : K) - γ₀) = u * mixedEmbedding K γ := by
    simp only [t, map_sub, mul_sub, add_sub_cancel]
  refine ⟨⟨u * mixedEmbedding K ((γ : K) - γ₀), mem_thetaLattice.2 ⟨_, hmem, rfl⟩⟩, ?_, ht⟩
  rw [mem_ofPred_eq, ht, ← support_tent r]
  exact (Set.indicator_apply_ne_zero.1 hγ).2

/-- The theta sum is a sum with finitely many nonzero terms, hence summable. -/
theorem summable_adelicTent_unitEmbedding_mul (d : (FiniteAdeleRing (𝓞 K) K)ˣ) (r : ℝ)
    (b : IdeleGroup (𝓞 K) K) :
    Summable fun γ : Kˣ ↦ adelicTent d r (IdeleGroup.unitEmbedding (𝓞 K) K γ * b) :=
  summable_of_hasFiniteSupport (hasFiniteSupport_adelicTent_unitEmbedding_mul d r b)

/-- The theta sum increases with the radius. -/
theorem thetaSum_mono (d : (FiniteAdeleRing (𝓞 K) K)ˣ) {r r' : ℝ} (h : r ≤ r')
    (b : IdeleGroup (𝓞 K) K) : thetaSum d r b ≤ thetaSum d r' b :=
  (summable_adelicTent_unitEmbedding_mul d r b).tsum_le_tsum (fun _ ↦ adelicTent_mono d h _)
    (summable_adelicTent_unitEmbedding_mul d r' b)

open scoped Classical in
/-- The points of a lattice coset `t + L` within distance `h ≤ r/3` of the ball of radius `r/3`
about `1` lie in the ball of radius `2r/3`, where the tent of radius `r` is at least `r/3`; so they
number at most `3/r` times the sum of that tent over `t + L`. -/
private theorem ncard_le_tsum_tent (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] {r h : ℝ}
    (hr : 0 < r) (hh0 : 0 ≤ h) (hh : h ≤ r / 3) (t : mixedSpace K) :
    ({ℓ : L | t + (ℓ : mixedSpace K) ∈ cthickening h (support (tent (K := K) (r / 3)))}.ncard :
      ℝ) ≤ 3 / r * ∑' ℓ : L, tent r (t + (ℓ : mixedSpace K)) := by
  set S := {ℓ : L | t + (ℓ : mixedSpace K) ∈ cthickening h (support (tent (K := K) (r / 3)))}
  have hsub (ℓ : L) (hℓ : ℓ ∈ S) : dist (t + (ℓ : mixedSpace K)) 1 ≤ 2 * r / 3 := by
    have hS' : cthickening h (support (tent (K := K) (r / 3))) ⊆ closedBall 1 (h + r / 3) := by
      rw [support_tent, ← cthickening_closedBall hh0 (by positivity)]
      exact cthickening_subset_of_subset _ (ball_subset_closedBall (x := (1 : mixedSpace K)))
    have := mem_closedBall.1 (hS' hℓ)
    linarith
  have hS : S.Finite := (ZLattice.finite_setOf_add_mem L (isBounded_closedBall (x := 1)
    (r := 2 * r / 3)) t).subset fun ℓ hℓ ↦ mem_closedBall.2 (hsub ℓ hℓ)
  have hsum : Summable fun ℓ : L ↦ tent r (t + (ℓ : mixedSpace K)) :=
    summable_of_hasFiniteSupport <| (ZLattice.finite_setOf_add_mem L
      (isBounded_ball (x := 1) (r := r)) t).subset fun ℓ hℓ ↦ by
        rwa [mem_ofPred_eq, ← support_tent r]
  have hle : r / 3 * hS.toFinset.card ≤ ∑' ℓ : L, tent r (t + (ℓ : mixedSpace K)) :=
    calc r / 3 * hS.toFinset.card = ∑ _ℓ ∈ hS.toFinset, r / 3 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ ℓ ∈ hS.toFinset, tent r (t + (ℓ : mixedSpace K)) :=
          Finset.sum_le_sum fun ℓ hℓ ↦ div_three_le_tent (hsub ℓ (hS.mem_toFinset.1 hℓ))
      _ ≤ ∑' ℓ : L, tent r (t + (ℓ : mixedSpace K)) := hsum.sum_le_tsum _ fun ℓ _ ↦ tent_nonneg _ _
  rw [Set.ncard_eq_toFinset_card S hS]
  calc (hS.toFinset.card : ℝ) = 3 / r * (r / 3 * hS.toFinset.card) := by field_simp
    _ ≤ 3 / r * ∑' ℓ : L, tent r (t + (ℓ : mixedSpace K)) := by gcongr

open scoped Classical in
/-- **Idelic theta sums are Riemann sums.** Let `d` be a finite idele and `r ≤ 1`. There are
`δ > 0` and `C > 0` such that for every `l > 0` some real `i` satisfies
`|i - Θ_{r/3}(b)| ≤ C · l ^ δ · Θ_r(b)` for every idele `b` of module `|b| = l`: up to this error,
the theta sum of radius `r/3` depends only on the module. -/
theorem exists_abs_sub_thetaSum_le_mul_rpow (d : (FiniteAdeleRing (𝓞 K) K)ˣ) {r : ℝ}
    (hr : r ≤ 1) :
    ∃ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ l > (0 : ℝ), ∃ i : ℝ, ∀ b : IdeleGroup (𝓞 K) K,
      ((ideleNorm b : ℝ≥0) : ℝ) = l → |i - thetaSum d (r / 3) b| ≤ C * l ^ δ * thetaSum d r b := by
  rcases le_or_gt r 0 with hr0 | hr0
  · -- Nonpositive radii give vanishing theta sums.
    refine ⟨1, one_pos, 1, one_pos, fun l _ ↦ ⟨0, fun b _ ↦ ?_⟩⟩
    rw [thetaSum_of_nonpos d (by linarith) b, thetaSum_of_nonpos d hr0 b]
    simp
  obtain ⟨c₀, hc₀, hF⟩ := exists_isAddFundamentalDomain_thetaLattice d
  set n := finrank ℝ (mixedSpace K)
  have hn : 0 < n := finrank_pos
  refine ⟨(n : ℝ)⁻¹, by positivity, 3 * c₀ / r, by positivity, fun l hl ↦ ?_⟩
  -- The main term: the integral of the tent of radius `r/3` divided by the covolume `l κ`.
  refine ⟨if c₀ * l ^ (n : ℝ)⁻¹ ≤ r / 3 then
    (∫ y, tent (K := K) (r / 3) y) / (l * thetaCovolumeConst d) else 0, fun b hb ↦ ?_⟩
  have hδ : 0 ≤ c₀ * l ^ (n : ℝ)⁻¹ := by positivity
  split_ifs with hh
  · -- The Riemann-sum estimate over the lattice coset carrying the theta sums.
    obtain ⟨F, hFd, hFs⟩ := hF b
    rw [hb] at hFs
    obtain ⟨γ₀, hγ₀⟩ := nonempty_thetaCoset d b
    rw [thetaSum_eq_tsum_tent d (by linarith) b hγ₀, thetaSum_eq_tsum_tent d hr b hγ₀,
      ← hb, ← covolume_thetaLattice, abs_sub_comm, hb]
    refine (ZLattice.abs_tsum_sub_integral_div_covolume_le volume (thetaLattice d b) hFd hFs
      (lipschitzWith_tent (r / 3)) (hasCompactSupport_tent (r / 3)) _).trans ?_
    calc ((1 : ℝ≥0) : ℝ) * (c₀ * l ^ (n : ℝ)⁻¹) * _
        ≤ c₀ * l ^ (n : ℝ)⁻¹ * (3 / r * _) := by
          rw [NNReal.coe_one, one_mul]
          exact mul_le_mul_of_nonneg_left (ncard_le_tsum_tent _ hr0 hδ hh _) hδ
      _ = 3 * c₀ / r * l ^ (n : ℝ)⁻¹ * _ := by ring
  · -- For large modules the bound holds with `i = 0`, since `Θ_{r/3} ≤ Θ_r`.
    have h₁ : 1 ≤ 3 * c₀ / r * l ^ (n : ℝ)⁻¹ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr0]
      linarith [not_le.1 hh]
    rw [zero_sub, abs_neg, abs_of_nonneg (thetaSum_nonneg d _ b)]
    calc thetaSum d (r / 3) b ≤ thetaSum d r b := thetaSum_mono d (by linarith) b
      _ ≤ 3 * c₀ / r * l ^ (n : ℝ)⁻¹ * thetaSum d r b :=
          le_mul_of_one_le_left (thetaSum_nonneg d r b) h₁

end TauCeti.GlobalNumberFields
