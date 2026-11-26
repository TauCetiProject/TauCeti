/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.Calculus.Taylor.Basic
import TauCeti.LinearAlgebra.LinearMap.Coprod

/-!
# Approximate solutions of every finite order of a family of equations

Let `F : ℝ × E → G` be a family of equations `F (h, x) = 0` in a small parameter `h`, with a
solution `x₀` at `h = 0`. When the derivative `Λ` of `x ↦ F (0, x)` at `x₀` is onto, the solution
can be continued to every finite order in `h`: for each `N`, if `F` is `C^(N+1)` at `(0, x₀)`, there
is a polynomial profile `x(h) = x₀ + ∑_{i < N} h^(i+1) xᵢ` with residual `F (h, x(h)) = O(h^(N+1))`
(`TauCeti.exists_isBigO_pow_of_surjective`). No complement of the kernel of `Λ` and no continuity
of a right inverse is needed, and neither `E` nor `G` need be complete: only finitely many
coefficients are chosen, each a preimage under `Λ`.

The profile is built one order at a time. If the profile of order `N` has residual
`Φ(h) = O(h^(N+1))`, Taylor's theorem identifies its leading coefficient,
`Φ(h) = h^(N+1) c + O(h^(N+2))` with `c = Φ^(N+1)(0) / (N+1)!`
(`TauCeti.isBigO_sub_pow_smul_iteratedDeriv`), because a polynomial of degree `≤ N` that is
`O(h^(N+1))` vanishes (`TauCeti.eq_zero_of_isBigO_sum_pow_smul`). The correction
`h^(N+1) y` with `Λ y = -c` cancels that coefficient: since `F` is `C²`, the residual changes by
`h^(N+1) Λ y` up to a remainder bounded by the size `O(h)` of the profile's displacement times the
size `O(h^(N+1))` of the correction (`TauCeti.isBigO_sub_sub_pow_smul_fderiv`, from the uniform
quadratic remainder `IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul`).

**The slow-first recursion.** In Taubes's construction of approximate Seiberg–Witten solutions near
a pseudoholomorphic curve, the unknown splits into a slow variable `σ` (a divisor of vortex
zeros) and a fast variable `u`, and the target into a fast and a slow part through a fixed map
`P` and its complement `1 - P`. The derivative is block triangular in the following sense: the
fast column `∂_u F` reaches the whole fast part `P y`, and the slow column `∂_σ F`, read in the
slow part, reaches the whole slow part `y - P y`. Each order is then solved slow first: the slow
correction `τ` cancels the slow part of the coefficient, and the fast correction `g` cancels the
fast part of the coefficient as changed by `τ`
(`LinearMap.surjective_coprod_of_forall_exists_eq`). This gives profiles in both variables to every
finite order (`TauCeti.exists_isBigO_pow_of_forall_exists_eq`). For an equation
`S(h, σ, f) = 0` with `S(0, σ, 0) = 0` and fast variable `f = O(h)`, these statements apply to the
normalized equation `F(h, σ, u) = h⁻¹ S(h, σ, h u)`, once it is extended across `h = 0` to a map
that is `C^(N+1)` at the base point.

## Main results

* `TauCeti.isBigO_sub_sub_pow_smul_fderiv`: correcting a curve through `x₀` by `h^(j+1) y` changes
  the residual by `h^(j+1) Λ y + O(h^(j+2))`.
* `TauCeti.exists_isBigO_pow_of_surjective`: polynomial profiles with residual `O(h^(N+1))` when
  the derivative in the unknown is onto.
* `TauCeti.exists_isBigO_pow_of_forall_exists_eq`: profiles of every finite order for a slow and a
  fast variable, under the slow-first hypotheses.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *GR = SW: Counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

open Asymptotics Filter Topology Finset
open scoped Nat

namespace TauCeti

section Profile

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- The base solution has residual `F (h, x₀) = O(h)`. -/
private theorem isBigO_apply_zero_pow_one {F : ℝ × E → G} {x₀ : E}
    (hF : DifferentiableAt ℝ F (0, x₀)) (h₀ : F (0, x₀) = 0) :
    (fun h : ℝ ↦ F (h, x₀)) =O[𝓝 0] fun h ↦ h ^ 1 := by
  have hlim : Tendsto (fun h : ℝ ↦ (h, x₀)) (𝓝 0) (𝓝 (0, x₀)) :=
    ((continuous_id.prodMk continuous_const).tendsto 0)
  refine ((hF.isBigO_sub.comp_tendsto hlim).trans (IsBigO.of_bound 1 ?_)).congr_left ?_
  · exact Eventually.of_forall fun h ↦ by simp [Prod.norm_def]
  · intro h
    simp [h₀]

/-- **The linearized change of the residual.** Let `F` be `C²` at `(0, x₀)` and let `X` be a curve
through `x₀` at `h = 0`, differentiable there. Correcting `X` by `h^(j+1) y` changes the residual
by `h^(j+1) Λ y`, where `Λ` is the derivative of `x ↦ F (0, x)` at `x₀`, up to `O(h^(j+2))`. -/
theorem isBigO_sub_sub_pow_smul_fderiv {F : ℝ × E → G} {x₀ : E}
    (hF : ContDiffAt ℝ 2 F (0, x₀)) {X : ℝ → E} (hX : DifferentiableAt ℝ X 0) (hX0 : X 0 = x₀)
    (j : ℕ) (y : E) :
    (fun h ↦ F (h, X h + h ^ (j + 1) • y) - F (h, X h) -
      h ^ (j + 1) • fderiv ℝ (fun x ↦ F (0, x)) x₀ y) =O[𝓝 0] fun h ↦ h ^ (j + 2) := by
  -- The quadratic remainder of `F` at `(0, x₀)`, uniformly near that point.
  obtain ⟨δ, hδ, L, hL⟩ :=
    (isCompact_singleton (x := (0 : ℝ))).exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul
      (F := fun _ : ℝ ↦ F) (x := fun _ ↦ ((0 : ℝ), x₀))
      (fun p _ ↦ hF.comp (p, ((0 : ℝ), x₀)) contDiffAt_snd) continuousOn_const
  -- The displacements of the corrected and uncorrected profiles from `(0, x₀)` are `O(h)`.
  set a : ℝ → ℝ × E := fun h ↦ (h, X h + h ^ (j + 1) • y - x₀)
  set b : ℝ → ℝ × E := fun h ↦ (h, X h - x₀)
  have ha : a =O[𝓝 0] fun h ↦ h := by
    have hda : DifferentiableAt ℝ a 0 := by fun_prop
    simpa [a, hX0] using hda.isBigO_sub
  have hb : b =O[𝓝 0] fun h ↦ h := by
    have hdb : DifferentiableAt ℝ b 0 := by fun_prop
    simpa [b, hX0] using hdb.isBigO_sub
  have hsmall : ∀ᶠ h in 𝓝 (0 : ℝ), ‖a h‖ ≤ δ ∧ ‖b h‖ ≤ δ := by
    have hta := (ha.trans_tendsto tendsto_id).norm
    have htb := (hb.trans_tendsto tendsto_id).norm
    simp only [norm_zero] at hta htb
    exact (hta.eventually (Iic_mem_nhds hδ)).and (htb.eventually (Iic_mem_nhds hδ))
  have hab : (fun h ↦ (‖a h‖ + ‖b h‖) * ‖h ^ (j + 1)‖) =O[𝓝 0] fun h ↦ h * h ^ (j + 1) :=
    (ha.norm_left.add hb.norm_left).mul (isBigO_refl _ _).norm_left
  refine (IsBigO.of_bound (|L| * ‖y‖) ?_).trans (hab.congr_right fun h ↦ by ring)
  filter_upwards [hsmall] with h ⟨hah, hbh⟩
  have hrem := hL 0 rfl (a h) (b h) hah hbh
  have hpa : ((0 : ℝ), x₀) + a h = (h, X h + h ^ (j + 1) • y) := by simp [a]
  have hpb : ((0 : ℝ), x₀) + b h = (h, X h) := by simp [b]
  have hab' : a h - b h = (0, h ^ (j + 1) • y) := by
    simp only [a, b, Prod.mk_sub_mk, sub_self]
    congr 1
    abel
  have hnab : ‖((0 : ℝ), h ^ (j + 1) • y)‖ = ‖h ^ (j + 1)‖ * ‖y‖ := by
    rw [Prod.norm_def, norm_zero, norm_smul]
    exact max_eq_right (by positivity)
  rw [hpa, hpb, hab', hnab] at hrem
  rw [fderiv_slice_right (hF.differentiableAt (by norm_num)), ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ← map_smul, Prod.smul_mk, smul_zero]
  rw [norm_mul, norm_norm, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖a h‖ + ‖b h‖)]
  calc _ ≤ L * max ‖a h‖ ‖b h‖ * (‖h ^ (j + 1)‖ * ‖y‖) := hrem
    _ ≤ |L| * (‖a h‖ + ‖b h‖) * (‖h ^ (j + 1)‖ * ‖y‖) := by
        gcongr
        · exact le_abs_self L
        · exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = |L| * ‖y‖ * ((‖a h‖ + ‖b h‖) * ‖h ^ (j + 1)‖) := by ring

/-- **One order of the approximate solution.** If the profile `X` has residual `O(h^(N+1))`, the
correction `h^(N+1) y`, where `y` is a preimage under the slice derivative of minus the leading
coefficient of the residual, gives a residual `O(h^(N+2))`. -/
private theorem isBigO_add_pow_smul {F : ℝ × E → G} {x₀ : E} {N : ℕ}
    (hF : ContDiffAt ℝ (N + 2) F (0, x₀)) {X : ℝ → E} (hX : ContDiff ℝ (N + 2) X)
    (hX0 : X 0 = x₀) (hXres : (fun h ↦ F (h, X h)) =O[𝓝 0] fun h ↦ h ^ (N + 1)) {y : E}
    (hy : fderiv ℝ (fun x ↦ F (0, x)) x₀ y =
      -(((N + 1)! : ℝ)⁻¹ • iteratedDeriv (N + 1) (fun h ↦ F (h, X h)) 0)) :
    (fun h ↦ F (h, X h + h ^ (N + 1) • y)) =O[𝓝 0] fun h ↦ h ^ (N + 2) := by
  -- The leading coefficient of the residual.
  have hΦ : ContDiffAt ℝ (N + 1 + 1) (fun h ↦ F (h, X h)) 0 := by
    have hF' : ContDiffAt ℝ (N + 1 + 1) F (0, X 0) := by
      rw [hX0]
      exact_mod_cast hF
    exact hF'.comp 0 (contDiffAt_id.prodMk (by exact_mod_cast hX.contDiffAt))
  have hc := isBigO_sub_pow_smul_iteratedDeriv hΦ hXres
  -- The correction cancels it, up to the remainder of the linearization.
  have hR := isBigO_sub_sub_pow_smul_fderiv (hF.of_le (by norm_num))
    (hX.differentiable (by norm_num) 0) hX0 N y
  refine (hR.add hc).congr_left fun h ↦ ?_
  rw [hy, smul_neg]
  abel

/-- **Approximate implicit function theorem.** Let `F (0, x₀) = 0`, and let the derivative of
`x ↦ F (0, x)` at `x₀` be onto. If `F` is `C^(N+1)` at `(0, x₀)`, there is a polynomial profile
`x(h) = x₀ + ∑_{i < N} h^(i+1) xᵢ` along which `F (h, x(h)) = O(h^(N+1))` as `h → 0`. -/
theorem exists_isBigO_pow_of_surjective {F : ℝ × E → G} {x₀ : E} {n : WithTop ℕ∞} {N : ℕ}
    (hF : ContDiffAt ℝ n F (0, x₀)) (hN : N + 1 ≤ n) (h₀ : F (0, x₀) = 0)
    (hsurj : Function.Surjective (fderiv ℝ (fun x ↦ F (0, x)) x₀)) :
    ∃ x : ℕ → E, (fun h : ℝ ↦ F (h, x₀ + ∑ i ∈ range N, h ^ (i + 1) • x i)) =O[𝓝 0]
      fun h ↦ h ^ (N + 1) := by
  induction N with
  | zero =>
    refine ⟨0, ?_⟩
    exact by simpa using isBigO_apply_zero_pow_one (hF.differentiableAt fun hn ↦ by
      simp [hn] at hN) h₀
  | succ N ih =>
    obtain ⟨x, hx⟩ := ih (le_trans (by norm_cast; omega) hN)
    set X : ℝ → E := fun h ↦ x₀ + ∑ i ∈ range N, h ^ (i + 1) • x i
    obtain ⟨y, hy⟩ := hsurj
      (-(((N + 1)! : ℝ)⁻¹ • iteratedDeriv (N + 1) (fun h ↦ F (h, X h)) 0))
    refine ⟨Function.update x N y, ?_⟩
    have hupd (h : ℝ) : x₀ + ∑ i ∈ range (N + 1), h ^ (i + 1) • Function.update x N y i =
        X h + h ^ (N + 1) • y := by
      rw [sum_range_succ, Function.update_self, ← add_assoc]
      congr 2
      exact sum_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (mem_range.1 hi).ne]
    simp only [hupd]
    exact isBigO_add_pow_smul (hF.of_le (by exact_mod_cast hN)) (by fun_prop) (by simp) hx hy

end Profile

section SlowFirstProfile

variable {C D Y : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup D]
  [NormedSpace ℝ D] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Profiles of every finite order by the slow-first recursion.** Let `F (0, (σ₀, u₀)) = 0` for
a slow variable `σ ∈ C` and a fast variable `u ∈ D`, and let `P : Y → Y` be a linear map splitting
the target into a fast part `P y` and a slow part `y - P y`. Suppose that the fast partial
derivative `∂_u F` at `(0, (σ₀, u₀))` reaches every fast part, and that the slow partial derivative
`∂_σ F`, read in the slow part, reaches every slow part. If `F` is `C^(N+1)` at `(0, (σ₀, u₀))`,
there are polynomial profiles `σ(h) = σ₀ + ∑_{i < N} h^(i+1) σᵢ` and
`u(h) = u₀ + ∑_{i < N} h^(i+1) uᵢ` along which `F (h, (σ(h), u(h))) = O(h^(N+1))` as `h → 0`. -/
theorem exists_isBigO_pow_of_forall_exists_eq {F : ℝ × (C × D) → Y} {σ₀ : C} {u₀ : D}
    {n : WithTop ℕ∞} {N : ℕ} (hF : ContDiffAt ℝ n F (0, (σ₀, u₀))) (hN : N + 1 ≤ n)
    (h₀ : F (0, (σ₀, u₀)) = 0) (P : Y →ₗ[ℝ] Y)
    (hfast : ∀ y, ∃ g, fderiv ℝ (fun u ↦ F (0, (σ₀, u))) u₀ g = P y)
    (hslow : ∀ y, ∃ τ, fderiv ℝ (fun σ ↦ F (0, (σ, u₀))) σ₀ τ -
      P (fderiv ℝ (fun σ ↦ F (0, (σ, u₀))) σ₀ τ) = y - P y) :
    ∃ σ : ℕ → C, ∃ u : ℕ → D, (fun h : ℝ ↦ F (h, (σ₀ + ∑ i ∈ range N, h ^ (i + 1) • σ i,
      u₀ + ∑ i ∈ range N, h ^ (i + 1) • u i))) =O[𝓝 0] fun h ↦ h ^ (N + 1) := by
  -- The slice derivative splits into the slow and fast partial derivatives.
  set Λ := fderiv ℝ (fun x : C × D ↦ F (0, x)) (σ₀, u₀)
  have hd : DifferentiableAt ℝ (fun x : C × D ↦ F (0, x)) (σ₀, u₀) :=
    ((hF.differentiableAt fun hn ↦ by simp [hn] at hN).comp (σ₀, u₀)
      (differentiableAt_const _ |>.prodMk differentiableAt_id))
  have hsurj : Function.Surjective Λ := by
    intro y
    obtain ⟨⟨τ, g⟩, hτg⟩ := LinearMap.surjective_coprod_of_forall_exists_eq
      (f := (fderiv ℝ (fun σ ↦ F (0, (σ, u₀))) σ₀ : C →ₗ[ℝ] Y))
      (g := (fderiv ℝ (fun u ↦ F (0, (σ₀, u))) u₀ : D →ₗ[ℝ] Y)) P hfast hslow y
    exact ⟨(τ, g), by
      rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hd]; simpa using hτg⟩
  obtain ⟨x, hx⟩ := exists_isBigO_pow_of_surjective hF hN h₀ hsurj
  refine ⟨fun i ↦ (x i).1, fun i ↦ (x i).2, hx.congr_left fun h ↦ ?_⟩
  congr 2
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

end SlowFirstProfile

end TauCeti
