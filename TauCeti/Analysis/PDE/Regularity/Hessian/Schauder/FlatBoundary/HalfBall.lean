/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.VariableCoefficient

import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.MeasureTheory.Function.LpSeminorm.Support
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Schauder estimates on small half-balls at a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, with closure
`closure H = {x | c₀ ≤ ⟪x, ν⟫}`, let `0 < α < 1`, and let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a
non-divergence-form operator. This file localizes the `C^{2,α}` estimate up to the hyperplane `∂H`
for coefficients of small oscillation
(`exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_abs_sub_le_of_halfSpace`, in
the `TauCeti.PDE` namespace) to Hölder continuous coefficients on half-balls, in two steps.

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_support_subset_closedBall_of_halfSpace`:
  the estimate for a function whose Hessian vanishes in `H` outside a ball `closedBall x₀ R`
  centred in `closure H`. The coefficients need only be Hölder on `closedBall x₀ R ∩ closure H`:
  radial retraction onto the ball maps `closure H` into itself and replaces them by coefficients
  Hölder on `H` and within `L Rᵅ` of `a x₀`, without changing `L u` where the Hessian is nonzero.
* **The Schauder estimate on small half-balls**, in the `TauCeti.PDE` namespace,
  `exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_halfSpace`.
  If `R` is small compared with the Hölder modulus
  of the coefficients, then for every `ρ < R` there is `C`, independent of the solution, such that
  every `u` which is `C²` near `B_R ∩ closure H`, vanishes on `B_R ∩ ∂H` and has `α`-Hölder
  Hessian on `B_R ∩ closure H` satisfies

  `[D²u]_{α; closedBall x₀ ρ ∩ closure H} ≤ C ([L u]_{α; B_R ∩ H} + N)`,

  where `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on `B_R ∩ closure H`. Only values in the closed
  half-space enter, and `C` depends on the coefficients only through their ellipticity constants
  at the centre, their Hölder constant and a bound on their entries.

This is the boundary counterpart of the interior estimate on small balls
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`), and
the local estimate from which the global Schauder estimate on domains with `C^{2,α}` boundary is
assembled by flattening the boundary and covering.

## The argument

Choose a smooth cutoff `ζ` equal to one near `closedBall x₀ ρ` with support in `B_R`, the
translate of one fixed cutoff about the origin so that its bounds do not depend on `x₀`, and put
`w = ζ u`. Then `w` is `C²` on the open set `U ∪ (tsupport ζ)ᶜ`, which contains `closure H`, it
vanishes on `∂H`, and its Hessian vanishes outside `closedBall x₀ R`. On `closure H`,

`∂ᵢ∂ⱼw = ζ ∂ᵢ∂ⱼu + Tᵢⱼ`, where `Tᵢⱼ = u ∂ᵢ∂ⱼζ + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu`,

so `L w = ζ L u + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` on `H`. Each term is the product of a factor built from `ζ`, which
vanishes off `B_R`, with a factor that is bounded and Hölder on `B_R ∩ closure H`, so it is Hölder
on the whole of `closure H`; the products are estimated on the subtype `closure H` with
`HolderWith.smul_of_eq_zero`. On the convex set `B_R ∩ closure H` the functions `u` and `Du` are
Lipschitz, with constant `N`, hence `α`-Hölder. This bounds the Hölder constant of `L w` on `H` by
`C (K + N)` and `‖D²w‖_{L²(H)}` by `C N`, and the estimate for a Hessian supported in a ball bounds
the Hölder constant of `D²w` on `closure H`, which is that of `D²u` near
`closedBall x₀ ρ ∩ closure H`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2: Lemma 6.5 (the boundary estimate on half-balls) and the localization by cutoffs in
  the proof of Theorem 6.2.
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped InnerProductSpace NNReal ENNReal ContDiff

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The centred radial retraction onto `closedBall x₀ R` maps the closed half-space
`{x | c₀ ≤ ⟪x, ν⟫}` into itself when `x₀` lies in it: it moves each point along the segment
towards `x₀`. -/
private theorem mapsTo_centeredRadialRetraction_halfSpace {x₀ ν : E} {c₀ R : ℝ} (hR : 0 ≤ R)
    (hx₀ : c₀ ≤ ⟪x₀, ν⟫_ℝ) :
    MapsTo (TauCeti.centeredRadialRetraction x₀ R) {x | c₀ ≤ ⟪x, ν⟫_ℝ}
      (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}) := fun x hx => by
  refine ⟨TauCeti.centeredRadialRetraction_mem_closedBall hR x, ?_⟩
  set m : ℝ := min 1 (R / ‖x - x₀‖)
  have hm0 : 0 ≤ m := le_min zero_le_one (div_nonneg hR (norm_nonneg _))
  have hm1 : m ≤ 1 := min_le_left _ _
  have hx' : c₀ ≤ ⟪x, ν⟫_ℝ := mem_ofPred.1 hx
  rw [mem_ofPred, TauCeti.centeredRadialRetraction_def, TauCeti.radialRetraction_def,
    inner_add_left, real_inner_smul_left, inner_sub_left]
  nlinarith

/-- **Schauder estimate up to a flat boundary for a Hessian supported in a ball.** For
`0 < α < 1` there is `C > 0`, depending only on the dimension and `α`, with the following
property. Let `H = {x | c₀ < ⟪x, ν⟫}`, `ν ≠ 0`, let `x₀` lie in the closed half-space
`closure H`, and suppose `a x₀` has ellipticity bounds `λ, Λ`, with `λ > 0`, and every
coefficient entry is `α`-Hölder with constant `L` on `closedBall x₀ R ∩ closure H`. Put
`κ = C (Λ / λ)^(1 + (n+1)/4 + α/2)`. If

`2 κ (n+1)² (L Rᵅ + 2ᵅ L rᵅ) ≤ λ`,

then every `u` that is `C²` on an open set containing `closure H`, vanishes on the hyperplane
`∂H`, has `D²u` `α`-Hölder on `closure H` and in `L²(H)`, and whose Hessian vanishes at the
points of `H` outside `closedBall x₀ R`, satisfies

`[D²u]_{α; closure H} ≤ 2 κ ([L u]_{α; H} / λ + Q ‖D²u‖_{L²(H)})`, where
`Q = (n+1)² 2ᵅ L / λ |B_{r/2}|^(-1/2) + r^(-(n+1)/2-α)`.

The Hölder hypothesis on `D²u` is an a priori regularity assumption; its constant does not occur
in the conclusion. No comparison of `a` with one constant matrix is assumed: by the support
condition the coefficients may be retracted to the ball and frozen at its centre. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_support_subset_closedBall_of_halfSpace
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ ν : E} {c₀ lam Lam : ℝ},
      ν ≠ 0 → c₀ ≤ ⟪x₀, ν⟫_ℝ → 0 < lam →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ {L K : ℝ≥0} {R r : ℝ}, 0 ≤ R → 0 < r →
      2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * r ^ (α : ℝ)) ≤ lam →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ})) →
      ∀ {U : Set E} {u : E → ℝ}, IsOpen U → {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U → ContDiffOn ℝ 2 u U →
      (∀ x, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
      (∃ J, HolderOnWith J α (iteratedFDeriv ℝ 2 u) {x | c₀ ≤ ⟪x, ν⟫_ℝ}) →
      MemLp (iteratedFDeriv ℝ 2 u) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) →
      Function.support (iteratedFDeriv ℝ 2 u) ∩ {x | c₀ < ⟪x, ν⟫_ℝ} ⊆ closedBall x₀ R →
      HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) {x | c₀ < ⟪x, ν⟫_ℝ} →
      HolderOnWith (2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) *
        (K / lam + (((n : ℝ) + 1) ^ 2 * (L * 2 ^ (α : ℝ)) / lam *
          (volume (ball (0 : E) (r / 2)) ^ (-((2 : ℝ)⁻¹))).toReal +
          r ^ (-(((n : ℝ) + 1) / 2 + α))) *
            (eLpNorm (iteratedFDeriv ℝ 2 u) 2
              (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ})).toReal)).toNNReal
        α (iteratedFDeriv ℝ 2 u) {x | c₀ ≤ ⟪x, ν⟫_ℝ} := by
  obtain ⟨C₀, hC₀, hS⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_abs_sub_le_of_halfSpace
      hα hα1 (n := n)
  refine ⟨C₀, hC₀, fun {a x₀ ν c₀ lam Lam} hν hx₀ hlam hEll hEll' {L K R r} hR hr hsmall hL
    {U u} hU hHU hu hu0 hJ hH2 hsupp hf => ?_⟩
  set Hc : Set E := {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  have hoc : Ho ⊆ Hc := fun _ hx => mem_ofPred.2 (mem_ofPred.1 hx).le
  let q : E → E := TauCeti.centeredRadialRetraction x₀ R
  let a' : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun x => a (q x)
  have hq : MapsTo q Hc (closedBall x₀ R ∩ Hc) := mapsTo_centeredRadialRetraction_halfSpace hR hx₀
  have hx₀B : x₀ ∈ closedBall x₀ R ∩ Hc := ⟨mem_closedBall_self hR, hx₀⟩
  -- The retracted coefficients are Hölder on the open half-space, with constant `2ᵅ L`.
  have ha'_holder (i j : Fin (n + 1)) :
      HolderOnWith (L * 2 ^ (α : ℝ)) α (fun x => a' x i j) Ho := by
    have h := (hL i j).comp
      (((TauCeti.lipschitzWith_centeredRadialRetraction (x₀ := x₀) hR).holderWith).holderOnWith
        Hc) hq
    rw [mul_one] at h
    exact h.mono hoc
  -- They stay within `L Rᵅ` of their value at the centre.
  have ha'_close (x : E) (hx : c₀ < ⟪x, ν⟫_ℝ) (i j : Fin (n + 1)) :
      |a' x i j - a x₀ i j| ≤ L * R ^ (α : ℝ) := by
    have hmem := hq (hoc hx)
    simpa only [a', Real.dist_eq] using
      ((hL i j).dist_le hmem hx₀B).trans (by gcongr; exact mem_closedBall.1 hmem.1)
  -- On the open half-space the operator is unchanged, since the Hessian vanishes off the ball.
  have hf' : HolderOnWith K α (fun x => ∑ i, ∑ j, a' x i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) Ho := by
    refine hf.congr fun x hx => ?_
    by_cases hx' : x ∈ Function.support (iteratedFDeriv ℝ 2 u)
    · simp only [a', q, TauCeti.centeredRadialRetraction_of_mem_closedBall (hsupp ⟨hx', hx⟩)]
    · have hzero : iteratedFDeriv ℝ 2 u x = 0 := by simpa [Function.mem_support] using hx'
      have hentry (i j : Fin (n + 1)) : fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
        have hzero' := congrArg (fun H : E [×2]→L[ℝ] ℝ =>
          H ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) hzero
        simpa only [iteratedFDeriv_two_apply, zero_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one] using hzero'
      simp [hentry]
  let ε : ℝ≥0 := (L * R ^ (α : ℝ)).toNNReal
  have hε : (ε : ℝ) = L * R ^ (α : ℝ) :=
    Real.coe_toNNReal _ (mul_nonneg L.coe_nonneg (Real.rpow_nonneg hR _))
  have hsmall' :
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((ε : ℝ) + (L * 2 ^ (α : ℝ) : ℝ≥0) * r ^ (α : ℝ)) ≤ lam := by
    simpa only [hε, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat] using hsmall
  exact hS (A := a x₀) (a := a') hlam hEll hEll' hν hr hsmall'
    (fun x hx i j => by simpa only [hε] using ha'_close x hx i j) ha'_holder hU hHU hu hu0 hJ hH2
    hf'

/-! ### Cutoff products relative to a set -/

/-- Evaluating a family of linear maps at a coordinate vector keeps a Hölder constant and a
bound of the family on a set. -/
private theorem holderOnWith_apply_single_and_norm_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → E →L[ℝ] F} {C Z α : ℝ≥0} {s : Set E}
    (hf : HolderOnWith C α f s) (hfB : ∀ x ∈ s, ‖f x‖ ≤ Z) (i : Fin (n + 1)) :
    HolderOnWith C α (fun x => f x (EuclideanSpace.single i 1)) s ∧
      ∀ x ∈ s, ‖f x (EuclideanSpace.single i 1)‖ ≤ Z := by
  have hi : ‖(EuclideanSpace.single i 1 : E)‖ ≤ 1 := by simp
  refine ⟨fun x hx y hy => le_trans ?_ (hf x hx y hy),
    fun x hx => ((f x).unit_le_opNorm _ hi).trans (hfB x hx)⟩
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← sub_apply]
  exact ENNReal.ofReal_le_ofReal ((f x - f y).unit_le_opNorm _ hi)

/-- A smooth function with compact support has one constant `Z` which bounds it and its first and
second derivatives, together with their `α`-Hölder constants, for all of its translates at once. -/
private theorem exists_forall_holderWith_translate_and_norm_le {α : ℝ≥0} (hα : α ≤ 1)
    {ζ₀ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ₀) (hc : HasCompactSupport ζ₀) :
    ∃ Z : ℝ≥0, ∀ x₀ : E,
      (HolderWith Z α (fun x => ζ₀ (x - x₀)) ∧
        HolderWith Z α (fderiv ℝ fun x => ζ₀ (x - x₀)) ∧
        HolderWith Z α (fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)))) ∧
      ∀ x, ‖ζ₀ (x - x₀)‖ ≤ Z ∧ ‖fderiv ℝ (fun x => ζ₀ (x - x₀)) x‖ ≤ Z ∧
        ‖fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)) x‖ ≤ Z := by
  obtain ⟨C₀, h₀, b₀⟩ :=
    (hζ.of_le (by norm_cast)).exists_holderWith_and_norm_le_of_hasCompactSupport hc hα
  obtain ⟨C₁, h₁, b₁⟩ := ContDiff.exists_holderWith_and_norm_le_of_hasCompactSupport
    (hζ.fderiv_right (m := 1) (by norm_cast)) (hc.fderiv (𝕜 := ℝ)) hα
  obtain ⟨C₂, h₂, b₂⟩ := ((hζ.fderiv_right (m := 2) (by norm_cast)).fderiv_right (m := 1)
    le_rfl).exists_holderWith_and_norm_le_of_hasCompactSupport
      ((hc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)) hα
  refine ⟨C₀ + C₁ + C₂, fun x₀ => ?_⟩
  have hD1 : fderiv ℝ (fun x => ζ₀ (x - x₀)) = fun x => fderiv ℝ ζ₀ (x - x₀) :=
    funext fun _ => fderiv_comp_sub x₀
  have hD2 : fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)) =
      fun x => fderiv ℝ (fderiv ℝ ζ₀) (x - x₀) := by
    rw [hD1]
    exact funext fun _ => fderiv_comp_sub x₀
  have htr {F : Type} [NormedAddCommGroup F] {g : E → F} {C : ℝ≥0} (h : HolderWith C α g)
      (hC : C ≤ C₀ + C₁ + C₂) : HolderWith (C₀ + C₁ + C₂) α (fun x => g (x - x₀)) :=
    fun x y => by simpa only [edist_sub_right] using (h.mono hC) (x - x₀) (y - x₀)
  have hle₀ : C₀ ≤ C₀ + C₁ + C₂ := le_add_right (le_add_right le_rfl)
  have hle₁ : C₁ ≤ C₀ + C₁ + C₂ := le_add_right le_add_self
  have hle₂ : C₂ ≤ C₀ + C₁ + C₂ := le_add_self
  rw [hD2, hD1]
  exact ⟨⟨htr h₀ hle₀, htr h₁ hle₁, htr h₂ hle₂⟩, fun x =>
    ⟨(b₀ _).trans (by exact_mod_cast hle₀), (b₁ _).trans (by exact_mod_cast hle₁),
      (b₂ _).trans (by exact_mod_cast hle₂)⟩⟩

/-- The product of a factor `c`, Hölder and bounded on `t` and vanishing at the points of `t`
outside `s`, with a factor `g` which is Hölder and bounded on `s`, is Hölder on `t` and bounded by
the product of the bounds. Nothing is assumed about `g` off `s`. -/
private theorem holderOnWith_mul_and_abs_le {c g : E → ℝ} {s t : Set E} {α Kc Mc Kg Mg : ℝ≥0}
    (hc : HolderOnWith Kc α c t) (hcM : ∀ x ∈ t, |c x| ≤ Mc) (hc0 : ∀ x ∈ t, x ∉ s → c x = 0)
    (hg : HolderOnWith Kg α g s) (hgM : ∀ x ∈ s, |g x| ≤ Mg) :
    HolderOnWith (Mc * Kg + Mg * Kc) α (fun x => c x * g x) t ∧
      ∀ x ∈ t, |c x * g x| ≤ Mc * Mg := by
  refine ⟨HolderWith.restrict_iff.1 ?_, fun x hx => ?_⟩
  · have h := HolderWith.smul_of_eq_zero (X := ↥t) (c := fun x => c x) (f := fun x => g x)
      (s := {x : ↥t | (x : E) ∈ s}) hc.holderWith (fun x hx y hy => hg x hx y hy)
      (fun x => by simpa only [Real.norm_eq_abs] using hcM x x.property)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hgM x hx)
      (fun x hx => hc0 x x.property hx)
    simp only [smul_eq_mul] at h
    exact h
  · by_cases hxs : x ∈ s
    · rw [abs_mul]
      exact mul_le_mul (hcM x hx) (hgM x hxs) (abs_nonneg _) Mc.coe_nonneg
    · simp only [hc0 x hx hxs, zero_mul, abs_zero]
      positivity

/-- A finite sum of functions that are Hölder on `t` is Hölder on `t`, with the sum of the
constants; the relative form of `HolderWith.sum`. -/
private theorem holderOnWith_finset_sum {ι : Type*} {s : Finset ι} {C : ι → ℝ≥0} {α : ℝ≥0}
    {f : ι → E → ℝ} {t : Set E} (hf : ∀ i ∈ s, HolderOnWith (C i) α (f i) t) :
    HolderOnWith (∑ i ∈ s, C i) α (fun x => ∑ i ∈ s, f i x) t :=
  HolderWith.restrict_iff.1 (HolderWith.sum fun i hi => (hf i hi).holderWith)

/-- The second derivative of a product `ζ u`, at a point where `u` is `C²` or which lies outside
the topological support of `ζ`. -/
private theorem fderiv_fderiv_mul_apply_of_mem_or_notMem_tsupport {U : Set E} (hU : IsOpen U)
    {ζ u : E → ℝ} (hζ : ContDiff ℝ 2 ζ) (hu : ContDiffOn ℝ 2 u U) {x : E}
    (hx : x ∈ U ∨ x ∉ tsupport ζ) (v w : E) :
    fderiv ℝ (fderiv ℝ (ζ * u)) x v w = ζ x * fderiv ℝ (fderiv ℝ u) x v w +
      (fderiv ℝ (fderiv ℝ ζ) x v w * u x + fderiv ℝ ζ x v * fderiv ℝ u x w +
        fderiv ℝ ζ x w * fderiv ℝ u x v) := by
  rcases hx with hx | hx
  · rw [fderiv_fderiv_mul_apply hζ.contDiffAt (hu.contDiffAt (hU.mem_nhds hx))]
    ring
  · have hζu : x ∉ tsupport (ζ * u) := fun h => hx (tsupport_mul_subset_left h)
    simp [fderiv_fderiv_of_notMem_tsupport hζu, fderiv_fderiv_of_notMem_tsupport hx,
      fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]

/-- The lower-order part `Tᵢⱼ = ∂ᵢ∂ⱼζ u + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu` of the Hessian entry `∂ᵢ∂ⱼ(ζ u)` is
Hölder and bounded on `t` and vanishes at the points of `t` outside `s`, when the first and second
derivatives of `ζ` are globally Hölder and bounded with constant `Z`, the points of `t` outside
`s` lie outside the topological support of `ζ`, and `u` and its first derivatives are bounded by
`N` and Hölder with constant `H` on `s`. -/
private theorem holderOnWith_cutoff_remainder {s t : Set E} {ζ u : E → ℝ} {α Z N H : ℝ≥0}
    (hZ1 : HolderWith Z α (fderiv ℝ ζ)) (hZ2 : HolderWith Z α (fderiv ℝ (fderiv ℝ ζ)))
    (hB1 : ∀ x, ‖fderiv ℝ ζ x‖ ≤ Z) (hB2 : ∀ x, ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ Z)
    (hζs : ∀ x ∈ t, x ∉ s → x ∉ tsupport ζ) (hN0 : ∀ x ∈ s, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    (i j : Fin (n + 1)) :
    HolderOnWith (3 * (Z * H + N * Z)) α (fun x =>
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) t ∧
    (∀ x ∈ t, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
        u x + fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)| ≤
      3 * Z * N) ∧
    ∀ x ∈ t, x ∉ s →
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1) =
      0 := by
  have e1 (k : Fin (n + 1)) :=
    holderOnWith_apply_single_and_norm_le (hZ1.holderOnWith t) (fun x _ => hB1 x) k
  have e2i := holderOnWith_apply_single_and_norm_le (hZ2.holderOnWith t) (fun x _ => hB2 x) i
  have e2 := holderOnWith_apply_single_and_norm_le e2i.1 e2i.2 j
  have z1 (k : Fin (n + 1)) (x : E) (hx : x ∈ t) (hxs : x ∉ s) :
      fderiv ℝ ζ x (EuclideanSpace.single k 1) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (hζs x hx hxs), zero_apply]
  have z2 (x : E) (hx : x ∈ t) (hxs : x ∉ s) :
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
    rw [fderiv_fderiv_of_notMem_tsupport (hζs x hx hxs), zero_apply,
      zero_apply]
  obtain ⟨h1, b1⟩ := holderOnWith_mul_and_abs_le e2.1
    (fun x hx => by simpa only [Real.norm_eq_abs] using e2.2 x hx) z2 hH0 hN0
  obtain ⟨h2, b2⟩ := holderOnWith_mul_and_abs_le (e1 i).1
    (fun x hx => by simpa only [Real.norm_eq_abs] using (e1 i).2 x hx) (z1 i) (hH1 j) (hN1 j)
  obtain ⟨h3, b3⟩ := holderOnWith_mul_and_abs_le (e1 j).1
    (fun x hx => by simpa only [Real.norm_eq_abs] using (e1 j).2 x hx) (z1 j) (hH1 i) (hN1 i)
  refine ⟨((h1.add h2).add h3).mono_const (le_of_eq (by ring)), fun x hx => ?_,
    fun x hx hxs => ?_⟩
  · refine (abs_add_three _ _ _).trans ((add_le_add_three (b1 x hx) (b2 x hx)
      (b3 x hx)).trans_eq ?_)
    ring
  · simp only [z2 x hx hxs, z1 i x hx hxs, z1 j x hx hxs, zero_mul, add_zero]

/-- The Hessian entries `∂ᵢ∂ⱼ(ζ u) = ζ ∂ᵢ∂ⱼu + Tᵢⱼ` of a cutoff product are Hölder and bounded on
`t`, when each point of `t` lies in the open set `U` on which `u` is `C²` or outside the
topological support of `ζ`, the points of `t` outside `s` lie outside that support, `ζ` and its
first two derivatives are globally Hölder and bounded with constant `Z`, and `u` and its first
and second derivatives are bounded by `N` on `s` and Hölder there with constants `H`, `H` and
`V`. -/
private theorem holderOnWith_fderiv_fderiv_cutoff_mul {s t U : Set E} (hU : IsOpen U)
    {ζ u : E → ℝ} {α Z N H V : ℝ≥0} (hζ : ContDiff ℝ 2 ζ) (hZ0 : HolderWith Z α ζ)
    (hZ1 : HolderWith Z α (fderiv ℝ ζ)) (hZ2 : HolderWith Z α (fderiv ℝ (fderiv ℝ ζ)))
    (hB : ∀ x, ‖ζ x‖ ≤ Z ∧ ‖fderiv ℝ ζ x‖ ≤ Z ∧ ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ Z)
    (htU : ∀ x ∈ t, x ∈ U ∨ x ∉ tsupport ζ) (hζs : ∀ x ∈ t, x ∉ s → x ∉ tsupport ζ)
    (hu : ContDiffOn ℝ 2 u U) (hN0 : ∀ x ∈ s, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hN2 : ∀ i j, ∀ x ∈ s,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    (hV : ∀ i j, HolderOnWith V α (fun x =>
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s)
    (i j : Fin (n + 1)) :
    HolderOnWith (Z * V + N * Z + 3 * (Z * H + N * Z)) α (fun x =>
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) t ∧
    ∀ x ∈ t, |fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)| ≤ 4 * Z * N := by
  obtain ⟨hT, bT, -⟩ := holderOnWith_cutoff_remainder hZ1 hZ2 (fun x => (hB x).2.1)
    (fun x => (hB x).2.2) hζs hN0 hN1 hH0 hH1 i j
  obtain ⟨h1, b1⟩ := holderOnWith_mul_and_abs_le (hZ0.holderOnWith t)
    (fun x _ => by simpa only [Real.norm_eq_abs] using (hB x).1)
    (fun x hx hxs => image_eq_zero_of_notMem_tsupport (hζs x hx hxs)) (hV i j) (hN2 i j)
  have hW (x : E) (hx : x ∈ t) :
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        (ζ x * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          (fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
            u x + fderiv ℝ ζ x (EuclideanSpace.single i 1) *
              fderiv ℝ u x (EuclideanSpace.single j 1) +
            fderiv ℝ ζ x (EuclideanSpace.single j 1) *
              fderiv ℝ u x (EuclideanSpace.single i 1))) :=
    fderiv_fderiv_mul_apply_of_mem_or_notMem_tsupport hU hζ hu (htU x hx) _ _
  refine ⟨(h1.add hT).congr fun x hx => (hW x hx).symm, fun x hx => ?_⟩
  rw [hW x hx]
  calc _ ≤ (Z * N : ℝ) + 3 * Z * N := (abs_add_le _ _).trans (add_le_add (b1 x hx) (bT x hx))
    _ = _ := by ring

/-- For a cutoff product `ζ u` as in `holderOnWith_fderiv_fderiv_cutoff_mul`, the operator
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` is Hölder on `t`, when the coefficients are
bounded by `M` and Hölder with constant `L` on `s`, and `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` is Hölder with constant
`K` on `s`. The Hessian of `u` need not be Hölder. -/
private theorem holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul {s t U : Set E} (hU : IsOpen U)
    {ζ u : E → ℝ} {α Z N H : ℝ≥0} (hζ : ContDiff ℝ 2 ζ) (hZ0 : HolderWith Z α ζ)
    (hZ1 : HolderWith Z α (fderiv ℝ ζ)) (hZ2 : HolderWith Z α (fderiv ℝ (fderiv ℝ ζ)))
    (hB : ∀ x, ‖ζ x‖ ≤ Z ∧ ‖fderiv ℝ ζ x‖ ≤ Z ∧ ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ Z)
    (htU : ∀ x ∈ t, x ∈ U ∨ x ∉ tsupport ζ) (hζs : ∀ x ∈ t, x ∉ s → x ∉ tsupport ζ)
    (hu : ContDiffOn ℝ 2 u U) (hN0 : ∀ x ∈ s, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hN2 : ∀ i j, ∀ x ∈ s,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {L M K : ℝ≥0}
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) s) (hM : ∀ x ∈ s, ∀ i j, |a x i j| ≤ M)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s) :
    HolderOnWith (Z * K + (n + 1) ^ 2 * (M * N * Z + (3 * Z * N * L + M * (3 * (Z * H + N * Z)))))
      α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ (ζ * u)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) t := by
  set f : E → ℝ := fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hfM (x : E) (hx : x ∈ s) : |f x| ≤ ((n + 1) ^ 2 * M * N : ℝ≥0) := by
    calc |f x| ≤ ∑ i, ∑ j, |a x i j • fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), (M * N : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [smul_eq_mul, abs_mul]
          exact mul_le_mul (hM x hx i j) (hN2 i j x hx) (abs_nonneg _) M.coe_nonneg
      _ = _ := by simp; ring
  -- On `t`, `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ f + ∑ᵢⱼ Tᵢⱼ aᵢⱼ`.
  set T : Fin (n + 1) → Fin (n + 1) → E → ℝ := fun i j x =>
    fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
      fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
      fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)
  have heq : EqOn (fun x => ζ x * f x + ∑ i, ∑ j, T i j x * a x i j)
      (fun x => ∑ i, ∑ j, a x i j •
        fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      t := fun x hx => by
    simp only [fderiv_fderiv_mul_apply_of_mem_or_notMem_tsupport hU hζ hu (htU x hx), smul_eq_mul,
      f, T, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨h1, -⟩ := holderOnWith_mul_and_abs_le (hZ0.holderOnWith t)
    (fun x _ => by simpa only [Real.norm_eq_abs] using (hB x).1)
    (fun x hx hxs => image_eq_zero_of_notMem_tsupport (hζs x hx hxs)) hK hfM
  have h2 (i j : Fin (n + 1)) : HolderOnWith (3 * Z * N * L + M * (3 * (Z * H + N * Z))) α
      (fun x => T i j x * a x i j) t := by
    obtain ⟨hT, bT, hT0⟩ := holderOnWith_cutoff_remainder hZ1 hZ2 (fun x => (hB x).2.1)
      (fun x => (hB x).2.2) hζs hN0 hN1 hH0 hH1 i j
    exact (holderOnWith_mul_and_abs_le hT (Mc := 3 * Z * N) (by exact_mod_cast bT) hT0 (hL i j)
      fun x hx => hM x hx i j).1
  have hsum := holderOnWith_finset_sum (s := Finset.univ)
    (f := fun i x => ∑ j, T i j x * a x i j) fun i _ =>
      holderOnWith_finset_sum (s := Finset.univ) (f := fun j x => T i j x * a x i j)
        fun j _ => h2 i j
  refine ((h1.add hsum).congr heq).mono_const (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- A function differentiable on an open set `U`, with derivative bounded by `N` on a convex set
`s ⊆ U` contained in the ball `B_R`, is `α`-Hölder on `s` with constant `N (2R)^(1 - α)` for
every `α ≤ 1`: it is `N`-Lipschitz on `s`, whose diameter is at most `2R`. -/
private theorem holderOnWith_of_convex_of_norm_fderiv_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → F} {s U : Set E} {x₀ : E} {R : ℝ} {N α : ℝ≥0} (hα : α ≤ 1)
    (hs : Convex ℝ s) (hsR : s ⊆ ball x₀ R) (hU : IsOpen U) (hsU : s ⊆ U)
    (hg : DifferentiableOn ℝ g U) (hN : ∀ x ∈ s, ‖fderiv ℝ g x‖ ≤ N) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α g s := by
  have hA : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ (2 * R).toNNReal := by
    intro x hx y hy
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [dist_triangle_right x y x₀, mem_ball.1 (hsR hx), mem_ball.1 (hsR hy)]
  have hL : LipschitzOnWith N g s :=
    hs.lipschitzOnWith_of_nnNorm_fderiv_le
      (fun x hx => hg.differentiableAt (hU.mem_nhds (hsU hx)))
      fun x hx => by rw [← NNReal.coe_le_coe, coe_nnNorm]; exact hN x hx
  simpa using (holderOnWith_one.2 hL).of_le hA hα

/-- The coordinate bounds and Hölder constants of a function `u` which is `C²` on an open set `U`,
on a convex set `s ⊆ U` inside the ball `B_R` on which `‖Du‖` and `‖D²u‖` are bounded by `N` and
`D²u` is Hölder with constant `V`: `u` and the partial derivatives `∂ᵢu` are Hölder on `s` with
constant `N (2R)^(1 - α)`, the `∂ᵢu` and `∂ᵢ∂ⱼu` are bounded by `N`, and the `∂ᵢ∂ⱼu` are Hölder
with constant `V`. -/
private theorem entries_of_convex_of_norm_le {u : E → ℝ} {s U : Set E} {x₀ : E} {R : ℝ}
    {N V α : ℝ≥0} (hα : α ≤ 1) (hs : Convex ℝ s) (hsR : s ⊆ ball x₀ R) (hU : IsOpen U)
    (hsU : s ⊆ U) (hu : ContDiffOn ℝ 2 u U) (hN1 : ∀ x ∈ s, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ s, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) (hV : HolderOnWith V α (iteratedFDeriv ℝ 2 u) s) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α u s ∧
    (∀ i, HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α
      (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s) ∧
    (∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N) ∧
    (∀ i j, ∀ x ∈ s,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N) ∧
    ∀ i j, HolderOnWith V α (fun x =>
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s := by
  have hHDu : HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α (fderiv ℝ u) s :=
    holderOnWith_of_convex_of_norm_fderiv_le hα hs hsR hU hsU
      ((hu.fderiv_of_isOpen hU (m := 1) le_rfl).differentiableOn one_ne_zero)
      fun x hx => by rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact hN2 x hx
  refine ⟨holderOnWith_of_convex_of_norm_fderiv_le hα hs hsR hU hsU
      (hu.differentiableOn two_ne_zero) hN1,
    fun i => (holderOnWith_apply_single_and_norm_le hHDu hN1 i).1,
    fun i x hx => by
      simpa only [Real.norm_eq_abs] using (holderOnWith_apply_single_and_norm_le hHDu hN1 i).2 x hx,
    fun i j x hx => ?_, fun i j => ?_⟩
  · simpa [iteratedFDeriv_two_apply] using
      ((iteratedFDeriv ℝ 2 u x).norm_apply_orthonormalBasis_le
        (EuclideanSpace.basisFun _ ℝ) i j).trans (hN2 x hx)
  · simpa [iteratedFDeriv_two_apply] using
      hV.apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j

/-- A function `w` which is `C²` on an open set `W` containing the open half-space `H`, whose
Hessian is bounded by `B ≥ 0` on `H` and vanishes outside `closedBall x₀ R`, has Hessian in `L²(H)`,
with norm at most `|closedBall 0 R|^{1/2} B`. -/
private theorem memLp_and_toReal_eLpNorm_le_of_support_subset_closedBall {w : E → ℝ} {W : Set E}
    {x₀ ν : E} {c₀ R B : ℝ} (hW : IsOpen W) (hw : ContDiffOn ℝ 2 w W)
    (hHW : {x | c₀ < ⟪x, ν⟫_ℝ} ⊆ W)
    (hsupp : Function.support (iteratedFDeriv ℝ 2 w) ⊆ closedBall x₀ R) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ {x | c₀ < ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 w x‖ ≤ B) :
    MemLp (iteratedFDeriv ℝ 2 w) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) ∧
      (eLpNorm (iteratedFDeriv ℝ 2 w) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ})).toReal ≤
        (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) * B := by
  have hHo : MeasurableSet {x : E | c₀ < ⟪x, ν⟫_ℝ} :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  have haesm : AEStronglyMeasurable (iteratedFDeriv ℝ 2 w)
      (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) :=
    ((ContinuousOn.continuousOn_iteratedFDeriv hw hW (by norm_num)).mono
      hHW).aestronglyMeasurable hHo
  have hle : eLpNorm (iteratedFDeriv ℝ 2 w) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) ≤
      volume (closedBall (0 : E) R) ^ (2⁻¹ : ℝ) * ENNReal.ofReal B := by
    refine (eLpNorm_le_of_ae_bound_of_support_subset haesm hsupp
      (ae_restrict_of_forall_mem hHo hB)).trans ?_
    rw [ENNReal.toReal_ofNat]
    refine mul_le_mul_left (ENNReal.rpow_le_rpow ?_ (by norm_num)) _
    exact (Measure.restrict_apply_le _ _).trans_eq (Measure.addHaar_closedBall_center _ _ _)
  have hfin : volume (closedBall (0 : E) R) ^ (2⁻¹ : ℝ) * ENNReal.ofReal B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      measure_closedBall_lt_top.ne) ENNReal.ofReal_ne_top
  refine ⟨hle.trans_lt hfin.lt_top, (ENNReal.toReal_mono hfin hle).trans_eq ?_⟩
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB0]

/-- The cutoff product `w = ζ u` of a cutoff `ζ` supported in the ball `B_R` and a function `u`
which is `C²` on an open set `U ⊇ B_R ∩ closure H`, vanishes on `B_R ∩ ∂H`, and has bounds `N` on
`u` and its first two derivatives and a Hölder Hessian on `B_R ∩ closure H`, satisfies the
hypotheses of the estimate up to the boundary for a Hessian supported in a ball: `w` is `C²` on an
open set containing `closure H` and vanishes on `∂H`; its Hessian is Hölder on `closure H`,
supported in `closedBall x₀ R`, and has `L²(H)` norm at most `|closedBall 0 R|^{1/2} (n+1)² 4 Z N`;
and `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼw` is Hölder on `H` with constant `Z K + N B₂`. -/
private theorem cutoff_mul_data_of_halfSpace {ζ u : E → ℝ} {x₀ ν : E} {c₀ R : ℝ} {U : Set E}
    {α Z N K V L M δ B₂ : ℝ≥0} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hα1 : α ≤ 1)
    (hζ : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ ball x₀ R)
    (hZ0 : HolderWith Z α ζ) (hZ1 : HolderWith Z α (fderiv ℝ ζ))
    (hZ2 : HolderWith Z α (fderiv ℝ (fderiv ℝ ζ)))
    (hB : ∀ x, ‖ζ x‖ ≤ Z ∧ ‖fderiv ℝ ζ x‖ ≤ Z ∧ ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ Z)
    (hU : IsOpen U) (hBU : ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hu0 : ∀ x ∈ ball x₀ R, ⟪x, ν⟫_ℝ = c₀ → u x = 0)
    (hN0 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, |u x| ≤ N)
    (hN1 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N)
    (hV : HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}))
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))
    (hM : ∀ x ∈ ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}, ∀ i j, |a x i j| ≤ M)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))
    (hδ : δ = (2 * R).toNNReal ^ ((1 : ℝ) - α))
    (hB₂ : B₂ = (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))) :
    (IsOpen (U ∪ (tsupport ζ)ᶜ) ∧ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U ∪ (tsupport ζ)ᶜ ∧
      ContDiffOn ℝ 2 (ζ * u) (U ∪ (tsupport ζ)ᶜ)) ∧
    (∀ x, ⟪x, ν⟫_ℝ = c₀ → (ζ * u) x = 0) ∧
    (∃ J, HolderOnWith J α (iteratedFDeriv ℝ 2 (ζ * u)) {x | c₀ ≤ ⟪x, ν⟫_ℝ}) ∧
    MemLp (iteratedFDeriv ℝ 2 (ζ * u)) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) ∧
    (eLpNorm (iteratedFDeriv ℝ 2 (ζ * u)) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ})).toReal ≤
      (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) * (((n : ℝ) + 1) ^ 2 * (4 * Z)) * N ∧
    Function.support (iteratedFDeriv ℝ 2 (ζ * u)) ⊆ closedBall x₀ R ∧
    HolderOnWith (Z * K + N * B₂) α (fun x => ∑ i, ∑ j, a x i j •
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      {x | c₀ < ⟪x, ν⟫_ℝ} := by
  subst hB₂ hδ
  set Hc : Set E := {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  have hoc : Ho ⊆ Hc := fun _ hx => mem_ofPred.2 (mem_ofPred.1 hx).le
  set W : Set E := U ∪ (tsupport ζ)ᶜ
  have hWo : IsOpen W := hU.union (isClosed_tsupport ζ).isOpen_compl
  have hHW : Hc ⊆ W := fun x hx => by
    by_cases hxζ : x ∈ tsupport ζ
    · exact Or.inl (hBU ⟨hζs hxζ, hx⟩)
    · exact Or.inr hxζ
  -- `w = ζ u` is `C²` on `W`: it is a product of `C²` functions on `U`, and vanishes off the
  -- support of `ζ`.
  have hw : ContDiffOn ℝ 2 (ζ * u) W := contDiffOn_of_locally_contDiffOn fun x hx => by
    rcases hx with hx | hx
    · exact ⟨U, hU, hx, (hζ.contDiffOn.mul hu).mono inter_subset_right⟩
    · refine ⟨(tsupport ζ)ᶜ, (isClosed_tsupport ζ).isOpen_compl, hx,
        (contDiffOn_const (c := (0 : ℝ))).congr fun y hy => ?_⟩
      simp [image_eq_zero_of_notMem_tsupport hy.2]
  have hw0 (x : E) (hx : ⟪x, ν⟫_ℝ = c₀) : (ζ * u) x = 0 := by
    by_cases hxB : x ∈ ball x₀ R
    · simp [hu0 x hxB hx]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hxB (hζs h)]
  -- The bounds and Hölder constants of `u` and its first two derivatives on `B_R ∩ closure H`.
  set s : Set E := ball x₀ R ∩ Hc
  have hsc : Convex ℝ s := by
    have h : Hc = {x | c₀ ≤ innerSL ℝ ν x} := Set.ext fun x => by simp [Hc, real_inner_comm]
    exact (convex_ball x₀ R).inter (h ▸ convex_halfSpace_ge (innerSL ℝ ν).toLinearMap.isLinear c₀)
  have hsU : s ⊆ U := hBU
  have hsR : s ⊆ ball x₀ R := inter_subset_left
  obtain ⟨hHu, hdu, hdu', hd2u, hVe⟩ :=
    entries_of_convex_of_norm_le hα1 hsc hsR hU hsU hu hN1 hN2 hV
  -- The Hessian entries of `w` on the closed half-space.
  have hWH (i j : Fin (n + 1)) := holderOnWith_fderiv_fderiv_cutoff_mul hU hζ hZ0 hZ1 hZ2 hB
    (fun x hx => hHW hx) (fun x hx hxs h => hxs (mem_inter (hζs h) hx)) hu hN0 hdu' hd2u hHu
    hdu hVe i j
  have hJ : HolderOnWith _ α (iteratedFDeriv ℝ 2 (ζ * u)) Hc :=
    .of_apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) fun i j => by
      simpa [iteratedFDeriv_two_apply] using (hWH i j).1
  -- The `L²(H)` norm of the Hessian of `w`.
  have hbound (x : E) (hx : x ∈ Ho) :
      ‖iteratedFDeriv ℝ 2 (ζ * u) x‖ ≤ ((n : ℝ) + 1) ^ 2 * (4 * Z) * N := by
    have h := (iteratedFDeriv ℝ 2 (ζ * u) x).opNorm_le_card_sq_mul_of_norm_apply_le
      (EuclideanSpace.basisFun _ ℝ) (B := 4 * Z * N) fun i j => by
        simpa [iteratedFDeriv_two_apply] using (hWH i j).2 x (hoc hx)
    simpa [mul_assoc] using h
  have hsupp : Function.support (iteratedFDeriv ℝ 2 (ζ * u)) ⊆ closedBall x₀ R :=
    (support_iteratedFDeriv_subset 2).trans
      (tsupport_mul_subset_left.trans (hζs.trans ball_subset_closedBall))
  obtain ⟨hmem, hL2⟩ := memLp_and_toReal_eLpNorm_le_of_support_subset_closedBall hWo hw
    (hoc.trans hHW) hsupp (by positivity) hbound
  refine ⟨⟨hWo, hHW, hw⟩, hw0, ⟨_, hJ⟩, hmem, hL2.trans_eq (by ring), hsupp, ?_⟩
  -- The operator applied to `w`, on the open half-space.
  have hso : ball x₀ R ∩ Ho ⊆ s := inter_subset_inter_right _ hoc
  refine (holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul hU hζ hZ0 hZ1 hZ2 hB
    (fun x hx => hHW (hoc hx)) (fun x hx hxs h => hxs (mem_inter (hζs h) hx)) hu
    (fun x hx => hN0 x (hso hx)) (fun i x hx => hdu' i x (hso hx))
    (fun i j x hx => hd2u i j x (hso hx)) (hHu.mono hso) (fun i => (hdu i).mono hso) hL hM
    hK).mono_const (le_of_eq ?_)
  ring

/-- The comparison of constants closing the estimate: if `X ≤ A N`, then
`2 κ ((Z K + N B) / λ + Q X) ≤ 2 κ (Z / λ + B / λ + Q A) (K + N)`. -/
private theorem cutoff_constant_le {κ lam Z B Q A K N X : ℝ} (hκ : 0 ≤ κ) (hlam : 0 < lam)
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hX : X ≤ A * N) :
    2 * κ * ((Z * K + N * B) / lam + Q * X) ≤ 2 * κ * (Z / lam + B / lam + Q * A) * (K + N) := by
  have hZl : 0 ≤ Z / lam := by positivity
  have hBl : 0 ≤ B / lam := by positivity
  have hQA : 0 ≤ Q * A := mul_nonneg hQ hA
  calc 2 * κ * ((Z * K + N * B) / lam + Q * X)
      ≤ 2 * κ * (Z / lam * K + B / lam * N + Q * A * N) := by
        rw [add_div, mul_div_right_comm, mul_comm N B, mul_div_right_comm, mul_assoc Q A]
        gcongr
    _ ≤ 2 * κ * (Z / lam + B / lam + Q * A) * (K + N) := by
        rw [mul_assoc (2 * κ)]
        gcongr
        nlinarith

/-- **The Schauder estimate on small half-balls at a flat boundary.** Let `0 < α < 1`. There is
`C₀ > 0`, depending only on the dimension and `α`, with the following property. Let `0 < λ`, `Λ`,
`L`, `M` and `R` be given, put `κ = C₀ (Λ / λ)^(1 + (n+1)/4 + α/2)`, and assume the scale condition

`2 κ (n+1)² (1 + 2ᵅ) L Rᵅ ≤ λ`.

Then for every `ρ < R` there is `C`, depending only on `n`, `α`, `λ`, `Λ`, `L`, `M`, `R` and `ρ`,
with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}`, `ν ≠ 0`, and let `x₀ ∈ closure H`.
Let `a` be `α`-Hölder entrywise with constant `L` on `closedBall x₀ R ∩ closure H` and bounded
entrywise by `M` on `B_R ∩ H`, and suppose `a x₀` has ellipticity bounds `λ, Λ`. Put
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an open set containing `B_R ∩ closure H`, vanishing on
`B_R ∩ ∂H`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `B_R ∩ closure H` and with `D²u`
`α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `B_R ∩ H` with constant `K`, then
`D²u` is `α`-Hölder on `closedBall x₀ ρ ∩ closure H` with constant `C (K + N)`.

Only values of `u` and `a` in the closed half-space enter. The constant `C` does not depend on the
centre `x₀`, the half-space or the coefficient field `a` beyond the bounds `λ`, `Λ`, `L` and `M`. -/
theorem
    exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_halfSpace
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {lam Lam : ℝ} {L M : ℝ≥0} {R : ℝ}, 0 < lam →
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((1 + 2 ^ (α : ℝ)) * L * R ^ (α : ℝ)) ≤ lam →
      ∀ {ρ : ℝ}, ρ < R → ∃ C : ℝ≥0,
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ ν : E} {c₀ : ℝ}, ν ≠ 0 →
      c₀ ≤ ⟪x₀, ν⟫_ℝ →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ})) →
      (∀ x ∈ ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}, ∀ i j, |a x i j| ≤ M) →
      ∀ {U : Set E} {u : E → ℝ} {N K V : ℝ≥0}, IsOpen U →
        ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U → ContDiffOn ℝ 2 u U →
        (∀ x ∈ ball x₀ R, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
        (∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, |u x| ≤ N) →
        (∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
          (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u)
          (closedBall x₀ ρ ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}) := by
  obtain ⟨C₀, hC₀, hCS⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_of_support_subset_closedBall_of_halfSpace hα hα1
      (n := n)
  refine ⟨C₀, hC₀, fun {lam Lam L M R} hlam hsmall {ρ} hρR => ?_⟩
  -- If `R ≤ 0` then `ρ < 0` and the closed ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · exact ⟨0, fun {a x₀ ν c₀} _ _ _ _ _ _ {U u N K V} _ _ _ _ _ _ _ _ _ => by
      rw [closedBall_eq_empty.2 (hρR.trans_le hR), empty_inter]
      exact holderOnWith_empty _ _ _⟩
  -- A cutoff `ζ₀`, equal to one near `closedBall 0 ρ` and supported in `B(0, R)`, and its
  -- constant `Z`, which serves for its translates about every centre.
  obtain ⟨ζ₀, hζ₀, -, hζ₀1, hζ₀c, hζ₀s⟩ :=
    (isCompact_closedBall (0 : E) ρ).exists_contDiff_cutoff isOpen_ball
      (closedBall_subset_ball hρR)
  obtain ⟨Z, hZ⟩ := exists_forall_holderWith_translate_and_norm_le hα1.le hζ₀ hζ₀c
  -- The constants of the estimate, which do not depend on `u`, `a`, `x₀` or the half-space.
  set δ : ℝ≥0 := (2 * R).toNNReal ^ ((1 : ℝ) - α)
  set κ : ℝ := C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  set Q : ℝ := ((n : ℝ) + 1) ^ 2 * (L * 2 ^ (α : ℝ)) / lam *
      (volume (ball (0 : E) (R / 2)) ^ (-((2 : ℝ)⁻¹))).toReal + R ^ (-(((n : ℝ) + 1) / 2 + α))
  set B₂ : ℝ≥0 := (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))
  set A₃ : ℝ := (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) * (((n : ℝ) + 1) ^ 2 * (4 * Z))
  refine ⟨(2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal,
    fun {a x₀ ν c₀} hν hx₀ hEll hEll' hL hM {U u N K V} hU hBU hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  -- The cutoff `ζ` about `x₀`, the translate of `ζ₀`, and the cutoff product `w = ζ u`.
  set ζ : E → ℝ := fun x => ζ₀ (x - x₀)
  obtain ⟨⟨hZ0, hZ1, hZ2⟩, hB⟩ := hZ x₀
  have hζ2 : ContDiff ℝ 2 ζ := (hζ₀.of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const)
  have hζ1 : closedBall x₀ ρ ⊆ interior (ζ ⁻¹' {1}) := fun x hx =>
    preimage_interior_subset_interior_preimage (continuous_id.sub continuous_const)
      (hζ₀1 (by simpa [dist_eq_norm] using hx))
  have hζs : tsupport ζ ⊆ ball x₀ R := fun x hx => by
    simpa [dist_eq_norm] using hζ₀s (tsupport_comp_subset_preimage ζ₀
      (continuous_id.sub continuous_const) hx)
  have hoB : ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ} ⊆ closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} :=
    inter_subset_inter ball_subset_closedBall fun _ hx => mem_ofPred.2 (mem_ofPred.1 hx).le
  obtain ⟨⟨hWo, hHW, hw⟩, hw0, hJ, hmem, hL2, hsupp, hLw⟩ := cutoff_mul_data_of_halfSpace
    hα1.le hζ2 hζs hZ0 hZ1 hZ2 hB hU hBU hu hu0 hN0 hN1 hN2 hV (fun i j => (hL i j).mono hoB) hM
    hK (δ := δ) (B₂ := B₂) rfl rfl
  -- The estimate up to the boundary for a Hessian supported in a ball, at the radius `R`.
  have hsmall' : 2 * κ * ((n : ℝ) + 1) ^ 2 *
      (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * R ^ (α : ℝ)) ≤ lam := by
    convert hsmall using 2
    ring
  have key := hCS hν hx₀ hlam hEll hEll' (L := L) (K := Z * K + N * B₂) (r := R) hR.le hR
    hsmall' hL hWo hHW hw hw0 hJ hmem (fun x hx => hsupp hx.1) hLw
  -- Comparison of the constants.
  have hlamLam : lam ≤ Lam := by
    have h := (hEll (EuclideanSpace.single 0 1)).trans (hEll' (EuclideanSpace.single 0 1))
    simpa using h
  have hκ : 0 ≤ κ := mul_nonneg hC₀.le
    (Real.rpow_nonneg (div_nonneg (hlam.le.trans hlamLam) hlam.le) _)
  have hbound : 2 * κ * (((Z * K + N * B₂ : ℝ≥0) : ℝ) / lam +
      Q * (eLpNorm (iteratedFDeriv ℝ 2 (ζ * u)) 2
        (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ})).toReal) ≤
      ((2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal * (K + N) : ℝ≥0) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    push_cast
    exact cutoff_constant_le hκ hlam Z.coe_nonneg B₂.coe_nonneg (by positivity) (by positivity)
      K.coe_nonneg N.coe_nonneg hL2
  -- On a neighbourhood of `closedBall x₀ ρ` the cutoff is one, so `D²w = D²u` there.
  have hwu (x : E) (hx : x ∈ closedBall x₀ ρ) :
      iteratedFDeriv ℝ 2 (ζ * u) x = iteratedFDeriv ℝ 2 u x :=
    Filter.EventuallyEq.iteratedFDeriv_mul_eq (by
      filter_upwards [mem_interior_iff_mem_nhds.1 (hζ1 hx)] with y hy
      simpa using hy)
  intro x hx y hy
  rw [← hwu x hx.1, ← hwu y hy.1]
  refine (key x hx.2 y hy.2).trans ?_
  gcongr
  exact Real.toNNReal_le_iff_le_coe.2 hbound

end TauCeti.PDE
