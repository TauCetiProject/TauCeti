/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.VariableCoefficient

import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Cutoff
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Module.Ball.Retraction
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
on the whole of `closure H` (`HolderOnWith.smul_of_eq_zero`, through the cutoff calculus of
`TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul`). On the convex set
`B_R ∩ closure H` the functions `u` and `Du` are Lipschitz, with constant `N`, hence `α`-Hölder.
This bounds the Hölder constant of `L w` on `H` by `C (K + N)` and `‖D²w‖_{L²(H)}` by `C N`, and
the estimate for a Hessian supported in a ball bounds the Hölder constant of `D²w` on
`closure H`, which is that of `D²u` near `closedBall x₀ ρ ∩ closure H`.

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
  have hq : MapsTo q Hc (closedBall x₀ R ∩ Hc) :=
    TauCeti.mapsTo_centeredRadialRetraction_of_convex hR (TauCeti.convex_setOf_le_inner ν c₀) hx₀
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
        (EuclideanSpace.single j 1)) Ho :=
    hf.congr (TauCeti.eqOn_sum_sum_smul_fderiv_fderiv_apply
      (v := fun i => EuclideanSpace.single i 1) hsupp fun x hx => by
        simp only [a', q, TauCeti.centeredRadialRetraction_of_mem_closedBall hx]).symm
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
  have hsc : Convex ℝ s := (convex_ball x₀ R).inter (TauCeti.convex_setOf_le_inner ν c₀)
  obtain ⟨hHu, hdu, hdu', hd2u, hVe⟩ := holderOnWith_coordinates_of_convex_of_norm_le hα1 hsc
    inter_subset_left (fun x hx => hu.contDiffAt (hU.mem_nhds (hBU hx))) hN1 hN2 hV
  -- The Hessian entries of `w` on the closed half-space.
  have hWH (i j : Fin (n + 1)) := holderOnWith_fderiv_fderiv_cutoff_mul hU hζ hZ0 hZ1 hZ2 hB
    (fun x hx => hHW hx) (fun x hx hxs h => hxs (mem_inter (hζs h) hx)) hu hN0 hdu' hd2u hHu
    hdu hVe i j
  have hJ : HolderOnWith _ α (iteratedFDeriv ℝ 2 (ζ * u)) Hc :=
    .of_apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) fun i j => by
      simpa [iteratedFDeriv_two_apply] using (hWH i j).1
  -- The `L²(H)` norm of the Hessian of `w`.
  have hsupp : Function.support (iteratedFDeriv ℝ 2 (ζ * u)) ⊆ closedBall x₀ R :=
    (support_iteratedFDeriv_subset 2).trans
      (tsupport_mul_subset_left.trans (hζs.trans ball_subset_closedBall))
  obtain ⟨hmem, hL2⟩ :=
    Measure.memLp_and_toReal_eLpNorm_iteratedFDeriv_two_le_of_support_subset_closedBall (p := 2)
      volume (EuclideanSpace.basisFun _ ℝ)
      (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
      ((ContinuousOn.continuousOn_iteratedFDeriv hw hWo (by norm_num)).mono (hoc.trans hHW)) hsupp
      (B := 4 * Z * N) (by positivity) fun x hx i j => by simpa using (hWH i j).2 x (hoc hx)
  refine ⟨⟨hWo, hHW, hw⟩, hw0, ⟨_, hJ⟩, hmem,
    hL2.trans_eq (by simp only [Fintype.card_fin, ENNReal.toReal_ofNat]; push_cast; ring), hsupp,
    ?_⟩
  -- The operator applied to `w`, on the open half-space.
  have hso : ball x₀ R ∩ Ho ⊆ s := inter_subset_inter_right _ hoc
  refine (holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul hU hζ hZ0 hZ1 hZ2 hB
    (fun x hx => hHW (hoc hx)) (fun x hx hxs h => hxs (mem_inter (hζs h) hx)) hu
    (fun x hx => hN0 x (hso hx)) (fun i x hx => hdu' i x (hso hx))
    (fun i j x hx => hd2u i j x (hso hx)) (hHu.mono hso) (fun i => (hdu i).mono hso) hL hM
    hK).mono_const (le_of_eq ?_)
  ring

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
  -- Cutoffs `ζ x₀`, equal to one near `closedBall x₀ ρ` and supported in `B_R`, with one
  -- constant `Z` for every centre.
  obtain ⟨ζ, Z, hζ⟩ := exists_forall_contDiff_cutoff_holderWith_and_norm_le («E» := E) hρR hα1.le
  -- The constants of the estimate, which do not depend on `u`, `a`, `x₀` or the half-space.
  set δ : ℝ≥0 := (2 * R).toNNReal ^ ((1 : ℝ) - α)
  set κ : ℝ := C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  set Q : ℝ := ((n : ℝ) + 1) ^ 2 * (L * 2 ^ (α : ℝ)) / lam *
      (volume (ball (0 : E) (R / 2)) ^ (-((2 : ℝ)⁻¹))).toReal + R ^ (-(((n : ℝ) + 1) / 2 + α))
  set B₂ : ℝ≥0 := (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))
  set A₃ : ℝ := (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) * (((n : ℝ) + 1) ^ 2 * (4 * Z))
  refine ⟨(2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal,
    fun {a x₀ ν c₀} hν hx₀ hEll hEll' hL hM {U u N K V} hU hBU hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  -- The cutoff product `w = ζ x₀ u`.
  obtain ⟨hζ2, hζ1, hζs, ⟨hZ0, hZ1, hZ2⟩, hB⟩ := hζ x₀
  have hoB : ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ} ⊆ closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} :=
    inter_subset_inter ball_subset_closedBall fun _ hx => mem_ofPred.2 (mem_ofPred.1 hx).le
  obtain ⟨⟨hWo, hHW, hw⟩, hw0, hJ, hmem, hL2, hsupp, hLw⟩ := cutoff_mul_data_of_halfSpace
    hα1.le (hζ2.of_le (by norm_cast)) hζs hZ0 hZ1 hZ2 hB hU hBU hu hu0 hN0 hN1 hN2 hV
    (fun i j => (hL i j).mono hoB) hM hK (δ := δ) (B₂ := B₂) rfl rfl
  -- The estimate up to the boundary for a Hessian supported in a ball, at the radius `R`.
  have hsmall' : 2 * κ * ((n : ℝ) + 1) ^ 2 *
      (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * R ^ (α : ℝ)) ≤ lam := by
    convert hsmall using 2
    ring
  have key := hCS hν hx₀ hlam hEll hEll' (L := L) (K := Z * K + N * B₂) (r := R) hR.le hR
    hsmall' hL hWo hHW hw hw0 hJ hmem (fun x hx => hsupp hx.1) hLw
  -- `ζ x₀` is one near `closedBall x₀ ρ`, so `D²(ζ x₀ u) = D²u` there.
  exact TauCeti.holderOnWith_iteratedFDeriv_inter_of_mul_of_subset_interior
    (key.mono_const (cutoff_constant_le hlam (by positivity) (by positivity)
      ENNReal.toReal_nonneg hL2)) hζ1

end TauCeti.PDE
