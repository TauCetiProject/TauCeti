/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.VariableCoefficient
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Cutoff
import TauCeti.MeasureTheory.Function.LpSeminorm.Support

/-!
# The Schauder estimate near a flat boundary portion

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, with closure
`closure H = {x | c₀ ≤ ⟪x, ν⟫}`, let `0 < α < 1`, and let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a
non-divergence-form operator whose coefficients are `α`-Hölder with constant `L` on
`closedBall x₀ R ∩ closure H`, for a centre `x₀ ∈ closure H`, with `a(x₀)` elliptic with constants
`0 < λ ≤ Λ`. This file proves the `C^{2,α}` estimate near the flat boundary portion
`ball x₀ R ∩ ∂H` for solutions vanishing there
(`exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_halfSpace`,
in the `TauCeti.PDE` namespace). If `R` is small compared with the Hölder modulus of the
coefficients, then for every `ρ < R` there is a constant `C`, independent of the solution, such that
every `u` which is `C²` on an open set containing `ball x₀ R ∩ closure H`, vanishes on
`ball x₀ R ∩ ∂H` and has `α`-Hölder Hessian on `ball x₀ R ∩ closure H` satisfies

`[D²u]_{α; closedBall x₀ ρ ∩ closure H} ≤ C ([L u]_{α; ball x₀ R ∩ H} + N)`,

where `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on `ball x₀ R ∩ closure H`. The Hölder constant of the
Hessian enters only qualitatively. The constant `C` depends on the coefficients only through `λ`,
`Λ`, `L` and a bound `M` for their entries, and not on the centre `x₀` or on the half-space. This is
the boundary counterpart of the interior estimate on small balls
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`), and
the local estimate that the global `C^{2,α}` estimate on a domain with `C^{2,α}` boundary
transports through boundary-flattening charts and patches together by a covering.

The estimate is proved in two steps, as in the interior.

* **Compact support**
  (`exists_holderOnWith_iteratedFDeriv_two_of_support_subset_closedBall_of_halfSpace`). If the
  Hessian of `u` vanishes in `H` outside `closedBall x₀ R`, the coefficients may be replaced
  by `a ∘ q`, where `q` is the radial retraction onto `closedBall x₀ R`: it moves points of
  `closure H` along segments towards `x₀ ∈ closure H`, so it maps `closure H` into
  `closedBall x₀ R ∩ closure H`, where `a` is Hölder. The new coefficients are Hölder on `H`, within
  `L Rᵅ` of `a(x₀)`, and give the same operator on `u`, so the estimate up to a flat boundary for
  coefficients of small oscillation applies.
* **Cutoff.** For a cutoff `ζ` equal to one near `closedBall x₀ ρ` and supported in `ball x₀ R`,
  the product `w = ζ u` is `C²` on an open set containing `closure H`, vanishes on `∂H`, and its
  Hessian vanishes outside `closedBall x₀ R`. The Hölder constant of `L w` on `H` and the `L²` norm
  of `D²w` on `H` are bounded by `C (K + N)` and `C N`
  (`TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul`), and `D²w = D²u` near
  `closedBall x₀ ρ`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2, the boundary estimate by freezing coefficients (Lemma 6.5) and its localization
  by cutoffs.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped InnerProductSpace NNReal ENNReal ContDiff

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- At a point where the Hessian of `u` vanishes unless the radial retraction `q` onto
`closedBall x₀ R` fixes the point, the coefficients `a ∘ q` and `a` give the same value of
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. -/
private theorem sum_smul_fderiv_fderiv_comp_centeredRadialRetraction_eq
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {u : E → ℝ} {x₀ x : E} {R : ℝ}
    (hx : x ∈ Function.support (iteratedFDeriv ℝ 2 u) → x ∈ closedBall x₀ R) :
    ∑ i, ∑ j, a (TauCeti.centeredRadialRetraction x₀ R x) i j •
        fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      ∑ i, ∑ j, a x i j •
        fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  by_cases hx' : x ∈ Function.support (iteratedFDeriv ℝ 2 u)
  · simp only [TauCeti.centeredRadialRetraction_of_mem_closedBall (hx hx')]
  · have hentry (i j : Fin (n + 1)) : fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
      have hzero := congrArg (fun H : E [×2]→L[ℝ] ℝ =>
        H ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
        (Function.notMem_support.1 hx')
      simpa only [iteratedFDeriv_two_apply, zero_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one] using hzero
    simp [hentry]

/-- **Schauder estimate up to a flat boundary for a Hessian supported in a ball.** Let
`0 < α < 1`. There is `C > 0`, depending only on dimension and `α`, with the following property.
Let `H = {x | c₀ < ⟪x, ν⟫}`, `ν ≠ 0`, let `x₀ ∈ closure H`, let `a` be `α`-Hölder entrywise with
constant `L` on `closedBall x₀ R ∩ closure H`, and suppose `a x₀` has ellipticity bounds `λ, Λ`,
with `λ > 0`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu` and `κ = C (Λ / λ)^(1 + (n+1)/4 + α/2)`. Let `u` be `C²` on
an open set containing `closure H`, vanishing on `∂H`, with `D²u` `α`-Hölder on `closure H`, in
`L²(H)` and vanishing in `H` outside `closedBall x₀ R`. Then the scale condition

`2 κ (n+1)² (L Rᵅ + 2ᵅ L rᵅ) ≤ λ`

implies

`[D²u]_{α; closure H} ≤ 2 κ ([L u]_{α; H} / λ + Q ‖D²u‖_{L²(H)})`, where
`Q = (n+1)² 2ᵅ L / λ |B_{r/2}|^(-1/2) + r^(-(n+1)/2-α)`.

No uniform comparison of `a` with one constant matrix is assumed: the support condition allows
the coefficients to be retracted to the ball and frozen at its centre. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_support_subset_closedBall_of_halfSpace
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ ν : E} {c₀ lam Lam : ℝ},
      0 < lam → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) → ν ≠ 0 → c₀ ≤ ⟪x₀, ν⟫_ℝ →
      ∀ {L K : ℝ≥0} {R r : ℝ}, 0 ≤ R → 0 < r →
      2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * r ^ (α : ℝ)) ≤ lam →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ})) →
      ∀ {U : Set E} {u : E → ℝ}, IsOpen U → {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U → ContDiffOn ℝ 2 u U →
      (∀ x, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
      (∃ J, HolderOnWith J α (iteratedFDeriv ℝ 2 u) {x | c₀ ≤ ⟪x, ν⟫_ℝ}) →
      Function.support (iteratedFDeriv ℝ 2 u) ∩ {x | c₀ < ⟪x, ν⟫_ℝ} ⊆ closedBall x₀ R →
      MemLp (iteratedFDeriv ℝ 2 u) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) →
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
  refine ⟨C₀, hC₀, fun {a x₀ ν c₀ lam Lam} hlam hEll hEll' hν hx₀ {L K R r} hR hr hsmall hL
    {U u} hU hHU hu hu0 hJ hsupp hH2 hf => ?_⟩
  set Hc : Set E := {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  let q : E → E := TauCeti.centeredRadialRetraction x₀ R
  let a' : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun x => a (q x)
  -- The retraction maps the closed half-space into the part of the closed ball in it.
  have hq (x : E) (hx : x ∈ Hc) : q x ∈ closedBall x₀ R ∩ Hc :=
    ⟨TauCeti.centeredRadialRetraction_mem_closedBall hR x,
      (convex_setOf_le_inner ν c₀).segment_subset hx₀ hx
        (TauCeti.centeredRadialRetraction_mem_segment hR x)⟩
  have hx₀' : x₀ ∈ closedBall x₀ R ∩ Hc := ⟨mem_closedBall_self hR, hx₀⟩
  have ha'_holder (i j : Fin (n + 1)) :
      HolderOnWith (L * 2 ^ (α : ℝ)) α (fun x => a' x i j) Ho := by
    have h := (hL i j).comp
      ((TauCeti.lipschitzWith_centeredRadialRetraction (x₀ := x₀) hR).holderWith.holderOnWith Ho)
      fun x hx => hq x (mem_ofPred.2 (mem_ofPred.1 hx).le)
    rw [mul_one] at h
    exact h
  let ε : ℝ≥0 := (L * R ^ (α : ℝ)).toNNReal
  have hε : (ε : ℝ) = L * R ^ (α : ℝ) :=
    Real.coe_toNNReal _ (mul_nonneg L.coe_nonneg (Real.rpow_nonneg hR _))
  have ha'_close (x : E) (hx : c₀ < ⟪x, ν⟫_ℝ) (i j : Fin (n + 1)) :
      |a' x i j - a x₀ i j| ≤ ε := by
    have hqx := hq x hx.le
    rw [hε]
    simpa only [a', Real.dist_eq] using
      ((hL i j).dist_le hqx hx₀').trans (by gcongr; exact mem_closedBall.1 hqx.1)
  -- On `H` the retracted coefficients give the same operator on `u`.
  have hf' : HolderOnWith K α (fun x => ∑ i, ∑ j, a' x i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ho := by
    have heq (x : E) (hx : x ∈ Ho) := sum_smul_fderiv_fderiv_comp_centeredRadialRetraction_eq
      (a := a) (u := u) fun hx' => hsupp ⟨hx', hx⟩
    intro x hx y hy
    have h := hf x hx y hy
    dsimp only at h ⊢
    rwa [heq x hx, heq y hy]
  have hsmall' :
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((ε : ℝ) + (L * 2 ^ (α : ℝ) : ℝ≥0) * r ^ (α : ℝ)) ≤ lam := by
    simpa only [hε, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat] using hsmall
  exact hS (A := a x₀) (a := a') hlam hEll hEll' (L := L * 2 ^ (α : ℝ)) (K := K) (ε := ε) hν hr
    hsmall' ha'_close ha'_holder hU hHU hu hu0 hJ hH2 hf'

/-- The cutoff product `ζ u` of a cutoff `ζ` supported in the ball `B_R` and a function `u` which
is `C²` on an open set containing `B_R ∩ closure H`, with bounds `N` on `u` and its first two
derivatives and a Hölder Hessian there, has a Hessian which is Hölder on `closure H` and bounded
there by `(n+1)² 4 Z N`, and `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u)` is Hölder on `H` with constant `Z K + N B₂`. The
constants `δ` and `B₂` are given by their definitions. -/
private theorem cutoff_mul_data_of_halfSpace {ζ u : E → ℝ} {x₀ ν : E} {c₀ R : ℝ} {U : Set E}
    {α Z N K V L M δ B₂ : ℝ≥0} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hα1 : α ≤ 1)
    (hζ2 : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ ball x₀ R)
    (hZ0 : HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hU : IsOpen U) (hUsub : ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hN0 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, |u x| ≤ N)
    (hN1 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N)
    (hV : HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}))
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}))
    (hM : ∀ x ∈ ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}, ∀ i j, |a x i j| ≤ M)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))
    (hδ : δ = (2 * R).toNNReal ^ ((1 : ℝ) - α))
    (hB₂ : B₂ = (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))) :
    (∃ J, HolderOnWith J α (iteratedFDeriv ℝ 2 (ζ * u)) {x | c₀ ≤ ⟪x, ν⟫_ℝ}) ∧
      HolderOnWith (Z * K + N * B₂) α (fun x => ∑ i, ∑ j, a x i j •
        fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
        {x | c₀ < ⟪x, ν⟫_ℝ} ∧
      ∀ x ∈ {x | c₀ ≤ ⟪x, ν⟫_ℝ},
        ‖iteratedFDeriv ℝ 2 (ζ * u) x‖ ≤ ((n : ℝ) + 1) ^ 2 * (4 * Z * N) := by
  subst hB₂ hδ
  set Hc : Set E := {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  have hoc : Ho ⊆ Hc := fun _ hx => mem_ofPred.2 (mem_ofPred.1 hx).le
  have hoc' : ball x₀ R ∩ Ho ⊆ ball x₀ R ∩ Hc := inter_subset_inter_right _ hoc
  obtain ⟨hHu, hHdu⟩ := holderOnWith_and_holderOnWith_fderiv_apply_single
    ((convex_ball x₀ R).inter (convex_setOf_le_inner ν c₀)) inter_subset_left hα1 hU hUsub hu
    hN1 hN2
  have hdu (i : Fin (n + 1)) (x : E) (hx : x ∈ ball x₀ R ∩ Hc) :
      |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N := by
    simpa using ((fderiv ℝ u x).unit_le_opNorm (EuclideanSpace.single i 1) (by simp)).trans
      (hN1 x hx)
  have hd2u (i j : Fin (n + 1)) (x : E) (hx : x ∈ ball x₀ R ∩ Hc) :
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N := by
    simpa [iteratedFDeriv_two_apply] using
      ((iteratedFDeriv ℝ 2 u x).norm_apply_orthonormalBasis_le
        (EuclideanSpace.basisFun _ ℝ) i j).trans (hN2 x hx)
  have hζU : tsupport ζ ∩ Hc ⊆ U := fun x hx => hUsub ⟨hζs hx.1, hx.2⟩
  have hWH := holderOnWith_fderiv_fderiv_cutoff_mul hU hζ2 hζs hζU hZ0 hZ1 hZ2 hu hN0 hdu hd2u
    hHu hHdu fun i j => by
      simpa [iteratedFDeriv_two_apply] using
        hV.apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j
  refine ⟨⟨_, .of_apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) fun i j => by
      simpa [iteratedFDeriv_two_apply] using (hWH i j).1⟩,
    (holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul hU hζ2 hζs
      (fun x hx => hζU ⟨hx.1, hoc hx.2⟩) hZ0 hZ1 hZ2 hu (fun x hx => hN0 x (hoc' hx))
      (fun i x hx => hdu i x (hoc' hx)) (fun i j x hx => hd2u i j x (hoc' hx)) (hHu.mono hoc')
      (fun i => (hHdu i).mono hoc')
      (fun i j => (hL i j).mono (inter_subset_inter ball_subset_closedBall hoc))
      hM hK).mono_const
      (le_of_eq (by ring)), fun x hx => ?_⟩
  refine ((iteratedFDeriv ℝ 2 (ζ * u) x).opNorm_le_card_sq_mul_of_norm_apply_le
    (EuclideanSpace.basisFun _ ℝ) (B := 4 * Z * N) fun i j => ?_).trans_eq (by simp)
  simpa [iteratedFDeriv_two_apply] using (hWH i j).2 x hx

/-- A cutoff product `ζ u`, for `ζ` supported in `B_R` and `u` which is `C²` on an open set
containing `B_R ∩ closure H` and vanishes on `B_R ∩ ∂H`, is `C²` on an open set containing
`closure H`, vanishes on `∂H`, and has Hessian vanishing outside `closedBall x₀ R`. -/
private theorem exists_contDiffOn_cutoff_mul_of_halfSpace {ζ u : E → ℝ} {x₀ ν : E} {c₀ R : ℝ}
    {U : Set E} (hζ2 : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ ball x₀ R) (hU : IsOpen U)
    (hUsub : ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hu0 : ∀ x ∈ ball x₀ R, ⟪x, ν⟫_ℝ = c₀ → u x = 0) :
    ∃ U' : Set E, IsOpen U' ∧ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U' ∧ ContDiffOn ℝ 2 (ζ * u) U' ∧
      (∀ x, ⟪x, ν⟫_ℝ = c₀ → (ζ * u) x = 0) ∧
      Function.support (iteratedFDeriv ℝ 2 (ζ * u)) ⊆ closedBall x₀ R := by
  refine ⟨U ∪ (tsupport ζ)ᶜ, hU.union (isClosed_tsupport ζ).isOpen_compl, fun x hx => ?_,
    fun x hx => ?_, fun x hx => ?_, (support_iteratedFDeriv_subset 2).trans
      (tsupport_mul_subset_left.trans (hζs.trans ball_subset_closedBall))⟩
  · by_cases h : x ∈ tsupport ζ
    · exact Or.inl (hUsub ⟨hζs h, hx⟩)
    · exact Or.inr h
  · refine ContDiffAt.contDiffWithinAt ?_
    rcases hx with hx | hx
    · exact hζ2.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport ζ).isOpen_compl.mem_nhds hx] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  · by_cases h : x ∈ ball x₀ R
    · simp [hu0 x h hx]
    · simp [image_eq_zero_of_notMem_tsupport fun h' => h (hζs h')]

/-- If `w` is `C²` on an open set containing `closure H` and its Hessian vanishes outside
`closedBall x₀ R` and is bounded by `B` on `closure H`, then the Hessian is in `L²(H)`, with
`L²(H)` norm at most `|closedBall 0 R|^{1/2} B`. -/
private theorem memLp_and_toReal_eLpNorm_iteratedFDeriv_two_le_of_halfSpace {w : E → ℝ}
    {U : Set E} {x₀ ν : E} {c₀ R B : ℝ} (hU : IsOpen U) (hHU : {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U)
    (hw : ContDiffOn ℝ 2 w U) (hsupp : Function.support (iteratedFDeriv ℝ 2 w) ⊆ closedBall x₀ R)
    (hB : ∀ x ∈ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 w x‖ ≤ B) (hB0 : 0 ≤ B) :
    MemLp (iteratedFDeriv ℝ 2 w) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) ∧
      (eLpNorm (iteratedFDeriv ℝ 2 w) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ})).toReal ≤
        (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) * B := by
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  have hoc (x : E) (hx : x ∈ Ho) : x ∈ {x | c₀ ≤ ⟪x, ν⟫_ℝ} := mem_ofPred.2 (mem_ofPred.1 hx).le
  have hHo : IsOpen Ho := isOpen_lt continuous_const (continuous_id.inner continuous_const)
  have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ 2 w) (volume.restrict Ho) :=
    ((ContinuousOn.continuousOn_iteratedFDeriv hw hU le_rfl).mono fun x hx =>
      hHU (hoc x hx)).aestronglyMeasurable hHo.measurableSet
  have hle : eLpNorm (iteratedFDeriv ℝ 2 w) 2 (volume.restrict Ho) ≤
      volume (closedBall (0 : E) R) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal B := by
    refine (eLpNorm_le_of_ae_bound_of_support_subset hmeas hsupp
      (ae_restrict_of_forall_mem hHo.measurableSet fun x hx => hB x (hoc x hx))).trans ?_
    rw [← Measure.addHaar_closedBall_center volume x₀ R]
    gcongr
    exact Measure.restrict_le_self
  have hfin : volume (closedBall (0 : E) R) ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      measure_closedBall_lt_top.ne) ENNReal.ofReal_ne_top
  refine ⟨memLp_iff.2 (hle.trans_lt hfin.lt_top), (ENNReal.toReal_mono hfin hle).trans_eq ?_⟩
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB0, ENNReal.toReal_ofNat]

/-- **The Schauder estimate near a flat boundary portion.** Let `0 < α < 1`. There is `C₀ > 0`,
depending only on dimension and `α`, with the following property. Let `0 < λ`, `Λ`, `L`, `M` and
`R` be given, put `κ = C₀ (Λ / λ)^(1 + (n+1)/4 + α/2)`, and assume the scale condition

`2 κ (n+1)² (1 + 2ᵅ) L Rᵅ ≤ λ`.

Then for every `ρ < R` there is `C`, depending only on `n`, `α`, `λ`, `Λ`, `L`, `M`, `R` and `ρ`,
with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}`, `ν ≠ 0`, and `x₀ ∈ closure H`. Let `a`
be `α`-Hölder entrywise with constant `L` on `closedBall x₀ R ∩ closure H` and bounded entrywise
by `M` on `B_R ∩ H`, and suppose `a x₀` has ellipticity bounds `λ, Λ`. Put
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an open set containing `B_R ∩ closure H`, vanishing on
`B_R ∩ ∂H`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `B_R ∩ closure H` and with `D²u`
`α`-Hölder there (with any constant). If `L u` is `α`-Hölder on `B_R ∩ H` with constant `K`, then
`D²u` is `α`-Hölder on `closedBall x₀ ρ ∩ closure H` with constant `C (K + N)`.

The constant `C` does not depend on the centre `x₀`, on the half-space or on the coefficient field
`a` beyond the bounds `λ`, `Λ`, `L` and `M`. -/
theorem
    exists_holderOnWith_iteratedFDeriv_two_closedBall_inter_of_sum_smul_fderiv_fderiv_of_halfSpace
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {lam Lam : ℝ} {L M : ℝ≥0} {R : ℝ}, 0 < lam →
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((1 + 2 ^ (α : ℝ)) * L * R ^ (α : ℝ)) ≤ lam →
      ∀ {ρ : ℝ}, ρ < R → ∃ C : ℝ≥0,
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ ν : E} {c₀ : ℝ},
      ν ≠ 0 → c₀ ≤ ⟪x₀, ν⟫_ℝ →
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
    exists_holderOnWith_iteratedFDeriv_two_of_support_subset_closedBall_of_halfSpace hα hα1 (n := n)
  refine ⟨C₀, hC₀, fun {lam Lam L M R} hlam hsmall {ρ} hρR => ?_⟩
  -- If `R ≤ 0` then `ρ < 0` and the closed ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · exact ⟨0, fun {a x₀ ν c₀} _ _ _ _ _ _ {U u N K V} _ _ _ _ _ _ _ _ _ => by
      rw [closedBall_eq_empty.2 (hρR.trans_le hR), empty_inter]
      exact holderOnWith_empty _ _ _⟩
  -- Cutoffs about every centre, equal to one near `closedBall x₀ ρ` and supported in `B(x₀, R)`,
  -- with one constant `Z`.
  obtain ⟨Z, hcut⟩ := exists_cutoff_holderWith_and_abs_le (n := n) hα1.le hρR
  -- The constants of the estimate, which do not depend on `u`, `a`, `x₀` or the half-space.
  set δ : ℝ≥0 := (2 * R).toNNReal ^ ((1 : ℝ) - α)
  set κ : ℝ := C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  set Q : ℝ := ((n : ℝ) + 1) ^ 2 * (L * 2 ^ (α : ℝ)) / lam *
      (volume (ball (0 : E) (R / 2)) ^ (-((2 : ℝ)⁻¹))).toReal + R ^ (-(((n : ℝ) + 1) / 2 + α))
  set B₂ : ℝ≥0 := (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))
  set A₃ : ℝ := (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) * (((n : ℝ) + 1) ^ 2 * (4 * Z))
  refine ⟨(2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal,
    fun {a x₀ ν c₀} hν hx₀ hEll hEll' hL hM {U u N K V} hU hUsub hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  obtain ⟨ζ, hζ2, hζs, hwu, hZ0, hZ1, hZ2⟩ := hcut x₀
  -- The cutoff product `ζ u` is `C²` on an open set containing `closure H`, vanishes on `∂H`,
  -- has Hölder data, and its Hessian is in `L²(H)` with norm at most `A₃ N`.
  obtain ⟨hJ, hLw, hbd⟩ := cutoff_mul_data_of_halfSpace hα1.le hζ2 hζs hZ0 hZ1 hZ2 hU hUsub hu
    hN0 hN1 hN2 hV hL hM hK (δ := δ) (B₂ := B₂) rfl rfl
  obtain ⟨U', hU', hHU', hw, hw0, hsupp⟩ :=
    exists_contDiffOn_cutoff_mul_of_halfSpace hζ2 hζs hU hUsub hu hu0
  obtain ⟨hH2, hL2⟩ :=
    memLp_and_toReal_eLpNorm_iteratedFDeriv_two_le_of_halfSpace hU' hHU' hw hsupp hbd
      (by positivity)
  -- The compact-support estimate up to the boundary, at the radius `r = R`.
  have hsmall' : 2 * κ * ((n : ℝ) + 1) ^ 2 *
      (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * R ^ (α : ℝ)) ≤ lam := by
    convert hsmall using 2
    ring
  have key := hCS hlam hEll hEll' hν hx₀ (L := L) (K := Z * K + N * B₂) hR.le hR hsmall' hL hU'
    hHU' hw hw0 hJ (inter_subset_left.trans hsupp) hH2 hLw
  -- Comparison of the constants.
  have hlamLam : lam ≤ Lam := by
    have h := (hEll (EuclideanSpace.single 0 1)).trans (hEll' (EuclideanSpace.single 0 1))
    simpa using h
  have hκ : 0 ≤ κ := mul_nonneg hC₀.le
    (Real.rpow_nonneg (div_nonneg (hlam.le.trans hlamLam) hlam.le) _)
  have hQ : 0 ≤ Q := by positivity
  have hA₃ : 0 ≤ A₃ := by positivity
  have hbound : 2 * κ * (((Z * K + N * B₂ : ℝ≥0) : ℝ) / lam +
      Q * (eLpNorm (iteratedFDeriv ℝ 2 (ζ * u)) 2
        (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ})).toReal) ≤
      ((2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal * (K + N) : ℝ≥0) :=
    two_mul_mul_add_div_add_mul_le_toNNReal_mul hκ hlam hQ hA₃ (hL2.trans_eq (by ring))
  -- The cutoff is one near `closedBall x₀ ρ`, so `D²w = D²u` there.
  intro x hx y hy
  rw [← hwu u x hx.1, ← hwu u y hy.1]
  refine (key x hx.2 y hy.2).trans ?_
  gcongr
  exact Real.toNNReal_le_iff_le_coe.2 hbound

end TauCeti.PDE
