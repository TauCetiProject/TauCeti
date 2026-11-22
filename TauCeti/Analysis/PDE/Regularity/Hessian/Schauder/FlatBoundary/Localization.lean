/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.VariableCoefficient
import TauCeti.Analysis.Calculus.BumpFunction.HolderCutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.Analysis.Calculus.IteratedFDeriv.OrthonormalBasis
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.CompactSupport
import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Cutoff
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.MetricSpace.Bounded

/-!
# The Schauder estimate on half-balls at a flat boundary

Let `0 < α < 1`, let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, with
closure `closure H = {x | c₀ ≤ ⟪x, ν⟫}`, and let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a non-divergence-form
operator whose coefficients are `α`-Hölder with constant `L` and bounded by `M` on the closed
half-ball `closedBall x₀ R ∩ closure H` about a point `x₀ ∈ closure H`, with `a(x₀)` elliptic with
constants `0 < λ ≤ Λ`. If `R` is small compared with the Hölder modulus of the coefficients, then
for every `ρ < R` there is a constant `C`, independent of the solution, such that every `u` which
is `C²` up to the flat boundary on the half-ball `B_R ∩ closure H`, vanishes on the flat boundary
`B_R ∩ ∂H` and has an `α`-Hölder Hessian there satisfies

`[D²u]_{α; closedBall x₀ ρ ∩ closure H} ≤ C ([L u]_{α; B_R ∩ H} + N)`,

where `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on `B_R ∩ closure H`. The Hölder constant of the Hessian
enters only qualitatively, and `C` depends on the coefficients only through `λ`, `Λ`, `L` and `M`,
not on `x₀`, `ν` or `c₀`. This is the boundary counterpart of the interior estimate on small balls
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`), and
the estimate near a flat boundary portion from which, after flattening a curved boundary by charts,
the global Schauder estimate on a domain with `C^{2,α}` boundary is assembled.

## The argument

Two steps reduce the estimate to the one up to a flat boundary for coefficients of small
oscillation, in the `TauCeti.PDE` namespace
(`exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_abs_sub_le_of_halfSpace`).

* **Compact support.** If the Hessian of `u` vanishes in `closure H` off `closedBall x₀ R`, the
  coefficients may be replaced by `a ∘ q`, where `q` is the radial retraction onto
  `closedBall x₀ R`. Since `x₀ ∈ closure H`, the retraction moves each point of `closure H` along
  the segment towards `x₀`, so it stays in `closure H`; hence `a ∘ q` is `α`-Hölder on `H` with
  constant `2ᵅ L` and within `L Rᵅ` of `a(x₀)` there, while `L u` does not change where the
  Hessian is nonzero.
* **Cutoff.** For a cutoff `ζ` equal to one near `closedBall x₀ ρ` and supported in `B_R`, the
  product `w = ζ u` is `C²` on an open set containing `closure H`, vanishes on `∂H` and has its
  Hessian supported in `closedBall x₀ R`. The bounds of
  `TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Cutoff`, on the set `t = closure H` for the
  Hessian of `w` and on `t = H` for `L w`, bound the Hölder constant of `L w` on `H` by `C (K + N)`
  and the `L²` norm of `D²w` on `H` by `C N`, and `D²w = D²u` near `closedBall x₀ ρ`.

## Main declarations

In the `TauCeti.PDE` namespace:

* `exists_holderOnWith_iteratedFDeriv_two_of_support_subset_closedBall_of_halfSpace`: the estimate
  up to a flat boundary for a Hessian supported in a ball about a point of `closure H`, with
  coefficients Hölder only on the closed half-ball.
* `exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv_of_halfSpace`: the
  Schauder estimate on small half-balls.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2, Lemma 6.4 and the localization in the proof of Lemma 6.5.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped InnerProductSpace NNReal ENNReal ContDiff

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- A Hessian vanishing in the closed half-space off a closed ball is square integrable on the open
half-space, when the function is `C²` on an open set containing the closed half-space. -/
private theorem memLp_iteratedFDeriv_two_of_support_inter_subset_closedBall {ν x₀ : E} {c₀ R : ℝ}
    {U : Set E} {u : E → ℝ} (hU : IsOpen U) (hHU : {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U)
    (hu : ContDiffOn ℝ 2 u U)
    (hsupp : Function.support (iteratedFDeriv ℝ 2 u) ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ closedBall x₀ R) :
    MemLp (iteratedFDeriv ℝ 2 u) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) := by
  set K : Set E := closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  have hKc : IsClosed {x : E | c₀ ≤ ⟪x, ν⟫_ℝ} :=
    isClosed_le continuous_const (continuous_id.inner continuous_const)
  have hK : IsCompact K := (isCompact_closedBall x₀ R).inter_right hKc
  have hcont : ContinuousOn (iteratedFDeriv ℝ 2 u) K :=
    (ContinuousOn.continuousOn_iteratedFDeriv hu hU le_rfl).mono (inter_subset_right.trans hHU)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hind : MemLp (K.indicator (iteratedFDeriv ℝ 2 u)) 2 volume :=
    (memLp_indicator_iff_restrict hKm.nullMeasurableSet).2
      (hcont.memLp_restrict_of_subset_isCompact hK hKm subset_rfl 2)
  refine (hind.restrict _).ae_eq ?_
  refine (ae_restrict_iff' (measurableSet_lt measurable_const
    (continuous_id.inner continuous_const).measurable)).2 (ae_of_all _ fun x hx => ?_)
  by_cases hxK : x ∈ K
  · exact indicator_of_mem hxK _
  · rw [indicator_of_notMem hxK]
    by_contra h
    exact hxK ⟨hsupp ⟨Ne.symm h, (mem_ofPred_eq ▸ hx).le⟩, (mem_ofPred_eq ▸ hx).le⟩

/-- Precomposing coefficients that are `α`-Hölder with constant `L` on the closed half-ball
`closedBall x₀ R ∩ closure H`, with `x₀ ∈ closure H`, with the radial retraction onto
`closedBall x₀ R` gives coefficients that are `α`-Hölder on `H` with constant `2ᵅ L` and within
`L Rᵅ` of `a x₀` there: the retraction maps `H` into the closed half-ball. -/
private theorem holderOnWith_comp_centeredRadialRetraction_and_abs_sub_le
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {ν x₀ : E} {c₀ R : ℝ} {L α : ℝ≥0} (hR : 0 ≤ R)
    (hx₀ : c₀ ≤ ⟪x₀, ν⟫_ℝ)
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ})) :
    (∀ i j, HolderOnWith (L * 2 ^ (α : ℝ)) α
      (fun x => a (TauCeti.centeredRadialRetraction x₀ R x) i j) {x | c₀ < ⟪x, ν⟫_ℝ}) ∧
    ∀ x, c₀ < ⟪x, ν⟫_ℝ → ∀ i j,
      |a (TauCeti.centeredRadialRetraction x₀ R x) i j - a x₀ i j| ≤ L * R ^ (α : ℝ) := by
  have hq_mem {x : E} (hx : c₀ < ⟪x, ν⟫_ℝ) :
      TauCeti.centeredRadialRetraction x₀ R x ∈ closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} :=
    ⟨TauCeti.centeredRadialRetraction_mem_closedBall hR x,
      (convex_setOf_le_inner ν c₀).centeredRadialRetraction_mem hx₀ hx.le hR⟩
  refine ⟨fun i j => ?_, fun x hx i j => ?_⟩
  · simpa only [Function.comp_def, mul_one] using (hL i j).comp
      ((TauCeti.lipschitzWith_centeredRadialRetraction hR).holderWith.holderOnWith _)
      fun x hx => hq_mem hx
  · have hdist : dist (TauCeti.centeredRadialRetraction x₀ R x) x₀ ≤ R :=
      mem_closedBall.1 (hq_mem hx).1
    simpa only [Real.dist_eq] using ((hL i j).dist_le (hq_mem hx)
      ⟨mem_closedBall_self hR, hx₀⟩).trans (by gcongr)

/-- **Schauder estimate up to a flat boundary for a Hessian supported in a ball.** Let `0 < α < 1`.
There is `C > 0`, depending only on dimension and `α`, with the following property. Let
`H = {x | c₀ < ⟪x, ν⟫}`, `ν ≠ 0`, let `x₀ ∈ closure H`, let `a` be `α`-Hölder entrywise with
constant `L` on the closed half-ball `closedBall x₀ R ∩ closure H`, and suppose `a x₀` has
ellipticity bounds `λ, Λ`, with `λ > 0`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu` and
`κ = C (Λ / λ)^(1 + (n+1)/4 + α/2)`. If

`2 κ (n+1)² (L Rᵅ + 2ᵅ L rᵅ) ≤ λ`,

then every `u` that is `C²` on an open set containing `closure H`, vanishes on `∂H`, has `D²u`
`α`-Hölder on `closure H` and vanishing at the points of `closure H` off `closedBall x₀ R`,
satisfies

`[D²u]_{α; closure H} ≤ 2 κ ([L u]_{α; H} / λ + Q ‖D²u‖_{L²(H)})`, where
`Q = (n+1)² 2ᵅ L / λ |B_{r/2}|^(-1/2) + r^(-(n+1)/2-α)`.

The Hölder hypothesis on `D²u` is an a priori regularity assumption; its constant does not occur
in the conclusion. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_support_subset_closedBall_of_halfSpace
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E} {lam Lam : ℝ},
      0 < lam → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ {ν : E} {c₀ : ℝ}, ν ≠ 0 → c₀ ≤ ⟪x₀, ν⟫_ℝ →
      ∀ {L K : ℝ≥0} {R r : ℝ}, 0 < r →
      2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * r ^ (α : ℝ)) ≤ lam →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ})) →
      ∀ {U : Set E} {u : E → ℝ}, IsOpen U → {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U → ContDiffOn ℝ 2 u U →
      (∀ x, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
      (∃ J, HolderOnWith J α (iteratedFDeriv ℝ 2 u) {x | c₀ ≤ ⟪x, ν⟫_ℝ}) →
      Function.support (iteratedFDeriv ℝ 2 u) ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ closedBall x₀ R →
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
  refine ⟨C₀, hC₀, fun {a x₀ lam Lam} hlam hEll hEll' {ν c₀} hν hx₀ {L K R r} hr hsmall hL
    {U u} hU hHU hu hu0 hJ hsupp hf => ?_⟩
  set Hc : Set E := {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  -- If `R < 0` the closed ball is empty, so the Hessian vanishes on `closure H`.
  rcases lt_or_ge R 0 with hR | hR
  · have h0 (z : E) (hz : z ∈ Hc) : iteratedFDeriv ℝ 2 u z = 0 := by
      by_contra h
      simpa [closedBall_eq_empty.2 hR] using hsupp ⟨h, hz⟩
    intro x hx y hy
    simp [h0 x hx, h0 y hy]
  -- Retract the coefficients onto the closed half-ball.
  let q : E → E := TauCeti.centeredRadialRetraction x₀ R
  let a' : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun x => a (q x)
  obtain ⟨ha'_holder, ha'_close⟩ :=
    holderOnWith_comp_centeredRadialRetraction_and_abs_sub_le hR hx₀ hL
  let ε : ℝ≥0 := (L * R ^ (α : ℝ)).toNNReal
  have hε : (ε : ℝ) = L * R ^ (α : ℝ) :=
    Real.coe_toNNReal _ (mul_nonneg L.coe_nonneg (Real.rpow_nonneg hR _))
  -- Where the Hessian is nonzero the retraction is the identity, so `L u` is unchanged.
  have hf' : HolderOnWith K α (fun x => ∑ i, ∑ j, a' x i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ho := by
    refine hf.congr fun x hx =>
      (sum_smul_fderiv_fderiv_comp_centeredRadialRetraction_eq a fun h =>
        hsupp ⟨h, (mem_ofPred_eq ▸ hx).le⟩).symm
  have hsmall' :
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((ε : ℝ) + (L * 2 ^ (α : ℝ) : ℝ≥0) * r ^ (α : ℝ)) ≤ lam := by
    simpa only [hε, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat] using hsmall
  simpa only [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat] using
    hS (A := a x₀) (a := a') hlam hEll hEll' hν hr hsmall' (fun x hx i j => hε ▸ ha'_close x hx i j)
      ha'_holder hU hHU hu hu0 hJ
      (memLp_iteratedFDeriv_two_of_support_inter_subset_closedBall hU hHU hu hsupp) hf'

/-- A cutoff product `ζ u`, for a smooth cutoff `ζ` supported in `B_R` and a function `u` which is
`C²` on an open set containing the half-ball `B_R ∩ closure H`, is `C²` on an open set containing
`closure H`, and its Hessian vanishes off `closedBall x₀ R`. -/
private theorem exists_contDiffOn_cutoff_mul_of_halfSpace {ζ u : E → ℝ} {ν x₀ : E} {c₀ R : ℝ}
    {U : Set E} (hζ : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ ball x₀ R) (hU : IsOpen U)
    (hUs : ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U) (hu : ContDiffOn ℝ 2 u U) :
    (∃ W, IsOpen W ∧ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ W ∧ ContDiffOn ℝ 2 (ζ * u) W) ∧
      Function.support (iteratedFDeriv ℝ 2 (ζ * u)) ⊆ closedBall x₀ R := by
  refine ⟨⟨U ∪ (tsupport ζ)ᶜ, hU.union (isClosed_tsupport ζ).isOpen_compl, fun x hx => ?_,
    fun x hx => ?_⟩, (support_iteratedFDeriv_subset 2).trans
      (tsupport_mul_subset_left.trans (hζs.trans ball_subset_closedBall))⟩
  · by_cases hxs : x ∈ tsupport ζ
    · exact Or.inl (hUs ⟨hζs hxs, hx⟩)
    · exact Or.inr hxs
  -- On `U` both factors are `C²`; off the support of `ζ` the product vanishes near `x`.
  refine ContDiffAt.contDiffWithinAt ?_
  rcases hx with hx | hx
  · exact hζ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport ζ).isOpen_compl.mem_nhds hx] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]

/-- The data of a cutoff product `ζ u` on a half-ball, for a cutoff `ζ` supported in `B_R` and a
function `u` that is `C²` up to the flat boundary with bounds `N` on `u` and its first two
derivatives and a Hölder Hessian on `B_R ∩ closure H`: the Hessian of `ζ u` is Hölder on
`closure H`, the operator `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ` applied to `ζ u` is Hölder on `H` with constant
`Z K + N B₂`, and the `L²` norm of the Hessian on `H` is at most
`|closedBall 0 R|^{1/2} (n+1)² 4 Z N`. The constants `δ` and `B₂` are given by their
definitions. -/
private theorem cutoff_mul_data_of_halfSpace {ζ u : E → ℝ} {ν x₀ : E} {c₀ R : ℝ} {U : Set E}
    {α Z N K V L M δ B₂ : ℝ≥0} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hα1 : α ≤ 1)
    (hζ : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ ball x₀ R)
    (hZ0 : HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hU : IsOpen U) (hUs : ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hN0 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, |u x| ≤ N)
    (hN1 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N)
    (hV : HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}))
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}))
    (hM : ∀ x ∈ closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ∀ i j, |a x i j| ≤ M)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))
    (hδ : δ = (2 * R).toNNReal ^ ((1 : ℝ) - α))
    (hB₂ : B₂ = (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))) :
    (∃ J, HolderOnWith J α (iteratedFDeriv ℝ 2 (ζ * u)) {x | c₀ ≤ ⟪x, ν⟫_ℝ}) ∧
      HolderOnWith (Z * K + N * B₂) α (fun x => ∑ i, ∑ j, a x i j •
        fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
        {x | c₀ < ⟪x, ν⟫_ℝ} ∧
      (eLpNorm (iteratedFDeriv ℝ 2 (ζ * u)) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ})).toReal ≤
        (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) *
          (((n : ℝ) + 1) ^ 2 * (4 * Z)) * N := by
  subst hB₂ hδ
  have hconv := (convex_ball x₀ R).inter (convex_setOf_le_inner ν c₀)
  set Hc : Set E := {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  have hHo : Ho ⊆ Hc := fun x (hx : c₀ < ⟪x, ν⟫_ℝ) => hx.le
  have hsub : ball x₀ R ∩ Ho ⊆ ball x₀ R ∩ Hc := inter_subset_inter_right _ hHo
  have hsub' : ball x₀ R ∩ Ho ⊆ closedBall x₀ R ∩ Hc :=
    inter_subset_inter ball_subset_closedBall hHo
  obtain ⟨hHu, hHdu⟩ := hconv.holderOnWith_and_holderOnWith_fderiv_apply_of_norm_le
    (D := (2 * R).toNNReal) hα1 (fun _ hx _ hy => edist_le_two_mul_of_mem_ball hx.1 hy.1) hU hUs
    hu hN1 hN2
  have hdu (i : Fin (n + 1)) (x : E) (hx : x ∈ ball x₀ R ∩ Hc) :
      |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N := by
    simpa using ((fderiv ℝ u x).unit_le_opNorm (EuclideanSpace.single i 1) (by simp)).trans
      (hN1 x hx)
  have hd2u (i j : Fin (n + 1)) (x : E) (hx : x ∈ ball x₀ R ∩ Hc) :
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N := by
    simpa using (norm_fderiv_fderiv_apply_orthonormalBasis_le u (EuclideanSpace.basisFun _ ℝ) i j
      x).trans (hN2 x hx)
  have htU {t : Set E} (ht : t ⊆ Hc) : t ∩ tsupport ζ ⊆ U := fun x hx => hUs ⟨hζs hx.2, ht hx.1⟩
  have hWH := holderOnWith_fderiv_fderiv_cutoff_mul hU hζ.contDiffOn hζs (htU subset_rfl) hZ0 hZ1
    hZ2 hu hN0 hdu hd2u hHu (fun i => hHdu _ (by simp)) fun i j => by
      simpa [iteratedFDeriv_two_apply] using
        hV.apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j
  refine ⟨⟨_, .of_apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) fun i j => by
      simpa [iteratedFDeriv_two_apply] using (hWH i j).1⟩,
    (holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul hU hζ.contDiffOn hζs (htU hHo) hZ0 hZ1 hZ2 hu
      (fun x hx => hN0 x (hsub hx)) (fun i x hx => hdu i x (hsub hx))
      (fun i j x hx => hd2u i j x (hsub hx)) (hHu.mono hsub) (fun i => (hHdu _ (by simp)).mono hsub)
      (fun i j => (hL i j).mono hsub') (fun x hx => hM x (hsub' hx)) hK).mono_const
      (le_of_eq (by ring)), ?_⟩
  obtain ⟨⟨W, hWo, hHW, hw⟩, hsupp⟩ := exists_contDiffOn_cutoff_mul_of_halfSpace hζ hζs hU hUs hu
  have hHom : MeasurableSet Ho :=
    measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable
  exact (Measure.toReal_eLpNorm_restrict_iteratedFDeriv_two_le_of_support_subset_closedBall (p := 2)
    volume (EuclideanSpace.basisFun _ ℝ) hHom
    ((ContinuousOn.continuousOn_iteratedFDeriv hw hWo le_rfl).mono (hHo.trans hHW)) hsupp
    (B := 4 * Z * N) (by positivity) fun x hx i j => by
      simpa using (hWH i j).2 x (hHo hx)).trans_eq
    (by simp only [Fintype.card_fin, ENNReal.toReal_ofNat]; push_cast; ring)

/-- **The Schauder estimate on small half-balls.** Let `0 < α < 1`. There is `C₀ > 0`, depending
only on dimension and `α`, with the following property. Let `0 < λ`, `Λ`, `L`, `M` and `R` be
given, put `κ = C₀ (Λ / λ)^(1 + (n+1)/4 + α/2)`, and assume the scale condition

`2 κ (n+1)² (1 + 2ᵅ) L Rᵅ ≤ λ`.

Then for every `ρ < R` there is `C`, depending only on `n`, `α`, `λ`, `Λ`, `L`, `M`, `R` and `ρ`,
with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}`, `ν ≠ 0`, and `x₀ ∈ closure H`. Let `a`
be `α`-Hölder entrywise with constant `L` and bounded entrywise by `M` on the closed half-ball
`closedBall x₀ R ∩ closure H`, and suppose `a x₀` has ellipticity bounds `λ, Λ`. Put
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on an open set containing the half-ball `B_R ∩ closure H`,
vanishing on the flat boundary `B_R ∩ ∂H`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on
`B_R ∩ closure H` and with `D²u` `α`-Hölder there (with any constant). If `L u` is `α`-Hölder on
`B_R ∩ H` with constant `K`, then `D²u` is `α`-Hölder on `closedBall x₀ ρ ∩ closure H` with
constant `C (K + N)`.

The constant `C` does not depend on the centre `x₀`, on the half-space or on the coefficient field
`a` beyond the bounds `λ`, `Λ`, `L` and `M`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv_of_halfSpace
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {lam Lam : ℝ} {L M : ℝ≥0} {R : ℝ}, 0 < lam →
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((1 + 2 ^ (α : ℝ)) * L * R ^ (α : ℝ)) ≤ lam →
      ∀ {ρ : ℝ}, ρ < R → ∃ C : ℝ≥0,
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {ν x₀ : E} {c₀ : ℝ}, ν ≠ 0 →
      c₀ ≤ ⟪x₀, ν⟫_ℝ →
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ})) →
      (∀ x ∈ closedBall x₀ R ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}, ∀ i j, |a x i j| ≤ M) →
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
  · exact ⟨0, fun {a ν x₀ c₀} _ _ _ _ _ _ {U u N K V} _ _ _ _ _ _ _ _ _ => by
      rw [closedBall_eq_empty.2 (hρR.trans_le hR), empty_inter]
      exact holderOnWith_empty _ _ _⟩
  -- Cutoffs about every centre with one constant `Z`, and the constants of the estimate, which
  -- do not depend on `u`, `a`, `x₀` or the half-space.
  obtain ⟨Z, hZ⟩ := exists_forall_exists_cutoff
    (fun i : Fin (n + 1) => EuclideanSpace.single i (1 : ℝ)) hα1.le hρR
  set δ : ℝ≥0 := (2 * R).toNNReal ^ ((1 : ℝ) - α)
  set κ : ℝ := C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  set Q : ℝ := ((n : ℝ) + 1) ^ 2 * (L * 2 ^ (α : ℝ)) / lam *
      (volume (ball (0 : E) (R / 2)) ^ (-((2 : ℝ)⁻¹))).toReal + R ^ (-(((n : ℝ) + 1) / 2 + α))
  set B₂ : ℝ≥0 := (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))
  set A₃ : ℝ := (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) * (((n : ℝ) + 1) ^ 2 * (4 * Z))
  refine ⟨(2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal,
    fun {a ν x₀ c₀} hν hx₀ hEll hEll' hL hM {U u N K V} hU hUs hu hu0 hN0 hN1 hN2 hV hK => ?_⟩
  obtain ⟨ζ, hζ, hζ1, hζs, hZ0, hZ1, hZ2⟩ := hZ x₀
  have hζ2 : ContDiff ℝ 2 ζ := hζ.of_le (by norm_cast)
  obtain ⟨hJ, hLw, hL2⟩ := cutoff_mul_data_of_halfSpace hα1.le hζ2 hζs hZ0 hZ1 hZ2 hU hUs hu hN0
    hN1 hN2 hV hL hM hK (δ := δ) (B₂ := B₂) rfl rfl
  -- The cutoff product `ζ u` vanishes on `∂H` and is `C²` on an open set containing
  -- `closure H`; its Hessian vanishes off `closedBall x₀ R`.
  have hw0 (x : E) (hx : ⟪x, ν⟫_ℝ = c₀) : (ζ * u) x = 0 := by
    by_cases hxb : x ∈ ball x₀ R
    · simp [hu0 x hxb hx]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hxb (hζs h)]
  obtain ⟨⟨W, hWo, hHW, hw⟩, hsupp⟩ := exists_contDiffOn_cutoff_mul_of_halfSpace hζ2 hζs hU hUs hu
  have key := hCS hlam hEll hEll' hν hx₀ (K := Z * K + N * B₂) hR
    (by convert hsmall using 2; ring) hL hWo hHW hw hw0 hJ (fun x hx => hsupp hx.1) hLw
  have hlamLam : lam ≤ Lam := by
    simpa using (hEll (EuclideanSpace.single 0 1)).trans (hEll' (EuclideanSpace.single 0 1))
  have hbound := two_mul_mul_add_div_add_mul_le (Z := Z) (B := B₂) (K := K) (N := N)
    (mul_nonneg hC₀.le (Real.rpow_nonneg (div_nonneg (hlam.le.trans hlamLam) hlam.le) _) : 0 ≤ κ)
    hlam.le (by positivity : 0 ≤ Q) (by positivity : 0 ≤ A₃) hL2
  -- On a neighbourhood of `closedBall x₀ ρ` the cutoff is one, so `D²(ζ u) = D²u` there.
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
