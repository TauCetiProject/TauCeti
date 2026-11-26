/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Cover
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The orbit-torus operator on the skew covers of an orbit torus

Let `γ` be a closed orbit of period `d` of the suspension flow of a surface diffeomorphism and
`C = S¹ × γ` its orbit torus in `S¹ × Y_φ`, with circle factor of length `ℓ₀`. In a unitary
trivialization of the normal bundle, the normal operator of `C` is `D = ∂s + J₀ (∂t - S)` for a
loop `S` of period `d`, infinitesimally symplectic for `Im ⟪·, ·⟫`, with return map `P = Ψ(d)` of
`ζ' = S ζ`. Taubes's weighted count needs this operator on every finite cover of `C`. A finite
cover is `ℝ² / Λ` for a sublattice `Λ` of `ℓ₀ ℤ × d ℤ`, and `Λ` has a basis `(ℓ, 0)`, `(σ, T)`
with `ℓ = k ℓ₀`, `σ = a ℓ₀` and `T = n d` (its Hermite normal form). The covers along the two
factors, `σ = 0`, are treated in `TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Cover`.
This file treats all of them, the *skew* covers `σ ≠ 0` included, and proves the Fredholm
alternative there: the operator on the cover is invertible exactly when `det (1 - P ^ n) ≠ 0`
(`TauCeti.isInvertible_skewTorusOperator_coverPullback_iff_det_ne_zero`). As on the covers along
the factors, only the number `n` of turns along `γ` matters, not the shear `σ`.

**The spaces.** A map on the cover is a map `u(s, t)` with `u (s + ℓ, t) = u (s, t)` and
`u (s + σ, t + T) = u (s, t)`. Its `s`-independent mode `a₀(t)`, the average over `s`, is a loop
of period `T`. Its other modes `cos (ωₖ s) aₖ(t) + sin (ωₖ s) bₖ(t)`, `ωₖ = 2(k + 1)π/ℓ`, satisfy
`(aₖ, bₖ)(t + T) = R(ωₖ σ) (aₖ, bₖ)(t)` for the rotation
`R(φ) (a, b) = (cos φ a - sin φ b, sin φ a + cos φ b)` of the pair, since translating by `-σ` in
`s` rotates the mode. If `q σ ∈ ℓ ℤ` for a positive integer `q`, as for every cover of `C` (take
`q = k`), these loops have period `q T`, and they are the modes of
`TauCeti.torusModeSobolev F ω` for loops of period `q T` that satisfy (with
`TauCeti.CircleSobolev.rotate θ a = a(· + θ)`)

`rotate T aₖ = cos (ωₖ σ) aₖ - sin (ωₖ σ) bₖ`,  `rotate T bₖ = sin (ωₖ σ) aₖ + cos (ωₖ σ) bₖ`.

These maps form the closed subspace `TauCeti.skewTorusModeSobolev F ℓ σ θ` of the Sobolev space
`H¹`, for the rotation `θ = T` of the circle of length `q T`, and the mode sequences in `H⁰(F)²`
with the same property form `TauCeti.skewTorusModeL2 F ℓ σ θ`. For `σ = 0` and `q = 1` the
condition is empty, and these are the spaces of `TauCeti.periodicTorusOperator`. If `q σ ∉ ℓ ℤ`,
the modes `k` with `q ωₖ σ ∉ 2π ℤ` of an invariant map of period `q T` vanish, so these spaces
then hold only part of the maps on the cover; the results of this file hold for every `q`.

**The operator.** Read with period `q T`, the loop `S` is invariant under the rotation by `T`, so
`A ζ = J₀ (ζ' - S ζ)` commutes with it (`TauCeti.CircleSobolev.loopOperator_rotate_of_invariant`),
and the mode operator `(aₖ, bₖ) ↦ (A aₖ + ωₖ bₖ, A bₖ - ωₖ aₖ)` commutes with the rotations of the
pair. So `D` maps the invariant modes to invariant modes, and restricts to
`TauCeti.skewTorusModeOperator`. On the cover, `D` is `A` on the `s`-independent mode, a loop of
period `T`, and this restriction on the others (`TauCeti.skewTorusOperator`).

**Invertibility on the other modes.** On all the modes of frequencies `ωₖ`, `D` is invertible
(`TauCeti.isInvertible_torusModeOperator_periodic`). It commutes with the rotation `x ↦ θ x` by `T`
of every mode (`TauCeti.torusModeOperator_rotateMode`) and with the translation `x ↦ σ x` by `-σ`
in `s`, and the invariant maps are the solutions of `θ x = σ x`. If `D x` is invariant, then
`D (θ x) = θ (D x) = σ (D x) = D (σ x)`, so `θ x = σ x` by injectivity: the inverse of `D` maps
invariant targets to invariant maps. Hence the restriction is invertible
(`TauCeti.isInvertible_skewTorusModeOperator`).

**The comparison.** The operator on the cover is `(J₀ L_S) ⊕ D'` for the invertible restriction
`D'`, so the comparison of `TauCeti.kerProdMapLoopOperatorEquiv` and the lemmas beside it applies:
the inclusions of the `s`-independent mode identify the kernel and the cokernel of the operator on
the cover with those of the loop operator `L_S ζ = ζ' - S ζ` of period `T`
(`TauCeti.kerSkewTorusOperatorEquiv`, `TauCeti.quotientRangeSkewTorusOperatorEquiv`), so its
determinant line with that of `1 - Ψ(T)` (`TauCeti.detLineSkewTorusOperatorEquiv`). It is
Fredholm of index zero, invertible exactly when `det (1 - Ψ(T)) ≠ 0`
(`TauCeti.isInvertible_skewTorusOperator_iff_det_ne_zero`), and then the orientation of its
determinant line induced by `1 - Ψ(T)` and the one given by bijectivity differ by the sign of
`det (1 - Ψ(T))` (`TauCeti.sign_detLineEndEquiv_detLineSkewTorusOperatorEquiv`).
For the orbit traversed `n` times, `T = n d` and `Ψ(T) = P ^ n`
(`TauCeti.dysonSeriesLeft_coverPullback`).

**The absolute determinant sign.** Since the operator on a skew cover is `(J₀ L_S) ⊕ D'` with `D'`
invertible along every path of infinitesimally symplectic loops, transporting the complex
orientation of a complex-linear reference operator, such as `∂s + J₀ ∂t`, along such a path follows
the return maps (`TauCeti.detLineOrientationTransport_rayOfNeZero_prodMap_loopOperator`). At a
bijective endpoint the transported orientation therefore reads with the sign of `det (1 - Ψ(T))`
against the orientation given by bijectivity
(`TauCeti.sign_detLineEquivOfBijective_prodMap_loopOperator_eq_sign_det`,
`TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det`). On the finite covers of an
orbit torus this is the sign `sgn det (1 - P ^ n)` of the untwisted operator on the cover, whatever
the shear (`TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_coverPullback_eq_sign_det`).
For the operators twisted by the sign character of the cover that is `-1` on `(σ, T)`, respectively
`(σ, n T)`, the signs are `sgn det (1 + Ψ(T))` and `sgn det (1 + P ^ n)`
(`TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_eq_sign_det`), the
signs found on the covers along the orbit in
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Cover`.

## Main definitions

* `TauCeti.skewTorusModeSobolev F ℓ σ θ`, `TauCeti.skewTorusModeL2 F ℓ σ θ`: the maps periodic of
  period `ℓ` in `s` with no `s`-independent part that are invariant under the translation by
  `(σ, θ)`, in `H¹` and in `L²`.
* `TauCeti.skewTorusModeOperator`: the restriction of `TauCeti.torusModeOperator` to them.
* `TauCeti.skewTorusOperator T q ℓ σ S`: the operator `∂s + J₀ (∂t - S)` on the cover with lattice
  spanned by `(ℓ, 0)` and `(σ, T)`, when `q σ ∈ ℓ ℤ`.

## Main results

* `TauCeti.isInvertible_skewTorusModeOperator`: invertibility on the modes of nonzero frequency.
* `TauCeti.kerSkewTorusOperatorEquiv`, `TauCeti.quotientRangeSkewTorusOperatorEquiv`,
  `TauCeti.detLineSkewTorusOperatorEquiv`: the kernel, cokernel and determinant line are those of
  `L_S` and of `1 - Ψ(T)`.
* `TauCeti.isFredholm_skewTorusOperator`, `TauCeti.index_skewTorusOperator`: Fredholm of index
  zero.
* `TauCeti.isInvertible_skewTorusOperator_iff_det_ne_zero`,
  `TauCeti.isInvertible_skewTorusOperator_coverPullback_iff_det_ne_zero`: the Fredholm
  alternative, and on the covers of an orbit torus in terms of `P ^ n`.
* `TauCeti.sign_detLineEndEquiv_detLineSkewTorusOperatorEquiv`: the comparison of the two
  orientations of a bijective operator by the sign of `det (1 - Ψ(T))`.
* `TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det`,
  `TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_coverPullback_eq_sign_det`: the
  orientation transported from the complex orientation has sign `sgn det (1 - Ψ(T))`, on the
  covers of an orbit torus `sgn det (1 - P ^ n)`.
* `TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_eq_sign_det`,
  `sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_coverPullback_eq_sign_det`:
  for the operators twisted by the sign character, the signs `sgn det (1 + Ψ(T))` and
  `sgn det (1 + P ^ n)`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893 (the normal operators of tori on their finite
  unbranched covers).
* D. Salamon, *Lectures on Floer homology*, in Symplectic Geometry and Topology,
  IAS/Park City Math. Ser. 7 (1999), Lecture 2 (the operator `J₀ ∂t + S` and the return map).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (orientations of determinant lines by
  transport from complex-linear operators).
-/

public section

noncomputable section

open Complex
open LinearMap (ker range)
open Set (uIcc left_mem_uIcc right_mem_uIcc)
open scoped Real lp

namespace TauCeti

open CircleSobolev

/-- The product of the two mode spaces carrying `TauCeti.torusModeSobolev`. -/
local notation "𝕏[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 1 F × CircleSobolev 1 F)) ×
  ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

/-- The `L²` space of mode sequences, the target of `TauCeti.torusModeOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

/-! ### Translations of the modes -/

section Translation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {T : ℝ}

/-- The quarter turn `(a, b) ↦ (-b, a)` of a mode. -/
private def quarterTurn (s : ℝ) :
    WithLp 2 (CircleSobolev s F × CircleSobolev s F) →L[ℂ]
      WithLp 2 (CircleSobolev s F × CircleSobolev s F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap ∘L
    ((-WithLp.sndL 2 ℂ (CircleSobolev s F) (CircleSobolev s F)).prod
      (WithLp.fstL 2 ℂ (CircleSobolev s F) (CircleSobolev s F)))

/-- The translation by `-σ` in `s` of a mode of frequency `ω`: if `(a, b)` is the mode
`cos (ω s) a + sin (ω s) b` of `u`, the corresponding mode of `u (s - σ, t)` is
`(cos (ωσ) a - sin (ωσ) b, sin (ωσ) a + cos (ωσ) b)`. -/
private def shiftPair (s ω σ : ℝ) :
    WithLp 2 (CircleSobolev s F × CircleSobolev s F) →L[ℂ]
      WithLp 2 (CircleSobolev s F × CircleSobolev s F) :=
  Real.cos (ω * σ) • ContinuousLinearMap.id ℂ _ + Real.sin (ω * σ) • quarterTurn s

@[simp]
private theorem shiftPair_apply (s ω σ : ℝ)
    (y : WithLp 2 (CircleSobolev s F × CircleSobolev s F)) :
    shiftPair s ω σ y = WithLp.toLp 2 (Real.cos (ω * σ) • y.fst - Real.sin (ω * σ) • y.snd,
      Real.sin (ω * σ) • y.fst + Real.cos (ω * σ) • y.snd) := by
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;>
    simp [shiftPair, quarterTurn, sub_eq_add_neg, add_comm]

private theorem norm_shiftPair_le (s ω σ : ℝ) :
    ‖shiftPair (F := F) s ω σ‖ ≤ 1 + ‖quarterTurn (F := F) s‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs]
  · exact (mul_le_mul (Real.abs_cos_le_one _) ContinuousLinearMap.norm_id_le (norm_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  · exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

/-- The translation by `-σ` in `s` of every mode of a sequence of modes with the frequencies
`ω`. -/
private def shiftSeq (s : ℝ) (ω : ℕ → ℝ) (σ : ℝ) :
    ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F)) →L[ℂ]
      ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F)) :=
  lp.mapCLM 2 (fun k ↦ shiftPair s (ω k) σ) (by positivity) fun k ↦ norm_shiftPair_le s (ω k) σ

private theorem shiftSeq_apply_apply (s : ℝ) (ω : ℕ → ℝ) (σ : ℝ)
    (y : ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F))) (k : ℕ) :
    shiftSeq s ω σ y k = shiftPair s (ω k) σ (y k) := by
  simp [shiftSeq]

private theorem shiftPair_smul_withLpProdMap_inclusion (ω σ c : ℝ)
    (y : WithLp 2 (CircleSobolev 1 F × CircleSobolev 1 F)) :
    shiftPair 0 ω σ (c • (inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one) y) =
      c • (inclusion zero_le_one).withLpProdMap 2 (inclusion zero_le_one)
        (shiftPair 1 ω σ y) := by
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;>
    simp [← Complex.coe_smul, smul_sub, smul_add, smul_smul]

/-- A mode is invariant under the translation by `(σ, θ)` exactly when rotating it by `θ` agrees
with translating it by `-σ` in `s`. -/
private theorem rotatePair_eq_shiftPair_iff (s ω σ : ℝ) (θ : AddCircle T)
    (y : WithLp 2 (CircleSobolev s F × CircleSobolev s F)) :
    rotatePair s θ y = shiftPair s ω σ y ↔
      rotate θ y.fst = Real.cos (ω * σ) • y.fst - Real.sin (ω * σ) • y.snd ∧
        rotate θ y.snd = Real.sin (ω * σ) • y.fst + Real.cos (ω * σ) • y.snd := by
  rw [← (WithLp.ofLp_injective 2).eq_iff, rotatePair_apply, shiftPair_apply]
  simp [Prod.ext_iff]

/-- The translation by `-σ` in `s` of every mode of an element of
`TauCeti.torusModeSobolev F ω`. -/
private def shiftMode {ω : ℕ → ℝ} (σ : ℝ) (x : torusModeSobolev F ω) : torusModeSobolev F ω :=
  ⟨(shiftSeq 1 ω σ (x : 𝕏[F]).1, shiftSeq 0 ω σ (x : 𝕏[F]).2), mem_torusModeSobolev_iff.2 fun k ↦ by
    rw [shiftSeq_apply_apply, shiftSeq_apply_apply, mem_torusModeSobolev_iff.1 x.property k,
      shiftPair_smul_withLpProdMap_inclusion]⟩

private theorem shiftMode_fst_apply {ω : ℕ → ℝ} (σ : ℝ) (x : torusModeSobolev F ω) (k : ℕ) :
    (shiftMode σ x : 𝕏[F]).1 k = shiftPair 1 (ω k) σ ((x : 𝕏[F]).1 k) :=
  shiftSeq_apply_apply _ _ _ _ _

private theorem shiftMode_snd_apply {ω : ℕ → ℝ} (σ : ℝ) (x : torusModeSobolev F ω) (k : ℕ) :
    (shiftMode σ x : 𝕏[F]).2 k = shiftPair 0 (ω k) σ ((x : 𝕏[F]).2 k) :=
  shiftSeq_apply_apply _ _ _ _ _

/-- An element of `TauCeti.torusModeSobolev F ω` is invariant under the translation by `(σ, θ)`,
its rotation by `θ` agreeing with its translation by `-σ` in `s`, as soon as the modes of its
first sequence are: the second sequence is determined by the first. -/
private theorem rotateMode_eq_shiftMode {ω : ℕ → ℝ} {σ : ℝ} {θ : AddCircle T}
    {x : torusModeSobolev F ω}
    (hx : ∀ k, rotatePair 1 θ ((x : 𝕏[F]).1 k) = shiftPair 1 (ω k) σ ((x : 𝕏[F]).1 k)) :
    rotateMode θ x = shiftMode σ x := by
  refine Subtype.ext (Prod.ext (lp.ext (funext fun k ↦ ?_)) (lp.ext (funext fun k ↦ ?_)))
  · rw [rotateMode_fst_apply, shiftMode_fst_apply, hx k]
  · rw [rotateMode_snd_apply, shiftMode_snd_apply, mem_torusModeSobolev_iff.1 x.property k,
      rotatePair_smul_withLpProdMap_inclusion, shiftPair_smul_withLpProdMap_inclusion, hx k]

end Translation

/-! ### The invariant maps -/

section Space

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {T : ℝ}

variable (F) in
/-- The mode sequences in `H^s(F)²`, for the frequencies `ωₖ = 2(k + 1)π/ℓ`, whose modes are
invariant under the translation by `(σ, θ)`: rotating each by `θ` agrees with translating it by
`-σ` in `s`. -/
private def invariantModes (s ℓ σ : ℝ) (θ : AddCircle T) :
    Submodule ℂ ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F)) :=
  ker ((lp.ampliation ℕ 2 (rotatePair s θ) - shiftSeq s (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) σ :
    ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F)) →L[ℂ]
      ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F))) :
    ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F)) →ₗ[ℂ]
      ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F)))

private theorem mem_invariantModes_iff {s ℓ σ : ℝ} {θ : AddCircle T}
    {y : ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F))} :
    y ∈ invariantModes F s ℓ σ θ ↔
      ∀ k : ℕ, rotatePair s θ (y k) = shiftPair s (2 * (k + 1) * π / ℓ) σ (y k) := by
  simp only [invariantModes, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_eq_zero,
    FunLike.coe_sub, Pi.sub_apply, lp.ext_iff, funext_iff, lp.ampliation_apply_apply,
    shiftSeq_apply_apply]

private theorem isClosed_invariantModes (s ℓ σ : ℝ) (θ : AddCircle T) :
    IsClosed (invariantModes F s ℓ σ θ :
      Set ℓ²(ℕ, WithLp 2 (CircleSobolev s F × CircleSobolev s F))) := by
  rw [invariantModes]
  exact ContinuousLinearMap.isClosed_ker _

variable (F) in
/-- The Sobolev space `H¹` of maps `u(s, t)` periodic of period `ℓ` in `s`, with no
`s`-independent part, invariant under the translation `(s, t) ↦ (s + σ, t + θ)`, in modes: the
elements of `TauCeti.torusModeSobolev F ω`, `ωₖ = 2(k + 1)π/ℓ`, whose modes `(aₖ, bₖ)` satisfy
`rotate θ aₖ = cos (ωₖ σ) aₖ - sin (ωₖ σ) bₖ` and `rotate θ bₖ = sin (ωₖ σ) aₖ + cos (ωₖ σ) bₖ`
(`TauCeti.mem_skewTorusModeSobolev_iff`): the translation by `θ` in `t` of the mode
`cos (ωₖ s) aₖ + sin (ωₖ s) bₖ` is its translation by `-σ` in `s`. It is a subspace of the ambient
space of pairs of mode sequences, contained in `TauCeti.torusModeSobolev F ω`
(`TauCeti.skewTorusModeSobolev_le_torusModeSobolev`). -/
def skewTorusModeSobolev (ℓ σ : ℝ) (θ : AddCircle T) : Submodule ℂ 𝕏[F] :=
  torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) ⊓
    (invariantModes F 1 ℓ σ θ).comap (LinearMap.fst ℂ _ _)

private theorem mem_skewTorusModeSobolev_iff_rotatePair {ℓ σ : ℝ} {θ : AddCircle T} {x : 𝕏[F]} :
    x ∈ skewTorusModeSobolev F ℓ σ θ ↔
      x ∈ torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) ∧
        ∀ k : ℕ, rotatePair 1 θ (x.1 k) = shiftPair 1 (2 * (k + 1) * π / ℓ) σ (x.1 k) := by
  rw [skewTorusModeSobolev, Submodule.mem_inf, Submodule.mem_comap, LinearMap.fst_apply,
    mem_invariantModes_iff]

theorem mem_skewTorusModeSobolev_iff {ℓ σ : ℝ} {θ : AddCircle T} {x : 𝕏[F]} :
    x ∈ skewTorusModeSobolev F ℓ σ θ ↔
      x ∈ torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) ∧ ∀ k : ℕ,
        rotate θ (x.1 k).fst = Real.cos (2 * (k + 1) * π / ℓ * σ) • (x.1 k).fst -
            Real.sin (2 * (k + 1) * π / ℓ * σ) • (x.1 k).snd ∧
          rotate θ (x.1 k).snd = Real.sin (2 * (k + 1) * π / ℓ * σ) • (x.1 k).fst +
            Real.cos (2 * (k + 1) * π / ℓ * σ) • (x.1 k).snd := by
  simp only [mem_skewTorusModeSobolev_iff_rotatePair, rotatePair_eq_shiftPair_iff]

theorem skewTorusModeSobolev_le_torusModeSobolev (ℓ σ : ℝ) (θ : AddCircle T) :
    skewTorusModeSobolev F ℓ σ θ ≤ torusModeSobolev F fun k : ℕ ↦ 2 * (k + 1) * π / ℓ :=
  fun _ hx ↦ (mem_skewTorusModeSobolev_iff_rotatePair.1 hx).1

/-- `TauCeti.skewTorusModeSobolev` is closed: it is the intersection of the closed subspace
`TauCeti.torusModeSobolev F ω` with the preimage of a kernel of a continuous map. -/
theorem isClosed_skewTorusModeSobolev (ℓ σ : ℝ) (θ : AddCircle T) :
    IsClosed (skewTorusModeSobolev F ℓ σ θ : Set 𝕏[F]) := by
  rw [skewTorusModeSobolev, Submodule.coe_inf, Submodule.comap_coe, LinearMap.coe_fst]
  exact (isClosed_torusModeSobolev _).inter
    ((isClosed_invariantModes 1 ℓ σ θ).preimage continuous_fst)

/-- The Sobolev space `H¹` of maps invariant under a translation is complete. -/
instance [CompleteSpace F] (ℓ σ : ℝ) (θ : AddCircle T) :
    CompleteSpace (skewTorusModeSobolev F ℓ σ θ) :=
  (isClosed_skewTorusModeSobolev ℓ σ θ).completeSpace_coe

variable (F) in
/-- The `L²` space of maps periodic of period `ℓ` in `s`, with no `s`-independent part, invariant
under the translation `(s, t) ↦ (s + σ, t + θ)`, in modes: the mode sequences in `H⁰(F)²` whose
modes `(aₖ, bₖ)` satisfy `rotate θ aₖ = cos (ωₖ σ) aₖ - sin (ωₖ σ) bₖ` and
`rotate θ bₖ = sin (ωₖ σ) aₖ + cos (ωₖ σ) bₖ`, `ωₖ = 2(k + 1)π/ℓ`
(`TauCeti.mem_skewTorusModeL2_iff`). It is the target of `TauCeti.skewTorusModeOperator`. -/
def skewTorusModeL2 (ℓ σ : ℝ) (θ : AddCircle T) : Submodule ℂ 𝕐[F] :=
  invariantModes F 0 ℓ σ θ

private theorem mem_skewTorusModeL2_iff_rotatePair {ℓ σ : ℝ} {θ : AddCircle T} {y : 𝕐[F]} :
    y ∈ skewTorusModeL2 F ℓ σ θ ↔
      ∀ k : ℕ, rotatePair 0 θ (y k) = shiftPair 0 (2 * (k + 1) * π / ℓ) σ (y k) := by
  rw [skewTorusModeL2, mem_invariantModes_iff]

theorem mem_skewTorusModeL2_iff {ℓ σ : ℝ} {θ : AddCircle T} {y : 𝕐[F]} :
    y ∈ skewTorusModeL2 F ℓ σ θ ↔ ∀ k : ℕ,
      rotate θ (y k).fst = Real.cos (2 * (k + 1) * π / ℓ * σ) • (y k).fst -
          Real.sin (2 * (k + 1) * π / ℓ * σ) • (y k).snd ∧
        rotate θ (y k).snd = Real.sin (2 * (k + 1) * π / ℓ * σ) • (y k).fst +
          Real.cos (2 * (k + 1) * π / ℓ * σ) • (y k).snd := by
  simp only [mem_skewTorusModeL2_iff_rotatePair, rotatePair_eq_shiftPair_iff]

/-- `TauCeti.skewTorusModeL2` is closed, as the kernel of a continuous map. -/
theorem isClosed_skewTorusModeL2 (ℓ σ : ℝ) (θ : AddCircle T) :
    IsClosed (skewTorusModeL2 F ℓ σ θ : Set 𝕐[F]) :=
  isClosed_invariantModes 0 ℓ σ θ

/-- The `L²` space of maps invariant under a translation is complete. -/
instance [CompleteSpace F] (ℓ σ : ℝ) (θ : AddCircle T) : CompleteSpace (skewTorusModeL2 F ℓ σ θ) :=
  (isClosed_skewTorusModeL2 ℓ σ θ).completeSpace_coe

end Space

/-! ### The orbit-torus operator on the invariant maps -/

section Operator

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceSkewCover : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- The orbit-torus operator commutes with the translation by `-σ` in `s` of every mode. -/
private theorem torusModeOperator_shiftMode {ω : ℕ → ℝ} (σ : ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (x : torusModeSobolev F ω) (k : ℕ) :
    torusModeOperator T ω S (shiftMode σ x) k =
      shiftPair 0 (ω k) σ (torusModeOperator T ω S x k) := by
  rw [torusModeOperator_apply_apply_eq, torusModeOperator_apply_apply_eq, shiftMode_fst_apply]
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;> simp [shiftPair_apply] <;>
    simp only [← Complex.coe_smul] <;> module

/-- For a loop `S` invariant under the rotation by `θ`, the orbit-torus operator `∂s + A` maps maps
invariant under the translation by `(σ, θ)` to targets invariant under it. -/
theorem torusModeOperator_mem_skewTorusModeL2 {ℓ σ : ℝ} {θ : AddCircle T}
    {S : C(AddCircle T, F →L[ℝ] F)} (hS : ∀ t, S (t + θ) = S t)
    {x : torusModeSobolev F fun k : ℕ ↦ 2 * (k + 1) * π / ℓ}
    (hx : (x : 𝕏[F]) ∈ skewTorusModeSobolev F ℓ σ θ) :
    torusModeOperator T (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) S x ∈ skewTorusModeL2 F ℓ σ θ :=
  mem_skewTorusModeL2_iff_rotatePair.2 fun k ↦ by
    have h := rotateMode_eq_shiftMode (σ := σ) (θ := θ) (x := x)
      (mem_skewTorusModeSobolev_iff_rotatePair.1 hx).2
    rw [← torusModeOperator_rotateMode T hS, h, torusModeOperator_shiftMode]

/-- The orbit-torus operator `∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, on maps periodic of period `ℓ` in `s`
with no `s`-independent part, invariant under the translation by `(σ, θ)`, for a loop `S` invariant
under the rotation by `θ`: the restriction of `TauCeti.torusModeOperator T ω S`,
`ωₖ = 2(k + 1)π/ℓ`, to `TauCeti.skewTorusModeSobolev F ℓ σ θ`, with values in
`TauCeti.skewTorusModeL2 F ℓ σ θ` (`TauCeti.restrictTorusModeOperator`). -/
def skewTorusModeOperator (ℓ σ : ℝ) (θ : AddCircle T) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t, S (t + θ) = S t) :
    skewTorusModeSobolev F ℓ σ θ →L[ℝ] skewTorusModeL2 F ℓ σ θ :=
  restrictTorusModeOperator T (skewTorusModeSobolev_le_torusModeSobolev ℓ σ θ) _ S fun x ↦
    torusModeOperator_mem_skewTorusModeL2 T hS x.property

@[simp]
theorem coe_skewTorusModeOperator_apply (ℓ σ : ℝ) (θ : AddCircle T)
    (S : C(AddCircle T, F →L[ℝ] F)) (hS : ∀ t, S (t + θ) = S t)
    (x : skewTorusModeSobolev F ℓ σ θ) :
    (skewTorusModeOperator T ℓ σ θ S hS x : 𝕐[F]) =
      torusModeOperator T (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) S
        (Submodule.inclusion (skewTorusModeSobolev_le_torusModeSobolev ℓ σ θ) x) :=
  coe_restrictTorusModeOperator_apply _ _ _ _ _ x

/-- **Complex linearity.** If the loop operator `L_S` commutes with multiplication by complex
scalars, as for a constant complex scalar loop, so does the orbit-torus operator on maps invariant
under a translation, the complex structure acting by `J₀`. -/
theorem skewTorusModeOperator_apply_smul (ℓ σ : ℝ) (θ : AddCircle T)
    {S : C(AddCircle T, F →L[ℝ] F)} (hS : ∀ t, S (t + θ) = S t)
    (hS' : ∀ (c : ℂ) (a : CircleSobolev 1 F), loopOperator T S (c • a) = c • loopOperator T S a)
    (c : ℂ) (x : skewTorusModeSobolev F ℓ σ θ) :
    skewTorusModeOperator T ℓ σ θ S hS (c • x) = c • skewTorusModeOperator T ℓ σ θ S hS x :=
  Subtype.ext <| by
    rw [Submodule.coe_smul, coe_skewTorusModeOperator_apply, coe_skewTorusModeOperator_apply,
      map_smul, torusModeOperator_apply_smul T _ hS']

/-- **Continuous dependence on the loop.** The orbit-torus operator on maps invariant under the
translation by `(σ, θ)` depends continuously, in operator norm, on the loop `S`, with its uniform
norm, among the loops invariant under the rotation by `θ`. -/
theorem continuous_skewTorusModeOperator (ℓ σ : ℝ) (θ : AddCircle T) :
    Continuous fun S : {S : C(AddCircle T, F →L[ℝ] F) // ∀ t, S (t + θ) = S t} ↦
      skewTorusModeOperator T ℓ σ θ S.val S.property :=
  continuous_restrictTorusModeOperator T _ _ fun _ hS x ↦
    torusModeOperator_mem_skewTorusModeL2 T hS x.property

variable (q : ℕ) [NeZero q]

/-- **The orbit-torus operator on a skew cover.** The operator `∂s + J₀ (∂t - S)` for a loop `S` of
period `T`, on maps `u(s, t)` with the `s`-independent mode a loop of period `T` and the other
modes loops of period `q T` invariant under the translation by `(σ, T)`. A map is a pair `(a₀, x)`
of its `s`-independent mode `a₀ ∈ H¹(F)` and its other modes `x` (`TauCeti.skewTorusModeSobolev`);
the operator is `A = J₀ L_S` on the first and `TauCeti.skewTorusModeOperator` for the loop `S` read
with period `q T` (`AddCircle.coverPullback`) on the second. When `q σ ∈ ℓ ℤ`, as for every finite
cover of an orbit torus (take `q = k` for `ℓ = k ℓ₀`), these are all the maps periodic under the
lattice spanned by `(ℓ, 0)` and `(σ, T)`, and this is the operator on that cover. For other `q`
the modes `k` with `q ωₖ σ ∉ 2π ℤ` vanish, and this models the cover operator only partially;
the results below hold for every `q`. The covers of the orbit torus along its two factors are the
case `σ = 0`. -/
def skewTorusOperator (ℓ σ : ℝ) (S : C(AddCircle T, F →L[ℝ] F)) :
    CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T)) →L[ℝ]
      CircleSobolev 0 F × skewTorusModeL2 F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T)) :=
  (I • loopOperator T S).prodMap (skewTorusModeOperator ((q : ℝ) * T) ℓ σ _
    (AddCircle.coverPullback q S) (AddCircle.coverPullback_add_coe_period q S))

@[simp]
theorem skewTorusOperator_apply (ℓ σ : ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (x : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))) :
    skewTorusOperator T q ℓ σ S x = (I • loopOperator T S x.1,
      skewTorusModeOperator ((q : ℝ) * T) ℓ σ _ (AddCircle.coverPullback q S)
        (AddCircle.coverPullback_add_coe_period q S) x.2) :=
  (rfl)

/-- `TauCeti.skewTorusOperator` is `(J₀ L_S) ⊕ B` for the operator `B` on the modes of nonzero
frequency. -/
theorem skewTorusOperator_eq_prodMap (ℓ σ : ℝ) (S : C(AddCircle T, F →L[ℝ] F)) :
    skewTorusOperator T q ℓ σ S = (I • loopOperator T S).prodMap
      (skewTorusModeOperator ((q : ℝ) * T) ℓ σ _ (AddCircle.coverPullback q S)
        (AddCircle.coverPullback_add_coe_period q S)) :=
  (rfl)

/-- **Complex linearity.** For a loop `S` of complex-linear maps the orbit-torus operator on a skew
cover commutes with multiplication by complex scalars, the complex structure of the Sobolev spaces
acting by `J₀`. -/
theorem skewTorusOperator_apply_smul (ℓ σ : ℝ) {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v, S t (I • v) = I • S t v) (c : ℂ)
    (x : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))) :
    skewTorusOperator T q ℓ σ S (c • x) = c • skewTorusOperator T q ℓ σ S x := by
  refine Prod.ext ?_ ?_
  · simp only [skewTorusOperator_apply, Prod.smul_fst]
    rw [loopOperator_smul T hS, smul_comm c I]
  · simp only [skewTorusOperator_apply, Prod.smul_snd]
    exact skewTorusModeOperator_apply_smul ((q : ℝ) * T) ℓ σ _ _
      (loopOperator_smul ((q : ℝ) * T) (coverPullback_apply_I_smul q hS)) c x.2

/-- **The reference operator is complex linear.** For `S = 0` the operator `∂s + J₀ ∂t` on a skew
cover commutes with multiplication by complex scalars, the complex structure of the Sobolev spaces
acting by `J₀`. -/
theorem skewTorusOperator_zero_apply_smul (ℓ σ : ℝ) (c : ℂ)
    (x : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))) :
    skewTorusOperator T q ℓ σ 0 (c • x) = c • skewTorusOperator T q ℓ σ 0 x :=
  skewTorusOperator_apply_smul T q ℓ σ (fun _ _ ↦ by simp) c x

/-- The operator of a skew cover on the modes of nonzero frequency depends continuously on the
loop. -/
private theorem continuous_skewTorusModeOperator_coverPullback (ℓ σ : ℝ) :
    Continuous fun S : C(AddCircle T, F →L[ℝ] F) ↦
      skewTorusModeOperator ((q : ℝ) * T) ℓ σ _ (AddCircle.coverPullback q S)
        (AddCircle.coverPullback_add_coe_period q S) :=
  (continuous_skewTorusModeOperator _ ℓ σ _).comp
    (f := fun S : C(AddCircle T, F →L[ℝ] F) ↦
      (⟨AddCircle.coverPullback q S, AddCircle.coverPullback_add_coe_period q S⟩ :
        {S' : C(AddCircle ((q : ℝ) * T), F →L[ℝ] F) // ∀ t, S' (t + (T : ℝ)) = S' t}))
    ((AddCircle.continuous_coverPullback q).subtype_mk _)

/-- **Continuous dependence on the loop.** The orbit-torus operator on a skew cover depends
continuously, in operator norm, on the loop `S` with its uniform norm. -/
theorem continuous_skewTorusOperator (ℓ σ : ℝ) :
    Continuous (skewTorusOperator (F := F) T q ℓ σ) :=
  ((continuous_loopOperator T).const_smul I).prod_mapL ℝ
    (continuous_skewTorusModeOperator_coverPullback T q ℓ σ)

end Operator

/-! ### Invertibility on the modes of nonzero frequency -/

section Inner

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceSkewCoverInner : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- If the orbit-torus operator maps `x` to a target invariant under the translation by `(σ, θ)`,
then `x` is invariant: the rotation `θ x` and the shift `σ x` have the same image
`θ (D x) = σ (D x)`, so `θ x = σ x` by injectivity. -/
private theorem mem_skewTorusModeSobolev_of_mem {ℓ σ : ℝ} (hℓ : ℓ ≠ 0) {θ : AddCircle T}
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hS' : ∀ t, S (t + θ) = S t) {x : torusModeSobolev F fun k : ℕ ↦ 2 * (k + 1) * π / ℓ}
    (hx : torusModeOperator T (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) S x ∈ skewTorusModeL2 F ℓ σ θ) :
    (x : 𝕏[F]) ∈ skewTorusModeSobolev F ℓ σ θ := by
  have h : rotateMode θ x = shiftMode σ x := by
    refine (isInvertible_torusModeOperator_periodic T hℓ S hS).injective
      (lp.ext (funext fun k ↦ ?_))
    rw [torusModeOperator_rotateMode T hS', torusModeOperator_shiftMode,
      mem_skewTorusModeL2_iff_rotatePair.1 hx k]
  refine mem_skewTorusModeSobolev_iff_rotatePair.2 ⟨x.property, fun k ↦ ?_⟩
  simpa only [rotateMode_fst_apply, shiftMode_fst_apply] using
    congrArg (fun z : torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) ↦ (z : 𝕏[F]).1 k) h

/-- **Invertibility on the modes of nonzero frequency.** For `ℓ ≠ 0` and every infinitesimally
symplectic loop `S` invariant under the rotation by `θ`, the orbit-torus operator `∂s + A`,
`A ζ = J₀ (ζ' - S ζ)`, is invertible from the Sobolev space `H¹` of maps periodic in `s` with no
`s`-independent part, invariant under the translation by `(σ, θ)`, onto the corresponding `L²`
space. -/
theorem isInvertible_skewTorusModeOperator {ℓ : ℝ} (hℓ : ℓ ≠ 0) (σ : ℝ) {θ : AddCircle T}
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hS' : ∀ t, S (t + θ) = S t) :
    (skewTorusModeOperator T ℓ σ θ S hS').IsInvertible :=
  -- The inverse of `D` maps invariant targets to invariant maps.
  isInvertible_restrictTorusModeOperator T _ _ _
    (isInvertible_torusModeOperator_periodic T hℓ S hS) fun _ hx ↦
      mem_skewTorusModeSobolev_of_mem T hℓ hS hS' hx

end Inner

/-! ### The comparison with the return map -/

section Comparison

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] (q : ℕ) [NeZero q] {ℓ : ℝ} (σ : ℝ)

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceSkewCoverComparison : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F


/-- The modes of nonzero frequency of the operator on a skew cover form an invertible operator. -/
private theorem isInvertible_skewTorusModeOperator_coverPullback (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (skewTorusModeOperator ((q : ℝ) * T) ℓ σ _ (AddCircle.coverPullback q S)
      (AddCircle.coverPullback_add_coe_period q S)).IsInvertible :=
  isInvertible_skewTorusModeOperator _ hℓ σ _ (im_inner_coverPullback_add_eq_zero q hS) _

/-- **The kernel of the orbit-torus operator on a skew cover.** For `ℓ ≠ 0` and an infinitesimally
symplectic loop `S`, taking the `s`-independent mode is a linear equivalence from the kernel of
`∂s + A` on a skew cover (`TauCeti.skewTorusOperator`) onto the kernel of `L_S ζ = ζ' - S ζ` on
loops of period `T` (`TauCeti.coe_kerSkewTorusOperatorEquiv_apply`); the kernel elements are
`s`-independent. It is `TauCeti.kerProdMapLoopOperatorEquiv` for the invertible operator on the
other modes. -/
def kerSkewTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    ker (skewTorusOperator T q ℓ σ S).toLinearMap ≃ₗ[ℝ]
      ker (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) :=
  kerProdMapLoopOperatorEquiv T S (isInvertible_skewTorusModeOperator_coverPullback T q σ hℓ S hS)

/-- The kernel elements of `TauCeti.skewTorusOperator` are `s`-independent: the inverse of
`TauCeti.kerSkewTorusOperatorEquiv` sends `a` to the map `(a, 0)` with no other modes. -/
@[simp]
theorem kerSkewTorusOperatorEquiv_symm_apply (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (a : ker (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F)) :
    ((kerSkewTorusOperatorEquiv T q σ hℓ S hS).symm a :
      CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))) =
        ((a : CircleSobolev 1 F), 0) :=
  kerProdMapLoopOperatorEquiv_symm_apply T S _ a

@[simp]
theorem coe_kerSkewTorusOperatorEquiv_apply (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (x : ker (skewTorusOperator T q ℓ σ S).toLinearMap) :
    (kerSkewTorusOperatorEquiv T q σ hℓ S hS x : CircleSobolev 1 F) = x.val.1 :=
  coe_kerProdMapLoopOperatorEquiv_apply T S _ x

/-- **The cokernel of the orbit-torus operator on a skew cover.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S`, `z ↦ -J₀ z₀` on the `s`-independent mode induces a linear
equivalence from the cokernel of `∂s + A` on a skew cover (`TauCeti.skewTorusOperator`) onto the
cokernel of `L_S ζ = ζ' - S ζ` on loops of period `T`
(`TauCeti.quotientRangeSkewTorusOperatorEquiv_mk`). It is
`TauCeti.quotientRangeProdMapLoopOperatorEquiv` for the invertible operator on the other modes. -/
def quotientRangeSkewTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    ((CircleSobolev 0 F × skewTorusModeL2 F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))) ⧸
        range (skewTorusOperator T q ℓ σ S).toLinearMap) ≃ₗ[ℝ]
      CircleSobolev 0 F ⧸ range (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) :=
  quotientRangeProdMapLoopOperatorEquiv T S
    (isInvertible_skewTorusModeOperator_coverPullback T q σ hℓ S hS)

/-- On the class of `z`, `TauCeti.quotientRangeSkewTorusOperatorEquiv` is the class of `-J₀ z₀`,
where `z₀` is the `s`-independent mode of `z`. -/
@[simp]
theorem quotientRangeSkewTorusOperatorEquiv_mk (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (z : CircleSobolev 0 F × skewTorusModeL2 F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))) :
    quotientRangeSkewTorusOperatorEquiv T q σ hℓ S hS (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((-I) • z.1) :=
  quotientRangeProdMapLoopOperatorEquiv_mk T S _ z

/-- **The determinant line of the orbit-torus operator on a skew cover.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S`, the isomorphisms of kernels and cokernels with those of
`L_S ζ = ζ' - S ζ` (`TauCeti.kerSkewTorusOperatorEquiv`,
`TauCeti.quotientRangeSkewTorusOperatorEquiv`), followed by those of `L_S` with `1 - Ψ(T)`
(`TauCeti.CircleSobolev.kerLoopOperatorEquiv`,
`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv`), identify the determinant line of `∂s + A`
on a skew cover with the determinant line of `1 - Ψ(T)`, where `Ψ = TauCeti.dysonSeriesLeft S`. -/
def detLineSkewTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (skewTorusOperator T q ℓ σ S).toLinearMap.detLine ≃ₗ[ℝ]
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)).detLine :=
  detLineProdMapLoopOperatorEquiv T S
    (isInvertible_skewTorusModeOperator_coverPullback T q σ hℓ S hS)

/-- `TauCeti.detLineSkewTorusOperatorEquiv` is the isomorphism of determinant lines induced by the
isomorphisms of kernels and cokernels with those of `1 - Ψ(T)`. -/
theorem detLineSkewTorusOperatorEquiv_def (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    detLineSkewTorusOperatorEquiv T q σ hℓ S hS =
      LinearMap.detLineCongrKerCoker
        ((kerSkewTorusOperatorEquiv T q σ hℓ S hS).trans (kerLoopOperatorEquiv T S))
        ((quotientRangeSkewTorusOperatorEquiv T q σ hℓ S hS).trans
          (quotientRangeLoopOperatorEquiv T S)) :=
  detLineProdMapLoopOperatorEquiv_def T S _

/-- `TauCeti.detLineSkewTorusOperatorEquiv` is the transport along the isomorphisms of kernels and
cokernels with those of `L_S` (`TauCeti.kerSkewTorusOperatorEquiv`,
`TauCeti.quotientRangeSkewTorusOperatorEquiv`), followed by the identification of the determinant
line of `L_S` with that of `1 - Ψ(T)` (`TauCeti.CircleSobolev.detLineLoopOperatorEquiv`). -/
theorem detLineSkewTorusOperatorEquiv_eq_trans (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    detLineSkewTorusOperatorEquiv T q σ hℓ S hS =
      (LinearMap.detLineCongrKerCoker (kerSkewTorusOperatorEquiv T q σ hℓ S hS)
        (quotientRangeSkewTorusOperatorEquiv T q σ hℓ S hS)).trans
        (detLineLoopOperatorEquiv T S) :=
  detLineProdMapLoopOperatorEquiv_eq_trans T S _

/-- **The orbit-torus operator on a skew cover is Fredholm.** It is the direct sum of the Fredholm
operator `J₀ L_S` and an invertible operator. -/
theorem isFredholm_skewTorusOperator (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (skewTorusOperator T q ℓ σ S).IsFredholm :=
  isFredholm_prodMap_loopOperator T S
    (isInvertible_skewTorusModeOperator_coverPullback T q σ hℓ S hS)

/-- **The orbit-torus operator on a skew cover has index zero**, as `L_S`, whose kernel and
cokernel it shares. -/
@[simp]
theorem index_skewTorusOperator (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (skewTorusOperator T q ℓ σ S).index = 0 :=
  index_prodMap_loopOperator T S (isInvertible_skewTorusModeOperator_coverPullback T q σ hℓ S hS)

/-- **The Fredholm alternative on a skew cover.** For `ℓ ≠ 0` and an infinitesimally symplectic
loop `S` of period `T`, the operator `∂s + A` of `TauCeti.skewTorusOperator` is invertible exactly
when `det (1 - Ψ(T)) ≠ 0`, where `Ψ = TauCeti.dysonSeriesLeft S`, whatever the shear `σ` and the
integer `q`. When `q σ ∈ ℓ ℤ` it is the operator on maps periodic under the lattice spanned by
`(ℓ, 0)` and `(σ, T)`. -/
theorem isInvertible_skewTorusOperator_iff_det_ne_zero (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (skewTorusOperator T q ℓ σ S).IsInvertible ↔
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)) ≠ 0 :=
  isInvertible_prodMap_loopOperator_iff_det_ne_zero T S
    (isInvertible_skewTorusModeOperator_coverPullback T q σ hℓ S hS)

/-- **The Fredholm alternative on the covers of an orbit torus.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S` of period `T` with return map `P = Ψ(T)`, the operator
`∂s + J₀ (∂t - S)` of the loop traversed `n` times (`TauCeti.skewTorusOperator` for the period
`n T`) is invertible exactly when `det (1 - P ^ n) ≠ 0`, whatever `σ` and `q`. When `q σ ∈ ℓ ℤ` it
is the operator on maps periodic under the lattice spanned by `(ℓ, 0)` and `(σ, n T)`. Every
finite cover of the orbit torus has such a lattice, with `q = k` for `ℓ = k ℓ₀`, so this model
operator is invertible on all the finite covers exactly when no positive power of `P` has the
eigenvalue `1`. -/
theorem isInvertible_skewTorusOperator_coverPullback_iff_det_ne_zero (n : ℕ) [NeZero n]
    (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (skewTorusOperator ((n : ℝ) * T) q ℓ σ (AddCircle.coverPullback n S)).IsInvertible ↔
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F) ^ n) ≠ 0 := by
  rw [isInvertible_skewTorusOperator_iff_det_ne_zero _ q σ hℓ _
    (im_inner_coverPullback_add_eq_zero n hS), dysonSeriesLeft_coverPullback,
    ContinuousLinearMap.toLinearMap_pow]

/-- **The determinant line of a nondegenerate orbit-torus operator on a skew cover.** Let `∂s + A`
on a skew cover be bijective, equivalently `det (1 - Ψ(T)) ≠ 0`. Transporting its determinant line
to that of `1 - Ψ(T)` (`TauCeti.detLineSkewTorusOperatorEquiv`) and applying the canonical
trivialization of the determinant line of an endomorphism (`LinearMap.detLineEndEquiv`) gives
`(det (1 - Ψ(T)))⁻¹` times the trivialization of the determinant line of the bijective operator
(`LinearMap.detLineEquivOfBijective`). -/
theorem detLineEndEquiv_detLineSkewTorusOperatorEquiv (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hD : Function.Bijective (skewTorusOperator T q ℓ σ S).toLinearMap)
    (x : (skewTorusOperator T q ℓ σ S).toLinearMap.detLine) :
    LinearMap.detLineEndEquiv (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))
        (detLineSkewTorusOperatorEquiv T q σ hℓ S hS x) =
      (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)))⁻¹ *
        (skewTorusOperator T q ℓ σ S).toLinearMap.detLineEquivOfBijective hD x :=
  detLineEndEquiv_detLineProdMapLoopOperatorEquiv T S _ hD x

/-- **The orientation sign of a nondegenerate orbit-torus operator on a skew cover.** In the
situation of `TauCeti.detLineEndEquiv_detLineSkewTorusOperatorEquiv`, the orientation of the
determinant line of `∂s + A` on a skew cover induced by the canonical trivialization for
`1 - Ψ(T)` and the orientation given by bijectivity differ by the sign of `det (1 - Ψ(T))`. -/
theorem sign_detLineEndEquiv_detLineSkewTorusOperatorEquiv (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hD : Function.Bijective (skewTorusOperator T q ℓ σ S).toLinearMap)
    (x : (skewTorusOperator T q ℓ σ S).toLinearMap.detLine) :
    SignType.sign (LinearMap.detLineEndEquiv
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))
          (detLineSkewTorusOperatorEquiv T q σ hℓ S hS x)) =
      SignType.sign (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))) *
        SignType.sign ((skewTorusOperator T q ℓ σ S).toLinearMap.detLineEquivOfBijective hD x) :=
  sign_detLineEndEquiv_detLineProdMapLoopOperatorEquiv T S _ hD x

end Comparison

/-! ### The determinant signs on the skew covers -/

section Orientation

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] (q : ℕ) [NeZero q] {ℓ : ℝ} (σ : ℝ)
  {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ}

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceSkewCoverOrientation : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- **The orbit-torus operator on a skew cover has determinant sign `sgn det (1 - P)`.** Let `M` be
a path of infinitesimally symplectic loops of period `T`, continuous on `[a, b]`, whose loop `M a`
consists of complex-linear maps, so that the operator `∂s + J₀ (∂t - M a)` on the skew cover
(`TauCeti.skewTorusOperator`) is the real map underlying a complex-linear map `f`. If the operator
`∂s + J₀ (∂t - M b)` on the skew cover is bijective, equivalently `det (1 - Ψ_b(T)) ≠ 0`, every
element `x` of its determinant line in the orientation transported from the complex orientation at
`a` reads, in the trivialization given by bijectivity (`LinearMap.detLineEquivOfBijective`), with
the sign of `det (1 - Ψ_b(T))`, whatever the shear `σ` and the integer `q`. -/
theorem sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det (hℓ : ℓ ≠ 0)
    (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T)) →ₗ[ℂ]
      CircleSobolev 0 F × skewTorusModeL2 F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))}
    (hf : f.restrictScalars ℝ = skewTorusOperator T q ℓ σ (M a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (skewTorusOperator T q ℓ σ (M b)))
    {x : (skewTorusOperator T q ℓ σ (M b)).toLinearMap.detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport (T := fun τ ↦ skewTorusOperator T q ℓ σ (M τ)) a b
        ((continuous_skewTorusOperator T q ℓ σ).comp_continuousOn hM)
        (fun τ hτ ↦ isFredholm_skewTorusOperator T q σ hℓ (M τ) (hMs τ hτ))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_skewTorusOperator T q σ hℓ (M a) (hMs a left_mem_uIcc))))) :
    SignType.sign ((skewTorusOperator T q ℓ σ (M b)).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) :=
  sign_detLineEquivOfBijective_prodMap_loopOperator_eq_sign_det T
    (D := fun τ ↦ skewTorusOperator T q ℓ σ (M τ))
    (B := fun τ ↦ skewTorusModeOperator ((q : ℝ) * T) ℓ σ _ (AddCircle.coverPullback q (M τ))
      (AddCircle.coverPullback_add_coe_period q (M τ)))
    (fun τ ↦ skewTorusOperator_eq_prodMap T q ℓ σ (M τ)) hM
    ((continuous_skewTorusModeOperator_coverPullback T q ℓ σ).comp_continuousOn hM)
    (fun τ hτ ↦ isInvertible_skewTorusModeOperator_coverPullback T q σ hℓ (M τ) (hMs τ hτ)) hMa
    ((continuous_skewTorusOperator T q ℓ σ).comp_continuousOn hM)
    (fun τ hτ ↦ isFredholm_skewTorusOperator T q σ hℓ (M τ) (hMs τ hτ)) hf hz hb hx hxz

/-- **The orbit-torus operator on a skew cover twisted along `(σ, T)` has determinant sign
`sgn det (1 + Ψ(T))`.** In the situation of
`TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det`, consider the operators of
`TauCeti.skewTorusOperator` for the loops
`(M τ)ₐ = TauCeti.CircleSobolev.antiperiodicGaugeLoop T (M τ)`, whose return map is `-Ψ_τ(T)`.
When `q σ ∈ ℓ ℤ`, in the periodic gauge they are the operators on maps `u` with
`u (s + ℓ, t) = u (s, t)` and `u (s + σ, t + T) = -u (s, t)`, twisted by the real sign character
of the cover that is `-1` on `(σ, T)`; the result holds for every `q`. If the one at `b` is
bijective, every element `x` of its determinant line in the orientation transported from the
complex orientation at `a` reads, in the trivialization given by bijectivity, with the sign of
`det (1 + Ψ_b(T))`. -/
theorem sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_eq_sign_det
    (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × skewTorusModeSobolev F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T)) →ₗ[ℂ]
      CircleSobolev 0 F × skewTorusModeL2 F ℓ σ ((T : ℝ) : AddCircle ((q : ℝ) * T))}
    (hf : f.restrictScalars ℝ = skewTorusOperator T q ℓ σ (antiperiodicGaugeLoop T (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (skewTorusOperator T q ℓ σ (antiperiodicGaugeLoop T (M b))))
    {x : (skewTorusOperator T q ℓ σ (antiperiodicGaugeLoop T (M b))).toLinearMap.detLine}
    (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ skewTorusOperator T q ℓ σ (antiperiodicGaugeLoop T (M τ))) a b
        ((continuous_skewTorusOperator T q ℓ σ).comp_continuousOn
          ((continuous_antiperiodicGaugeLoop T).comp_continuousOn hM))
        (fun τ hτ ↦ isFredholm_skewTorusOperator T q σ hℓ _
          (im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs τ hτ)))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_skewTorusOperator T q σ hℓ _
              (im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs a left_mem_uIcc)))))) :
    SignType.sign ((skewTorusOperator T q ℓ σ
        (antiperiodicGaugeLoop T (M b))).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) := by
  rw [← one_sub_dysonSeriesLeft_antiperiodicGaugeLoop_period]
  exact sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det T q σ
    (M := fun τ ↦ antiperiodicGaugeLoop T (M τ)) hℓ
    ((continuous_antiperiodicGaugeLoop T).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs τ hτ))
    (antiperiodicGaugeLoop_apply_I_smul T hMa) hf hz hb hx hxz

/-- **The orbit-torus operator on a finite cover has determinant sign `sgn det (1 - P ^ n)`.** Let
`M` be a path of infinitesimally symplectic loops of period `T`, continuous on `[a, b]`, whose loop
`M a` consists of complex-linear maps, and read the loops with period `n T`. On the cover with
lattice spanned by `(ℓ, 0)` and `(σ, n T)` (for `q σ ∈ ℓ ℤ`), the operator
`∂s + J₀ (∂t - M a)` is the real map underlying a complex-linear map `f`. If the operator
`∂s + J₀ (∂t - M b)` on this cover is bijective, equivalently `det (1 - P ^ n) ≠ 0`, every element
`x` of its determinant line in the orientation transported from the complex orientation at `a`
reads, in the trivialization given by bijectivity, with the sign of `det (1 - P ^ n)`, where
`P = Ψ_b(T)` is the return map of `ζ' = M b ζ` over one period. The sign depends on the number `n`
of turns along the orbit only, not on the shear `σ`. -/
theorem sign_detLineEquivOfBijective_skewTorusOperator_coverPullback_eq_sign_det (n : ℕ)
    [NeZero n] (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F ×
        skewTorusModeSobolev F ℓ σ (((n : ℝ) * T : ℝ) : AddCircle ((q : ℝ) * ((n : ℝ) * T))) →ₗ[ℂ]
      CircleSobolev 0 F ×
        skewTorusModeL2 F ℓ σ (((n : ℝ) * T : ℝ) : AddCircle ((q : ℝ) * ((n : ℝ) * T)))}
    (hf : f.restrictScalars ℝ =
      skewTorusOperator ((n : ℝ) * T) q ℓ σ (AddCircle.coverPullback n (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective
      (skewTorusOperator ((n : ℝ) * T) q ℓ σ (AddCircle.coverPullback n (M b))))
    {x : (skewTorusOperator ((n : ℝ) * T) q ℓ σ
      (AddCircle.coverPullback n (M b))).toLinearMap.detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ skewTorusOperator ((n : ℝ) * T) q ℓ σ (AddCircle.coverPullback n (M τ))) a b
        ((continuous_skewTorusOperator _ q ℓ σ).comp_continuousOn
          ((AddCircle.continuous_coverPullback n).comp_continuousOn hM))
        (fun τ hτ ↦ isFredholm_skewTorusOperator _ q σ hℓ _
          (im_inner_coverPullback_add_eq_zero n (hMs τ hτ)))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_skewTorusOperator _ q σ hℓ _
              (im_inner_coverPullback_add_eq_zero n (hMs a left_mem_uIcc)))))) :
    SignType.sign ((skewTorusOperator ((n : ℝ) * T) q ℓ σ
        (AddCircle.coverPullback n (M b))).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F) ^ n)) := by
  rw [← ContinuousLinearMap.toLinearMap_pow, ← dysonSeriesLeft_coverPullback]
  exact sign_detLineEquivOfBijective_skewTorusOperator_eq_sign_det _ q σ
    (M := fun τ ↦ AddCircle.coverPullback n (M τ)) hℓ
    ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_coverPullback_add_eq_zero n (hMs τ hτ))
    (coverPullback_apply_I_smul n hMa) hf hz hb hx hxz

/-- **The operator on every finite cover twisted along `(σ, n T)` has determinant sign
`sgn det (1 + P ^ n)`.** In the situation of
`TauCeti.sign_detLineEquivOfBijective_skewTorusOperator_coverPullback_eq_sign_det`, consider the
operators of `TauCeti.skewTorusOperator` for the period `n T` and the loops
`TauCeti.CircleSobolev.antiperiodicGaugeLoop (n T)` of the pulled-back loops. When `q σ ∈ ℓ ℤ`
they are, in the periodic gauge, the operators on the cover with lattice spanned by `(ℓ, 0)` and
`(σ, n T)` twisted by the real sign character of the cover that is `-1` on `(σ, n T)`; the result
holds for every `q`. If the one at `b` is bijective, every element `x` of its determinant line in
the orientation transported from the complex orientation at `a` reads, in the trivialization given
by bijectivity, with the sign of `det (1 + P ^ n)`, where `P = Ψ_b(T)`. -/
theorem
sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_coverPullback_eq_sign_det
    (n : ℕ) [NeZero n] (hℓ : ℓ ≠ 0) (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F ×
        skewTorusModeSobolev F ℓ σ (((n : ℝ) * T : ℝ) : AddCircle ((q : ℝ) * ((n : ℝ) * T))) →ₗ[ℂ]
      CircleSobolev 0 F ×
        skewTorusModeL2 F ℓ σ (((n : ℝ) * T : ℝ) : AddCircle ((q : ℝ) * ((n : ℝ) * T)))}
    (hf : f.restrictScalars ℝ = skewTorusOperator ((n : ℝ) * T) q ℓ σ
      (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M a))))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (skewTorusOperator ((n : ℝ) * T) q ℓ σ
      (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M b)))))
    {x : (skewTorusOperator ((n : ℝ) * T) q ℓ σ (antiperiodicGaugeLoop ((n : ℝ) * T)
      (AddCircle.coverPullback n (M b)))).toLinearMap.detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ skewTorusOperator ((n : ℝ) * T) q ℓ σ
          (antiperiodicGaugeLoop ((n : ℝ) * T) (AddCircle.coverPullback n (M τ)))) a b
        ((continuous_skewTorusOperator _ q ℓ σ).comp_continuousOn
          ((continuous_antiperiodicGaugeLoop _).comp_continuousOn
            ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)))
        (fun τ hτ ↦ isFredholm_skewTorusOperator _ q σ hℓ _
          (im_inner_antiperiodicGaugeLoop_add_eq_zero _
            (im_inner_coverPullback_add_eq_zero n (hMs τ hτ))))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_skewTorusOperator _ q σ hℓ _
              (im_inner_antiperiodicGaugeLoop_add_eq_zero _
                (im_inner_coverPullback_add_eq_zero n (hMs a left_mem_uIcc))))))) :
    SignType.sign ((skewTorusOperator ((n : ℝ) * T) q ℓ σ (antiperiodicGaugeLoop ((n : ℝ) * T)
        (AddCircle.coverPullback n (M b)))).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F) ^ n)) := by
  rw [← ContinuousLinearMap.toLinearMap_pow, ← dysonSeriesLeft_coverPullback]
  exact sign_detLineEquivOfBijective_skewTorusOperator_antiperiodicGaugeLoop_eq_sign_det _ q σ
    (M := fun τ ↦ AddCircle.coverPullback n (M τ)) hℓ
    ((AddCircle.continuous_coverPullback n).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_coverPullback_add_eq_zero n (hMs τ hτ))
    (coverPullback_apply_I_smul n hMa) hf hz hb hx hxz

end Orientation

end TauCeti
