/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Complex
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Antiperiodic
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.ComplexOrientation
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.PeriodicSobolev
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The determinant signs of the orbit-torus operators periodic along the circle factor

Let `γ` be a closed orbit of the suspension flow of a surface diffeomorphism and `C = S¹ × γ` its
orbit torus in `S¹ × Y_φ`. In a unitary trivialization of the normal bundle, the normal operator of
`C` is `D = ∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, for a loop `S` which is infinitesimally symplectic for
`Im ⟪·, ·⟫`, with return map `P = Ψ(T)` of `ζ' = S ζ`. In Taubes's weighted count, each of the four
real sign characters of the torus twists `D`, and the twisted operator contributes the sign of its
determinant line: the orientation obtained by transporting the complex orientation of a
complex-linear reference operator, such as `∂s + J₀ ∂t`, along a path of Fredholm operators to `D`,
read against the orientation given by invertibility of `D`. The two characters nontrivial along
the circle factor contribute `+`
(`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.AntiperiodicOrientation`). This file proves
that the character trivial on both factors contributes `sgn det (1 - P)` and the character
nontrivial on `γ` only contributes `sgn det (1 + P)`.

For the characters trivial along the circle factor, `D` acts on maps periodic in `s`
(`TauCeti.periodicTorusOperator`). Unlike the operators antiperiodic in `s`, it is not invertible
along a path to the complex-linear reference: `∂s + J₀ ∂t` has the constant maps as kernel. Its
determinant line is identified with that of the endomorphism `1 - P` of the fibre
(`TauCeti.detLinePeriodicTorusOperatorEquiv`), through the identification for the loop operator
`L_S ζ = ζ' - S ζ` (`TauCeti.CircleSobolev.detLineLoopOperatorEquiv`) and the inclusions of the
`s`-independent mode. The steps are:

* **Coherence.** Along a family of loops, the normalized generators of the determinant lines of
  `1 - P` (`LinearMap.detLineEndGenerator`), transported to the orbit-torus operators, form a
  continuous orientation of their determinant line bundle
  (`TauCeti.isDetLineCoherentOn_detLinePeriodicTorusOperatorEquiv_symm`). A kernel chart `(D₂, q)`
  of `L_S` gives the kernel chart `(l ↦ (J₀ D₂ l, 0), ((a, y), l) ↦ q (a, l))` of `D`, which reads
  the transported generators exactly as the first reads those of `L_S`, whose coherence is
  `TauCeti.CircleSobolev.isDetLineCoherentOn_detLineLoopOperatorEquiv_symm`. So transport along a
  path of loops carries the transported generator at one end to the one at the other
  (`TauCeti.detLineOrientationTransport_rayOfNeZero_detLinePeriodicTorusOperatorEquiv_symm`).
* **The complex orientation.** For a loop of complex-linear maps, the transported generator is
  complex positive
  (`TauCeti.isComplexPositiveDetLine_detLineCongrOfEq_detLinePeriodicTorusOperatorEquiv_symm`),
  since `1 - P` is complex linear and the identifications of kernels and cokernels commute with `I`.
  Hence transporting the complex orientation from a complex-linear loop gives the transported
  generator (`TauCeti.detLineOrientationTransport_rayOfNeZero_periodicTorusOperator`).
* **The sign.** At a bijective endpoint the transported generator is `det (1 - P)` times the
  generator of the trivialization given by bijectivity
  (`LinearMap.detLineCongrKerCoker_symm_detLineEndGenerator_eq_det_smul`), so the
  determinant sign is `sgn det (1 - P)`
  (`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det`). The character
  nontrivial on `γ` only is realized in the periodic gauge by the loop `Sₐ` of
  `TauCeti.CircleSobolev.antiperiodicGaugeLoop`, whose return map is `-P`; its sign is
  `sgn det (1 + P)`
  (`TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det`).

These are the signs that `TauCeti.orbitTorusTwistSign` prescribes from the return map on the two
characters trivial on `S¹`, here obtained as determinant signs of the model operators.

The three steps use only that the periodic orbit-torus operator is `(J₀ L_S) ⊕ B` for an invertible
operator `B` on the modes of nonzero frequency (`TauCeti.detLineProdMapLoopOperatorEquiv`). They
are proved once for every such operator, with `B` depending continuously on the parameter
(`TauCeti.isDetLineCoherentOn_detLineProdMapLoopOperatorEquiv_symm`,
`TauCeti.detLineOrientationTransport_rayOfNeZero_prodMap_loopOperator`,
`TauCeti.sign_detLineEquivOfBijective_prodMap_loopOperator_eq_sign_det`), and the operators on the
skew covers of an orbit torus (`TauCeti.skewTorusOperator`) are of this form too.

## Main results

* `TauCeti.isDetLineCoherentOn_detLineProdMapLoopOperatorEquiv_symm`,
  `TauCeti.detLineOrientationTransport_rayOfNeZero_prodMap_loopOperator` and
  `TauCeti.sign_detLineEquivOfBijective_prodMap_loopOperator_eq_sign_det`: coherence, transport of
  the complex orientation and the determinant sign `sgn det (1 - Ψ(T))` for `(J₀ L_S) ⊕ B`.
* `TauCeti.isDetLineCoherentOn_detLinePeriodicTorusOperatorEquiv_symm`: the transported normalized
  generators are coherent along families of loops.
* `TauCeti.detLineOrientationTransport_rayOfNeZero_periodicTorusOperator`: transport of the complex
  orientation from a complex-linear loop follows the return maps.
* `TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det`: the untwisted
  operator has determinant sign `sgn det (1 - P)`.
* `TauCeti.sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det`:
  the operator twisted along the orbit only has determinant sign `sgn det (1 + P)`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893 (the determinant signs of the twisted normal operators
  of tori).
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

/-- The `L²` space of mode sequences, the target of `TauCeti.torusModeOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {ℓ : ℝ}

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpacePeriodicOrientation : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-! ### The asymptotic operator beside an invertible operator

The arguments below use only that the orbit-torus operator is `(J₀ L_S) ⊕ B` for an invertible `B`
(`TauCeti.detLineProdMapLoopOperatorEquiv`), so they are stated for every such operator. The
periodic orbit-torus operator (`B` the operator on the modes of nonzero frequency) and the operator
on a skew cover (`TauCeti.skewTorusOperator`) are of this form. -/

section ProdMap

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']

/-! #### Kernel charts -/

section Chart

variable {Λ G : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- The stabilizer `l ↦ (J₀ D₂ l, 0)` of `(J₀ L_S) ⊕ B` built from a stabilizer `D₂` of `L_S`. -/
private def torusStab (D₂ : Λ →L[ℝ] CircleSobolev 0 F) : Λ →L[ℝ] CircleSobolev 0 F × E' :=
  ContinuousLinearMap.inl ℝ _ _ ∘L (I • D₂)

/-- The kernel coordinate `((a, y), l) ↦ q (a, l)` of the stabilized `(J₀ L_S) ⊕ B` built from a
kernel coordinate `q` of the stabilized `L_S`. -/
private def torusCoord (q : CircleSobolev 1 F × Λ →L[ℝ] G) : (CircleSobolev 1 F × E) × Λ →L[ℝ] G :=
  q ∘L (ContinuousLinearMap.fst ℝ _ _).prodMap (ContinuousLinearMap.id ℝ Λ)

/-- **Kernel charts of `L_S` give kernel charts of `(J₀ L_S) ⊕ B`.** For an invertible `B`, if
`(D₂, q)` is a kernel chart of `L_S`, then `(l ↦ (J₀ D₂ l, 0), ((a, y), l) ↦ q (a, l))` is a kernel
chart of `(J₀ L_S) ⊕ B`, and it reads the transport of an element `y` of the determinant line of
`L_S` along the isomorphisms of kernels and cokernels (`TauCeti.kerProdMapLoopOperatorEquiv`,
`TauCeti.quotientRangeProdMapLoopOperatorEquiv`) as the first chart reads `y`. -/
private theorem exists_detLineChartEquiv_detLineCongrKerCoker_symm
    (S : C(AddCircle T, F →L[ℝ] F)) {B : E →L[ℝ] E'} (hB : B.IsInvertible)
    {D₂ : Λ →L[ℝ] CircleSobolev 0 F} {q : CircleSobolev 1 F × Λ →L[ℝ] G}
    (h : (((loopOperator T S).coprod D₂).prod q).IsInvertible)
    (y : (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F).detLine) :
    ∃ h' : ((((I • loopOperator T S).prodMap B).coprod (torusStab (E' := E') D₂)).prod
        (torusCoord (E := E) q)).IsInvertible,
      ContinuousLinearMap.detLineChartEquiv ((I • loopOperator T S).prodMap B) (torusStab D₂)
          (torusCoord q) h'
          ((LinearMap.detLineCongrKerCoker (kerProdMapLoopOperatorEquiv T S hB)
            (quotientRangeProdMapLoopOperatorEquiv T S hB)).symm y) =
        ContinuousLinearMap.detLineChartEquiv (loopOperator T S) D₂ q h y := by
  set Φ : (CircleSobolev 1 F × E) × Λ →ₗ[ℝ] CircleSobolev 1 F × Λ :=
    (LinearMap.fst ℝ _ _).prodMap LinearMap.id
  have hΦ : ∀ y, ((I • loopOperator T S).prodMap B).coprod (torusStab D₂) y = 0 →
      (loopOperator T S).coprod D₂ (Φ y) = 0 := by
    rintro ⟨⟨a, b⟩, l⟩ hy
    have h1 : I • loopOperator T S a + I • D₂ l = 0 := by
      simpa [torusStab] using congrArg Prod.fst hy
    rw [← smul_add, smul_eq_zero] at h1
    simpa [Φ] using h1.resolve_left I_ne_zero
  have hK : ∀ u : ker ((I • loopOperator T S).prodMap B).toLinearMap,
      Φ ((u : CircleSobolev 1 F × E), 0) =
        ((kerProdMapLoopOperatorEquiv T S hB u : CircleSobolev 1 F), 0) := fun u ↦
    Prod.ext (coe_kerProdMapLoopOperatorEquiv_apply T S hB u).symm rfl
  have hΛ : ∀ y, ((I • loopOperator T S).prodMap B).coprod (torusStab D₂) y = 0 →
      (Φ y).2 = LinearEquiv.refl ℝ Λ y.2 := fun _ _ ↦ rfl
  have hC : ∀ l, quotientRangeProdMapLoopOperatorEquiv T S hB
      (((I • loopOperator T S).prodMap B).toLinearMap.range.mkQ (torusStab D₂ l)) =
        (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F).range.mkQ
          (D₂ (LinearEquiv.refl ℝ Λ l)) := fun l ↦ by
    rw [Submodule.mkQ_apply, quotientRangeProdMapLoopOperatorEquiv_mk]
    simp [torusStab, smul_smul]
  have hq : ∀ y, ((I • loopOperator T S).prodMap B).coprod (torusStab D₂) y = 0 →
      q (Φ y) = LinearEquiv.refl ℝ G (torusCoord q y) := fun _ _ ↦ rfl
  have h' := ContinuousLinearMap.isInvertible_prod_coprod_of_kerCokerEquiv hΦ hK hΛ hC
    (LinearEquiv.refl ℝ G) hq h
  refine ⟨h', ?_⟩
  have := ContinuousLinearMap.detLineChartEquiv_detLineCongrKerCoker hΦ hK hΛ hC
    (LinearEquiv.refl ℝ G) hq h' h
    ((LinearMap.detLineCongrKerCoker (kerProdMapLoopOperatorEquiv T S hB)
      (quotientRangeProdMapLoopOperatorEquiv T S hB)).symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  simp [LinearEquiv.detLineCongr_refl]

end Chart

/-! #### Coherence along families -/

omit [CompleteSpace E] [CompleteSpace E'] in
/-- `(J₀ L_{M x}) ⊕ B x` depends continuously on `x` where `M` and `B` do. -/
theorem continuousOn_prodMap_loopOperator {X : Type*} [TopologicalSpace X]
    {M : X → C(AddCircle T, F →L[ℝ] F)} {B : X → E →L[ℝ] E'} {s : Set X}
    (hM : ContinuousOn M s) (hBc : ContinuousOn B s) :
    ContinuousOn (fun x ↦ (I • loopOperator T (M x)).prodMap (B x)) s :=
  ContinuousOn.prod_mapL ℝ (((continuous_loopOperator T).const_smul I).comp_continuousOn hM) hBc

/-- **The determinant lines of a family `(J₀ L_{M x}) ⊕ B x` and of its return maps are coherently
identified.** Let `M` be a family of continuous loops and `B` a family of invertible operators,
both continuous on a parameter set `s`, and let `w x` be the normalized generator of the
determinant line of `1 - Ψ_x(T)` (`LinearMap.detLineEndGenerator`), `Ψ_x` the propagator of
`ζ' = M x ζ`, transported to the determinant line of `(J₀ L_{M x}) ⊕ B x` along
`TauCeti.detLineProdMapLoopOperatorEquiv`. Then `w` is coherent on `s`
(`TauCeti.IsDetLineCoherentOn`): a continuous orientation of the determinant line bundle of the
family, although kernels and cokernels jump. A kernel chart of the loop operators `L_{M x}` gives
a kernel chart of `(J₀ L_{M x}) ⊕ B x` reading `w x` as it reads the coherent family of
`TauCeti.CircleSobolev.isDetLineCoherentOn_detLineLoopOperatorEquiv_symm`. -/
theorem isDetLineCoherentOn_detLineProdMapLoopOperatorEquiv_symm {X : Type*}
    [TopologicalSpace X] {M : X → C(AddCircle T, F →L[ℝ] F)} {B : X → E →L[ℝ] E'} {s : Set X}
    (hM : ContinuousOn M s) (hBc : ContinuousOn B s) (hB : ∀ x ∈ s, (B x).IsInvertible)
    {w : ∀ x, ((I • loopOperator T (M x)).prodMap (B x) :
      CircleSobolev 1 F × E →ₗ[ℝ] CircleSobolev 0 F × E').detLine}
    (hw : ∀ x (hx : x ∈ s), w x = (detLineProdMapLoopOperatorEquiv T (M x) (hB x hx)).symm
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M x t) T) : F →ₗ[ℝ] F)).detLineEndGenerator) :
    IsDetLineCoherentOn (fun x ↦ (I • loopOperator T (M x)).prodMap (B x)) w s := by
  -- On `s`, `w` is the transport of the coherent family of the loop operators.
  have hw' (x : X) (hx : x ∈ s) : w x =
      (LinearMap.detLineCongrKerCoker (kerProdMapLoopOperatorEquiv T (M x) (hB x hx))
        (quotientRangeProdMapLoopOperatorEquiv T (M x) (hB x hx))).symm
        ((detLineLoopOperatorEquiv T (M x)).symm
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M x t) T) : F →ₗ[ℝ] F)).detLineEndGenerator) := by
    rw [hw x hx, detLineProdMapLoopOperatorEquiv_eq_trans, LinearEquiv.symm_trans_apply]
  refine isDetLineCoherentOn_iff.2 fun x₀ hx₀ ↦ ?_
  obtain ⟨-, S, _, G, _, q, h₀, hev⟩ := isDetLineCoherentWithinAt_iff.1
    (isDetLineCoherentOn_iff.1 (isDetLineCoherentOn_detLineLoopOperatorEquiv_symm T M s hM) x₀ hx₀)
  obtain ⟨h₀', -⟩ := exists_detLineChartEquiv_detLineCongrKerCoker_symm T (M x₀) (hB x₀ hx₀) h₀
    ((detLineLoopOperatorEquiv T (M x₀)).symm
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M x₀ t) T) : F →ₗ[ℝ] F)).detLineEndGenerator)
  have hne : w x₀ ≠ 0 := by
    rw [hw' x₀ hx₀]
    exact (LinearEquiv.map_ne_zero_iff _).2 ((LinearEquiv.map_ne_zero_iff _).2
      (LinearMap.detLineEndGenerator_ne_zero _))
  refine isDetLineCoherentWithinAt_of_eventually_sameRay (s := s) (x₀ := x₀)
    (T := fun x ↦ (I • loopOperator T (M x)).prodMap (B x)) (v := w)
    (continuousOn_prodMap_loopOperator T hM hBc x₀ hx₀)
    (isFredholm_prodMap_loopOperator T (M x₀) (hB x₀ hx₀)) hne h₀'
    ((hev.and (self_mem_nhdsWithin (s := s) (a := x₀))).mono fun x hx ↦ ?_)
  obtain ⟨⟨h, hx⟩, hxs⟩ := hx
  obtain ⟨h', -⟩ := exists_detLineChartEquiv_detLineCongrKerCoker_symm T (M x) (hB x hxs) h
    ((detLineLoopOperatorEquiv T (M x)).symm
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M x t) T) : F →ₗ[ℝ] F)).detLineEndGenerator)
  refine ⟨h', ?_⟩
  -- The readings of `w x` and `w x₀` are those of the coherent family of the loop operators.
  have e : ∀ y ∈ s, ∀ (h₁ : _) (h₂ : _), ContinuousLinearMap.detLineChartEquiv
      ((I • loopOperator T (M y)).prodMap (B y)) (torusStab S.subtypeL) (torusCoord q) h₁ (w y) =
      ContinuousLinearMap.detLineChartEquiv (loopOperator T (M y)) S.subtypeL q h₂
        ((detLineLoopOperatorEquiv T (M y)).symm
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M y t) T) : F →ₗ[ℝ] F)).detLineEndGenerator) := by
    intro y hy h₁ h₂
    rw [hw' y hy]
    exact (exists_detLineChartEquiv_detLineCongrKerCoker_symm T (M y) (hB y hy) h₂
      _).choose_spec
  exact (congrArg₂ (SameRay ℝ) (e x hxs h' h) (e x₀ hx₀ h₀' h₀)).mpr hx

variable {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {B : ℝ → E →L[ℝ] E'} {a b : ℝ}

/-- **Orientation transport along `(J₀ L_{M τ}) ⊕ B τ` follows the return maps.** Along a path `M`
of loops and a path `B` of invertible operators, both continuous on `[a, b]`, transport of
orientations of the determinant lines of `(J₀ L_{M τ}) ⊕ B τ` carries the orientation of the
transported normalized generator of `1 - Ψ_a(T)` to that of `1 - Ψ_b(T)`. -/
theorem detLineOrientationTransport_rayOfNeZero_detLineProdMapLoopOperatorEquiv_symm
    (hM : ContinuousOn M (uIcc a b)) (hBc : ContinuousOn B (uIcc a b))
    (hB : ∀ τ ∈ uIcc a b, (B τ).IsInvertible) :
    detLineOrientationTransport (T := fun τ ↦ (I • loopOperator T (M τ)).prodMap (B τ)) a b
        (continuousOn_prodMap_loopOperator T hM hBc)
        (fun τ hτ ↦ isFredholm_prodMap_loopOperator T (M τ) (hB τ hτ))
        (rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M a t) T) : F →ₗ[ℝ] F))) :
          (detLineProdMapLoopOperatorEquiv T (M a) (hB a left_mem_uIcc)).symm _ ≠ 0)) =
      rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) :
          (detLineProdMapLoopOperatorEquiv T (M b) (hB b right_mem_uIcc)).symm _ ≠ 0) := by
  classical
  -- The transported generators, extended by zero off `[a, b]`, form a coherent family.
  let W (τ : ℝ) : ((I • loopOperator T (M τ)).prodMap (B τ) :
      CircleSobolev 1 F × E →ₗ[ℝ] CircleSobolev 0 F × E').detLine :=
    if hτ : τ ∈ uIcc a b then (detLineProdMapLoopOperatorEquiv T (M τ) (hB τ hτ)).symm
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M τ t) T) : F →ₗ[ℝ] F)).detLineEndGenerator
    else 0
  have hW := isDetLineCoherentOn_detLineProdMapLoopOperatorEquiv_symm T hM hBc hB (w := W)
    fun τ hτ ↦ dite_eq_left hτ
  have hWa : W a = _ := dite_eq_left left_mem_uIcc
  have hWb : W b = _ := dite_eq_left right_mem_uIcc
  refine (congrArg (detLineOrientationTransport a b _ _) ((ray_eq_iff _ _).2 ?_)).trans
    ((detLineOrientationTransport_rayOfNeZero _ _ hW).trans ((ray_eq_iff _ _).2 ?_))
  · rw [hWa]
  · rw [hWb]

/-! #### The complex orientation -/

section Complex

variable [Module ℂ E] [IsScalarTower ℝ ℂ E] [Module ℂ E'] [IsScalarTower ℝ ℂ E']

omit [CompleteSpace E] [CompleteSpace E'] in
/-- **The complex orientation of a complex-linear `(J₀ L_S) ⊕ B`.** Let `S` be a loop of
complex-linear maps and `B` invertible, such that `(J₀ L_S) ⊕ B` is the real map underlying a
complex-linear map `f`. Then `TauCeti.detLineProdMapLoopOperatorEquiv` respects complex
orientations: the normalized generator of the determinant line of the complex-linear endomorphism
`1 - Ψ(T)` is carried to a complex positive element of the determinant line of `f`. The kernel
inclusion `a ↦ (a, 0)` and the cokernel map `[w] ↦ [(J₀ w, 0)]` commute with `I`, and so does the
identification for `L_S`,
`TauCeti.CircleSobolev.isComplexPositiveDetLine_detLineCongrOfEq_detLineLoopOperatorEquiv_symm`. -/
theorem isComplexPositiveDetLine_detLineCongrOfEq_detLineProdMapLoopOperatorEquiv_symm
    {S : C(AddCircle T, F →L[ℝ] F)} (hSI : ∀ t v, S t (I • v) = I • S t v)
    {B : E →L[ℝ] E'} (hB : B.IsInvertible)
    {f : CircleSobolev 1 F × E →ₗ[ℂ] CircleSobolev 0 F × E'}
    (hf : f.restrictScalars ℝ = (I • loopOperator T S).prodMap B) :
    f.IsComplexPositiveDetLine (LinearMap.detLineCongrOfEq hf.symm
      ((detLineProdMapLoopOperatorEquiv T S hB).symm
        (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)).detLineEndGenerator)) := by
  set A : CircleSobolev 1 F →ₗ[ℂ] CircleSobolev 0 F := (complexLoopOperator T hSI :
    CircleSobolev 1 F →ₗ[ℂ] CircleSobolev 0 F)
  have hA : (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) =
      A.restrictScalars ℝ := by
    rw [← restrictScalars_complexLoopOperator T hSI, ContinuousLinearMap.coe_restrictScalars]
  rw [detLineProdMapLoopOperatorEquiv_eq_trans, LinearEquiv.symm_trans_apply,
    LinearMap.detLineCongrKerCoker_symm]
  refine (isComplexPositiveDetLine_detLineCongrOfEq_detLineLoopOperatorEquiv_symm hSI
    hA).detLineCongrOfEq_detLineCongrKerCoker hA hf.symm (fun x y h ↦ ?_) fun y y' h ↦ ?_
  · rw [kerProdMapLoopOperatorEquiv_symm_apply, kerProdMapLoopOperatorEquiv_symm_apply, h]
    simp
  · -- The range of the complex-linear `L_S` is stable under `I`.
    rw [LinearEquiv.symm_apply_eq, quotientRangeProdMapLoopOperatorEquiv_mk,
      Submodule.Quotient.eq] at h ⊢
    obtain ⟨u, hu⟩ := h
    refine ⟨I • u, ?_⟩
    simp only [ContinuousLinearMap.coe_coe] at hu ⊢
    rw [loopOperator_I_smul T hSI, hu, Prod.smul_fst, smul_sub, smul_comm I (-I)]

/-- **Transport of the complex orientation along `(J₀ L_{M τ}) ⊕ B τ`.** Let `M` be a path of
loops and `B` a path of invertible operators, both continuous on `[a, b]`, such that the loop
`M a` consists of complex-linear maps and `(J₀ L_{M a}) ⊕ B a` is the real map underlying a
complex-linear map `f`. Transporting the complex orientation of `(J₀ L_{M a}) ⊕ B a`, that of any
complex positive element `z` of the determinant line of `f`, along the operators
`(J₀ L_{M τ}) ⊕ B τ` gives the orientation of the normalized generator of the determinant line of
`1 - Ψ_b(T)` transported along `TauCeti.detLineProdMapLoopOperatorEquiv`. -/
theorem detLineOrientationTransport_rayOfNeZero_prodMap_loopOperator
    (hM : ContinuousOn M (uIcc a b)) (hBc : ContinuousOn B (uIcc a b))
    (hB : ∀ τ ∈ uIcc a b, (B τ).IsInvertible) (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × E →ₗ[ℂ] CircleSobolev 0 F × E'}
    (hf : f.restrictScalars ℝ = (I • loopOperator T (M a)).prodMap (B a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    detLineOrientationTransport (T := fun τ ↦ (I • loopOperator T (M τ)).prodMap (B τ)) a b
        (continuousOn_prodMap_loopOperator T hM hBc)
        (fun τ hτ ↦ isFredholm_prodMap_loopOperator T (M τ) (hB τ hτ))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_prodMap_loopOperator T (M a) (hB a left_mem_uIcc)))) =
      rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) :
          (detLineProdMapLoopOperatorEquiv T (M b) (hB b right_mem_uIcc)).symm _ ≠ 0) := by
  have := (isFredholm_prodMap_loopOperator T (M a)
    (hB a left_mem_uIcc)).finiteDimensional_quotient_range_of_restrictScalars_eq hf
  -- `z` is a positive multiple of the transported normalized generator, which is complex positive.
  obtain ⟨c, hc, rfl⟩ :=
    (isComplexPositiveDetLine_detLineCongrOfEq_detLineProdMapLoopOperatorEquiv_symm T hMa
      (hB a left_mem_uIcc) hf).exists_pos_smul_eq hz
  rw [← detLineOrientationTransport_rayOfNeZero_detLineProdMapLoopOperatorEquiv_symm T hM hBc hB]
  congr 1
  refine (ray_eq_iff _ _).2 ?_
  rw [LinearEquiv.map_smul, ← LinearMap.detLineCongrOfEq_symm hf, LinearEquiv.apply_symm_apply]
  exact SameRay.sameRay_pos_smul_left _ hc

/-- **`(J₀ L_S) ⊕ B` has determinant sign `sgn det (1 - Ψ(T))`.** In the situation of
`TauCeti.detLineOrientationTransport_rayOfNeZero_prodMap_loopOperator`, let `D` be a family of
operators with `D τ = (J₀ L_{M τ}) ⊕ B τ`, such as the orbit-torus operators on maps periodic in `s`
or on a skew cover, and let `D b` be bijective, equivalently `det (1 - Ψ_b(T)) ≠ 0`. Every element
`x` of its determinant line in the orientation transported along `D` from the complex orientation
of `D a` reads, in the trivialization given by bijectivity (`LinearMap.detLineEquivOfBijective`),
with the sign of `det (1 - Ψ_b(T))`. -/
theorem sign_detLineEquivOfBijective_prodMap_loopOperator_eq_sign_det
    {D : ℝ → CircleSobolev 1 F × E →L[ℝ] CircleSobolev 0 F × E'}
    (hD : ∀ τ, D τ = (I • loopOperator T (M τ)).prodMap (B τ))
    (hM : ContinuousOn M (uIcc a b)) (hBc : ContinuousOn B (uIcc a b))
    (hB : ∀ τ ∈ uIcc a b, (B τ).IsInvertible) (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × E →ₗ[ℂ] CircleSobolev 0 F × E'}
    (hf : f.restrictScalars ℝ = D a)
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (D b))
    {x : (D b).toLinearMap.detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport (T := D) a b
        ((continuousOn_prodMap_loopOperator T hM hBc).congr fun τ _ ↦ hD τ)
        (fun τ hτ ↦ hD τ ▸ isFredholm_prodMap_loopOperator T (M τ) (hB τ hτ))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (hD a ▸ isFredholm_prodMap_loopOperator T (M a) (hB a left_mem_uIcc))))) :
    SignType.sign ((D b).toLinearMap.detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) := by
  obtain rfl : D = fun τ ↦ (I • loopOperator T (M τ)).prodMap (B τ) := funext hD
  rw [detLineOrientationTransport_rayOfNeZero_prodMap_loopOperator T hM hBc hB hMa hf hz,
    ray_eq_iff, detLineProdMapLoopOperatorEquiv_def] at hxz
  exact LinearMap.sign_detLineEquivOfBijective_eq_sign_det_of_sameRay _ hb _ _ hx hxz

end Complex

end ProdMap

/-! ### The periodic orbit-torus operator

The periodic orbit-torus operator is `(J₀ L_S) ⊕ B` for the invertible operator `B` on the modes of
nonzero frequency (`TauCeti.periodicTorusOperator_eq_prodMap`), so the results below are those of
the previous section. Their proofs rely on the exposed definitions of
`TauCeti.periodicTorusOperator` and `TauCeti.detLinePeriodicTorusOperatorEquiv` unfolding
definitionally to `(J₀ L_S) ⊕ B` and to `TauCeti.detLineProdMapLoopOperatorEquiv`. -/

/-- **The determinant lines of a family of periodic orbit-torus operators and of its return maps are
coherently identified.** Let `M` be a family of continuous loops, continuous on a parameter set
`s` and infinitesimally symplectic at every point of `s`, and let `w x` be the normalized generator
of the determinant line of `1 - Ψ_x(T)` (`LinearMap.detLineEndGenerator`), `Ψ_x` the propagator of
`ζ' = M x ζ`, transported to the determinant line of `∂s + J₀ (∂t - M x)` on maps periodic in `s`
along `TauCeti.detLinePeriodicTorusOperatorEquiv`. Then `w` is coherent on `s`
(`TauCeti.IsDetLineCoherentOn`): a continuous orientation of the determinant line bundle of the
family, although kernels and cokernels jump. It is
`TauCeti.isDetLineCoherentOn_detLineProdMapLoopOperatorEquiv_symm` for the invertible operators on
the modes of nonzero frequency. -/
theorem isDetLineCoherentOn_detLinePeriodicTorusOperatorEquiv_symm (hℓ : ℓ ≠ 0) {X : Type*}
    [TopologicalSpace X] {M : X → C(AddCircle T, F →L[ℝ] F)} {s : Set X} (hM : ContinuousOn M s)
    (hMs : ∀ x ∈ s, ∀ t v w, (inner ℂ (M x t v) w).im + (inner ℂ v (M x t w)).im = 0)
    {w : ∀ x, (periodicTorusOperator T ℓ (M x) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine}
    (hw : ∀ x (hx : x ∈ s), w x = (detLinePeriodicTorusOperatorEquiv T hℓ (M x) (hMs x hx)).symm
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M x t) T) : F →ₗ[ℝ] F)).detLineEndGenerator) :
    IsDetLineCoherentOn (fun x ↦ periodicTorusOperator T ℓ (M x)) w s :=
  isDetLineCoherentOn_detLineProdMapLoopOperatorEquiv_symm T hM
    ((continuous_torusModeOperator T _).comp_continuousOn hM)
    (fun x hx ↦ isInvertible_torusModeOperator_periodic T hℓ (M x) (hMs x hx)) hw

/-- **Orientation transport along periodic orbit-torus operators follows the return maps.** Along a
path `M` of infinitesimally symplectic loops, continuous on `[a, b]`, transport of orientations of
the determinant lines of the operators `∂s + J₀ (∂t - M τ)` on maps periodic in `s` carries the
orientation of the transported normalized generator of `1 - Ψ_a(T)` to that of `1 - Ψ_b(T)`. -/
theorem detLineOrientationTransport_rayOfNeZero_detLinePeriodicTorusOperatorEquiv_symm
    (hℓ : ℓ ≠ 0) {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ} (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0) :
    detLineOrientationTransport (T := fun τ ↦ periodicTorusOperator T ℓ (M τ)) a b
        ((continuous_periodicTorusOperator T ℓ).comp_continuousOn hM)
        (fun τ hτ ↦ isFredholm_periodicTorusOperator T hℓ (M τ) (hMs τ hτ))
        (rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M a t) T) : F →ₗ[ℝ] F))) :
          (detLinePeriodicTorusOperatorEquiv T hℓ (M a) (hMs a left_mem_uIcc)).symm _ ≠ 0)) =
      rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) :
          (detLinePeriodicTorusOperatorEquiv T hℓ (M b) (hMs b right_mem_uIcc)).symm _ ≠ 0) :=
  detLineOrientationTransport_rayOfNeZero_detLineProdMapLoopOperatorEquiv_symm T hM
    ((continuous_torusModeOperator T _).comp_continuousOn hM)
    (fun τ hτ ↦ isInvertible_torusModeOperator_periodic T hℓ (M τ) (hMs τ hτ))

/-- **The complex orientation of a complex-linear periodic orbit-torus operator.** Let `S` be an
infinitesimally symplectic loop of complex-linear maps, so that `∂s + J₀ (∂t - S)` on maps periodic
in `s` is the real map underlying a complex-linear map `f`. Then
`TauCeti.detLinePeriodicTorusOperatorEquiv` respects complex orientations: the normalized generator
of the determinant line of the complex-linear endomorphism `1 - Ψ(T)` is carried to a complex
positive element of the determinant line of `f`. -/
theorem isComplexPositiveDetLine_detLineCongrOfEq_detLinePeriodicTorusOperatorEquiv_symm
    (hℓ : ℓ ≠ 0) {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hSI : ∀ t v, S t (I • v) = I • S t v)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ = periodicTorusOperator T ℓ S) :
    f.IsComplexPositiveDetLine (LinearMap.detLineCongrOfEq hf.symm
      ((detLinePeriodicTorusOperatorEquiv T hℓ S hS).symm
        (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)).detLineEndGenerator)) :=
  isComplexPositiveDetLine_detLineCongrOfEq_detLineProdMapLoopOperatorEquiv_symm T hSI
    (isInvertible_torusModeOperator_periodic T hℓ S hS) hf

variable {M : ℝ → C(AddCircle T, F →L[ℝ] F)} {a b : ℝ}

/-- **Transport of the complex orientation along periodic orbit-torus operators.** Let `M` be a
path of infinitesimally symplectic loops, continuous on `[a, b]`, whose loop `M a` consists of
complex-linear maps, so that the operator `∂s + J₀ (∂t - M a)` on maps periodic in `s` is the real
map underlying a complex-linear map `f`. Transporting the complex orientation of
`∂s + J₀ (∂t - M a)`, that of any complex positive element `z` of the determinant line of `f`,
along the operators `∂s + J₀ (∂t - M τ)` gives the orientation of the normalized generator of the
determinant line of `1 - Ψ_b(T)` transported along `TauCeti.detLinePeriodicTorusOperatorEquiv`. -/
theorem detLineOrientationTransport_rayOfNeZero_periodicTorusOperator (hℓ : ℓ ≠ 0)
    (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ = periodicTorusOperator T ℓ (M a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z) :
    detLineOrientationTransport (T := fun τ ↦ periodicTorusOperator T ℓ (M τ)) a b
        ((continuous_periodicTorusOperator T ℓ).comp_continuousOn hM)
        (fun τ hτ ↦ isFredholm_periodicTorusOperator T hℓ (M τ) (hMs τ hτ))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator T hℓ (M a) (hMs a left_mem_uIcc)))) =
      rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) :
          (detLinePeriodicTorusOperatorEquiv T hℓ (M b) (hMs b right_mem_uIcc)).symm _ ≠ 0) :=
  detLineOrientationTransport_rayOfNeZero_prodMap_loopOperator T
    (B := fun τ ↦ torusModeOperator T (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) (M τ)) hM
    ((continuous_torusModeOperator T _).comp_continuousOn hM)
    (fun τ hτ ↦ isInvertible_torusModeOperator_periodic T hℓ (M τ) (hMs τ hτ)) hMa hf hz

/-! ### The absolute determinant signs -/

/-- **The untwisted orbit-torus operator has determinant sign `sgn det (1 - P)`.** In the situation
of `TauCeti.detLineOrientationTransport_rayOfNeZero_periodicTorusOperator`, let the operator
`∂s + J₀ (∂t - M b)` on maps periodic in `s` be bijective, equivalently `det (1 - Ψ_b(T)) ≠ 0`.
Every element `x` of its determinant line in the orientation transported from the complex
orientation of `∂s + J₀ (∂t - M a)` reads, in the trivialization given by bijectivity
(`LinearMap.detLineEquivOfBijective`), with the sign of `det (1 - Ψ_b(T))`. So the transported
complex orientation is the orientation given by bijectivity exactly when `det (1 - Ψ_b(T)) > 0`. -/
theorem sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det (hℓ : ℓ ≠ 0)
    (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ = periodicTorusOperator T ℓ (M a))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (periodicTorusOperator T ℓ (M b)))
    {x : (periodicTorusOperator T ℓ (M b) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport (T := fun τ ↦ periodicTorusOperator T ℓ (M τ)) a b
        ((continuous_periodicTorusOperator T ℓ).comp_continuousOn hM)
        (fun τ hτ ↦ isFredholm_periodicTorusOperator T hℓ (M τ) (hMs τ hτ))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator T hℓ (M a) (hMs a left_mem_uIcc))))) :
    SignType.sign ((periodicTorusOperator T ℓ (M b) :
        CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
          CircleSobolev 0 F × 𝕐[F]).detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) :=
  sign_detLineEquivOfBijective_prodMap_loopOperator_eq_sign_det T
    (D := fun τ ↦ periodicTorusOperator T ℓ (M τ))
    (B := fun τ ↦ torusModeOperator T (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) (M τ))
    (fun τ ↦ periodicTorusOperator_eq_prodMap T ℓ (M τ)) hM
    ((continuous_torusModeOperator T _).comp_continuousOn hM)
    (fun τ hτ ↦ isInvertible_torusModeOperator_periodic T hℓ (M τ) (hMs τ hτ)) hMa hf hz hb hx hxz

/-- **The orbit-torus operator twisted along the orbit has determinant sign `sgn det (1 + P)`.**
Let `M` be a path of infinitesimally symplectic loops, continuous on `[a, b]`, whose loop `M a`
consists of complex-linear maps. On maps periodic in `s` and antiperiodic along the orbit, realized
in the periodic gauge, the operators are `∂s + J₀ (∂t - (M τ)ₐ)` for the loops
`(M τ)ₐ = TauCeti.CircleSobolev.antiperiodicGaugeLoop T (M τ)`, and the one at `a` is the real map
underlying a complex-linear map `f`. If `∂s + J₀ (∂t - (M b)ₐ)` is bijective, equivalently
`det (1 + Ψ_b(T)) ≠ 0`, every element `x` of its determinant line in the orientation transported
from the complex orientation at `a` reads, in the trivialization given by bijectivity, with the
sign of `det (1 + Ψ_b(T))`, where `Ψ_b(T)` is the return map of `ζ' = M b ζ`. -/
theorem sign_detLineEquivOfBijective_periodicTorusOperator_antiperiodicGaugeLoop_eq_sign_det
    (hℓ : ℓ ≠ 0)
    (hM : ContinuousOn M (uIcc a b))
    (hMs : ∀ τ ∈ uIcc a b, ∀ t v w, (inner ℂ (M τ t v) w).im + (inner ℂ v (M τ t w)).im = 0)
    (hMa : ∀ t v, M a t (I • v) = I • M a t v)
    {f : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℂ]
      CircleSobolev 0 F × 𝕐[F]}
    (hf : f.restrictScalars ℝ = periodicTorusOperator T ℓ (antiperiodicGaugeLoop T (M a)))
    {z : (f.restrictScalars ℝ).detLine} (hz : f.IsComplexPositiveDetLine z)
    (hb : Function.Bijective (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T (M b))))
    {x : (periodicTorusOperator T ℓ (antiperiodicGaugeLoop T (M b)) :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
        CircleSobolev 0 F × 𝕐[F]).detLine} (hx : x ≠ 0)
    (hxz : rayOfNeZero ℝ x hx =
      detLineOrientationTransport
        (T := fun τ ↦ periodicTorusOperator T ℓ (antiperiodicGaugeLoop T (M τ))) a b
        ((continuous_periodicTorusOperator T ℓ).comp_continuousOn
          ((continuous_antiperiodicGaugeLoop T).comp_continuousOn hM))
        (fun τ hτ ↦ isFredholm_periodicTorusOperator T hℓ _
          (im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs τ hτ)))
        (rayOfNeZero ℝ (LinearMap.detLineCongrOfEq hf z)
          (hz.detLineCongrOfEq_ne_zero_of_isFredholm hf
            (isFredholm_periodicTorusOperator T hℓ _
              (im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs a left_mem_uIcc)))))) :
    SignType.sign ((periodicTorusOperator T ℓ (antiperiodicGaugeLoop T (M b)) :
        CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →ₗ[ℝ]
          CircleSobolev 0 F × 𝕐[F]).detLineEquivOfBijective hb x) =
      SignType.sign
        (LinearMap.det (1 + (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : F →ₗ[ℝ] F))) := by
  rw [← one_sub_dysonSeriesLeft_antiperiodicGaugeLoop_period]
  exact sign_detLineEquivOfBijective_periodicTorusOperator_eq_sign_det T
    (M := fun τ ↦ antiperiodicGaugeLoop T (M τ)) hℓ
    ((continuous_antiperiodicGaugeLoop T).comp_continuousOn hM)
    (fun τ hτ ↦ im_inner_antiperiodicGaugeLoop_add_eq_zero T (hMs τ hτ))
    (antiperiodicGaugeLoop_apply_I_smul T hMa) hf hz hb hx hxz

end TauCeti
