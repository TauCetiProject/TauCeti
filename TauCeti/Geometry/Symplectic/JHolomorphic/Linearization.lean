/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import TauCeti.Analysis.Calculus.ParametricFDeriv
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local-coordinate Cauchy–Riemann linearization

The Cauchy–Riemann defect is `du ∘ j - J(u) ∘ du`. Its zero set recovers
J-holomorphicity when the map is differentiable. We differentiate this actual nonlinear
operator for a jointly twice continuously differentiable family of maps and a differentiable
family of target endomorphisms. The parameter derivative includes both the
variation of the map and the variation of the target almost complex structure.

These are local-coordinate formulas, without a Sobolev completion or a transversality
assertion. For square-minus-one structures, the defect equals twice the usual anti-complex-linear
part composed with the source structure.
The geometric linearization follows McDuff–Salamon, *J-holomorphic Curves and Symplectic
Topology*, Section 3.1. The exchange of map and parameter derivatives uses
`TauCeti.hasFDerivAt_spatialFDeriv`, based on Mathlib's `ContDiffAt.isSymmSndFDerivAt`.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter
open scoped ContDiff Topology

variable {P U V : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The continuous-linear Cauchy–Riemann defect at a point. No square-minus-one
condition is needed for the construction or its differentiation. -/
noncomputable def cauchyRiemannOperator (j : U →L[ℝ] U) (J : V → V →L[ℝ] V)
    (u : U → V) (x : U) : U →L[ℝ] V :=
  (fderiv ℝ u x).comp j - (J (u x)).comp (fderiv ℝ u x)

/-- Evaluation of the Cauchy–Riemann defect. -/
@[simp]
theorem cauchyRiemannOperator_apply (j : U →L[ℝ] U) (J : V → V →L[ℝ] V)
    (u : U → V) (x v : U) :
    cauchyRiemannOperator j J u x v =
      fderiv ℝ u x (j v) - J (u x) (fderiv ℝ u x v) :=
  (rfl)

/-- Vanishing of the defect is precisely the existing J-holomorphicity condition.
Finite dimensionality supplies continuity of the algebraic almost complex structures. -/
theorem cauchyRiemannOperator_eq_zero_iff [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
    (j : AlmostComplexStructure U) (J : V → AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : DifferentiableAt ℝ u x) :
    cauchyRiemannOperator j.toLinearMap.toContinuousLinearMap
      (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) u x = 0 ↔
      IsJHolomorphicAt (fun _ ↦ j) J u x := by
  constructor
  · intro h
    apply isJHolomorphicAt_of_hasFDerivAt hu.hasFDerivAt
    apply (isComplexLinearMap_iff_apply _ _ _).mpr
    intro v
    have hv := congrArg (fun L : U →L[ℝ] V ↦ L v) h
    simpa using sub_eq_zero.mp hv
  · intro h
    ext v
    simp [h.fderiv_apply_commute]

/-- On an open set, the zero set of the defect agrees with J-holomorphicity on that set. -/
theorem cauchyRiemannOperator_eq_zero_on_iff [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
    (j : AlmostComplexStructure U) (J : V → AlmostComplexStructure V) (u : U → V)
    {s : Set U} (hs : IsOpen s) (hu : DifferentiableOn ℝ u s) :
    (∀ x ∈ s, cauchyRiemannOperator j.toLinearMap.toContinuousLinearMap
      (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) u x = 0) ↔
      IsJHolomorphicOn (fun _ ↦ j) J u s := by
  rw [isJHolomorphicOn_iff]
  constructor
  · intro h x hx
    exact ((cauchyRiemannOperator_eq_zero_iff j J u x
      ((hu x hx).differentiableAt (hs.mem_nhds hx))).mp (h x hx)).isJHolomorphicWithinAt
  · intro h x hx
    exact (cauchyRiemannOperator_eq_zero_iff j J u x
      ((hu x hx).differentiableAt (hs.mem_nhds hx))).mpr
        ((h x hx).isJHolomorphicAt_of_mem_nhds (hs.mem_nhds hx))

/-- The derivative of the Cauchy–Riemann defect in a map direction `ξ`, with the
target endomorphism field fixed. -/
noncomputable def cauchyRiemannLinearization (j : U →L[ℝ] U) (J : V → V →L[ℝ] V)
    (u ξ : U → V) (x : U) : U →L[ℝ] V :=
  (fderiv ℝ ξ x).comp j - (J (u x)).comp (fderiv ℝ ξ x) -
    (fderiv ℝ J (u x) (ξ x)).comp (fderiv ℝ u x)

/-- Evaluation of the local-coordinate map linearization. -/
@[simp]
theorem cauchyRiemannLinearization_apply (j : U →L[ℝ] U) (J : V → V →L[ℝ] V)
    (u ξ : U → V) (x v : U) :
    cauchyRiemannLinearization j J u ξ x v =
      fderiv ℝ ξ x (j v) - J (u x) (fderiv ℝ ξ x v) -
        fderiv ℝ J (u x) (ξ x) (fderiv ℝ u x v) :=
  (rfl)

/-- The local-coordinate linearization is additive on differentiable directions. -/
@[simp]
theorem cauchyRiemannLinearization_add (j : U →L[ℝ] U) (J : V → V →L[ℝ] V)
    (u ξ η : U → V) (x : U) (hξ : DifferentiableAt ℝ ξ x)
    (hη : DifferentiableAt ℝ η x) :
    cauchyRiemannLinearization j J u (ξ + η) x =
      cauchyRiemannLinearization j J u ξ x + cauchyRiemannLinearization j J u η x := by
  ext v
  simp only [cauchyRiemannLinearization_apply, fderiv_add hξ hη, add_apply,
    Pi.add_apply, map_add]
  abel

/-- The local-coordinate linearization respects real scaling, including for totalized
derivatives. -/
@[simp]
theorem cauchyRiemannLinearization_smul (j : U →L[ℝ] U) (J : V → V →L[ℝ] V)
    (u ξ : U → V) (x : U) (c : ℝ) :
    cauchyRiemannLinearization j J u (c • ξ) x = c • cauchyRiemannLinearization j J u ξ x := by
  ext v
  simp only [cauchyRiemannLinearization_apply, fderiv_const_smul_field c,
    smul_apply, Pi.smul_apply, map_smul, smul_sub]

/-- The nonlinear defect is differentiable along jointly `C²` map families and differentiable
endomorphism families. This is a derivative in the parameter normed space. -/
theorem differentiableAt_cauchyRiemannOperator
    (j : U →L[ℝ] U) (J : P → V → V →L[ℝ] V) (u : P → U → V)
    (p : P) (x : U) (hu : ContDiffAt ℝ 2 (Function.uncurry u) (p, x))
    (hJ : DifferentiableAt ℝ (Function.uncurry J) (p, u p x)) :
    DifferentiableAt ℝ (fun q ↦ cauchyRiemannOperator j (J q) (u q) x) p := by
  have hdu := (hu.fderiv (m := 1) contDiffAt_const (by norm_num)).differentiableAt
    (by norm_num)
  have huP := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp p
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p x)
  have hJP := hJ.hasFDerivAt.comp p
    ((hasFDerivAt_id p).prodMk huP)
  simpa only [cauchyRiemannOperator, Function.comp_def, Function.uncurry_def, id_eq,
    Pi.sub_def] using
    (hdu.clm_comp (differentiableAt_const j)).sub (hJP.differentiableAt.clm_comp hdu)

/-- Universal variation of the nonlinear Cauchy–Riemann operator. The direction field is
the actual parameter derivative of `u`; equality of mixed derivatives follows from joint
`C²` regularity rather than being an additional assumption. -/
theorem fderiv_cauchyRiemannOperator_apply
    (j : U →L[ℝ] U) (J : P → V → V →L[ℝ] V) (u : P → U → V)
    (p : P) (x : U) (hu : ContDiffAt ℝ 2 (Function.uncurry u) (p, x))
    (hJ : DifferentiableAt ℝ (Function.uncurry J) (p, u p x)) (h : P) (v : U) :
    fderiv ℝ (fun q ↦ cauchyRiemannOperator j (J q) (u q) x) p h v =
      cauchyRiemannLinearization j (J p) (u p)
        (fun y ↦ fderiv ℝ (fun q ↦ u q y) p h) x v -
      fderiv ℝ (fun q ↦ J q (u p x)) p h (fderiv ℝ (u p) x v) := by
  have hF := hu.differentiableAt (by norm_num)
  have hA := hasFDerivAt_spatialFDeriv (𝕜 := ℝ) (F := Function.uncurry u)
    (p := p) (x := x) (by simpa using hu)
  have hswap : ContDiffAt ℝ 2 (Function.uncurry (fun y q ↦ u q y)) (x, p) :=
    hu.comp (x, p) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hParameter :=
    (hswap.fderiv (m := 1) contDiffAt_const (by norm_num)).differentiableAt one_ne_zero
  have hξ : HasFDerivAt (fun y ↦ fderiv ℝ (fun q ↦ u q y) p h)
      ((fderiv ℝ (fun y ↦ fderiv ℝ (fun q ↦ u q y) p) x).flip h) x := by
    simpa only [comp_zero, zero_add] using
      hParameter.hasFDerivAt.clm_apply (hasFDerivAt_const (x := x) h)
  have huP := hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p x)
  have hJP := hJ.hasFDerivAt.comp p ((hasFDerivAt_id p).prodMk huP)
  have hresF := ((hA.clm_comp (hasFDerivAt_const (x := p) j)).sub
    (hJP.clm_comp hA)).fderiv
  simp only [Function.comp_def, Function.uncurry_def, id_eq, Pi.sub_def] at hresF
  simp only [cauchyRiemannOperator]
  rw [hresF]
  simp only [cauchyRiemannLinearization_apply, sub_apply, add_apply, comp_apply,
    compL_apply, flip_apply, zero_apply, map_zero, zero_add]
  rw [hξ.fderiv]
  simp only [flip_apply]
  have hJp := hJ.hasFDerivAt.comp p
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) p (u p x))
  have hJx := hJ.hasFDerivAt.comp (u p x)
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p (u p x))
  have eJp := hJp.fderiv
  have eJx := hJx.fderiv
  have euP := huP.fderiv
  simp only [Function.comp_def, Function.uncurry_def] at eJp eJx euP
  rw [eJp, eJx, euP]
  simp only [comp_apply, inl_apply, inr_apply, prod_apply, id_apply]
  have hsplit (a : V) : (h, a) = (0, a) + (h, (0 : V)) := by simp
  rw [hsplit, map_add]
  simp only [add_apply]
  abel

end TauCeti
