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
assertion. The Leibniz rule identifies the first-order symbol, and the reparametrization
formula proves that, for a `C²` curve J-holomorphic near the point, differentiable infinitesimal
source reparametrizations have tangent-valued linearization.
For square-minus-one structures, the defect equals twice the usual anti-complex-linear part
composed with the source structure.
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

/-- A vanishing Cauchy–Riemann defect makes the derivative intertwine the source and
target endomorphisms pointwise. -/
theorem fderiv_apply_eq_of_cauchyRiemannOperator_eq_zero
    {j : U →L[ℝ] U} {J : V → V →L[ℝ] V} {u : U → V} {x : U}
    (h : cauchyRiemannOperator j J u x = 0) (v : U) :
    fderiv ℝ u x (j v) = J (u x) (fderiv ℝ u x v) := by
  have hv := congrArg (fun L : U →L[ℝ] V ↦ L v) h
  simpa only [cauchyRiemannOperator_apply, zero_apply, sub_eq_zero] using hv

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
    exact fderiv_apply_eq_of_cauchyRiemannOperator_eq_zero h
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
  simp only [cauchyRiemannLinearization_apply, fderiv_add hξ hη, _root_.add_apply,
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
    _root_.smul_apply, Pi.smul_apply, map_smul, smul_sub]

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
  have hξ := hasFDerivAt_parameterFDeriv_apply (F := fun w ↦ u w.1 w.2) hu h
  have huP := hF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p x)
  have hJP := hJ.hasFDerivAt.comp p ((hasFDerivAt_id p).prodMk huP)
  have hresF := ((hA.clm_comp (hasFDerivAt_const (x := p) j)).sub
    (hJP.clm_comp hA)).fderiv
  simp only [Function.comp_def, Function.uncurry_def, id_eq, Pi.sub_def] at hresF
  simp only [cauchyRiemannOperator]
  rw [hresF]
  simp only [cauchyRiemannLinearization_apply, _root_.sub_apply, _root_.add_apply, comp_apply,
    compL_apply, flip_apply, _root_.zero_apply, map_zero, zero_add]
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
  simp only [comp_apply, inl_apply, inr_apply, ContinuousLinearMap.prod_apply, id_apply]
  have hsplit (a : V) : (h, a) = (0, a) + (h, (0 : V)) := by simp
  rw [hsplit, map_add]
  simp only [_root_.add_apply]
  abel

/-- Differentiating the holomorphicity identity in a source direction. -/
private theorem fderiv_cauchyRiemannOperator_eq_zero
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u : U → V) (x a v : U)
    (hu : ContDiffAt ℝ 2 u x) (hJ : DifferentiableAt ℝ J (u x))
    (hhol : ∀ᶠ y in 𝓝 x, cauchyRiemannOperator j J u y = 0) :
    fderiv ℝ (fderiv ℝ u) x a (j v) -
      J (u x) (fderiv ℝ (fderiv ℝ u) x a v) -
      fderiv ℝ J (u x) (fderiv ℝ u x a) (fderiv ℝ u x v) = 0 := by
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hJu := hJ.comp x (hu.differentiableAt (by norm_num))
  have hh : (fun y ↦ fderiv ℝ u y (j v)) =ᶠ[𝓝 x]
      (fun y ↦ J (u y) (fderiv ℝ u y v)) := by
    filter_upwards [hhol] with y hy
    exact fderiv_apply_eq_of_cauchyRiemannOperator_eq_zero hy v
  have hleft := (hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := x) (j v))).fderiv
  have hright := (hJu.hasFDerivAt.clm_apply
    (hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := x) v))).fderiv
  have he := congrArg (fun L : U →L[ℝ] V ↦ L a)
    (hleft.symm.trans (hh.fderiv_eq.trans hright))
  simp only [add_apply, comp_apply, flip_apply, zero_apply, map_zero, zero_add] at he
  rw [fderiv_comp x hJ (hu.differentiableAt (by norm_num))] at he
  simp only [comp_apply, Function.comp_apply] at he
  rw [he]
  abel

/-- The ambient linearization on an infinitesimal reparametrization is tangent:
`D_u(du · a) = du · (da ∘ j - j ∘ da)`. The target structure may vary arbitrarily off the curve. -/
theorem cauchyRiemannLinearization_fderiv_apply
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u : U → V) (a : U → U) (x v : U)
    (hu : ContDiffAt ℝ 2 u x) (ha : DifferentiableAt ℝ a x)
    (hJ : DifferentiableAt ℝ J (u x))
    (hhol : ∀ᶠ y in 𝓝 x, cauchyRiemannOperator j J u y = 0) :
    cauchyRiemannLinearization j J u (fun y ↦ fderiv ℝ u y (a y)) x v =
      fderiv ℝ u x (fderiv ℝ a x (j v) - j (fderiv ℝ a x v)) := by
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs := hu.isSymmSndFDerivAt (by norm_num)
  have he := fderiv_cauchyRiemannOperator_eq_zero j J u x (a x) v hu hJ hhol
  have ht : J (u x) (fderiv ℝ u x (fderiv ℝ a x v)) =
      fderiv ℝ u x (j (fderiv ℝ a x v)) :=
    (fderiv_apply_eq_of_cauchyRiemannOperator_eq_zero hhol.self_of_nhds _).symm
  simp only [cauchyRiemannLinearization_apply, fderiv_clm_apply hdu ha,
    add_apply, comp_apply, flip_apply, map_add, map_sub]
  rw [hs (j v) (a x), hs v (a x), ht]
  rw [sub_sub, sub_eq_zero] at he
  rw [he]
  abel

/-- Leibniz rule for the ambient linearization. Its symbol is
`ξ ↦ df(jv) ξ - df(v) J ξ`, with no integrability assumption on `J`. -/
theorem cauchyRiemannLinearization_fun_smul
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u ξ : U → V) (f : U → ℝ) (x v : U)
    (hf : DifferentiableAt ℝ f x) (hξ : DifferentiableAt ℝ ξ x) :
    cauchyRiemannLinearization j J u (fun y ↦ f y • ξ y) x v =
      f x • cauchyRiemannLinearization j J u ξ x v +
        fderiv ℝ f x (j v) • ξ x - fderiv ℝ f x v • J (u x) (ξ x) := by
  simp only [cauchyRiemannLinearization_apply, fderiv_fun_smul hf hξ, add_apply,
    smul_apply, smulRight_apply, map_add, map_smul, smul_sub]
  abel

end TauCeti
