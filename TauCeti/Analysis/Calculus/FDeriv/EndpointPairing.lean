/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Endpoint bilinear pairings

Differentiate a bilinear pairing of endpoint differentials in time, retaining the coefficient
variation and both differential variations. Differentiating a terminal covector identity gives
an identity for the mixed endpoint differential paired with a test vector, including the
coefficient-variation term.

The statements allow arbitrary normed spaces over a nontrivially normed field, and bilinear
pairings with values in a normed space. Pointwise differentiability of the map and its derivative
suffices for time differentiation.
Symmetry requires `C²` over real or complex fields and
analyticity over other fields, as expressed by `minSmoothness`. Real scalar-valued pairings
supply the
coordinate Gram evolution used in reduced-volume Jacobian comparison. Constructing the geometric
endpoint map and proving its terminal covector identity are separate obligations.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Proposition 6.81.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The time derivative of an endpoint bilinear pairing includes the variations of the
coefficient and of both endpoint differentials. -/
theorem _root_.DifferentiableAt.hasDerivAt_endpoint_bilinear_pairing
    {E : X × 𝕜 → Y} {B : Y × 𝕜 → Y →L[𝕜] Y →L[𝕜] Z} {z : X × 𝕜}
    (hE : DifferentiableAt 𝕜 E z) (hDE : DifferentiableAt 𝕜 (fderiv 𝕜 E) z)
    (hB : DifferentiableAt 𝕜 B (E z, z.2)) (h k : X) :
    HasDerivAt
      (fun t ↦ B (E (z.1, t), t)
        (fderiv 𝕜 E (z.1, t) (h, 0)) (fderiv 𝕜 E (z.1, t) (k, 0)))
      (fderiv 𝕜 B (E z, z.2) (fderiv 𝕜 E z (0, 1), 1)
          (fderiv 𝕜 E z (h, 0)) (fderiv 𝕜 E z (k, 0)) +
        B (E z, z.2) (fderiv 𝕜 (fderiv 𝕜 E) z (0, 1) (h, 0))
          (fderiv 𝕜 E z (k, 0)) +
        B (E z, z.2) (fderiv 𝕜 E z (h, 0))
          (fderiv 𝕜 (fderiv 𝕜 E) z (0, 1) (k, 0))) z.2 := by
  have hD (v : X × 𝕜) :=
    hasDerivAt_fderiv_apply_snd (a := z.1) (t := z.2) hDE v
  have hBt : HasDerivAt (fun t ↦ B (E (z.1, t), t))
      (fderiv 𝕜 B (E z, z.2) (fderiv 𝕜 E z (0, 1), 1)) z.2 := by
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := 𝕜) (F := Y × 𝕜)
      (E := Y →L[𝕜] Y →L[𝕜] Z) (l := B)
      (f := fun t : 𝕜 ↦ (E (z.1, t), t)) z.2 hB.hasFDerivAt
      ((hasDerivAt_slice_right (a := z.1) (t := z.2)
        hE).prodMk (hasDerivAt_id z.2))
  simpa only [add_apply] using (hBt.clm_apply (hD (h, 0))).clm_apply
    (hD (k, 0))

/-- Differentiating an endpoint covector identity gives the mixed endpoint derivative paired
with `v`, together with the coefficient-variation term. -/
theorem _root_.ContDiffAt.fderiv_fderiv_eq_of_endpoint_pairing
    {E : X × 𝕜 → Y} {B : Y → Y →L[𝕜] Y →L[𝕜] Z} {l : Y → Z}
    {z : X × 𝕜} (hE : ContDiffAt 𝕜 (minSmoothness 𝕜 2) E z)
    (hB : DifferentiableAt 𝕜 B (E z)) (hl : DifferentiableAt 𝕜 (fderiv 𝕜 l) (E z))
    (h : X) (v : Y)
    (hpair : ∀ᶠ V in 𝓝 z.1,
      fderiv 𝕜 l (E (V, z.2)) v =
        B (E (V, z.2)) (fderiv 𝕜 E (V, z.2) (0, 1)) v) :
    fderiv 𝕜 (fderiv 𝕜 l) (E z) (fderiv 𝕜 E z (h, 0)) v =
      fderiv 𝕜 B (E z) (fderiv 𝕜 E z (h, 0))
          (fderiv 𝕜 E z (0, 1)) v +
        B (E z) (fderiv 𝕜 (fderiv 𝕜 E) z (0, 1) (h, 0)) v := by
  have hE2 : ContDiffAt 𝕜 2 E z := hE.of_le le_minSmoothness
  have hEs := (hE2.differentiableAt two_ne_zero).hasFDerivAt_slice_fst
  have hDE := hE2.hasFDerivAt_fderiv le_rfl
  have hDs := hDE.differentiableAt.hasFDerivAt_slice_fst
  have hls := hl.hasFDerivAt.comp z.1 hEs
  have hBs := hB.hasFDerivAt.comp z.1 hEs
  have hleft := hls.clm_apply (hasFDerivAt_const v z.1)
  have hright := (hBs.clm_apply (hDs.clm_apply (hasFDerivAt_const (0, 1) z.1))).clm_apply
    (hasFDerivAt_const v z.1)
  have hEq := congrArg (fun D : X →L[𝕜] Z ↦ D h)
    ((hleft.congr_of_eventuallyEq (Filter.EventuallyEq.symm hpair)).unique hright)
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    ContinuousLinearMap.inl_apply,
    map_zero, zero_add, Function.comp_def, Prod.eta] at hEq
  rw [← (hE.isSymmSndFDerivAt le_rfl).eq (0, 1) (h, 0)] at hEq
  simpa only [add_comm] using hEq

end TauCeti
