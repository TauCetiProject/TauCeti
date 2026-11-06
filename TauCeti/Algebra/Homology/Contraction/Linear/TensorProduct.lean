/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic

/-!
# Tensoring a contraction with a module carrying an operator

Let `(i, p, h)` be a special contraction of a graded module `(M, d_M)` onto `(N, d_N)`, with `i`
and `p` of degree zero and `h` of degree `-1`, and let `b` be any endomorphism of a module `C`.
The tensor product of `(M, d_M)` with `(C, b)` carries the endomorphism

`d_M ⊗ 1 + (1 ⊗ b) ∘ (τ ⊗ 1)`,

where `τ` is the Koszul twist of `M` (the sign `(-1)^{|x|}` on homogeneous `x`); when `d_M` has
degree one and squares to zero and `b` squares to zero, this is the differential of the tensor
product complex.  Then `(i ⊗ 1, p ⊗ 1, h ⊗ 1)` is a special contraction of `M ⊗ C` onto
`N ⊗ C` for these endomorphisms (`TauCeti.LinearSpecialContraction.rTensor`).  The only sign to
check is that `h`, having odd degree, anticommutes with `τ`, so the two cross terms
`(τ h + h τ) ⊗ b` cancel.  No condition on `b` is needed.

On the other side, let `C` be graded with Koszul twist `τ` and let `b` have degree one.  Then
`C ⊗ M` carries the endomorphism `b ⊗ 1 + τ ⊗ d_M`, and `(1 ⊗ i, 1 ⊗ p, τ ⊗ h)` is a special
contraction of `C ⊗ M` onto `C ⊗ N` (`TauCeti.LinearSpecialContraction.lTensor`).  Here the sign
sits on the homotopy, and the cross terms `(b τ + τ b) ⊗ h` cancel because `b` is odd; no
grading on `M` is needed.

This is the input of homological transfer for right `A∞` modules, where `C` is the coaugmented
bar construction of the algebra and `b` its bar differential: the higher module operations are
then a perturbation of the tensored contraction.  For `A∞` bimodules the contraction is tensored
with the bar constructions on both sides.

## Main definitions

* `TauCeti.LinearContraction.rTensor`: the contraction `(i ⊗ 1, p ⊗ 1, h ⊗ 1)` without side
  conditions, with homogeneity lemmas for its three maps.
* `TauCeti.LinearSpecialContraction.rTensor`: the special contraction `(i ⊗ 1, p ⊗ 1, h ⊗ 1)`.
* `TauCeti.LinearContraction.lTensor`: the contraction `(1 ⊗ i, 1 ⊗ p, τ ⊗ h)` without side
  conditions.
* `TauCeti.LinearSpecialContraction.lTensor`: the special contraction `(1 ⊗ i, 1 ⊗ p, τ ⊗ h)`.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
-/

public section

open scoped TensorProduct

universe uR uM uN uC

namespace TauCeti

namespace LinearContraction

variable {R : Type uR} [CommRing R]
  {M : Type uM} {N : Type uN} {C : Type uC}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup C] [Module R C]
  {dM : Module.End R M} {dN : Module.End R N}
  (G : InternalGrading R M) (H : InternalGrading R N) (b : Module.End R C)
  (c : LinearContraction dM dN)
  (hh : LinearMap.IsHomogeneous c.homotopy G.piece G.piece (-1))
  (hi : LinearMap.IsHomogeneous c.incl H.piece G.piece 0)
  (hp : LinearMap.IsHomogeneous c.proj G.piece H.piece 0)

/-- Tensor a graded contraction on the right with a fixed module with endomorphism.
The tensor endomorphisms use the Koszul sign on the second summand. -/
noncomputable def rTensor :
    LinearContraction
      (dM.rTensor C + b.lTensor M ∘ₗ (G.koszulTwist 1).rTensor C)
      (dN.rTensor C + b.lTensor N ∘ₗ (H.koszulTwist 1).rTensor C) where
  incl := c.incl.rTensor C
  proj := c.proj.rTensor C
  homotopy := c.homotopy.rTensor C
  dM_comp_incl := by
    apply TensorProduct.ext'
    intro x y
    have h : G.koszulTwist 1 (c.incl x) = c.incl (H.koszulTwist 1 x) := by
      simpa using hi.koszulTwist_apply 1 x
    simp [h]
  proj_comp_dM := by
    apply TensorProduct.ext'
    intro x y
    have h : H.koszulTwist 1 (c.proj x) = c.proj (G.koszulTwist 1 x) := by
      simpa using hp.koszulTwist_apply 1 x
    simp [h]
  proj_comp_incl := by ext x y; simp
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply TensorProduct.ext'
    intro x y
    have h : G.koszulTwist 1 (c.homotopy x) = -c.homotopy (G.koszulTwist 1 x) := by
      simpa using hh.koszulTwist_apply 1 x
    have hc := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at hc
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, LinearMap.id_apply, map_add, LinearMap.sub_apply]
    rw [h, TensorProduct.neg_tmul]
    calc
      _ = (dM (c.homotopy x) + c.homotopy (dM x)) ⊗ₜ[R] y := by
        rw [TensorProduct.add_tmul]
        abel
      _ = _ := by rw [hc, TensorProduct.sub_tmul]

@[simp]
theorem rTensor_incl : (c.rTensor G H b hh hi hp).incl = c.incl.rTensor C := (rfl)

@[simp]
theorem rTensor_proj : (c.rTensor G H b hh hi hp).proj = c.proj.rTensor C := (rfl)

@[simp]
theorem rTensor_homotopy :
    (c.rTensor G H b hh hi hp).homotopy = c.homotopy.rTensor C := (rfl)

/-- The tensor extension's inclusion has degree zero for any grading on the right factor. -/
theorem isHomogeneous_rTensor_incl (K : InternalGrading R C) :
    LinearMap.IsHomogeneous (c.rTensor G H b hh hi hp).incl
      (H.tensorProduct K).piece (G.tensorProduct K).piece 0 := by
  rw [rTensor_incl]
  exact hi.rTensor K

/-- The tensor extension's projection has degree zero for any grading on the right factor. -/
theorem isHomogeneous_rTensor_proj (K : InternalGrading R C) :
    LinearMap.IsHomogeneous (c.rTensor G H b hh hi hp).proj
      (G.tensorProduct K).piece (H.tensorProduct K).piece 0 := by
  rw [rTensor_proj]
  exact hp.rTensor K

/-- The tensor extension's homotopy has degree minus one for any grading on the right factor. -/
theorem isHomogeneous_rTensor_homotopy (K : InternalGrading R C) :
    LinearMap.IsHomogeneous (c.rTensor G H b hh hi hp).homotopy
      (G.tensorProduct K).piece (G.tensorProduct K).piece (-1) := by
  rw [rTensor_homotopy]
  exact hh.rTensor K

end LinearContraction

namespace LinearSpecialContraction

variable {R : Type uR} {M : Type uM} {N : Type uN} {C : Type uC} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup C] [Module R C]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {GM : InternalGrading R M} {GN : InternalGrading R N}
  (hh : LinearMap.IsHomogeneous c.homotopy GM.piece GM.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GN.piece GM.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj GM.piece GN.piece 0)
  (b : Module.End R C)

/-- **Tensoring a special contraction with a module carrying an operator.**  A special
contraction `(i, p, h)` of `(M, d_M)` onto `(N, d_N)`, by maps of degrees `0`, `0` and `-1`,
induces the special contraction `(i ⊗ 1, p ⊗ 1, h ⊗ 1)` of `M ⊗ C` onto `N ⊗ C` for the
endomorphisms `d ⊗ 1 + (1 ⊗ b) ∘ (τ ⊗ 1)`, with `τ` the Koszul twists. -/
noncomputable def rTensor :
    LinearSpecialContraction (dM.rTensor C + b.lTensor M ∘ₗ (GM.koszulTwist 1).rTensor C)
      (dN.rTensor C + b.lTensor N ∘ₗ (GN.koszulTwist 1).rTensor C) where
  toLinearContraction := c.toLinearContraction.rTensor GM GN b hh hincl hproj
  homotopy_comp_incl := by
    rw [LinearContraction.rTensor_homotopy, LinearContraction.rTensor_incl,
      ← LinearMap.rTensor_comp, c.homotopy_comp_incl, LinearMap.rTensor_zero]
  proj_comp_homotopy := by
    rw [LinearContraction.rTensor_proj, LinearContraction.rTensor_homotopy,
      ← LinearMap.rTensor_comp, c.proj_comp_homotopy, LinearMap.rTensor_zero]
  homotopy_comp_homotopy := by
    rw [LinearContraction.rTensor_homotopy, ← LinearMap.rTensor_comp,
      c.homotopy_comp_homotopy, LinearMap.rTensor_zero]

/-- Forgetting the side conditions commutes with tensoring a special contraction. -/
@[simp]
theorem toLinearContraction_rTensor :
    (c.rTensor hh hincl hproj b).toLinearContraction =
      c.toLinearContraction.rTensor GM GN b hh hincl hproj := (rfl)

/-- The inclusion of the tensored contraction is `i ⊗ 1`. -/
@[simp↓]
theorem rTensor_incl : (c.rTensor hh hincl hproj b).incl = c.incl.rTensor C := (rfl)

/-- The projection of the tensored contraction is `p ⊗ 1`. -/
@[simp↓]
theorem rTensor_proj : (c.rTensor hh hincl hproj b).proj = c.proj.rTensor C := (rfl)

/-- The homotopy of the tensored contraction is `h ⊗ 1`. -/
@[simp↓]
theorem rTensor_homotopy : (c.rTensor hh hincl hproj b).homotopy = c.homotopy.rTensor C := (rfl)

end LinearSpecialContraction

namespace LinearContraction

variable {R : Type uR} [CommRing R]
  {M : Type uM} {N : Type uN} {C : Type uC}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup C] [Module R C]
  {dM : Module.End R M} {dN : Module.End R N}
  {K : InternalGrading R C} {b : Module.End R C}
  (hb : LinearMap.IsHomogeneous b K.piece K.piece 1) (c : LinearContraction dM dN)

include hb in
/-- Tensor a contraction on the left with a graded module carrying an operator `b` of degree one.
The tensor endomorphisms are `b ⊗ 1 + τ ⊗ d`, with `τ` the Koszul twist of the left factor, and
the homotopy `τ ⊗ h` carries the same sign. -/
noncomputable def lTensor :
    LinearContraction (b.rTensor M + TensorProduct.map (K.koszulTwist 1) dM)
      (b.rTensor N + TensorProduct.map (K.koszulTwist 1) dN) where
  incl := c.incl.lTensor C
  proj := c.proj.lTensor C
  homotopy := TensorProduct.map (K.koszulTwist 1) c.homotopy
  dM_comp_incl := by
    refine TensorProduct.ext' fun y x ↦ ?_
    have h := LinearMap.congr_fun c.dM_comp_incl x
    simp only [LinearMap.comp_apply] at h
    simp [h]
  proj_comp_dM := by
    refine TensorProduct.ext' fun y x ↦ ?_
    have h := LinearMap.congr_fun c.proj_comp_dM x
    simp only [LinearMap.comp_apply] at h
    simp [h]
  proj_comp_incl := by
    rw [← LinearMap.lTensor_comp, c.proj_comp_incl, LinearMap.lTensor_id]
  dM_comp_homotopy_add_homotopy_comp_dM := by
    refine TensorProduct.ext' fun y x ↦ ?_
    have hτb : K.koszulTwist 1 (b y) = -b (K.koszulTwist 1 y) := by
      simpa using hb.koszulTwist_apply 1 y
    have hc := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at hc
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply, LinearMap.sub_apply,
      map_add, hτb, InternalGrading.koszulTwist_koszulTwist, TensorProduct.neg_tmul]
    rw [← TensorProduct.tmul_sub, ← hc, TensorProduct.tmul_add]
    abel

/-- The inclusion of the left tensored contraction is `1 ⊗ i`. -/
@[simp]
theorem lTensor_incl : (c.lTensor hb).incl = c.incl.lTensor C := (rfl)

/-- The projection of the left tensored contraction is `1 ⊗ p`. -/
@[simp]
theorem lTensor_proj : (c.lTensor hb).proj = c.proj.lTensor C := (rfl)

/-- The homotopy of the left tensored contraction is `τ ⊗ h`. -/
@[simp]
theorem lTensor_homotopy :
    (c.lTensor hb).homotopy = TensorProduct.map (K.koszulTwist 1) c.homotopy := (rfl)

end LinearContraction

namespace LinearSpecialContraction

variable {R : Type uR} {M : Type uM} {N : Type uN} {C : Type uC} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup C] [Module R C]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {K : InternalGrading R C} {b : Module.End R C}
  (hb : LinearMap.IsHomogeneous b K.piece K.piece 1)

/-- **Tensoring a special contraction on the left with a complex.**  A special contraction
`(i, p, h)` of `(M, d_M)` onto `(N, d_N)` induces the special contraction `(1 ⊗ i, 1 ⊗ p, τ ⊗ h)`
of `C ⊗ M` onto `C ⊗ N` for the endomorphisms `b ⊗ 1 + τ ⊗ d`, where `b` has degree one and `τ`
is the Koszul twist of `C`. -/
noncomputable def lTensor :
    LinearSpecialContraction (b.rTensor M + TensorProduct.map (K.koszulTwist 1) dM)
      (b.rTensor N + TensorProduct.map (K.koszulTwist 1) dN) where
  toLinearContraction := c.toLinearContraction.lTensor hb
  homotopy_comp_incl := by
    rw [LinearContraction.lTensor_homotopy, LinearContraction.lTensor_incl,
      LinearMap.map_comp_lTensor, c.homotopy_comp_incl, TensorProduct.map_zero_right]
  proj_comp_homotopy := by
    rw [LinearContraction.lTensor_proj, LinearContraction.lTensor_homotopy,
      LinearMap.lTensor_comp_map, c.proj_comp_homotopy, TensorProduct.map_zero_right]
  homotopy_comp_homotopy := by
    rw [LinearContraction.lTensor_homotopy, ← TensorProduct.map_comp, c.homotopy_comp_homotopy,
      TensorProduct.map_zero_right]

/-- Forgetting the side conditions commutes with tensoring a special contraction on the left. -/
@[simp]
theorem toLinearContraction_lTensor :
    (c.lTensor hb).toLinearContraction = c.toLinearContraction.lTensor hb := (rfl)

/-- The inclusion of the left tensored contraction is `1 ⊗ i`. -/
@[simp↓]
theorem lTensor_incl : (c.lTensor hb).incl = c.incl.lTensor C := (rfl)

/-- The projection of the left tensored contraction is `1 ⊗ p`. -/
@[simp↓]
theorem lTensor_proj : (c.lTensor hb).proj = c.proj.lTensor C := (rfl)

/-- The homotopy of the left tensored contraction is `τ ⊗ h`. -/
@[simp↓]
theorem lTensor_homotopy :
    (c.lTensor hb).homotopy = TensorProduct.map (K.koszulTwist 1) c.homotopy := (rfl)

end LinearSpecialContraction

end TauCeti
