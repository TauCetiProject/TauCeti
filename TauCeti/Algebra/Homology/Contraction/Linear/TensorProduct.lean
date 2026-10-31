/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Tensoring a special contraction with a module carrying an operator

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

This is the input of homological transfer for right `A∞` modules, where `C` is the coaugmented
bar construction of the algebra and `b` its bar differential: the higher module operations are
then a perturbation of the tensored contraction.

## Main definitions

* `TauCeti.LinearSpecialContraction.rTensor`: the special contraction `(i ⊗ 1, p ⊗ 1, h ⊗ 1)`.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
-/

public section

open scoped TensorProduct

universe uR uM uN uC

namespace TauCeti

namespace LinearSpecialContraction

variable {R : Type uR} {M : Type uM} {N : Type uN} {C : Type uC} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup C] [Module R C]
  {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {GM : InternalGrading R M} {GN : InternalGrading R N}
  (hh : LinearMap.IsHomogeneous c.homotopy GM.piece GM.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GN.piece GM.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj GM.piece GN.piece 0)
  (b : Module.End R C)

include hincl in
/-- The inclusion, of degree zero, commutes with the Koszul twists. -/
private theorem koszulTwist_incl (x : N) :
    GM.koszulTwist 1 (c.incl x) = c.incl (GN.koszulTwist 1 x) := by
  simpa using hincl.koszulTwist_apply 1 x

include hproj in
/-- The projection, of degree zero, commutes with the Koszul twists. -/
private theorem koszulTwist_proj (x : M) :
    GN.koszulTwist 1 (c.proj x) = c.proj (GM.koszulTwist 1 x) := by
  simpa using hproj.koszulTwist_apply 1 x

include hh in
/-- The homotopy, of degree `-1`, anticommutes with the Koszul twist. -/
private theorem koszulTwist_homotopy (x : M) :
    GM.koszulTwist 1 (c.homotopy x) = -c.homotopy (GM.koszulTwist 1 x) := by
  simpa using hh.koszulTwist_apply 1 x

/-- **Tensoring a special contraction with a module carrying an operator.**  A special
contraction `(i, p, h)` of `(M, d_M)` onto `(N, d_N)`, by maps of degrees `0`, `0` and `-1`,
induces the special contraction `(i ⊗ 1, p ⊗ 1, h ⊗ 1)` of `M ⊗ C` onto `N ⊗ C` for the
endomorphisms `d ⊗ 1 + (1 ⊗ b) ∘ (τ ⊗ 1)`, with `τ` the Koszul twists. -/
noncomputable def rTensor :
    LinearSpecialContraction (dM.rTensor C + b.lTensor M ∘ₗ (GM.koszulTwist 1).rTensor C)
      (dN.rTensor C + b.lTensor N ∘ₗ (GN.koszulTwist 1).rTensor C) where
  incl := c.incl.rTensor C
  proj := c.proj.rTensor C
  homotopy := c.homotopy.rTensor C
  dM_comp_incl := TensorProduct.ext' fun x y ↦ by
    simp [c.koszulTwist_incl hincl]
  proj_comp_dM := TensorProduct.ext' fun x y ↦ by
    simp [c.koszulTwist_proj hproj]
  proj_comp_incl := by
    rw [← LinearMap.rTensor_comp, c.proj_comp_incl, LinearMap.rTensor_id]
  dM_comp_homotopy_add_homotopy_comp_dM := TensorProduct.ext' fun x y ↦ by
    have e := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at e
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, LinearMap.sub_apply, LinearMap.id_apply,
      c.koszulTwist_homotopy hh, map_add]
    rw [← TensorProduct.sub_tmul, ← e, TensorProduct.add_tmul, TensorProduct.neg_tmul]
    abel
  homotopy_comp_incl := by
    rw [← LinearMap.rTensor_comp, c.homotopy_comp_incl, LinearMap.rTensor_zero]
  proj_comp_homotopy := by
    rw [← LinearMap.rTensor_comp, c.proj_comp_homotopy, LinearMap.rTensor_zero]
  homotopy_comp_homotopy := by
    rw [← LinearMap.rTensor_comp, c.homotopy_comp_homotopy, LinearMap.rTensor_zero]

/-- The inclusion of the tensored contraction is `i ⊗ 1`. -/
@[simp]
theorem rTensor_incl : (c.rTensor hh hincl hproj b).incl = c.incl.rTensor C := (rfl)

/-- The projection of the tensored contraction is `p ⊗ 1`. -/
@[simp]
theorem rTensor_proj : (c.rTensor hh hincl hproj b).proj = c.proj.rTensor C := (rfl)

/-- The homotopy of the tensored contraction is `h ⊗ 1`. -/
@[simp]
theorem rTensor_homotopy : (c.rTensor hh hincl hproj b).homotopy = c.homotopy.rTensor C := (rfl)

end LinearSpecialContraction

end TauCeti
