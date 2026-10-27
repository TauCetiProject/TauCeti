/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Analysis.Complex.QuadraticLeviForm
public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Squared distance on complex manifolds

For a holomorphic map `i` from a complex manifold to a complex inner product space,
the Levi form of `x ↦ ‖i x - a‖²` is the pullback of the ambient Hermitian metric by
the actual complex manifold derivative of `i`. In particular, it is positive definite
at every immersion point, independently of the center `a`.

At a critical point the resulting intrinsic real Hessian identity bounds the real
Morse index by the complex dimension. These are the differential identities needed
to apply Morse theory to squared-distance exhaustions of complex submanifolds.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.

The calculation uses `TauCeti.manifoldLeviForm_comp_apply` and
`TauCeti.leviForm_norm_sq`.
-/

public section

open Complex Function Module
open scoped Manifold

namespace TauCeti

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] {i : M → F} {x : M} {a : F}

/-- The Levi form of squared distance along a holomorphic map is the pullback of the
ambient Hermitian metric. -/
@[simp]
theorem manifoldLeviForm_norm_sq_sub_apply
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v w : E) :
    manifoldLeviForm E (fun y ↦ ‖i y - a‖ ^ 2) x v w =
      inner ℂ (mvfderiv 𝓘(ℂ, E) i x v) (mvfderiv 𝓘(ℂ, E) i x w) := by
  have h := manifoldLeviForm_comp_apply (g := fun y ↦ i y - a)
    (u := fun z : F ↦ ‖z‖ ^ 2) (contDiff_norm_sq ℂ).contDiffAt.contMDiffAt
    (hi.sub contMDiffAt_const) v w
  have hd := mvfderiv_sub (hi.mdifferentiableAt (by norm_num))
    (mdifferentiableAt_const (I := 𝓘(ℂ, E)) (c := a) (x := x))
  simp only [mvfderiv_const, sub_zero, Pi.sub_def] at hd
  -- The vectors `v w : E` are passed explicitly, so that they are elaborated as tangent vectors.
  rw [← hd, mvfderiv_apply_eq_mfderiv_apply (fun y ↦ i y - a) x v,
    mvfderiv_apply_eq_mfderiv_apply (fun y ↦ i y - a) x w]
  rw [manifoldLeviForm_eq_leviForm, leviForm_norm_sq] at h
  simpa only [comp_def] using h.trans (innerₛₗ_apply_apply ℂ _ _)

/-- The Levi diagonal of squared distance is the squared norm of the complex tangent map. -/
theorem re_manifoldLeviForm_norm_sq_sub_apply_self
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v : E) :
    (manifoldLeviForm E (fun y ↦ ‖i y - a‖ ^ 2) x v v).re =
      ‖mvfderiv 𝓘(ℂ, E) i x v‖ ^ 2 := by
  rw [manifoldLeviForm_norm_sq_sub_apply hi, ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq _

/-- Squared distance along a holomorphic map is strictly plurisubharmonic exactly at
its immersion points. -/
@[simp]
theorem isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_iff
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) :
    IsManifoldStrictlyPlurisubharmonicAt E (fun y ↦ ‖i y - a‖ ^ 2) x ↔
      Injective (mvfderiv 𝓘(ℂ, E) i x) := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff]
  constructor
  · intro h
    refine (injective_iff_map_eq_zero (mvfderiv 𝓘(ℂ, E) i x)).2 fun v hv ↦ ?_
    by_contra hne
    have hp := h v hne
    rw [re_manifoldLeviForm_norm_sq_sub_apply_self hi v, hv, norm_zero, sq, zero_mul] at hp
    exact lt_irrefl 0 hp
  · intro hinj v hv
    rw [re_manifoldLeviForm_norm_sq_sub_apply_self hi]
    exact sq_pos_of_pos (norm_pos_iff.mpr ((map_ne_zero_iff _ hinj).2 hv))

/-- Squared distance along a complex `C²` map is real `C²`. -/
private theorem contMDiffAt_norm_sq_sub (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 (fun y ↦ ‖i y - a‖ ^ 2) x :=
  (contDiff_norm_sq ℂ).contDiffAt.contMDiffAt.comp x
    ((hi.restrictScalars ℝ).sub contMDiffAt_const)

/-- The sum of the real Hessian on a complex tangent vector and its rotation by `I`
is four times the squared norm of the tangent map. The Hessian here is computed in the
preferred chart; at a critical point it is intrinsic. -/
theorem criticalHessian_norm_sq_sub_add_I_smul
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v : E) :
    criticalHessian 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x v v +
        criticalHessian 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x (I • v) (I • v) =
      4 * ‖mvfderiv 𝓘(ℂ, E) i x v‖ ^ 2 := by
  have h := re_manifoldLeviForm_norm_sq_sub_apply_self (a := a) hi v
  rw [re_manifoldLeviForm_apply] at h
  linarith

/-- At a critical point, the squared-distance Hessian identity can be computed in
any real `C²` chart, including charts which are not holomorphic. The two tangent
vectors in that chart are transported by its actual real manifold derivative. -/
theorem hessianQuadraticForm_norm_sq_sub_add_I_smul_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 2 M) (hx : x ∈ e.source)
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x)
    (hcrit : mvfderiv 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = 0) (v : E) :
    hessianQuadraticForm ((fun y ↦ ‖i y - a‖ ^ 2) ∘ e.symm) (e x)
        (mvfderiv 𝓘(ℝ, E) e x v) +
      hessianQuadraticForm ((fun y ↦ ‖i y - a‖ ^ 2) ∘ e.symm) (e x)
        (mvfderiv 𝓘(ℝ, E) e x (I • v)) =
      4 * ‖mvfderiv 𝓘(ℂ, E) i x v‖ ^ 2 := by
  have h := congrArg Complex.re (manifoldLeviForm_apply_self_of_mem_maximalAtlas he hx
    (contMDiffAt_norm_sq_sub hi) hcrit v)
  rw [re_manifoldLeviForm_norm_sq_sub_apply_self hi, Complex.ofReal_re] at h
  -- The chart derivative is read in the model space using the vector-valued API.
  rw [mvfderiv_apply_eq_mfderiv_apply e x v, mvfderiv_apply_eq_mfderiv_apply e x (I • v)]
  linarith

/-- At a critical point of squared distance along a holomorphic immersion, the real
Morse index is at most the complex dimension of the source. -/
theorem manifoldMorseIndex_norm_sq_sub_le [FiniteDimensional ℂ E]
    [IsManifold 𝓘(ℂ, E) 2 M]
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x)
    (hinj : Injective (mvfderiv 𝓘(ℂ, E) i x))
    (hcrit : mvfderiv 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = 0) :
    manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x ≤ finrank ℂ E := by
  have hpos := (isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_iff (a := a) hi).2 hinj
  exact hpos.manifoldMorseIndex_le (contMDiffAt_norm_sq_sub hi) hcrit

end TauCeti
