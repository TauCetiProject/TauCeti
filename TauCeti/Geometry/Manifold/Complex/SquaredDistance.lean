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
  have hnorm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ) 2 (fun z : F ↦ ‖z‖ ^ 2) (i x - a) :=
    (contDiff_norm_sq ℂ).contDiffAt.contMDiffAt
  have hsub := hi.sub (contMDiffAt_const (c := a))
  have h := manifoldLeviForm_comp_apply (g := fun y ↦ i y - a)
    (u := fun z : F ↦ ‖z‖ ^ 2) hnorm hsub v w
  simp only [manifoldLeviForm_def, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, comp_id, leviForm_norm_sq] at h
  -- The model-space Levi form takes vectors in the canonically identified tangent fibres.
  erw [innerₛₗ_apply_apply] at h
  erw [← mvfderiv_apply_eq_mfderiv_apply (fun y ↦ i y - a) x v,
    ← mvfderiv_apply_eq_mfderiv_apply (fun y ↦ i y - a) x w] at h
  have hd := mvfderiv_sub (hi.mdifferentiableAt (by norm_num))
    (mdifferentiableAt_const (I := 𝓘(ℂ, E)) (c := a) (x := x))
  simp only [mvfderiv_const, sub_zero] at hd
  simp only [Pi.sub_def] at hd
  rw [hd] at h
  simpa only [manifoldLeviForm_def, Function.comp_def] using h

/-- The Levi diagonal of squared distance is the squared norm of the complex tangent map. -/
theorem re_manifoldLeviForm_norm_sq_sub_apply_self
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v : E) :
    (manifoldLeviForm E (fun y ↦ ‖i y - a‖ ^ 2) x v v).re =
      ‖mvfderiv 𝓘(ℂ, E) i x v‖ ^ 2 := by
  rw [manifoldLeviForm_norm_sq_sub_apply hi, inner_self_eq_norm_sq_to_K]
  -- Evaluate the norm in the ambient space, through the vector-valued derivative.
  exact_mod_cast rfl

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
    apply (mvfderiv 𝓘(ℂ, E) i x).ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hne
    have hp := h v hne
    -- The kernel vector is in the tangent fibre, canonically the model of the Levi form.
    erw [re_manifoldLeviForm_norm_sq_sub_apply_self hi] at hp
    erw [hv] at hp
    simp only [norm_zero, sq, zero_mul, lt_self_iff_false] at hp
  · intro hinj v hv
    rw [re_manifoldLeviForm_norm_sq_sub_apply_self hi]
    exact sq_pos_of_pos (norm_pos_iff.mpr ((map_ne_zero_iff _ hinj).2 hv))

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
  have hnorm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ) 2 (fun z : F ↦ ‖z‖ ^ 2) (i x - a) :=
    (contDiff_norm_sq ℂ).contDiffAt.contMDiffAt
  have hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 (fun y ↦ ‖i y - a‖ ^ 2) x :=
    hnorm.comp x ((hi.restrictScalars ℝ).sub (contMDiffAt_const (c := a)))
  have h := congrArg Complex.re
    (manifoldLeviForm_apply_self_of_mem_maximalAtlas he hx hf hcrit v)
  rw [re_manifoldLeviForm_norm_sq_sub_apply_self hi] at h
  -- The chart derivative is read in the model space using the vector-valued API.
  erw [← mvfderiv_apply_eq_mfderiv_apply e x v,
    ← mvfderiv_apply_eq_mfderiv_apply e x (I • v)] at h
  simp only [Complex.ofReal_re] at h
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
  have hsub := (hi.restrictScalars ℝ).sub (contMDiffAt_const (c := a))
  have hnorm : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ) 2 (fun z : F ↦ ‖z‖ ^ 2) (i x - a) :=
    (contDiff_norm_sq ℂ).contDiffAt.contMDiffAt
  exact hpos.manifoldMorseIndex_le (hnorm.comp x hsub) hcrit

end TauCeti
