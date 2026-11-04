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
public import TauCeti.Geometry.Manifold.Morse.SquaredDistance
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Squared distance on complex manifolds

For a holomorphic map `i` from a complex manifold to a complex inner product space,
the Levi form of `x ↦ ‖i x - a‖²` is the pullback of the ambient Hermitian metric by
the actual complex manifold derivative of `i`. In particular, it is positive definite
at every immersion point, independently of the center `a`.

At a critical point the resulting intrinsic real Hessian identity bounds the real
Morse index by the complex dimension. Combining this index bound with Haar genericity of
squared-distance Morse functions along smooth immersions (`TauCeti.ae_isMorse_norm_sq_sub_comp`)
shows that for a smooth holomorphic immersion of a second-countable complex manifold into a
finite-dimensional complex inner product space and almost every center `a`, `y ↦ ‖i y - a‖²` is a
real Morse function whose critical points all have index at most `finrank ℂ E`
(`TauCeti.ae_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le`,
`TauCeti.exists_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le`).

Along the inclusion of an open subset, squared distance is strictly plurisubharmonic at every
point (`TauCeti.isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_subtypeVal`).

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.

The calculation uses `TauCeti.manifoldLeviForm_comp_apply` and
`TauCeti.leviForm_norm_sq`.
-/

public section

open Complex Function MeasureTheory Module TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] {i : M → F} {x : M} {a : F}

/-- The Levi form of squared distance along a holomorphic map is the pullback of the
ambient Hermitian metric. -/
@[simp]
theorem manifoldLeviForm_norm_sq_sub_comp_apply
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
theorem re_manifoldLeviForm_norm_sq_sub_comp_apply_self
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v : E) :
    (manifoldLeviForm E (fun y ↦ ‖i y - a‖ ^ 2) x v v).re =
      ‖mvfderiv 𝓘(ℂ, E) i x v‖ ^ 2 := by
  rw [manifoldLeviForm_norm_sq_sub_comp_apply hi, ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq _

/-- Squared distance along a holomorphic map is strictly plurisubharmonic exactly at
its immersion points. -/
@[simp]
theorem isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) :
    IsManifoldStrictlyPlurisubharmonicAt E (fun y ↦ ‖i y - a‖ ^ 2) x ↔
      Injective (mvfderiv 𝓘(ℂ, E) i x) := by
  rw [isManifoldStrictlyPlurisubharmonicAt_iff]
  constructor
  · intro h
    refine (injective_iff_map_eq_zero (mvfderiv 𝓘(ℂ, E) i x)).2 fun v hv ↦ ?_
    by_contra hne
    have hp := h v hne
    rw [re_manifoldLeviForm_norm_sq_sub_comp_apply_self hi v, hv, norm_zero, sq, zero_mul] at hp
    exact lt_irrefl 0 hp
  · intro hinj v hv
    rw [re_manifoldLeviForm_norm_sq_sub_comp_apply_self hi]
    exact sq_pos_of_pos (norm_pos_iff.mpr ((map_ne_zero_iff _ hinj).2 hv))

/-- Squared distance along a complex `C²` map is real `C²`. -/
theorem contMDiffAt_norm_sq_sub_comp (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 (fun y ↦ ‖i y - a‖ ^ 2) x := by
  have hiR : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 2 i x := by
    simpa using hi.restrictScalars ℝ
  exact (contDiff_norm_sq ℂ).contDiffAt.contMDiffAt.comp x (hiR.sub contMDiffAt_const)

/-- The sum of the real Hessian on a complex tangent vector and its rotation by `I`
is four times the squared norm of the tangent map. The Hessian here is computed in the
preferred chart; at a critical point it is intrinsic. -/
theorem criticalHessian_norm_sq_sub_comp_add_I_smul
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v : E) :
    criticalHessian 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x v v +
        criticalHessian 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x (I • v) (I • v) =
      4 * ‖mvfderiv 𝓘(ℂ, E) i x v‖ ^ 2 := by
  have h := re_manifoldLeviForm_norm_sq_sub_comp_apply_self (a := a) hi v
  rw [re_manifoldLeviForm_apply] at h
  linarith

/-- At a critical point, the squared-distance Hessian identity can be computed in
any real `C²` chart, including charts which are not holomorphic. The two tangent
vectors in that chart are transported by its actual real manifold derivative. -/
theorem hessianQuadraticForm_norm_sq_sub_comp_add_I_smul_of_mem_maximalAtlas
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
    (contMDiffAt_norm_sq_sub_comp hi) hcrit v)
  rw [re_manifoldLeviForm_norm_sq_sub_comp_apply_self hi, Complex.ofReal_re] at h
  -- The chart derivative is read in the model space using the vector-valued API.
  rw [mvfderiv_apply_eq_mfderiv_apply e x v, mvfderiv_apply_eq_mfderiv_apply e x (I • v)]
  linarith

/-- At a critical point of squared distance along a holomorphic immersion, the real
Morse index is at most the complex dimension of the source. -/
theorem manifoldMorseIndex_norm_sq_sub_comp_le [FiniteDimensional ℂ E]
    [IsManifold 𝓘(ℂ, E) 2 M]
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x)
    (hinj : Injective (mvfderiv 𝓘(ℂ, E) i x))
    (hcrit : mvfderiv 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x = 0) :
    manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x ≤ finrank ℂ E := by
  have hpos := (isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff (a := a) hi).2 hinj
  exact hpos.manifoldMorseIndex_le (contMDiffAt_norm_sq_sub_comp hi) hcrit

/-- Along the inclusion of an open subset of a complex inner product space, the squared distance
from any point is strictly plurisubharmonic at every point. -/
theorem isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_subtypeVal (U : Opens F) (a : F)
    (x : U) : IsManifoldStrictlyPlurisubharmonicAt F (fun y : U ↦ ‖(y : F) - a‖ ^ 2) x := by
  rw [isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff
    (contMDiff_subtype_val (I := 𝓘(ℂ, F)) x)]
  exact Manifold.injective_mvfderiv_subtype_val x

section Immersion

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [IsManifold 𝓘(ℂ, E) ∞ M]
  [SecondCountableTopology M]

/-- **Generic low-index squared-distance Morse functions on a holomorphically immersed manifold.**
For a smooth holomorphic immersion `i : M → F` of a second-countable complex manifold into a
finite-dimensional complex inner product space and almost every `a ∈ F` (with respect to any Haar
measure `μ`), `y ↦ ‖i y - a‖ ^ 2` is a real Morse function on `M` whose critical points all have
Morse index at most `finrank ℂ E`. -/
theorem ae_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) i x)) :
    ∀ᵐ a ∂μ, IsMorse 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) ∧
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2),
        manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x ≤ finrank ℂ E := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  have : IsManifold 𝓘(ℝ, E) ∞ M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)
  have : IsManifold 𝓘(ℝ, E) 2 M := .of_le (n := ∞) (by norm_cast)
  have : IsManifold 𝓘(ℂ, E) 2 M := .of_le (n := ∞) (by norm_cast)
  have hiR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ i := by simpa using hi.restrictScalars ℝ
  have hinjR (x : M) : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) i x) :=
    ((hi x).mdifferentiableAt (by simp)).injective_mfderiv_restrictScalars ℝ (hinj x)
  filter_upwards [ae_isMorse_norm_sq_sub_comp μ hiR hinjR] with a ha
  exact ⟨ha, fun x hx ↦ manifoldMorseIndex_norm_sq_sub_comp_le ((hi x).of_le (by norm_cast))
    (injective_mvfderiv_iff.2 (hinj x)) (mem_criticalPoints.1 hx)⟩

/-- **Existence of a low-index squared-distance Morse function on a holomorphically immersed
manifold.** -/
theorem exists_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le
    (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ i)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) i x)) :
    ∃ a : F, IsMorse 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) ∧
      ∀ x ∈ criticalPoints 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2),
        manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - a‖ ^ 2) x ≤ finrank ℂ E := by
  let _ : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  exact (ae_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le Measure.addHaar hi hinj).exists

end Immersion

end TauCeti
