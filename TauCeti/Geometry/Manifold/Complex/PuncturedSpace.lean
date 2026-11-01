/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.SquaredDistance
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Topology.Order.Sublevel

/-!
# Squared distance on a punctured complex space

Milnor's proof that a closed complex submanifold of `ℂᴺ` of complex dimension `n` has the
homotopy type of a CW complex of dimension at most `n` uses two properties of the squared
distance `ρ_a x = ‖x - a‖²` along the inclusion. It is strictly plurisubharmonic, so that its
critical points have Morse index at most `n`; this holds along every holomorphic immersion. And
it is proper, so that its sublevels are compact; this needs the inclusion to be closed.

The punctured space `ℂ² ∖ {0}`, with its ordinary inclusion into `ℂ²`, shows that closedness
cannot be dropped. It is an open subset of `ℂ²`, hence a complex manifold whose inclusion is a
holomorphic open embedding. Along it every `ρ_a` is strictly plurisubharmonic, and its only
possible critical point is the centre `a` itself. Nevertheless, for `r > ‖a‖²` the bounded
sublevel `{x ∈ ℂ² ∖ {0} | ρ_a x ≤ r}` accumulates at the missing origin and is not compact, and
`ρ_a` is not a proper map. The punctured space is homotopy equivalent to the unit sphere
(`TauCeti.complSingletonHomotopyEquivSphere`), here the three-sphere.

The results are stated for an arbitrary puncture of a complex inner product space, or of a real
normed space where complex structure plays no role. The first two hold on every open subset.

## Main results

* `TauCeti.isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_subtypeVal`: along the inclusion of
  an open subset, squared distance is strictly plurisubharmonic at every point.
* `TauCeti.mvfderiv_norm_sq_sub_subtypeVal_eq_zero_iff`: along the inclusion of an open subset,
  the only critical point of `ρ_a` is `a`.
* `TauCeti.not_isCompact_compl_singleton_inter_preimage_Iic`: the sublevel `{ρ_a ≤ r}` of the
  space punctured at `y` is not compact when `ρ_a y < r`.
* `TauCeti.not_isProperMap_norm_sq_sub_compl_singleton`: `ρ_a` is not proper on a punctured
  nonzero real normed space.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

open Set TopologicalSpace
open scoped Manifold

namespace TauCeti

section Open

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Along the inclusion of an open subset of a complex inner product space, the squared distance
from any point is strictly plurisubharmonic at every point. -/
theorem isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_subtypeVal (U : Opens F) (a : F)
    (x : U) : IsManifoldStrictlyPlurisubharmonicAt F (fun y : U ↦ ‖(y : F) - a‖ ^ 2) x := by
  rw [isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff
    (contMDiff_subtype_val (I := 𝓘(ℂ, F)) x)]
  intro v w h
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply,
    Manifold.mfderiv_subtype_val] at h
  exact (Manifold.tangentSpaceOpenEquiv x).injective h

/-- Along the inclusion of an open subset of a complex inner product space, the squared distance
from `a` has a critical point exactly at `a`. -/
theorem mvfderiv_norm_sq_sub_subtypeVal_eq_zero_iff (U : Opens F) (a : F) (x : U) :
    mvfderiv 𝓘(ℝ, F) (fun y : U ↦ ‖(y : F) - a‖ ^ 2) x = 0 ↔ (x : F) = a := by
  -- The real inner product `re ⟪·, ·⟫_ℂ` expresses the real derivative of the squared norm.
  let := InnerProductSpace.complexToReal (G := F)
  have hd : HasFDerivAt (fun v : F ↦ ‖v - a‖ ^ 2)
      (2 • (innerSL ℝ ((x : F) - a))) (x : F) :=
    ((hasFDerivAt_id (x : F)).sub_const a).norm_sq.congr_fderiv (by simp)
  have happ (v : F) : mvfderiv 𝓘(ℝ, F) (fun y : U ↦ ‖(y : F) - a‖ ^ 2) x v =
      2 * inner ℝ ((x : F) - a) v := by
    have hv : mvfderiv 𝓘(ℝ, F) (Subtype.val : U → F) x v = v :=
      (mvfderiv_apply_eq_mfderiv_apply (Subtype.val : U → F) x v).trans
        (by rw [Manifold.mfderiv_subtype_val]; exact Manifold.tangentSpaceOpenEquiv_apply x v)
    calc mvfderiv 𝓘(ℝ, F) (fun y : U ↦ ‖(y : F) - a‖ ^ 2) x v
        = fderiv ℝ (fun v : F ↦ ‖v - a‖ ^ 2) x (mvfderiv 𝓘(ℝ, F) (Subtype.val : U → F) x v) :=
          mvfderiv_comp_apply_of_differentiableAt hd.differentiableAt
            ((contMDiff_subtype_val (U := U) x).mdifferentiableAt one_ne_zero) v
      _ = 2 * inner ℝ ((x : F) - a) v := by
          rw [hv, hd.fderiv]
          simp [inner_sub_left]
  constructor
  · intro h
    have h0 := happ ((x : F) - a)
    rw [h, real_inner_self_eq_norm_sq] at h0
    have h1 : 2 * ‖(x : F) - a‖ ^ 2 = 0 := h0.symm
    simpa [sub_eq_zero] using h1
  · intro h
    -- Tangent vectors of the open subset are read as vectors of `F`.
    refine ContinuousLinearMap.ext fun v : F ↦ ?_
    rw [happ v, h, sub_self, inner_zero_left, mul_zero]
    rfl

end Open

section Punctured

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]

/-- In a nonzero real normed space punctured at `y`, the bounded sublevel `{ρ_a ≤ r}` of the
squared distance from `a` is not compact when `‖y - a‖² < r`: it accumulates at the puncture. -/
theorem not_isCompact_compl_singleton_inter_preimage_Iic {y a : F} {r : ℝ}
    (hr : ‖y - a‖ ^ 2 < r) :
    ¬IsCompact (({y}ᶜ : Set F) ∩ (fun v ↦ ‖v - a‖ ^ 2) ⁻¹' Iic r) :=
  not_isCompact_inter_preimage_Iic (by simp) (by simp)
    (by fun_prop) hr

/-- On a nonzero real normed space punctured at `y`, the squared distance from any point is not a
proper map. -/
theorem not_isProperMap_norm_sq_sub_compl_singleton (y a : F) :
    ¬IsProperMap fun x : ({y}ᶜ : Set F) ↦ ‖(x : F) - a‖ ^ 2 := by
  intro h
  refine not_isCompact_compl_singleton_inter_preimage_Iic (lt_add_one (‖y - a‖ ^ 2)) ?_
  have hK := (h.isCompact_preimage (isCompact_Icc (a := 0) (b := ‖y - a‖ ^ 2 + 1))).image
    continuous_subtype_val
  convert hK using 1
  ext v
  simp only [mem_inter_iff, mem_compl_iff, mem_preimage, mem_Iic, mem_image, mem_Icc,
    Subtype.exists, exists_and_right, exists_eq_right]
  exact ⟨fun ⟨hv, hle⟩ ↦ ⟨⟨hv, by positivity⟩, hle⟩, fun ⟨⟨hv, _⟩, hle⟩ ↦ ⟨hv, hle⟩⟩

end Punctured

/- The punctured plane `ℂ² ∖ {0}` with its ordinary inclusion into `ℂ²`: every squared distance is
strictly plurisubharmonic along the inclusion, yet its bounded sublevels reaching below the origin's
value are not compact. -/
example (a : EuclideanSpace ℂ (Fin 2)) {r : ℝ} (hr : ‖a‖ ^ 2 < r) :
    (∀ x : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℂ (Fin 2))),
      IsManifoldStrictlyPlurisubharmonicAt (EuclideanSpace ℂ (Fin 2))
        (fun y : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℂ (Fin 2))) ↦
          ‖(y : EuclideanSpace ℂ (Fin 2)) - a‖ ^ 2) x) ∧
    ¬IsCompact (({0}ᶜ : Set (EuclideanSpace ℂ (Fin 2))) ∩ (fun v ↦ ‖v - a‖ ^ 2) ⁻¹' Iic r) :=
  ⟨isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_subtypeVal _ a,
    not_isCompact_compl_singleton_inter_preimage_Iic (by simpa using hr)⟩

end TauCeti
