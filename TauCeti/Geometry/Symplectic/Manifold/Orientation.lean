/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Orientation.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Orientation

import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Normed.Module.Alternating.Tame
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Symplectic.ExistsCompatible

/-!
# The symplectic orientation of a symplectic manifold

A fiberwise nondegenerate smooth two-form `σ` on a manifold `M` makes each tangent space a
symplectic vector space, which carries its symplectic orientation
(`TauCeti.SymplecticForm.orientation`, the orientation of its Darboux bases). These tangent
orientations form an orientation of `M`, the **symplectic orientation**
`TauCeti.SmoothTwoForm.IsNondegenerate.orientation`. Classically it is the orientation in which the
volume form `σⁿ` is positive. Closedness of `σ` plays no role, so the construction applies to any
almost symplectic manifold, and in particular to every symplectic manifold.

The tangent orientations are locally constant because the linear symplectic orientation is locally
constant in the form. Read in a trivialization of the tangent bundle near `b`, the forms `σ_x` are
symplectic forms on the model space depending continuously on `x`. An almost complex structure `J`
tamed by `σ_b` is still tamed by `σ_x` for `x` near `b`, because taming a fixed `J` is an open
condition on alternating two-forms (`ContinuousAlternatingMap.isOpen_setOf_forall_ne_zero_pos`).
Symplectic forms taming a common almost complex structure have the same orientation
(`TauCeti.SymplecticForm.Tames.orientation_eq`).

A smooth map between manifolds of the same dimension pulling one nondegenerate form back to
another preserves their symplectic orientations
(`TauCeti.SmoothTwoForm.IsNondegenerate.isOrientationPreservingAt_orientation`): its differential
is injective, because the pulled back form is nondegenerate, and hence invertible. In particular
symplectomorphisms, and local diffeomorphisms pulling one form back to the other, preserve the
symplectic orientation.

The symplectic orientation of a product form `σ ⊕ τ` on `M × N` is the product orientation of the
symplectic orientations of `σ` and `τ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.orientation_prod`), and the symplectic orientation of a
constant symplectic form on a vector space is its constant linear symplectic orientation
(`TauCeti.SymplecticForm.orientation_constSmooth`).

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.orientation`: the symplectic orientation of a manifold
  with a fiberwise nondegenerate two-form.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.orientationAt_orientation`: its tangent orientation at
  `x` is the symplectic orientation of the tangent space at `x`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isOrientationPreservingAt_orientation`: smooth maps
  between manifolds of the same dimension pulling one nondegenerate form back to another preserve
  the symplectic orientations.
* `TauCeti.SmoothTwoForm.IsNondegenerate.orientation_prod`: the symplectic orientation of a
  product form is the product of the symplectic orientations.
* `TauCeti.SymplecticForm.orientation_constSmooth`: the symplectic orientation of a constant
  symplectic form is constant.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 2.1 and 3.1 (the symplectic volume form and the orientation of a symplectic manifold).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.1 and Homework 1.
-/

public section

noncomputable section

open Bundle Filter Module
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {k : ℕ}

namespace IsNondegenerate

variable (hσ : σ.IsNondegenerate) (hk : finrank ℝ E = k)

omit [FiniteDimensional ℝ E] in
/-- Read in the preferred trivialization of the tangent bundle at `b`, the tangent symplectic form
at `x` is the coordinate expression of `σ` in the chart at `b`. -/
private theorem transport_symplecticFormAt_apply {b x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) b).baseSet) (u v : E) :
    (hσ.symplecticFormAt x).transport
        ((trivializationAt E (TangentSpace I) b).linearEquivAt ℝ x hx) u v =
      RoughForm.inChartAt (I := I) σ.1 b (extChartAt I b x) ![u, v] := by
  have hx' : x ∈ (chartAt H b).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  rw [SymplecticForm.transport_apply, symplecticFormAt_apply, SmoothBundleForm.eval₂_apply,
    RoughForm.inChartAt_apply,
    (extChartAt I b).left_inv (by simpa only [extChartAt_source] using hx'),
    ← TangentBundle.symmL_trivializationAt hx']
  congr 1
  ext i
  fin_cases i <;> simp only [Trivialization.linearEquivAt_symm_apply] <;>
    exact (Trivialization.symmL_apply (R := ℝ) _ hx _).symm

/-- The tangent symplectic orientations are locally constant in the preferred trivializations of
the tangent bundle. -/
private theorem eventually_mapOrientation_orientation_eq (b : M) :
    ∀ᶠ x in 𝓝 b, ∀ hx : x ∈ (trivializationAt E (TangentSpace I) b).baseSet,
      (trivializationAt E (TangentSpace I) b).mapOrientation (Fin k) hx
          ((hσ.symplecticFormAt x).orientation hk) =
        (trivializationAt E (TangentSpace I) b).mapOrientation (Fin k)
          (FiberBundle.mem_baseSet_trivializationAt' b)
          ((hσ.symplecticFormAt b).orientation hk) := by
  set e := trivializationAt E (TangentSpace I) b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  -- The tangent symplectic forms, transported to the model space `E`.
  set ωE : ∀ x, x ∈ e.baseSet → SymplecticForm E := fun x hx ↦
    (hσ.symplecticFormAt x).transport (e.linearEquivAt ℝ x hx)
  have hmap (x : M) (hx : x ∈ e.baseSet) :
      e.mapOrientation (Fin k) hx ((hσ.symplecticFormAt x).orientation hk) =
        (ωE x hx).orientation hk := by
    rw [Trivialization.mapOrientation_apply]
    exact (SymplecticForm.isSymplectomorphism_iff_transport_eq.2 rfl).map_orientation hk
  -- An almost complex structure on `E` tamed by the form at `b` is tamed nearby.
  obtain ⟨J, hJ⟩ := (ωE b hb).exists_tames
  set g : M → E [⋀^Fin 2]→L[ℝ] ℝ := fun x ↦ RoughForm.inChartAt (I := I) σ.1 b (extChartAt I b x)
  have hgc : ContinuousAt g b :=
    (((SmoothForm.isSmoothForm σ).continuousOn_inChartAt b).comp (continuousOn_extChartAt b)
      (extChartAt I b).mapsTo).continuousAt (extChartAt_source_mem_nhds b)
  have hpos := hgc.eventually_mem <| (ContinuousAlternatingMap.isOpen_setOf_forall_ne_zero_pos
    (LinearMap.toContinuousLinearMap J.toLinearMap)).mem_nhds fun u hu ↦ by
      rw [LinearMap.coe_toContinuousLinearMap', ← transport_symplecticFormAt_apply hσ hb]
      exact hJ u hu
  filter_upwards [hpos, e.open_baseSet.mem_nhds hb] with x hx hxe hxe'
  rw [hmap, hmap]
  refine SymplecticForm.Tames.orientation_eq (fun u hu ↦ ?_) hJ hk
  have := hx u hu
  rwa [LinearMap.coe_toContinuousLinearMap', ← transport_symplecticFormAt_apply hσ hxe'] at this

/-- The **symplectic orientation** of a manifold `M` carrying a fiberwise nondegenerate smooth
two-form `σ`, for instance a symplectic form: at each point it is the symplectic orientation of the
tangent space, in which the Darboux bases `(q₁, p₁, …, qₙ, pₙ)` of `σ_x` are positive. -/
def orientation : Manifold.Orientation I M (Fin k) :=
  Manifold.Orientation.ofVectorBundleOrientation (Module.finBasisOfFinrankEq ℝ E hk).orientation
    ((Fintype.card_fin k).trans hk.symm)
    ⟨fun x ↦ (hσ.symplecticFormAt x).orientation hk,
      hσ.eventually_mapOrientation_orientation_eq hk⟩

/-- The tangent orientation of the symplectic orientation at `x` is the symplectic orientation of
the tangent space at `x`. -/
@[simp]
theorem orientationAt_orientation (x : M) :
    (hσ.orientation hk).orientationAt x = (hσ.symplecticFormAt x).orientation hk := by
  rw [orientation, Manifold.Orientation.orientationAt_ofVectorBundleOrientation,
    VectorBundleOrientation.coe_mk]

section Transport

variable {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] {σ₂ : SmoothTwoForm I₂ M₂}

/-- **Symplectic maps preserve the symplectic orientation.** A smooth map `f` between manifolds of
the same dimension which pulls a nondegenerate two-form `σ₂` back to `σ` preserves the symplectic
orientations at every point. This applies to symplectomorphisms and to local diffeomorphisms such
as covering maps; no global injectivity of `f` is needed. -/
theorem isOrientationPreservingAt_orientation (hσ₂ : σ₂.IsNondegenerate)
    (hk₂ : finrank ℝ E₂ = k) {f : M → M₂} (hf : ContMDiff I I₂ ∞ f)
    (hfσ : SmoothForm.mpullback f hf σ₂ = σ) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (hσ.orientation hk) (hσ₂.orientation hk₂) f
      x := by
  have hD (v w : TangentSpace I x) : hσ₂.symplecticFormAt (f x) (mfderiv I I₂ f x v)
      (mfderiv I I₂ f x w) = hσ.symplecticFormAt x v w := by
    rw [symplecticFormAt_apply, symplecticFormAt_apply, ← hfσ, SmoothForm.eval₂_mpullback]
  -- The differential is injective since it pulls the nondegenerate `σ₂` back to `σ`, and the two
  -- tangent spaces have the same dimension, so it is invertible.
  have hinj : Function.Injective (mfderiv I I₂ f x) :=
    (injective_iff_map_eq_zero _).2 fun v hv ↦ (hσ.symplecticFormAt x).separatingLeft v
      fun w ↦ (hD v w).symm.trans (by simp [hv])
  let e := (LinearEquiv.ofInjectiveOfFinrankEq (mfderiv I I₂ f x).toLinearMap hinj
    (hk.trans hk₂.symm)).toContinuousLinearEquiv
  rw [Manifold.Orientation.isOrientationPreservingAt_iff]
  refine ⟨e, rfl, ?_⟩
  rw [orientationAt_orientation, orientationAt_orientation]
  exact ((SymplecticForm.isSymplectomorphism_iff (e := e.toLinearEquiv)).2 hD).map_orientation hk

end Transport

section Prod

variable {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] {τ : SmoothTwoForm J N} {m n : ℕ}

/-- **The symplectic orientation of a product.** The symplectic orientation of the product form
`σ ⊕ τ` on `M × N` is the product of the symplectic orientations of `σ` and `τ`, with the tangent
directions of `M` first. -/
theorem orientation_prod (hτ : τ.IsNondegenerate) (hm : finrank ℝ E = m) (hn : finrank ℝ F = n) :
    (hσ.prod hτ).orientation (by rw [Module.finrank_prod, hm, hn]) =
      (hσ.orientation hm).prod (hτ.orientation hn) := by
  ext x
  rw [Manifold.Orientation.orientationAt_prod, orientationAt_orientation,
    orientationAt_orientation, orientationAt_orientation]
  -- The identification `T_x (M × N) = T_x₁ M × T_x₂ N` is the identity of `E × F`, and it
  -- carries the tangent form of the product to the linear direct sum of the tangent forms.
  have hid : (Manifold.tangentSpaceProdEquiv (I := I) (J := J) x).toLinearEquiv =
      LinearEquiv.refl ℝ (E × F) :=
    LinearEquiv.ext (Manifold.tangentSpaceProdEquiv_apply x)
  have h := (SymplecticForm.isSymplectomorphism_iff_transport_eq.2
    (hσ.symplecticFormAt_prod hτ x)).map_orientation
      (by rw [Module.finrank_prod, hm, hn] : finrank ℝ (E × F) = m + n)
  rw [hid, SymplecticForm.orientation_prod (hσ.symplecticFormAt x.1) (hτ.symplecticFormAt x.2) hm
    hn] at h
  -- Both tangent spaces are the model space `E × F`, so mapping by its identity changes nothing.
  exact (DFunLike.congr_fun (Orientation.map_refl (R := ℝ) (M := E × F) (Fin (m + n))) _).symm.trans
    h

end Prod

end IsNondegenerate

end SmoothTwoForm

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {k : ℕ}

/-- The symplectic orientation of a constant symplectic form on a vector space `V` is the constant
orientation given at every point by the linear symplectic orientation of the form. -/
@[simp]
theorem orientation_constSmooth (omegaForm : SymplecticForm V) (hk : finrank ℝ V = k) :
    (isNondegenerate_constSmooth omegaForm).orientation hk =
      Manifold.Orientation.model (omegaForm.orientation hk) (by rw [Fintype.card_fin, hk]) := by
  ext x
  rw [SmoothTwoForm.IsNondegenerate.orientationAt_orientation,
    isNondegenerate_constSmooth_symplecticFormAt, Manifold.Orientation.orientationAt_model]
  -- The two sides differ only in reading `V` as its own tangent space at `x`.
  rfl

end SymplecticForm

end TauCeti
