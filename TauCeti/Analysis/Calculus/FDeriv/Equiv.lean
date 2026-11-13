/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Sets.Opens

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.DiscreteSubset

/-!
# Derivatives under local and linear equivalences

Mathlib's `OpenPartialHomeomorph.hasFDerivAt_symm` computes the derivative of the inverse from an
invertible derivative of the map. Without assuming that invertibility, this file records that when
both the map and its inverse are differentiable at corresponding points, their derivatives compose
to the identity. It does so for open partial homeomorphisms, and for a map `Φ` differentiable on an
open set `U` and mapping it into an open set `V`, with an inverse `Ψ` differentiable on `V`
(`Φ ∘ Ψ = id` on `V` and `Ψ ∘ Φ = id` on `U`).

## Main results

* `OpenPartialHomeomorph.fderiv_symm_comp_fderiv`: the derivative of the inverse is a left inverse
  of the derivative.
* `OpenPartialHomeomorph.fderiv_comp_fderiv_symm`: the derivative of the inverse is a right
  inverse of the derivative.
* `OpenPartialHomeomorph.fderiv_symm_apply_fderiv_apply`,
  `OpenPartialHomeomorph.fderiv_apply_fderiv_symm_apply`: the same identities evaluated at a
  vector.
* `OpenPartialHomeomorph.fderiv_symm_comp_fderiv_of_mem_source`,
  `OpenPartialHomeomorph.fderiv_comp_fderiv_symm_of_mem_source` and their evaluated forms
  `OpenPartialHomeomorph.fderiv_symm_apply_fderiv_apply_of_mem_source`,
  `OpenPartialHomeomorph.fderiv_apply_fderiv_symm_apply_of_mem_source`: the identities at a point
  `p` of the source and its image `e p`.
* `OpenPartialHomeomorph.isInvertible_fderiv`, `OpenPartialHomeomorph.inverse_fderiv`: hence the
  derivative at such a point is invertible, with inverse the derivative of `e.symm` at `e p`.
* `TauCeti.fderiv_comp_fderiv_eq_id_of_invOn`: `DΦ(y) ∘ DΨ(Φ y) = id`.
* `ContinuousLinearEquiv.image_vanishingFDeriv_comp`: precomposition by a continuous linear
  equivalence preserves the image of the vanishing-derivative locus.

Precomposition by a continuous linear equivalence preserves the image of the vanishing-derivative
locus, with no differentiability premise. This follows the totalized derivative calculation in
[KLS](https://github.com/human-ai-mathematics/kls-lean), commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/Sard/Basic.lean`.

A point where a map has an antilipschitz derivative, such as an invertible derivative between
finite-dimensional spaces, is isolated in its fibre (`HasFDerivAt.eventually_ne`). Hence a compact
fibre consisting of such points is finite (`IsCompact.finite_of_hasFDerivAt`); this is the
finiteness of the preimage of a regular value under a proper map. The same holds for a compact
part `s ∩ f⁻¹(y)` of a fibre (`IsCompact.finite_inter_preimage_of_hasFDerivAt`), and so for a
compact fibre of a map `g : s → F` agreeing on `s` with `f`
(`IsCompact.finite_of_hasFDerivAt_subtype`), as for a map defined on an open subset `s`. In
particular a compact set of fixed points `x` of `g : s → E` at which `g` agrees with a map `φ`
having a derivative with `det (1 - Dφ(x)) ≠ 0` is finite
(`IsCompact.finite_setOf_apply_eq_self_of_hasFDerivAt`).
-/

public section

open Filter Set TopologicalSpace
open scoped Topology

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of the inverse of an open partial homeomorphism at a point of its target is a
left inverse of the derivative at the corresponding point of its source. -/
theorem fderiv_symm_comp_fderiv (e : OpenPartialHomeomorph E F) {p : F} (hp : p ∈ e.target)
    (hd : DifferentiableAt 𝕜 e (e.symm p)) (hds : DifferentiableAt 𝕜 e.symm p) :
    (fderiv 𝕜 e.symm p).comp (fderiv 𝕜 e (e.symm p)) = ContinuousLinearMap.id 𝕜 E := by
  have hds' : HasFDerivAt e.symm (fderiv 𝕜 e.symm p) (e (e.symm p)) := by
    rw [e.right_inv hp]
    exact hds.hasFDerivAt
  refine (hds'.comp _ hd.hasFDerivAt).unique ((hasFDerivAt_id _).congr_of_eventuallyEq ?_)
  exact eventually_of_mem (e.open_source.mem_nhds (e.map_target hp)) fun r hr ↦ e.left_inv hr

/-- The derivative of the inverse of an open partial homeomorphism at a point of its target is a
right inverse of the derivative at the corresponding point of its source. -/
theorem fderiv_comp_fderiv_symm (e : OpenPartialHomeomorph E F) {p : F} (hp : p ∈ e.target)
    (hd : DifferentiableAt 𝕜 e (e.symm p)) (hds : DifferentiableAt 𝕜 e.symm p) :
    (fderiv 𝕜 e (e.symm p)).comp (fderiv 𝕜 e.symm p) = ContinuousLinearMap.id 𝕜 F :=
  (hd.hasFDerivAt.comp p hds.hasFDerivAt).unique
    ((hasFDerivAt_id p).congr_of_eventuallyEq
      (eventually_of_mem (e.open_target.mem_nhds hp) fun _ hr ↦ e.right_inv hr))

/-- Pointwise form of `OpenPartialHomeomorph.fderiv_symm_comp_fderiv`. -/
theorem fderiv_symm_apply_fderiv_apply (e : OpenPartialHomeomorph E F) {p : F}
    (hp : p ∈ e.target) (hd : DifferentiableAt 𝕜 e (e.symm p))
    (hds : DifferentiableAt 𝕜 e.symm p) (v : E) :
    fderiv 𝕜 e.symm p (fderiv 𝕜 e (e.symm p) v) = v := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    DFunLike.congr_fun (e.fderiv_symm_comp_fderiv hp hd hds) v

/-- Pointwise form of `OpenPartialHomeomorph.fderiv_comp_fderiv_symm`. -/
theorem fderiv_apply_fderiv_symm_apply (e : OpenPartialHomeomorph E F) {p : F}
    (hp : p ∈ e.target) (hd : DifferentiableAt 𝕜 e (e.symm p))
    (hds : DifferentiableAt 𝕜 e.symm p) (w : F) :
    fderiv 𝕜 e (e.symm p) (fderiv 𝕜 e.symm p w) = w := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    DFunLike.congr_fun (e.fderiv_comp_fderiv_symm hp hd hds) w

/-- Source-point form of `OpenPartialHomeomorph.fderiv_symm_comp_fderiv`: for `p` in the source,
`De⁻¹_{e p} ∘ De_p = id`. -/
theorem fderiv_symm_comp_fderiv_of_mem_source (e : OpenPartialHomeomorph E F) {p : E}
    (hp : p ∈ e.source) (hd : DifferentiableAt 𝕜 e p) (hds : DifferentiableAt 𝕜 e.symm (e p)) :
    (fderiv 𝕜 e.symm (e p)).comp (fderiv 𝕜 e p) = ContinuousLinearMap.id 𝕜 E := by
  have h := e.fderiv_symm_comp_fderiv (e.map_source hp) (by rwa [e.left_inv hp]) hds
  rwa [e.left_inv hp] at h

/-- Source-point form of `OpenPartialHomeomorph.fderiv_comp_fderiv_symm`: for `p` in the source,
`De_p ∘ De⁻¹_{e p} = id`. -/
theorem fderiv_comp_fderiv_symm_of_mem_source (e : OpenPartialHomeomorph E F) {p : E}
    (hp : p ∈ e.source) (hd : DifferentiableAt 𝕜 e p) (hds : DifferentiableAt 𝕜 e.symm (e p)) :
    (fderiv 𝕜 e p).comp (fderiv 𝕜 e.symm (e p)) = ContinuousLinearMap.id 𝕜 F := by
  have h := e.fderiv_comp_fderiv_symm (e.map_source hp) (by rwa [e.left_inv hp]) hds
  rwa [e.left_inv hp] at h

/-- Pointwise form of `OpenPartialHomeomorph.fderiv_symm_comp_fderiv_of_mem_source`: for `p` in
the source, `De⁻¹_{e p} (De_p v) = v`. -/
theorem fderiv_symm_apply_fderiv_apply_of_mem_source (e : OpenPartialHomeomorph E F) {p : E}
    (hp : p ∈ e.source) (hd : DifferentiableAt 𝕜 e p) (hds : DifferentiableAt 𝕜 e.symm (e p))
    (v : E) : fderiv 𝕜 e.symm (e p) (fderiv 𝕜 e p v) = v := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    DFunLike.congr_fun (e.fderiv_symm_comp_fderiv_of_mem_source hp hd hds) v

/-- Pointwise form of `OpenPartialHomeomorph.fderiv_comp_fderiv_symm_of_mem_source`: for `p` in
the source, `De_p (De⁻¹_{e p} w) = w`. -/
theorem fderiv_apply_fderiv_symm_apply_of_mem_source (e : OpenPartialHomeomorph E F) {p : E}
    (hp : p ∈ e.source) (hd : DifferentiableAt 𝕜 e p) (hds : DifferentiableAt 𝕜 e.symm (e p))
    (w : F) : fderiv 𝕜 e p (fderiv 𝕜 e.symm (e p) w) = w := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    DFunLike.congr_fun (e.fderiv_comp_fderiv_symm_of_mem_source hp hd hds) w

/-- An open partial homeomorphism which is differentiable at a point of its source, and whose
inverse is differentiable at the image point, has an invertible derivative there. -/
theorem isInvertible_fderiv (e : OpenPartialHomeomorph E F) {y : E} (hy : y ∈ e.source)
    (he : DifferentiableAt 𝕜 e y) (hes : DifferentiableAt 𝕜 e.symm (e y)) :
    (fderiv 𝕜 e y).IsInvertible :=
  .of_inverse (e.fderiv_comp_fderiv_symm_of_mem_source hy he hes)
    (e.fderiv_symm_comp_fderiv_of_mem_source hy he hes)

/-- Under the same hypotheses, the inverse of the derivative at a point of the source is the
derivative of the inverse at the image point. -/
theorem inverse_fderiv (e : OpenPartialHomeomorph E F) {y : E} (hy : y ∈ e.source)
    (he : DifferentiableAt 𝕜 e y) (hes : DifferentiableAt 𝕜 e.symm (e y)) :
    (fderiv 𝕜 e y).inverse = fderiv 𝕜 e.symm (e y) :=
  ContinuousLinearMap.inverse_eq (e.fderiv_comp_fderiv_symm_of_mem_source hy he hes)
    (e.fderiv_symm_comp_fderiv_of_mem_source hy he hes)

end OpenPartialHomeomorph

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {U : Opens E} {V : Opens F}
  {Φ : E → F} {Ψ : F → E}

/-- **The derivative of the inverse.** If `Φ` is differentiable on `U` and maps it into `V`, and
`Ψ`, differentiable on `V`, is inverse to `Φ` (`Φ ∘ Ψ = id` on `V`, `Ψ ∘ Φ = id` on `U`), then
`DΦ(y) ∘ DΨ(Φ y) = id` at every `y ∈ U`. -/
theorem fderiv_comp_fderiv_eq_id_of_invOn (hΦ : DifferentiableOn 𝕜 Φ U) (hmaps : MapsTo Φ U V)
    (hΨ : DifferentiableOn 𝕜 Ψ V) (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U)
    {y : E} (hy : y ∈ (U : Set E)) :
    fderiv 𝕜 Φ y ∘L fderiv 𝕜 Ψ (Φ y) = ContinuousLinearMap.id 𝕜 F := by
  have hx : Φ y ∈ (V : Set F) := hmaps hy
  have hcomp : HasFDerivAt (Φ ∘ Ψ) (fderiv 𝕜 Φ y ∘L fderiv 𝕜 Ψ (Φ y)) (Φ y) := by
    have hΦd := ((hΦ y hy).differentiableAt (U.isOpen.mem_nhds hy)).hasFDerivAt
    rw [← hΨΦ hy] at hΦd
    have := hΦd.comp (Φ y) ((hΨ _ hx).differentiableAt (V.isOpen.mem_nhds hx)).hasFDerivAt
    rwa [hΨΦ hy] at this
  have hid : Φ ∘ Ψ =ᶠ[𝓝 (Φ y)] id :=
    Filter.eventually_of_mem (V.isOpen.mem_nhds hx) fun x hxV => hΦΨ hxV
  exact (hcomp.congr_of_eventuallyEq hid.symm).unique (hasFDerivAt_id (Φ y))

end TauCeti

/-- Precomposition by a continuous linear equivalence preserves the image of the locus where
the totalized Fréchet derivative vanishes. No differentiability hypothesis is needed. -/
theorem ContinuousLinearEquiv.image_vanishingFDeriv_comp {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (e : E ≃L[𝕜] F) (u : F → G) :
    u '' {x | fderiv 𝕜 u x = 0} = (u ∘ e) '' {y | fderiv 𝕜 (u ∘ e) y = 0} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm x, ?_, by simp⟩
    have hx0 : fderiv 𝕜 u x = 0 := hx
    simp only [Set.mem_ofPred_eq, e.comp_right_fderiv, e.apply_symm_apply, hx0,
      ContinuousLinearMap.zero_comp]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e y, ?_, rfl⟩
    ext v
    have hzero : fderiv 𝕜 (u ∘ e) y = 0 := hy
    rw [e.comp_right_fderiv] at hzero
    have := congrArg (fun L : E →L[𝕜] G ↦ L (e.symm v)) hzero
    simpa using this

/-- **A compact part of a fibre of regular points is finite.** If every point of `s ∩ f⁻¹(y)` is a
point where `f` has an antilipschitz derivative, for instance an invertible derivative between
spaces of the same finite dimension, then each of these points is isolated in the fibre, so
`s ∩ f⁻¹(y)` is finite as soon as it is compact. -/
theorem IsCompact.finite_inter_preimage_of_hasFDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : E → F} {f' : E → E →L[𝕜] F} {s : Set E} {y : F}
    (hK : IsCompact (s ∩ f ⁻¹' {y})) (hf : ∀ x ∈ s ∩ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hf' : ∀ x ∈ s ∩ f ⁻¹' {y}, ∃ C, AntilipschitzWith C (f' x)) : (s ∩ f ⁻¹' {y}).Finite :=
  hK.finite (isDiscrete_iff_nhdsNE.2 fun x hx ↦ inf_principal_eq_bot.2
    (((hf x hx).eventually_ne (hf' x hx)).mono fun _ hz hzK ↦ hz (hzK.2.trans hx.2.symm)))

/-- **A compact fibre of regular points is finite.** If every point of the fibre of `f` over `y`
is a point where `f` has an antilipschitz derivative, for instance an invertible derivative between
spaces of the same finite dimension, then each of these points is isolated in the fibre, so a
compact fibre is finite. -/
theorem IsCompact.finite_of_hasFDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {f' : E → E →L[𝕜] F} {y : F} (hK : IsCompact (f ⁻¹' {y}))
    (hf : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hf' : ∀ x ∈ f ⁻¹' {y}, ∃ C, AntilipschitzWith C (f' x)) : (f ⁻¹' {y}).Finite := by
  simpa using IsCompact.finite_inter_preimage_of_hasFDerivAt (s := univ) (by simpa using hK)
    (by simpa using hf) (by simpa using hf')

/-- **A compact fibre of regular points of a map on a subset is finite.** Let `g : s → F` agree on
`s` with `f : E → F`. If the fibre of `g` over `y` is compact and `f` has an antilipschitz
derivative at each of its points, for instance an invertible derivative between spaces of the same
finite dimension, then this fibre is finite. -/
theorem IsCompact.finite_of_hasFDerivAt_subtype {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {s : Set E} {g : s → F} {f : E → F} {f' : E → E →L[𝕜] F} {y : F}
    (hK : IsCompact (g ⁻¹' {y})) (hfg : ∀ z : s, f z = g z)
    (hf : ∀ x ∈ g ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hf' : ∀ x ∈ g ⁻¹' {y}, ∃ C, AntilipschitzWith C (f' x)) : (g ⁻¹' {y}).Finite := by
  -- Read in `E`, the fibre of `g` is the part `s ∩ f⁻¹(y)` of the fibre of `f`.
  have himage : Subtype.val '' (g ⁻¹' {y}) = s ∩ f ⁻¹' {y} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, (hfg z).trans hz⟩
    · rintro ⟨hws, hw⟩
      exact ⟨⟨w, hws⟩, (hfg ⟨w, hws⟩).symm.trans hw, rfl⟩
  have hmem : ∀ w (hw : w ∈ s ∩ f ⁻¹' {y}), (⟨w, hw.1⟩ : s) ∈ g ⁻¹' {y} :=
    fun w hw ↦ (hfg ⟨w, hw.1⟩).symm.trans hw.2
  refine Finite.of_finite_image ?_ Subtype.val_injective.injOn
  rw [himage]
  exact (himage ▸ hK.image continuous_subtype_val).finite_inter_preimage_of_hasFDerivAt
    (fun w hw ↦ hf _ (hmem w hw)) fun w hw ↦ hf' _ (hmem w hw)

/-- **A compact set of nondegenerate fixed points is finite.** Let `f : s → E` agree on `s` with
`φ : E → E`. If the fixed set of `f` is compact and at each fixed point `x` the map `φ` has a
derivative `φ' x` with `det (1 - φ' x) ≠ 0`, then the fixed set of `f` is finite. -/
theorem IsCompact.finite_setOf_apply_eq_self_of_hasFDerivAt {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {s : Set E} {f : s → E} {φ : E → E}
    {φ' : E → E →L[𝕜] E} (hc : IsCompact {x | f x = x}) (hφ : ∀ z : s, φ z = f z)
    (hd : ∀ x ∈ {x | f x = x}, HasFDerivAt φ (φ' x) x)
    (hdet : ∀ x ∈ {x | f x = x}, (ContinuousLinearMap.id 𝕜 E - φ' x).det ≠ 0) :
    {x | f x = x}.Finite := by
  -- The fixed points of `f` are the zeros of `x ↦ x - f x`, which agrees on `s` with
  -- `x ↦ x - φ x`, whose derivatives `1 - φ' x` are invertible there.
  have hfix : {x | f x = x} = (fun z : s ↦ (z : E) - f z) ⁻¹' {0} := by
    ext x
    exact eq_comm.trans sub_eq_zero.symm
  rw [hfix] at hc hd hdet ⊢
  exact hc.finite_of_hasFDerivAt_subtype (f := fun z ↦ z - φ z)
    (f' := fun x ↦ ContinuousLinearMap.id 𝕜 E - φ' x) (fun z ↦ by simp [hφ])
    (fun x hx ↦ (hasFDerivAt_id _).sub (hd x hx)) fun x hx ↦
      ⟨_, ((ContinuousLinearMap.id 𝕜 E - φ' x).toContinuousLinearEquivOfDetNeZero
        (hdet x hx)).antilipschitzWith⟩
