/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Relation
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Geometry.Manifold.Flow.Diffeomorph
import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# Lagrangian mechanics under changes of configuration coordinates

Let `h : M → N` be a diffeomorphism of configuration manifolds and `L : TN → 𝕜` a Lagrangian on
`N`. Reading `L` in the coordinates of `M` gives the Lagrangian `L ∘ Th` on `M`, where
`Th : TM → TN` is the tangent map of `h`. This file proves that every structure of Lagrangian
mechanics attached to `L ∘ Th` is the corresponding structure of `L` transported along the tangent
lift `Th` and the cotangent lift `T*h : T*M → T*N`, `(x, p) ↦ (h x, p ∘ (dh_x)⁻¹)`
(`Diffeomorph.cotangent`). So the Lagrangian and Hamiltonian descriptions of a mechanical system,
and in particular its equations of motion, do not depend on the configuration coordinates.

* **Legendre map.** `T*h ∘ F(L ∘ Th) = FL ∘ Th`
  (`TauCeti.cotangent_legendreMap_comp_tangentMap`). More generally, for any map `f : M → N` the
  covector `F(L ∘ Tf)(v)` is the pullback of `FL(Tf v)` along `df`
  (`TauCeti.legendreMap_comp_tangentMap_snd`), that is, the two Legendre transforms are related by
  the cotangent relation of `f` (`TauCeti.cotangentRel_legendreMap_comp_tangentMap`), provided `L`
  is differentiable along the fibre at `Tf v`. Both also hold with no differentiability of `L`
  when `df` is invertible at the base point of `v`
  (`TauCeti.legendreMap_comp_tangentMap_snd_of_isInvertible`,
  `TauCeti.cotangentRel_legendreMap_comp_tangentMap_of_isInvertible`).
* **Energy.** `E_(L ∘ Th) = E_L ∘ Th` (`TauCeti.lagrangianEnergy_comp_tangentMap`). For any map
  `f : M → N`, the energy of `L ∘ Tf` at `v` is that of `L` at `Tf v` when `L` is differentiable
  along the fibre at `Tf v` or `df` is invertible at the base point of `v`
  (`TauCeti.lagrangianEnergy_comp_tangentMap_apply`,
  `TauCeti.lagrangianEnergy_comp_tangentMap_apply_of_isInvertible`).
* **Fibre Hessian and regularity.** When `df` is invertible at the base point of `v`, the fibre
  Hessian of `L ∘ Tf` at `v` is that of `L` at `Tf v` composed with `df` in both arguments, and
  one is invertible exactly when the other is
  (`TauCeti.fiberHessian_comp_tangentMap_apply_of_isInvertible`,
  `TauCeti.isInvertible_fiberHessian_comp_tangentMap_iff_of_isInvertible`). So for a
  diffeomorphism `h`, `L ∘ Th` is regular exactly when `L` is
  (`TauCeti.isRegularLagrangian_comp_tangentMap_iff`), and hyperregular exactly when `L` is
  (`TauCeti.isHyperregularLagrangian_comp_tangentMap_iff`). The Hamiltonians then satisfy
  `H_(L ∘ Th) = H_L ∘ T*h` (`TauCeti.IsHyperregularLagrangian.hamiltonian_comp_tangentMap`).
* **Cartan forms.** For real smooth `L`, `θ_(L ∘ Th) = Th^* θ_L` and `ω_(L ∘ Th) = Th^* ω_L`
  (`TauCeti.cartanForm_comp_tangentMap`, `TauCeti.cartanTwoForm_comp_tangentMap`), because `T*h`
  preserves the Liouville form.
* **Equations of motion.** For a smooth regular real Lagrangian `L` on a finite-dimensional
  manifold `N` with boundaryless tangent bundle, the differential of `Th` carries the Lagrangian
  vector field `X_E` of `L ∘ Th`, the Hamiltonian vector field of the energy for the Cartan
  two-form, to that of `L` (`TauCeti.mfderiv_tangentMap_hamiltonianVectorField_cartanTwoForm`).
  Hence a curve `γ` in `TM` is an integral curve of `X_E` for `L ∘ Th` on a set of times exactly
  when `Th ∘ γ` is one for `L`
  (`TauCeti.isMIntegralCurveOn_tangentMap_comp_hamiltonianVectorField_cartanTwoForm_iff`,
  `TauCeti.isMIntegralCurve_tangentMap_comp_hamiltonianVectorField_cartanTwoForm_iff`).

The Legendre transform, energy and fibre Hessian statements are pointwise and allow any map
`f : M → N`; when `f` is not a diffeomorphism the Legendre transform of `L ∘ Tf` is a pullback of
that of `L`, not an image under a map of cotangent bundles. The global statements, about
regularity, the Hamiltonian, the Cartan forms and the equations of motion, are for
diffeomorphisms.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Sections 3.5 and 3.6.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 7.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

section Legendre

variable {𝕜 E H F H' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'} {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N] {n : WithTop ℕ∞}

/-- On the fibre through `x`, the Lagrangian `L ∘ Tf` is the restriction of `L` to the fibre
through `f x` precomposed with the differential of `f` at `x`. This holds by definition of
`tangentMap`, which sends the vector `w` at `x` to the vector `df_x w` at `f x`. -/
private theorem comp_tangentMap_mk' (f : M → N) (L : TangentBundle J N → 𝕜) (x : M) :
    (fun w : E ↦ (L ∘ tangentMap I J f) (TotalSpace.mk' E x w)) =
      (fun w : F ↦ L (TotalSpace.mk' F (f x) w)) ∘ mfderiv I J f x :=
  rfl

/-- **The Legendre map under a change of configuration.** If the Lagrangian `L` on `N` is
differentiable along the fibre at `Tf v`, then the Legendre transform of `L ∘ Tf` at `v` is the
pullback of the Legendre transform of `L` at `Tf v` along the differential of `f`. -/
theorem legendreMap_comp_tangentMap_snd (f : M → N) (L : TangentBundle J N → 𝕜)
    (v : TangentBundle I M)
    (hL : DifferentiableAt 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w))
      (mfderiv I J f v.proj v.2)) :
    (legendreMap (L ∘ tangentMap I J f) v).2 =
      (legendreMap L (tangentMap I J f v)).2 ∘L mfderiv I J f v.proj := by
  -- Read the differential and the velocity in the model spaces.
  let D : E →L[𝕜] F := mfderiv I J f v.proj
  let x : E := v.2
  have hL' : DifferentiableAt 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w)) (D x) := hL
  have hD : fderiv 𝕜 ((fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w)) ∘ D) x =
      fderiv 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w)) (D x) ∘L D := by
    rw [fderiv_comp x hL' D.differentiableAt, D.fderiv]
  rw [legendreMap_snd, legendreMap_snd, comp_tangentMap_mk']
  -- `Tf v` is the vector `df v` at `f v.proj` (`tangentMap_proj`, `tangentMap_snd`).
  exact hD

/-- **The Legendre map under a change of configuration with invertible differential.** If the
differential of `f` at the base point of `v` is invertible, then the Legendre transform of
`L ∘ Tf` at `v` is the pullback of the Legendre transform of `L` at `Tf v` along `df`, with no
differentiability assumption on `L`. -/
theorem legendreMap_comp_tangentMap_snd_of_isInvertible (f : M → N) (L : TangentBundle J N → 𝕜)
    (v : TangentBundle I M) (hf : (mfderiv I J f v.proj).IsInvertible) :
    (legendreMap (L ∘ tangentMap I J f) v).2 =
      (legendreMap L (tangentMap I J f v)).2 ∘L mfderiv I J f v.proj := by
  obtain ⟨A₀, hA₀⟩ := hf
  -- Read the differential in the model spaces.
  let A : E ≃L[𝕜] F := A₀
  have hA : (A : E →L[𝕜] F) = mfderiv I J f v.proj := hA₀
  have hD := A.comp_right_fderiv (f := fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w))
    (x := (v.2 : E))
  simp only [← ContinuousLinearEquiv.coe_coe, hA] at hD
  rw [legendreMap_snd, legendreMap_snd, comp_tangentMap_mk']
  -- `Tf v` is the vector `df v` at `f v.proj` (`tangentMap_proj`, `tangentMap_snd`).
  exact hD

/-- Legendre transforms whose covectors are related by the differential of `f` are related by
the cotangent relation of `f`. -/
private theorem cotangentRel_legendreMap_comp_tangentMap_of_snd (f : M → N)
    (L : TangentBundle J N → 𝕜) (v : TangentBundle I M)
    (hs : (legendreMap (L ∘ tangentMap I J f) v).2 =
      (legendreMap L (tangentMap I J f v)).2 ∘L mfderiv I J f v.proj) :
    CotangentBundle.cotangentRel I J f (legendreMap (L ∘ tangentMap I J f) v)
      (legendreMap L (tangentMap I J f v)) := by
  rw [legendreMap_def, legendreMap_def] at hs ⊢
  exact (CotangentBundle.cotangentRel_iff _ _ f _ _).2 ⟨rfl, hs⟩

/-- **The cotangent relation of Legendre transforms.** If `L` is differentiable along the fibre
at `Tf v`, the Legendre transforms of `L ∘ Tf` at `v` and of `L` at `Tf v` are related by the
cotangent relation of `f`. -/
theorem cotangentRel_legendreMap_comp_tangentMap (f : M → N) (L : TangentBundle J N → 𝕜)
    (v : TangentBundle I M)
    (hL : DifferentiableAt 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w))
      (mfderiv I J f v.proj v.2)) :
    CotangentBundle.cotangentRel I J f (legendreMap (L ∘ tangentMap I J f) v)
      (legendreMap L (tangentMap I J f v)) :=
  cotangentRel_legendreMap_comp_tangentMap_of_snd f L v
    (legendreMap_comp_tangentMap_snd f L v hL)

/-- **The cotangent relation of Legendre transforms, invertible differential.** If the
differential of `f` at the base point of `v` is invertible, the Legendre transforms of `L ∘ Tf`
at `v` and of `L` at `Tf v` are related by the cotangent relation of `f`, with no
differentiability assumption on `L`. -/
theorem cotangentRel_legendreMap_comp_tangentMap_of_isInvertible (f : M → N)
    (L : TangentBundle J N → 𝕜) (v : TangentBundle I M)
    (hf : (mfderiv I J f v.proj).IsInvertible) :
    CotangentBundle.cotangentRel I J f (legendreMap (L ∘ tangentMap I J f) v)
      (legendreMap L (tangentMap I J f v)) :=
  cotangentRel_legendreMap_comp_tangentMap_of_snd f L v
    (legendreMap_comp_tangentMap_snd_of_isInvertible f L v hf)

/-- The energy of `L ∘ Tf` at `v` is the energy of `L` at `Tf v` whenever the Legendre transforms
are related by the differential of `f`. -/
private theorem lagrangianEnergy_comp_tangentMap_apply_of_snd (f : M → N)
    (L : TangentBundle J N → 𝕜) (v : TangentBundle I M)
    (hs : (legendreMap (L ∘ tangentMap I J f) v).2 =
      (legendreMap L (tangentMap I J f v)).2 ∘L mfderiv I J f v.proj) :
    lagrangianEnergy (L ∘ tangentMap I J f) v = lagrangianEnergy L (tangentMap I J f v) := by
  rw [lagrangianEnergy_apply, lagrangianEnergy_apply]
  exact congrArg (· - L (tangentMap I J f v)) (DFunLike.congr_fun hs v.2)

/-- **The energy under a change of configuration.** If `L` is differentiable along the fibre at
`Tf v`, the energy of `L ∘ Tf` at `v` is the energy of `L` at `Tf v`. -/
theorem lagrangianEnergy_comp_tangentMap_apply (f : M → N) (L : TangentBundle J N → 𝕜)
    (v : TangentBundle I M)
    (hL : DifferentiableAt 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w))
      (mfderiv I J f v.proj v.2)) :
    lagrangianEnergy (L ∘ tangentMap I J f) v = lagrangianEnergy L (tangentMap I J f v) :=
  lagrangianEnergy_comp_tangentMap_apply_of_snd f L v (legendreMap_comp_tangentMap_snd f L v hL)

/-- **The energy under a change of configuration with invertible differential.** If the
differential of `f` at the base point of `v` is invertible, the energy of `L ∘ Tf` at `v` is the
energy of `L` at `Tf v`, with no differentiability assumption on `L`. -/
theorem lagrangianEnergy_comp_tangentMap_apply_of_isInvertible (f : M → N)
    (L : TangentBundle J N → 𝕜) (v : TangentBundle I M)
    (hf : (mfderiv I J f v.proj).IsInvertible) :
    lagrangianEnergy (L ∘ tangentMap I J f) v = lagrangianEnergy L (tangentMap I J f v) :=
  lagrangianEnergy_comp_tangentMap_apply_of_snd f L v
    (legendreMap_comp_tangentMap_snd_of_isInvertible f L v hf)

/-- **The energy is natural under diffeomorphisms.** For a `C^n` diffeomorphism `h` with
`n ≠ 0`, the energy of `L ∘ Th` is the energy of `L` composed with `Th`. -/
@[simp]
theorem lagrangianEnergy_comp_tangentMap (L : TangentBundle J N → 𝕜) (h : M ≃ₘ^n⟮I, J⟯ N)
    (hn : n ≠ 0) :
    lagrangianEnergy (L ∘ tangentMap I J h) = lagrangianEnergy L ∘ tangentMap I J h :=
  funext fun v ↦ lagrangianEnergy_comp_tangentMap_apply_of_isInvertible h L v
    (h.isInvertible_mfderiv hn)

/-- **The fibre Hessian under a change of configuration.** If the differential of `f` at the base
point of `v` is invertible, the fibre Hessian of `L ∘ Tf` at `v` evaluates `w₁, w₂` as the fibre
Hessian of `L` at `Tf v` evaluates `df w₁, df w₂`. -/
theorem fiberHessian_comp_tangentMap_apply_of_isInvertible (f : M → N)
    (L : TangentBundle J N → 𝕜) (v : TangentBundle I M)
    (hf : (mfderiv I J f v.proj).IsInvertible) (w₁ w₂ : TangentSpace I v.proj) :
    fiberHessian (L ∘ tangentMap I J f) v w₁ w₂ =
      fiberHessian L (tangentMap I J f v) (mfderiv I J f v.proj w₁)
        (mfderiv I J f v.proj w₂) := by
  obtain ⟨A₀, hA₀⟩ := hf
  -- Read the differential in the model spaces.
  let A : E ≃L[𝕜] F := A₀
  have hA : (A : E →L[𝕜] F) = mfderiv I J f v.proj := hA₀
  have hH := A.fderiv_fderiv_comp_right_apply_apply
    (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w)) (v.2 : E) (w₁ : E) (w₂ : E)
  simp only [← ContinuousLinearEquiv.coe_coe, hA] at hH
  rw [fiberHessian_def, fiberHessian_def, comp_tangentMap_mk']
  -- `Tf v` is the vector `df v` at `f v.proj` (`tangentMap_proj`, `tangentMap_snd`).
  exact hH

/-- **The fibre Hessian is natural under diffeomorphisms.** For a `C^n` diffeomorphism `h` with
`n ≠ 0`, the fibre Hessian of `L ∘ Th` at `v` evaluates `w₁, w₂` as the fibre Hessian of `L` at
`Th v` evaluates `dh w₁, dh w₂`. -/
@[simp]
theorem fiberHessian_comp_tangentMap_apply (L : TangentBundle J N → 𝕜) (h : M ≃ₘ^n⟮I, J⟯ N)
    (hn : n ≠ 0) (v : TangentBundle I M) (w₁ w₂ : TangentSpace I v.proj) :
    fiberHessian (L ∘ tangentMap I J h) v w₁ w₂ =
      fiberHessian L (tangentMap I J h v) (mfderiv I J h v.proj w₁)
        (mfderiv I J h v.proj w₂) :=
  fiberHessian_comp_tangentMap_apply_of_isInvertible h L v (h.isInvertible_mfderiv hn) w₁ w₂

/-- If the differential of `f` at the base point of `v` is invertible, the fibre Hessian of
`L ∘ Tf` at `v` is invertible exactly when that of `L` at `Tf v` is. -/
theorem isInvertible_fiberHessian_comp_tangentMap_iff_of_isInvertible (f : M → N)
    (L : TangentBundle J N → 𝕜) (v : TangentBundle I M)
    (hf : (mfderiv I J f v.proj).IsInvertible) :
    (fiberHessian (L ∘ tangentMap I J f) v).IsInvertible ↔
      (fiberHessian L (tangentMap I J f v)).IsInvertible := by
  obtain ⟨A₀, hA⟩ := hf
  -- Read the differential and both fibre Hessians as maps between the model spaces.
  let A : E ≃L[𝕜] F := A₀
  let P : E →L[𝕜] E →L[𝕜] 𝕜 := fiberHessian (L ∘ tangentMap I J f) v
  let Q : F →L[𝕜] F →L[𝕜] 𝕜 := fiberHessian L (tangentMap I J f v)
  have hPQ : P = Q.bilinearComp (A : E →L[𝕜] F) (A : E →L[𝕜] F) := by
    ext w₁ w₂
    rw [ContinuousLinearMap.bilinearComp_apply]
    exact (fiberHessian_comp_tangentMap_apply_of_isInvertible f L v ⟨A₀, hA⟩ w₁ w₂).trans
      (by rw [← hA]; rfl)
  have hQP : Q = P.bilinearComp (A.symm : F →L[𝕜] E) (A.symm : F →L[𝕜] E) := by
    ext w₁ w₂
    simp [hPQ]
  change P.IsInvertible ↔ Q.IsInvertible
  refine ⟨fun hP ↦ ?_, fun hQ ↦ ?_⟩
  · rw [hQP]
    exact hP.bilinearComp A.symm A.symm
  · rw [hPQ]
    exact hQ.bilinearComp A A

/-- **Invertibility of the fibre Hessian is natural under diffeomorphisms.** For a `C^n`
diffeomorphism `h` with `n ≠ 0`, the fibre Hessian of `L ∘ Th` at `v` is invertible exactly when
that of `L` at `Th v` is. -/
@[simp]
theorem isInvertible_fiberHessian_comp_tangentMap_iff (L : TangentBundle J N → 𝕜)
    (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (v : TangentBundle I M) :
    (fiberHessian (L ∘ tangentMap I J h) v).IsInvertible ↔
      (fiberHessian L (tangentMap I J h v)).IsInvertible :=
  isInvertible_fiberHessian_comp_tangentMap_iff_of_isInvertible h L v (h.isInvertible_mfderiv hn)

/-- **Regularity does not depend on the configuration coordinates.** For a `C^n` diffeomorphism
`h` with `n ≠ 0`, the Lagrangian `L ∘ Th` is regular exactly when `L` is. -/
@[simp]
theorem isRegularLagrangian_comp_tangentMap_iff (L : TangentBundle J N → 𝕜)
    (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    IsRegularLagrangian (L ∘ tangentMap I J h) ↔ IsRegularLagrangian L := by
  simp only [isRegularLagrangian_iff, isInvertible_fiberHessian_comp_tangentMap_iff L h hn]
  exact ⟨fun hL v ↦ h.tangentMap_apply_symm hn v ▸ hL (tangentMap J I h.symm v),
    fun hL v ↦ hL _⟩

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- **The Legendre map is natural under diffeomorphisms.** For a diffeomorphism `h : M → N` and a
Lagrangian `L` on `N`, the cotangent lift of `h` carries the Legendre transform of `L ∘ Th` at `v`
to the Legendre transform of `L` at `Th v`. -/
@[simp]
theorem cotangent_legendreMap_comp_tangentMap (L : TangentBundle J N → 𝕜) (h : M ≃ₘ⟮I, J⟯ N)
    (v : TangentBundle I M) :
    h.cotangent (legendreMap (L ∘ tangentMap I J h) v) = legendreMap L (tangentMap I J h v) :=
  (CotangentBundle.cotangentRel_diffeomorph_iff I J h _ _).1
    (cotangentRel_legendreMap_comp_tangentMap_of_isInvertible h L v
      (h.isInvertible_mfderiv (by simp)))

/-- For a diffeomorphism `h`, the Legendre map of `L ∘ Th` is `(T*h)⁻¹ ∘ FL ∘ Th`. -/
theorem legendreMap_comp_tangentMap (L : TangentBundle J N → 𝕜) (h : M ≃ₘ⟮I, J⟯ N) :
    legendreMap (L ∘ tangentMap I J h) = h.cotangent.symm ∘ legendreMap L ∘ tangentMap I J h :=
  funext fun v ↦ h.cotangent.eq_symm_apply.2 (cotangent_legendreMap_comp_tangentMap L h v)

/-- **Hyperregularity does not depend on the configuration coordinates.** For a diffeomorphism
`h`, the Lagrangian `L ∘ Th` is hyperregular exactly when `L` is. -/
@[simp]
theorem isHyperregularLagrangian_comp_tangentMap_iff (L : TangentBundle J N → 𝕜)
    (h : M ≃ₘ⟮I, J⟯ N) :
    IsHyperregularLagrangian (L ∘ tangentMap I J h) ↔ IsHyperregularLagrangian L := by
  have hb : Function.Bijective (legendreMap (L ∘ tangentMap I J h)) ↔
      Function.Bijective (legendreMap L) := by
    have h₁ : Function.Bijective ⇑h.cotangent.symm := h.cotangent.symm.bijective
    have h₂ : Function.Bijective ⇑h.tangent := h.tangent.bijective
    rw [legendreMap_comp_tangentMap, ← h.coe_tangent, Function.Bijective.of_comp_iff' h₁]
    exact Function.Bijective.of_comp_iff _ h₂
  have hr := isRegularLagrangian_comp_tangentMap_iff L h (by simp)
  exact ⟨fun hL ↦ ⟨hr.1 hL.1, hb.1 hL.2⟩, fun hL ↦ ⟨hr.2 hL.1, hb.2 hL.2⟩⟩

/-- **The Hamiltonian is natural under diffeomorphisms.** If `L` and `L ∘ Th` are hyperregular,
the Hamiltonian of `L ∘ Th` is the Hamiltonian of `L` composed with the cotangent lift of `h`. -/
theorem IsHyperregularLagrangian.hamiltonian_comp_tangentMap {L : TangentBundle J N → 𝕜}
    (hL : IsHyperregularLagrangian L) {h : M ≃ₘ⟮I, J⟯ N}
    (hLh : IsHyperregularLagrangian (L ∘ tangentMap I J h)) :
    hLh.hamiltonian = hL.hamiltonian ∘ h.cotangent := by
  refine (hLh.eq_hamiltonian_iff.2 ?_).symm
  rw [lagrangianEnergy_comp_tangentMap L h (by simp), ← hL.hamiltonian_comp_legendreMap]
  funext v
  simp

end Legendre

section Cartan

variable {E H F H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] {L : TangentBundle J N → ℝ}

/-- **The Cartan one-form is natural under diffeomorphisms.** For a smooth real Lagrangian `L` on
`N` and a diffeomorphism `h : M → N`, the Cartan one-form of `L ∘ Th` is the pullback of the
Cartan one-form of `L` along `Th`: `θ_(L ∘ Th) = Th^* θ_L`. -/
theorem cartanForm_comp_tangentMap (hL : ContMDiff J.tangent 𝓘(ℝ, ℝ) ∞ L) (h : M ≃ₘ⟮I, J⟯ N)
    (hLh : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (L ∘ tangentMap I J h)) :
    cartanForm (L ∘ tangentMap I J h) hLh =
      SmoothForm.mpullback (tangentMap I J h) (h.contMDiff.contMDiff_tangentMap (by simp))
        (cartanForm L hL) := by
  have key : ∀ (f g : TangentBundle I M → CotangentBundle J N)
      (hf : ContMDiff I.tangent (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ f)
      (hg : ContMDiff I.tangent (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ g), f = g →
      SmoothForm.mpullback f hf (CotangentBundle.liouvilleForm J N) =
        SmoothForm.mpullback g hg (CotangentBundle.liouvilleForm J N) := by
    rintro f g hf hg rfl
    rfl
  have hfun : legendreMap L ∘ tangentMap I J h =
      ⇑h.cotangent ∘ legendreMap (L ∘ tangentMap I J h) :=
    funext fun v ↦ by simp
  -- Both sides are pullbacks of Liouville forms, and `T*h` preserves the Liouville form.
  rw [cartanForm_eq_mpullback, cartanForm_eq_mpullback, SmoothForm.mpullback_mpullback,
    key _ _ _ (h.cotangent.contMDiff.comp (contMDiff_legendreMap hLh le_rfl)) hfun,
    ← SmoothForm.mpullback_mpullback (legendreMap (L ∘ tangentMap I J h)) h.cotangent
      (contMDiff_legendreMap hLh le_rfl) h.cotangent.contMDiff,
    Diffeomorph.mpullback_cotangent_liouvilleForm]

/-- **The Cartan two-form is natural under diffeomorphisms.** For a smooth real Lagrangian `L` on
`N` and a diffeomorphism `h : M → N`, the Cartan two-form of `L ∘ Th` is the pullback of the
Cartan two-form of `L` along `Th`: `ω_(L ∘ Th) = Th^* ω_L`. -/
theorem cartanTwoForm_comp_tangentMap (hL : ContMDiff J.tangent 𝓘(ℝ, ℝ) ∞ L) (h : M ≃ₘ⟮I, J⟯ N)
    (hLh : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (L ∘ tangentMap I J h)) :
    cartanTwoForm (L ∘ tangentMap I J h) hLh =
      SmoothForm.mpullback (tangentMap I J h) (h.contMDiff.contMDiff_tangentMap (by simp))
        (cartanTwoForm L hL) := by
  rw [cartanTwoForm_eq_neg_mextDerivₗ, cartanTwoForm_eq_neg_mextDerivₗ,
    cartanForm_comp_tangentMap hL h hLh, map_neg, ← SmoothForm.mextDerivₗ_mpullback]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [BoundarylessManifold J.tangent (TangentBundle J N)]

/-- **The Lagrangian vector field is natural under diffeomorphisms.** For a smooth regular real
Lagrangian `L` on a finite-dimensional manifold `N` with boundaryless tangent bundle and a
diffeomorphism `h : M → N`, the tangent map `Th` carries the Hamiltonian vector field of the
energy of `L ∘ Th` for its Cartan two-form to the Hamiltonian vector field of the energy of `L`
for the Cartan two-form of `L`. -/
theorem mfderiv_tangentMap_hamiltonianVectorField_cartanTwoForm
    (hL : ContMDiff J.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L) (h : M ≃ₘ⟮I, J⟯ N)
    (hLh : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (L ∘ tangentMap I J h)) (v : TangentBundle I M) :
    mfderiv I.tangent J.tangent (tangentMap I J h) v
        ((cartanTwoForm (L ∘ tangentMap I J h) hLh).hamiltonianVectorField
          (lagrangianEnergy (L ∘ tangentMap I J h)) v) =
      (cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) (tangentMap I J h v) := by
  have hω := hreg.isSymplectic_cartanTwoForm hL
  have hTh : IsLocalDiffeomorph I.tangent J.tangent ∞ (tangentMap I J h) :=
    h.coe_tangent ▸ h.tangent.isLocalDiffeomorph
  -- `Th` is a local diffeomorphism pulling `ω_L` back to `ω_(L ∘ Th)`, which is nondegenerate.
  have hpull := cartanTwoForm_comp_tangentMap hL h hLh
  have hωh : (cartanTwoForm (L ∘ tangentMap I J h) hLh).IsNondegenerate :=
    hpull ▸ hω.isNondegenerate.isNondegenerate_mpullback_of_isLocalDiffeomorph hTh
  have := hωh.mfderiv_hamiltonianVectorField_comp hω.isNondegenerate hTh.contMDiff hpull.symm
    (hTh.isInvertible_mfderiv (by simp) v).surjective
    ((contMDiff_lagrangianEnergy (m := ∞) hL le_rfl _).mdifferentiableAt (by simp))
  rwa [← lagrangianEnergy_comp_tangentMap L h (by simp)] at this

/-- **The equations of motion do not depend on the configuration coordinates, on a set of
times.** For a smooth regular real Lagrangian `L` on a finite-dimensional manifold `N` with
boundaryless tangent bundle and a diffeomorphism `h : M → N`, a curve `γ` in `TM` is an integral
curve on `s` of the Lagrangian vector field of `L ∘ Th`, the Hamiltonian vector field of its
energy for its Cartan two-form, exactly when `Th ∘ γ` is an integral curve on `s` of the
Lagrangian vector field of `L`. -/
theorem isMIntegralCurveOn_tangentMap_comp_hamiltonianVectorField_cartanTwoForm_iff
    (hL : ContMDiff J.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L) (h : M ≃ₘ⟮I, J⟯ N)
    (hLh : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (L ∘ tangentMap I J h)) {γ : ℝ → TangentBundle I M}
    {s : Set ℝ} :
    IsMIntegralCurveOn (tangentMap I J h ∘ γ)
        ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)) s ↔
      IsMIntegralCurveOn γ ((cartanTwoForm (L ∘ tangentMap I J h) hLh).hamiltonianVectorField
        (lagrangianEnergy (L ∘ tangentMap I J h))) s := by
  have hX := mfderiv_tangentMap_hamiltonianVectorField_cartanTwoForm hL hreg h hLh
  -- The inverse tangent lift carries the Lagrangian vector field of `L` back to that of `L ∘ Th`.
  have hY : ∀ y, mfderiv J.tangent I.tangent h.tangent.symm y
      ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) y) =
        (cartanTwoForm (L ∘ tangentMap I J h) hLh).hamiltonianVectorField
          (lagrangianEnergy (L ∘ tangentMap I J h)) (h.tangent.symm y) :=
    h.tangent.mfderiv_symm_apply_eq_of_mfderiv_apply_eq (by simp) fun v ↦ by
      rw [h.coe_tangent]
      exact hX v
  refine ⟨fun hγ ↦ ?_, fun hγ ↦ hγ.map_of_mfderiv_eq (fun t _ ↦
    ((h.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)) (γ t)).mdifferentiableAt (by simp))
    fun t _ ↦ hX (γ t)⟩
  exact (hγ.map_of_mfderiv_eq (fun t _ ↦ h.tangent.symm.mdifferentiable (by simp) _)
    fun t _ ↦ hY _).congr fun t _ ↦ by simp

/-- **The equations of motion do not depend on the configuration coordinates.** For a smooth
regular real Lagrangian `L` on a finite-dimensional manifold `N` with boundaryless tangent bundle
and a diffeomorphism `h : M → N`, a curve `γ` in `TM` is an integral curve of the Lagrangian
vector field of `L ∘ Th`, the Hamiltonian vector field of its energy for its Cartan two-form,
exactly when `Th ∘ γ` is an integral curve of the Lagrangian vector field of `L`. -/
theorem isMIntegralCurve_tangentMap_comp_hamiltonianVectorField_cartanTwoForm_iff
    (hL : ContMDiff J.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L) (h : M ≃ₘ⟮I, J⟯ N)
    (hLh : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (L ∘ tangentMap I J h)) {γ : ℝ → TangentBundle I M} :
    IsMIntegralCurve (tangentMap I J h ∘ γ)
        ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)) ↔
      IsMIntegralCurve γ ((cartanTwoForm (L ∘ tangentMap I J h) hLh).hamiltonianVectorField
        (lagrangianEnergy (L ∘ tangentMap I J h))) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, isMIntegralCurve_iff_isMIntegralCurveOn]
  exact isMIntegralCurveOn_tangentMap_comp_hamiltonianVectorField_cartanTwoForm_iff hL hreg h hLh

end Cartan

end TauCeti
