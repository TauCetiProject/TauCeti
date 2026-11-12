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
  covector `F(L ∘ Tf)(v)` is the pullback of `FL(Tf v)` along `df`, that is, the two Legendre
  transforms are related by the cotangent relation of `f`
  (`TauCeti.cotangentRel_legendreMap_comp_tangentMap`), provided `L` is differentiable along the
  fibre at `Tf v`. The pullback formula also holds with no differentiability of `L` when `df` is
  invertible there (`TauCeti.legendreMap_comp_tangentMap_snd_of_isInvertible`).
* **Energy.** `E_(L ∘ Th) = E_L ∘ Th` (`TauCeti.lagrangianEnergy_comp_tangentMap`).
* **Fibre Hessian and regularity.** The fibre Hessian of `L ∘ Th` at `v` is that of `L` at `Th v`
  composed with `dh` in both arguments (`TauCeti.fiberHessian_comp_tangentMap_apply`), so `L ∘ Th`
  is regular exactly when `L` is (`TauCeti.isRegularLagrangian_comp_tangentMap_iff`), and
  hyperregular exactly when `L` is (`TauCeti.isHyperregularLagrangian_comp_tangentMap_iff`). The
  Hamiltonians then satisfy `H_(L ∘ Th) = H_L ∘ T*h`
  (`TauCeti.IsHyperregularLagrangian.hamiltonian_comp_tangentMap`).
* **Cartan forms.** For real smooth `L`, `θ_(L ∘ Th) = Th^* θ_L` and `ω_(L ∘ Th) = Th^* ω_L`
  (`TauCeti.cartanForm_comp_tangentMap`, `TauCeti.cartanTwoForm_comp_tangentMap`), because `T*h`
  preserves the Liouville form.
* **Equations of motion.** For a smooth regular real Lagrangian on a finite-dimensional
  boundaryless manifold, the differential of `Th` carries the Lagrangian vector field `X_E` of
  `L ∘ Th`, the Hamiltonian vector field of the energy for the Cartan two-form, to that of `L`
  (`TauCeti.mfderiv_tangentMap_hamiltonianVectorField_cartanTwoForm`). Hence a curve `γ` in `TM`
  is an integral curve of `X_E` for `L ∘ Th` exactly when `Th ∘ γ` is one for `L`
  (`TauCeti.isMIntegralCurve_tangentMap_comp_iff`).

Only the cotangent-relation statements allow maps that are not diffeomorphisms; there the
Legendre transform of `L ∘ Tf` is a pullback of that of `L`, not an image under a map of
cotangent bundles.

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
  [ChartedSpace H' N]

/-- Precomposition of the derivative of a function `g` on `F` with a continuous linear map
`D : E → F`: if `g` is differentiable at `D x` or `D` is invertible, then
`(g ∘ D)'(x) = g'(D x) ∘ D`. -/
private theorem fderiv_comp_clm_of_or {g : F → 𝕜} {D : E →L[𝕜] F} {x : E}
    (h : DifferentiableAt 𝕜 g (D x) ∨ D.IsInvertible) :
    fderiv 𝕜 (g ∘ D) x = fderiv 𝕜 g (D x) ∘L D := by
  rcases h with hg | ⟨A, rfl⟩
  · rw [fderiv_comp x hg D.differentiableAt, D.fderiv]
  · exact A.comp_right_fderiv

/-- The Legendre transform of `v` as a covector at the base point of `v`. -/
private theorem legendreMap_eq_mk (L : TangentBundle J N → 𝕜) (v : TangentBundle J N) :
    legendreMap L v = TotalSpace.mk' (F →L[𝕜] 𝕜) v.proj
      (fderiv 𝕜 (fun w : F ↦ L (TotalSpace.mk' F v.proj w)) v.2) :=
  CotangentBundle.ext (proj_legendreMap L v) fun w ↦ by rw [legendreMap_snd]; rfl

/-- The Legendre transform of `L ∘ Tf` at `v` is the pullback along `df` of that of `L` at `Tf v`,
when `L` is differentiable along the fibre at `Tf v` or `df` is invertible at the base point. -/
private theorem legendreMap_comp_tangentMap_snd_of_or (f : M → N) (L : TangentBundle J N → 𝕜)
    (v : TangentBundle I M)
    (h : DifferentiableAt 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w))
      (mfderiv I J f v.proj v.2) ∨ (mfderiv I J f v.proj).IsInvertible) :
    (legendreMap (L ∘ tangentMap I J f) v).2 =
      (legendreMap L (tangentMap I J f v)).2 ∘L mfderiv I J f v.proj := by
  -- Read the differential and the velocity in the model spaces.
  let D : E →L[𝕜] F := mfderiv I J f v.proj
  let x : E := v.2
  have hD : fderiv 𝕜 ((fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w)) ∘ D) x =
      fderiv 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w)) (D x) ∘L D :=
    fderiv_comp_clm_of_or h
  rw [legendreMap_snd, legendreMap_snd]
  exact hD

/-- **The Legendre map under a change of configuration.** If the Lagrangian `L` on `N` is
differentiable along the fibre at `Tf v`, then the Legendre transform of `L ∘ Tf` at `v` is the
pullback of the Legendre transform of `L` at `Tf v` along the differential of `f`. -/
theorem legendreMap_comp_tangentMap_snd (f : M → N) (L : TangentBundle J N → 𝕜)
    (v : TangentBundle I M)
    (hL : DifferentiableAt 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w))
      (mfderiv I J f v.proj v.2)) :
    (legendreMap (L ∘ tangentMap I J f) v).2 =
      (legendreMap L (tangentMap I J f v)).2 ∘L mfderiv I J f v.proj :=
  legendreMap_comp_tangentMap_snd_of_or f L v (.inl hL)

/-- **The Legendre map under a change of configuration with invertible differential.** If the
differential of `f` at the base point of `v` is invertible, then the Legendre transform of
`L ∘ Tf` at `v` is the pullback of the Legendre transform of `L` at `Tf v` along `df`, with no
differentiability assumption on `L`. -/
theorem legendreMap_comp_tangentMap_snd_of_isInvertible (f : M → N) (L : TangentBundle J N → 𝕜)
    (v : TangentBundle I M) (hf : (mfderiv I J f v.proj).IsInvertible) :
    (legendreMap (L ∘ tangentMap I J f) v).2 =
      (legendreMap L (tangentMap I J f v)).2 ∘L mfderiv I J f v.proj :=
  legendreMap_comp_tangentMap_snd_of_or f L v (.inr hf)

/-- **The cotangent relation of Legendre transforms.** If `L` is differentiable along the fibre
at `Tf v`, the Legendre transforms of `L ∘ Tf` at `v` and of `L` at `Tf v` are related by the
cotangent relation of `f`. -/
theorem cotangentRel_legendreMap_comp_tangentMap (f : M → N) (L : TangentBundle J N → 𝕜)
    (v : TangentBundle I M)
    (hL : DifferentiableAt 𝕜 (fun w : F ↦ L (TotalSpace.mk' F (f v.proj) w))
      (mfderiv I J f v.proj v.2)) :
    CotangentBundle.cotangentRel I J f (legendreMap (L ∘ tangentMap I J f) v)
      (legendreMap L (tangentMap I J f v)) :=
  by
    have hs := legendreMap_comp_tangentMap_snd f L v hL
    rw [legendreMap_eq_mk, legendreMap_eq_mk] at hs ⊢
    exact (CotangentBundle.cotangentRel_iff _ _ f _ _).2 ⟨rfl, hs⟩

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

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- **The Legendre map is natural under diffeomorphisms.** For a diffeomorphism `h : M → N` and a
Lagrangian `L` on `N`, the cotangent lift of `h` carries the Legendre transform of `L ∘ Th` at `v`
to the Legendre transform of `L` at `Th v`. -/
@[simp]
theorem cotangent_legendreMap_comp_tangentMap (L : TangentBundle J N → 𝕜) (h : M ≃ₘ⟮I, J⟯ N)
    (v : TangentBundle I M) :
    h.cotangent (legendreMap (L ∘ tangentMap I J h) v) = legendreMap L (tangentMap I J h v) := by
  have hs := legendreMap_comp_tangentMap_snd_of_isInvertible h L v
    (h.isInvertible_mfderiv (by simp))
  rw [legendreMap_eq_mk, legendreMap_eq_mk] at hs ⊢
  refine (CotangentBundle.cotangentRel_diffeomorph_iff I J h _ _).1 ?_
  exact (CotangentBundle.cotangentRel_iff _ _ _ _ _).2 ⟨rfl, hs⟩

/-- For a diffeomorphism `h`, the Legendre map of `L ∘ Th` is `(T*h)⁻¹ ∘ FL ∘ Th`. -/
theorem legendreMap_comp_tangentMap (L : TangentBundle J N → 𝕜) (h : M ≃ₘ⟮I, J⟯ N) :
    legendreMap (L ∘ tangentMap I J h) = h.cotangent.symm ∘ legendreMap L ∘ tangentMap I J h :=
  funext fun v ↦ h.cotangent.eq_symm_apply.2 (cotangent_legendreMap_comp_tangentMap L h v)

omit [IsManifold I 2 M] [IsManifold J 2 N] in
/-- **The energy is natural under diffeomorphisms.** For a diffeomorphism `h`, the energy of
`L ∘ Th` is the energy of `L` composed with `Th`. -/
@[simp]
theorem lagrangianEnergy_comp_tangentMap (L : TangentBundle J N → 𝕜) (h : M ≃ₘ⟮I, J⟯ N) :
    lagrangianEnergy (L ∘ tangentMap I J h) = lagrangianEnergy L ∘ tangentMap I J h :=
  funext fun v ↦ lagrangianEnergy_comp_tangentMap_apply_of_snd h L v
    (legendreMap_comp_tangentMap_snd_of_isInvertible h L v (h.isInvertible_mfderiv (by simp)))

omit [IsManifold I 2 M] [IsManifold J 2 N] in
/-- The fibre Hessian of `L ∘ Th` at `v` is the fibre Hessian of `L` at `Th v` composed with the
differential `A = dh` on both arguments. Here the fibre Hessians are read as bilinear forms on the
model spaces, and precomposition of covectors with `A` is the equivalence
`A.symm.arrowCongr (refl)`. -/
private theorem fiberHessian_comp_tangentMap_eq (L : TangentBundle J N → 𝕜) (h : M ≃ₘ⟮I, J⟯ N)
    (v : TangentBundle I M) :
    ∃ A : E ≃L[𝕜] F, (A : E →L[𝕜] F) = mfderiv I J h v.proj ∧
      (fiberHessian (L ∘ tangentMap I J h) v : E →L[𝕜] E →L[𝕜] 𝕜) =
        ((A.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜) :
          (F →L[𝕜] 𝕜) ≃L[𝕜] E →L[𝕜] 𝕜) : (F →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) ∘L
          (fiberHessian L (tangentMap I J h v) : F →L[𝕜] F →L[𝕜] 𝕜) ∘L (A : E →L[𝕜] F) := by
  let A' : E ≃L[𝕜] F := h.mfderivToContinuousLinearEquiv (by simp) v.proj
  let B := A'.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let g : F → 𝕜 := fun w ↦ L (TotalSpace.mk' F (h v.proj) w)
  let x : E := v.2
  have hB : ∀ φ : F →L[𝕜] 𝕜, B φ = φ ∘L (A' : E →L[𝕜] F) := fun φ ↦ by
    ext w
    simp [B]
  -- On the fibre, `L ∘ Th` is `g ∘ A`, whose derivative is `B ∘ g' ∘ A`.
  have hd : fderiv 𝕜 (g ∘ A') = B ∘ fderiv 𝕜 g ∘ A' := by
    funext w
    rw [Function.comp_apply, Function.comp_apply, hB]
    exact A'.comp_right_fderiv
  have h2 : fderiv 𝕜 (fderiv 𝕜 (g ∘ A')) x =
      (B : (F →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) ∘L fderiv 𝕜 (fderiv 𝕜 g) (A' x) ∘L
        (A' : E →L[𝕜] F) := by
    rw [hd, B.comp_fderiv, A'.comp_right_fderiv]
  have hA : (A' : E →L[𝕜] F) = mfderiv I J h v.proj := h.mfderivToContinuousLinearEquiv_coe _
  refine ⟨A', hA, ?_⟩
  have hfun : (fun w : E ↦ (L ∘ tangentMap I J h) (TotalSpace.mk' E v.proj w)) = g ∘ A' := by
    funext w
    exact congrArg (fun u ↦ L (TotalSpace.mk' F (h v.proj) u)) (DFunLike.congr_fun hA w).symm
  have hx : A' x = mfderiv I J h v.proj v.2 := DFunLike.congr_fun hA x
  rw [hx] at h2
  rw [fiberHessian_def, fiberHessian_def, hfun]
  exact h2

omit [IsManifold I 2 M] [IsManifold J 2 N] in
/-- **The fibre Hessian is natural under diffeomorphisms.** The fibre Hessian of `L ∘ Th` at `v`
evaluates `w₁, w₂` as the fibre Hessian of `L` at `Th v` evaluates `dh w₁, dh w₂`. -/
@[simp]
theorem fiberHessian_comp_tangentMap_apply (L : TangentBundle J N → 𝕜) (h : M ≃ₘ⟮I, J⟯ N)
    (v : TangentBundle I M) (w₁ w₂ : TangentSpace I v.proj) :
    fiberHessian (L ∘ tangentMap I J h) v w₁ w₂ =
      fiberHessian L (tangentMap I J h v) (mfderiv I J h v.proj w₁)
        (mfderiv I J h v.proj w₂) := by
  obtain ⟨A, hA, hH⟩ := fiberHessian_comp_tangentMap_eq L h v
  rw [← hA]
  exact (DFunLike.congr_fun (DFunLike.congr_fun hH w₁) w₂).trans rfl

omit [IsManifold I 2 M] [IsManifold J 2 N] in
/-- The fibre Hessian of `L ∘ Th` at `v` is invertible exactly when that of `L` at `Th v` is. -/
theorem isInvertible_fiberHessian_comp_tangentMap_iff (L : TangentBundle J N → 𝕜)
    (h : M ≃ₘ⟮I, J⟯ N) (v : TangentBundle I M) :
    (fiberHessian (L ∘ tangentMap I J h) v).IsInvertible ↔
      (fiberHessian L (tangentMap I J h v)).IsInvertible := by
  obtain ⟨A, -, hH⟩ := fiberHessian_comp_tangentMap_eq L h v
  -- Read both fibre Hessians as bilinear forms on the model spaces.
  let P : E →L[𝕜] E →L[𝕜] 𝕜 := fiberHessian (L ∘ tangentMap I J h) v
  let Q : F →L[𝕜] F →L[𝕜] 𝕜 := fiberHessian L (tangentMap I J h v)
  let B : (F →L[𝕜] 𝕜) ≃L[𝕜] E →L[𝕜] 𝕜 := A.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  have hPQ : P = (B : (F →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) ∘L Q ∘L (A : E →L[𝕜] F) := hH
  have key : P.IsInvertible ↔ Q.IsInvertible := by
    rw [hPQ, ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv]
  exact key

/-- **Regularity does not depend on the configuration coordinates.** For a diffeomorphism `h`,
the Lagrangian `L ∘ Th` is regular exactly when `L` is. -/
@[simp]
theorem isRegularLagrangian_comp_tangentMap_iff (L : TangentBundle J N → 𝕜)
    (h : M ≃ₘ⟮I, J⟯ N) :
    IsRegularLagrangian (L ∘ tangentMap I J h) ↔ IsRegularLagrangian L := by
  simp only [isRegularLagrangian_iff, isInvertible_fiberHessian_comp_tangentMap_iff]
  refine ⟨fun hL v ↦ ?_, fun hL v ↦ hL _⟩
  have hv : tangentMap I J h (h.tangent.symm v) = v := by
    rw [← h.coe_tangent, Diffeomorph.apply_symm_apply]
  exact hv ▸ hL (h.tangent.symm v)

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
  exact ⟨fun hL ↦ ⟨(isRegularLagrangian_comp_tangentMap_iff L h).1 hL.1, hb.1 hL.2⟩,
    fun hL ↦ ⟨(isRegularLagrangian_comp_tangentMap_iff L h).2 hL.1, hb.2 hL.2⟩⟩

/-- **The Hamiltonian is natural under diffeomorphisms.** If `L` and `L ∘ Th` are hyperregular,
the Hamiltonian of `L ∘ Th` is the Hamiltonian of `L` composed with the cotangent lift of `h`. -/
theorem IsHyperregularLagrangian.hamiltonian_comp_tangentMap {L : TangentBundle J N → 𝕜}
    (hL : IsHyperregularLagrangian L) {h : M ≃ₘ⟮I, J⟯ N}
    (hLh : IsHyperregularLagrangian (L ∘ tangentMap I J h)) :
    hLh.hamiltonian = hL.hamiltonian ∘ h.cotangent := by
  refine (hLh.eq_hamiltonian_iff.2 ?_).symm
  rw [lagrangianEnergy_comp_tangentMap, ← hL.hamiltonian_comp_legendreMap]
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
      SmoothForm.mpullback h.tangent h.tangent.contMDiff (cartanForm L hL) := by
  have key : ∀ (f g : TangentBundle I M → CotangentBundle J N)
      (hf : ContMDiff I.tangent (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ f)
      (hg : ContMDiff I.tangent (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ g), f = g →
      SmoothForm.mpullback f hf (CotangentBundle.liouvilleForm J N) =
        SmoothForm.mpullback g hg (CotangentBundle.liouvilleForm J N) := by
    rintro f g hf hg rfl
    rfl
  have hfun : legendreMap L ∘ ⇑h.tangent = ⇑h.cotangent ∘ legendreMap (L ∘ tangentMap I J h) :=
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
      SmoothForm.mpullback h.tangent h.tangent.contMDiff (cartanTwoForm L hL) := by
  rw [cartanTwoForm_eq_neg_mextDerivₗ, cartanTwoForm_eq_neg_mextDerivₗ,
    cartanForm_comp_tangentMap hL h hLh, map_neg, ← SmoothForm.mextDerivₗ_mpullback]

variable [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [BoundarylessManifold I.tangent (TangentBundle I M)]
  [BoundarylessManifold J.tangent (TangentBundle J N)]

/-- **The Lagrangian vector field is natural under diffeomorphisms.** For a smooth regular real
Lagrangian `L` on a finite-dimensional boundaryless manifold `N` and a diffeomorphism
`h : M → N`, the tangent map `Th` carries the Hamiltonian vector field of the energy of `L ∘ Th`
for its Cartan two-form to the Hamiltonian vector field of the energy of `L` for the Cartan
two-form of `L`. -/
theorem mfderiv_tangentMap_hamiltonianVectorField_cartanTwoForm
    (hL : ContMDiff J.tangent 𝓘(ℝ, ℝ) ∞ L) (hreg : IsRegularLagrangian L) (h : M ≃ₘ⟮I, J⟯ N)
    (hLh : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (L ∘ tangentMap I J h)) (v : TangentBundle I M) :
    mfderiv I.tangent J.tangent h.tangent v
        ((cartanTwoForm (L ∘ tangentMap I J h) hLh).hamiltonianVectorField
          (lagrangianEnergy (L ∘ tangentMap I J h)) v) =
      (cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L) (h.tangent v) := by
  have hω := hreg.isSymplectic_cartanTwoForm hL
  have hωh := ((isRegularLagrangian_comp_tangentMap_iff L h).2 hreg).isSymplectic_cartanTwoForm hLh
  have := hωh.isNondegenerate.mfderiv_hamiltonianVectorField_comp hω.isNondegenerate
    h.tangent.contMDiff (cartanTwoForm_comp_tangentMap hL h hLh).symm
    (h.tangent.isInvertible_mfderiv (x := v) (by simp)).surjective
    ((contMDiff_lagrangianEnergy (m := ∞) hL le_rfl _).mdifferentiableAt (by simp))
  have hE : lagrangianEnergy (L ∘ tangentMap I J h) = lagrangianEnergy L ∘ ⇑h.tangent := by
    rw [lagrangianEnergy_comp_tangentMap, Diffeomorph.coe_tangent]
  rwa [← hE] at this

/-- **The equations of motion do not depend on the configuration coordinates.** For a smooth
regular real Lagrangian `L` on a finite-dimensional boundaryless manifold `N` and a
diffeomorphism `h : M → N`, a curve `γ` in `TM` is an integral curve of the Lagrangian vector
field of `L ∘ Th`, the Hamiltonian vector field of its energy for its Cartan two-form, exactly
when `Th ∘ γ` is an integral curve of the Lagrangian vector field of `L`. -/
theorem isMIntegralCurve_tangentMap_comp_iff (hL : ContMDiff J.tangent 𝓘(ℝ, ℝ) ∞ L)
    (hreg : IsRegularLagrangian L) (h : M ≃ₘ⟮I, J⟯ N)
    (hLh : ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞ (L ∘ tangentMap I J h)) {γ : ℝ → TangentBundle I M} :
    IsMIntegralCurve (h.tangent ∘ γ)
        ((cartanTwoForm L hL).hamiltonianVectorField (lagrangianEnergy L)) ↔
      IsMIntegralCurve γ ((cartanTwoForm (L ∘ tangentMap I J h) hLh).hamiltonianVectorField
        (lagrangianEnergy (L ∘ tangentMap I J h))) := by
  have hω := hreg.isSymplectic_cartanTwoForm hL
  have hωh := ((isRegularLagrangian_comp_tangentMap_iff L h).2 hreg).isSymplectic_cartanTwoForm hLh
  have hpull := cartanTwoForm_comp_tangentMap hL h hLh
  have hE : lagrangianEnergy (L ∘ tangentMap I J h) = lagrangianEnergy L ∘ ⇑h.tangent := by
    rw [lagrangianEnergy_comp_tangentMap, Diffeomorph.coe_tangent]
  constructor
  · intro hγ
    -- Pull back along the inverse tangent lift, which carries `E_(L ∘ Th)` to `E_L`.
    have hE' : lagrangianEnergy (L ∘ tangentMap I J h) ∘ ⇑h.tangent.symm = lagrangianEnergy L := by
      funext p
      simp only [hE, Function.comp_apply, Diffeomorph.apply_symm_apply]
    have := hω.isNondegenerate.isMIntegralCurve_comp_hamiltonianVectorField hωh.isNondegenerate
      h.tangent.symm.contMDiff (SmoothForm.mpullback_symm_eq_of_mpullback_eq hpull.symm)
      (fun t ↦ (h.tangent.symm.isInvertible_mfderiv (by simp)).surjective)
      (fun t ↦ ((contMDiff_lagrangianEnergy (m := ∞) hLh le_rfl) _).mdifferentiableAt (by simp))
      (hE' ▸ hγ)
    have hid : ⇑h.tangent.symm ∘ (⇑h.tangent ∘ γ) = γ := by
      funext t
      simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
    rwa [hid] at this
  · intro hγ
    have := hωh.isNondegenerate.isMIntegralCurve_comp_hamiltonianVectorField hω.isNondegenerate
      h.tangent.contMDiff hpull.symm
      (fun t ↦ (h.tangent.isInvertible_mfderiv (by simp)).surjective)
      (fun t ↦ ((contMDiff_lagrangianEnergy (m := ∞) hL le_rfl) _).mdifferentiableAt (by simp))
      (hE ▸ hγ)
    exact this

end Cartan

end TauCeti
