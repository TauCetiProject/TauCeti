/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import TauCeti.Geometry.Symplectic.Flux.Hamiltonian
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import TauCeti.Geometry.Manifold.DifferentialForm.ParametricPrimitive
import TauCeti.Geometry.Manifold.Flow.Parametric
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Diffeotopies whose velocity fields are Hamiltonian

Let `σ` be a two-form on a manifold `M` and let `φ_t`, `t ∈ [0, 1]`, be a smooth diffeotopy of `M`
with velocity field `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` (`TauCeti.Diffeotopy.velocity`). A Hamiltonian of the
diffeotopy, read along the motion (`TauCeti.Diffeotopy.HasHamiltonian`), is a single smooth
function `F` on the cylinder `M × [0, 1]` with `d(F_t) = φ_t^* (ι_{X_t} σ)` for every `t`. Setting
`H_t = F_t ∘ φ_t⁻¹` it gives, at every time, a Hamiltonian function of the velocity field,
`ι_{X_t} σ = d H_t` (`TauCeti.Diffeotopy.HasHamiltonian.isHamiltonianVectorField_velocity`).

This file proves the converse: if at every time `t` the velocity field `X_t` is the Hamiltonian
vector field of some differentiable function `H_t`, with no condition at all on how `H_t` depends
on `t`, then the diffeotopy has a Hamiltonian, which is jointly smooth in space and time
(`TauCeti.Diffeotopy.exists_hasHamiltonian_iff`). In particular a diffeotopy through
diffeomorphisms preserving `σ` is a Hamiltonian diffeotopy exactly when each of its velocity
fields is a Hamiltonian vector field
(`TauCeti.Diffeotopy.isHamiltonian_iff_forall_isHamiltonianVectorField_velocity`). Neither
closedness nor nondegeneracy of `σ`, nor connectedness or compactness of `M`, is needed.

The time-wise Hamiltonians are only determined up to a constant on each connected component of
`M` at each time, and an arbitrary choice need not even be continuous in `t`. The proof instead
reads the contraction `ι_{∂ₜ} Φ^* σ` of the pullback of `σ` along the motion
`Φ (x, t) = φ_t x` with the unit time vector `∂ₜ` as a smooth one-form on the cylinder. Its slice
at time `t` is `φ_t^* (ι_{X_t} σ) = d (H_t ∘ φ_t)`
(`TauCeti.Diffeotopy.mpullback_cylinderMap_apply_eq_eval₂_velocity`), so every slice is exact,
and the smooth selection of primitives along a smooth family of exact one-forms
(`TauCeti.exists_contMDiff_mvfderiv_eq_of_forall_exists`) chooses the primitives jointly
smoothly. The unit time vector field is smooth on the closed interval, including at its ends
(`TauCeti.contMDiff_one_tangentSpace_Icc`).

This is the step of the proof that a symplectic isotopy of zero flux is homotopic to a
Hamiltonian isotopy in which, after correcting the isotopy by symplectic flows so that its
velocity fields are Hamiltonian at every time, the time-wise Hamiltonians are assembled into
one smooth Hamiltonian.

## Main results

* `TauCeti.Diffeotopy.mpullback_cylinderMap_apply_eq_eval₂_velocity`: the integrand
  `(Φ^* σ)_(x, t)(∂ₜ, v)` is `σ_{φ_t x}(X_t (φ_t x), dφ_t v)`.
* `TauCeti.Diffeotopy.HasHamiltonian.isHamiltonianVectorField_velocity`: a Hamiltonian `F` along
  the motion makes each velocity field `X_t` the Hamiltonian vector field of `F_t ∘ φ_t⁻¹`.
* `TauCeti.Diffeotopy.exists_hasHamiltonian_iff`: a diffeotopy has a Hamiltonian, read along the
  motion, exactly when each of its velocity fields is a Hamiltonian vector field.
* `TauCeti.Diffeotopy.isHamiltonian_iff_forall_isHamiltonianVectorField_velocity`: a diffeotopy
  is Hamiltonian exactly when it preserves `σ` and each of its velocity fields is a Hamiltonian
  vector field.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (Hamiltonian isotopies, and the smooth choice of
  Hamiltonians in the proof of Theorem 10.2.5).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Section 3.1.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] {σ : SmoothTwoForm J M} {Φ : Diffeotopy J ∞ M}

/-- **The flux integrand through the velocity field.** The pullback of `σ` along the motion,
evaluated at `(x, t)` on the unit time vector `∂ₜ` and a spatial vector `v`, is
`σ_{φ_t x}(X_t (φ_t x), dφ_t v)`, the pullback `φ_t^* (ι_{X_t} σ)` of the contraction of `σ`
with the velocity field, evaluated at `x` on `v`. -/
theorem mpullback_cylinderMap_apply_eq_eval₂_velocity (p : M × unitInterval) (v : E) :
    mpullback (J.prod (𝓡∂ 1)) J Φ.cylinderMap σ.val p
        ![((0 : E), (1 : TangentSpace (𝓡∂ 1) p.2)), (v, (0 : EuclideanSpace ℝ (Fin 1)))] =
      SmoothBundleForm.eval₂ σ (Φ (p.2, p.1)) (Φ.velocity p.2 (Φ (p.2, p.1)))
        (mfderiv J J (Φ.timeSlice p.2) p.1 v) := by
  refine Eq.trans ?_ (SmoothBundleForm.eval₂_apply σ _ _ _).symm
  rw [mpullback_apply, velocity_apply, ← Φ.mfderiv_cylinderMap_inl (by simp) p v,
    ← Φ.cylinderMap_apply p, Prod.mk.eta]
  -- Both sides evaluate `σ` at `φ_t x` on the images of `∂ₜ` and `(v, 0)` under the derivative of
  -- the motion.
  exact congrArg (σ.val (Φ.cylinderMap p)) (funext fun i : Fin 2 ↦ by fin_cases i <;> rfl)

variable (σ Φ) in
/-- The one-form `ι_{∂ₜ} Φ^* σ` on the cylinder: the contraction of the pullback of `σ` along the
motion with the unit time vector field `∂ₜ`. -/
private def timeContraction : RoughForm (J.prod (𝓡∂ 1)) (M × unitInterval) ℝ 1 :=
  (mpullback (J.prod (𝓡∂ 1)) J Φ.cylinderMap σ.val).interior
    (verticalField J fun (_ : M) (t : unitInterval) ↦ (1 : TangentSpace (𝓡∂ 1) t))

/-- The one-form `ι_{∂ₜ} Φ^* σ` on the cylinder is smooth. -/
private theorem isSmoothForm_interior_mpullback_cylinderMap :
    IsSmoothForm (J.prod (𝓡∂ 1)) ∞ (timeContraction σ Φ) :=
  ((SmoothForm.isSmoothForm σ).mpullback (Φ.contMDiff_cylinderMap.of_le (by simp))).interior
    (contMDiff_verticalField (contMDiff_one_tangentSpace_Icc.comp contMDiff_snd))

/-- **The velocity fields of a diffeotopy with a Hamiltonian are Hamiltonian.** If `F` is a
Hamiltonian of `φ_t`, read along the motion, then at every time `t` the velocity field `X_t` is the
Hamiltonian vector field of `H_t = F_t ∘ φ_t⁻¹`, that is `ι_{X_t} σ = d H_t`. -/
theorem HasHamiltonian.isHamiltonianVectorField_velocity {F : M × unitInterval → ℝ}
    (hF : Φ.HasHamiltonian σ F) (t : unitInterval) :
    σ.IsHamiltonianVectorField ((fun x ↦ F (x, t)) ∘ (Φ.timeSlice t).symm) (Φ.velocity t) := by
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun y w ↦ ?_
  -- Write `y = φ_t x` and `w = dφ_t v`.
  set x := (Φ.timeSlice t).symm y
  set v : E := mfderiv J J (Φ.timeSlice t).symm y w
  have hy : Φ (t, x) = y := by
    rw [← timeSlice_apply]
    exact (Φ.timeSlice t).apply_symm_apply y
  have hw : mfderiv J J (Φ.timeSlice t) x v = w := by
    have h := (Φ.timeSlice t).mfderiv_apply_mfderiv_symm_apply (by simp) x
      (w : TangentSpace J (Φ.timeSlice t x))
    rwa [(Φ.timeSlice t).apply_symm_apply] at h
  have h₁ : mvfderiv J ((fun x ↦ F (x, t)) ∘ (Φ.timeSlice t).symm) y w =
      mvfderiv J (fun x ↦ F (x, t)) x v :=
    DFunLike.congr_fun ((Φ.timeSlice t).symm.mvfderiv_comp_diffeomorph (by simp) _ y) w
  -- The defining identity of `F` at `(x, t)`, through the velocity field.
  have h₂ : SmoothBundleForm.eval₂ σ (Φ (t, x)) (Φ.velocity t (Φ (t, x)))
      (mfderiv J J (Φ.timeSlice t) x v) = mvfderiv J (fun x ↦ F (x, t)) x v :=
    (mpullback_cylinderMap_apply_eq_eval₂_velocity (x, t) v).symm.trans
      ((hF.mpullback_cylinderMap_apply (x, t) v).trans
        ((hF.contMDiff.mdifferentiableAt (by simp)).mvfderiv_prod_eq_apply_of_snd_eq_zero
          (v := (v, 0)) rfl))
  rw [h₁, ← h₂, hy]
  exact congrArg (SmoothBundleForm.eval₂ σ y (Φ.velocity t y)) hw.symm

/-- If the velocity field `X_t` is the Hamiltonian vector field of `H`, then `H ∘ φ_t` is a
primitive of the slice at time `t` of the one-form `ι_{∂ₜ} Φ^* σ` on the cylinder. -/
private theorem mvfderiv_comp_timeSlice_eq_interior_mpullback_cylinderMap {t : unitInterval}
    {H : M → ℝ} (hX : σ.IsHamiltonianVectorField H (Φ.velocity t)) (x : M) (v : E) :
    mvfderiv J (H ∘ Φ.timeSlice t) x v =
      timeContraction σ Φ (x, t) ![(v, (0 : EuclideanSpace ℝ (Fin 1)))] := by
  refine (DFunLike.congr_fun ((Φ.timeSlice t).mvfderiv_comp_diffeomorph (by simp) H x) v).trans ?_
  refine (SmoothTwoForm.isHamiltonianVectorField_iff.1 hX _ _).symm.trans ?_
  have h := mpullback_cylinderMap_apply_eq_eval₂_velocity (σ := σ) (Φ := Φ) (x, t) v
  rw [← timeSlice_apply] at h
  dsimp only at h
  rw [timeContraction, RoughForm.interior_apply, verticalField_apply]
  exact h.symm

/-- **Hamiltonians from Hamiltonian velocity fields.** A diffeotopy has a Hamiltonian, read along
the motion, exactly when at every time `t` its velocity field `X_t` is the Hamiltonian vector field
of a differentiable function `H_t`, that is `ι_{X_t} σ = d H_t`. No regularity of `H_t` in `t` is
assumed, while a Hamiltonian along the motion is by definition jointly smooth on the cylinder. -/
theorem exists_hasHamiltonian_iff :
    (∃ F, Φ.HasHamiltonian σ F) ↔ ∀ t : unitInterval, ∃ H : M → ℝ,
      MDifferentiable J 𝓘(ℝ) H ∧ σ.IsHamiltonianVectorField H (Φ.velocity t) := by
  refine ⟨fun ⟨F, hF⟩ t ↦ ⟨_, ?_, hF.isHamiltonianVectorField_velocity t⟩, fun h ↦ ?_⟩
  · exact ((hF.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).comp
      (Φ.timeSlice t).symm.contMDiff).mdifferentiable (by simp)
  rcases isEmpty_or_nonempty M with _ | ⟨⟨x₀⟩⟩
  · exact ⟨0, hasHamiltonian_iff.2 ⟨contMDiff_const, fun p ↦ isEmptyElim p.1⟩⟩
  -- The functions `H_t ∘ φ_t` are primitives of the slices of `ι_{∂ₜ} Φ^* σ`, which the smooth
  -- selection of primitives assembles into one smooth function on the cylinder.
  have hslice (t : unitInterval) : ∃ f : M → ℝ, MDifferentiable J 𝓘(ℝ) f ∧
      ∀ (x : M) (v : E), mvfderiv J f x v =
        timeContraction σ Φ (x, t) ![(v, (0 : EuclideanSpace ℝ (Fin 1)))] := by
    obtain ⟨H, hH, hX⟩ := h t
    exact ⟨H ∘ Φ.timeSlice t, hH.comp ((Φ.timeSlice t).contMDiff.mdifferentiable (by simp)),
      mvfderiv_comp_timeSlice_eq_interior_mpullback_cylinderMap hX⟩
  obtain ⟨F, hF, -, hFB⟩ := exists_contMDiff_mvfderiv_eq_of_forall_exists
    isSmoothForm_interior_mpullback_cylinderMap hslice x₀
  refine ⟨F, hasHamiltonian_iff.2 ⟨hF, fun p v ↦ ?_⟩⟩
  refine Eq.trans ?_
    ((hF.mdifferentiableAt (by simp)).mvfderiv_prod_eq_apply_of_snd_eq_zero (v := (v, 0)) rfl).symm
  rw [hFB, timeContraction, RoughForm.interior_apply, verticalField_apply, Prod.mk.eta]
  -- The two sides agree up to the implicit base points `(p.1, p.2).2` and `p.2` of the unit time
  -- vector, which are equal by eta for pairs.
  rfl

/-- **Hamiltonian diffeotopies by their velocity fields.** A diffeotopy is Hamiltonian exactly when
every map `φ_t` preserves `σ` and at every time `t` its velocity field is the Hamiltonian vector
field of a differentiable function. -/
theorem isHamiltonian_iff_forall_isHamiltonianVectorField_velocity :
    Φ.IsHamiltonian σ ↔ (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) ∧
      ∀ t : unitInterval, ∃ H : M → ℝ,
        MDifferentiable J 𝓘(ℝ) H ∧ σ.IsHamiltonianVectorField H (Φ.velocity t) := by
  rw [isHamiltonian_iff, exists_hasHamiltonian_iff]

end Diffeotopy

end TauCeti
