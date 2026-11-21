/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.Translate
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Symplectic.Darboux.Momenta

/-!
# Action–angle coordinates on the cotangent bundle of a torus

Let `p > 0` and let `Tⁿ = ι → AddCircle p` be the torus, with coordinate time forms `dθ_j`
(`TauCeti.torusTimeForm`). Its cotangent bundle `T*Tⁿ` is the model of the Liouville–Arnold
theorem: a covector `ξ` over `[θ]` is determined by its **actions** `I_j = ξ(e_j)`, its values on
the coordinate vectors, and then `ξ = ∑ j, I_j dθ_j`. This file studies the corresponding map

`κ : ℝ^ι × ℝ^ι → T*Tⁿ`, `κ(θ, I) = ∑ j, I_j dθ_j` at `[θ]`

(`TauCeti.CotangentBundle.actionAngleCover`), which reads a covector in angle coordinates
`θ ∈ ℝ^ι`, defined modulo `p ℤ^ι`, and action coordinates `I ∈ ℝ^ι`.

* The actions `I_j = ξ(e_j)` of a covector (`TauCeti.CotangentBundle.torusActions`) of `κ(θ, I)`
  are `I` (`TauCeti.CotangentBundle.torusActions_actionAngleCover`).
* `κ` is surjective, and `κ(θ, I) = κ(θ', I')` exactly when `I' = I` and `θ' - θ ∈ p ℤ^ι`
  (`TauCeti.CotangentBundle.surjective_actionAngleCover`,
  `TauCeti.CotangentBundle.actionAngleCover_eq_actionAngleCover_iff`).
* `κ` is smooth, and it pulls the Liouville form `λ` back to `∑ j, I_j dθ_j`
  (`TauCeti.CotangentBundle.mpullback_liouvilleForm_actionAngleCover_apply`) and the canonical
  symplectic form `ω = -dλ` back to `∑ j, dθ_j ∧ dI_j`
  (`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleCover`).
* Since `∑ j, dθ_j ∧ dI_j` is nondegenerate, `κ` is a local diffeomorphism
  (`TauCeti.CotangentBundle.isLocalDiffeomorph_actionAngleCover`). Hence the action map is smooth
  (`TauCeti.CotangentBundle.contMDiff_torusActions`), since its composite with `κ` is the
  projection `(θ, I) ↦ I`.

So `(θ mod p, I)` are global coordinates on `T*Tⁿ` in which `ω = ∑ j, dθ_j ∧ dI_j`. These are the
coordinates in which the Liouville–Arnold theorem states its normal form near a compact regular
level of an integrable system.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action–angle variables).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι]

/-- The **action–angle covering map** of the cotangent bundle of the torus `ι → AddCircle p`: it
sends angles `θ` and actions `I` to the covector `∑ j, I_j dθ_j` at the point `[θ]` of the
torus. -/
def actionAngleCover (x : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (fun i ↦ (x.1 i : AddCircle p))
    (∑ j, x.2 j • SmoothForm.degreeOneEquiv (torusTimeForm (fun _ ↦ p) j)
      (fun i ↦ (x.1 i : AddCircle p)))

/-- The action–angle covering map lies over the covering map `θ ↦ [θ]` of the torus. -/
@[simp]
theorem proj_actionAngleCover (x : (ι → ℝ) × (ι → ℝ)) :
    (actionAngleCover p x).proj = fun i ↦ (x.1 i : AddCircle p) :=
  (rfl)

/-- The covector `κ(θ, I)` evaluates a tangent vector `v : ι → ℝ` of the torus as
`∑ j, I_j * v_j`. -/
@[simp]
theorem actionAngleCover_snd_apply (x : (ι → ℝ) × (ι → ℝ)) (v : ι → ℝ) :
    (actionAngleCover p x).snd v = ∑ j, x.2 j * v j := by
  -- Read `v` as a tangent vector at `[θ]`, where the fibrewise sum is evaluated termwise.
  let w : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (fun i ↦ (x.1 i : AddCircle p)) := v
  refine (sum_apply Finset.univ (fun j ↦ x.2 j • SmoothForm.degreeOneEquiv
    (torusTimeForm (fun _ ↦ p) j) (fun i ↦ (x.1 i : AddCircle p))) w).trans
    (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [smul_apply, SmoothForm.degreeOneEquiv_apply_apply_vec, torusTimeForm_apply]
  -- Definitionally `w = v`, and `•` on `ℝ` is `*`.
  rfl

/-- The **actions** of a covector `ξ` of the torus `ι → AddCircle p`: its values `ξ(e_j)` on the
coordinate vectors. -/
def torusActions [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) : ι → ℝ :=
  fun j ↦ z.snd (Pi.single j 1)

/-- The `j`-th action of a covector is its value on the `j`-th coordinate vector. -/
theorem torusActions_apply [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (j : ι) :
    torusActions p z j = z.snd (Pi.single j 1) :=
  (rfl)

/-- **The actions of `κ(θ, I)` are `I`.** The covector `κ(θ, I)` takes the value `I_j` on the
`j`-th coordinate vector of the torus. -/
@[simp]
theorem torusActions_actionAngleCover [DecidableEq ι] (x : (ι → ℝ) × (ι → ℝ)) :
    torusActions p (actionAngleCover p x) = x.2 :=
  funext fun j ↦ by simp [torusActions_apply, Pi.single_apply]

/-- In action–angle coordinates the action map is the projection `(θ, I) ↦ I`. -/
@[simp]
theorem torusActions_comp_actionAngleCover [DecidableEq ι] :
    torusActions p ∘ actionAngleCover (ι := ι) p = Prod.snd :=
  funext (torusActions_actionAngleCover p)

/-- **The fibres of the action–angle covering map.** Two pairs of angles and actions give the same
covector exactly when they have the same actions and their angles differ by an element of
`p ℤ^ι`. -/
theorem actionAngleCover_eq_actionAngleCover_iff {x y : (ι → ℝ) × (ι → ℝ)} :
    actionAngleCover p x = actionAngleCover p y ↔
      y.2 = x.2 ∧ ∃ m : ι → ℤ, y.1 = x.1 + fun i ↦ m i * p := by
  -- Equal base points are angles differing by `p ℤ^ι`.
  have hbase : ((fun i ↦ (x.1 i : AddCircle p)) = fun i ↦ (y.1 i : AddCircle p)) ↔
      ∃ m : ι → ℤ, y.1 = x.1 + fun i ↦ m i * p := by
    simp only [funext_iff, Pi.add_apply]
    refine ⟨fun h ↦ ?_, fun ⟨m, hm⟩ i ↦ ?_⟩
    · choose m hm using fun i ↦ (AddCircle.coe_eq_zero_iff (p := p)).1
        (by rw [AddCircle.coe_sub, h i, sub_self] : ((y.1 i - x.1 i : ℝ) : AddCircle p) = 0)
      exact ⟨m, fun i ↦ by rw [← zsmul_eq_mul, hm i]; ring⟩
    · rw [hm i, AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period,
        smul_zero, add_zero]
  classical
  refine ⟨fun h ↦ ⟨?_, hbase.1 (congrArg TotalSpace.proj h)⟩,
    fun ⟨h2, h1⟩ ↦ CotangentBundle.ext (hbase.2 h1) fun v ↦ ?_⟩
  · -- Compare the actions.
    simpa using (congrArg (torusActions p) h).symm
  · exact (actionAngleCover_snd_apply p x v).trans
      ((congrArg (fun I : ι → ℝ ↦ ∑ j, I j * v j) h2.symm).trans
        (actionAngleCover_snd_apply p y v).symm)

/-- The action–angle covering map is periodic in the angles, with period `p` in each angle. -/
theorem actionAngleCover_add_intCast_mul (θ I : ι → ℝ) (m : ι → ℤ) :
    actionAngleCover p ((θ + fun i ↦ m i * p), I) = actionAngleCover p (θ, I) :=
  ((actionAngleCover_eq_actionAngleCover_iff p).2 ⟨rfl, -m, by
    ext i
    simp only [Pi.add_apply, Pi.neg_apply, Int.cast_neg]
    ring⟩)

/-- **The action–angle covering map is surjective.** Every covector of the torus is `∑ j, I_j dθ_j`
at some `[θ]`, its actions being `I`. -/
theorem surjective_actionAngleCover :
    Surjective (actionAngleCover (ι := ι) p) := by
  classical
  intro z
  obtain ⟨θ, hθ⟩ : ∃ θ : ι → ℝ, (fun i ↦ (θ i : AddCircle p)) = z.proj :=
    ⟨fun i ↦ (QuotientAddGroup.mk_surjective (z.proj i)).choose,
      funext fun i ↦ (QuotientAddGroup.mk_surjective (z.proj i)).choose_spec⟩
  refine ⟨(θ, torusActions p z), CotangentBundle.ext hθ fun v ↦ ?_⟩
  -- A covector is determined by its values on the coordinate vectors.
  refine (actionAngleCover_snd_apply p _ v).trans ?_
  refine ((LinearMap.pi_apply_eq_sum_univ z.snd.toLinearMap v).trans ?_).symm
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [← Pi.single_apply, Pi.single_comm, smul_eq_mul, mul_comm]
  -- `z.2` is a covector on the tangent space, a type synonym of `ι → ℝ`.
  rfl

/-- **The action–angle covering map is smooth.** -/
theorem contMDiff_actionAngleCover :
    ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (actionAngleCover (ι := ι) p) := by
  -- The base map `(θ, I) ↦ [θ]` is the smooth covering map of the torus after `fst`.
  have hb := (AddCircle.contMDiff_coe_pi (ι := ι) p ∞).comp
    (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).contMDiff
  refine ContMDiff.sum_sectionAlong Finset.univ _ hb fun j _ ↦ ?_
  -- Each term is a smooth coefficient times the smooth section `dθ_j` along the base map.
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).comp
    (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).contMDiff.smul_totalSpace
    ((SmoothForm.degreeOneEquiv (torusTimeForm (fun _ ↦ p) j)).contMDiff.comp hb)

/-- **The tautological form in action–angle coordinates.** The action–angle covering map pulls the
Liouville form `λ` back to `∑ j, I_j dθ_j`: at `(θ, I)` it evaluates a tangent vector `(a, b)` as
`∑ j, I_j * a_j`. -/
theorem mpullback_liouvilleForm_actionAngleCover_apply (x : (ι → ℝ) × (ι → ℝ))
    (v : Fin 1 → TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) x) :
    mpullback 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (actionAngleCover p)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)).val x v =
      ∑ j, x.2 j * (v 0).1 j := by
  -- The base map `(θ, I) ↦ [θ]` is the covering map of the torus after `fst`, so its derivative
  -- is `fst`.
  have hb (u : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) x) :
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (fun x : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (x.1 i : AddCircle p)) x u = u.1 :=
    DFunLike.congr_fun ((AddCircle.hasMFDerivAt_coe_pi (ι := ι) p x.1).comp x
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).hasMFDerivAt).mfderiv u
  rw [mpullback_liouvilleForm_apply_of_proj_comp_eq (g := fun x : (ι → ℝ) × (ι → ℝ) ↦
      fun i ↦ (x.1 i : AddCircle p)) (fun _ ↦ rfl)
      (((contMDiff_actionAngleCover p) x).mdifferentiableAt (by simp)),
    hb, actionAngleCover_snd_apply]

/-- The one-form `(θ, I) ↦ ∑ j, I_j dθ_j` on `ℝ^ι × ℝ^ι`, as a continuous linear function of the
point. -/
private def actionAngleLiouvilleCLM :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (((ι → ℝ) × (ι → ℝ)) [⋀^Fin 1]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := (ι → ℝ) × (ι → ℝ)) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (∑ j, ((StrongDual.smulRightL ℝ ((ι → ℝ) × (ι → ℝ)) ℝ
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)))).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))))

private theorem actionAngleLiouvilleCLM_apply (x : (ι → ℝ) × (ι → ℝ))
    (v : Fin 1 → (ι → ℝ) × (ι → ℝ)) :
    actionAngleLiouvilleCLM x v = ∑ j, x.2 j * (v 0).1 j := by
  simp [actionAngleLiouvilleCLM, mul_comm]

/-- The one-form `(θ, I) ↦ ∑ j, I_j dθ_j` on `ℝ^ι × ℝ^ι`, as a form on the model space. -/
private def actionAngleLiouville : RoughForm 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ((ι → ℝ) × (ι → ℝ)) ℝ 1 :=
  fun x ↦ actionAngleLiouvilleCLM x

/-- Evaluated on a fixed vector, the one-form `∑ j, I_j dθ_j` is the linear function
`(θ, I) ↦ ∑ j, I_j * u_j` of the point. -/
private theorem hasFDerivAt_actionAngleLiouvilleCLM_apply (u : Fin 1 → (ι → ℝ) × (ι → ℝ))
    (x : (ι → ℝ) × (ι → ℝ)) :
    HasFDerivAt (fun y ↦ actionAngleLiouvilleCLM y u)
      (∑ j, (u 0).1 j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))) x := by
  have h : (fun y ↦ actionAngleLiouvilleCLM y u) =
      ⇑(∑ j, (u 0).1 j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))) := by
    funext y
    simp [actionAngleLiouvilleCLM_apply, mul_comm]
  rw [h]
  exact ContinuousLinearMap.hasFDerivAt _

/-- The exterior derivative of `∑ j, I_j dθ_j` is `∑ j, dI_j ∧ dθ_j`. -/
private theorem extDeriv_actionAngleLiouville_apply (x v w : (ι → ℝ) × (ι → ℝ)) :
    extDeriv (E := (ι → ℝ) × (ι → ℝ)) (F := ℝ) actionAngleLiouville x ![v, w] =
      ∑ j, (v.2 j * w.1 j - w.2 j * v.1 j) := by
  refine (extDeriv_apply (actionAngleLiouvilleCLM (ι := ι)).differentiableAt ![v, w]).trans ?_
  rw [Fin.sum_univ_two, (hasFDerivAt_actionAngleLiouvilleCLM_apply _ x).fderiv,
    (hasFDerivAt_actionAngleLiouvilleCLM_apply _ x).fderiv]
  simp [Fin.removeNth, sub_eq_add_neg, Finset.sum_add_distrib, mul_comm]

/-- **The symplectic form in action–angle coordinates.** The action–angle covering map pulls the
canonical symplectic form `ω = -dλ` of the cotangent bundle of the torus back to
`∑ j, dθ_j ∧ dI_j`: on tangent vectors `(a, b)` and `(a', b')` it takes the value
`∑ j, (a_j * b'_j - a'_j * b_j)`. -/
theorem eval₂_symplecticForm_mfderiv_actionAngleCover (x : (ι → ℝ) × (ι → ℝ))
    (v w : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) x) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (actionAngleCover p x)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (actionAngleCover p) x v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (actionAngleCover p) x w) =
      ∑ j, (v.1 j * w.2 j - w.1 j * v.2 j) := by
  have hκ := contMDiff_actionAngleCover (ι := ι) p
  -- The pulled-back Liouville form is the linear form `∑ j, I_j dθ_j`.
  have hpull : (SmoothForm.mpullback (actionAngleCover p) hκ
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))).val =
      actionAngleLiouville := by
    funext y
    ext u
    rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_actionAngleCover_apply]
    exact (actionAngleLiouvilleCLM_apply y u).symm
  -- `ω = -dλ`, and `d` commutes with the pullback along `κ`.
  have h := SmoothForm.mextDeriv_mpullback_apply_two (actionAngleCover p) hκ
    (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) x v w
  rw [hpull, mextDeriv_eq_extDeriv] at h
  rw [SmoothBundleForm.eval₂_apply, symplecticForm_eq_neg_mextDeriv, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, ← h]
  refine (congrArg Neg.neg (extDeriv_actionAngleLiouville_apply x v w)).trans ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The action–angle covering map is a local diffeomorphism.** Its pullback
`∑ j, dθ_j ∧ dI_j` of the canonical symplectic form is nondegenerate, so its differential is
injective, between spaces of the same dimension. -/
theorem isLocalDiffeomorph_actionAngleCover :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (actionAngleCover (ι := ι) p) := by
  classical
  intro x
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_actionAngleCover p).contMDiffOn
    isOpen_univ (Set.mem_univ x) BoundarylessManifold.isInteriorPoint (by simp)
    ((injective_iff_map_eq_zero _).2 fun v hv ↦ ?_)
    (by simp only [Module.finrank_prod, ContinuousLinearMap.dual_finrank_eq])
  -- A vector killed by the differential pairs to zero with every vector under `∑ dθ_j ∧ dI_j`.
  have h (w : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) x) :
      ∑ j, (v.1 j * w.2 j - w.1 j * v.2 j) = 0 :=
    (eval₂_symplecticForm_mfderiv_actionAngleCover p x v w).symm.trans (by
      rw [hv, eval₂_symplecticForm]
      exact LinearMap.map_zero₂ _ _)
  exact eq_of_forall_sum_mul_sub_mul_eq (c := (0 : (ι → ℝ) × (ι → ℝ))) fun w ↦ by
    simpa using h w

/-- The action map of the cotangent bundle of the torus is smooth. -/
theorem contMDiff_torusActions [DecidableEq ι] :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ, ι → ℝ) ∞ (torusActions (ι := ι) p) := by
  rw [← (isLocalDiffeomorph_actionAngleCover (ι := ι) p).contMDiff_comp_iff
    (surjective_actionAngleCover p) le_rfl, torusActions_comp_actionAngleCover]
  exact contMDiff_iff_contDiff.2 contDiff_snd

/-- A function of the actions is differentiable where its profile is differentiable at the actions.
-/
theorem mdifferentiableAt_comp_torusActions [DecidableEq ι] {h : (ι → ℝ) → ℝ}
    {z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
    (hh : DifferentiableAt ℝ h (torusActions p z)) :
    MDifferentiableAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ)
      (h ∘ torusActions p) z :=
  hh.mdifferentiableAt.comp z ((contMDiff_torusActions p z).mdifferentiableAt (by simp))

end CotangentBundle

end TauCeti
