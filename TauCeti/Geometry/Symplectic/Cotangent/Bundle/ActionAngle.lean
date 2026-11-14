/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

/-!
# The linear cotangent space covers the cotangent bundle of a torus

Let `p > 0` and let `Tⁿ = ι → AddCircle p` be the torus, a manifold whose tangent space at every
point is `ι → ℝ`. A covector of `Tⁿ` at `[θ]` is therefore a continuous linear form `ℓ` on
`ι → ℝ`, and the map

`(θ, ℓ) ↦ ℓ at [θ]`

(`TauCeti.CotangentBundle.torusCover p`) from the linear cotangent space
`(ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)` onto `T*Tⁿ` is the cotangent lift of the covering map
`ℝⁿ → Tⁿ`, `θ ↦ ([θ i])ᵢ`. This file proves that it is a surjective smooth local diffeomorphism
whose fibres are the translates of the angles by `p ℤ^ι`, and that it is symplectic: it pulls the
canonical form `ω = -dλ` of `T*Tⁿ` (`TauCeti.CotangentBundle.symplecticForm`) back to the linear
form `TauCeti.strongDualCotangentSymplecticForm`, `ω((δθ, δℓ), (δθ', δℓ')) = δℓ'(δθ) - δℓ(δθ')`.
Writing `ℓ = ∑ᵢ Iᵢ dθᵢ`, with actions `Iᵢ = ℓ(eᵢ)`, this is `ω = ∑ᵢ dθᵢ ∧ dIᵢ`: these are the
action–angle coordinates of the model `T*Tⁿ` of the Liouville–Arnold theorem.

The proof computes the Liouville form: the cover lies over `θ ↦ [θ]`, whose derivative is the
identity (`AddCircle.hasMFDerivAt_coe_pi`), so it pulls `λ` back to the linear Liouville form
`TauCeti.cotangentLiouvilleForm`, `(δθ, δℓ) ↦ ℓ(δθ)`, and `ω = -dλ` follows from the linear
identity `TauCeti.neg_extDeriv_cotangentLiouvilleForm_apply`. Smoothness uses that the tangent
trivializations of `Tⁿ` are the identity (`AddCircle.symmL_trivializationAt_pi`).

## Main definitions

* `TauCeti.CotangentBundle.torusCover p`: the cover `(θ, ℓ) ↦ ℓ at [θ]` of `T*Tⁿ`.

## Main results

* `TauCeti.CotangentBundle.contMDiff_torusCover`,
  `TauCeti.CotangentBundle.isLocalDiffeomorph_torusCover`: it is a smooth local diffeomorphism.
* `TauCeti.CotangentBundle.torusCover_surjective`,
  `TauCeti.CotangentBundle.torusCover_eq_torusCover_iff`: it is onto, and identifies two points
  exactly when their angles differ by `p ℤ^ι` and their covectors agree.
* `TauCeti.CotangentBundle.mpullback_torusCover_liouvilleForm`: it pulls the Liouville form back
  to the linear Liouville form.
* `TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_torusCover`: it pulls the canonical
  symplectic form back to the linear one.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action–angle variables).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 2 and 18.
-/

public section

noncomputable section

open Bundle Set Filter Function
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι]

/-- The cover of the cotangent bundle of the torus `ι → AddCircle p` by the linear cotangent space
`(ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)`: the pair `(θ, ℓ)` is sent to the covector `ℓ` at `[θ]`, the tangent
spaces of the torus being `ι → ℝ`. It is the cotangent lift of the covering map `θ ↦ [θ]`. -/
def torusCover (q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (fun i ↦ (q.1 i : AddCircle p)) q.2

@[simp]
theorem proj_torusCover (q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :
    (torusCover p q).proj = fun i ↦ (q.1 i : AddCircle p) :=
  (rfl)

@[simp]
theorem torusCover_snd (q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :
    (torusCover p q).2 = q.2 :=
  (rfl)

/-- The cover of `T*Tⁿ` by the linear cotangent space is smooth. -/
theorem contMDiff_torusCover :
    ContMDiff 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (torusCover (ι := ι) p) := by
  intro q₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨(AddCircle.contMDiff_coe_pi p (ι := ι) ∞).contMDiffAt.comp q₀
    contDiff_fst.contMDiff.contMDiffAt, ?_⟩
  -- Near `q₀` the base point stays in the chart at `[q₀.1]`, where the tangent trivialization of
  -- the torus is the identity, so the fibre coordinate is the covector `q.2` itself.
  have hsrc : ∀ᶠ q in 𝓝 q₀, (torusCover p q).proj ∈
      (chartAt (ModelPi fun _ : ι ↦ ℝ) (torusCover p q₀).proj).source :=
    ((AddCircle.contMDiff_coe_pi p (ι := ι) ∞).continuous.comp
      continuous_fst).continuousAt.preimage_mem_nhds
      ((chartAt _ _).open_source.mem_nhds (mem_chart_source _ _))
  refine contDiff_snd.contMDiff.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with q hq
  ext v
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    AddCircle.symmL_trivializationAt_pi p _ hq]
  -- The cotangent fibre is a type synonym of `(ι → ℝ) →L[ℝ] ℝ`, on which
  -- `ContinuousLinearMap.comp_id` does not match; composing with the identity is the identity.
  rfl

/-- The base point of the cover of `T*Tⁿ` depends on the angles alone, with derivative the
first projection `(δθ, δℓ) ↦ δθ`. -/
theorem hasMFDerivAt_proj_torusCover (q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :
    HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun q ↦ (torusCover p q).proj) q
      (ContinuousLinearMap.fst ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)) :=
  (AddCircle.hasMFDerivAt_coe_pi p q.1).comp q
    (ContinuousLinearMap.fst ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)).hasMFDerivAt

/-- **The cover of `T*Tⁿ` pulls the Liouville form back to the linear Liouville form**
`(δθ, δℓ) ↦ ℓ(δθ)` at `(θ, ℓ)`, that is `λ = ∑ᵢ Iᵢ dθᵢ`. -/
theorem mpullback_torusCover_liouvilleForm :
    mpullback 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusCover p)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)).1 =
      cotangentLiouvilleForm := by
  funext q
  ext v
  rw [mpullback_liouvilleForm_apply_of_proj_comp_eq (fun _ ↦ rfl)
    (((contMDiff_torusCover p) q).mdifferentiableAt (by simp)),
    (hasMFDerivAt_proj_torusCover p q).mfderiv]
  exact (cotangentLiouvilleForm_apply q v).symm

/-- **The cover of `T*Tⁿ` is symplectic.** It pulls the canonical symplectic form `ω = -dλ` of
`T*Tⁿ` back to the linear form `TauCeti.strongDualCotangentSymplecticForm`,
`((δθ, δℓ), (δθ', δℓ')) ↦ δℓ'(δθ) - δℓ(δθ')`, that is `ω = ∑ᵢ dθᵢ ∧ dIᵢ` for the actions
`Iᵢ = ℓ(eᵢ)`. -/
theorem eval₂_symplecticForm_mfderiv_torusCover (q : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
    (v w : TangentSpace 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) q) :
    SmoothBundleForm.eval₂ (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (ι → AddCircle p)) (torusCover p q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusCover p) q v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusCover p) q w) =
      strongDualCotangentSymplecticForm v w := by
  refine (SmoothForm.eval₂_mpullback (torusCover p) (contMDiff_torusCover p) _ q v w).symm.trans ?_
  -- Pullback commutes with the exterior derivative, so `ψ^*ω = -d(ψ^*λ)`.
  rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    SmoothBundleForm.eval₂_apply, NegMemClass.coe_neg, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, mextDerivₗ_apply, SmoothForm.coe_mpullback,
    mpullback_torusCover_liouvilleForm]
  -- Over the model space the manifold exterior derivative is the flat one, and `-dλ = ω` for the
  -- linear Liouville form.
  have h := mextDeriv_eq_extDeriv (E := (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) (F := ℝ) (k := 1)
    cotangentLiouvilleForm q
  rw [h]
  exact neg_extDeriv_cotangentLiouvilleForm_apply q ![v, w]

/-- **The cover of `T*Tⁿ` is a local diffeomorphism.** Its differential is injective, since it
pulls the nondegenerate form `ω` back to the nondegenerate linear form, and source and target have
the same dimension. -/
theorem isLocalDiffeomorph_torusCover :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (torusCover (ι := ι) p) := by
  intro q
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_torusCover p).contMDiffOn isOpen_univ
    (mem_univ q) BoundarylessManifold.isInteriorPoint (by simp) ?_ rfl
  rw [injective_iff_map_eq_zero]
  intro v hv
  refine strongDualCotangentSymplecticForm.nondegenerate.1 v fun w ↦ ?_
  have h := eval₂_symplecticForm_mfderiv_torusCover p q v w
  rw [hv] at h
  refine h.symm.trans ?_
  exact SmoothBundleForm.eval₂_zero_left _ _ _

/-- **The fibres of the cover of `T*Tⁿ`.** Two points have the same image exactly when their
angles differ by `p ℤ^ι` and their covectors agree. -/
theorem torusCover_eq_torusCover_iff {q q' : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)} :
    torusCover p q = torusCover p q' ↔
      (∃ m : ι → ℤ, q'.1 = q.1 + fun i ↦ m i • p) ∧ q'.2 = q.2 := by
  constructor
  · intro h
    have h1 := congrArg TotalSpace.proj h
    -- All fibres of `T*Tⁿ` are the type `(ι → ℝ) →L[ℝ] ℝ`, so the covectors can be compared.
    have h2 : q.2 = q'.2 := congrArg (fun z ↦ (z.2 : (ι → ℝ) →L[ℝ] ℝ)) h
    refine ⟨?_, h2.symm⟩
    have hm (i : ι) : ∃ m : ℤ, q'.1 i = q.1 i + m • p := by
      have h := congrFun h1 i
      simp only [proj_torusCover] at h
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h)
      exact ⟨m, by rw [hm]; abel⟩
    choose m hm using hm
    exact ⟨m, funext hm⟩
  · rintro ⟨⟨m, hm⟩, h2⟩
    refine CotangentBundle.ext (funext fun i ↦ ?_) fun v ↦
      congrArg (fun ℓ : (ι → ℝ) →L[ℝ] ℝ ↦ ℓ v) h2.symm
    simp only [proj_torusCover, hm, Pi.add_apply]
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simp)

/-- The cover of `T*Tⁿ` by the linear cotangent space is onto. -/
theorem torusCover_surjective : Surjective (torusCover (ι := ι) p) := by
  intro z
  choose θ hθ using fun i ↦ QuotientAddGroup.mk_surjective (z.proj i)
  exact ⟨(θ, z.2), CotangentBundle.ext (funext hθ) fun _ ↦ rfl⟩

end CotangentBundle

end TauCeti
