/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# Action–angle coordinates on the cotangent bundle of a torus

For a finite family of positive periods `p i`, the tangent space of the torus
`Tⁿ = ∀ i, AddCircle (p i)` at every point is `ι → ℝ`, and the coordinate time forms `dθ_i`
(`TauCeti.torusTimeForm`) are its coordinate functionals. So a covector `ξ` over `θ ∈ Tⁿ` is
determined by its **actions** `I_i = ξ(e_i)`, its values on the coordinate vectors, and
`ξ = ∑ i, I_i dθ_i`. This file shows that the map

`(θ, I) ↦ ∑ i, I_i dθ_i` at `θ`

(`TauCeti.CotangentBundle.torusActionAngle p`) from `Tⁿ × ℝⁿ` to `T*Tⁿ` is a smooth bijection,
under which the Liouville form is `λ = ∑ i, I_i dθ_i` and the canonical symplectic form is
`ω = -dλ = ∑ i, dθ_i ∧ dI_i`. These are the action–angle coordinates of the cotangent bundle of a
torus, the model of the Liouville–Arnold theorem.

The Liouville form is computed from its definition `λ(v) = ξ(dπ v)`: the projection of
`torusActionAngle p` to the torus is the first projection of `Tⁿ × ℝⁿ`. The symplectic form is
then `-d(∑ i, I_i dθ_i)`, by naturality of the exterior derivative and the Leibniz rule, since the
forms `dθ_i` are closed.

## Main definitions

* `TauCeti.CotangentBundle.torusActionAngle p`: the covector `∑ i, I_i dθ_i` over `θ`.

## Main results

* `TauCeti.CotangentBundle.torusActionAngle_snd_apply_single`: the actions of
  `torusActionAngle p (θ, I)` are `I`.
* `TauCeti.CotangentBundle.torusActionAngle_proj_snd_apply_single`: every covector is
  `torusActionAngle p` of its base point and its actions; with
  `TauCeti.CotangentBundle.torusActionAngle_injective`, the map is a bijection.
* `TauCeti.CotangentBundle.contMDiff_torusActionAngle`: the map is smooth.
* `TauCeti.CotangentBundle.mpullback_torusActionAngle_liouvilleForm`: it pulls `λ` back to
  `∑ i, I_i dθ_i`.
* `TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_torusActionAngle`: it pulls `ω` back to
  `∑ i, dθ_i ∧ dI_i`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (the canonical form `∑ dθ_i ∧ dI_i` in action–angle
  variables).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 2.2 and 18.4.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-- The **action–angle covector** of the torus `Tⁿ = ∀ i, AddCircle (p i)`: the covector
`∑ i, I_i dθ_i` over the point `θ`, for `(θ, I) ∈ Tⁿ × ℝⁿ`. The tangent space of the torus is
`ι → ℝ`, on which `dθ_i` is the `i`-th coordinate functional. -/
def torusActionAngle (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) q.1 (∑ j, q.2 j • ContinuousLinearMap.proj j)

/-- The action–angle covector of `(θ, I)` lies over `θ`. -/
@[simp]
theorem proj_torusActionAngle (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    (torusActionAngle p q).proj = q.1 :=
  (rfl)

/-- The action–angle covector of `(θ, I)` sends a tangent vector `v : ι → ℝ` to
`∑ j, I_j * v_j`. -/
@[simp]
theorem torusActionAngle_snd_apply (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) (v : ι → ℝ) :
    (torusActionAngle p q).2 v = ∑ j, q.2 j * v j := by
  -- The fibre of the cotangent bundle is a type synonym of `(ι → ℝ) →L[ℝ] ℝ`.
  have h : (torusActionAngle p q).2 v =
      (∑ j, q.2 j • ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) v := (rfl)
  simp [h]

/-- The action–angle covector of `(θ, I)` has actions `I`: its value on the `i`-th coordinate
vector is `I_i`. -/
theorem torusActionAngle_snd_apply_single [DecidableEq ι]
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) (i : ι) :
    (torusActionAngle p q).2 (Pi.single i 1) = q.2 i := by
  simp [Pi.single_apply]

/-- Every covector of the torus is the action–angle covector of its base point and its actions. -/
theorem torusActionAngle_proj_snd_apply_single [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    torusActionAngle p (z.proj, fun i ↦ z.2 (Pi.single i 1)) = z := by
  refine CotangentBundle.ext rfl fun v ↦ (torusActionAngle_snd_apply p _ v).trans ?_
  -- A covector on `ι → ℝ` is determined by its values on the coordinate vectors.
  have key (L : (ι → ℝ) →L[ℝ] ℝ) (w : ι → ℝ) : ∑ j, L (Pi.single j 1) * w j = L w := by
    calc ∑ j, L (Pi.single j 1) * w j = ∑ j, L (w j • Pi.single j 1) := by
          simp [mul_comm]
      _ = L (∑ j, w j • Pi.single j 1) := (map_sum L _ _).symm
      _ = L w := by
          congr 1
          ext k
          simp [Pi.single_apply]
  exact key z.2 v

/-- The action–angle covector determines its base point and its actions. -/
theorem torusActionAngle_injective : Function.Injective (torusActionAngle p) := by
  classical
  intro q q' h
  refine Prod.ext (congrArg TotalSpace.proj h) (funext fun i ↦ ?_)
  -- The base points agree, so the two covectors live in the same fibre.
  obtain ⟨θ, I⟩ := q
  obtain ⟨θ', I'⟩ := q'
  obtain rfl : θ = θ' := congrArg TotalSpace.proj h
  have := congrArg (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (∀ i, AddCircle (p i)) ↦ z.2 (Pi.single i 1)) h
  simpa [Pi.single_apply] using this

/-- Every covector of the torus is an action–angle covector. -/
theorem torusActionAngle_surjective : Function.Surjective (torusActionAngle p) := by
  classical
  exact fun z ↦ ⟨_, torusActionAngle_proj_snd_apply_single p z⟩

/-- The `i`-th coordinate time form of the torus, as a covector, is the `i`-th coordinate
functional of the tangent space `ι → ℝ`. -/
private theorem degreeOneEquiv_torusTimeForm (i : ι) (x : ∀ i, AddCircle (p i)) :
    SmoothForm.degreeOneEquiv (torusTimeForm p i) x = ContinuousLinearMap.proj i := by
  ext v
  rw [SmoothForm.degreeOneEquiv_apply_apply, torusTimeForm_apply]
  rfl

/-- The actions `I_j` are smooth functions on `Tⁿ × ℝⁿ`. -/
private theorem contMDiff_snd_apply (j : ι) :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞
      (fun q : (∀ i, AddCircle (p i)) × (ι → ℝ) ↦ q.2 j) :=
  (contDiff_apply (𝕜 := ℝ) (F' := fun _ : ι ↦ ℝ) j).contMDiff.comp contMDiff_snd

/-- The action–angle covector depends smoothly on `(θ, I)`. -/
theorem contMDiff_torusActionAngle :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (torusActionAngle p) := by
  intro q₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_fst, ?_⟩
  -- In coordinates, the covector is the combination with coefficients `I_j` of the coordinate
  -- expressions of the smooth sections `dθ_j`.
  have hsec (j : ι) := (contMDiffAt_hom_bundle _).mp
    ((SmoothForm.degreeOneEquiv (torusTimeForm p j)).contMDiff q₀.1)
  have hj (j : ι) : ContMDiffAt ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ) ∞ (fun q : (∀ i, AddCircle (p i)) × (ι → ℝ) ↦ q.2 j •
        ContinuousLinearMap.inCoordinates (ι → ℝ)
          (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) ℝ (fun _ ↦ ℝ) q₀.1 q.1 q₀.1 q.1
          (SmoothForm.degreeOneEquiv (torusTimeForm p j) q.1)) q₀ := by
    exact (contMDiff_snd_apply p j q₀).smul ((hsec j).2.comp q₀ contMDiffAt_fst)
  have hcoord := contMDiffAt_finsetSum (t := Finset.univ) fun j _ ↦ hj j
  refine hcoord.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ ?_)
  simp only [degreeOneEquiv_torusTimeForm, torusActionAngle, ContinuousLinearMap.inCoordinates]
  ext v
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_apply, sum_apply, smul_apply, smul_eq_mul]
  -- The coordinate functionals act on the tangent space, a type synonym of `ι → ℝ`.
  exact Finset.sum_congr (M := ℝ) rfl fun i _ ↦ (rfl)

/-- **The Liouville form in action–angle coordinates.** The action–angle covector pulls the
Liouville form of the torus back to `∑ i, I_i dθ_i`, where `dθ_i` is pulled back to `Tⁿ × ℝⁿ`
along the first projection. -/
theorem mpullback_torusActionAngle_liouvilleForm :
    (SmoothForm.mpullback (torusActionAngle p) (contMDiff_torusActionAngle p)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 =
      ∑ i, fun q : (∀ i, AddCircle (p i)) × (ι → ℝ) ↦
        q.2 i • (SmoothForm.mpullback Prod.fst contMDiff_fst (torusTimeForm p i)).1 q := by
  funext q
  ext v
  rw [SmoothForm.coe_mpullback,
    mpullback_liouvilleForm_apply_of_proj_comp_eq (g := Prod.fst) (proj_torusActionAngle p)
      ((contMDiff_torusActionAngle p q).mdifferentiableAt (by simp)),
    mfderiv_fst]
  simp only [Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, SmoothForm.mpullback_apply, mfderiv_fst,
    torusTimeForm_apply, smul_eq_mul]
  exact torusActionAngle_snd_apply p q _

/-- **The canonical symplectic form in action–angle coordinates.** The action–angle covector pulls
the canonical symplectic form `ω = -dλ` of the torus back to `∑ i, dθ_i ∧ dI_i`: it pairs the
tangent vectors `(a, b)` and `(a', b')` of `Tⁿ × ℝⁿ` at `(θ, I)` to `∑ i, (a_i b'_i - a'_i b_i)`. -/
theorem eval₂_symplecticForm_mfderiv_torusActionAngle (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (a b a' b' : ι → ℝ) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (torusActionAngle p q)
        (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusActionAngle p) q (a, b))
        (mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusActionAngle p) q (a', b')) =
      ∑ i, (a i * b' i - a' i * b i) := by
  set β : ι → SmoothForm ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      ((∀ i, AddCircle (p i)) × (ι → ℝ)) ℝ 1 :=
    fun i ↦ SmoothForm.mpullback Prod.fst contMDiff_fst (torusTimeForm p i)
  have hcoord := contMDiff_snd_apply p
  -- `ω = -dλ`, and the exterior derivative commutes with the pullback.
  rw [SmoothBundleForm.eval₂_apply, symplecticForm_eq_neg_mextDeriv, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply]
  refine (congrArg Neg.neg (SmoothForm.mextDeriv_mpullback_apply_two (torusActionAngle p)
    (contMDiff_torusActionAngle p) _ q (a, b) (a', b')).symm).trans ?_
  rw [mpullback_torusActionAngle_liouvilleForm,
    mextDeriv_sum _ _ fun i _ ↦ ((β i).isSmoothForm.of_le (by simp)).fun_smul
      ((hcoord i).of_le (by simp))]
  -- The Leibniz rule, with `dθ_i` closed, gives `d (I_i dθ_i) = dI_i ∧ dθ_i`.
  simp only [Finset.sum_apply, ContinuousAlternatingMap.sum_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine (congrArg Neg.neg (mextDeriv_fun_smul_apply ((hcoord i q).mdifferentiableAt (by simp))
    ((β i).mdifferentiableAt q) (a, b) (a', b'))).trans ?_
  have hd (u w : ι → ℝ) :
      mvfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
        (fun q : (∀ i, AddCircle (p i)) × (ι → ℝ) ↦ q.2 i) q (u, w) = w i := by
    refine (mvfderiv_apply_eq_mfderiv_apply _ q (u, w)).trans ?_
    exact (DFunLike.congr_fun
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasMFDerivAt.comp q
        (hasMFDerivAt_snd q)).mfderiv (u, w)).trans (rfl)
  have hβ (u w : ι → ℝ) : (β i).1 q ![(u, w)] = u i := by
    refine (SmoothForm.mpullback_apply_one _ _ _ q (u, w)).trans ?_
    rw [mfderiv_fst, torusTimeForm_apply]
    rfl
  rw [hd, hd, hβ, hβ, (SmoothForm.isClosed_def _).mp
    ((isClosed_torusTimeForm p i).mpullback Prod.fst contMDiff_fst)]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, mul_zero, add_zero]
  ring

end CotangentBundle

end TauCeti
