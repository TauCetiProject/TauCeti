/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.Comass
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ExternalProduct
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Extension
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod

/-!
# External products of forms on orthogonal direct sums

The external product `φ ⊠ ψ = pr₁*φ ∧ pr₂*ψ` of a real `k`-form `φ` on `E` and a real `l`-form
`ψ` on `F` is the `(k + l)`-form `ContinuousAlternatingMap.externalProduct φ ψ` on the `L²`
product `WithLp 2 (E × F)`; its evaluation on product frames and the comass bounds
`‖φ‖ ‖ψ‖ ≤ ‖φ ⊠ ψ‖ ≤ binomial(k + l, k) ‖φ‖ ‖ψ‖` hold for normed spaces and are in
`TauCeti.Analysis.Normed.Module.Alternating.Wedge.ExternalProduct`. This file treats inner
product spaces, where `E ⊕ F` is the orthogonal direct sum. When one factor is decomposable, the
form `⟪w₁ ∧ ⋯ ∧ w_l, ·⟫` of a simple `l`-vector, the lower bound is attained:
`‖φ ⊠ ψ‖ = ‖φ‖ ‖ψ‖`. In particular the external product of a form of comass at most one with a
unit decomposable form, such as the volume form of an oriented subspace, again has comass at most
one. The same equality holds when one factor is of top degree, a multiple of a volume form of its
factor. The product of calibrated frames of the two factors is a calibrated frame of the external
product. These are the pointwise inputs for products of calibrations on Riemannian products.

Both cases follow Harvey and Lawson. Suppose `ψ` vanishes as soon as one of its arguments lies
in the kernel of a linear map `q` from `F` to a space of dimension at most `l`. Let `u` be an
orthonormal frame of `E ⊕ F` spanning `W`. The vectors of `W` whose second component lies in the
kernel of `q` form a subspace of dimension at least `k`; choose an orthonormal basis of `W` whose
first `k` vectors lie in it. On that basis the value of `φ ⊠ ψ` splits as a value of `φ` times a
value of `ψ`, and its absolute value is at least `|(φ ⊠ ψ)(u)|`, because both frames are
orthonormal bases of `W`. For the form `ψ` of `w₁ ∧ ⋯ ∧ w_l`, `q` is given by the `l` coordinates
`⟪wⱼ, ·⟫`; for `ψ` of top degree, `q` is the identity of `F`.

## Main results

* `ContinuousAlternatingMap.norm_externalProduct_of_apply_update_eq_zero`: the comass is the
  product of the comasses when `ψ` vanishes whenever an argument lies in the kernel of a map to a
  space of dimension at most its degree.
* `ContinuousAlternatingMap.norm_externalProduct_alternatingFormEquiv_ιMulti` and
  `ContinuousAlternatingMap.norm_alternatingFormEquiv_ιMulti_externalProduct`: with a decomposable
  factor on either side the comass is the product of the comasses.
* `ContinuousAlternatingMap.norm_externalProduct_of_finrank_le_right` and
  `ContinuousAlternatingMap.norm_externalProduct_of_finrank_le_left`: the same with a top-degree
  factor on either side.
* `ContinuousAlternatingMap.IsCalibratedFrame.externalProduct`: the product of calibrated frames
  is calibrated by the external product.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §II.7,
  Proposition 7.10.
-/

public section

open Module exteriorPower
open scoped RealInnerProductSpace

namespace ContinuousAlternatingMap

section InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {k l : ℕ}

/-- **Products of calibrated frames are calibrated**: if `v` is calibrated by `φ` and `w` by
`ψ`, the product frame `((v₁, 0), …, (v_k, 0), (0, w₁), …, (0, w_l))` is calibrated by `φ ⊠ ψ`. -/
theorem IsCalibratedFrame.externalProduct {φ : E [⋀^Fin k]→L[ℝ] ℝ} {ψ : F [⋀^Fin l]→L[ℝ] ℝ}
    {v : Fin k → E} {w : Fin l → F} (hv : φ.IsCalibratedFrame v) (hw : ψ.IsCalibratedFrame w) :
    (φ.externalProduct ψ).IsCalibratedFrame (Fin.append (fun i ↦ WithLp.toLp 2 (v i, (0 : F)))
      (fun j ↦ WithLp.toLp 2 ((0 : E), w j))) :=
  ⟨TauCeti.orthonormal_append_toLp_iff.2 ⟨hv.orthonormal, hw.orthonormal⟩, by
    simp [hv.apply_eq_one, hw.apply_eq_one]⟩

/-- **The comass of an external product with a form vanishing on a kernel** is the product of
the comasses: `‖φ ⊠ ψ‖ = ‖φ‖ ‖ψ‖` whenever `ψ` vanishes as soon as one of its arguments lies in the
kernel of a linear map `q` from `F` to a space of dimension at most `l`. -/
theorem norm_externalProduct_of_apply_update_eq_zero (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) {G : Type*} [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
    (q : F →ₗ[ℝ] G) (hq : finrank ℝ G ≤ l)
    (hψ : ∀ x, q x = 0 → ∀ (y : Fin l → F) (j : Fin l), ψ (Function.update y j x) = 0) :
    ‖externalProduct φ ψ‖ = ‖φ‖ * ‖ψ‖ := by
  refine le_antisymm ((opNorm_le_iff_le_orthonormal (by positivity)).2 fun u hu ↦ ?_)
    (norm_mul_norm_le_norm_externalProduct φ ψ)
  -- An orthonormal basis of the span of `u` whose first `k` vectors have second components in
  -- the kernel of `q`.
  obtain ⟨c, hc⟩ := hu.exists_orthonormalBasis_span_apply_castAdd_eq_zero
    (q ∘ₗ (WithLp.sndL 2 ℝ E F).toLinearMap) hq
  have hcu : Fin.append (fun i ↦ (c (Fin.castAdd l i) : WithLp 2 (E × F)))
      (fun j ↦ (c (Fin.natAdd k j) : WithLp 2 (E × F))) = fun i ↦ (c i : WithLp 2 (E × F)) :=
    Fin.append_castAdd_natAdd (f := fun i ↦ (c i : WithLp 2 (E × F)))
  have hnorm (i : Fin (k + l)) : ‖(c i : WithLp 2 (E × F))‖ = 1 := by
    rw [Submodule.norm_coe, c.norm_eq_one]
  rw [norm_apply_eq_norm_apply_orthonormalBasis_span _ hu c, ← hcu]
  refine norm_externalProduct_apply_append_le φ ψ (fun i ↦ ?_) (fun j ↦ ?_)
    fun y i j ↦ hψ _ ?_ y j
  · exact (WithLp.norm_fst_le (x := _)).trans (hnorm _).le
  · exact (WithLp.norm_snd_le (x := _)).trans (hnorm _).le
  · simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, WithLp.sndL_apply] using hc i

section Decomposable

variable [FiniteDimensional ℝ F]

/-- **The comass of an external product with a decomposable form** is the product of the
comasses: `‖φ ⊠ ⟪w₁ ∧ ⋯ ∧ w_l, ·⟫‖ = ‖φ‖ ‖w₁ ∧ ⋯ ∧ w_l‖`. -/
theorem norm_externalProduct_alternatingFormEquiv_ιMulti (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (w : Fin l → F) :
    ‖externalProduct φ (TauCeti.alternatingFormEquiv F l (ιMulti ℝ l w))‖ =
      ‖φ‖ * ‖ιMulti ℝ l w‖ := by
  rw [← TauCeti.norm_alternatingFormEquiv_ιMulti w]
  -- The form of `w₁ ∧ ⋯ ∧ w_l` vanishes on the kernel of the `l` coordinates `⟪wⱼ, ·⟫`.
  refine norm_externalProduct_of_apply_update_eq_zero φ _
    (LinearMap.pi fun j ↦ (innerSL ℝ (w j)).toLinearMap) (by simp) fun x hx y j ↦ ?_
  refine TauCeti.alternatingFormEquiv_ιMulti_apply_eq_zero_of_forall_inner_eq_zero w _ (i := j)
    fun j' ↦ ?_
  simpa only [Function.update_self, LinearMap.pi_apply, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, Pi.zero_apply] using congr_fun hx j'

end Decomposable

/-- **The comass of an external product with a decomposable first factor** is the product of
the comasses: `‖⟪w₁ ∧ ⋯ ∧ w_k, ·⟫ ⊠ ψ‖ = ‖w₁ ∧ ⋯ ∧ w_k‖ ‖ψ‖`. -/
theorem norm_alternatingFormEquiv_ιMulti_externalProduct [FiniteDimensional ℝ E] (w : Fin k → E)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖externalProduct (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k w)) ψ‖ =
      ‖ιMulti ℝ k w‖ * ‖ψ‖ := by
  rw [norm_externalProduct_comm, norm_externalProduct_alternatingFormEquiv_ιMulti, mul_comm]

/-- **The comass of an external product with a top-degree form.** If the degree of `ψ` is at
least the dimension of `F`, so that `ψ` is a multiple of a volume form of `F` or zero, then
`‖φ ⊠ ψ‖ = ‖φ‖ ‖ψ‖`. In particular, for a unit volume form `ψ` the external product has the
comass of `φ`. -/
theorem norm_externalProduct_of_finrank_le_right [FiniteDimensional ℝ F] (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) (hl : finrank ℝ F ≤ l) :
    ‖externalProduct φ ψ‖ = ‖φ‖ * ‖ψ‖ :=
  norm_externalProduct_of_apply_update_eq_zero φ ψ LinearMap.id hl fun x hx y j ↦ by
    rw [LinearMap.id_apply] at hx
    rw [hx, ψ.map_update_zero]

/-- **The comass of an external product with a top-degree first factor**: `‖φ ⊠ ψ‖ = ‖φ‖ ‖ψ‖`
when the degree of `φ` is at least the dimension of `E`. -/
theorem norm_externalProduct_of_finrank_le_left [FiniteDimensional ℝ E] (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) (hk : finrank ℝ E ≤ k) :
    ‖externalProduct φ ψ‖ = ‖φ‖ * ‖ψ‖ := by
  rw [norm_externalProduct_comm, norm_externalProduct_of_finrank_le_right ψ φ hk, mul_comm]

end InnerProduct

end ContinuousAlternatingMap
