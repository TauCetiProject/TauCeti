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
one. The product of calibrated frames of the two factors is a calibrated frame of the external
product. These are the pointwise inputs for products of calibrations on Riemannian products.

The decomposable case follows Harvey and Lawson. Let `u` be an orthonormal frame of `E ⊕ F`
spanning `W`, and `ψ` the form of `w₁ ∧ ⋯ ∧ w_l`. The vectors of `W` whose second component is
orthogonal to every `wⱼ` form a subspace of dimension at least `k`; choose an orthonormal basis
of `W` whose first `k` vectors lie in it. On that basis the value of `φ ⊠ ψ` splits as a value of
`φ` times a value of `ψ`, and its absolute value is at least `|(φ ⊠ ψ)(u)|`, because both frames
are orthonormal bases of `W`.

## Main results

* `ContinuousAlternatingMap.norm_externalProduct_alternatingFormEquiv_ιMulti` and
  `ContinuousAlternatingMap.norm_alternatingFormEquiv_ιMulti_externalProduct`: with a decomposable
  factor on either side the comass is the product of the comasses.
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

/-- An orthonormal `(k + l)`-frame `u` of `E ⊕ F` can be replaced by an orthonormal frame `(a, b)`
whose first `k` vectors have second components orthogonal to the `l` vectors `w`, without
decreasing the absolute value of any `(k + l)`-form. Both frames are orthonormal bases of the span
of `u`; the vectors `a` are chosen in the subspace of that span cut out by the `l` linear
conditions `⟪wⱼ, ·.snd⟫ = 0`, which has dimension at least `k`. -/
private lemma exists_orthonormal_append_le_of_orthonormal (w : Fin l → F)
    {u : Fin (k + l) → WithLp 2 (E × F)} (hu : Orthonormal ℝ u) :
    ∃ (a : Fin k → WithLp 2 (E × F)) (b : Fin l → WithLp 2 (E × F)),
      Orthonormal ℝ (Fin.append a b) ∧ (∀ i j, ⟪w j, (a i).snd⟫ = 0) ∧
      ∀ Φ : WithLp 2 (E × F) [⋀^Fin (k + l)]→L[ℝ] ℝ, |Φ u| ≤ |Φ (Fin.append a b)| := by
  classical
  let W := Submodule.span ℝ (Set.range u)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range u)
  have hW : finrank ℝ W = k + l := by simpa using finrank_span_eq_card hu.linearIndependent
  let L : W →ₗ[ℝ] Fin l → ℝ := LinearMap.pi fun j ↦
    (innerSL ℝ (w j)).toLinearMap ∘ₗ (WithLp.sndL 2 ℝ E F).toLinearMap ∘ₗ W.subtype
  have hK : k ≤ finrank ℝ (LinearMap.ker L) := by
    have h₁ := L.finrank_range_add_finrank_ker
    have h₂ : finrank ℝ (LinearMap.range L) ≤ l := by
      simpa using Submodule.finrank_le (LinearMap.range L)
    omega
  let B := stdOrthonormalBasis ℝ (LinearMap.ker L)
  let a₀ : Fin k → W := fun i ↦ B (Fin.castLE hK i)
  have ha₀ : Orthonormal ℝ a₀ :=
    (B.orthonormal.comp _ (Fin.castLE_injective hK)).comp_linearIsometry
      (LinearMap.ker L).subtypeₗᵢ
  let v₀ : Fin (k + l) → W := Fin.append a₀ 0
  have hv₀ : Orthonormal ℝ ((Set.range (Fin.castAdd l)).domRestrict v₀) := by
    rw [orthonormal_iff_ite]
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    simp [v₀, Set.domRestrict, Subtype.ext_iff, orthonormal_iff_ite.1 ha₀ i j]
  obtain ⟨c, hc⟩ := hv₀.exists_orthonormalBasis_extension_of_card_eq (by simp [hW])
  have hcu : Fin.append (fun i ↦ (c (Fin.castAdd l i) : WithLp 2 (E × F)))
      (fun j ↦ (c (Fin.natAdd k j) : WithLp 2 (E × F))) = fun i ↦ (c i : WithLp 2 (E × F)) :=
    Fin.append_castAdd_natAdd (f := fun i ↦ (c i : WithLp 2 (E × F)))
  refine ⟨fun i ↦ c (Fin.castAdd l i), fun j ↦ c (Fin.natAdd k j), ?_, fun i j ↦ ?_,
    fun Φ ↦ ?_⟩
  · rw [hcu]
    exact c.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · have hmem : L (c (Fin.castAdd l i)) = 0 := by
      rw [hc _ (Set.mem_range_self i)]
      simp only [v₀, Fin.append_left]
      exact LinearMap.mem_ker.1 (B (Fin.castLE hK i)).property
    simpa [L] using congr_fun hmem j
  · rw [hcu, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact (Φ.norm_apply_eq_norm_apply_orthonormalBasis_span hu c).le

section Decomposable

variable [FiniteDimensional ℝ F]

/-- **The comass of an external product with a decomposable form** is the product of the
comasses: `‖φ ⊠ ⟪w₁ ∧ ⋯ ∧ w_l, ·⟫‖ = ‖φ‖ ‖w₁ ∧ ⋯ ∧ w_l‖`. -/
theorem norm_externalProduct_alternatingFormEquiv_ιMulti (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (w : Fin l → F) :
    ‖externalProduct φ (TauCeti.alternatingFormEquiv F l (ιMulti ℝ l w))‖ =
      ‖φ‖ * ‖ιMulti ℝ l w‖ := by
  classical
  set ψ := TauCeti.alternatingFormEquiv F l (ιMulti ℝ l w)
  rw [← TauCeti.norm_alternatingFormEquiv_ιMulti w]
  refine le_antisymm ((opNorm_le_iff_le_orthonormal (by positivity)).2 fun u hu ↦ ?_)
    (norm_mul_norm_le_norm_externalProduct φ ψ)
  obtain ⟨a, b, hab, ha, hle⟩ := exists_orthonormal_append_le_of_orthonormal w hu
  have hsplit := externalProduct_apply_append_of_forall φ ψ a b fun y i j ↦
    TauCeti.alternatingFormEquiv_ιMulti_apply_eq_zero_of_forall_inner_eq_zero w _ (i := j)
      (by simpa using ha i)
  have hfst (i : Fin k) : ‖(a i).fst‖ ≤ 1 :=
    (WithLp.norm_fst_le (x := a i)).trans (by simpa using (hab.1 (Fin.castAdd l i)).le)
  have hsnd (j : Fin l) : ‖(b j).snd‖ ≤ 1 :=
    (WithLp.norm_snd_le (x := b j)).trans (by simpa using (hab.1 (Fin.natAdd k j)).le)
  rw [Real.norm_eq_abs]
  calc |externalProduct φ ψ u| ≤ |externalProduct φ ψ (Fin.append a b)| := hle _
    _ = ‖φ fun i ↦ (a i).fst‖ * ‖ψ fun j ↦ (b j).snd‖ := by
      rw [hsplit, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (‖φ‖ * ∏ i, ‖(a i).fst‖) * (‖ψ‖ * ∏ j, ‖(b j).snd‖) := by
      gcongr
      · exact φ.le_opNorm _
      · exact ψ.le_opNorm _
    _ ≤ (‖φ‖ * 1) * (‖ψ‖ * 1) := by
      gcongr
      · exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ hfst i
      · exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ hsnd j
    _ = ‖φ‖ * ‖ψ‖ := by ring

end Decomposable

/-- **The comass of an external product with a decomposable first factor** is the product of
the comasses: `‖⟪w₁ ∧ ⋯ ∧ w_k, ·⟫ ⊠ ψ‖ = ‖w₁ ∧ ⋯ ∧ w_k‖ ‖ψ‖`. -/
theorem norm_alternatingFormEquiv_ιMulti_externalProduct [FiniteDimensional ℝ E] (w : Fin k → E)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖externalProduct (TauCeti.alternatingFormEquiv E k (ιMulti ℝ k w)) ψ‖ =
      ‖ιMulti ℝ k w‖ * ‖ψ‖ := by
  rw [norm_externalProduct_comm, norm_externalProduct_alternatingFormEquiv_ιMulti, mul_comm]

end InnerProduct

end ContinuousAlternatingMap
