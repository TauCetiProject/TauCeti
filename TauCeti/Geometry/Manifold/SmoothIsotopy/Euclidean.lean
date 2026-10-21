/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Linear
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Linearization
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Trans

/-!
# The Euclidean disc theorem

Two smooth embeddings between real normed spaces, with finite-dimensional source,
that have the same value at the origin and derivative equivalences with positive
relative determinant are smoothly isotopic, fixing that value throughout. For
self-embeddings, agreement in orientation is expressed by positivity of the product
of their derivative determinants, so both determinants may be negative.

Translate the common centre to zero, linearize both embeddings by rescaling, and
connect the two linear maps through their orientation-preserving relative map.
Smooth concatenation and translation back give the relative isotopy. This is the
Euclidean ambient-space case of the disc theorem, for the open-disc source `ℝⁿ`.
It provides the comparison of embeddings in Euclidean coordinates; it does not assert
an ambient isotopy or compare embeddings into a general manifold.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6,
  Theorem 6.6, p. 117.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.

The construction uses `linearizationIsotopy`,
`ContinuousLinearEquiv.exists_smoothIsotopy`, and `SmoothIsotopy.trans`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Euclidean disc theorem.** Smooth embeddings with a common centre and derivative
equivalences with positive relative determinant are smoothly isotopic relative to that centre.
The source is finite-dimensional; the target needs neither an orientation nor a completeness
instance. -/
theorem exists_smoothIsotopy_of_det_pos
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ E F) (hcentre : f 0 = g 0)
    (Lf Lg : E ≃L[ℝ] F) (hLf : HasFDerivAt f (Lf : E →L[ℝ] F) 0)
    (hLg : HasFDerivAt g (Lg : E →L[ℝ] F) 0)
    (hrelative : 0 < (Lf.trans Lg.symm).toContinuousLinearMap.det) :
    ∃ G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap,
      ∀ t : unitInterval, G (t, 0) = f 0 := by
  let : FiniteDimensional ℝ F := Lf.toLinearEquiv.finiteDimensional
  -- Translate both embeddings to the same zero centre.
  let τ : F ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F :=
    { toFun := fun x => x - f 0
      invFun := fun x => x + f 0
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  have hτ (x : F) : τ x = x - f 0 := by
    rw [← Diffeomorph.coe_toEquiv]
    rfl
  have hτsymm (x : F) : τ.symm x = x + f 0 := by
    rw [← Diffeomorph.toEquiv_coe_symm]
    rfl
  let f' := f.transDiffeomorph τ
  let g' := g.transDiffeomorph τ
  have hf' : (f' : E → F) = fun x => f x - f 0 := by
    funext x
    simp [f', hτ]
  have hg' : (g' : E → F) = fun x => g x - f 0 := by
    funext x
    simp [g', hτ]
  have hf0 : f' 0 = 0 := by rw [hf']; simp
  have hg0 : g' 0 = 0 := by simp [hg', hcentre]
  have hfreg : ContDiff ℝ (↑(⊤ : ℕ∞) + 1) f' := by simpa using f'.contMDiff.contDiff
  have hgreg : ContDiff ℝ (↑(⊤ : ℕ∞) + 1) g' := by simpa using g'.contMDiff.contDiff
  have hLf' : HasFDerivAt f' (Lf : E →L[ℝ] F) 0 := by
    rw [hf']
    exact hLf.sub_const _
  have hLg' : HasFDerivAt g' (Lg : E →L[ℝ] F) 0 := by
    rw [hg']
    exact hLg.sub_const _
  obtain ⟨L, hL⟩ := Lf.exists_smoothIsotopy Lg hrelative
  let F₀ := linearizationIsotopy f' Lf hfreg hLf' hf0
  let F₁ := linearizationIsotopy g' Lg hgreg hLg' hg0
  -- Concatenation is stationary near its joins and preserves the fixed origin.
  let K := (F₀.symm.trans L le_rfl).trans F₁ le_rfl
  have hK (t : unitInterval) : K (t, 0) = 0 := by
    simp only [K, SmoothIsotopy.trans_apply, SmoothIsotopy.symm_apply]
    split_ifs <;> simp [F₀, F₁, hL]
  -- Translate the motion back; the endpoints and the fixed centre are unchanged.
  let G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap :=
    { toContMDiffMap := ⟨fun p => τ.symm (K p), τ.symm.contMDiff.comp K.contMDiff⟩
      map_zero_left := fun x => by
        simp only [ContMDiffMap.coeFn_mk]
        rw [K.apply_zero]
        simp [f']
      map_one_left := fun x => by
        simp only [ContMDiffMap.coeFn_mk]
        rw [K.apply_one]
        simp [g']
      isSmoothEmbedding := fun t => by
        simpa only [ContMDiffMap.coeFn_mk, SmoothIsotopy.toContMDiffMap_apply,
          Function.comp_def] using
          isSmoothEmbedding_diffeomorph_comp (K.isSmoothEmbedding t) τ.symm }
  refine ⟨G, fun t => ?_⟩
  -- Evaluate the locally constructed translated motion.
  exact (congrArg τ.symm (hK t)).trans (by simp [hτsymm])

/-- **Euclidean disc theorem.** Smooth self-embeddings with a common centre and the
same derivative orientation there are smoothly isotopic relative to that centre.
The determinant condition permits either common orientation and includes dimension zero. -/
theorem exists_smoothIsotopy_of_det_mul_pos
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E) (hcentre : f 0 = g 0)
    (hdet : 0 < (fderiv ℝ f 0).det * (fderiv ℝ g 0).det) :
    ∃ G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap,
      ∀ t : unitInterval, G (t, 0) = f 0 := by
  let Lf := (fderiv ℝ f 0).toContinuousLinearEquivOfDetNeZero
    (mul_ne_zero_iff.mp hdet.ne').1
  let Lg := (fderiv ℝ g 0).toContinuousLinearEquivOfDetNeZero
    (mul_ne_zero_iff.mp hdet.ne').2
  have hLf : HasFDerivAt f (Lf : E →L[ℝ] E) 0 := by
    simpa only [Lf, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      (f.contMDiff.contDiff.differentiable (by simp) 0).hasFDerivAt
  have hLg : HasFDerivAt g (Lg : E →L[ℝ] E) 0 := by
    simpa only [Lg, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      (g.contMDiff.contDiff.differentiable (by simp) 0).hasFDerivAt
  have hrelative : 0 < (Lf.trans Lg.symm).toContinuousLinearMap.det := by
    have heq : (Lf.trans Lg.symm).toContinuousLinearMap.det =
        (Lg : E →L[ℝ] E).det⁻¹ * (Lf : E →L[ℝ] E).det := by
      simpa only [ContinuousLinearMap.det, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
        ContinuousLinearEquiv.trans_toLinearEquiv, ContinuousLinearEquiv.toLinearEquiv_symm,
        Units.val_mul, LinearEquiv.coe_det, LinearEquiv.det_coe_symm] using
        congrArg (fun u : ℝˣ => (u : ℝ))
          (LinearEquiv.det_trans Lf.toLinearEquiv Lg.toLinearEquiv.symm)
    rw [heq]
    simpa only [Lf, Lg, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero,
      inv_mul_eq_div, div_pos_iff] using mul_pos_iff.mp hdet
  exact f.exists_smoothIsotopy_of_det_pos g hcentre Lf Lg hLf hLg hrelative

end TauCeti.SmoothEmbedding
