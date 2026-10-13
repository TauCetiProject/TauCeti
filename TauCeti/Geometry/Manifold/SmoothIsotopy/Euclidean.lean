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

Two smooth embeddings of a finite-dimensional real normed space into itself that have
the same value at the origin and agree in orientation there are smoothly isotopic,
fixing that value throughout. Agreement in orientation is expressed by positivity
of the product of their derivative determinants, so both determinants may be negative.

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

/-- **Euclidean disc theorem.** Smooth self-embeddings with a common centre and the
same derivative orientation there are smoothly isotopic relative to that centre.
The determinant condition permits either common orientation and includes dimension zero. -/
theorem exists_smoothIsotopy_of_det_mul_pos
    (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E E) (hcentre : f 0 = g 0)
    (hdet : 0 < (fderiv ℝ f 0).det * (fderiv ℝ g 0).det) :
    ∃ G : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap,
      ∀ t : unitInterval, G (t, 0) = f 0 := by
  -- Translate both embeddings to the same zero centre.
  let τ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E :=
    { toFun := fun x => x - f 0
      invFun := fun x => x + f 0
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  have hτ (x : E) : τ x = x - f 0 := by
    rw [← Diffeomorph.coe_toEquiv]
    rfl
  have hτsymm (x : E) : τ.symm x = x + f 0 := by
    rw [← Diffeomorph.toEquiv_coe_symm]
    rfl
  let f' := f.transDiffeomorph τ
  let g' := g.transDiffeomorph τ
  have hf' : (f' : E → E) = fun x => f x - f 0 := by
    funext x
    simp [f', hτ]
  have hg' : (g' : E → E) = fun x => g x - f 0 := by
    funext x
    simp [g', hτ]
  have hf0 : f' 0 = 0 := by rw [hf']; simp
  have hg0 : g' 0 = 0 := by simp [hg', hcentre]
  -- The orientation hypothesis also gives both invertible derivatives.
  let Lf := (fderiv ℝ f 0).toContinuousLinearEquivOfDetNeZero
    (mul_ne_zero_iff.mp hdet.ne').1
  let Lg := (fderiv ℝ g 0).toContinuousLinearEquivOfDetNeZero
    (mul_ne_zero_iff.mp hdet.ne').2
  have hfreg : ContDiff ℝ (↑(⊤ : ℕ∞) + 1) f' := by simpa using f'.contMDiff.contDiff
  have hgreg : ContDiff ℝ (↑(⊤ : ℕ∞) + 1) g' := by simpa using g'.contMDiff.contDiff
  have hLf : HasFDerivAt f' (Lf : E →L[ℝ] E) 0 := by
    simpa only [Lf, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero,
      hf', fderiv_sub_const] using (hfreg.differentiable (by simp) 0).hasFDerivAt
  have hLg : HasFDerivAt g' (Lg : E →L[ℝ] E) 0 := by
    simpa only [Lg, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero,
      hg', fderiv_sub_const] using (hgreg.differentiable (by simp) 0).hasFDerivAt
  have hrelative : 0 < (Lf.trans Lg.symm).toContinuousLinearMap.det := by
    have hcomp : (Lf.trans Lg.symm : E →L[ℝ] E) =
        (Lg.symm : E →L[ℝ] E).comp (Lf : E →L[ℝ] E) := by
      ext x
      simp
    have heq : (Lf.trans Lg.symm).toContinuousLinearMap.det =
        (fderiv ℝ g 0).det⁻¹ * (fderiv ℝ f 0).det := by
      calc
        (Lf.trans Lg.symm).toContinuousLinearMap.det =
            (Lg.symm : E →L[ℝ] E).det * (Lf : E →L[ℝ] E).det := by
          rw [hcomp]
          exact LinearMap.det_comp _ _
        _ = _ := by simp [Lf, Lg]
    rw [heq]
    rcases mul_pos_iff.mp hdet with h | h
    · exact mul_pos (inv_pos.mpr h.2) h.1
    · exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr h.2) h.1
  obtain ⟨L, hL⟩ := Lf.exists_smoothIsotopy Lg hrelative
  let F := linearizationIsotopy f' Lf hfreg hLf hf0
  let H := linearizationIsotopy g' Lg hgreg hLg hg0
  -- Concatenation is stationary near its joins and preserves the fixed origin.
  let K := (F.symm.trans L le_rfl).trans H le_rfl
  have hK (t : unitInterval) : K (t, 0) = 0 := by
    simp only [K, SmoothIsotopy.trans_apply, SmoothIsotopy.symm_apply]
    split_ifs <;> simp [F, H, hL]
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

end TauCeti.SmoothEmbedding
