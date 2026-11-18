/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem

/-!
# The local normal form of a submersion

Let `f : E → F` be `C^n`, `1 ≤ n`, on an open set `s`, and let its derivative `f' = Df(a)` at
`a ∈ s` be surjective with complemented kernel, for instance when `E` is finite-dimensional. Then
near `a` the map `f` is its own derivative after a change of variables: there is a `C^n`
diffeomorphism `Θ` from a neighbourhood of `a` in `s` onto an open subset of `E`, with `C^n`
inverse, such that `f = f' ∘ Θ` there (`ContDiffOn.exists_openPartialHomeomorph_eqOn_fderiv_comp`).
So a submersion is, in suitable coordinates on its source, a surjective linear map.

The change of variables is `Θ x = L⁻¹ (f x, P (x - a))`, where `P` is a continuous projection onto
`ker f'` and `L = (f', P) : E ≃ F × ker f'` is the linear equivalence of
`ContinuousLinearMap.implicitCoordEquiv`. Its derivative at `a` is `L⁻¹ ∘ L = id`, so the inverse
function theorem applies, and `f' (Θ x) = (L (Θ x)).1 = f x`.

This normal form reduces local questions about a submersion to the linear case, for instance the
integration of a compactly supported function over the fibres of `f`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1.
-/

public section

noncomputable section

open Set

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F] [CompleteSpace F]
  {n : WithTop ℕ∞} {f : E → F} {s : Set E} {a : E}

/-- **Local normal form of a submersion.** A map `f` that is `C^n`, `1 ≤ n`, on an open set `s` and
whose derivative at `a ∈ s` is surjective with complemented kernel agrees, on a neighbourhood of
`a` contained in `s`, with its derivative at `a` composed with a `C^n` diffeomorphism `Θ` onto an
open set, whose inverse is `C^n` as well. -/
theorem ContDiffOn.exists_openPartialHomeomorph_eqOn_fderiv_comp (hf : ContDiffOn 𝕂 n f s)
    (hs : IsOpen s) (ha : a ∈ s) (hn : 1 ≤ n) (hsurj : (fderiv 𝕂 f a).range = ⊤)
    (hker : (fderiv 𝕂 f a).ker.ClosedComplemented) :
    ∃ Θ : OpenPartialHomeomorph E E, a ∈ Θ.source ∧ Θ.source ⊆ s ∧
      ContDiffOn 𝕂 n Θ Θ.source ∧ ContDiffOn 𝕂 n Θ.symm Θ.target ∧
      EqOn f (fderiv 𝕂 f a ∘ Θ) Θ.source := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  set f' := fderiv 𝕂 f a
  set L := f'.implicitCoordEquiv hsurj hker
  -- The second coordinate of `L` is a projection onto the kernel of `f'`.
  set g : E → E := fun x ↦ L.symm (f x, (L (x - a)).2)
  have hg : ContDiffOn 𝕂 n g s := by
    have hL : ContDiff 𝕂 n fun x ↦ (L (x - a)).2 := by fun_prop
    exact L.symm.contDiff.comp_contDiffOn (hf.prodMk hL.contDiffOn)
  have hfa : HasFDerivAt f f' a :=
    ((hf.differentiableOn hn0).differentiableAt (hs.mem_nhds ha)).hasFDerivAt
  have hga : HasFDerivAt g (ContinuousLinearMap.id 𝕂 E) a := by
    have hsnd : HasFDerivAt (fun x ↦ (L (x - a)).2)
        ((ContinuousLinearMap.snd 𝕂 F f'.ker).comp (L : E →L[𝕂] F × f'.ker)) a :=
      ((ContinuousLinearMap.snd 𝕂 F f'.ker).comp (L : E →L[𝕂] F × f'.ker)).hasFDerivAt.comp a
        ((hasFDerivAt_id a).sub_const a) |>.congr_fderiv (by ext; simp)
    refine ((L.symm : F × f'.ker →L[𝕂] E).hasFDerivAt.comp a (hfa.prodMk hsnd)).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_id',
      id_eq]
    rw [ContinuousLinearEquiv.symm_apply_eq, Prod.ext_iff]
    simp [L, f']
  obtain ⟨Θ, hΘ, haΘ, hΘs, hΘ'⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hg hs ha hn
    (e := ContinuousLinearEquiv.refl 𝕂 E) (by simpa using hga.fderiv.symm)
  refine ⟨Θ, haΘ, hΘs, hΘ ▸ hg.mono hΘs, hΘ', fun x _ ↦ ?_⟩
  simp only [Function.comp_apply, hΘ, g]
  -- `f' v` is the first coordinate of `L v`.
  have h := f'.implicitCoordEquiv_apply hsurj hker (L.symm (f x, (L (x - a)).2))
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact congrArg Prod.fst h
