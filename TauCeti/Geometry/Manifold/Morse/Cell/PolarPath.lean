/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.NegativeColumn
public import TauCeti.Geometry.Manifold.Morse.Cell.NegativeDisc
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.Morse.ChartTransition

/-!
# Polar factors of three families of Morse charts

Let `ψ₀`, `ψ₁` and `ψ₂` be charts of a space `M` with a common centre, in which a function `f` has
the normal form `f = c - ‖u‖² + ‖v‖²` on `E × F`. Write `A_ij` for the derivative at the origin of
the transition `ψ_i ∘ ψ_j⁻¹`, and `h_ij` for the polar factor of its negative block
`u ↦ (A_ij (u, 0)).1`. This orthogonal map of `E` compares the negative discs of the charts `j` and
`i` (`OpenPartialHomeomorph.exists_negativeDisc_homotopy`). The comparisons do not compose
strictly: `h₀₂ ≠ h₀₁ h₁₂` in general, although `A₀₂ = A₀₁ A₁₂`, because the negative block of
`A₀₂` also involves the off-diagonal blocks of `A₀₁` and `A₁₂`.

This file joins `h₀₁ h₁₂` to `h₀₂` by a path of linear isometric equivalences, continuously in
the charts. For families of charts `ψᵢ p`, `p` in any topological space `P`, whose transitions
`ψ₀ p ∘ (ψ₁ p)⁻¹` and `ψ₁ p ∘ (ψ₂ p)⁻¹` have derivatives at the origin depending continuously on
`p`, there are linear isometric equivalences `γ p t`, jointly continuous in `p` and `t ∈ [0, 1]`,
from `h₀₁ p ∘ h₁₂ p` at `t = 0` to `h₀₂ p` at `t = 1`
(`TauCeti.exists_path_polarFactor_family_of_charts`). For a single choice of the three charts the
determinants show that `h₀₁ h₁₂` and `h₀₂` lie in the same component of the orthogonal group
(`PartialDiffeomorph.exists_path_linearIsometryEquiv_of_polarFactor_transition`); over a parameter
space this gives no path depending continuously on the parameter, which the explicit path here
does. The derivatives preserve the quadratic form `-‖u‖² + ‖v‖²`
(`OpenPartialHomeomorph.norm_sq_sub_apply_of_hasFDerivAt`) and compose by the chain rule
(`OpenPartialHomeomorph.hasFDerivAt_comp_symm_trans`), so the path is the one of
`ContinuousLinearMap.exists_path_polarFactor_fst_comp_comp` for `A = A₀₁` and the negative column
`C = A₁₂ ∘ inl`.

The same holds for charts with values in `ℝⁿ` in the normal form
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, the form of the Morse charts whose cells are compared over
a parameter space (`TauCeti.exists_homotopy_morseFamilyCharacteristicMap_polarFactor`). There
`h_ij` is the polar factor of `ι† A_ij ι`, for the zero extension `ι : ℝᵏ → ℝⁿ` onto the first `k`
coordinates (`TauCeti.exists_path_polarFactor_family_of_charts_euclidean`).

## Main results

* `TauCeti.exists_path_polarFactor_family_of_charts`: a path of linear isometric equivalences from
  `h₀₁ h₁₂` to `h₀₂`, continuous in the parameter of three families of split Morse charts.
* `TauCeti.exists_path_polarFactor_family_of_charts_euclidean`: the same for families of charts in
  `ℝⁿ`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Remark 3.3 and Lemma 3.6.
-/

public section

open Set unitInterval ContinuousLinearMap
open LinearIsometry (piLpExtendByZero)

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] {P : Type*} [TopologicalSpace P] {f : M → ℝ} {c : ℝ}

section Split

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The polar factors of three families of Morse charts are joined by a continuous path.** Let
`ψ₀ p`, `ψ₁ p` and `ψ₂ p` be charts with a common centre, in which `f = c - ‖u‖² + ‖v‖²`, for `p`
in a topological space `P`. Suppose that the transitions `ψ₀ p ∘ (ψ₁ p)⁻¹` and
`ψ₁ p ∘ (ψ₂ p)⁻¹` have derivatives `D₀₁ p` and `D₁₂ p` at the origin, continuous in `p`. Let
`h_ij p` be the polar factor of the negative block `fst ∘ D_ij p ∘ inl` of the derivative of the
transition `ψ_i p ∘ (ψ_j p)⁻¹`. Then there are linear isometric equivalences `γ p t` of `E`,
jointly continuous in `p` and `t ∈ [0, 1]`, with `γ p 0 = h₀₁ p ∘ h₁₂ p` and `γ p 1 = h₀₂ p`. -/
theorem exists_path_polarFactor_family_of_charts (ψ₀ ψ₁ ψ₂ : P → OpenPartialHomeomorph M (E × F))
    (hf₀ : ∀ p, ∀ y ∈ (ψ₀ p).source, f y = c - ‖(ψ₀ p y).1‖ ^ 2 + ‖(ψ₀ p y).2‖ ^ 2)
    (hf₁ : ∀ p, ∀ y ∈ (ψ₁ p).source, f y = c - ‖(ψ₁ p y).1‖ ^ 2 + ‖(ψ₁ p y).2‖ ^ 2)
    (hf₂ : ∀ p, ∀ y ∈ (ψ₂ p).source, f y = c - ‖(ψ₂ p y).1‖ ^ 2 + ‖(ψ₂ p y).2‖ ^ 2)
    (h₀ : ∀ p, (0 : E × F) ∈ (ψ₀ p).target) (h₁ : ∀ p, (0 : E × F) ∈ (ψ₁ p).target)
    (h₂ : ∀ p, (0 : E × F) ∈ (ψ₂ p).target) (hp₀₁ : ∀ p, (ψ₀ p).symm 0 = (ψ₁ p).symm 0)
    (hp₁₂ : ∀ p, (ψ₁ p).symm 0 = (ψ₂ p).symm 0) {D₀₁ D₁₂ : P → E × F →L[ℝ] E × F}
    (hT₀₁ : ∀ p, HasFDerivAt (fun z ↦ ψ₀ p ((ψ₁ p).symm z)) (D₀₁ p) 0)
    (hT₁₂ : ∀ p, HasFDerivAt (fun z ↦ ψ₁ p ((ψ₂ p).symm z)) (D₁₂ p) 0)
    (hD₀₁ : Continuous D₀₁) (hD₁₂ : Continuous D₁₂) :
    ∃ γ : P → I → (E ≃ₗᵢ[ℝ] E),
      Continuous (fun q : P × I ↦ (γ q.1 q.2 : E →L[ℝ] E)) ∧
      (∀ p, ⇑(γ p 0) = (fst ℝ E F ∘L D₀₁ p ∘L inl ℝ E F).polarFactor ∘L
        (fst ℝ E F ∘L D₁₂ p ∘L inl ℝ E F).polarFactor) ∧
      ∀ p, ⇑(γ p 1) = (fst ℝ E F ∘L fderiv ℝ (fun z ↦ ψ₀ p ((ψ₂ p).symm z)) 0 ∘L
        inl ℝ E F).polarFactor := by
  have hQ₀₁ (p : P) := (ψ₀ p).norm_sq_sub_apply_of_hasFDerivAt (ψ₁ p) (hf₀ p) (hf₁ p) (h₀ p)
    (h₁ p) (hp₀₁ p) (hT₀₁ p)
  have hQ₁₂ (p : P) := (ψ₁ p).norm_sq_sub_apply_of_hasFDerivAt (ψ₂ p) (hf₁ p) (hf₂ p) (h₁ p)
    (h₂ p) (hp₁₂ p) (hT₁₂ p)
  -- `D₀₁ p` preserves `Q`, hence the negative cone, and `D₁₂ p ∘ inl` is an isometric negative
  -- column; the derivative of the composite transition is `D₀₁ p ∘ D₁₂ p`.
  obtain ⟨γ, hγc, hγ0, hγ1⟩ := exists_path_polarFactor_fst_comp_comp hD₀₁
    (fun p _ ↦ (D₀₁ p).norm_snd_apply_lt_norm_fst_apply_of_norm_sq_sub (hQ₀₁ p))
    (C := fun p ↦ D₁₂ p ∘L inl ℝ E F) (hD₁₂.clm_comp continuous_const)
    (fun p u ↦ by simpa using hQ₁₂ p (u, 0))
  refine ⟨γ, hγc, hγ0, fun p ↦ ?_⟩
  -- The chain rule at the common centre `(ψ₂ p)⁻¹ 0`, which both charts send to the origin.
  have hx₂ := (ψ₂ p).map_target (h₂ p)
  have hx₁ : (ψ₂ p).symm 0 ∈ (ψ₁ p).source := hp₁₂ p ▸ (ψ₁ p).map_target (h₁ p)
  have hψ₂ : ψ₂ p ((ψ₂ p).symm 0) = 0 := (ψ₂ p).right_inv (h₂ p)
  have hψ₁ : ψ₁ p ((ψ₂ p).symm 0) = 0 := by rw [← hp₁₂ p, (ψ₁ p).right_inv (h₁ p)]
  have hT := (ψ₀ p).hasFDerivAt_comp_symm_trans (ψ₁ p) (ψ₂ p) hx₁ hx₂ (hψ₁ ▸ hT₀₁ p)
    (hψ₂ ▸ hT₁₂ p)
  rw [hψ₂] at hT
  rw [hγ1, hT.fderiv, comp_assoc]

end Split

section Euclidean

variable {n k : ℕ}

/-- **The polar factors of three families of Euclidean Morse charts are joined by a continuous
path.** Let `ψ₀ p`, `ψ₁ p` and `ψ₂ p` be charts with values in `ℝⁿ` and a common centre, in which
`f = c - Σ_{j < k} yⱼ² + Σ_{j ≥ k} yⱼ²`, for `p` in a topological space `P`. Suppose that the
transitions `ψ₀ p ∘ (ψ₁ p)⁻¹` and `ψ₁ p ∘ (ψ₂ p)⁻¹` have derivatives `D₀₁ p` and `D₁₂ p` at the
origin, continuous in `p`. Let `ι : ℝᵏ → ℝⁿ` be the zero extension onto the first `k` coordinates
and `h_ij p` the polar factor of the negative block `ι† A ι` of the derivative `A` of the
transition `ψ_i p ∘ (ψ_j p)⁻¹`. Then there are linear isometric equivalences `γ p t` of `ℝᵏ`,
jointly continuous in `p` and `t ∈ [0, 1]`, with `γ p 0 = h₀₁ p ∘ h₁₂ p` and `γ p 1 = h₀₂ p`. -/
theorem exists_path_polarFactor_family_of_charts_euclidean
    (ψ₀ ψ₁ ψ₂ : P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hk : k ≤ n)
    (hf₀ : ∀ p, ∀ y ∈ (ψ₀ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₀ p y j ^ 2)
    (hf₁ : ∀ p, ∀ y ∈ (ψ₁ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₁ p y j ^ 2)
    (hf₂ : ∀ p, ∀ y ∈ (ψ₂ p).source, f y = c + ∑ j, (if j.val < k then -1 else 1) * ψ₂ p y j ^ 2)
    (h₀ : ∀ p, (0 : EuclideanSpace ℝ (Fin n)) ∈ (ψ₀ p).target)
    (h₁ : ∀ p, (0 : EuclideanSpace ℝ (Fin n)) ∈ (ψ₁ p).target)
    (h₂ : ∀ p, (0 : EuclideanSpace ℝ (Fin n)) ∈ (ψ₂ p).target)
    (hp₀₁ : ∀ p, (ψ₀ p).symm 0 = (ψ₁ p).symm 0) (hp₁₂ : ∀ p, (ψ₁ p).symm 0 = (ψ₂ p).symm 0)
    {D₀₁ D₁₂ : P → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT₀₁ : ∀ p, HasFDerivAt (fun z ↦ ψ₀ p ((ψ₁ p).symm z)) (D₀₁ p) 0)
    (hT₁₂ : ∀ p, HasFDerivAt (fun z ↦ ψ₁ p ((ψ₂ p).symm z)) (D₁₂ p) 0)
    (hD₀₁ : Continuous D₀₁) (hD₁₂ : Continuous D₁₂) :
    ∃ γ : P → I → (EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)),
      Continuous (fun q : P × I ↦
        (γ q.1 q.2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))) ∧
      (∀ p, ⇑(γ p 0) = (adjoint (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
          D₀₁ p ∘L (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor ∘L
        (adjoint (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
          D₁₂ p ∘L (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor) ∧
      ∀ p, ⇑(γ p 1) =
        (adjoint (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap ∘L
          fderiv ℝ (fun z ↦ ψ₀ p ((ψ₂ p).symm z)) 0 ∘L
            (piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor := by
  -- Split the coordinates into the negative factor `j < k` and the positive factor.
  set S := EuclideanSpace.sumComplEquivProd ℝ (fun j : Fin n ↦ j.val < k)
  set e := EuclideanSpace.finCastLEEquiv ℝ hk
  set φ : (P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) → P →
      OpenPartialHomeomorph M _ := fun ψ p ↦ (ψ p).transHomeomorph S.toHomeomorph
  -- The transitions of the split charts are those of `ψᵢ p` conjugated by `S`.
  have hTS (ψ ψ' : P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (p : P) :
      (fun z ↦ φ ψ p ((φ ψ' p).symm z)) = S ∘ (fun z ↦ ψ p ((ψ' p).symm z)) ∘ S.symm := by
    funext z
    simp [φ]
  have hTφ (ψ ψ' : P → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      {D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} (p : P)
      (hT : HasFDerivAt (fun z ↦ ψ p ((ψ' p).symm z)) D 0) :
      HasFDerivAt (fun z ↦ φ ψ p ((φ ψ' p).symm z))
        ((S : _ →L[ℝ] _) ∘L D ∘L (S.symm : _ →L[ℝ] _)) 0 := by
    have hT' : HasFDerivAt (fun z ↦ ψ p ((ψ' p).symm z)) D (S.symm 0) := by rwa [map_zero]
    rw [hTS]
    exact S.hasFDerivAt.comp 0 (hT'.comp 0 S.symm.hasFDerivAt)
  obtain ⟨γ, hγc, hγ0, hγ1⟩ := exists_path_polarFactor_family_of_charts (φ ψ₀) (φ ψ₁) (φ ψ₂)
    (fun p ↦ (ψ₀ p).apply_eq_of_transHomeomorph_sumComplEquivProd (hf₀ p))
    (fun p ↦ (ψ₁ p).apply_eq_of_transHomeomorph_sumComplEquivProd (hf₁ p))
    (fun p ↦ (ψ₂ p).apply_eq_of_transHomeomorph_sumComplEquivProd (hf₂ p))
    (fun p ↦ by simpa [φ] using h₀ p) (fun p ↦ by simpa [φ] using h₁ p)
    (fun p ↦ by simpa [φ] using h₂ p) (fun p ↦ by simpa [φ] using hp₀₁ p)
    (fun p ↦ by simpa [φ] using hp₁₂ p) (fun p ↦ hTφ ψ₀ ψ₁ p (hT₀₁ p))
    (fun p ↦ hTφ ψ₁ ψ₂ p (hT₁₂ p)) (by fun_prop) (by fun_prop)
  -- Read the path through `e`, which identifies `ℝᵏ` with the negative factor.
  refine ⟨fun p t ↦ e.trans ((γ p t).trans e.symm), ?_, fun p ↦ ?_, fun p ↦ ?_⟩
  · have hcoe (g : EuclideanSpace ℝ {j : Fin n // j.val < k} ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ {j : Fin n // j.val < k}) :
        ((e.trans (g.trans e.symm) : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
          EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) =
          (e.symm : EuclideanSpace ℝ {j : Fin n // j.val < k} →L[ℝ] EuclideanSpace ℝ (Fin k)) ∘L
            (g : EuclideanSpace ℝ {j : Fin n // j.val < k} →L[ℝ] _) ∘L
            (e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ {j : Fin n // j.val < k}) := by
      ext
      simp
    simp only [hcoe]
    fun_prop
  · ext w
    simp [hγ0, EuclideanSpace.polarFactor_adjoint_comp_comp_piLpExtendByZero, e, S]
  · have hfd : fderiv ℝ (fun z ↦ φ ψ₀ p ((φ ψ₂ p).symm z)) 0 =
        (S : _ →L[ℝ] _) ∘L fderiv ℝ (fun z ↦ ψ₀ p ((ψ₂ p).symm z)) 0 ∘L (S.symm : _ →L[ℝ] _) := by
      rw [hTS, S.comp_fderiv, S.symm.comp_right_fderiv, map_zero]
    ext w
    simp [hγ1, hfd, EuclideanSpace.polarFactor_adjoint_comp_comp_piLpExtendByZero, e, S]

end Euclidean

end TauCeti
