/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry

/-!
# The Hodge star of alternating forms

On an oriented finite-dimensional real inner product space `V` of dimension `m`, the Hodge star
of `⋀ᵏ V` is transported along `TauCeti.alternatingFormEquiv` to the continuous alternating forms
`V [⋀^Fin k]→L[ℝ] ℝ`, the fibres of the bundle of differential forms. This gives
`Orientation.formHodgeStar : (V [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] V [⋀^Fin l]→L[ℝ] ℝ` for `k + l = m`.

It is characterized by the wedge identity `α ∧ ⋆β = ⟨α, β⟩ vol` of forms, where `∧` is the
wedge product of forms `ContinuousAlternatingMap.wedge`, `⟨·, ·⟩` is the Gram inner product
`TauCeti.alternatingFormInner` and `vol` is `Orientation.volumeForm`. This is the identity that
turns the `L²` pairing of forms on an oriented Riemannian manifold into an integral of a top
form. The star is an isometry, satisfies `⋆⋆ = (-1) ^ (k l)` on `k`-forms, and changes sign
with the orientation.

In an arbitrary basis `b`, with dual basis `b*` for the inner product, the star is computed by
`(⋆α)(w) = ∑ α(b_{i₁}, …, b_{iₖ}) vol(b*_{i₁}, …, b*_{iₖ}, w₁, …, wₗ)`
(`Orientation.formHodgeStar_apply_eq_sum`). Writing `b*` through the inverse Gram matrix of `b`
(`Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum`), in the coordinate frame of a Riemannian
metric this expresses the star through the inverse metric and the volume of the frame.

## Main definitions

* `Orientation.formHodgeStar`: the Hodge star of alternating forms.

## Main results

* `Orientation.wedge_formHodgeStar_apply`: `α ∧ ⋆β = ⟨α, β⟩ vol`.
* `Orientation.formHodgeStar_formHodgeStar`: `⋆⋆α = (-1) ^ (k l) α`.
* `Orientation.alternatingFormInner_formHodgeStar`: the star preserves the inner product of forms.
* `Orientation.formHodgeStar_apply_eq_sum`: the star in an arbitrary basis.
* `Orientation.formHodgeStar_apply_eq_volumeForm_mul_sum`: the star through the inverse Gram
  matrix of an arbitrary basis.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Module exteriorPower TauCeti Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [_i : Fact (finrank ℝ V = n)]

namespace Orientation

variable (o : Orientation ℝ V (Fin n))

/-- The Hodge star of alternating forms on an oriented real inner product space, `k`-forms to
`l`-forms for `k + l = finrank ℝ V`: the Hodge star of `⋀ᵏ V` transported along
`TauCeti.alternatingFormEquiv`. It is characterized by `α ∧ ⋆β = ⟨α, β⟩ vol`
(`Orientation.wedge_formHodgeStar_apply`). -/
def formHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V) :
    (V [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] V [⋀^Fin l]→L[ℝ] ℝ :=
  ((alternatingFormEquiv V k).symm.trans (o.hodgeStar hkl)).trans (alternatingFormEquiv V l)

/-- The Hodge star of the form of `x ∈ ⋀ᵏ V` is the form of `⋆x`. -/
@[simp]
theorem formHodgeStar_alternatingFormEquiv {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x : ⋀[ℝ]^k V) :
    o.formHodgeStar hkl (alternatingFormEquiv V k x) =
      alternatingFormEquiv V l (o.hodgeStar hkl x) := by
  simp [formHodgeStar]

/-- The Hodge star of a form `α` evaluates on `(v₁, …, vₗ)` as the volume of `a ∧ v₁ ∧ ⋯ ∧ vₗ`,
where `a ∈ ⋀ᵏ V` represents `α`. -/
theorem formHodgeStar_apply {k l : ℕ} (hkl : k + l = finrank ℝ V) (α : V [⋀^Fin k]→L[ℝ] ℝ)
    (v : Fin l → V) :
    o.formHodgeStar hkl α v =
      wedgePairing o.volumeEquiv hkl ((alternatingFormEquiv V k).symm α) (ιMulti ℝ l v) := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V k).surjective α
  rw [formHodgeStar_alternatingFormEquiv, alternatingFormEquiv_apply, inner_hodgeStar_apply,
    LinearEquiv.symm_apply_apply]

/-- A top-degree inner product with a wedge of vectors, read in any degree `d = finrank ℝ V`: it
is the volume of the element times the volume form of the vectors. -/
private theorem inner_ιMulti_eq_volumeEquiv_mul_volumeForm {d : ℕ} (hd : d = finrank ℝ V)
    (z : ⋀[ℝ]^d V) (z' : ⋀[ℝ]^(finrank ℝ V) V) (hz : (z : ExteriorAlgebra ℝ V) = z')
    (v : Fin d → V) :
    ⟪z, ιMulti ℝ d v⟫ = o.volumeEquiv z' * o.volumeForm (v ∘ finCongr (hd.trans _i.out).symm) := by
  subst hd
  obtain rfl : z = z' := Subtype.ext hz
  rw [o.inner_eq_volumeEquiv_mul_volumeEquiv, volumeEquiv_ιMulti]

/-- **The wedge characterization of the Hodge star of forms**: for `k`-forms `α` and `β`,
`α ∧ ⋆β = ⟨α, β⟩ vol`, where `vol` is the volume form of the orientation, read in degree
`k + l = finrank ℝ V`. -/
theorem wedge_formHodgeStar_apply {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (α β : V [⋀^Fin k]→L[ℝ] ℝ) (v : Fin (k + l) → V) :
    α.wedge (o.formHodgeStar hkl β) v =
      alternatingFormInner V k α β * o.volumeForm (v ∘ finCongr (hkl.trans _i.out).symm) := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V k).surjective α
  obtain ⟨b, rfl⟩ := (alternatingFormEquiv V k).surjective β
  -- The wedge of forms is the form of the exterior product `a ∧ ⋆b`, a top-degree element whose
  -- volume is `⟪a, b⟫`.
  set z : ⋀[ℝ]^(finrank ℝ V) V := ⟨_, by
    rw [← hkl]; exact (wedge ℝ V k l a (o.hodgeStar hkl b)).2⟩
  rw [formHodgeStar_alternatingFormEquiv, ← alternatingFormEquiv_wedge,
    alternatingFormEquiv_apply, alternatingFormInner_alternatingFormEquiv,
    ← o.wedgePairing_hodgeStar hkl, wedgePairing_apply_eq_of_coe_mul_eq _ hkl _ _ z rfl]
  exact o.inner_ιMulti_eq_volumeEquiv_mul_volumeForm hkl _ z rfl v

/-- The Hodge star preserves the inner product of forms. -/
@[simp]
theorem alternatingFormInner_formHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner V l (o.formHodgeStar hkl α) (o.formHodgeStar hkl β) =
      alternatingFormInner V k α β := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V k).surjective α
  obtain ⟨b, rfl⟩ := (alternatingFormEquiv V k).surjective β
  simp

/-- **The square of the Hodge star of forms**: `⋆⋆α = (-1) ^ (k l) α` for a `k`-form `α`, where
`k + l = finrank ℝ V`. -/
theorem formHodgeStar_formHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (hlk : l + k = finrank ℝ V) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    o.formHodgeStar hlk (o.formHodgeStar hkl α) = (-1 : ℝ) ^ (k * l) • α := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V k).surjective α
  rw [formHodgeStar_alternatingFormEquiv, formHodgeStar_alternatingFormEquiv,
    hodgeStar_hodgeStar, map_smul]

/-- Reversing the orientation negates the Hodge star of forms. -/
@[simp]
theorem formHodgeStar_neg_orientation {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (α : V [⋀^Fin k]→L[ℝ] ℝ) : (-o).formHodgeStar hkl α = -o.formHodgeStar hkl α := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv V k).surjective α
  simp

/-- **The Hodge star of forms in an arbitrary basis**: if `b` is a basis of `V` and `b*` its dual
basis for the inner product, then `(⋆α)(w₁, …, wₗ)` is the sum over the increasing `k`-tuples
`i₁ < ⋯ < iₖ` of `α(b_{i₁}, …, b_{iₖ}) vol(b*_{i₁}, …, b*_{iₖ}, w₁, …, wₗ)`. -/
theorem formHodgeStar_apply_eq_sum {ι : Type*} [LinearOrder ι] [Fintype ι] {k l : ℕ}
    (hkl : k + l = finrank ℝ V) (b : Basis ι ℝ V) (α : V [⋀^Fin k]→L[ℝ] ℝ) (w : Fin l → V) :
    o.formHodgeStar hkl α w = ∑ s : powersetCard ι k, α (b ∘ powersetCard.ofFinEmbEquiv.symm s) *
      o.volumeForm (Fin.append (LinearMap.BilinForm.dualBasis (innerₗ V) nondegenerate_inner b ∘
        powersetCard.ofFinEmbEquiv.symm s) w ∘ Fin.cast (hkl.trans _i.out).symm) := by
  -- Re-indexing a wedge of vectors along a cast of `Fin` does not change it.
  have key : ∀ {N : ℕ} (h : N = k + l) (f : Fin (k + l) → V),
      ExteriorAlgebra.ιMulti ℝ N (f ∘ Fin.cast h) = ExteriorAlgebra.ιMulti ℝ (k + l) f := by
    rintro N rfl f
    rfl
  rw [o.formHodgeStar_apply, alternatingFormEquiv_symm_eq_sum b, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, wedgePairing_apply_eq_of_coe_mul_eq _ hkl _ _
    (ιMulti ℝ _ (Fin.append (LinearMap.BilinForm.dualBasis (innerₗ V) nondegenerate_inner b ∘
      powersetCard.ofFinEmbEquiv.symm s) w ∘ Fin.cast hkl.symm))
    (by rw [ιMulti_apply_coe, ιMulti_apply_coe, ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_mul_ιMulti, key]), o.volumeEquiv_ιMulti]
  simp only [Function.comp_def, finCongr_apply, Fin.cast_cast]

/-- **The Hodge star of forms through the inverse Gram matrix**: for a basis `b` of `V` indexed by
`Fin n` with Gram matrix `G`, `(⋆α)(w)` is `vol(b)` times the sum over the increasing `k`-tuples
`i₁ < ⋯ < iₖ` of `α(b_{i₁}, …, b_{iₖ})` times the `b`-determinant of
`(∑ⱼ (G⁻¹)_{i₁ j} bⱼ, …, ∑ⱼ (G⁻¹)_{iₖ j} bⱼ, w₁, …, wₗ)`. -/
theorem formHodgeStar_apply_eq_volumeForm_mul_sum {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (b : Basis (Fin n) ℝ V) (α : V [⋀^Fin k]→L[ℝ] ℝ) (w : Fin l → V) :
    o.formHodgeStar hkl α w = o.volumeForm b * ∑ s : powersetCard (Fin n) k,
      α (b ∘ powersetCard.ofFinEmbEquiv.symm s) *
        b.det (Fin.append (fun i ↦ ∑ j,
          (Matrix.gram ℝ b)⁻¹ (powersetCard.ofFinEmbEquiv.symm s i) j • b j) w ∘
            Fin.cast (hkl.trans _i.out).symm) := by
  rw [o.formHodgeStar_apply_eq_sum hkl b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hdual : LinearMap.BilinForm.dualBasis (innerₗ V) nondegenerate_inner b ∘
      powersetCard.ofFinEmbEquiv.symm s = fun i ↦ ∑ j,
        (Matrix.gram ℝ b)⁻¹ (powersetCard.ofFinEmbEquiv.symm s i) j • b j := by
    funext i
    exact dualBasis_innerₗ_eq_sum b _
  have hvol : ∀ v, o.volumeForm v = o.volumeForm b * b.det v := fun v ↦ by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det b o.volumeForm]
    simp
  rw [hdual, hvol]
  ring

end Orientation
