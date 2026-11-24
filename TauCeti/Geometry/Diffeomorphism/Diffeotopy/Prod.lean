/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Topology.Homotopy.Isotopy.Prod

/-!
# Products of diffeotopies

Two diffeotopies `φ_t` of `M` and `ψ_t` of `N` run simultaneously give the diffeotopy

`(φ × ψ)_t (x, y) = (φ_t x, ψ_t y)`

of the product manifold `M × N` (`TauCeti.Diffeotopy.prodCongr`), the smooth counterpart of the
product of ambient isotopies `TauCeti.AmbientIsotopy.prodCongr`. Its time slices are the products
`φ_t × ψ_t` of the time slices (`TauCeti.Diffeotopy.timeSlice_prodCongr`). The two projections
intertwine it with its factors: `pr₁ ∘ (φ × ψ)_t = φ_t ∘ pr₁` and `pr₂ ∘ (φ × ψ)_t = ψ_t ∘ pr₂`
(`TauCeti.Diffeotopy.semiconj_fst_timeSlice_prodCongr`,
`TauCeti.Diffeotopy.semiconj_snd_timeSlice_prodCongr`). These identities transport invariants of
diffeotopies that are natural under such intertwining maps, for instance the flux, from the
factors to the product.

The product is compatible with the group operations on diffeotopies: the product of constant
diffeotopies is constant, and products commute with pointwise composition and inversion.

## Main definitions

* `TauCeti.Diffeotopy.prodCongr Φ Ψ`: the product diffeotopy
  `(t, (x, y)) ↦ (Φ (t, x), Ψ (t, y))`.

## Main results

* `TauCeti.Diffeotopy.timeSlice_prodCongr`, `TauCeti.Diffeotopy.final_prodCongr`: the time slices
  and the final diffeomorphism of a product are products.
* `TauCeti.Diffeotopy.semiconj_fst_timeSlice_prodCongr`,
  `TauCeti.Diffeotopy.semiconj_snd_timeSlice_prodCongr`: the projections intertwine the product
  with its factors.
* `TauCeti.Diffeotopy.refl_prodCongr_refl`, `TauCeti.Diffeotopy.prodCongr_trans_prodCongr`,
  `TauCeti.Diffeotopy.prodCongr_symm`: compatibility with the constant diffeotopy, pointwise
  composition and inversion.
* `TauCeti.Diffeotopy.toAmbientIsotopy_prodCongr`: forgetting smoothness gives the product of
  ambient isotopies.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2.
-/

public section

noncomputable section

namespace TauCeti

namespace Diffeotopy

open unitInterval
open scoped Manifold ContDiff

variable {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E H} {J' : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} (Φ : Diffeotopy J n M) (Ψ : Diffeotopy J' n N)

/-- The **product** of two diffeotopies, `(t, (x, y)) ↦ (Φ (t, x), Ψ (t, y))`: the two motions
run simultaneously on the product manifold. -/
def prodCongr : Diffeotopy (J.prod J') n (M × N) where
  toDiffeomorph :=
    { toFun := fun p ↦ (p.1, Φ (p.1, p.2.1), Ψ (p.1, p.2.2))
      invFun := fun p ↦
        (p.1, (Φ.toDiffeomorph.symm (p.1, p.2.1)).2, (Ψ.toDiffeomorph.symm (p.1, p.2.2)).2)
      left_inv := fun p ↦ Prod.ext rfl <| Prod.ext (Φ.symm_apply_apply (p.1, p.2.1))
        (Ψ.symm_apply_apply (p.1, p.2.2))
      right_inv := fun p ↦ Prod.ext rfl <| Prod.ext (Φ.apply_symm_apply (p.1, p.2.1))
        (Ψ.apply_symm_apply (p.1, p.2.2))
      contMDiff_toFun :=
        contMDiff_fst.prodMk
          ((Φ.contMDiff.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
            (Ψ.contMDiff.comp (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd))))
      contMDiff_invFun :=
        contMDiff_fst.prodMk
          (((contMDiff_snd.comp Φ.toDiffeomorph.symm.contMDiff).comp
              (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
            ((contMDiff_snd.comp Ψ.toDiffeomorph.symm.contMDiff).comp
              (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))) }
  fst_apply _ := rfl
  snd_apply_zero' p := by
    -- The motions of the factors start at the identity.
    exact Prod.ext (Φ.apply_zero p.1) (Ψ.apply_zero p.2)

/-- The product diffeotopy moves each coordinate by its own diffeotopy. -/
@[simp]
theorem prodCongr_apply (p : I × M × N) :
    Φ.prodCongr Ψ p = (Φ (p.1, p.2.1), Ψ (p.1, p.2.2)) :=
  (rfl)

/-- The motion of a product diffeotopy on the cylinder is the pair of motions of its factors. -/
theorem cylinderMap_prodCongr (p : (M × N) × I) :
    (Φ.prodCongr Ψ).cylinderMap p =
      (Φ.cylinderMap (p.1.1, p.2), Ψ.cylinderMap (p.1.2, p.2)) := by
  simp only [cylinderMap_apply, prodCongr_apply]

/-- The time slices of a product diffeotopy are the products of the time slices. -/
@[simp]
theorem timeSlice_prodCongr (t : I) :
    (Φ.prodCongr Ψ).timeSlice t = (Φ.timeSlice t).prodCongr (Ψ.timeSlice t) :=
  Diffeomorph.ext fun ⟨_, _⟩ ↦ by
    simp only [timeSlice_apply, prodCongr_apply, Diffeomorph.coe_prodCongr, Prod.map_apply]

/-- The final diffeomorphism of a product diffeotopy is the product of the final
diffeomorphisms. -/
@[simp]
theorem final_prodCongr : (Φ.prodCongr Ψ).final = Φ.final.prodCongr Ψ.final := by
  rw [final_def, final_def, final_def, timeSlice_prodCongr]

/-- The first projection intertwines the product diffeotopy with its first factor:
`pr₁ ∘ (φ × ψ)_t = φ_t ∘ pr₁`. -/
theorem semiconj_fst_timeSlice_prodCongr (t : I) :
    Function.Semiconj Prod.fst ((Φ.prodCongr Ψ).timeSlice t) (Φ.timeSlice t) :=
  fun _ ↦ by simp only [timeSlice_apply, prodCongr_apply]

/-- The second projection intertwines the product diffeotopy with its second factor:
`pr₂ ∘ (φ × ψ)_t = ψ_t ∘ pr₂`. -/
theorem semiconj_snd_timeSlice_prodCongr (t : I) :
    Function.Semiconj Prod.snd ((Φ.prodCongr Ψ).timeSlice t) (Ψ.timeSlice t) :=
  fun _ ↦ by simp only [timeSlice_apply, prodCongr_apply]

/-- The product of the constant diffeotopies is the constant diffeotopy. -/
@[simp]
theorem refl_prodCongr_refl : (refl J n M).prodCongr (refl J' n N) = refl (J.prod J') n (M × N) :=
  ext fun _ ↦ by simp only [prodCongr_apply, refl_apply]

/-- Products of diffeotopies commute with pointwise composition. -/
@[simp]
theorem prodCongr_trans_prodCongr (Φ' : Diffeotopy J n M) (Ψ' : Diffeotopy J' n N) :
    (Φ.prodCongr Ψ).trans (Φ'.prodCongr Ψ') = (Φ.trans Φ').prodCongr (Ψ.trans Ψ') :=
  ext fun _ ↦ by simp only [trans_apply, prodCongr_apply]

/-- The pointwise inverse of a product diffeotopy is the product of the pointwise inverses. -/
@[simp]
theorem prodCongr_symm : (Φ.prodCongr Ψ).symm = Φ.symm.prodCongr Ψ.symm :=
  ext fun p ↦ by
    rw [symm_apply, prodCongr_apply, symm_apply, symm_apply]
    -- The inverse of the product's total diffeomorphism is its `invFun`, the pair of inverses.
    rfl

/-- Forgetting smoothness turns the product of diffeotopies into the product of ambient
isotopies. -/
@[simp]
theorem toAmbientIsotopy_prodCongr :
    (Φ.prodCongr Ψ).toAmbientIsotopy = Φ.toAmbientIsotopy.prodCongr Ψ.toAmbientIsotopy :=
  AmbientIsotopy.ext fun p ↦ by
    rw [toAmbientIsotopy_apply, AmbientIsotopy.prodCongr_apply, toAmbientIsotopy_apply,
      toAmbientIsotopy_apply, prodCongr_apply]

end Diffeotopy

end TauCeti
