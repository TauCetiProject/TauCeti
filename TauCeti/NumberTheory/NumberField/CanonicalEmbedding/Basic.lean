/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.House

import Mathlib.RingTheory.Complex
import TauCeti.RingTheory.NormTrace.Pi
import TauCeti.RingTheory.NormTrace.Prod

/-!
# Coordinatewise embeddings, sup norm, and the integer lattice in the mixed space

Mathlib's `NumberField.mixedEmbedding K : K →+* mixedSpace K` sends a single field element `x : K`
to its tuple of archimedean embeddings `(φ_w x)_w` across the real and complex infinite places of
`K`. When a family `(g w)_w : InfinitePlace K → K` varies with the infinite place — for example,
the coefficients of place-dependent linear forms in Diophantine approximation — the ring
homomorphism `TauCeti.NumberField.mixedEmbedding.mixedDiag K` assembles `(g w)_w` into the element
of `mixedSpace K` whose `w`-coordinate agrees with `mixedEmbedding K (g w)`.

For a number field `K`, the sup norm of `mixedEmbedding K x` on `mixedSpace K` equals the house of
`x` (`TauCeti.NumberField.norm_mixedEmbedding`), and `mixedEmbedding K` embeds `𝓞 K` injectively
onto `NumberField.mixedEmbedding.integerLattice K ⊆ mixedSpace K`, packaged here as a `ℤ`-linear
equivalence `TauCeti.NumberField.mixedEmbedding.integerLatticeEquiv K`.

## Main definitions

* `TauCeti.NumberField.mixedEmbedding.mixedDiag`: the ring homomorphism
  `(InfinitePlace K → K) →+* mixedSpace K` taking `g` to
  `((φ_w (g w))_{w real}, (φ_w (g w))_{w complex})`.
* `TauCeti.NumberField.mixedEmbedding.integerLatticeEquiv K`: the `ℤ`-linear equivalence
  `𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K` induced by `mixedEmbedding K`.
* `TauCeti.NumberField.mixedEmbedding.multSqrt K`: the element of `mixedSpace K` equal to `1` at
  real places and `√2` at complex places.

## Main results

* `TauCeti.NumberField.mixedEmbedding.mixedDiag_apply_isReal` and
  `TauCeti.NumberField.mixedEmbedding.mixedDiag_apply_isComplex`: real and complex coordinates of
  `mixedDiag K g`.
* `TauCeti.NumberField.mixedEmbedding.mixedDiag_const`: on a constant family `fun _ ↦ x`,
  `mixedDiag K` agrees with `mixedEmbedding K x`.
* `TauCeti.NumberField.mixedEmbedding.normAtPlace_congr`: `normAtPlace w x` depends only on the
  `w`-coordinate of `x`.
* `TauCeti.NumberField.mixedEmbedding.normAtPlace_mixedDiag`:
  `normAtPlace w (mixedDiag K g) = w (g w)`.
* `TauCeti.NumberField.mixedEmbedding.abs_normAtPlace_sub_normAtPlace_le`:
  `|normAtPlace w x - normAtPlace w y| ≤ normAtPlace w (x - y)`.
* `TauCeti.NumberField.mixedEmbedding.normAtPlace_le_norm`: `normAtPlace w x ≤ ‖x‖`.
* `TauCeti.NumberField.mixedEmbedding.abs_normAtPlace_sub_normAtPlace_le_norm`:
  `|normAtPlace w x - normAtPlace w y| ≤ ‖x - y‖`.
* `TauCeti.NumberField.mixedEmbedding.normAtPlace_multSqrt`: `normAtPlace w (multSqrt K) = √w.mult`.
* `TauCeti.NumberField.mixedEmbedding.isUnit_multSqrt`: `multSqrt K` is a unit in `mixedSpace K`.
* `NumberField.mixedEmbedding.algebraNorm_apply`: the `ℝ`-algebra norm of `c : mixedSpace K` as a
  product over the infinite places.
* `NumberField.mixedEmbedding.abs_algebraNorm`: `|Algebra.norm ℝ c| = mixedEmbedding.norm c`.
* `TauCeti.NumberField.mixedEmbedding.algebraNorm_multSqrt`: the `ℝ`-algebra norm of `multSqrt K`
  is `2 ^ nrComplexPlaces K`.
* `TauCeti.NumberField.norm_mixedEmbedding`: `‖mixedEmbedding K x‖ = house x`.
* `TauCeti.NumberField.mixedEmbedding.coe_integerLatticeEquiv` and
  `TauCeti.NumberField.mixedEmbedding.mixedEmbedding_integerLatticeEquiv_symm`: coercing
  `integerLatticeEquiv K x` and `(integerLatticeEquiv K).symm y` into `mixedSpace K`.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K]

open scoped Classical in
/-- **The `ℝ`-algebra norm of a point of the mixed space.** Each real coordinate contributes
its own factor and each complex coordinate contributes the norm of multiplication by a complex
number, namely `Complex.normSq`. -/
theorem algebraNorm_apply [Fintype (InfinitePlace K)] (c : mixedSpace K) :
    Algebra.norm ℝ c = (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  simp [TauCeti.Algebra.norm_prod, TauCeti.Algebra.norm_pi, Algebra.norm_complex_apply]

/-- **The absolute `ℝ`-algebra norm of `c` is the mixed norm of `c`.** Reach for this rather
than `algebraNorm_apply` when the norm feeds a measure-scaling lemma such as
`Measure.addHaar_image_linearMap`, which asks for the absolute value. -/
theorem abs_algebraNorm [NumberField K] (c : mixedSpace K) :
    |Algebra.norm ℝ c| = mixedEmbedding.norm c := by
  rw [algebraNorm_apply, abs_mul, Finset.abs_prod, Finset.abs_prod, mixedEmbedding.norm_apply,
    InfinitePlace.prod_eq_prod_mul_prod]
  simp [normAtPlace_apply_of_isReal, normAtPlace_apply_of_isComplex, Complex.normSq_eq_norm_sq,
    Subtype.prop]

end NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

variable (K : Type*) [Field K]

/-- The ring homomorphism assembling a family `(g w)_w` indexed by the infinite places of `K` into
an element of `mixedSpace K` whose `w`-coordinate agrees with `mixedEmbedding K (g w)`. -/
noncomputable def mixedDiag : (InfinitePlace K → K) →+* mixedSpace K :=
  RingHom.prod
    (RingHom.pi fun w ↦ (embedding_of_isReal w.property).comp (Pi.evalRingHom _ w.val))
    (RingHom.pi fun w ↦ w.val.embedding.comp (Pi.evalRingHom _ w.val))

variable {K}

/-- Real coordinate of `mixedDiag K g` at a real infinite place `w`. -/
@[simp]
theorem mixedDiag_apply_isReal (g : InfinitePlace K → K)
    (w : {w : InfinitePlace K // IsReal w}) :
    (mixedDiag K g).1 w = embedding_of_isReal w.property (g w.val) := by
  rfl

/-- Complex coordinate of `mixedDiag K g` at a complex infinite place `w`. -/
@[simp]
theorem mixedDiag_apply_isComplex (g : InfinitePlace K → K)
    (w : {w : InfinitePlace K // IsComplex w}) :
    (mixedDiag K g).2 w = w.val.embedding (g w.val) := by
  rfl

/-- On a constant family `fun _ ↦ x`, `mixedDiag K` reduces to `mixedEmbedding K x`. -/
@[simp]
theorem mixedDiag_const (x : K) :
    mixedDiag K (fun _ ↦ x) = mixedEmbedding K x := by
  ext <;> simp

/-- `normAtPlace w` depends only on the `w`-coordinate of an element of `mixedSpace K`. -/
theorem normAtPlace_congr (w : InfinitePlace K) {x y : mixedSpace K}
    (h₁ : ∀ hw : IsReal w, x.1 ⟨w, hw⟩ = y.1 ⟨w, hw⟩)
    (h₂ : ∀ hw : IsComplex w, x.2 ⟨w, hw⟩ = y.2 ⟨w, hw⟩) :
    normAtPlace w x = normAtPlace w y := by
  by_cases hw : IsReal w
  · simp [normAtPlace_apply_of_isReal hw, h₁ hw]
  · have hwc : IsComplex w := not_isReal_iff_isComplex.mp hw
    simp [normAtPlace_apply_of_isComplex hwc, h₂ hwc]

/-- At any infinite place `w`, the norm of `mixedDiag K g` is `w (g w)`. -/
@[simp]
theorem normAtPlace_mixedDiag (w : InfinitePlace K) (g : InfinitePlace K → K) :
    normAtPlace w (mixedDiag K g) = w (g w) := by
  rw [← normAtPlace_apply]
  exact normAtPlace_congr w (fun hw ↦ by simp) (fun hwc ↦ by simp)

/-- Reverse triangle inequality for `normAtPlace w`: the absolute difference of local norms at `w`
is at most the local norm of the difference. -/
theorem abs_normAtPlace_sub_normAtPlace_le (w : InfinitePlace K) (x y : mixedSpace K) :
    |normAtPlace w x - normAtPlace w y| ≤ normAtPlace w (x - y) := by
  rcases w.isReal_or_isComplex with hw | hw
  · simpa only [normAtPlace_apply_of_isReal hw, Prod.fst_sub, Pi.sub_apply] using
      abs_norm_sub_norm_le (x.1 ⟨w, hw⟩) (y.1 ⟨w, hw⟩)
  · simpa only [normAtPlace_apply_of_isComplex hw, Prod.snd_sub, Pi.sub_apply] using
      abs_norm_sub_norm_le (x.2 ⟨w, hw⟩) (y.2 ⟨w, hw⟩)

open scoped Classical in
/-- At every infinite place `w`, the local norm `normAtPlace w x` is at most the sup norm `‖x‖` on
`mixedSpace K`. -/
theorem normAtPlace_le_norm [NumberField K] (w : InfinitePlace K) (x : mixedSpace K) :
    normAtPlace w x ≤ ‖x‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun u ↦ normAtPlace u x) (Finset.mem_univ w)

open scoped Classical in
/-- At every infinite place `w`, `normAtPlace w` is 1-Lipschitz with respect to the sup norm on
`mixedSpace K`: `|normAtPlace w x - normAtPlace w y| ≤ ‖x - y‖`. -/
theorem abs_normAtPlace_sub_normAtPlace_le_norm [NumberField K]
    (w : InfinitePlace K) (x y : mixedSpace K) :
    |normAtPlace w x - normAtPlace w y| ≤ ‖x - y‖ :=
  (abs_normAtPlace_sub_normAtPlace_le w x y).trans (normAtPlace_le_norm w (x - y))

/-- The `ℤ`-linear equivalence `𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K` induced by
`mixedEmbedding K`. -/
noncomputable def integerLatticeEquiv (K : Type*) [Field K] [NumberField K] :
    𝓞 K ≃ₗ[ℤ] mixedEmbedding.integerLattice K :=
  LinearEquiv.ofInjective
    ((mixedEmbedding K).toIntAlgHom.toLinearMap.comp
      ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ))
    (fun _ _ hxy ↦ RingOfIntegers.ext <| mixedEmbedding_injective K (by simpa using hxy))

/-- Coercing `integerLatticeEquiv K x` to `mixedSpace K` evaluates `mixedEmbedding K` at `x`. -/
@[simp]
theorem coe_integerLatticeEquiv [NumberField K] (x : 𝓞 K) :
    (integerLatticeEquiv K x : mixedSpace K) = mixedEmbedding K (x : K) :=
  (rfl)

/-- Applying `mixedEmbedding K` to `(integerLatticeEquiv K).symm y` recovers `(y : mixedSpace K)`.
-/
@[simp]
theorem mixedEmbedding_integerLatticeEquiv_symm [NumberField K]
    (y : mixedEmbedding.integerLattice K) :
    mixedEmbedding K (((integerLatticeEquiv K).symm y : 𝓞 K) : K) = (y : mixedSpace K) := by
  rw [← coe_integerLatticeEquiv, LinearEquiv.apply_symm_apply]

/-- The element of `mixedSpace K` with coordinate `1` at every real place and `√2` at every complex
place. Multiplying a tuple coordinatewise by `multSqrt K` turns the ambient Euclidean squared norm
into the multiplicity-weighted sum `∑ w, w.mult * ∑ i, ‖w.embedding (x i)‖ ^ 2`. -/
noncomputable def multSqrt (K : Type*) [Field K] : mixedSpace K :=
  mixedSpaceOfRealSpace (fun w : InfinitePlace K ↦ √(w.mult : ℝ))

/-- At a real place, `multSqrt K` has coordinate `1`. -/
@[simp]
theorem multSqrt_apply_isReal (w : {w : InfinitePlace K // w.IsReal}) :
    (multSqrt K).1 w = 1 := by
  simp [multSqrt, mixedSpaceOfRealSpace_apply, InfinitePlace.mult, w.property]

/-- At a complex place, `multSqrt K` has coordinate `√2`. -/
@[simp]
theorem multSqrt_apply_isComplex (w : {w : InfinitePlace K // w.IsComplex}) :
    (multSqrt K).2 w = (√2 : ℂ) := by
  simp [multSqrt, mixedSpaceOfRealSpace_apply, InfinitePlace.mult,
    not_isReal_iff_isComplex.mpr w.property]

/-- At every infinite place `w`, the norm of `multSqrt K` is `√w.mult`. -/
@[simp]
theorem normAtPlace_multSqrt (w : InfinitePlace K) :
    normAtPlace w (multSqrt K) = √(w.mult : ℝ) :=
  normAtPlace_mixedSpaceOfRealSpace (Real.sqrt_nonneg _)

/-- The `ℝ`-algebra norm of `multSqrt K` is `2 ^ nrComplexPlaces K`. -/
theorem algebraNorm_multSqrt {K : Type*} [Field K] [NumberField K] :
    Algebra.norm ℝ (multSqrt K) = (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K := by
  classical
  rw [_root_.NumberField.mixedEmbedding.algebraNorm_apply]
  simp only [multSqrt_apply_isReal, multSqrt_apply_isComplex, Finset.prod_const_one, one_mul,
    Complex.normSq_ofReal, Real.mul_self_sqrt zero_le_two, Finset.prod_const, Finset.card_univ]

/-- `multSqrt K` is a unit in `mixedSpace K`. -/
theorem isUnit_multSqrt (K : Type*) [Field K] : IsUnit (multSqrt K) := by
  rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  simp

end TauCeti.NumberField.mixedEmbedding

namespace TauCeti.NumberField

open Classical in
/-- On `mixedSpace K`, the sup norm of `mixedEmbedding K x` is the house of `x`. -/
@[simp]
theorem norm_mixedEmbedding {K : Type*} [Field K] [NumberField K] (x : K) :
    ‖mixedEmbedding K x‖ = house x := by
  refine le_antisymm ?_ ?_
  · rw [norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ ↦ ?_
    rw [normAtPlace_apply, ← norm_embedding_eq]
    exact norm_embedding_le_house x w.embedding
  · rw [house, canonicalEmbedding.norm_le_iff]
    intro φ
    rw [← InfinitePlace.apply, ← normAtPlace_apply]
    exact mixedEmbedding.normAtPlace_le_norm (InfinitePlace.mk φ) (mixedEmbedding K x)

end TauCeti.NumberField
