/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Shuffle.InnerProduct
public import TauCeti.Algebra.TypeAHeckeAlgebra.Shuffle.Tail

/-!
# First-site orthogonal projections and Jucys–Murphy compression on the Hilbert shuffle carrier

This file lifts the algebraic first-site decomposition and rest-compression identities of
`TauCeti.Algebra.TypeAHeckeAlgebra.Shuffle.Tail` to the orthonormal-mask Hilbert carrier
`PiLp 2 fun _ : ShuffleMask k l ↦ U` (`TauCeti.TypeAHeckeAlgebra.shuffleHilbertRep`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.firstSelectedHilbertProj` and
  `TauCeti.TypeAHeckeAlgebra.firstRestHilbertProj`: continuous symmetric orthogonal projections on
  `PiLp 2` onto masks selecting site `0` and masks leaving site `0` in the rest.

## Main results

* `TauCeti.TypeAHeckeAlgebra.isSymmetric_shuffleHilbertRep_tailJucysMurphy` and
  `TauCeti.TypeAHeckeAlgebra.isSymmetric_shuffleHilbertRep_tailAdditiveJucysMurphy`: symmetry of
  tail Jucys–Murphy operators for real parameters and symmetric rest generators.
* `TauCeti.TypeAHeckeAlgebra.firstRestHilbertProj_shuffleHilbertRep_tailAdditiveJucysMurphy_zero`
  and `TauCeti.TypeAHeckeAlgebra.firstRestHilbertProj_shuffleHilbertRep_tailJucysMurphy_zero`:
  pointwise Hilbert-carrier first-site rest-compression identities.
* `firstRestHilbertProj_comp_shuffleHilbertRep_tailAdditiveJucysMurphy_zero_comp` and
  `firstRestHilbertProj_comp_shuffleHilbertRep_tailJucysMurphy_zero_comp`: operator-level
  Hilbert-carrier compression identities.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52.
* G. E. Murphy, *On the representation theory of the symmetric groups and associated Hecke
  algebras*, J. Algebra 152 (1992), 492–513.
-/

public section

open scoped InnerProductSpace

namespace TauCeti.TypeAHeckeAlgebra

variable {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ} {k l : ℕ}
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]

section Projections

variable (𝕜 U) [NeZero (k + l)]

/-- Orthogonal projection onto masks selecting site `0` on the `PiLp 2` shuffle Hilbert carrier. -/
noncomputable def firstSelectedHilbertProj :
    Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U) :=
  ((WithLp.linearEquiv 2 𝕜 (ShuffleMask k l → U)).symm.conjAlgEquiv 𝕜) (firstSelectedProj 𝕜 U)

/-- Orthogonal projection onto masks leaving site `0` in the rest on the `PiLp 2` shuffle Hilbert
carrier. -/
noncomputable def firstRestHilbertProj : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U) :=
  ((WithLp.linearEquiv 2 𝕜 (ShuffleMask k l → U)).symm.conjAlgEquiv 𝕜) (firstRestProj 𝕜 U)

variable {𝕜 U}

/-- Pointwise evaluation of `firstSelectedHilbertProj` at mask `S`. -/
@[simp]
theorem firstSelectedHilbertProj_apply (f : PiLp 2 fun _ : ShuffleMask k l ↦ U)
    (S : ShuffleMask k l) :
    firstSelectedHilbertProj 𝕜 U f S = if (0 : Fin (k + l)) ∈ S.val then f S else 0 :=
  firstSelectedProj_apply (WithLp.ofLp f) S

/-- Pointwise evaluation of `firstRestHilbertProj` at mask `S`. -/
@[simp]
theorem firstRestHilbertProj_apply (f : PiLp 2 fun _ : ShuffleMask k l ↦ U)
    (S : ShuffleMask k l) :
    firstRestHilbertProj 𝕜 U f S = if (0 : Fin (k + l)) ∈ S.val then 0 else f S :=
  firstRestProj_apply (WithLp.ofLp f) S

/-- `firstSelectedHilbertProj` and `firstRestHilbertProj` sum to `1`. -/
@[simp]
theorem firstSelectedHilbertProj_add_firstRestHilbertProj :
    (firstSelectedHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) +
      firstRestHilbertProj 𝕜 U = 1 := by
  rw [firstSelectedHilbertProj, firstRestHilbertProj, ← map_add,
    firstSelectedProj_add_firstRestProj, map_one]

/-- `firstSelectedHilbertProj` is idempotent under composition. -/
@[simp]
theorem firstSelectedHilbertProj_comp_firstSelectedHilbertProj :
    (firstSelectedHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) ∘ₗ
      firstSelectedHilbertProj 𝕜 U = firstSelectedHilbertProj 𝕜 U :=
  LinearMap.ext fun _ ↦ PiLp.ext fun S ↦ by by_cases h : (0 : Fin (k + l)) ∈ S.val <;> simp [h]

/-- `firstRestHilbertProj` is idempotent under composition. -/
@[simp]
theorem firstRestHilbertProj_comp_firstRestHilbertProj :
    (firstRestHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) ∘ₗ
      firstRestHilbertProj 𝕜 U = firstRestHilbertProj 𝕜 U :=
  LinearMap.ext fun _ ↦ PiLp.ext fun S ↦ by by_cases h : (0 : Fin (k + l)) ∈ S.val <;> simp [h]

/-- `firstSelectedHilbertProj` annihilates the image of `firstRestHilbertProj`. -/
@[simp]
theorem firstSelectedHilbertProj_comp_firstRestHilbertProj :
    (firstSelectedHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) ∘ₗ
      firstRestHilbertProj 𝕜 U = 0 :=
  LinearMap.ext fun _ ↦ PiLp.ext fun S ↦ by by_cases h : (0 : Fin (k + l)) ∈ S.val <;> simp [h]

/-- `firstRestHilbertProj` annihilates the image of `firstSelectedHilbertProj`. -/
@[simp]
theorem firstRestHilbertProj_comp_firstSelectedHilbertProj :
    (firstRestHilbertProj 𝕜 U : Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) ∘ₗ
      firstSelectedHilbertProj 𝕜 U = 0 :=
  LinearMap.ext fun _ ↦ PiLp.ext fun S ↦ by by_cases h : (0 : Fin (k + l)) ∈ S.val <;> simp [h]

/-- `firstSelectedHilbertProj` is symmetric with respect to the `PiLp 2` inner product. -/
theorem isSymmetric_firstSelectedHilbertProj :
    (firstSelectedHilbertProj 𝕜 U :
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)).IsSymmetric := fun _ _ ↦ by
  simp only [PiLp.inner_apply, firstSelectedHilbertProj_apply]
  exact Finset.sum_congr rfl fun S _ ↦ by by_cases h : (0 : Fin (k + l)) ∈ S.val <;> simp [h]

/-- `firstRestHilbertProj` is symmetric with respect to the `PiLp 2` inner product. -/
theorem isSymmetric_firstRestHilbertProj :
    (firstRestHilbertProj 𝕜 U :
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)).IsSymmetric := fun _ _ ↦ by
  simp only [PiLp.inner_apply, firstRestHilbertProj_apply]
  exact Finset.sum_congr rfl fun S _ ↦ by by_cases h : (0 : Fin (k + l)) ∈ S.val <;> simp [h]

/-- The images of `firstSelectedHilbertProj` and `firstRestHilbertProj` are pairwise orthogonal. -/
theorem inner_firstSelectedHilbertProj_firstRestHilbertProj
    (f g : PiLp 2 fun _ : ShuffleMask k l ↦ U) :
    ⟪firstSelectedHilbertProj 𝕜 U f, firstRestHilbertProj 𝕜 U g⟫_𝕜 = 0 := by
  simp only [PiLp.inner_apply, firstSelectedHilbertProj_apply, firstRestHilbertProj_apply]
  exact Finset.sum_eq_zero fun S _ ↦ by by_cases h : (0 : Fin (k + l)) ∈ S.val <;> simp [h]

/-- `firstSelectedHilbertProj` is continuous on the `PiLp 2` shuffle Hilbert carrier. -/
theorem continuous_firstSelectedHilbertProj :
    Continuous (firstSelectedHilbertProj 𝕜 U :
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) := by
  -- Expose the `toLp ∘ firstSelectedProj ∘ ofLp` definition to apply `PiLp.continuous_toLp`.
  change Continuous (fun f ↦ WithLp.toLp 2 (firstSelectedProj 𝕜 U (WithLp.ofLp f)))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun S ↦ ?_)
  by_cases h : (0 : Fin (k + l)) ∈ S.val
  · simpa [h] using PiLp.continuous_apply 2 (fun _ : ShuffleMask k l ↦ U) S
  · simpa [h] using continuous_const

/-- `firstRestHilbertProj` is continuous on the `PiLp 2` shuffle Hilbert carrier. -/
theorem continuous_firstRestHilbertProj :
    Continuous (firstRestHilbertProj 𝕜 U :
      Module.End 𝕜 (PiLp 2 fun _ : ShuffleMask k l ↦ U)) := by
  -- Expose the `toLp ∘ firstRestProj ∘ ofLp` definition to apply `PiLp.continuous_toLp`.
  change Continuous (fun f ↦ WithLp.toLp 2 (firstRestProj 𝕜 U (WithLp.ofLp f)))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun S ↦ ?_)
  by_cases h : (0 : Fin (k + l)) ∈ S.val
  · simpa [h] using continuous_const
  · simpa [h] using PiLp.continuous_apply 2 (fun _ : ShuffleMask k l ↦ U) S

end Projections

/-- Tail normalized Jucys–Murphy elements act symmetrically on `shuffleHilbertRep` for a real
parameter and symmetric rest generators. -/
theorem isSymmetric_shuffleHilbertRep_tailJucysMurphy (hq : star (q : 𝕜) = q)
    (ρ : TypeAHeckeAlgebra 𝕜 q l →ₐ[𝕜] Module.End 𝕜 U)
    (hρ : ∀ i, (ρ (T q i)).IsSymmetric) (i : Fin (k + l)) :
    (shuffleHilbertRep k ρ (tailJucysMurphy q i)).IsSymmetric := by
  have : Fact (IsSelfAdjoint (q : 𝕜)) := ⟨hq⟩
  intro f g
  simpa only [star_tailJucysMurphy] using
    inner_shuffleHilbertRep_star k ρ hρ (tailJucysMurphy q i) f g

/-- Tail additive Jucys–Murphy elements act symmetrically on `shuffleHilbertRep` for a real
parameter and symmetric rest generators. -/
theorem isSymmetric_shuffleHilbertRep_tailAdditiveJucysMurphy (hq : star (q : 𝕜) = q)
    (ρ : TypeAHeckeAlgebra 𝕜 q l →ₐ[𝕜] Module.End 𝕜 U)
    (hρ : ∀ i, (ρ (T q i)).IsSymmetric) (i : Fin (k + l)) :
    (shuffleHilbertRep k ρ (tailAdditiveJucysMurphy q i)).IsSymmetric := by
  have : Fact (IsSelfAdjoint (q : 𝕜)) := ⟨hq⟩
  intro f g
  simpa only [star_tailAdditiveJucysMurphy] using
    inner_shuffleHilbertRep_star k ρ hρ (tailAdditiveJucysMurphy q i) f g

/-- **Pointwise Hilbert-carrier first-site additive Jucys–Murphy rest-compression identity.** -/
theorem firstRestHilbertProj_shuffleHilbertRep_tailAdditiveJucysMurphy_zero
    (k : ℕ) (ρ : TypeAHeckeAlgebra 𝕜 q (l + 1) →ₐ[𝕜] Module.End 𝕜 U)
    (f : PiLp 2 fun _ : ShuffleMask k (l + 1) ↦ U) (S : ShuffleMask k (l + 1)) :
    firstRestHilbertProj 𝕜 U
        (shuffleHilbertRep k ρ (tailAdditiveJucysMurphy q (0 : Fin (k + (l + 1))))
          (firstRestHilbertProj 𝕜 U f)) S =
      ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1))) (firstRestHilbertProj 𝕜 U f S) := by
  have hproj : WithLp.ofLp (firstRestHilbertProj 𝕜 U f) = firstRestProj 𝕜 U (WithLp.ofLp f) := rfl
  have h := congrFun (LinearMap.congr_fun
    (firstRestProj_comp_shuffleRep_tailAdditiveJucysMurphy_zero_comp_firstRestProj k ρ)
    (WithLp.ofLp f)) S
  simpa only [LinearMap.comp_apply, LinearMap.compLeft_apply, Function.comp_apply,
    firstRestHilbertProj_apply, shuffleHilbertRep_apply, hproj, firstRestProj_apply] using h

/-- **Pointwise Hilbert-carrier first-site normalized Jucys–Murphy rest-compression identity.** -/
theorem firstRestHilbertProj_shuffleHilbertRep_tailJucysMurphy_zero
    (k : ℕ) (ρ : TypeAHeckeAlgebra 𝕜 q (l + 1) →ₐ[𝕜] Module.End 𝕜 U)
    (f : PiLp 2 fun _ : ShuffleMask k (l + 1) ↦ U) (S : ShuffleMask k (l + 1)) :
    firstRestHilbertProj 𝕜 U
        (shuffleHilbertRep k ρ (tailJucysMurphy q (0 : Fin (k + (l + 1))))
          (firstRestHilbertProj 𝕜 U f)) S =
      ρ (tailJucysMurphy q (0 : Fin (l + 1))) (firstRestHilbertProj 𝕜 U f S) := by
  have hproj : WithLp.ofLp (firstRestHilbertProj 𝕜 U f) = firstRestProj 𝕜 U (WithLp.ofLp f) := rfl
  have h := congrFun (LinearMap.congr_fun
    (firstRestProj_comp_shuffleRep_tailJucysMurphy_zero_comp_firstRestProj k ρ)
    (WithLp.ofLp f)) S
  simpa only [LinearMap.comp_apply, LinearMap.compLeft_apply, Function.comp_apply,
    firstRestHilbertProj_apply, shuffleHilbertRep_apply, hproj, firstRestProj_apply] using h

/-- **Operator-level Hilbert-carrier first-site additive Jucys–Murphy rest-compression identity.**
Compressing `shuffleHilbertRep k ρ (tailAdditiveJucysMurphy q 0)` by `firstRestHilbertProj` equals
the fiberwise action of `ρ (tailAdditiveJucysMurphy q 0)` on `firstRestHilbertProj`. -/
theorem firstRestHilbertProj_comp_shuffleHilbertRep_tailAdditiveJucysMurphy_zero_comp
    (k : ℕ) (ρ : TypeAHeckeAlgebra 𝕜 q (l + 1) →ₐ[𝕜] Module.End 𝕜 U) :
    firstRestHilbertProj 𝕜 U ∘ₗ
        shuffleHilbertRep k ρ (tailAdditiveJucysMurphy q (0 : Fin (k + (l + 1)))) ∘ₗ
          firstRestHilbertProj 𝕜 U =
      (((WithLp.linearEquiv 2 𝕜 (ShuffleMask k (l + 1) → U)).symm.conjAlgEquiv 𝕜)
          ((ρ (tailAdditiveJucysMurphy q (0 : Fin (l + 1)))).compLeft (ShuffleMask k (l + 1)))) ∘ₗ
        firstRestHilbertProj 𝕜 U :=
  LinearMap.ext fun f ↦ PiLp.ext fun S ↦
    firstRestHilbertProj_shuffleHilbertRep_tailAdditiveJucysMurphy_zero k ρ f S

/-- **Operator-level Hilbert-carrier first-site normalized Jucys–Murphy rest-compression identity.**
Compressing `shuffleHilbertRep k ρ (tailJucysMurphy q 0)` by `firstRestHilbertProj` equals the
fiberwise action of `ρ (tailJucysMurphy q 0)` on `firstRestHilbertProj`. -/
theorem firstRestHilbertProj_comp_shuffleHilbertRep_tailJucysMurphy_zero_comp
    (k : ℕ) (ρ : TypeAHeckeAlgebra 𝕜 q (l + 1) →ₐ[𝕜] Module.End 𝕜 U) :
    firstRestHilbertProj 𝕜 U ∘ₗ
        shuffleHilbertRep k ρ (tailJucysMurphy q (0 : Fin (k + (l + 1)))) ∘ₗ
          firstRestHilbertProj 𝕜 U =
      (((WithLp.linearEquiv 2 𝕜 (ShuffleMask k (l + 1) → U)).symm.conjAlgEquiv 𝕜)
          ((ρ (tailJucysMurphy q (0 : Fin (l + 1)))).compLeft (ShuffleMask k (l + 1)))) ∘ₗ
        firstRestHilbertProj 𝕜 U :=
  LinearMap.ext fun f ↦ PiLp.ext fun S ↦
    firstRestHilbertProj_shuffleHilbertRep_tailJucysMurphy_zero k ρ f S

end TauCeti.TypeAHeckeAlgebra
