/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Convolution

/-!
# Change of coefficients for Hecke algebras

Let `φ : A →+* B` be a homomorphism of commutative semirings and `μ` an `A`-valued Haar measure on
a Hausdorff topological group `G`. Composing with `φ` sends a test function `f ∈ C_c^∞(G, A)` to
`φ ∘ f ∈ C_c^∞(G, B)` (`TauCeti.HaarMeasureWithValues.mapCoeff`), and the `B`-valued Haar measure
`φ μ = μ.map φ` integrates it to the image of the integral
(`TauCeti.HaarMeasureWithValues.integral_map_mapCoeff`): both are computed from an expansion
`f = ∑ 1_{K_i} • m_i` into indicators of compact open sets. Hence composing with `φ` turns
convolution against `μ` into convolution against `φ μ`
(`TauCeti.HaarMeasureWithValues.convolution_map_mapCoeff`), and is a homomorphism of non-unital
rings `H(G, A) → H(G, B)` (`TauCeti.HeckeAlgebra.mapCoeff`), semilinear over `φ`. This is the
coefficient-change map underlying `H(G, A) ⊗_A B ≅ H(G, B)`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.1, pp. 11–12.
-/

public section

open LocallyConstant

namespace TauCeti

variable {A B G : Type*} [CommSemiring A] [CommSemiring B] [TopologicalSpace G]

namespace HaarMeasureWithValues

variable (φ : A →+* B)

/-- Change of coefficients of test functions: `f ↦ φ ∘ f`, a `φ`-semilinear map
`C_c^∞(G, A) → C_c^∞(G, B)`. -/
noncomputable def mapCoeff : compactlySupported A G A →ₛₗ[φ] compactlySupported B G B where
  toFun f := ⟨(f : LocallyConstant G A).map φ,
    mem_compactlySupported.2 ((mem_compactlySupported.1 f.property).comp_left (map_zero φ))⟩
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp

/-- The value of `φ ∘ f` at `x` is `φ (f x)`. -/
@[simp]
theorem mapCoeff_apply (f : compactlySupported A G A) (x : G) :
    (mapCoeff φ f : LocallyConstant G B) x = φ ((f : LocallyConstant G A) x) :=
  (rfl)

variable [Group G] [ContinuousConstSMul G G] [T2Space G] (μ : HaarMeasureWithValues A G)

/-- **Integration commutes with change of coefficients**: `∫ φ ∘ f d(φ μ) = φ (∫ f dμ)`. -/
theorem integral_map_mapCoeff (f : compactlySupported A G A) :
    (μ.map (φ : A →+ B)).integral (mapCoeff φ f) = φ (μ.integral f) := by
  classical
  obtain ⟨s, K, hf⟩ := exists_eq_sum_compactOpenIndicator (mem_compactlySupported.1 f.property)
  have hφf : (mapCoeff φ f : LocallyConstant G B) =
      ∑ m ∈ s, compactOpenIndicator (K m) (φ m) := by
    ext x
    rw [mapCoeff_apply, hf]
    simp only [← LocallyConstant.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    by_cases hx : x ∈ K m
    · simp [hx]
    · simp [hx]
  rw [integral_eq_sum_smul_of_eq_sum_compactOpenIndicator _ _ s K (fun m ↦ φ m) hφf,
    integral_eq_sum_smul_of_eq_sum_compactOpenIndicator μ f s K id hf, map_sum]
  simp

variable [IsTopologicalGroup G]

/-- **Convolution commutes with change of coefficients**:
`(φ ∘ f₁) ⋆_{φ μ} (φ ∘ f₂) = φ ∘ (f₁ ⋆_μ f₂)`. -/
theorem convolution_map_mapCoeff (f₁ f₂ : compactlySupported A G A) :
    (μ.map (φ : A →+ B)).convolution (mapCoeff φ f₁) (mapCoeff φ f₂) =
      mapCoeff φ (μ.convolution f₁ f₂) := by
  ext x
  rw [convolution_apply, mapCoeff_apply, convolution_apply, ← integral_map_mapCoeff]
  congr 1
  ext y
  simp

end HaarMeasureWithValues

namespace HeckeAlgebra

variable [Group G] [IsTopologicalGroup G] [T2Space G] (φ : A →+* B)
  (μ : HaarMeasureWithValues A G)

/-- **Change of coefficients for Hecke algebras**: composing with a ring homomorphism
`φ : A →+* B` is a homomorphism of non-unital rings `H(G, A) → H(G, B)`, the Hecke algebra of
`G` with respect to `μ` mapping to that with respect to `φ μ`. -/
noncomputable def mapCoeff :
    HeckeAlgebra μ →ₙ+* HeckeAlgebra (μ.map (φ : A →+ B)) where
  toFun f := ⟨HaarMeasureWithValues.mapCoeff φ f.toCompactlySupported⟩
  map_mul' f₁ f₂ := by
    ext1
    exact (HaarMeasureWithValues.convolution_map_mapCoeff φ μ _ _).symm
  map_zero' := by
    ext1
    simp
  map_add' f₁ f₂ := by
    ext1
    simp

/-- `mapCoeff φ μ f` is `φ ∘ f`. -/
@[simp]
theorem toCompactlySupported_mapCoeff (f : HeckeAlgebra μ) :
    (mapCoeff φ μ f).toCompactlySupported =
      HaarMeasureWithValues.mapCoeff φ f.toCompactlySupported :=
  (rfl)

/-- `mapCoeff φ μ` is `φ`-semilinear. -/
theorem mapCoeff_smul (c : A) (f : HeckeAlgebra μ) :
    mapCoeff φ μ (c • f) = φ c • mapCoeff φ μ f := by
  ext1
  exact (HaarMeasureWithValues.mapCoeff φ).map_smulₛₗ c f.toCompactlySupported

end HeckeAlgebra

end TauCeti
