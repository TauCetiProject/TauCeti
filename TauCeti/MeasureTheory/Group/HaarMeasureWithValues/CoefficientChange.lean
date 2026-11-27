/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Convolution
public import TauCeti.Topology.LocallyConstant.CompactSupport.MapCoeff

/-!
# Change of coefficients for Hecke algebras

Let `φ : A →+* B` be a homomorphism of commutative semirings and `μ` an `A`-valued Haar measure on
a Hausdorff topological group `G`. Composing with `φ` sends a test function `f ∈ C_c^∞(G, A)` to
`φ ∘ f ∈ C_c^∞(G, B)` (`LocallyConstant.compactlySupported.map` along `φ`, viewed as a
`φ`-semilinear map `A → B`), and the `B`-valued Haar measure `φ μ = μ.map φ` integrates it to the
image of the integral, by naturality of the integral under semilinear maps
(`TauCeti.HaarMeasureWithValues.integral_comp_commSL`). Hence composing with `φ` turns
convolution against `μ` into convolution against `φ μ`
(`TauCeti.HaarMeasureWithValues.convolution_map_map`), and is a homomorphism of non-unital
semirings `H(G, A) → H(G, B)` (of non-unital rings when `A` and `B` are rings)
(`TauCeti.HeckeAlgebra.mapCoeff`), semilinear over `φ`. This is the coefficient-change map
underlying `H(G, A) ⊗_A B ≅ H(G, B)`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.1, pp. 11–12.
-/

public section

open LocallyConstant

namespace TauCeti

variable {A B G : Type*} [CommSemiring A] [CommSemiring B] [TopologicalSpace G]

namespace HaarMeasureWithValues

variable (φ : A →+* B) [Group G] [IsTopologicalGroup G] [T2Space G]
  (μ : HaarMeasureWithValues A G)

/-- **Convolution commutes with change of coefficients**:
`(φ ∘ f₁) ⋆_{φ μ} (φ ∘ f₂) = φ ∘ (f₁ ⋆_μ f₂)`. -/
@[simp]
theorem convolution_map_map (f₁ f₂ : compactlySupported A G A) :
    (μ.map (φ : A →+ B)).convolution (compactlySupported.map φ.toSemilinearMap f₁)
        (compactlySupported.map φ.toSemilinearMap f₂) =
      compactlySupported.map φ.toSemilinearMap (μ.convolution f₁ f₂) := by
  ext x
  rw [convolution_apply, compactlySupported.map_apply, convolution_apply,
    ← integral_comp_commSL μ φ φ.toSemilinearMap]
  congr 1
  ext y
  simp

end HaarMeasureWithValues

namespace HeckeAlgebra

variable [Group G] [IsTopologicalGroup G] [T2Space G] (φ : A →+* B)
  (μ : HaarMeasureWithValues A G)

/-- **Change of coefficients for Hecke algebras**: composing with a ring homomorphism
`φ : A →+* B` is a homomorphism of non-unital semirings `H(G, A) → H(G, B)` (of non-unital rings
when `A` and `B` are rings), the Hecke algebra of `G` with respect to `μ` mapping to that with
respect to `φ μ`. -/
noncomputable def mapCoeff :
    HeckeAlgebra μ →ₙ+* HeckeAlgebra (μ.map (φ : A →+ B)) where
  toFun f := ⟨compactlySupported.map φ.toSemilinearMap f.toCompactlySupported⟩
  map_mul' f₁ f₂ := by
    ext1
    exact (HaarMeasureWithValues.convolution_map_map φ μ _ _).symm
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
      compactlySupported.map φ.toSemilinearMap f.toCompactlySupported :=
  (rfl)

/-- `mapCoeff φ μ` is `φ`-semilinear. -/
@[simp]
theorem mapCoeff_smul (c : A) (f : HeckeAlgebra μ) :
    mapCoeff φ μ (c • f) = φ c • mapCoeff φ μ f := by
  ext1
  exact (compactlySupported.map φ.toSemilinearMap).map_smulₛₗ c f.toCompactlySupported

end HeckeAlgebra

end TauCeti
