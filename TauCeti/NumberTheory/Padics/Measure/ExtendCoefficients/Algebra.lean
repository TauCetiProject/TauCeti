/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Basic
public import TauCeti.NumberTheory.Padics.Measure.CharacterIntegral

/-!
# Coefficient extension and convolution

Extension of coefficients from the closed unit ball respects the right-handed convolution of
measures on a profinite topological monoid. The ring homomorphism
`TauCeti.AbstractMeasure.extendCoefficientsRingHom` makes the extension available to ring-theoretic
constructions, without requiring the monoid to be commutative or the
source coefficient ring to be normed or complete. The coefficient homomorphism is assumed
continuous; an isometric coefficient embedding satisfies this hypothesis when the source carries
its norm topology.

Composing this extension with character integration gives
`TauCeti.ContinuousMonoidHom.extendedCharacterRingHom`, the scalar map used to evaluate
pseudomeasures after clearing a character-dependent denominator. Its values
on source-valued characters agree with the original integrals after applying the coefficient map.
No map on a total quotient ring is asserted.

The extension is `AbstractMeasure.extendCoefficients`, and convolution and character integration
are the existing `AbstractMeasure` and `ContinuousMonoidHom` constructions. No topology or norm
instance on measures is introduced.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Sections 3.3
  and 3.6, Proposition 3.16 and Definition 3.34.
-/

public noncomputable section

open AbstractMeasure ContinuousMap

namespace TauCeti

variable {G O K : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [Monoid G] [ContinuousMul G]

namespace AbstractMeasure

variable (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (hjc : Continuous j)

/-- Right convolution of an extended measure with a coefficient-extended test function is the
coefficient extension of the original right convolution. -/
theorem convolveFunRight_extendCoefficients_comp (ν : D(G, O)) (f : C(G, O)) :
    convolveFunRight (extendCoefficients j hj ν) ((⟨j, hjc⟩ : C(O, K)).comp f) =
      (⟨j, hjc⟩ : C(O, K)).comp (convolveFunRight ν f) := by
  ext x
  simp only [convolveFunRight_apply, comp_apply]
  exact extendCoefficients_apply_comp j ν hj hjc
    ⟨fun y ↦ f (x * y), by fun_prop⟩

include hjc in
/-- Extension of coefficients preserves convolution, including on noncommutative monoids. -/
@[simp]
theorem extendCoefficients_mul (μ ν : D(G, O)) :
    extendCoefficients j hj (μ * ν) =
      extendCoefficients j hj μ * extendCoefficients j hj ν := by
  symm
  apply eq_extendCoefficients_of_apply_comp j (μ * ν) hj hjc
  intro f
  rw [AbstractMeasure.mul_apply, convolveFunRight_extendCoefficients_comp j hj hjc,
    extendCoefficients_apply_comp, AbstractMeasure.mul_apply]

omit [ContinuousMul G] in
/-- The convolution identity, the Dirac measure at `1`, is preserved by coefficient extension. -/
@[simp]
theorem extendCoefficients_one : extendCoefficients j hj (1 : D(G, O)) = 1 := by
  simp [one_def]

/-- Extension from unit-ball coefficients as a unital ring homomorphism of convolution rings. -/
def extendCoefficientsRingHom : D(G, O) →+* D(G, K) :=
  { extendCoefficients j hj with
    map_one' := extendCoefficients_one j hj
    map_mul' := extendCoefficients_mul j hj hjc }

/-- The ring homomorphism has the same underlying function as the additive coefficient extension. -/
@[simp]
theorem coe_extendCoefficientsRingHom :
    ⇑(extendCoefficientsRingHom (G := G) j hj hjc) = extendCoefficients j hj :=
  (rfl)

end AbstractMeasure

namespace ContinuousMonoidHom

variable (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (hjc : Continuous j)

/-- Integration of a scalar-valued continuous character after extending integral coefficients.
This is a ring map on measures, not on their total quotient ring. -/
def extendedCharacterRingHom : D(G, O) →+* K :=
  χ.characterIntegralAlgHom.toRingHom.comp (AbstractMeasure.extendCoefficientsRingHom j hj hjc)

/-- The extended character map integrates the character against the extended measure. -/
@[simp]
theorem extendedCharacterRingHom_apply (μ : D(G, O)) :
    extendedCharacterRingHom χ j hj hjc μ = extendCoefficients j hj μ χ := by
  simp [extendedCharacterRingHom]

/-- The extended character map recovers the character on a Dirac measure. -/
theorem extendedCharacterRingHom_dirac (x : G) :
    extendedCharacterRingHom χ j hj hjc (dirac O x) = χ x := by
  simp

/-- If a scalar-valued character is obtained by applying `j` to an `O`-valued character, its
extended integral is `j` applied to the original character integral. -/
theorem extendedCharacterRingHom_eq_of_forall_eq (κ : G →ₜ* O)
    (hχ : ∀ x, χ x = j (κ x)) (μ : D(G, O)) :
    extendedCharacterRingHom χ j hj hjc μ = j (κ.characterIntegralAlgHom μ) := by
  have htest : (χ : C(G, K)) = (⟨j, hjc⟩ : C(O, K)).comp κ := by
    ext x
    exact hχ x
  rw [extendedCharacterRingHom_apply, htest, extendCoefficients_apply_comp,
    ContinuousMonoidHom.characterIntegralAlgHom_apply]

end ContinuousMonoidHom

open TauCeti.AbstractMeasure TauCeti.ContinuousMonoidHom

variable (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (hjc : Continuous j)

/-! These computations check the multiplicity and the order of the convolution factors. -/

example (x y : G) (a b : O) :
    extendCoefficientsRingHom j hj hjc ((a • dirac O x) * (b • dirac O y)) =
      (j a * j b) • dirac K (x * y) := by
  simp [smul_smul, mul_comm, dirac_mul_dirac]

example (χ : G →ₜ* K) (x : G) (a : O) :
    extendedCharacterRingHom χ j hj hjc (a • dirac O x) = j a * χ x := by
  simp

example (χ : G →ₜ* K) (x : G) :
    extendedCharacterRingHom χ j hj hjc (dirac O x - 1) = χ x - 1 := by
  rw [map_sub, map_one]
  simp

end TauCeti
