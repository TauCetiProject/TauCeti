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
source coefficient ring to be normed or complete. Continuity of the coefficient homomorphism is
needed only for the comparison formulas on arbitrary source-valued continuous test functions.

Composing this extension with character integration gives
`TauCeti.ContinuousMonoidHom.extendedCharacterRingHom`, the scalar map used to evaluate
pseudomeasures after clearing a character-dependent denominator. Its values
on source-valued characters agree with the original integrals after applying the coefficient map.
No map on a total quotient ring is asserted.

Use `TauCeti.AbstractMeasure.extendCoefficientsRingHom j hj`, or open
`TauCeti.AbstractMeasure` and write `extendCoefficientsRingHom j hj`.
Use `TauCeti.ContinuousMonoidHom.extendedCharacterRingHom χ j hj`, or open
`TauCeti.ContinuousMonoidHom` and write `extendedCharacterRingHom χ j hj`.
The spelling `χ.extendedCharacterRingHom j hj` does not elaborate even after opening this namespace,
because the character type is Mathlib's `ContinuousMonoidHom`.

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

/-- Cast an integer-valued continuous test into locally constant ring-valued tests. -/
private def intCastLocallyConstant {X R : Type*} [TopologicalSpace X] [IntCast R]
    (f : C(X, ℤ)) : LocallyConstant X R :=
  ⟨fun x ↦ (f x : R), ((IsLocallyConstant.iff_continuous _).mpr f.continuous).comp Int.cast⟩

/-- Transport an integer fibre-indicator decomposition into any topological commutative ring. -/
private theorem fiberIndicator_comp_eq_sum_intCast {X A R : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (q : C(X, A)) (m : C(X × X, X)) (a : A) {n : ℕ}
    (g h : Fin n → C(X, ℤ))
    (hgh : ∀ x y, (q.comp m).fiberIndicator (R := ℤ) a (x, y) = ∑ i, g i x * h i y) :
    (q.fiberIndicator (R := R) a).comp m =
      ∑ i, (intCastLocallyConstant (R := R) (g i) : C(X, R)).prodMul
        (intCastLocallyConstant (R := R) (h i)) := by
  classical
  ext p
  have hp := congrArg (Int.castRingHom R) (hgh p.1 p.2)
  simpa [fiberIndicator_apply, intCastLocallyConstant] using hp

/-- Extension of coefficients preserves convolution, including on noncommutative monoids. -/
@[simp]
theorem extendCoefficients_mul (μ ν : D(G, O)) :
    extendCoefficients j hj (μ * ν) =
      extendCoefficients j hj μ * extendCoefficients j hj ν := by
  classical
  apply finiteProjection_ext
  intro q
  ext a
  rw [finiteProjection_extendCoefficients, Finsupp.mapRange_apply,
    finiteProjection_apply, finiteProjection_apply]
  let m : C(G × G, G) := ⟨fun p ↦ p.1 * p.2, continuous_mul⟩
  let f : C(G × G, ℤ) := (q.comp m).fiberIndicator a
  -- Discrete integer-valued tests have exact finite sums of separated functions.
  obtain ⟨n, g, h, hgh⟩ := f.exists_finite_sum_mul_approximation_of_mem_uniformity
    (S := SetRel.id) (DiscreteUniformity.relId_mem_uniformity ℤ)
  let gO (i : Fin n) := intCastLocallyConstant (R := O) (g i)
  let hO (i : Fin n) := intCastLocallyConstant (R := O) (h i)
  have htestK : (q.fiberIndicator (R := K) a).comp m =
      ∑ i, ((gO i).map j : C(G, K)).prodMul ((hO i).map j) := by
    rw [fiberIndicator_comp_eq_sum_intCast (R := K) q m a g h hgh]
    apply Finset.sum_congr rfl
    intro i _
    congr 1 <;> ext x <;> simp [gO, hO, intCastLocallyConstant]
  simp only [mul_def, map_apply]
  rw [fiberIndicator_comp_eq_sum_intCast (R := O) q m a g h hgh, htestK]
  simp only [map_sum, prodMul_def, prodMk'_prod_apply, map_mul,
    extendCoefficients_apply_locallyConstant, gO, hO]

omit [ContinuousMul G] in
/-- The convolution identity, the Dirac measure at `1`, is preserved by coefficient extension. -/
@[simp]
theorem extendCoefficients_one : extendCoefficients j hj (1 : D(G, O)) = 1 := by
  simp [one_def]

/-- Extension from unit-ball coefficients as a unital ring homomorphism of convolution rings. -/
def extendCoefficientsRingHom : D(G, O) →+* D(G, K) :=
  { extendCoefficients j hj with
    map_one' := extendCoefficients_one j hj
    map_mul' := extendCoefficients_mul j hj }

/-- The ring homomorphism has the same underlying function as the additive coefficient extension. -/
@[simp]
theorem coe_extendCoefficientsRingHom :
    ⇑(extendCoefficientsRingHom (G := G) j hj) = extendCoefficients j hj :=
  (rfl)

end AbstractMeasure

namespace ContinuousMonoidHom

variable (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (hjc : Continuous j)

/-- Integration of a scalar-valued continuous character after extending integral coefficients.
This is a ring map on measures, not on their total quotient ring. -/
def extendedCharacterRingHom : D(G, O) →+* K :=
  χ.characterIntegralAlgHom.toRingHom.comp (AbstractMeasure.extendCoefficientsRingHom j hj)

/-- The extended character map integrates the character against the extended measure. -/
@[simp]
theorem extendedCharacterRingHom_apply (μ : D(G, O)) :
    extendedCharacterRingHom χ j hj μ = extendCoefficients j hj μ χ := by
  simp [extendedCharacterRingHom]

/-- The extended character map recovers the character on a Dirac measure. -/
theorem extendedCharacterRingHom_dirac (x : G) :
    extendedCharacterRingHom χ j hj (dirac O x) = χ x := by
  simp

include hjc in
/-- If a scalar-valued character is obtained by applying `j` to an `O`-valued character, its
extended integral is `j` applied to the original character integral. -/
theorem extendedCharacterRingHom_apply_eq_characterIntegralAlgHom (κ : G →ₜ* O)
    (hχ : ∀ x, χ x = j (κ x)) (μ : D(G, O)) :
    extendedCharacterRingHom χ j hj μ = j (κ.characterIntegralAlgHom μ) := by
  have htest : (χ : C(G, K)) = (⟨j, hjc⟩ : C(O, K)).comp κ := by
    ext x
    exact hχ x
  rw [extendedCharacterRingHom_apply, htest, extendCoefficients_apply_comp,
    ContinuousMonoidHom.characterIntegralAlgHom_apply]

end ContinuousMonoidHom

open TauCeti.AbstractMeasure TauCeti.ContinuousMonoidHom

variable (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)

/-! These computations check the multiplicity and the order of the convolution factors. -/

example (x y : G) (a b : O) :
    extendCoefficientsRingHom j hj ((a • dirac O x) * (b • dirac O y)) =
      (j a * j b) • dirac K (x * y) := by
  simp [smul_smul, mul_comm, dirac_mul_dirac]

example (χ : G →ₜ* K) (x : G) (a : O) :
    extendedCharacterRingHom χ j hj (a • dirac O x) = j a * χ x := by
  simp

example (χ : G →ₜ* K) (x : G) :
    extendedCharacterRingHom χ j hj (dirac O x - 1) = χ x - 1 := by
  rw [map_sub, map_one]
  simp

end TauCeti
