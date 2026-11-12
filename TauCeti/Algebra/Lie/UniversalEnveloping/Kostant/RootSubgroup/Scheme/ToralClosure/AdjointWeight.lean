/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Tangent

/-!
# Adjoint characters of the root vectors of a Kostant toral closure

Let `G` be the Kostant toral closure of a finite free Kostant-stable lattice with a basis of Cartan
weight vectors, and let the root generator `eᵢ` have integral weight `α`. The normalized root
vector `TauCeti.UniversalEnvelopingAlgebra.kostantToralRootVector` is then an eigenvector for the
weight torus of `G`, with eigencharacter `α` itself rather than its reduction modulo the
characteristic of a value ring. The adjoint-action equation holds with values in every commutative
ring, including nonreduced rings, without a smoothness assumption on `G`.

When the integral augmentation cotangent module is projective, the same vector, transported
through `Derivation.cotangentLinearEquiv`, belongs to the adjoint comodule weight space of `α`, and
a nonzero `α` is a nontrivial adjoint weight. Nothing here proves cotangent projectivity, that the
root lines exhaust their weight spaces, or maximality of the torus. As in the generic adjoint API,
projectivity refers to the cotangent algebra's integer module.

## Main results

All in the namespace `TauCeti.UniversalEnvelopingAlgebra`:

* `adDerivation_kostantWeightTorusToral_kostantToralRootVector`: torus points act on each
  normalized root vector through its root character.
* `mem_adjointWeightSpace_kostantWeightTorusToral_iff`: the adjoint weight-space criterion of the
  toral closure in matrix coordinates, assuming cotangent projectivity.
* `kostantToralRootVector_mem_adjointWeightSpace`: the normalized root vectors, viewed in the
  cotangent dual, have their prescribed adjoint weights.
* `weightCharacter_mem_nontrivialAdjointWeights_kostantWeightTorusToral`: every nonzero root
  weight is a nontrivial adjoint weight.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.

The weight-space interpretation uses `TauCeti.HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus`.
The matrix support calculation is
`TauCeti.UniversalEnvelopingAlgebra.kostantRootGeneratorIntMatrix_eq_zero_of_weight_ne`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

noncomputable section

-- Cotangent-projectivity hypotheses over `ℤ` are stated with `Algebra.toModule` and
-- `Ideal.instModuleCotangentOfAlgebra` given local priority over the additive-group module.
attribute [local instance high] Algebra.toModule
-- Keep the cotangent algebra module rather than the generic integer module on its additive group.
attribute [local instance high] Ideal.instModuleCotangentOfAlgebra

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Fintype κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)

omit [Fintype κ] in
/-- The weight-torus coordinate map of the Kostant toral closure, composed with the quotient
bialgebra map, is the general-linear weight-torus coordinate map. -/
private theorem kostantWeightTorusToralCoordinateMap_comp_mkBialgHom [Finite κ] :
    (kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt).hom.comp
        (Bialgebra.Quotient.mkBialgHom
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap wt).hom := by
  rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
    mkQuotient_comp_kostantWeightTorusToralCoordinateMap]

/-- Over any commutative value ring, the weight torus of the Kostant toral closure acts on each
normalized root vector through the weight of its root generator. This includes rings with
nilpotents. -/
theorem adDerivation_kostantWeightTorusToral_kostantToralRootVector {B : Type*} [CommRing B]
    (s : WithConv (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)) →ₐ[ℤ] B)) (i : I)
    {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) :
    Derivation.adDerivation B
        (Derivation.pointInCounitAlgebra
          (H := GeneralLinear.coordinateHopfAlgebra ℤ n ⧸
            (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal) B
          (toConv (s.ofConv.comp
            (kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt).hom.toAlgHom)))
        (kostantToralRootVector e h ρ M hM hnil b wt (B := B) i) =
      (DiagonalizableGroup.charOfPoint s.ofConv (SplitTorus.weightCharacter α) : B) •
        kostantToralRootVector e h ρ M hM hnil b wt (B := B) i := by
  apply HopfIdeal.quotientLieHom_injective (kostantToralDefiningIdeal e h ρ M hM hnil b wt)
  apply (GeneralLinear.tangentLinearEquivMatrix (R := ℤ) (B := B) n).injective
  rw [GeneralLinear.tangentLinearEquivMatrix_apply,
    GeneralLinear.tangentLinearEquivMatrix_apply]
  ext r s'
  rw [HopfIdeal.tangentMatrix_adDerivation_weightTorus_apply
    (kostantToralDefiningIdeal e h ρ M hM hnil b wt) wt
    (kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt).hom
    (kostantWeightTorusToralCoordinateMap_comp_mkBialgHom e h ρ M hM hnil b wt),
    map_smul, map_smul, Matrix.smul_apply, smul_eq_mul, tangentMatrix_kostantToralRootVector]
  by_cases hrs : wt r - wt s' = α
  · rw [hrs]
  · rw [Matrix.map_apply,
      kostantRootGeneratorIntMatrix_eq_zero_of_weight_ne e h ρ M hM b wt i hα hwt hrs]
    simp

variable [Module.Projective ℤ (Bialgebra.CotangentSpace ℤ
  (GeneralLinear.coordinateHopfAlgebra ℤ n ⧸
    (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal))]

/-- An adjoint weight vector of the Kostant toral closure has matrix entries only at the
corresponding weight differences of the lattice basis. Cotangent projectivity is needed for the
adjoint comodule, not for the entrywise torus-action equation. -/
theorem mem_adjointWeightSpace_kostantWeightTorusToral_iff (α : Multiplicative (κ →₀ ℤ))
    (x : Module.Dual ℤ (Bialgebra.CotangentSpace ℤ
      (GeneralLinear.coordinateHopfAlgebra ℤ n ⧸
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal))) :
    x ∈ Derivation.adjointWeightSpace
        (kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt).hom α ↔
      ∀ r s, SplitTorus.weightCharacter (wt r - wt s) ≠ α →
        GeneralLinear.tangentMatrix n
          (HopfIdeal.quotientLieHom (kostantToralDefiningIdeal e h ρ M hM hnil b wt)
            (Derivation.cotangentLinearEquiv (B := ℤ) x)) r s = 0 :=
  HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus
    (kostantToralDefiningIdeal e h ρ M hM hnil b wt) wt
    (kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt).hom
    (kostantWeightTorusToralCoordinateMap_comp_mkBialgHom e h ρ M hM hnil b wt) α x

/-- A normalized root vector of the Kostant toral closure, viewed in the cotangent dual, has the
weight of its root generator as adjoint character. -/
theorem kostantToralRootVector_mem_adjointWeightSpace (i : I) {α : κ → ℤ}
    (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) :
    (Derivation.cotangentLinearEquiv (B := ℤ)).symm
        (kostantToralRootVector e h ρ M hM hnil b wt (B := ℤ) i) ∈
      Derivation.adjointWeightSpace (kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt).hom
        (SplitTorus.weightCharacter α) := by
  rw [mem_adjointWeightSpace_kostantWeightTorusToral_iff]
  intro r s hrs
  rw [LinearEquiv.apply_symm_apply, tangentMatrix_kostantToralRootVector, Matrix.map_apply]
  simp only [Int.cast_id]
  exact kostantRootGeneratorIntMatrix_eq_zero_of_weight_ne e h ρ M hM b wt i hα hwt
    fun h ↦ hrs (congrArg _ h)

/-- The nonzero weight of a root generator is a nontrivial adjoint weight of the Kostant toral
closure, assuming its cotangent module is projective and its factored root coordinate map is
surjective. -/
theorem weightCharacter_mem_nontrivialAdjointWeights_kostantWeightTorusToral (i : I)
    {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V)) (hα₀ : α ≠ 0)
    (hi : Function.Surjective (kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i).hom) :
    SplitTorus.weightCharacter α ∈
      Derivation.nontrivialAdjointWeights
        (kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt).hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨fun h ↦ hα₀ ?_, fun hbot ↦ ?_⟩
  · ext j
    simpa using congrArg (fun c : Multiplicative (κ →₀ ℤ) ↦ Multiplicative.toAdd c j) h
  · have hv := kostantToralRootVector_mem_adjointWeightSpace e h ρ M hM hnil b wt i hα hwt
    rw [hbot, Submodule.mem_bot] at hv
    have hz := congrArg (Derivation.cotangentLinearEquiv (B := ℤ)) hv
    exact kostantToralRootVector_ne_zero e h ρ M hM hnil b wt i hi
      (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hz)

end

end TauCeti.UniversalEnvelopingAlgebra
