/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.FreeProduct.VonNeumann
public import TauCeti.Probability.FreeProbability.Law.Basic

/-!
# Simultaneous C⋆- and von Neumann realizations of compactly supported laws

Let `μ : I → Measure ℝ` be an arbitrary family of measures on `ℝ`. Each compactly supported
probability measure `μ i` is realized in the commutative C⋆-algebra `C((μ i).support, ℂ)` as the
law of the real coordinate function `x ↦ x` with respect to integration against `μ i` (with a
trivial one-point fallback at `0` for indices outside compactly supported probability measures so
the ambient realization carries no proof parameters in its types). Forming the reduced C⋆-free
product of these commutative factors and passing to its generated von Neumann algebra produces:

1. A unital C⋆-algebra `FreeLawRealization.cstarAlgebra μ` equipped with a **tracial** state
   `cstarState μ` and freely independent selfadjoint elements `cstarElement μ i` such that, whenever
   `μ i` is a compactly supported probability measure, `(cstarState μ).law (cstarElement μ i) = μ i`
   and `spectrum ℝ (cstarElement μ i) ⊆ (μ i).support`.
2. A concrete von Neumann algebra `FreeLawRealization.vonNeumannAlgebra μ` on the completed GNS
   Hilbert space, equipped with a **tracial** vacuum vector state `vonNeumannState μ` and freely
   independent selfadjoint operators `vonNeumannElement μ i` (whose generated von Neumann
   subalgebras are also freely independent) with the same laws and spectral inclusions.
3. The canonical state-preserving star-algebra inclusion `toVonNeumann μ` transporting any
   selfadjoint noncommutative polynomial or continuous-functional-calculus expression from the
   C⋆-realization to the von Neumann realization without changing its law.

## Main declarations

* `TauCeti.FreeLawRealization.cstarAlgebra`, `cstarState`, `cstarElement`: the tracial reduced
  C⋆-realization of a family of compactly supported probability measures on `ℝ`.
* `TauCeti.FreeLawRealization.vonNeumannAlgebra`, `vonNeumannState`, `vonNeumannElement`: the
  tracial von Neumann realization on the completed GNS Hilbert space.
* `TauCeti.FreeLawRealization.toVonNeumann`, `law_toVonNeumann`: state- and law-preserving
  transport from the C⋆-realization into the von Neumann realization.
* `TauCeti.FreeLawRealization.cstarState_mul_comm`,
  `TauCeti.FreeLawRealization.vonNeumannState_mul_comm`: traciality of both vacuum states.
* `TauCeti.FreeLawRealization.law_cstarElement`, `TauCeti.FreeLawRealization.law_vonNeumannElement`,
  `TauCeti.FreeLawRealization.spectrum_cstarElement_subset_support`,
  `TauCeti.FreeLawRealization.spectrum_vonNeumannElement_subset_support`: per-index law
  identifications and spectral bounds by the measure supports.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §§1.5, 3.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 3 and 7.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder

namespace TauCeti
namespace FreeLawRealization

section Factor

open Classical in
/-- The compact support set used to realize `μ` as a commutative C⋆-factor: `μ.support` when `μ`
is a compactly supported probability measure, and `{0}` otherwise. -/
def compactSupport (μ : Measure ℝ) : Set ℝ :=
  if IsProbabilityMeasure μ ∧ IsCompact μ.support then μ.support else {0}

private theorem isCompact_compactSupport (μ : Measure ℝ) : IsCompact (compactSupport μ) := by
  classical
  unfold compactSupport
  split_ifs with h
  · exact h.2
  · exact isCompact_singleton

instance (μ : Measure ℝ) : CompactSpace (compactSupport μ) :=
  isCompact_iff_compactSpace.1 (isCompact_compactSupport μ)

private def factorCoord (μ : Measure ℝ) : C(compactSupport μ, ℂ) :=
  (ContinuousMap.restrict (compactSupport μ) (ContinuousMap.id ℝ)).realToRCLike ℂ

private theorem isSelfAdjoint_factorCoord (μ : Measure ℝ) :
    IsSelfAdjoint (factorCoord μ) :=
  ContinuousMap.isSelfAdjoint_realToRCLike ℂ

private theorem spectrum_factorCoord {μ : Measure ℝ} [hP : IsProbabilityMeasure μ]
    (hK : IsCompact μ.support) :
    spectrum ℝ (factorCoord μ) = μ.support := by
  rw [factorCoord, ContinuousMap.spectrum_realToRCLike, ContinuousMap.spectrum_eq_range]
  have hcs : compactSupport μ = μ.support := by simp [compactSupport, hP, hK]
  ext x
  simp [ContinuousMap.restrict, hcs]

open Classical in
private def factorPositiveLinearMap (μ : Measure ℝ) : C(compactSupport μ, ℂ) →ₚ[ℂ] ℂ :=
  if h : IsProbabilityMeasure μ ∧ IsCompact μ.support then
    let _ : IsProbabilityMeasure μ := h.1
    ContinuousMap.integralPositiveLinearMap (μ.comap ((↑) : compactSupport μ → ℝ))
  else
    ContinuousMap.integralPositiveLinearMap (Measure.dirac ⟨0, by simp [compactSupport, h]⟩)

private theorem law_factorCoord {μ : Measure ℝ} [hP : IsProbabilityMeasure μ]
    (hK : IsCompact μ.support) :
    (factorPositiveLinearMap μ).law (factorCoord μ) = μ := by
  have hfp : factorPositiveLinearMap μ =
      ContinuousMap.integralPositiveLinearMap (μ.comap ((↑) : compactSupport μ → ℝ)) := by
    simp [factorPositiveLinearMap, hP, hK]
  have hcompl : μ (compactSupport μ)ᶜ = 0 := by
    rw [show compactSupport μ = μ.support by simp [compactSupport, hP, hK]]
    exact μ.measure_compl_support
  rw [hfp, factorCoord]
  exact PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id hcompl

/-- Integration against `μ` on `compactSupport μ` (or against `δ₀` outside compactly supported
probability measures) as a unital `StarPositiveFunctional` on `C(compactSupport μ, ℂ)`. -/
def factorFunctional (μ : Measure ℝ) : StarPositiveFunctional C(compactSupport μ, ℂ) :=
  StarPositiveFunctional.ofPositiveLinearMap (factorPositiveLinearMap μ)

private theorem factorFunctional_apply (μ : Measure ℝ) (a : C(compactSupport μ, ℂ)) :
    factorFunctional μ a = factorPositiveLinearMap μ a :=
  StarPositiveFunctional.ofPositiveLinearMap_apply (factorPositiveLinearMap μ) a

/-- `factorFunctional μ` is normalized (`factorFunctional μ 1 = 1`) for every measure `μ`. -/
@[simp]
theorem factorFunctional_one (μ : Measure ℝ) : factorFunctional μ 1 = 1 := by
  classical
  rw [factorFunctional_apply]
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support
  · have := h.1
    rw [← (factorPositiveLinearMap μ).ofReal_law_real_univ (isSelfAdjoint_factorCoord μ),
      law_factorCoord h.2]
    simp
  · have hfp : factorPositiveLinearMap μ =
        ContinuousMap.integralPositiveLinearMap (Measure.dirac ⟨0, by simp [compactSupport, h]⟩) :=
      by simp [factorPositiveLinearMap, h]
    rw [hfp, ContinuousMap.integralPositiveLinearMap_apply]
    simp

private theorem factorFunctional_mul_comm (μ : Measure ℝ) (a b : C(compactSupport μ, ℂ)) :
    factorFunctional μ (a * b) = factorFunctional μ (b * a) := by
  rw [mul_comm]

attribute [irreducible] compactSupport factorCoord factorPositiveLinearMap factorFunctional

end Factor

variable {I : Type*} [DecidableEq I]

/-! ### Reduced C⋆-realization -/

/-- The completed GNS Hilbert space of the free-product realization of `μ : I → Measure ℝ`. -/
abbrev HilbertSpace (μ : I → Measure ℝ) : Type _ :=
  ReducedFreeProduct.HilbertSpace (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

/-- The unital C⋆-algebra of the reduced free-product realization of `μ`, realized as a closed star
subalgebra of bounded operators on `HilbertSpace μ`. -/
abbrev cstarAlgebra (μ : I → Measure ℝ) :
    StarSubalgebra ℂ (HilbertSpace μ →L[ℂ] HilbertSpace μ) :=
  ReducedFreeProduct.algebra (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

/-- The vacuum state on `cstarAlgebra μ`. -/
def cstarState (μ : I → Measure ℝ) : cstarAlgebra μ →ₚ[ℂ] ℂ :=
  ReducedFreeProduct.state (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

@[simp]
theorem cstarState_one (μ : I → Measure ℝ) : cstarState μ 1 = 1 :=
  ReducedFreeProduct.state_one (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

/-- Because each commutative factor functional is tracial, `cstarState μ` is tracial on
`cstarAlgebra μ`. -/
theorem cstarState_mul_comm (μ : I → Measure ℝ) (x y : cstarAlgebra μ) :
    cstarState μ (x * y) = cstarState μ (y * x) :=
  ReducedFreeProduct.state_mul_comm (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i)) (fun i => factorFunctional_mul_comm (μ i)) x y

private def cstarFactor (μ : I → Measure ℝ) (i : I) :
    C(compactSupport (μ i), ℂ) →⋆ₐ[ℂ] cstarAlgebra μ :=
  ReducedFreeProduct.factor (fun j => factorFunctional (μ j))
    (fun j => factorFunctional_one (μ j)) i

/-- The `i`-th canonical factor subalgebra in `cstarAlgebra μ`. -/
def cstarSubalgebra (μ : I → Measure ℝ) (i : I) : Subalgebra ℂ (cstarAlgebra μ) :=
  (cstarFactor μ i).toAlgHom.range

/-- The factor subalgebras `cstarSubalgebra μ i` are freely independent for `cstarState μ`. -/
theorem isFreelyIndependent_cstarSubalgebra (μ : I → Measure ℝ) :
    IsFreelyIndependent (cstarState μ).toLinearMap (cstarSubalgebra μ) :=
  ReducedFreeProduct.isFreelyIndependent_factor (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

/-- The `i`-th selfadjoint generator in `cstarAlgebra μ`. When `μ i` is a compactly supported
probability measure, its law under `cstarState μ` is `μ i`. -/
def cstarElement (μ : I → Measure ℝ) (i : I) : cstarAlgebra μ :=
  cstarFactor μ i (factorCoord (μ i))

/-- `cstarElement μ i` lies in the `i`-th factor subalgebra `cstarSubalgebra μ i`. -/
theorem cstarElement_mem_cstarSubalgebra (μ : I → Measure ℝ) (i : I) :
    cstarElement μ i ∈ cstarSubalgebra μ i :=
  ⟨factorCoord (μ i), rfl⟩

/-- Every generator `cstarElement μ i` is selfadjoint. -/
theorem isSelfAdjoint_cstarElement (μ : I → Measure ℝ) (i : I) :
    IsSelfAdjoint (cstarElement μ i) :=
  (isSelfAdjoint_factorCoord (μ i)).map (cstarFactor μ i)

/-- The elements `cstarElement μ i` are freely independent for `cstarState μ`. -/
theorem isFreelyIndependentElements_cstarElement (μ : I → Measure ℝ) :
    IsFreelyIndependentElements (cstarState μ).toLinearMap (cstarElement μ) := by
  rw [isFreelyIndependentElements_iff]
  exact (isFreelyIndependent_cstarSubalgebra μ).mono fun i =>
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (cstarElement_mem_cstarSubalgebra μ i))

/-- When `μ i` is a compactly supported probability measure, the law of `cstarElement μ i` with
respect to `cstarState μ` is `μ i`. -/
theorem law_cstarElement {μ : I → Measure ℝ} {i : I} [IsProbabilityMeasure (μ i)]
    (hμ : IsCompact (μ i).support) :
    (cstarState μ).law (cstarElement μ i) = μ i :=
  (PositiveLinearMap.law_map_starAlgHom (factorPositiveLinearMap (μ i)) (cstarState μ)
    (cstarFactor μ i) (fun x => (ReducedFreeProduct.state_factor
      (fun j => factorFunctional (μ j)) (fun j => factorFunctional_one (μ j)) i x).trans
      (factorFunctional_apply (μ i) x)) (isSelfAdjoint_factorCoord (μ i))).trans
    (law_factorCoord hμ)

/-- When `μ i` is a compactly supported probability measure, the real spectrum of
`cstarElement μ i` is contained in `(μ i).support`. -/
theorem spectrum_cstarElement_subset_support {μ : I → Measure ℝ} {i : I}
    [IsProbabilityMeasure (μ i)] (hμ : IsCompact (μ i).support) :
    spectrum ℝ (cstarElement μ i) ⊆ (μ i).support := by
  let π : C(compactSupport (μ i), ℂ) →ₐ[ℝ] cstarAlgebra μ :=
    (cstarFactor μ i).toAlgHom.restrictScalars ℝ
  exact (AlgHom.spectrum_apply_subset π (factorCoord (μ i))).trans_eq (spectrum_factorCoord hμ)

/-! ### Concrete von Neumann realization and transport -/

/-- The concrete von Neumann algebra generated by `cstarAlgebra μ` on `HilbertSpace μ`. -/
abbrev vonNeumannAlgebra (μ : I → Measure ℝ) : VonNeumannAlgebra (HilbertSpace μ) :=
  ReducedFreeProduct.vonNeumannAlgebra (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

/-- The canonical unital star-algebra inclusion from `cstarAlgebra μ` into `vonNeumannAlgebra μ`. -/
def toVonNeumann (μ : I → Measure ℝ) : cstarAlgebra μ →⋆ₐ[ℂ] vonNeumannAlgebra μ :=
  ReducedFreeProduct.toVonNeumann (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

/-- The tracial vacuum vector state on `vonNeumannAlgebra μ`. -/
def vonNeumannState (μ : I → Measure ℝ) : vonNeumannAlgebra μ →ₚ[ℂ] ℂ :=
  ReducedFreeProduct.vonNeumannState (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

@[simp]
theorem vonNeumannState_toVonNeumann (μ : I → Measure ℝ) (x : cstarAlgebra μ) :
    vonNeumannState μ (toVonNeumann μ x) = cstarState μ x :=
  ReducedFreeProduct.vonNeumannState_toVonNeumann
    (fun i => factorFunctional (μ i)) (fun i => factorFunctional_one (μ i)) x

@[simp]
theorem vonNeumannState_one (μ : I → Measure ℝ) : vonNeumannState μ 1 = 1 :=
  ReducedFreeProduct.vonNeumannState_one (fun i => factorFunctional (μ i))
    (fun i => factorFunctional_one (μ i))

/-- The vacuum vector state `vonNeumannState μ` is tracial on `vonNeumannAlgebra μ`. -/
theorem vonNeumannState_mul_comm (μ : I → Measure ℝ) (x y : vonNeumannAlgebra μ) :
    vonNeumannState μ (x * y) = vonNeumannState μ (y * x) :=
  ReducedFreeProduct.vonNeumannState_mul_comm
    (fun i => factorFunctional (μ i)) (fun i => factorFunctional_one (μ i))
    (fun i => factorFunctional_mul_comm (μ i)) x y

/-- Transporting any selfadjoint element from the C⋆-realization to the von Neumann realization
preserves its law. -/
theorem law_toVonNeumann (μ : I → Measure ℝ) {x : cstarAlgebra μ} (hx : IsSelfAdjoint x) :
    (vonNeumannState μ).law (toVonNeumann μ x) = (cstarState μ).law x :=
  PositiveLinearMap.law_map_starAlgHom (cstarState μ) (vonNeumannState μ) (toVonNeumann μ)
    (vonNeumannState_toVonNeumann μ) hx

/-- The `i`-th selfadjoint generator in `vonNeumannAlgebra μ`, transported from
`cstarElement μ i`. -/
def vonNeumannElement (μ : I → Measure ℝ) (i : I) : vonNeumannAlgebra μ :=
  toVonNeumann μ (cstarElement μ i)

@[simp]
theorem toVonNeumann_cstarElement (μ : I → Measure ℝ) (i : I) :
    toVonNeumann μ (cstarElement μ i) = vonNeumannElement μ i :=
  (rfl)

/-- Every generator `vonNeumannElement μ i` is selfadjoint. -/
theorem isSelfAdjoint_vonNeumannElement (μ : I → Measure ℝ) (i : I) :
    IsSelfAdjoint (vonNeumannElement μ i) :=
  (isSelfAdjoint_cstarElement μ i).map (toVonNeumann μ)

/-- The von Neumann subalgebra generated by the `i`-th factor inside `vonNeumannAlgebra μ`, viewed
as a subalgebra of `vonNeumannAlgebra μ`. -/
def vonNeumannSubalgebra (μ : I → Measure ℝ) (i : I) : Subalgebra ℂ (vonNeumannAlgebra μ) :=
  (VonNeumannAlgebra.adjoin (Set.range fun a =>
    (ReducedFreeProduct.vonNeumannFactor
      (fun j => factorFunctional (μ j))
      (fun j => factorFunctional_one (μ j)) i a).1)).toSubalgebra.comap
    (SubalgebraClass.val (vonNeumannAlgebra μ))

/-- The generated von Neumann subalgebras `vonNeumannSubalgebra μ i` are freely independent for
`vonNeumannState μ`. -/
theorem isFreelyIndependent_vonNeumannSubalgebra (μ : I → Measure ℝ) :
    IsFreelyIndependent (vonNeumannState μ).toLinearMap (vonNeumannSubalgebra μ) :=
  ReducedFreeProduct.isFreelyIndependent_adjoin_vonNeumannFactor
    (fun i => factorFunctional (μ i)) (fun i => factorFunctional_one (μ i))

/-- `vonNeumannElement μ i` lies in the `i`-th generated von Neumann subalgebra. -/
theorem vonNeumannElement_mem_vonNeumannSubalgebra (μ : I → Measure ℝ) (i : I) :
    vonNeumannElement μ i ∈ vonNeumannSubalgebra μ i :=
  VonNeumannAlgebra.subset_adjoin _ ⟨factorCoord (μ i),
    congrArg Subtype.val (ReducedFreeProduct.vonNeumannFactor_apply
      (fun j => factorFunctional (μ j)) (fun j => factorFunctional_one (μ j))
      i (factorCoord (μ i)))⟩

/-- The operators `vonNeumannElement μ i` are freely independent for `vonNeumannState μ`. -/
theorem isFreelyIndependentElements_vonNeumannElement (μ : I → Measure ℝ) :
    IsFreelyIndependentElements (vonNeumannState μ).toLinearMap (vonNeumannElement μ) := by
  rw [isFreelyIndependentElements_iff]
  exact (isFreelyIndependent_vonNeumannSubalgebra μ).mono fun i =>
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (vonNeumannElement_mem_vonNeumannSubalgebra μ i))

/-- When `μ i` is a compactly supported probability measure, the law of `vonNeumannElement μ i`
with respect to `vonNeumannState μ` is `μ i`. -/
theorem law_vonNeumannElement {μ : I → Measure ℝ} {i : I} [IsProbabilityMeasure (μ i)]
    (hμ : IsCompact (μ i).support) :
    (vonNeumannState μ).law (vonNeumannElement μ i) = μ i :=
  (law_toVonNeumann μ (isSelfAdjoint_cstarElement μ i)).trans (law_cstarElement hμ)

/-- When `μ i` is a compactly supported probability measure, the real spectrum of
`vonNeumannElement μ i` is contained in `(μ i).support`. -/
theorem spectrum_vonNeumannElement_subset_support {μ : I → Measure ℝ} {i : I}
    [IsProbabilityMeasure (μ i)] (hμ : IsCompact (μ i).support) :
    spectrum ℝ (vonNeumannElement μ i) ⊆ (μ i).support := by
  let π : cstarAlgebra μ →ₐ[ℝ] vonNeumannAlgebra μ :=
    (toVonNeumann μ).toAlgHom.restrictScalars ℝ
  exact (AlgHom.spectrum_apply_subset π (cstarElement μ i)).trans
    (spectrum_cstarElement_subset_support hμ)

end FreeLawRealization
end TauCeti
