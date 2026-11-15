/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Completion

/-!
# Evaluation of `A⟨X⟩_T` and its completion as `A`-algebra homomorphisms

When the target `B` of Wedhorn's evaluation (Proposition 5.50) is an `A`-algebra with structure
map continuous at `0`, the evaluation homomorphisms `TauCeti.Huber.weightedEvalHom` and
`TauCeti.Huber.weightedEvalHomCompletion` commute with `algebraMap` and therefore bundle as
continuous `A`-algebra homomorphisms. Because the action on constants is fixed by the `A`-algebra
structure, continuous `A`-algebra homomorphisms out of `A⟨X⟩_T` or its separated completion are
determined by the images of the coordinate variables alone.

When `B` carries a linear topology — a neighbourhood basis of `0` consisting of open ideals, as on
any adic ring — every subset of `B` is bounded (`TauCeti.Huber.isBounded_of_isLinearTopology`), so
every element of `B` is power-bounded (`powerBoundedSubring B = ⊤`). Consequently arbitrary choices
of `b₁, …, bₖ ∈ B` define a unique continuous `A`-algebra homomorphism out of `A⟨X⟩_T` and out of
`TauCeti.Huber.restrictedMvPowerSeriesCompletion k A`, in contrast with general nonarchimedean
targets where the variable images must be power-bounded.

## Main definitions

* `TauCeti.Huber.weightedEvalAlgHom`: evaluation `A⟨X⟩_T →ₐ[A] B` at weight-bounded `b`.
* `TauCeti.Huber.weightedEvalAlgHomCompletion`: its extension to `Completion A⟨X⟩_T →ₐ[A] B`.

## Main results

* `TauCeti.Huber.weightedRestrictedSubring_algHom_ext_of_continuous` and
  `TauCeti.Huber.completion_weightedRestrictedSubring_algHom_ext_of_continuous`: continuous
  `A`-algebra homomorphisms out of `A⟨X⟩_T` or its completion into a Hausdorff target are
  determined by their values on the variables.
* `TauCeti.Huber.existsUnique_continuous_algHom_weightedRestrictedSubring` and
  `TauCeti.Huber.existsUnique_continuous_algHom_completion_weightedRestrictedSubring`: the
  universal properties as `A`-algebras under `IsWeightBounded`.
* `TauCeti.Huber.existsUnique_continuous_algHom_weightedRestrictedSubring_of_isLinearTopology` and
  `existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology`:
  the universal properties into a complete Hausdorff linearly topologised `A`-algebra, for
  arbitrary variable values `b : Fin k → B`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §5.6, Proposition 5.50.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.3.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {T : Fin k → Set A}

section Uniqueness

variable {B : Type*} [Semiring B] [Algebra A B] [TopologicalSpace B] [T2Space B]

/-- Two continuous `A`-algebra homomorphisms out of `A⟨X⟩_T` into a Hausdorff `A`-algebra that
agree on every variable are equal. -/
theorem weightedRestrictedSubring_algHom_ext_of_continuous (hT : IsWeightFamily T)
    {f g : weightedRestrictedSubring T hT →ₐ[A] B} (hf : Continuous f) (hg : Continuous g)
    (hX : ∀ i, f (weightedX T hT i) = g (weightedX T hT i)) : f = g :=
  AlgHom.toRingHom_injective <| weightedRestrictedSubring_ringHom_ext_of_continuous hT hf hg
    (fun a ↦ by simp only [RingHom.coe_coe, ← algebraMap_weightedRestrictedSubring,
      AlgHom.commutes])
    hX

/-- Two continuous `A`-algebra homomorphisms out of the completion of `A⟨X⟩_T` into a Hausdorff
`A`-algebra that agree on every variable are equal. -/
theorem completion_weightedRestrictedSubring_algHom_ext_of_continuous (hT : IsWeightFamily T)
    {f g : Completion (weightedRestrictedSubring T hT) →ₐ[A] B} (hf : Continuous f)
    (hg : Continuous g)
    (hX : ∀ i, f ((weightedX T hT i : weightedRestrictedSubring T hT) :
      Completion (weightedRestrictedSubring T hT)) =
        g ((weightedX T hT i : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT))) : f = g :=
  AlgHom.toRingHom_injective <| completion_weightedRestrictedSubring_ringHom_ext_of_continuous hT
    hf hg
    (fun a ↦ by
      simp only [RingHom.coe_coe, ← algebraMap_completion_weightedRestrictedSubring_apply,
        AlgHom.commutes])
    hX

end Uniqueness

section UniversalProperty

variable {B : Type*} [CommRing B] [Algebra A B] [UniformSpace B] [IsUniformAddGroup B]
  [NonarchimedeanRing B] [CompleteSpace B] [T2Space B] {b : Fin k → B}

/-- Evaluation on `A⟨X⟩_T` at weight-bounded `b : Fin k → B`, bundled as an `A`-algebra
homomorphism when `algebraMap A B` is continuous at `0`. -/
noncomputable def weightedEvalAlgHom (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b) :
    weightedRestrictedSubring T hT →ₐ[A] B :=
  { weightedEvalHom hT hA hb with
    commutes' a := by
      rw [algebraMap_weightedRestrictedSubring]
      exact weightedEvalHom_weightedC hT hA hb a }

/-- `weightedEvalAlgHom` has the same underlying function as `weightedEvalHom`. -/
@[simp]
theorem coe_weightedEvalAlgHom (hT : IsWeightFamily T) (hA : ContinuousAt (algebraMap A B) 0)
    (hb : IsWeightBounded (algebraMap A B) T b) :
    ⇑(weightedEvalAlgHom hT hA hb) = ⇑(weightedEvalHom hT hA hb) := (rfl)

/-- The underlying ring homomorphism of `weightedEvalAlgHom` is `weightedEvalHom`. -/
theorem toRingHom_weightedEvalAlgHom (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b) :
    (weightedEvalAlgHom hT hA hb).toRingHom = weightedEvalHom hT hA hb := (rfl)

/-- `weightedEvalAlgHom` sends the `i`-th variable to `b i`. -/
theorem weightedEvalAlgHom_weightedX (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b)
    (i : Fin k) : weightedEvalAlgHom hT hA hb (weightedX T hT i) = b i :=
  weightedEvalHom_weightedX hT hA hb i

/-- `weightedEvalAlgHom` is continuous. -/
theorem continuous_weightedEvalAlgHom (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b) :
    Continuous (weightedEvalAlgHom hT hA hb) :=
  continuous_weightedEvalHom hT hA hb

/-- **The `A`-algebra universal property of `A⟨X⟩_T`.** For a complete Hausdorff nonarchimedean
`A`-algebra `B` with `algebraMap A B` continuous at `0` and weight-bounded `b : Fin k → B`, there
is a unique continuous `A`-algebra homomorphism `A⟨X⟩_T →ₐ[A] B` sending each `Xᵢ` to `b i`. -/
theorem existsUnique_continuous_algHom_weightedRestrictedSubring (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b) :
    ∃! ψ : weightedRestrictedSubring T hT →ₐ[A] B,
      Continuous ψ ∧ ∀ i, ψ (weightedX T hT i) = b i :=
  ⟨weightedEvalAlgHom hT hA hb,
    ⟨continuous_weightedEvalAlgHom hT hA hb, weightedEvalAlgHom_weightedX hT hA hb⟩,
    fun _ ⟨hψ, hX⟩ ↦ weightedRestrictedSubring_algHom_ext_of_continuous hT hψ
      (continuous_weightedEvalAlgHom hT hA hb)
      fun i ↦ (hX i).trans (weightedEvalAlgHom_weightedX hT hA hb i).symm⟩

/-- Evaluation on the separated completion of `A⟨X⟩_T` at weight-bounded `b : Fin k → B`, bundled
as an `A`-algebra homomorphism. -/
noncomputable def weightedEvalAlgHomCompletion (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b) :
    Completion (weightedRestrictedSubring T hT) →ₐ[A] B :=
  { weightedEvalHomCompletion hT hA hb with
    commutes' a := by
      rw [algebraMap_completion_weightedRestrictedSubring_apply]
      exact (weightedEvalHomCompletion_coe hT hA hb (weightedC T hT a)).trans
        (weightedEvalHom_weightedC hT hA hb a) }

/-- `weightedEvalAlgHomCompletion` has the same underlying map as `weightedEvalHomCompletion`. -/
@[simp]
theorem coe_weightedEvalAlgHomCompletion (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b) :
    ⇑(weightedEvalAlgHomCompletion hT hA hb) = ⇑(weightedEvalHomCompletion hT hA hb) := (rfl)

/-- The underlying ring homomorphism of `weightedEvalAlgHomCompletion` is
`weightedEvalHomCompletion`. -/
theorem toRingHom_weightedEvalAlgHomCompletion (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b) :
    (weightedEvalAlgHomCompletion hT hA hb).toRingHom = weightedEvalHomCompletion hT hA hb := (rfl)

/-- `weightedEvalAlgHomCompletion` sends the `i`-th variable to `b i`. -/
theorem weightedEvalAlgHomCompletion_weightedX (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b)
    (i : Fin k) :
    weightedEvalAlgHomCompletion hT hA hb
      ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i := by
  rw [coe_weightedEvalAlgHomCompletion, weightedEvalHomCompletion_coe]
  exact weightedEvalHom_weightedX hT hA hb i

/-- `weightedEvalAlgHomCompletion` is continuous. -/
theorem continuous_weightedEvalAlgHomCompletion (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (hb : IsWeightBounded (algebraMap A B) T b) :
    Continuous (weightedEvalAlgHomCompletion hT hA hb) :=
  continuous_weightedEvalHomCompletion hT hA hb

/-- **The `A`-algebra universal property of the completion of `A⟨X⟩_T`.** For a complete Hausdorff
nonarchimedean `A`-algebra `B` with `algebraMap A B` continuous at `0` and weight-bounded
`b : Fin k → B`, there is a unique continuous `A`-algebra homomorphism from the completion of
`A⟨X⟩_T` to `B` sending each `Xᵢ` to `b i`. -/
theorem existsUnique_continuous_algHom_completion_weightedRestrictedSubring
    (hT : IsWeightFamily T) (hA : ContinuousAt (algebraMap A B) 0)
    (hb : IsWeightBounded (algebraMap A B) T b) :
    ∃! ψ : Completion (weightedRestrictedSubring T hT) →ₐ[A] B,
      Continuous ψ ∧ ∀ i, ψ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i :=
  ⟨weightedEvalAlgHomCompletion hT hA hb,
    ⟨continuous_weightedEvalAlgHomCompletion hT hA hb,
      weightedEvalAlgHomCompletion_weightedX hT hA hb⟩,
    fun _ ⟨hψ, hX⟩ ↦ completion_weightedRestrictedSubring_algHom_ext_of_continuous hT hψ
      (continuous_weightedEvalAlgHomCompletion hT hA hb)
      fun i ↦ (hX i).trans (weightedEvalAlgHomCompletion_weightedX hT hA hb i).symm⟩

end UniversalProperty

section LinearTopology

variable {B : Type*} [CommRing B] [Algebra A B] [UniformSpace B] [IsUniformAddGroup B]
  [IsLinearTopology B B] [CompleteSpace B] [T2Space B]

/-- **The `A`-algebra universal property of `A⟨X⟩_T` for linearly topologised targets.** Because
open ideals form a neighbourhood basis of `0` in `B`, every element of `B` is power-bounded, so
arbitrary values `b : Fin k → B` define a unique continuous `A`-algebra homomorphism
`A⟨X⟩_T →ₐ[A] B`. -/
theorem existsUnique_continuous_algHom_weightedRestrictedSubring_of_isLinearTopology
    (hT : IsWeightFamily T) (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    ∃! ψ : weightedRestrictedSubring T hT →ₐ[A] B,
      Continuous ψ ∧ ∀ i, ψ (weightedX T hT i) = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact existsUnique_continuous_algHom_weightedRestrictedSubring hT hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) T b)

/-- **The `A`-algebra universal property of `A⟨X₁, …, Xₖ⟩` for linearly topologised targets**
(EGA I, Ch. 0, §7.5.3). For a complete separated linearly topologised commutative `A`-algebra `B`
whose structure map is continuous at `0` (for instance when `[ContinuousSMul A B]`), arbitrary
choices `b : Fin k → B` of the variables define a unique continuous `A`-algebra homomorphism out of
`restrictedMvPowerSeriesCompletion k A`. -/
theorem existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
    (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    ∃! ψ : restrictedMvPowerSeriesCompletion k A →ₐ[A] B,
      Continuous ψ ∧ ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  exact existsUnique_continuous_algHom_completion_weightedRestrictedSubring
    isWeightFamily_one_weight hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) _ b)

end LinearTopology

end TauCeti.Huber
