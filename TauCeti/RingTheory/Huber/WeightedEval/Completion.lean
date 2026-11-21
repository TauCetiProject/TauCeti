/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import TauCeti.Topology.Algebra.UniformRing

/-!
# The universal property of the completed algebra of `A⟨X⟩_T`

Wedhorn's Proposition 5.50 —
`existsUnique_continuous_ringHom_weightedRestrictedSubring_of_isWeightedVarPowerBounded` — is the
universal property of the restricted-series ring `A⟨X⟩_T` itself. This file carries it across the
separated completion: a ring homomorphism `φ : A →+* B` into a complete Hausdorff nonarchimedean
ring, continuous at zero, together with weight-bounded values `bᵢ`, extends to the completion of
`A⟨X⟩_T` in exactly one continuous way.

Neither half is new mathematics; both compose 5.50 with a standard property of the completion.
Existence is `UniformSpace.Completion.extensionHom` applied to the evaluation homomorphism, which
is available exactly because the target is already assumed complete and Hausdorff — the same
hypotheses 5.50 carries, so the completed statement asks for nothing extra. Uniqueness is
`completion_weightedRestrictedSubring_ringHom_ext_of_continuous`, itself
`UniformSpace.Completion.ringHom_ext_of_continuous` — two continuous ring homomorphisms out of a
completion that agree after composing with the coercion are equal — applied to 5.50's own
uniqueness clause for the restrictions along
`UniformSpace.Completion.coeRingHom`.

At the trivial weight family `Tᵢ = {1}` the domain is the completed restricted power-series
algebra `TauCeti.Huber.restrictedMvPowerSeriesCompletion k A`, written `A⟨X₁,…,Xₖ⟩` for an
arbitrary Tate ring, so this is that algebra's universal property. It is
stated for a general weight family because nothing in the argument uses triviality.

Into a complete Hausdorff linearly topologised ring, such as an adic ring, the completed
restricted-series algebra is free on its variables: a continuous ring homomorphism from `A`
extends uniquely, for arbitrary values of the variables. Every element of a linearly
topologised ring is power-bounded, so the universal property applies with no condition
on the values.

## Main definitions

* `weightedEvalHomCompletion`: the evaluation homomorphism of 5.50, extended to the completion.
* `weightedEvalCompletionAlgHomOfIsLinearTopology`: evaluation of the completion of `A⟨X⟩_T` in a
  complete Hausdorff linearly topologised `A`-algebra at an arbitrary tuple `b : Fin k → B`.

## Main results

* `existsUnique_continuous_ringHom_completion_weightedRestrictedSubring`: the `∃!` that the phrase
  "universal property" names, under `IsWeightBounded`.
* existsUnique_continuous_ringHom_completion_weightedRestrictedSubring_of_isWeightedVarPowerBounded
  — the same under `IsWeightedVarPowerBounded`, the coordinatewise condition Proposition 5.50
  states. This is the one to cite as 5.50.
* `existsUnique_continuous_ringHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology` and
  `existsUnique_continuous_algHom_completion_weightedRestrictedSubring_of_isLinearTopology`: the
  universal property into a complete Hausdorff linearly topologised ring or `A`-algebra, with no
  condition on the values of the variables.
* `completion_weightedRestrictedSubring_ringHom_ext_of_continuous`: the uniqueness half on its own,
  which asks of the target only a semiring structure and a Hausdorff topology.
* `weightedEvalHomCompletion_coe`: the value of the extension on the image of `A⟨X⟩_T`. The body of
  the definition is not exported, so this is how a consumer computes with it.
* `continuous_weightedEvalHomCompletion`: the extension is continuous.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §7.5.3, for
  the universal property of restricted power series over an adic ring.
-/

public section

namespace TauCeti.Huber

open UniformSpace

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  {T : Fin k → Set A}

/-! ### Uniqueness

Uniqueness asks far less of the target than existence does, so it is proved first, under its own
hypotheses on `B`. -/

section Uniqueness

variable {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B]

/-- **A continuous homomorphism out of the completion of `A⟨X⟩_T` is determined by its values on
the generators.** Two of them agreeing on every constant series *and* every variable are equal.

This is `weightedRestrictedSubring_ringHom_ext_of_continuous` carried across the completion: that
lemma identifies the two restrictions along `UniformSpace.Completion.coeRingHom`, and
`UniformSpace.Completion.ringHom_ext_of_continuous` propagates the agreement to the completion
by density of the image of the coercion. The completeness and `T3Space` hypotheses that the
universal property below carries are what the evaluation homomorphism needs in order to exist;
uniqueness needs neither. -/
theorem completion_weightedRestrictedSubring_ringHom_ext_of_continuous (hT : IsWeightFamily T)
    {f g : Completion (weightedRestrictedSubring T hT) →+* B} (hf : Continuous f)
    (hg : Continuous g) (hC : ∀ a, f (weightedC T hT a) = g (weightedC T hT a))
    (hX : ∀ i, f (weightedX T hT i) = g (weightedX T hT i)) : f = g := by
  -- `⇑UniformSpace.Completion.coeRingHom` is the coercion `((↑) : _ → Completion _)`, by the
  -- definition of `coeRingHom`, so composing with it is restriction along the coercion. That
  -- unfolding is the only definitional bridge the proof crosses, and `hcomp` states it once.
  have hcomp : ∀ (h : Completion (weightedRestrictedSubring T hT) →+* B)
      (x : weightedRestrictedSubring T hT), (h.comp Completion.coeRingHom) x = h x :=
    fun _ _ ↦ rfl
  exact Completion.ringHom_ext_of_continuous hf hg
    (weightedRestrictedSubring_ringHom_ext_of_continuous hT
      (by simpa only [RingHom.coe_comp] using hf.comp Completion.continuous_coeRingHom)
      (by simpa only [RingHom.coe_comp] using hg.comp Completion.continuous_coeRingHom)
      (fun a ↦ (hcomp f _).trans ((hC a).trans (hcomp g _).symm))
      fun i ↦ (hcomp f _).trans ((hX i).trans (hcomp g _).symm))

end Uniqueness

/-! ### The extended evaluation homomorphism and the universal property -/

section UniversalProperty

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T3Space B] {φ : A →+* B} {b : Fin k → B}

/-- The evaluation homomorphism of Proposition 5.50, extended to the completion of `A⟨X⟩_T`.
The extension exists because the target is complete and Hausdorff. -/
noncomputable def weightedEvalHomCompletion (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) :
    Completion (weightedRestrictedSubring T hT) →+* B :=
  Completion.extensionHom (weightedEvalHom hT hφ hb) (continuous_weightedEvalHom hT hφ hb)

/-- The extension is the evaluation homomorphism on the image of `A⟨X⟩_T`. The body of
`weightedEvalHomCompletion` is not exported, so this is how a consumer computes with it. -/
@[simp]
theorem weightedEvalHomCompletion_coe (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (f : weightedRestrictedSubring T hT) :
    weightedEvalHomCompletion hT hφ hb (f : Completion (weightedRestrictedSubring T hT))
      = weightedEvalHom hT hφ hb f :=
  Completion.extensionHom_coe (weightedEvalHom hT hφ hb) (continuous_weightedEvalHom hT hφ hb) f

/-- The extended evaluation homomorphism is continuous: it is a `UniformSpace.Completion`
extension, and those are continuous by construction. -/
theorem continuous_weightedEvalHomCompletion (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) : Continuous (weightedEvalHomCompletion hT hφ hb) :=
  Completion.continuous_extension

/-- **The universal property of the completion of `A⟨X⟩_T`, under `IsWeightBounded`.** Given
`φ : A →+* B` continuous at zero and weight-bounded values `b`, there is exactly one continuous
ring homomorphism from the completion of `A⟨X⟩_T` to `B` restricting to `φ` on the constants and
sending each `Xᵢ` to `bᵢ`.

This mirrors `existsUnique_continuous_ringHom_weightedRestrictedSubring`, the uncompleted
statement under the same uniform hypothesis. Proposition 5.50's own hypothesis is the
coordinatewise one, so the theorem to cite as 5.50 is the `_of_isWeightedVarPowerBounded` form of
this one, below:
`existsUnique_continuous_ringHom_completion_weightedRestrictedSubring_of_isWeightedVarPowerBounded`.

As in the uncompleted statement, uniqueness is among *continuous* homomorphisms, and continuity is
used at both steps of the argument: 5.50 pins `ψ` down on the image of `A⟨X⟩_T` from its values on
the constants and the variables, by density of the polynomials, and the density of that image in
the completion carries the agreement the rest of the way. Whether a discontinuous homomorphism
with the same values can exist is not addressed here. -/
theorem existsUnique_continuous_ringHom_completion_weightedRestrictedSubring
    (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b) :
    ∃! ψ : Completion (weightedRestrictedSubring T hT) →+* B, Continuous ψ ∧
      (∀ a, ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) = φ a) ∧
      ∀ i, ψ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i := by
  -- The extension's values on the generators: its value on the image of `A⟨X⟩_T` composed with
  -- the uncompleted evaluation's own computations.
  have hC₀ : ∀ a, weightedEvalHomCompletion hT hφ hb
      ((weightedC T hT a : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = φ a := fun a ↦ by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]
  have hX₀ : ∀ i, weightedEvalHomCompletion hT hφ hb
      ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i := fun i ↦ by
    rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
  exact ⟨weightedEvalHomCompletion hT hφ hb,
    ⟨continuous_weightedEvalHomCompletion hT hφ hb, hC₀, hX₀⟩,
    fun _ ⟨hψ, hC, hX⟩ ↦ completion_weightedRestrictedSubring_ringHom_ext_of_continuous hT hψ
      (continuous_weightedEvalHomCompletion hT hφ hb)
      (fun a ↦ (hC a).trans (hC₀ a).symm) fun i ↦ (hX i).trans (hX₀ i).symm⟩

/-- **Wedhorn 5.50 for the completed algebra**, under the hypothesis Proposition 5.50 itself
carries: each weighted variable `φ(Tᵢ) · bᵢ` power-bounded as a set, one index at a time.

This is the theorem to cite as 5.50 for the completion. It is the statement above composed with
`isWeightBounded_of_isWeightedVarPowerBounded`, exactly as
`existsUnique_continuous_ringHom_weightedRestrictedSubring_of_isWeightedVarPowerBounded` relates
to its own uniform form. -/
theorem
  existsUnique_continuous_ringHom_completion_weightedRestrictedSubring_of_isWeightedVarPowerBounded
    (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0) (hb : IsWeightedVarPowerBounded φ T b) :
    ∃! ψ : Completion (weightedRestrictedSubring T hT) →+* B, Continuous ψ ∧
      (∀ a, ψ ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) = φ a) ∧
      ∀ i, ψ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i :=
  existsUnique_continuous_ringHom_completion_weightedRestrictedSubring hT hφ
    (isWeightBounded_of_isWeightedVarPowerBounded hb)

end UniversalProperty

section LinearTopology

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsLinearTopology B B] [CompleteSpace B] [T2Space B]

/-- **The universal property of `A⟨X₁, …, Xₖ⟩` for linearly topologised targets.** A continuous
ring homomorphism `φ : A → B` into a complete Hausdorff linearly topologised ring, such as an
adic ring, extends to exactly one continuous ring homomorphism `A⟨X₁, …, Xₖ⟩ → B` sending each
`Xᵢ` to a prescribed `bᵢ`, with no condition on the `bᵢ`. -/
theorem existsUnique_continuous_ringHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
    {φ : A →+* B} (hφ : Continuous φ) (b : Fin k → B) :
    ∃! ψ : restrictedMvPowerSeriesCompletion k A →+* B, Continuous ψ ∧
      (∀ a, ψ (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) = φ a) ∧
      ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) = b i := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  simpa only [algebraMap_completion_weightedRestrictedSubring_apply] using
    existsUnique_continuous_ringHom_completion_weightedRestrictedSubring isWeightFamily_one_weight
      hφ.continuousAt (isWeightBounded_of_isLinearTopology φ _ b)

variable [Algebra A B]

/-- Evaluation of the completed restricted-series algebra in a complete Hausdorff linearly
topologised `A`-algebra (with `algebraMap A B` continuous at `0`) at `b : Fin k → B`
(EGA I, Ch. 0, §7.5.3). -/
noncomputable def weightedEvalCompletionAlgHomOfIsLinearTopology (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    Completion (weightedRestrictedSubring T hT) →ₐ[A] B :=
  haveI := IsLinearTopology.isTopologicalRing (R := B)
  haveI := IsLinearTopology.nonarchimedeanRing B
  let φ :=
    weightedEvalHomCompletion hT hA (isWeightBounded_of_isLinearTopology (algebraMap A B) T b)
  { __ := φ, toFun := φ,
    commutes' := fun a ↦ by
      dsimp only [φ]
      rw [algebraMap_completion_weightedRestrictedSubring_apply, weightedEvalHomCompletion_coe,
        weightedEvalHom_weightedC] }

/-- Underlying ring homomorphism of `weightedEvalCompletionAlgHomOfIsLinearTopology`. -/
@[simp]
theorem coe_weightedEvalCompletionAlgHomOfIsLinearTopology (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    (weightedEvalCompletionAlgHomOfIsLinearTopology hT hA b :
      Completion (weightedRestrictedSubring T hT) →+* B) =
      letI := IsLinearTopology.isTopologicalRing (R := B)
      letI := IsLinearTopology.nonarchimedeanRing B
      weightedEvalHomCompletion hT hA
        (isWeightBounded_of_isLinearTopology (algebraMap A B) T b) :=
  RingHom.ext fun _ ↦ rfl

/-- On the uncompleted subring, `weightedEvalCompletionAlgHomOfIsLinearTopology` agrees with
`weightedEvalAlgHomOfIsLinearTopology`. -/
@[simp]
theorem weightedEvalCompletionAlgHomOfIsLinearTopology_coe (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B)
    (f : weightedRestrictedSubring T hT) :
    weightedEvalCompletionAlgHomOfIsLinearTopology hT hA b
        (f : Completion (weightedRestrictedSubring T hT)) =
      weightedEvalAlgHomOfIsLinearTopology hT hA b f := by
  have := IsLinearTopology.isTopologicalRing (R := B)
  have := IsLinearTopology.nonarchimedeanRing B
  rw [← RingHom.coe_coe (weightedEvalAlgHomOfIsLinearTopology hT hA b),
    coe_weightedEvalAlgHomOfIsLinearTopology]
  exact weightedEvalHomCompletion_coe hT hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) T b) f

/-- `weightedEvalCompletionAlgHomOfIsLinearTopology` sends each coordinate variable `Xᵢ` to `bᵢ`. -/
theorem weightedEvalCompletionAlgHomOfIsLinearTopology_weightedX (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) (i : Fin k) :
    weightedEvalCompletionAlgHomOfIsLinearTopology hT hA b
        ((weightedX T hT i : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) = b i := by
  rw [weightedEvalCompletionAlgHomOfIsLinearTopology_coe,
    weightedEvalAlgHomOfIsLinearTopology_weightedX]

/-- `weightedEvalCompletionAlgHomOfIsLinearTopology` is continuous. -/
theorem continuous_weightedEvalCompletionAlgHomOfIsLinearTopology (hT : IsWeightFamily T)
    (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    Continuous (weightedEvalCompletionAlgHomOfIsLinearTopology hT hA b) :=
  letI := IsLinearTopology.isTopologicalRing (R := B)
  letI := IsLinearTopology.nonarchimedeanRing B
  continuous_weightedEvalHomCompletion hT hA
    (isWeightBounded_of_isLinearTopology (algebraMap A B) T b)

/-- **Universal property of the completion of `A⟨X⟩_T` for complete Hausdorff linearly topologised
`A`-algebras** (EGA I, Ch. 0, §7.5.3). -/
theorem existsUnique_continuous_algHom_completion_weightedRestrictedSubring_of_isLinearTopology
    (hT : IsWeightFamily T) (hA : ContinuousAt (algebraMap A B) 0) (b : Fin k → B) :
    ∃! ψ : Completion (weightedRestrictedSubring T hT) →ₐ[A] B,
      Continuous ψ ∧ ∀ i, ψ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) = b i :=
  letI := IsLinearTopology.isTopologicalRing (R := B)
  letI := IsLinearTopology.nonarchimedeanRing B
  ⟨weightedEvalCompletionAlgHomOfIsLinearTopology hT hA b,
    ⟨continuous_weightedEvalCompletionAlgHomOfIsLinearTopology hT hA b,
      weightedEvalCompletionAlgHomOfIsLinearTopology_weightedX hT hA b⟩,
    fun ψ ⟨hψ, hX⟩ ↦ AlgHom.toRingHom_injective <|
      (existsUnique_continuous_ringHom_completion_weightedRestrictedSubring hT hA
        (isWeightBounded_of_isLinearTopology (algebraMap A B) T b)).unique
          ⟨hψ, fun a ↦ by
            rw [← algebraMap_completion_weightedRestrictedSubring_apply]; exact ψ.commutes a, hX⟩
          ⟨continuous_weightedEvalCompletionAlgHomOfIsLinearTopology hT hA b, fun a ↦ by simp,
            weightedEvalCompletionAlgHomOfIsLinearTopology_weightedX hT hA b⟩⟩

end LinearTopology

end TauCeti.Huber

end
