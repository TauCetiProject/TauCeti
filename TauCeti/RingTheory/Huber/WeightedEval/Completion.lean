/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import TauCeti.Topology.Algebra.Nonarchimedean.LinearTopology
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
* `restrictedCompletionEvalLinear`: evaluation `A⟨X₁, …, Xₖ⟩ →+* B` into a complete Hausdorff
  linearly topologised ring along a continuous coefficient homomorphism, at arbitrary variable
  values.
* `restrictedCompletionLiftLinear`: the same evaluation as an `A`-algebra homomorphism when `B` is
  a complete Hausdorff linearly topologised `A`-algebra with a continuous structure map.

## Main results

* `existsUnique_continuous_ringHom_completion_weightedRestrictedSubring`: the `∃!` that the phrase
  "universal property" names, under `IsWeightBounded`.
* existsUnique_continuous_ringHom_completion_weightedRestrictedSubring_of_isWeightedVarPowerBounded
  — the same under `IsWeightedVarPowerBounded`, the coordinatewise condition Proposition 5.50
  states. This is the one to cite as 5.50.
* `weightedEvalHomCompletion_weightedMapCompletion` and `map_weightedEvalHomCompletion`:
  naturality under coefficient maps and target continuous homomorphisms.
* `existsUnique_continuous_ringHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology` and
  `existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology`: the
  universal property of `A⟨X₁, …, Xₖ⟩` into a complete Hausdorff linearly topologised ring or
  `A`-algebra, with no power-boundedness condition on the values of the variables.
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

/-- **Naturality in the source coefficients on completions**: evaluating after the completed
coefficient map `weightedMapCompletion` induced by `θ : C →+* A` agrees with completed evaluation
along `φ.comp θ`. -/
theorem weightedEvalHomCompletion_weightedMapCompletion {C : Type*} [CommRing C]
    [TopologicalSpace C] [NonarchimedeanRing C] {θ : C →+* A} {R : Fin k → Set C}
    (hθ : Continuous θ) (hR : IsWeightFamily R) (hT : IsWeightFamily T)
    (hRT : ∀ i, θ '' R i ⊆ T i) (hφ : ContinuousAt φ 0) (hb : IsWeightBounded φ T b)
    (hφθ : ContinuousAt (φ.comp θ) 0) (hb' : IsWeightBounded (φ.comp θ) R b)
    (x : Completion (weightedRestrictedSubring R hR)) :
    weightedEvalHomCompletion hT hφ hb (weightedMapCompletion hθ hR hT hRT x) =
      weightedEvalHomCompletion hR hφθ hb' x := by
  refine Completion.induction_on x (isClosed_eq
    ((continuous_weightedEvalHomCompletion hT hφ hb).comp
      (continuous_weightedMapCompletion hθ hR hT hRT))
    (continuous_weightedEvalHomCompletion hR hφθ hb')) fun f ↦ ?_
  rw [weightedMapCompletion_coe, weightedEvalHomCompletion_coe, weightedEvalHomCompletion_coe,
    weightedEvalHom_weightedMap hθ hR hT hRT hφ hb hφθ hb' f]

/-- **Naturality in the target on completions**: applying a continuous ring homomorphism
`ψ : B →+* D` into a complete Hausdorff nonarchimedean ring to a completed evaluation agrees with
completed evaluation along `ψ.comp φ` at `ψ ∘ b`. -/
theorem map_weightedEvalHomCompletion {D : Type*} [CommRing D] [UniformSpace D]
    [IsUniformAddGroup D] [NonarchimedeanRing D] [CompleteSpace D] [T3Space D]
    {ψ : B →+* D} (hψ : Continuous ψ) (hT : IsWeightFamily T) (hφ : ContinuousAt φ 0)
    (hb : IsWeightBounded φ T b) (hψφ : ContinuousAt (ψ.comp φ) 0)
    (hb' : IsWeightBounded (ψ.comp φ) T (ψ ∘ b))
    (x : Completion (weightedRestrictedSubring T hT)) :
    ψ (weightedEvalHomCompletion hT hφ hb x) = weightedEvalHomCompletion hT hψφ hb' x := by
  refine Completion.induction_on x (isClosed_eq
    (hψ.comp (continuous_weightedEvalHomCompletion hT hφ hb))
    (continuous_weightedEvalHomCompletion hT hψφ hb')) fun f ↦ ?_
  rw [weightedEvalHomCompletion_coe, weightedEvalHomCompletion_coe,
    map_weightedEvalHom hψ hT hφ hb hψφ hb' f]

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

/-! ### Linearly topologised targets

In a general nonarchimedean target `B`, evaluating `A⟨X₁, …, Xₖ⟩` at `b₁, …, bₖ` requires each
`bᵢ` to be power-bounded (`IsPowerBounded`); for instance, over a nontrivially normed field `K`
there is no proper nonzero ideal, so powers of an element of norm greater than one are unbounded.
When `B` is linearly topologised (`IsLinearTopology B B`), zero admits a neighbourhood basis of
open ideals, and ideals absorb arbitrary multiplication, so *every* subset — and in particular
every set of powers `{bᵢ ^ n | n : ℕ}` — is bounded (`isBounded_of_isLinearTopology`). Hence
arbitrary `b₁, …, bₖ ∈ B` define a unique continuous homomorphism out of `A⟨X₁, …, Xₖ⟩`. -/

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsLinearTopology B B] [CompleteSpace B] [T2Space B]

/-- **Evaluation of `A⟨X₁, …, Xₖ⟩` in a complete Hausdorff linearly topologised ring**, for a
continuous coefficient homomorphism `φ : A →+* B` and *arbitrary* values `b₁, …, bₖ ∈ B`. Ideal
neighbourhoods of zero make every element of `B` power-bounded, so no bound on `b` is needed. -/
noncomputable def restrictedCompletionEvalLinear {φ : A →+* B} (hφ : Continuous φ)
    (b : Fin k → B) : restrictedMvPowerSeriesCompletion k A →+* B :=
  letI := IsLinearTopology.isTopologicalRing (R := B)
  letI := IsLinearTopology.nonarchimedeanRing B
  weightedEvalHomCompletion isWeightFamily_one_weight hφ.continuousAt
    (isWeightBounded_of_isLinearTopology φ _ b)

/-- `restrictedCompletionEvalLinear` is `weightedEvalHomCompletion` with the linear-topology
boundedness witness. -/
theorem restrictedCompletionEvalLinear_eq_weightedEvalHomCompletion [NonarchimedeanRing B]
    {φ : A →+* B} (hφ : Continuous φ) (b : Fin k → B) :
    restrictedCompletionEvalLinear hφ b =
      weightedEvalHomCompletion isWeightFamily_one_weight hφ.continuousAt
        (isWeightBounded_of_isLinearTopology φ _ b) := (rfl)

/-- On a represented restricted series, `restrictedCompletionEvalLinear` computes `weightedEval`. -/
@[simp]
theorem restrictedCompletionEvalLinear_coe {φ : A →+* B} (hφ : Continuous φ) (b : Fin k → B)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    restrictedCompletionEvalLinear hφ b (f : restrictedMvPowerSeriesCompletion k A) =
      weightedEval φ b f := by
  let _ := IsLinearTopology.isTopologicalRing (R := B)
  let _ := IsLinearTopology.nonarchimedeanRing B
  rw [restrictedCompletionEvalLinear_eq_weightedEvalHomCompletion, weightedEvalHomCompletion_coe,
    coe_weightedEvalHom]

/-- `restrictedCompletionEvalLinear` is continuous. -/
theorem continuous_restrictedCompletionEvalLinear {φ : A →+* B} (hφ : Continuous φ)
    (b : Fin k → B) : Continuous (restrictedCompletionEvalLinear hφ b) := by
  let _ := IsLinearTopology.isTopologicalRing (R := B)
  let _ := IsLinearTopology.nonarchimedeanRing B
  exact continuous_weightedEvalHomCompletion isWeightFamily_one_weight hφ.continuousAt _

/-- `restrictedCompletionEvalLinear` extends `φ` on constants. -/
theorem restrictedCompletionEvalLinear_algebraMap {φ : A →+* B} (hφ : Continuous φ)
    (b : Fin k → B) (a : A) :
    restrictedCompletionEvalLinear hφ b
        (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) = φ a := by
  simp

/-- `restrictedCompletionEvalLinear` sends each variable `Xᵢ` to `bᵢ`. -/
theorem restrictedCompletionEvalLinear_weightedX {φ : A →+* B} (hφ : Continuous φ)
    (b : Fin k → B) (i : Fin k) :
    restrictedCompletionEvalLinear hφ b
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) = b i := by
  simp

/-- `restrictedCompletionEvalLinear` is the unique continuous ring homomorphism extending `φ` and
sending each `Xᵢ` to `bᵢ`. -/
theorem restrictedCompletionEvalLinear_unique {φ : A →+* B} (hφ : Continuous φ) (b : Fin k → B)
    {ψ : restrictedMvPowerSeriesCompletion k A →+* B} (hψ : Continuous ψ)
    (hC : ∀ a, ψ (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) = φ a)
    (hX : ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
        restrictedMvPowerSeriesCompletion k A) = b i) :
    ψ = restrictedCompletionEvalLinear hφ b :=
  completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight hψ
    (continuous_restrictedCompletionEvalLinear hφ b)
    (fun a ↦ by simpa using hC a)
    (fun i ↦ by rw [hX, restrictedCompletionEvalLinear_weightedX])

/-- **Base-change naturality for linear-topology evaluation**: evaluating after the completed
coefficient map induced by a continuous `θ : C →+* A` agrees with evaluating along `φ.comp θ`. -/
theorem restrictedCompletionEvalLinear_weightedMapCompletion {C : Type*} [CommRing C]
    [TopologicalSpace C] [NonarchimedeanRing C] {θ : C →+* A} (hθ : Continuous θ)
    {φ : A →+* B} (hφ : Continuous φ) (b : Fin k → B)
    (x : restrictedMvPowerSeriesCompletion k C) :
    restrictedCompletionEvalLinear hφ b
        (weightedMapCompletion hθ isWeightFamily_one_weight isWeightFamily_one_weight
          (by simp) x) =
      restrictedCompletionEvalLinear (φ := φ.comp θ) (hφ.comp hθ) b x := by
  let _ := IsLinearTopology.isTopologicalRing (R := B)
  let _ := IsLinearTopology.nonarchimedeanRing B
  exact weightedEvalHomCompletion_weightedMapCompletion hθ isWeightFamily_one_weight
    isWeightFamily_one_weight (by simp) hφ.continuousAt _ (hφ.comp hθ).continuousAt _ x

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
          restrictedMvPowerSeriesCompletion k A) = b i :=
  ⟨restrictedCompletionEvalLinear hφ b,
    ⟨continuous_restrictedCompletionEvalLinear hφ b,
      restrictedCompletionEvalLinear_algebraMap hφ b,
      restrictedCompletionEvalLinear_weightedX hφ b⟩,
    fun _ ⟨hψ, hC, hX⟩ ↦ restrictedCompletionEvalLinear_unique hφ b hψ hC hX⟩

/-- **The `A`-algebra lift out of `A⟨X₁, …, Xₖ⟩` into a linearly topologised `A`-algebra** with a
continuous structure map, sending each `Xᵢ` to an arbitrary `bᵢ ∈ B`. -/
noncomputable def restrictedCompletionLiftLinear [Algebra A B]
    (hA : Continuous (algebraMap A B)) (b : Fin k → B) :
    restrictedMvPowerSeriesCompletion k A →ₐ[A] B :=
  { restrictedCompletionEvalLinear hA b with
    commutes' := restrictedCompletionEvalLinear_algebraMap hA b }

/-- `restrictedCompletionLiftLinear` has the same underlying map as
`restrictedCompletionEvalLinear`, so `simp` normalises the `A`-algebra lift onto the ring
evaluation. -/
@[simp]
theorem coe_restrictedCompletionLiftLinear [Algebra A B]
    (hA : Continuous (algebraMap A B)) (b : Fin k → B) :
    ⇑(restrictedCompletionLiftLinear hA b) = ⇑(restrictedCompletionEvalLinear hA b) := (rfl)

/-- `restrictedCompletionLiftLinear` is continuous. -/
theorem continuous_restrictedCompletionLiftLinear [Algebra A B]
    (hA : Continuous (algebraMap A B)) (b : Fin k → B) :
    Continuous (restrictedCompletionLiftLinear hA b) :=
  continuous_restrictedCompletionEvalLinear hA b

/-- `restrictedCompletionLiftLinear` sends each variable `Xᵢ` to `bᵢ`. -/
theorem restrictedCompletionLiftLinear_weightedX [Algebra A B]
    (hA : Continuous (algebraMap A B)) (b : Fin k → B) (i : Fin k) :
    restrictedCompletionLiftLinear hA b
        ((weightedX _ isWeightFamily_one_weight i :
          weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
            restrictedMvPowerSeriesCompletion k A) = b i :=
  restrictedCompletionEvalLinear_weightedX hA b i

/-- `restrictedCompletionLiftLinear` is the unique continuous `A`-algebra homomorphism sending each
`Xᵢ` to `bᵢ`. -/
theorem restrictedCompletionLiftLinear_unique [Algebra A B]
    (hA : Continuous (algebraMap A B)) (b : Fin k → B)
    {ψ : restrictedMvPowerSeriesCompletion k A →ₐ[A] B} (hψ : Continuous ψ)
    (hX : ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
        restrictedMvPowerSeriesCompletion k A) = b i) :
    ψ = restrictedCompletionLiftLinear hA b :=
  AlgHom.toRingHom_injective <|
    restrictedCompletionEvalLinear_unique hA b hψ ψ.commutes hX

/-- **The `A`-algebra universal property of `A⟨X₁, …, Xₖ⟩` for linearly topologised targets**
(EGA I, Ch. 0, §7.5.3). For a complete Hausdorff linearly topologised commutative `A`-algebra `B`
with a continuous structure map, arbitrary elements `b₁, …, bₖ ∈ B` define a unique continuous
`A`-algebra homomorphism `A⟨X₁, …, Xₖ⟩ →ₐ[A] B` sending each `Xᵢ` to `bᵢ`. -/
theorem existsUnique_continuous_algHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology
    [Algebra A B] (hA : Continuous (algebraMap A B)) (b : Fin k → B) :
    ∃! ψ : restrictedMvPowerSeriesCompletion k A →ₐ[A] B, Continuous ψ ∧
      ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion k A) = b i :=
  ⟨restrictedCompletionLiftLinear hA b,
    ⟨continuous_restrictedCompletionLiftLinear hA b,
      restrictedCompletionLiftLinear_weightedX hA b⟩,
    fun _ ⟨hψ, hX⟩ ↦ restrictedCompletionLiftLinear_unique hA b hψ hX⟩

end LinearTopology

end TauCeti.Huber

end
