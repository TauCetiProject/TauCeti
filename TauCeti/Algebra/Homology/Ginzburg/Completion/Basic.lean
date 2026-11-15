/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.AdamsCompletion
public import TauCeti.Algebra.Homology.Ginzburg.Basic

/-!
# The completed two-dimensional Ginzburg differential graded algebra

Let `Q` be a finite quiver and `Π₂(Q)` its non-completed two-dimensional Ginzburg differential
graded algebra, the path algebra of the Ginzburg quiver with the differential
`TauCeti.ginzburgTwoDifferential` (`TauCeti.isDGAlgebra_ginzburgTwoDifferential`).  Besides its
cohomological grading it carries the Adams grading `TauCeti.ginzburgTwoAdamsDegree`, in which the
doubled arrows have degree `1` and the adjoined loops degree `2`, and the differential has bidegree
`(1, 0)`.

The **completed two-dimensional Ginzburg algebra** `Π̂₂(Q)` is the length-adic completion of
`Π₂(Q)` along this Adams grading, taken in the category of graded modules: in each cohomological
degree, the finite sums of paths are replaced by formal series of paths of unbounded Adams degree.
It is the Adams completion `TauCeti.adamsCompletion` of `Π₂(Q)`, a subalgebra of the formal power
series over the Ginzburg path algebra whose coefficient of index `n` is Adams-homogeneous of degree
`n`, with the coefficientwise differential.  The two gradings of the Ginzburg path algebra are
compatible because every path is homogeneous for both at once.

The comparison morphism `TauCeti.ginzburgTwoToCompleted` from `Π₂(Q)` to `Π̂₂(Q)` is an injective
morphism of differential graded algebras whose image consists of the series with finitely many
nonzero coefficients.  The ordinary and the completed algebra are distinct objects and are not
interchanged: which of the two a derived Koszul duality statement produces depends on whether the
Adams grading is retained or forgotten.

## Main definitions

* `TauCeti.completedGinzburgTwo`: **the completed two-dimensional Ginzburg algebra** `Π̂₂(Q)`.
* `TauCeti.completedGinzburgTwoGrading` and `TauCeti.completedGinzburgTwoDifferential`: its
  cohomological grading and its differential.
* `TauCeti.ginzburgTwoToCompleted`: the comparison morphism of differential graded algebras
  `Π₂(Q) → Π̂₂(Q)`.

## Main results

* `TauCeti.isHomogeneous_gradeBy_ginzburgTwoAdamsDegree` and
  `TauCeti.isHomogeneous_gradeBy_ginzburgTwoDegree`: the cohomological and Adams gradings of the
  Ginzburg path algebra are compatible.
* `TauCeti.isDGAlgebra_completedGinzburgTwoDifferential`: **`Π̂₂(Q)` is a differential graded
  algebra.**
* `TauCeti.mem_completedGinzburgTwo_iff`: its elements are the series of Adams-homogeneous
  coefficients with uniformly bounded cohomological degree.
* `TauCeti.ginzburgTwoToCompleted_injective` and `TauCeti.mem_range_ginzburgTwoToCompleted_iff`:
  **`Π₂(Q)` is the finite-support part of `Π̂₂(Q)`.**
* `TauCeti.completedGinzburgTwoDifferential_ginzburgTwoToCompleted_loop`: in the completion the
  differential of the adjoined loop `t_i` is still the local preprojective relator `ρ_i`.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6, for the completed Ginzburg algebra.
* T. Etgü and Y. Lekili, *Koszul duality patterns in Floer theory*, Section 4, for the completed
  and the non-completed two-dimensional Ginzburg algebra.
-/

public section

open DirectSum PowerSeries

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q]

section Finite

variable [Finite Q]

/-! ### Compatibility of the two gradings -/

/-- The Adams components of a cohomologically homogeneous element of the Ginzburg path algebra are
cohomologically homogeneous. -/
theorem isHomogeneous_gradeBy_ginzburgTwoAdamsDegree (p : ℤ) :
    SetLike.IsHomogeneous (gradeBy k (ginzburgTwoAdamsDegree (Q := Q)))
      (gradeBy k (ginzburgTwoDegree (Q := Q)) p) :=
  isHomogeneous_gradeBy_gradeBy k ginzburgTwoAdamsDegree ginzburgTwoDegree p

/-- The cohomological components of an Adams-homogeneous element of the Ginzburg path algebra are
Adams-homogeneous. -/
theorem isHomogeneous_gradeBy_ginzburgTwoDegree (n : ℕ) :
    SetLike.IsHomogeneous (gradeBy k (ginzburgTwoDegree (Q := Q)))
      (gradeBy k (ginzburgTwoAdamsDegree (Q := Q)) n) :=
  isHomogeneous_gradeBy_gradeBy k ginzburgTwoDegree ginzburgTwoAdamsDegree n

/-! ### The completed algebra -/

variable (Q)

/-- **The completed two-dimensional Ginzburg algebra** `Π̂₂(Q)`: the length-adic completion of
`Π₂(Q)` along its Adams grading, in each cohomological degree.  Its elements are the formal power
series over the Ginzburg path algebra whose coefficient of index `n` is a combination of paths of
Adams degree `n`, with uniformly bounded cohomological degree. -/
noncomputable abbrev completedGinzburgTwo :
    Subalgebra k (PowerSeries (pathAlgebra k (GinzburgQuiver Q))) :=
  adamsCompletion (gradeBy k (ginzburgTwoAdamsDegree (Q := Q)))
    (gradeBy k (ginzburgTwoDegree (Q := Q)))

/-- The cohomological grading of the completed two-dimensional Ginzburg algebra. -/
noncomputable abbrev completedGinzburgTwoGrading : ℤ → Submodule k (completedGinzburgTwo k Q) :=
  adamsCompletionGrading (gradeBy k (ginzburgTwoAdamsDegree (Q := Q)))
    (gradeBy k (ginzburgTwoDegree (Q := Q)))

/-- **The elements of `Π̂₂(Q)`** are the power series whose coefficient of index `n` is a
combination of paths of Adams degree `n`, and whose cohomological components vanish outside a
finite set of degrees. -/
theorem mem_completedGinzburgTwo_iff {f : PowerSeries (pathAlgebra k (GinzburgQuiver Q))} :
    f ∈ completedGinzburgTwo k Q ↔
      (∀ n, coeff n f ∈ gradeBy k (ginzburgTwoAdamsDegree (Q := Q)) n) ∧
        ∃ s : Finset ℤ, ∀ n, ∀ p ∉ s,
          (decompose (gradeBy k (ginzburgTwoDegree (Q := Q))) (coeff n f) p :
            pathAlgebra k (GinzburgQuiver Q)) = 0 :=
  mem_adamsCompletion_iff _ _ (isHomogeneous_gradeBy_ginzburgTwoDegree k)

end Finite

/-! ### The differential -/

variable [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)] (Q)

/-- The differential of the completed two-dimensional Ginzburg algebra: the Ginzburg differential
applied coefficientwise. -/
noncomputable abbrev completedGinzburgTwoDifferential :
    completedGinzburgTwo k Q →ₗ[k] completedGinzburgTwo k Q :=
  adamsCompletionDifferential (gradeBy k (ginzburgTwoAdamsDegree (Q := Q)))
    (gradeBy k (ginzburgTwoDegree (Q := Q))) (isDGAlgebra_ginzburgTwoDifferential k)
    fun _ _ hx => ginzburgTwoDifferential_mem_gradeBy_ginzburgTwoAdamsDegree k hx

/-- **The completed two-dimensional Ginzburg differential graded algebra** `Π̂₂(Q)`. -/
theorem isDGAlgebra_completedGinzburgTwoDifferential :
    IsDGAlgebra (completedGinzburgTwoGrading k Q) (completedGinzburgTwoDifferential k Q) :=
  isDGAlgebra_adamsCompletionDifferential _ _ _ _

/-! ### The comparison morphism -/

/-- **The comparison morphism `Π₂(Q) → Π̂₂(Q)`** of differential graded algebras, sending an
element of the Ginzburg path algebra to the series of its Adams-homogeneous components. -/
noncomputable def ginzburgTwoToCompleted :
    DGAlgHom (isDGAlgebra_ginzburgTwoDifferential k (Q := Q))
      (isDGAlgebra_completedGinzburgTwoDifferential k Q) :=
  toAdamsCompletion _ _ _ _ (isHomogeneous_gradeBy_ginzburgTwoAdamsDegree k)

@[simp]
theorem coe_ginzburgTwoToCompleted_apply (x : pathAlgebra k (GinzburgQuiver Q)) :
    ((ginzburgTwoToCompleted k Q x : completedGinzburgTwo k Q) :
        PowerSeries (pathAlgebra k (GinzburgQuiver Q))) =
      gradedComponentSeries (gradeBy k (ginzburgTwoAdamsDegree (Q := Q))) x :=
  coe_toAdamsCompletion_apply _ _ _ _ _ x

/-- The coefficient of index `n` of the image of an element of `Π₂(Q)` is its component of Adams
degree `n`. -/
theorem coeff_ginzburgTwoToCompleted (x : pathAlgebra k (GinzburgQuiver Q)) (n : ℕ) :
    coeff n (ginzburgTwoToCompleted k Q x : PowerSeries (pathAlgebra k (GinzburgQuiver Q))) =
      (decompose (gradeBy k ginzburgTwoAdamsDegree) x n : pathAlgebra k (GinzburgQuiver Q)) := by
  rw [coe_ginzburgTwoToCompleted_apply, coeff_gradedComponentSeries]

/-- **`Π₂(Q)` embeds in `Π̂₂(Q)`.** -/
theorem ginzburgTwoToCompleted_injective : Function.Injective (ginzburgTwoToCompleted k Q) :=
  toAdamsCompletion_injective _ _ _ _ _

/-- **`Π₂(Q)` is the finite-support part of `Π̂₂(Q)`**: an element of the completion comes from
the non-completed algebra exactly when only finitely many of its coefficients are nonzero. -/
theorem mem_range_ginzburgTwoToCompleted_iff {f : completedGinzburgTwo k Q} :
    f ∈ Set.range (ginzburgTwoToCompleted k Q) ↔
      (Function.support fun n =>
        coeff n (f : PowerSeries (pathAlgebra k (GinzburgQuiver Q)))).Finite :=
  mem_range_toAdamsCompletion_iff _ _ _ _ _

/-- **In the completion, the differential of the adjoined loop `t_i` is the local preprojective
relator `ρ_i`**, the defining equation of the two-dimensional Ginzburg differential. -/
theorem completedGinzburgTwoDifferential_ginzburgTwoToCompleted_loop (i : Q) :
    completedGinzburgTwoDifferential k Q
        (ginzburgTwoToCompleted k Q (ofArrow (GinzburgHom.loop i))) =
      ginzburgTwoToCompleted k Q (ginzburgMap k (localPreprojectiveRelator k i)) := by
  rw [DGAlgHom.map_d, ginzburgTwoDifferential_ofArrow_loop]

end TauCeti
