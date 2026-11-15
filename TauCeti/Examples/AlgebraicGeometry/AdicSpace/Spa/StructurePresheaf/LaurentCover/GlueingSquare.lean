/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.GlueingSquare
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglySheafy
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.Restricted.Noetherian
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc

/-!
# End-to-end checks for simple Laurent glueing squares

* Canonical existence theorem `exists_simpleLaurent_glueingSquare`: for any complete Hausdorff
  sheafy Tate ring `R`, pair of definition `P`, and element `f : R`, the canonical `ratLoc`
  completed rational localisations `R⟨f, 1/1⟩`, `R⟨1/f⟩`, and `R⟨f², 1/f⟩` (with transition maps
  supplied by `IsRationalCompletion.existsUnique_laurentLeftAlgHom` and
  `IsRationalCompletion.existsUnique_laurentRightAlgHom`) witness models `R₁`, `R₂`, `R₁₂` forming a
  `GlueingSquare`.
* Non-vacuous field check: `ℚ_[p]` at `f = p`.
* Non-vacuous geometric check: the `1`-variable Tate algebra `ℚ_p⟨X⟩` at its coordinate variable
  `X`, glueing the closed unit disc `Spa(ℚ_p⟨X⟩)` across `{|X| ≤ 1}` and `{|X| ≥ 1}` over the unit
  circle `{|X| = 1}`, together with flat module recovery for `ℚ_p⟨X⟩ × ℚ_p⟨X⟩`.
-/

public section

namespace TauCeti.Huber.LaurentGlueingSquareChecks

/-- Any finite set containing `1` generates the unit ideal, which is open. -/
theorem isOpen_span_of_one_mem {A : Type*} [CommRing A] [TopologicalSpace A] {T : Finset A}
    (h1 : (1 : A) ∈ T) : IsOpen (Ideal.span (T : Set A) : Set A) := by
  have htop : Ideal.span (T : Set A) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Finset.mem_coe.mpr h1)) isUnit_one
  rw [htop]
  exact isOpen_univ

section CanonicalModels

variable {R : Type u} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsTateRing R] [CompleteSpace R] [T2Space R]

open Classical in
/-- For any complete Hausdorff sheafy Tate ring `R`, pair of definition `P`, and `f : R`, there
exist models `R₁`, `R₂`, `R₁₂` of `R⟨f, 1/1⟩`, `R⟨1/f⟩`, and `R⟨f², 1/f⟩` (constructed from
`ratLoc` and `existsUnique_laurentLeftAlgHom` / `existsUnique_laurentRightAlgHom`) that form a
`GlueingSquare`. -/
theorem exists_simpleLaurent_glueingSquare (hs : IsSheafyRing R) (P : PairOfDefinition R)
    (f : R) :
    ∃ (R₁ R₂ R₁₂ : Type u) (_ : CommRing R₁) (_ : CommRing R₂) (_ : CommRing R₁₂)
      (_ : TopologicalSpace R₁) (_ : TopologicalSpace R₂) (_ : TopologicalSpace R₁₂)
      (_ : Algebra R R₁) (_ : Algebra R R₂) (_ : Algebra R R₁₂)
      (_ : Algebra R₁ R₁₂) (_ : Algebra R₂ R₁₂)
      (_ : IsScalarTower R R₁ R₁₂) (_ : IsScalarTower R R₂ R₁₂),
      IsRationalCompletion P {f, 1} 1 (isOpen_span_of_one_mem (by simp)) R₁ ∧
        IsRationalCompletion P {1} f (isOpen_span_of_one_mem (by simp)) R₂ ∧
        IsRationalCompletion P {f * f, 1} f (isOpen_span_of_one_mem (by simp)) R₁₂ ∧
        GlueingSquare R R₁ R₂ R₁₂ := by
  let T₁ : Finset R := {f, 1}
  let T₂ : Finset R := {1}
  let T₁₂ : Finset R := {f * f, 1}
  have hT₁ : IsOpen (Ideal.span (T₁ : Set R) : Set R) := isOpen_span_of_one_mem (by simp [T₁])
  have hT₂ : IsOpen (Ideal.span (T₂ : Set R) : Set R) := isOpen_span_of_one_mem (by simp [T₂])
  have hT₁₂ : IsOpen (Ideal.span (T₁₂ : Set R) : Set R) := isOpen_span_of_one_mem (by simp [T₁₂])
  let h₁ := isRationalCompletion_ratLoc P T₁ 1 hT₁
  let h₂ := isRationalCompletion_ratLoc P T₂ f hT₂
  let h₁₂ := isRationalCompletion_ratLoc P T₁₂ f hT₁₂
  let ρ₁ := (h₁.existsUnique_laurentLeftAlgHom h₁₂).choose
  let ρ₂ := (h₂.existsUnique_laurentRightAlgHom h₁₂).choose
  let _ := ρ₁.toRingHom.toAlgebra
  let _ := ρ₂.toRingHom.toAlgebra
  have hc₁ := (h₁.existsUnique_laurentLeftAlgHom h₁₂).choose_spec.1
  have hc₂ := (h₂.existsUnique_laurentRightAlgHom h₁₂).choose_spec.1
  have _ := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₁.commutes r).symm
  have _ := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, h₁, h₂, h₁₂,
    GlueingSquare.of_simpleLaurent_of_isSheafyRing hs h₁ h₂ h₁₂ hc₁ hc₂⟩

end CanonicalModels

section ConcreteTateRings

variable (p : ℕ) [Fact p.Prime]

open Classical in
/-- **Field check**: `ℚ_[p]` admits a simple Laurent `GlueingSquare` at `f = p` with all hypotheses
discharged unconditionally. -/
example :
    let P := (IsHuberRing.nonempty_pairOfDefinition (A := ℚ_[p])).some
    ∃ (R₁ R₂ R₁₂ : Type) (_ : CommRing R₁) (_ : CommRing R₂) (_ : CommRing R₁₂)
      (_ : TopologicalSpace R₁) (_ : TopologicalSpace R₂) (_ : TopologicalSpace R₁₂)
      (_ : Algebra ℚ_[p] R₁) (_ : Algebra ℚ_[p] R₂) (_ : Algebra ℚ_[p] R₁₂)
      (_ : Algebra R₁ R₁₂) (_ : Algebra R₂ R₁₂)
      (_ : IsScalarTower ℚ_[p] R₁ R₁₂) (_ : IsScalarTower ℚ_[p] R₂ R₁₂),
      IsRationalCompletion P {(p : ℚ_[p]), 1} 1 (isOpen_span_of_one_mem (by simp)) R₁ ∧
        IsRationalCompletion P {1} (p : ℚ_[p]) (isOpen_span_of_one_mem (by simp)) R₂ ∧
        IsRationalCompletion P {(p : ℚ_[p]) * p, 1} (p : ℚ_[p])
          (isOpen_span_of_one_mem (by simp)) R₁₂ ∧
        GlueingSquare ℚ_[p] R₁ R₂ R₁₂ :=
  exists_simpleLaurent_glueingSquare IsStronglySheafy.of_isStronglyNoetherian.isSheafyRing _ _

open Classical in
/-- **Tate algebra and module glueing check**: on the `1`-variable Tate algebra `ℚ_p⟨X⟩`, the simple
Laurent cover by `{|X| ≤ 1}` and `{|X| ≥ 1}` at the coordinate variable `X` forms a `GlueingSquare`
and recovers the rank-`2` free module `ℚ_p⟨X⟩ × ℚ_p⟨X⟩` from the sections of its induced glueing
datum, with all hypotheses discharged unconditionally. -/
example :
    let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]
    let X : A := Pair.polydiscVar 1 ℚ_[p] 0
    let P := (IsHuberRing.nonempty_pairOfDefinition (A := A)).some
    ∃ (R₁ R₂ R₁₂ : Type) (_ : CommRing R₁) (_ : CommRing R₂) (_ : CommRing R₁₂)
      (_ : TopologicalSpace R₁) (_ : TopologicalSpace R₂) (_ : TopologicalSpace R₁₂)
      (_ : Algebra A R₁) (_ : Algebra A R₂) (_ : Algebra A R₁₂)
      (_ : Algebra R₁ R₁₂) (_ : Algebra R₂ R₁₂)
      (_ : IsScalarTower A R₁ R₁₂) (_ : IsScalarTower A R₂ R₁₂),
      IsRationalCompletion P {X, 1} 1 (isOpen_span_of_one_mem (by simp)) R₁ ∧
        IsRationalCompletion P {1} X (isOpen_span_of_one_mem (by simp)) R₂ ∧
        IsRationalCompletion P {X * X, 1} X (isOpen_span_of_one_mem (by simp)) R₁₂ ∧
        GlueingSquare A R₁ R₂ R₁₂ ∧
        Nonempty ((A × A) ≃ₗ[A] (GlueingDatum.ofModule R₁ R₂ R₁₂ A (A × A)).sections A) := by
  let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]
  let X : A := Pair.polydiscVar 1 ℚ_[p] 0
  let P := (IsHuberRing.nonempty_pairOfDefinition (A := A)).some
  have hs : IsSheafyRing A :=
    ((IsStronglySheafy.of_isStronglyNoetherian (A := ℚ_[p])).restrictedMvPowerSeriesCompletion
      1).isSheafyRing
  obtain ⟨R₁, R₂, R₁₂, _, _, _, _, _, _, _, _, _, _, _, _, _, h₁, h₂, h₁₂, hsq⟩ :=
    exists_simpleLaurent_glueingSquare hs P X
  exact ⟨R₁, R₂, R₁₂, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›,
    h₁, h₂, h₁₂, hsq, ⟨hsq.equivSectionsOfModule (A × A)⟩⟩

end ConcreteTateRings

end TauCeti.Huber.LaurentGlueingSquareChecks

end
