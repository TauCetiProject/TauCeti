/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Finite
public import TauCeti.NumberTheory.NumberField.CMType.Overlap.Descent
import Mathlib.LinearAlgebra.Span.Basic

/-!
# The span of CM overlap characters

The subspace `CMClassFunction.overlapSpan` is the domain on which total CM heights determine
a linear functional. Its generators are the `CMType.galoisAverageOverlap` of types on finite
étale rational algebras. The span is proper: every member vanishes at complex conjugation and
is invariant under inversion, while the constant function one does not vanish there.
`CMClassFunction.overlapSpan_linearMap_eq_iff` tests equality on the overlaps using
`LinearMap.ext_on`.

## References

* F. Andreatta, E. Z. Goren, B. Howard and K. Madapusi Pera, *Faltings heights of abelian
  varieties with complex multiplication*, Ann. of Math. 187 (2018), Definition 9.1.1 and
  Remark 9.1.2.
-/

public section

namespace TauCeti

universe v u

variable (Ω : Type v) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Algebra Ω ℂ]

local notation "cΩ" => AlgEquiv.restrictNormal (RingEquiv.toRatAlgEquiv (starRingAut : RingAut ℂ)) Ω

namespace CMClassFunction

/-- The conjugacy-averaged overlap characters of CM types on finite étale rational algebras in
universe `u`, viewed as elements of CM⁰ on the absolute Galois group. -/
def overlapGenerators : Set (CMClassFunction ℚ cΩ) :=
  {a | ∃ (E : CommAlgCat.FiniteEtale.{u} ℚ) (_ : CMType.StarCompCommute E) (Φ : CMType E),
    Φ.galoisAverageOverlap Ω = a}

variable {Ω} in
/-- Membership in the generator set means being the averaged overlap of a CM type. -/
@[simp]
theorem mem_overlapGenerators_iff {a : CMClassFunction ℚ cΩ} :
    a ∈ overlapGenerators.{v, u} Ω ↔
      ∃ (E : CommAlgCat.FiniteEtale.{u} ℚ) (_ : CMType.StarCompCommute E) (Φ : CMType E),
        Φ.galoisAverageOverlap Ω = a :=
  (Iff.rfl)

/-- The rational span `H_CM` of all conjugacy-averaged overlaps. In `overlapSpan.{v, u} Ω`,
`v` is the universe of the algebraic closure and `u` is that of the finite étale algebras. -/
noncomputable def overlapSpan : Submodule ℚ (CMClassFunction ℚ cΩ) :=
  Submodule.span ℚ (overlapGenerators.{v, u} Ω)

/-- The defining span of the overlap subspace. This is not a simp lemma so that
`CMType.galoisAverageOverlap_mem_overlapSpan` can recognize the abstract span. -/
theorem overlapSpan_eq_span :
    overlapSpan.{v, u} Ω = Submodule.span ℚ (overlapGenerators.{v, u} Ω) :=
  (rfl)

end CMClassFunction

/-- Each conjugacy-averaged overlap of a CM type belongs to the overlap span. -/
@[simp]
theorem CMType.galoisAverageOverlap_mem_overlapSpan
    {E : CommAlgCat.FiniteEtale.{u} ℚ} [CMType.StarCompCommute E] (Φ : CMType E) :
    Φ.galoisAverageOverlap Ω ∈ CMClassFunction.overlapSpan.{v, u} Ω := by
  rw [CMClassFunction.overlapSpan_eq_span]
  exact Submodule.subset_span ((CMClassFunction.mem_overlapGenerators_iff).mpr
    ⟨E, ‹_›, Φ, rfl⟩)

namespace CMClassFunction

variable {Ω} in
/-- Every member of the overlap span vanishes at complex conjugation. -/
theorem apply_complexConj_eq_zero_of_mem_overlapSpan {a : CMClassFunction ℚ cΩ}
    (ha : a ∈ overlapSpan.{v, u} Ω) : a.val.val cΩ = 0 := by
  rw [overlapSpan_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨E, hE, Φ, rfl⟩ := mem_overlapGenerators_iff.mp ha
    exact Φ.galoisAverageOverlap_starRingAut Ω
  | zero => simp only [Submodule.coe_zero, Pi.zero_apply]
  | add x y _ _ ihx ihy =>
    simp only [Submodule.coe_add, Pi.add_apply, ihx, ihy, add_zero]
  | smul r x _ ih => simp only [Submodule.coe_smul, Pi.smul_apply, ih, smul_zero]

variable {Ω} in
/-- Every member of the overlap span is invariant under inversion. -/
theorem apply_inv_eq_of_mem_overlapSpan {a : CMClassFunction ℚ cΩ}
    (ha : a ∈ overlapSpan.{v, u} Ω) (g : Gal(Ω/ℚ)) : a.val.val g⁻¹ = a.val.val g := by
  rw [overlapSpan_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨E, hE, Φ, rfl⟩ := mem_overlapGenerators_iff.mp ha
    exact Φ.galoisAverageOverlap_inv Ω g
  | zero => simp only [Submodule.coe_zero, Pi.zero_apply]
  | add x y _ _ ihx ihy => simp only [Submodule.coe_add, Pi.add_apply, ihx, ihy]
  | smul r x _ ih => simp only [Submodule.coe_smul, Pi.smul_apply, ih]

/-- The overlap span is strictly smaller than CM⁰, since the constant function one belongs to
CM⁰ but does not vanish at complex conjugation. -/
theorem overlapSpan_lt_top : overlapSpan.{v, u} Ω < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  let a : CMClassFunction ℚ cΩ :=
    ⟨ClassFunction.ofConjClasses 1, ofConjClasses_one_mem⟩
  have ha : a ∈ overlapSpan.{v, u} Ω := by rw [htop]; exact Submodule.mem_top
  have hz := apply_complexConj_eq_zero_of_mem_overlapSpan ha
  have hone : a.val.val cΩ = 1 := by
    simp only [a, ClassFunction.ofConjClasses_apply, Pi.one_apply]
  exact one_ne_zero (hone.symm.trans hz)

variable {Ω} in
/-- Two linear maps on the overlap span agree exactly when they agree on each generating
averaged overlap. This is not a simp lemma since the generator test expands an equality into a
quantified condition. -/
theorem overlapSpan_linearMap_eq_iff {M : Type*} [AddCommMonoid M] [Module ℚ M]
    {f g : overlapSpan.{v, u} Ω →ₗ[ℚ] M} :
    f = g ↔ ∀ (E : CommAlgCat.FiniteEtale.{u} ℚ) (_ : CMType.StarCompCommute E) (Φ : CMType E),
      f ⟨Φ.galoisAverageOverlap Ω, Φ.galoisAverageOverlap_mem_overlapSpan Ω⟩ =
        g ⟨Φ.galoisAverageOverlap Ω, Φ.galoisAverageOverlap_mem_overlapSpan Ω⟩ :=
  ⟨fun h ↦ by subst g; exact fun _ _ _ ↦ rfl, fun h ↦ by
    have hspan (S : Submodule ℚ (CMClassFunction ℚ cΩ))
        (hS : S = Submodule.span ℚ (overlapGenerators.{v, u} Ω)) :
        Submodule.span ℚ (((↑) : S → CMClassFunction ℚ cΩ) ⁻¹'
          overlapGenerators.{v, u} Ω) = ⊤ := by
      subst S
      exact Submodule.span_span_coe_preimage
    exact LinearMap.ext_on (hspan _ (overlapSpan_eq_span Ω)) fun a ha ↦ by
      obtain ⟨E, hE, Φ, heq⟩ := mem_overlapGenerators_iff.mp (Set.mem_preimage.mp ha)
      exact (Subtype.ext heq :
        (⟨Φ.galoisAverageOverlap Ω, Φ.galoisAverageOverlap_mem_overlapSpan Ω⟩ :
          overlapSpan.{v, u} Ω) = a) ▸ h E hE Φ⟩

end CMClassFunction

end TauCeti
