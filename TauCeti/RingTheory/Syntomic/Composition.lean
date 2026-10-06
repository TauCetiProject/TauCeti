/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Syntomic.StandardSyntomic
import Mathlib.RingTheory.Flat.Stability
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.KrullDimension.Presentation

/-!
# Composition of standard syntomic algebras

For a scalar tower `R → S → T`, standard syntomic algebras of relative dimensions `n` and
`m` compose to a standard syntomic algebra of relative dimension `n + m`. This is the
algebraic composition theorem for the local complete-intersection charts of syntomic
morphisms. There are no Noetherian or nontriviality assumptions on the rings in the tower.

Every nonempty fibre of the composite has dimension `n + m`, even when either map also
has empty fibres.

## References

* [Stacks Project, Section 10.136, Tag 00SK](https://stacks.math.columbia.edu/tag/00SK):
  relative global complete intersections and standard syntomic ring maps.
-/

public section

open TensorProduct

namespace TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension

universe u v w

variable {n m : ℕ} {R : Type u} {S : Type v} {T : Type w}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Standard syntomic algebras compose, with addition of their relative dimensions. -/
theorem trans [hS : IsStandardSyntomicOfRelativeDimension n R S]
    [hT : IsStandardSyntomicOfRelativeDimension m S T] :
    IsStandardSyntomicOfRelativeDimension (n + m) R T := by
  have := hS.flat
  have := hT.flat
  have : Module.Flat R T := .trans R S T
  obtain ⟨ι, σ, _, _, P, hP⟩ := hS.exists_presentation
  obtain ⟨ι', σ', _, _, Q, hQ⟩ := hT.exists_presentation
  have hcard : Nat.card (ι' ⊕ ι) = n + m + Nat.card (σ' ⊕ σ) := by
    simp only [Nat.card_sum]
    omega
  refine (Q.comp P).isStandardSyntomicOfRelativeDimension hcard fun p _ _ ↦ ?_
  have hdim : ((Q.comp P).baseChange p.ResidueField).dimension = n + m := by
    simp only [_root_.Algebra.Presentation.dimension, hcard]
    omega
  -- A maximal ideal of the nonempty total fibre supplies the presentation lower bound.
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := p.Fiber T)
  have : M.IsMaximal := hM
  have hlow := ((Q.comp P).baseChange p.ResidueField).dimension_le_height_of_isMaximal M
  rw [hdim] at hlow
  refine le_antisymm ?_ ((WithBot.coe_le_coe.mpr hlow).trans
    Ideal.height_le_ringKrullDim_of_isPrime)
  -- View the total fibre as a base change of `T` over the intermediate fibre of `S`.
  let F := S ⊗[R] p.ResidueField
  let G := F ⊗[S] T
  let e : G ≃+* p.Fiber T :=
    (_root_.Algebra.TensorProduct.comm S F T).toRingEquiv.trans
      ((_root_.Algebra.TensorProduct.cancelBaseChange R S S T p.ResidueField).toRingEquiv.trans
        (_root_.Algebra.TensorProduct.comm R T p.ResidueField).toRingEquiv)
  have := hS.finitePresentation
  have := hT.finitePresentation
  have : IsNoetherianRing (p.Fiber S) :=
    _root_.Algebra.FiniteType.isNoetherianRing p.ResidueField (p.Fiber S)
  have : IsNoetherianRing F := isNoetherianRing_of_ringEquiv (p.Fiber S)
    (_root_.Algebra.TensorProduct.comm R p.ResidueField S).toRingEquiv
  have : IsNoetherianRing G := _root_.Algebra.FiniteType.isNoetherianRing F G
  have hF : ringKrullDim F ≤ n :=
    (ringKrullDim_eq_of_ringEquiv
      (_root_.Algebra.TensorProduct.comm R S p.ResidueField).toRingEquiv).trans_le
        (hS.ringKrullDim_fiber_le p)
  have hG : ringKrullDim G ≤ ringKrullDim F + m :=
    ringKrullDim_le_ringKrullDim_add_of_ringKrullDim_fiber_le
      (fun q _ ↦ (baseChange (n := m) (R := S) (S := T) F).ringKrullDim_fiber_le q)
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact hG.trans (by simpa only [Nat.cast_add] using add_le_add_left hF (m : WithBot ℕ∞))

end TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension
