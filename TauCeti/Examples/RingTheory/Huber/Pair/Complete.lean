/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair.Complete
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Checks for completeness of rings of integral elements

The subring `A⁺` is allowed to vary: on `ℚ_p` the prime `p` gives the adic topology,
completeness, and the localization description for every ring of integral elements.
The nonunit conclusion is tested on `p` and on zero. The zero-ring checks verify that
completeness and localization do not require nontriviality, whereas excluding units does.
-/

public section

open Topology

namespace TauCeti.Huber.IntegralElementsCompleteChecks

variable (p : ℕ) [Fact p.Prime]

/-- The topology on every ring of integral elements of `ℚ_p` is the `p`-adic topology. -/
example {Aplus : Subring ℚ_[p]} (h : IsRingOfIntegralElements Aplus) :
    IsAdic (Ideal.span {(p : Aplus)}) := by
  exact Aplus.isAdic_span_singleton_of_isOpen_of_isBounded h.isOpen h.isBounded
    (by simpa using Padic.isPseudoUniformizer_p (p := p)) (p : Aplus).property

/-- Completeness holds for the same prime and the same arbitrary plus ring. -/
example {Aplus : Subring ℚ_[p]} (h : IsRingOfIntegralElements Aplus) :
    IsAdicComplete (Ideal.span {(p : Aplus)}) Aplus :=
  h.isAdicComplete_span_singleton _ (by simpa using Padic.isPseudoUniformizer_p (p := p))

/-- Inverting `p` in that plus ring recovers `ℚ_p`, on its existing scalar structure. -/
example {Aplus : Subring ℚ_[p]} (h : IsRingOfIntegralElements Aplus) :
    IsLocalization.Away (p : Aplus) ℚ_[p] :=
  Aplus.isLocalizationAway_of_isOpen h.isOpen _
    (by simpa using (Padic.isPseudoUniformizer_p (p := p)).isTopologicallyNilpotent)
    (by simpa using (Padic.isPseudoUniformizer_p (p := p)).isUnit)

/-- The prime is not invertible in any plus ring of `ℚ_p`. -/
example {Aplus : Subring ℚ_[p]} (h : IsRingOfIntegralElements Aplus) :
    ¬ IsUnit (p : Aplus) :=
  h.not_isUnit_of_isTopologicallyNilpotent (a := (p : Aplus))
    (by simpa using (Padic.isPseudoUniformizer_p (p := p)).isTopologicallyNilpotent)

/-- Zero is another topologically nilpotent nonunit, without a pseudouniformiser hypothesis. -/
example {Aplus : Subring ℚ_[p]} (h : IsRingOfIntegralElements Aplus) :
    ¬ IsUnit (0 : Aplus) :=
  h.not_isUnit_of_isTopologicallyNilpotent (a := (0 : Aplus))
    (by simpa using (IsTopologicallyNilpotent.zero : IsTopologicallyNilpotent (0 : ℚ_[p])))

/-- Regularity in the plus ring follows from being a unit in the ambient ring, even when
neither ring is a domain. -/
example {A : Type*} [CommRing A] [TopologicalSpace A] (S : Subring A) (a : S)
    (ha : IsPseudoUniformizer (a : A)) : IsSMulRegular S a := by
  intro x y hxy
  apply Subtype.ext
  exact ha.isUnit.isRegular.left (congrArg (fun z : S ↦ (z : A)) hxy)

/-- The completeness assertion includes zero rings with the zero pseudouniformiser. -/
example {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [NonarchimedeanRing A] [CompleteSpace A] [T0Space A] [Subsingleton A] [IsUniform A]
    {Aplus : Subring A} (h : IsRingOfIntegralElements Aplus) :
    IsAdicComplete (Ideal.span {(0 : Aplus)}) Aplus := by
  apply h.isAdicComplete_span_singleton
  exact isPseudoUniformizer_iff.mpr ⟨isUnit_of_subsingleton _, IsTopologicallyNilpotent.zero⟩

/-- The localization assertion also includes zero rings and does not need uniformity. -/
example {A : Type*} [CommRing A] [TopologicalSpace A] [Subsingleton A]
    [SeparatelyContinuousMul A] (S : Subring A) (hS : IsOpen (S : Set A)) :
    IsLocalization.Away (0 : S) A :=
  S.isLocalizationAway_of_isOpen hS 0 IsTopologicallyNilpotent.zero (isUnit_of_subsingleton _)

/-- Nontriviality is essential for the nonunit conclusion. -/
example {A : Type*} [CommRing A] [Subsingleton A] (S : Subring A) : IsUnit (0 : S) :=
  isUnit_of_subsingleton _

end TauCeti.Huber.IntegralElementsCompleteChecks
