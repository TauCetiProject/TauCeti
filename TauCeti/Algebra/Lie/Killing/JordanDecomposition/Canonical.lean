/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.JordanDecomposition.Basic

/-!
# Canonical internal Jordan decomposition

In a finite-dimensional Killing Lie algebra over an algebraically closed field, the internal
Jordan decomposition determines canonical nilpotent and semisimple parts. Here nilpotence and
semisimplicity refer to the adjoint endomorphism, not to a chosen representation. The
characterization by commuting parts makes the construction independent of the choices used in
its existence proof. Lie algebra isomorphisms preserve both parts, so in particular every action
by Lie algebra automorphisms preserves the decomposition.

The existence and uniqueness results in `JordanDecomposition.Basic` are the central inputs.
No assertion is made here about transport through a general Lie homomorphism or representation.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.4.
-/

public section

open LieAlgebra Module.End

namespace TauCeti.LieAlgebra

variable (K : Type*) {L : Type*} [Field K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]

/-- The internal Jordan decomposition, ordered as (nilpotent part, semisimple part). -/
noncomputable def jordanDecomposition (x : L) : L × L :=
  let h := TauCeti.exists_isNilpotent_ad_isSemisimple_ad (K := K) x
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

/-- The canonical parts have polynomial adjoint actions, are respectively nilpotent and
semisimple, commute, and sum to the original element. -/
theorem jordanDecomposition_spec (x : L) :
    ad K L (jordanDecomposition K x).1 ∈ Algebra.adjoin K {ad K L x} ∧
      ad K L (jordanDecomposition K x).2 ∈ Algebra.adjoin K {ad K L x} ∧
      IsNilpotent (ad K L (jordanDecomposition K x).1) ∧
      IsSemisimple (ad K L (jordanDecomposition K x).2) ∧
      ⁅(jordanDecomposition K x).1, (jordanDecomposition K x).2⁆ = 0 ∧
      x = (jordanDecomposition K x).1 + (jordanDecomposition K x).2 := by
  simpa only [jordanDecomposition] using
    Classical.choose_spec (Classical.choose_spec
      (TauCeti.exists_isNilpotent_ad_isSemisimple_ad (K := K) x))

/-- A pair is the canonical internal Jordan decomposition exactly when it consists of commuting
ad-nilpotent and ad-semisimple elements whose sum is the given element. -/
theorem eq_jordanDecomposition_iff (x n s : L) :
    (n, s) = jordanDecomposition K x ↔
      IsNilpotent (ad K L n) ∧ IsSemisimple (ad K L s) ∧ ⁅n, s⁆ = 0 ∧ x = n + s := by
  constructor
  · intro h
    simpa only [← h] using (jordanDecomposition_spec K x).2.2
  · rintro ⟨hn, hs, hns, hx⟩
    obtain ⟨_, _, hn', hs', hns', hx'⟩ := jordanDecomposition_spec K x
    obtain ⟨hnn, hss⟩ := TauCeti.isNilpotent_ad_isSemisimple_ad_unique
      hn hs hn' hs' hns hns' (hx.symm.trans hx')
    exact Prod.ext hnn hss

/-- The nilpotent part of the internal Jordan decomposition. -/
noncomputable def nilpotentPart (x : L) : L := (jordanDecomposition K x).1

/-- The semisimple part of the internal Jordan decomposition. -/
noncomputable def semisimplePart (x : L) : L := (jordanDecomposition K x).2

/-- The nilpotent part is the first component of the internal Jordan decomposition. -/
theorem nilpotentPart_def (x : L) : nilpotentPart K x = (jordanDecomposition K x).1 := (rfl)

/-- The semisimple part is the second component of the internal Jordan decomposition. -/
theorem semisimplePart_def (x : L) : semisimplePart K x = (jordanDecomposition K x).2 := (rfl)

/-- The adjoint action of the nilpotent part is a polynomial in the original adjoint action. -/
theorem ad_nilpotentPart_mem_adjoin (x : L) :
    ad K L (nilpotentPart K x) ∈ Algebra.adjoin K {ad K L x} :=
  (jordanDecomposition_spec K x).1

/-- The adjoint action of the semisimple part is a polynomial in the original adjoint action. -/
theorem ad_semisimplePart_mem_adjoin (x : L) :
    ad K L (semisimplePart K x) ∈ Algebra.adjoin K {ad K L x} :=
  (jordanDecomposition_spec K x).2.1

/-- The nilpotent part is ad-nilpotent. -/
@[simp]
theorem isNilpotent_ad_nilpotentPart (x : L) : IsNilpotent (ad K L (nilpotentPart K x)) :=
  (jordanDecomposition_spec K x).2.2.1

/-- The semisimple part is ad-semisimple. -/
@[simp]
theorem isSemisimple_ad_semisimplePart (x : L) : IsSemisimple (ad K L (semisimplePart K x)) :=
  (jordanDecomposition_spec K x).2.2.2.1

/-- The two internal Jordan parts commute. -/
@[simp]
theorem lie_nilpotentPart_semisimplePart (x : L) :
    ⁅nilpotentPart K x, semisimplePart K x⁆ = 0 :=
  (jordanDecomposition_spec K x).2.2.2.2.1

/-- The sum of the internal Jordan parts is the original element. -/
@[simp]
theorem nilpotentPart_add_semisimplePart (x : L) :
    nilpotentPart K x + semisimplePart K x = x :=
  (jordanDecomposition_spec K x).2.2.2.2.2.symm

/-- An ad-nilpotent element has itself as nilpotent part and zero as semisimple part. -/
theorem jordanDecomposition_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad K L x)) :
    jordanDecomposition K x = (x, 0) := by
  symm
  exact (eq_jordanDecomposition_iff K x x 0).2 ⟨hx, by simp, by simp, by simp⟩

/-- An ad-semisimple element has zero as nilpotent part and itself as semisimple part. -/
theorem jordanDecomposition_of_isSemisimple_ad {x : L} (hx : IsSemisimple (ad K L x)) :
    jordanDecomposition K x = (0, x) := by
  symm
  exact (eq_jordanDecomposition_iff K x 0 x).2 ⟨by simp, hx, by simp, by simp⟩

/-- The nilpotent part vanishes exactly for ad-semisimple elements. -/
@[simp]
theorem nilpotentPart_eq_zero_iff (x : L) :
    nilpotentPart K x = 0 ↔ IsSemisimple (ad K L x) := by
  constructor
  · intro h
    have hx : semisimplePart K x = x := by simpa [h] using nilpotentPart_add_semisimplePart K x
    simpa only [hx] using isSemisimple_ad_semisimplePart K x
  · intro h
    simp [nilpotentPart_def, jordanDecomposition_of_isSemisimple_ad K h]

/-- The semisimple part vanishes exactly for ad-nilpotent elements. -/
@[simp]
theorem semisimplePart_eq_zero_iff (x : L) :
    semisimplePart K x = 0 ↔ IsNilpotent (ad K L x) := by
  constructor
  · intro h
    have hx : nilpotentPart K x = x := by simpa [h] using nilpotentPart_add_semisimplePart K x
    simpa only [hx] using isNilpotent_ad_nilpotentPart K x
  · intro h
    simp [semisimplePart_def, jordanDecomposition_of_isNilpotent_ad K h]

/-- Taking the nilpotent part fixes an ad-nilpotent element. -/
@[simp]
theorem nilpotentPart_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad K L x)) :
    nilpotentPart K x = x := by
  simp [nilpotentPart_def, jordanDecomposition_of_isNilpotent_ad K hx]

/-- Taking the semisimple part fixes an ad-semisimple element. -/
@[simp]
theorem semisimplePart_of_isSemisimple_ad {x : L} (hx : IsSemisimple (ad K L x)) :
    semisimplePart K x = x := by
  simp [semisimplePart_def, jordanDecomposition_of_isSemisimple_ad K hx]

end TauCeti.LieAlgebra

namespace LieEquiv

open TauCeti.LieAlgebra

variable {K L L' : Type*} [Field K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  [LieRing L'] [LieAlgebra K L'] [FiniteDimensional K L'] [IsKilling K L']

/-- Lie algebra isomorphisms preserve the internal Jordan decomposition. In particular this
applies to any action by Lie algebra automorphisms. -/
theorem map_jordanDecomposition (e : L ≃ₗ⁅K⁆ L') (x : L) :
    jordanDecomposition K (e x) =
      (e (nilpotentPart K x), e (semisimplePart K x)) := by
  symm
  apply (eq_jordanDecomposition_iff K (e x) _ _).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← conj_ad_apply]
    exact (isNilpotent_ad_nilpotentPart K x).map (e.toLinearEquiv.conjAlgEquiv K)
  · apply (LinearEquiv.isSemisimple_iff (ad K L (semisimplePart K x))
      (ad K L' (e (semisimplePart K x))) e.toLinearEquiv ?_).mp
      (isSemisimple_ad_semisimplePart K x)
    ext y
    exact e.map_lie _ _
  · rw [← map_lie, lie_nilpotentPart_semisimplePart, map_zero]
  · rw [← map_add, nilpotentPart_add_semisimplePart]

/-- Lie algebra isomorphisms preserve nilpotent parts. -/
@[simp]
theorem map_nilpotentPart (e : L ≃ₗ⁅K⁆ L') (x : L) :
    nilpotentPart K (e x) = e (nilpotentPart K x) := by
  simpa only [nilpotentPart_def] using congrArg Prod.fst (e.map_jordanDecomposition x)

/-- Lie algebra isomorphisms preserve semisimple parts. -/
@[simp]
theorem map_semisimplePart (e : L ≃ₗ⁅K⁆ L') (x : L) :
    semisimplePart K (e x) = e (semisimplePart K x) := by
  simpa only [semisimplePart_def] using congrArg Prod.snd (e.map_jordanDecomposition x)

end LieEquiv
