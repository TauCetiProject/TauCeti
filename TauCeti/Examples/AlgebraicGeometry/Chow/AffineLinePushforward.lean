/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.AffineSpace
public import TauCeti.AlgebraicGeometry.Chow.PointCycle

/-!
# Example: pushforward of cycles along the affine line does not descend to `CH_0`

On the affine line `𝔸¹_k = Spec k[X]` over a field `k`, the zero-cycle `[0]` of the origin is
rationally equivalent to zero, as `CH_0(𝔸¹_k) = 0`
(`TauCeti.AlgebraicGeometry.Chow.subsingleton_chowGroup_zero_affineLine`), but its pushforward
along the structure morphism `𝔸¹_k ⟶ Spec k`, which is not proper, is the class of the point,
which is `1` under `CH_0(Spec k) ≃ ℤ`. So the cycle-level pushforward along `𝔸¹_k ⟶ Spec k`
induces no map `CH_0(𝔸¹_k) ⟶ CH_0(Spec k)`: proper pushforward on Chow groups needs properness.
-/

public section

open AlgebraicGeometry CategoryTheory Polynomial

namespace TauCeti.AlgebraicGeometry.Chow.AffineLinePushforwardExample

universe u

variable (k : Type u) [Field k]

/-- `Spec k` over itself through the identity. -/
noncomputable instance instOverSpecSelf : (Spec (.of k)).Over (Spec (.of k)) := ⟨𝟙 _⟩

instance isOver_affineLine : (Spec (.of k[X]) ↘ Spec (.of k)).IsOver (Spec (.of k)) :=
  ⟨Category.comp_id _⟩

instance locallyOfFiniteType_affineLine : LocallyOfFiniteType (Spec (.of k[X]) ↘ Spec (.of k)) :=
  LocallyOfFiniteType.Spec_algebraMap

instance locallyOfFiniteType_self : LocallyOfFiniteType (Spec (.of k) ↘ Spec (.of k)) :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 _))

/-- The zero-cycle `[0]` of the origin of the affine line. -/
noncomputable abbrev originCycle [DecidableEq (Spec (.of k[X]))] :
    cyclesOfDimension (Spec (.of k[X])) 0 :=
  ⟨_, single_mem_cyclesOfDimension_zero
    (TauCeti.AlgebraicGeometry.isClosed_singleton_of_section
      (SpecMap_constantCoeff_comp_SpecMap_algebraMap k)) 1⟩

/-- The pushforward of `[0]` along `𝔸¹_k ⟶ Spec k` has class `1` in `CH_0(Spec k) ≃ ℤ`. -/
theorem equivIntOfUnique_cycleClass_cyclesMap_originCycle [DecidableEq (Spec (.of k[X]))] :
    ChowGroup.equivIntOfUnique (Spec (.of k))
      (cycleClass (cyclesMap k (Spec (.of k[X]) ↘ Spec (.of k)) (originCycle k))) = 1 := by
  classical
  have h : (Spec (.of k[X]) ↘ Spec (.of k)).residueDegree
      (Spec.map (CommRingCat.ofHom (Polynomial.constantCoeff (R := k)))
        (IsLocalRing.closedPoint k)) = 1 :=
    TauCeti.AlgebraicGeometry.residueDegree_eq_one_of_section
      (SpecMap_constantCoeff_comp_SpecMap_algebraMap k) _
  rw [ChowGroup.equivIntOfUnique_cycleClass, cyclesMap_single, one_mul,
    Function.locallyFinsuppWithin.single_apply]
  split_ifs with hc
  · rw [h, Nat.cast_one]
  · exact absurd (Subsingleton.elim _ _) hc

/-- **Pushforward along `𝔸¹_k ⟶ Spec k` does not descend to `CH_0`.** No additive map
`CH_0(𝔸¹_k) ⟶ CH_0(Spec k)` is compatible with the cycle-level pushforward along the structure
morphism: `[0]` is rationally equivalent to zero, but its pushforward is not. -/
theorem not_exists_chowGroup_pushforward :
    ¬ ∃ φ : ChowGroup (Spec (.of k[X])) 0 →+ ChowGroup (Spec (.of k)) 0,
      ∀ α, φ (cycleClass α) =
        cycleClass (cyclesMap k (Spec (.of k[X]) ↘ Spec (.of k)) α) := by
  classical
  rintro ⟨φ, hφ⟩
  have := subsingleton_chowGroup_zero_affineLine (κ := k)
  have h := equivIntOfUnique_cycleClass_cyclesMap_originCycle k
  rw [← hφ, Subsingleton.elim (cycleClass (originCycle k)) 0, map_zero, map_zero] at h
  exact zero_ne_one h

end TauCeti.AlgebraicGeometry.Chow.AffineLinePushforwardExample
