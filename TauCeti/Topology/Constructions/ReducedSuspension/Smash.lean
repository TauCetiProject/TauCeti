/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.ReducedSuspension
public import TauCeti.Topology.SmashProduct
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The reduced suspension as a smash product with `I / {0, 1}`

For every pointed topological space `(X, x₀)`, `TauCeti.ReducedSuspension X x₀` is canonically
homeomorphic to `X ∧ (I / {0, 1})` (`TauCeti.ReducedSuspension.homeomorphSmashIntervalQuotient`),
where `I / {0, 1}` is the pointed quotient of `TauCeti.intervalEndpointPair` and the interval
factor sits on the right. No local compactness hypothesis on `X` is needed because the collapse map
`I → I / {0, 1}` from a compact space to a Hausdorff space is proper, so `id_X × π` is a quotient
map for every `X`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0.
* J. P. May, *A Concise Course in Algebraic Topology*, Section 8.2.
-/

public section

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

universe u

namespace TauCeti

/-- The unit interval `I` and its boundary `{0, 1}`, lifted to universe `u` as a `TopPair`. -/
abbrev intervalEndpointPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (ULift.{u} I)) (ULift.down ⁻¹' ({0, 1} : Set I))

instance instCompactSpaceIntervalEndpointPairQuotient :
    CompactSpace intervalEndpointPair.{u}.ordinaryPairQuotient :=
  haveI : CompactSpace intervalEndpointPair.{u}.fst := inferInstanceAs (CompactSpace (ULift.{u} I))
  intervalEndpointPair.{u}.compactSpace_ordinaryPairQuotient

instance instT2SpaceIntervalEndpointPairQuotient :
    T2Space intervalEndpointPair.{u}.ordinaryPairQuotient := by
  have : T3Space intervalEndpointPair.{u}.fst := inferInstanceAs (T3Space (ULift.{u} I))
  refine intervalEndpointPair.{u}.t2Space_ordinaryPairQuotient_of_isClosed ?_
  rw [TopPair.range_ofSubset_map]
  exact (isClosed_singleton.union isClosed_singleton).preimage continuous_uliftDown

namespace ReducedSuspension

variable {X : Type u} [TopologicalSpace X] (x₀ : X)

private def intervalπ : C(I, intervalEndpointPair.{u}.ordinaryPairQuotient) :=
  ⟨fun t ↦ intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t),
    intervalEndpointPair.{u}.ordinaryPairQuotientπ.hom.continuous.comp continuous_uliftUp⟩

@[simp]
private lemma intervalπ_zero :
    intervalπ.{u} 0 = intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint :=
  intervalEndpointPair.{u}.ordinaryPairQuotientπ_map ⟨ULift.up 0, Or.inl rfl⟩

@[simp]
private lemma intervalπ_one :
    intervalπ.{u} 1 = intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint :=
  intervalEndpointPair.{u}.ordinaryPairQuotientπ_map ⟨ULift.up 1, Or.inr rfl⟩

private lemma surjective_intervalπ : Function.Surjective intervalπ.{u} :=
  haveI : Nonempty intervalEndpointPair.{u}.snd := ⟨⟨ULift.up 0, Or.inl rfl⟩⟩
  intervalEndpointPair.{u}.surjective_ordinaryPairQuotientπ.comp Equiv.ulift.symm.surjective

private lemma isQuotientMap_id_prodMap_intervalπ :
    IsQuotientMap ((ContinuousMap.id X).prodMap intervalπ.{u}) :=
  (isProperMap_id.prodMap intervalπ.{u}.continuous.isProperMap).isClosedMap.isQuotientMap
    ((ContinuousMap.id X).prodMap intervalπ.{u}).continuous
    (Function.surjective_id.prodMap surjective_intervalπ)

private lemma factorsThrough_mk_id_prodMap_intervalπ {x₀ : X} :
    Function.FactorsThrough (mk : X × I → ReducedSuspension X x₀)
      ((ContinuousMap.id X).prodMap intervalπ.{u}) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by
    obtain ⟨rfl, ht⟩ := Prod.mk.inj h
    rcases (intervalEndpointPair.{u}.ordinaryPairQuotientπ_eq_iff _ _).1 ht with h' | ⟨h₁, h₂⟩
    · rw [ULift.up.inj h', ContinuousMap.id_apply]
    · rw [TopPair.range_ofSubset_map] at h₁ h₂
      exact mk_eq_mk_iff.2
        (Or.inr ⟨mem_reducedSuspensionLocus.2 (Or.inr h₁),
          mem_reducedSuspensionLocus.2 (Or.inr h₂)⟩)

private def smashIntervalQuotientFwd :
    C(ReducedSuspension X x₀,
      SmashProduct x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint) :=
  lift ((SmashProduct.mk x₀ _).comp ((ContinuousMap.id X).prodMap intervalπ.{u}))
    (SmashProduct.basepoint _ _) fun ⟨_, _⟩ hp ↦ by
      rcases mem_reducedSuspensionLocus.1 hp with rfl | rfl | rfl <;> simp

private def smashIntervalQuotientInv :
    C(SmashProduct x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint,
      ReducedSuspension X x₀) :=
  let g := (isQuotientMap_id_prodMap_intervalπ (X := X)).lift
    (mk : C(X × I, ReducedSuspension X x₀)) factorsThrough_mk_id_prodMap_intervalπ
  have hg (x : X) (t : I) : g (x, intervalπ.{u} t) = mk (x, t) :=
    DFunLike.congr_fun ((isQuotientMap_id_prodMap_intervalπ (X := X)).lift_comp
      (mk : C(X × I, ReducedSuspension X x₀)) factorsThrough_mk_id_prodMap_intervalπ) (x, t)
  SmashProduct.lift g basepoint
    (fun z ↦ let ⟨t, ht⟩ := surjective_intervalπ z; ht ▸ (hg x₀ t).trans (mk_basepoint t))
    (fun x ↦ intervalπ_zero ▸ (hg x 0).trans (mk_zero x))

@[simp]
private lemma smashIntervalQuotientInv_mk_intervalπ (x : X) (t : I) :
    smashIntervalQuotientInv x₀
      (SmashProduct.mk x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint
        (x, intervalπ.{u} t)) = mk (x, t) :=
  (SmashProduct.lift_mk _ _ _ _ x (intervalπ.{u} t)).trans <|
    DFunLike.congr_fun ((isQuotientMap_id_prodMap_intervalπ (X := X)).lift_comp
      (mk : C(X × I, ReducedSuspension X x₀)) factorsThrough_mk_id_prodMap_intervalπ) (x, t)

/-- **The reduced suspension is the smash product with `I / {0, 1}`** for every pointed
topological space `(X, x₀)`: `ΣX ≃ₜ X ∧ (I / {0, 1})`, with the interval factor on the right. -/
def homeomorphSmashIntervalQuotient :
    ReducedSuspension X x₀ ≃ₜ
      SmashProduct x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint where
  toFun := smashIntervalQuotientFwd x₀
  invFun := smashIntervalQuotientInv x₀
  left_inv := ind fun _ _ ↦ by simp [smashIntervalQuotientFwd]
  right_inv := SmashProduct.ind fun _ z ↦ by
    obtain ⟨t, rfl⟩ := surjective_intervalπ z
    simp [smashIntervalQuotientFwd]
  continuous_toFun := (smashIntervalQuotientFwd x₀).continuous
  continuous_invFun := (smashIntervalQuotientInv x₀).continuous

@[simp]
lemma homeomorphSmashIntervalQuotient_mk (x : X) (t : I) :
    homeomorphSmashIntervalQuotient x₀ (mk (x, t)) =
      SmashProduct.mk x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint
        (x, intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t)) := by
  simp [homeomorphSmashIntervalQuotient, smashIntervalQuotientFwd, intervalπ]

@[simp]
lemma homeomorphSmashIntervalQuotient_basepoint :
    homeomorphSmashIntervalQuotient x₀ (basepoint : ReducedSuspension X x₀) =
      SmashProduct.basepoint x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint := by
  simp [homeomorphSmashIntervalQuotient, smashIntervalQuotientFwd]

@[simp]
lemma homeomorphSmashIntervalQuotient_symm_mk_π (x : X) (t : I) :
    (homeomorphSmashIntervalQuotient x₀).symm
      (SmashProduct.mk x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint
        (x, intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t))) =
      mk (x, t) :=
  (homeomorphSmashIntervalQuotient x₀).symm_apply_eq.2
    (homeomorphSmashIntervalQuotient_mk x₀ x t).symm

@[simp]
lemma homeomorphSmashIntervalQuotient_symm_basepoint :
    (homeomorphSmashIntervalQuotient x₀).symm
      (SmashProduct.basepoint x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint) =
      (basepoint : ReducedSuspension X x₀) :=
  (homeomorphSmashIntervalQuotient x₀).symm_apply_eq.2
    (homeomorphSmashIntervalQuotient_basepoint x₀).symm

end ReducedSuspension

end TauCeti

end
