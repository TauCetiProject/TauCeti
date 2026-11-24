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

private lemma isQuotientMap_id_prodMap_intervalπ :
    IsQuotientMap ((ContinuousMap.id X).prodMap intervalπ.{u}) :=
  haveI : Nonempty intervalEndpointPair.{u}.snd := ⟨⟨ULift.up 0, Or.inl rfl⟩⟩
  (isProperMap_id.prodMap intervalπ.{u}.continuous.isProperMap).isClosedMap.isQuotientMap
    ((ContinuousMap.id X).prodMap intervalπ.{u}).continuous <| Function.surjective_id.prodMap <|
      intervalEndpointPair.{u}.surjective_ordinaryPairQuotientπ.comp Equiv.ulift.symm.surjective

/-- **The reduced suspension is the smash product with `I / {0, 1}`** for every pointed
topological space `(X, x₀)`: `ΣX ≃ₜ X ∧ (I / {0, 1})`, with the interval factor on the right. -/
def homeomorphSmashIntervalQuotient :
    ReducedSuspension X x₀ ≃ₜ
      SmashProduct x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint :=
  let q := (ContinuousMap.id X).prodMap intervalπ.{u}
  have hπ {t : I} (ht : t = 0 ∨ t = 1) : intervalπ.{u} t = _ :=
    intervalEndpointPair.{u}.ordinaryPairQuotientπ_map ⟨ULift.up t, ht⟩
  have hq : IsQuotientMap q := isQuotientMap_id_prodMap_intervalπ (X := X)
  have hsurj : Function.Surjective intervalπ.{u} := fun z ↦
    let ⟨⟨_, t⟩, h⟩ := hq.surjective (x₀, z); ⟨t, (Prod.mk.inj h).2⟩
  let fwd : C(ReducedSuspension X x₀,
      SmashProduct x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint) :=
    lift ((SmashProduct.mk x₀ _).comp q) (SmashProduct.basepoint _ _) fun ⟨x, t⟩ hp ↦ by
      rcases mem_reducedSuspensionLocus.1 hp with rfl | rfl | rfl
      · simp [q]
      · simp [q, hπ (Or.inl rfl)]
      · simp [q, hπ (Or.inr rfl)]
  have hfact : Function.FactorsThrough (mk : X × I → ReducedSuspension X x₀) q :=
    fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by
      obtain ⟨rfl, ht⟩ := Prod.mk.inj h
      rcases (intervalEndpointPair.{u}.ordinaryPairQuotientπ_eq_iff _ _).1 ht with h' | ⟨h₁, h₂⟩
      · cases congrArg ULift.down h'; rfl
      · rw [TopPair.range_ofSubset_map] at h₁ h₂
        exact mk_eq_mk_iff.2
          (Or.inr ⟨mem_reducedSuspensionLocus.2 (Or.inr h₁),
            mem_reducedSuspensionLocus.2 (Or.inr h₂)⟩)
  let g := hq.lift (mk : C(X × I, ReducedSuspension X x₀)) hfact
  have hg (x : X) (t : I) : g (x, intervalπ.{u} t) = mk (x, t) :=
    DFunLike.congr_fun (hq.lift_comp (mk : C(X × I, ReducedSuspension X x₀)) hfact) (x, t)
  let inv : C(SmashProduct x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint,
      ReducedSuspension X x₀) :=
    SmashProduct.lift g basepoint
      (fun z ↦ let ⟨t, ht⟩ := hsurj z; ht ▸ (hg x₀ t).trans (mk_basepoint t))
      (fun x ↦ hπ (Or.inl rfl) ▸ (hg x 0).trans (mk_zero x))
  { toFun := fwd, invFun := inv
    left_inv := ind fun x t ↦ by simp [fwd, inv, q, hg]
    right_inv := SmashProduct.ind fun x z ↦ by obtain ⟨t, rfl⟩ := hsurj z; simp [fwd, inv, q, hg]
    continuous_toFun := fwd.continuous, continuous_invFun := inv.continuous }

@[simp]
lemma homeomorphSmashIntervalQuotient_mk (x : X) (t : I) :
    homeomorphSmashIntervalQuotient x₀ (mk (x, t)) =
      SmashProduct.mk x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint
        (x, intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t)) := by
  simp [homeomorphSmashIntervalQuotient, intervalπ]

@[simp]
lemma homeomorphSmashIntervalQuotient_basepoint :
    homeomorphSmashIntervalQuotient x₀ (basepoint : ReducedSuspension X x₀) =
      SmashProduct.basepoint x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint := by
  simp [homeomorphSmashIntervalQuotient]

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
