/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoodComponents
public import TauCeti.Combinatorics.PermutationTriple.CycleData

import TauCeti.Topology.Covering.Finite

/-!
# Points of the filled cover

For a map to the thrice-punctured sphere, one point is added for each connected component
over each of the three standard punctured neighborhoods. For a finite cover, the
component-cycle equivalences identify the
number of added points with the sum of the three full cycle counts of its monodromy triple.

These are the new points in the compactification of a finite cover. Their puncture labels
determine where the extended map sends them. A homeomorphism over the thrice-punctured sphere
transports these added points by its induced bijections on connected components, preserving
puncture labels and respecting identities, inverses, and composition. The component bijections
use Mathlib's `Topology.IsCoinducing.connectedComponentsHomeomorph`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §1.2.7 (one added point for each component over a puncture).
-/

public section

noncomputable section

namespace TauCeti

open ThricePuncturedSphere Set

variable {E : Type*} [TopologicalSpace E] (p : E → ThricePuncturedSphere)

/-- The components above the punctures `0`, `1`, and `∞`, respectively. Each component
contributes one point to the filled cover. -/
def FilledPoint : Type _ :=
  ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero) ⊕
    ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne) ⊕
      ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)

namespace FilledPoint

/-- Add a point over the puncture `0` for each component of its punctured preimage. -/
def overZero : ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero) → FilledPoint p :=
  Sum.inl

/-- Add a point over the puncture `1` for each component of its punctured preimage. -/
def overOne : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne) → FilledPoint p :=
  Sum.inr ∘ Sum.inl

/-- Add a point over the puncture `∞` for each component of its punctured preimage. -/
def overInf : ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf) → FilledPoint p :=
  Sum.inr ∘ Sum.inr

/-- The three kinds of added point, as an explicit sum for defining maps out of them. -/
def equivSum : FilledPoint p ≃
    ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero) ⊕
      ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne) ⊕
        ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf) := Equiv.refl _

@[simp]
theorem equivSum_overZero (c) : equivSum p (overZero p c) = Sum.inl c := (rfl)

@[simp]
theorem equivSum_overOne (c) : equivSum p (overOne p c) = Sum.inr (Sum.inl c) := (rfl)

@[simp]
theorem equivSum_overInf (c) : equivSum p (overInf p c) = Sum.inr (Sum.inr c) := (rfl)

/-- The added points as pairs `⟨q, c⟩` of a puncture `q` and a connected component `c` of
`p ⁻¹' D_q*`, so that the three punctures can be handled by one argument. -/
def sigmaEquiv : FilledPoint p ≃ Σ q : Puncture, ConnectedComponents (p ⁻¹' q.neighborhood) :=
  (equivSum p).trans
    { toFun
        | .inl c => ⟨.zero, c⟩
        | .inr (.inl c) => ⟨.one, c⟩
        | .inr (.inr c) => ⟨.inf, c⟩
      invFun
        | ⟨.zero, c⟩ => .inl c
        | ⟨.one, c⟩ => .inr (.inl c)
        | ⟨.inf, c⟩ => .inr (.inr c)
      left_inv := by rintro (c | c | c) <;> rfl
      right_inv := by rintro ⟨_ | _ | _, c⟩ <;> rfl }

@[simp]
theorem sigmaEquiv_overZero (c) : sigmaEquiv p (overZero p c) = ⟨.zero, c⟩ := by
  simp [sigmaEquiv]

@[simp]
theorem sigmaEquiv_overOne (c) : sigmaEquiv p (overOne p c) = ⟨.one, c⟩ := by
  simp [sigmaEquiv]

@[simp]
theorem sigmaEquiv_overInf (c) : sigmaEquiv p (overInf p c) = ⟨.inf, c⟩ := by
  simp [sigmaEquiv]

@[simp]
theorem sigmaEquiv_symm_zero (c) : (sigmaEquiv p).symm ⟨.zero, c⟩ = overZero p c := by
  rfl

@[simp]
theorem sigmaEquiv_symm_one (c) : (sigmaEquiv p).symm ⟨.one, c⟩ = overOne p c := by
  rfl

@[simp]
theorem sigmaEquiv_symm_inf (c) : (sigmaEquiv p).symm ⟨.inf, c⟩ = overInf p c := by
  rfl

theorem overZero_injective : Function.Injective (overZero p) := Sum.inl_injective

theorem overOne_injective : Function.Injective (overOne p) :=
  Sum.inr_injective.comp Sum.inl_injective

theorem overInf_injective : Function.Injective (overInf p) :=
  Sum.inr_injective.comp Sum.inr_injective

/-- The puncture over which an added point lies, with `0`, `1`, and `2` representing
`0`, `1`, and `∞`. -/
def puncture : FilledPoint p → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

@[simp]
theorem puncture_overZero (c) : puncture p (overZero p c) = 0 := (rfl)

@[simp]
theorem puncture_overOne (c) : puncture p (overOne p c) = 1 := (rfl)

@[simp]
theorem puncture_overInf (c) : puncture p (overInf p c) = 2 := (rfl)

/-- Every added point lies over exactly one of the three punctures. -/
theorem cases (y : FilledPoint p) :
    (∃ c, y = overZero p c) ∨ (∃ c, y = overOne p c) ∨
      (∃ c, y = overInf p c) := by
  cases y with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr y =>
    cases y with
    | inl c => exact Or.inr (Or.inl ⟨c, rfl⟩)
    | inr c => exact Or.inr (Or.inr ⟨c, rfl⟩)

/-- The points labelled `0` are exactly those constructed over `0`. -/
theorem puncture_eq_zero_iff (y : FilledPoint p) :
    puncture p y = 0 ↔ ∃ c, y = overZero p c := by
  constructor
  · intro h
    rcases FilledPoint.cases p y with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨c, rfl⟩
    · simp at h
    · simp at h
  · rintro ⟨c, rfl⟩
    simp

/-- The points labelled `1` are exactly those constructed over `1`. -/
theorem puncture_eq_one_iff (y : FilledPoint p) :
    puncture p y = 1 ↔ ∃ c, y = overOne p c := by
  constructor
  · intro h
    rcases FilledPoint.cases p y with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · simp at h
    · exact ⟨c, rfl⟩
    · simp at h
  · rintro ⟨c, rfl⟩
    simp

/-- The points labelled `2` (the puncture `∞`) are exactly those constructed over `∞`. -/
theorem puncture_eq_two_iff (y : FilledPoint p) :
    puncture p y = 2 ↔ ∃ c, y = overInf p c := by
  constructor
  · intro h
    rcases FilledPoint.cases p y with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · simp at h
    · simp at h
    · exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    simp

section Transport

open Function

variable {p} {F G : Type*} [TopologicalSpace F] [TopologicalSpace G]
  {p' : F → ThricePuncturedSphere} {p'' : G → ThricePuncturedSphere}

/-- Restrict an isomorphism over the sphere to the preimage of a standard punctured
neighbourhood. -/
def neighborhoodCongr (h : E ≃ₜ F) (hh : p' ∘ h = p) (q : Puncture) :
    (p ⁻¹' q.neighborhood) ≃ₜ (p' ⁻¹' q.neighborhood) :=
  h.subtype fun x ↦ by simp only [mem_preimage, ← congr_fun hh x, comp_apply]

@[simp]
theorem coe_neighborhoodCongr_apply (h : E ≃ₜ F) (hh : p' ∘ h = p) (q : Puncture)
    (x : p ⁻¹' q.neighborhood) : (neighborhoodCongr h hh q x : F) = h x :=
  (rfl)

@[simp]
theorem coe_neighborhoodCongr_symm_apply (h : E ≃ₜ F) (hh : p' ∘ h = p) (q : Puncture)
    (y : p' ⁻¹' q.neighborhood) : ((neighborhoodCongr h hh q).symm y : E) = h.symm y :=
  (rfl)

/-- An isomorphism over the sphere transports added points by its induced bijection on
components over each puncture. -/
def congr (h : E ≃ₜ F) (hh : p' ∘ h = p) : FilledPoint p ≃ FilledPoint p' :=
  (sigmaEquiv p).trans <| (Equiv.sigmaCongrRight fun q ↦
    ((neighborhoodCongr h hh q).isQuotientMap.isCoinducing.connectedComponentsHomeomorph
      fun y ↦ by
        convert (isConnected_singleton (x := (neighborhoodCongr h hh q).symm y)) using 1
        ext x
        exact (neighborhoodCongr h hh q).eq_symm_apply.symm).toEquiv).trans (sigmaEquiv p').symm

/-- The puncture and component of a transported point. -/
@[simp]
theorem sigmaEquiv_congr (h : E ≃ₜ F) (hh : p' ∘ h = p) (i : FilledPoint p) :
    sigmaEquiv p' (congr h hh i) =
      ⟨(sigmaEquiv p i).1,
        (neighborhoodCongr h hh (sigmaEquiv p i).1).continuous.connectedComponentsMap
          (sigmaEquiv p i).2⟩ := by
  simp [congr, Topology.IsCoinducing.connectedComponentsHomeomorph]

/-- On a component represented by a point, transport is represented by the image point. -/
@[simp]
theorem congr_sigmaEquiv_symm_mk (h : E ≃ₜ F) (hh : p' ∘ h = p) (q : Puncture)
    (x : p ⁻¹' q.neighborhood) :
    congr h hh ((sigmaEquiv p).symm ⟨q, ConnectedComponents.mk x⟩) =
      (sigmaEquiv p').symm ⟨q, ConnectedComponents.mk (neighborhoodCongr h hh q x)⟩ := by
  apply (sigmaEquiv p').injective
  rw [sigmaEquiv_congr, Equiv.apply_symm_apply]
  simp only [Equiv.apply_symm_apply, Continuous.connectedComponentsMap_mk]

/-- Transport does not change the puncture label. -/
@[simp]
theorem puncture_congr (h : E ≃ₜ F) (hh : p' ∘ h = p) (i : FilledPoint p) :
    puncture p' (congr h hh i) = puncture p i := by
  obtain ⟨⟨q, c⟩, rfl⟩ := (sigmaEquiv p).symm.surjective i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hi := congr_sigmaEquiv_symm_mk h hh q x
  rw [hi]
  cases q with
  | zero =>
    simp only [sigmaEquiv_symm_zero]
    exact (puncture_overZero _ _).trans (puncture_overZero _ _).symm
  | one =>
    simp only [sigmaEquiv_symm_one]
    exact (puncture_overOne _ _).trans (puncture_overOne _ _).symm
  | inf =>
    simp only [sigmaEquiv_symm_inf]
    exact (puncture_overInf _ _).trans (puncture_overInf _ _).symm

/-- Identity isomorphisms fix every added point. -/
@[simp]
theorem congr_refl : congr (Homeomorph.refl E) (p := p) (by simp) = Equiv.refl _ := by
  ext i
  obtain ⟨⟨q, c⟩, rfl⟩ := (sigmaEquiv p).symm.surjective i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [congr_sigmaEquiv_symm_mk]
  rfl

/-- Transport along a composite is the composite of the two transports. -/
theorem congr_trans (h : E ≃ₜ F) (hh : p' ∘ h = p) (k : F ≃ₜ G)
    (hk : p'' ∘ k = p') :
    congr (h.trans k) (by funext x; exact (congr_fun hk (h x)).trans (congr_fun hh x)) =
      (congr h hh).trans (congr k hk) := by
  ext i
  obtain ⟨⟨q, c⟩, rfl⟩ := (sigmaEquiv p).symm.surjective i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp only [Equiv.trans_apply, congr_sigmaEquiv_symm_mk]
  rfl

/-- Transport along the inverse isomorphism reverses transport. -/
@[simp]
theorem symm_congr (h : E ≃ₜ F) (hh : p' ∘ h = p) :
    (congr h hh).symm =
      congr h.symm (by funext y; simpa using (congr_fun hh (h.symm y)).symm) := by
  symm
  ext i
  apply (congr h hh).injective
  obtain ⟨⟨q, c⟩, rfl⟩ := (sigmaEquiv p').symm.surjective i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp only [congr_sigmaEquiv_symm_mk, Equiv.apply_symm_apply]
  congr 2
  congr 1
  apply Subtype.ext
  simp

end Transport

variable {n : ℕ}

/-- A numbered finite cover has only finitely many added points. -/
theorem finite (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n) :
    Finite (FilledPoint p) := by
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ0EquivConnectedComponents ν)
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ1EquivConnectedComponents ν)
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσinfEquivConnectedComponents ν)
  rw [FilledPoint]
  infer_instance

variable (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)

/-- The number of points added to a numbered finite cover is the sum of the cycle counts
of its three monodromy permutations. Fixed points count as cycles of length one. -/
theorem natCard_eq_cycleCounts :
    Nat.card (FilledPoint p) =
      (hp.monodromyTriple ν).cycleCounts.1 +
        (hp.monodromyTriple ν).cycleCounts.2.1 +
          (hp.monodromyTriple ν).cycleCounts.2.2 := by
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ0EquivConnectedComponents ν)
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ1EquivConnectedComponents ν)
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσinfEquivConnectedComponents ν)
  have : Finite (FilledPoint p) := finite p hp ν
  simp only [PermutationTriple.cycleCounts_σ0, PermutationTriple.cycleCounts_σ1,
    PermutationTriple.cycleCounts_σinf, orbitCount_def]
  rw [FilledPoint, Nat.card_sum, Nat.card_sum,
    Nat.card_congr (hp.sameCycleQuotientσ0EquivConnectedComponents ν).symm,
    Nat.card_congr (hp.sameCycleQuotientσ1EquivConnectedComponents ν).symm,
    Nat.card_congr (hp.sameCycleQuotientσinfEquivConnectedComponents ν).symm]
  omega

end FilledPoint

open Equiv.Perm FilledPoint

namespace FilledCover

variable {p}

/-- **The added points are the cycles of the monodromy.** For a cover whose fibre over `1/2` is
numbered by `ν`, the components of `p ⁻¹' D_q*` over the punctures `0`, `1` and `∞`, which are
the points added in `FilledCover p`, are the cycles of `σ0`, `σ1` and `σinf` respectively
(`IsCoveringMap.sameCycleQuotientσ0EquivConnectedComponents` and its analogues). -/
def indexEquiv (hp : IsCoveringMap p) {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) :
    FilledPoint p ≃ Quotient (SameCycle.setoid (hp.monodromyTriple ν).σ0) ⊕
      Quotient (SameCycle.setoid (hp.monodromyTriple ν).σ1) ⊕
        Quotient (SameCycle.setoid (hp.monodromyTriple ν).σinf) :=
  (equivSum p).trans <| (hp.sameCycleQuotientσ0EquivConnectedComponents ν).symm.sumCongr <|
    (hp.sameCycleQuotientσ1EquivConnectedComponents ν).symm.sumCongr
      (hp.sameCycleQuotientσinfEquivConnectedComponents ν).symm

@[simp]
theorem indexEquiv_overZero (hp : IsCoveringMap p) {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (c) :
    indexEquiv hp ν (overZero p c) =
      .inl ((hp.sameCycleQuotientσ0EquivConnectedComponents ν).symm c) := by
  simp [indexEquiv]

@[simp]
theorem indexEquiv_overOne (hp : IsCoveringMap p) {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (c) :
    indexEquiv hp ν (overOne p c) =
      .inr (.inl ((hp.sameCycleQuotientσ1EquivConnectedComponents ν).symm c)) := by
  simp [indexEquiv]

@[simp]
theorem indexEquiv_overInf (hp : IsCoveringMap p) {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (c) :
    indexEquiv hp ν (overInf p c) =
      .inr (.inr ((hp.sameCycleQuotientσinfEquivConnectedComponents ν).symm c)) := by
  simp [indexEquiv]

@[simp]
theorem indexEquiv_symm_inl (hp : IsCoveringMap p) {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (a) :
    (indexEquiv hp ν).symm (.inl a) =
      overZero p (hp.sameCycleQuotientσ0EquivConnectedComponents ν a) := by
  rw [Equiv.symm_apply_eq, indexEquiv_overZero, Equiv.symm_apply_apply]

@[simp]
theorem indexEquiv_symm_inr_inl (hp : IsCoveringMap p) {n : ℕ}
    (ν : p ⁻¹' {basePt} ≃ Fin n) (a) :
    (indexEquiv hp ν).symm (.inr (.inl a)) =
      overOne p (hp.sameCycleQuotientσ1EquivConnectedComponents ν a) := by
  rw [Equiv.symm_apply_eq, indexEquiv_overOne, Equiv.symm_apply_apply]

@[simp]
theorem indexEquiv_symm_inr_inr (hp : IsCoveringMap p) {n : ℕ}
    (ν : p ⁻¹' {basePt} ≃ Fin n) (a) :
    (indexEquiv hp ν).symm (.inr (.inr a)) =
      overInf p (hp.sameCycleQuotientσinfEquivConnectedComponents ν a) := by
  rw [Equiv.symm_apply_eq, indexEquiv_overInf, Equiv.symm_apply_apply]

/-- **A finite cover has finitely many added points.** This is `FilledPoint.finite`, applied to a
numbering of the fibre over `1/2`, which is finite as soon as one fibre is. -/
theorem finite_filledPoint (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere}
    (hfin : Finite (p ⁻¹' {z₀})) : Finite (FilledPoint p) :=
  have := finite_fiber_of_finite_fiber hp hfin basePt
  FilledPoint.finite p hp (Finite.equivFin _)

end FilledCover

end TauCeti
