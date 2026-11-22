/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Support
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral
import TauCeti.RingTheory.Huber.LocalizationTopology.Valuation

/-!
# The geometric universal property of a rational localisation

The coordinate ring `A⟨T/s⟩` of a rational subset has an *algebraic* universal property: a
continuous `φ : A → B` into a complete `B` extends across `ρ : A → A⟨T/s⟩` as soon as `φ s` is a
unit and every fraction `φ t / φ s` is power-bounded
(`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_locTopology`).
Wedhorn's Lemma 8.1 replaces those two algebraic conditions by a single *geometric* one — that
`Spa(φ)` factors through the rational subset `U = R(T/s)`. This file carries that replacement out
in two shapes: one with the unit `φ s` kept as a hypothesis, for a caller that has it in hand, and
Wedhorn's own, in which the unit is *derived* from the geometric condition.

Wedhorn's proof has three steps, and all three are discharged here:

> As `Spa(φ)` factors through `U`, we have `|φ(t)|_w ≤ |φ(s)|_w ≠ 0` for all `w ∈ Spa B` and for
> all `t ∈ T`. This implies `φ(s) ∈ B^×` by Proposition 7.52. Moreover, for all `w ∈ Spa B` we
> have `|φ(t)/φ(s)|_w ≤ 1`. This implies `φ(t)/φ(s) ∈ B⁺` by Proposition 7.52. Thus the claim
> follows from the universal property of `A → A⟨T/s⟩`.

The step `φ s ∈ B^×` is Wedhorn's Proposition 7.52(2), which is on hand for a complete Hausdorff
Huber pair as `TauCeti.ValuationSpectrum.isUnit_iff_forall_mem_spa_notMem_supp`; the step
`|φ(t)/φ(s)|_w ≤ 1` is a division by that unit. The step from there to `φ(t)/φ(s) ∈ B⁺` is
Proposition 7.52(1), available for a ring of integral elements as
`TauCeti.Huber.IsRingOfIntegralElements.mem_of_forall_vle_one`, which the assembly consumes at its
one use site. All three steps are therefore proved, and each asks of the target only what a
complete affinoid ring supplies.

The other half of Lemma 8.1, that `Spa ρ : Spa A⟨T/s⟩ → Spa A` factors through `U`, is already
`TauCeti.ValuationSpectrum.spaComapLoc_mem_rationalSubset`; it is not repeated here.

## Main results

All five are in the `TauCeti.ValuationSpectrum` namespace.

* `isUnit_of_forall_comap_mem_rationalSubset` : if every point of `Spa (B, B⁺)` pulls back into
  `R(T/s)`, the denominator becomes a unit in `B`.
* `vle_one_of_comap_mem_rationalSubset` : at a point whose pullback lies in `R(T/s)`, the
  fraction `φ t / φ s` is sub-unit.
* `existsUnique_continuous_ringHom_of_isUnit_of_forall_comap_mem_rationalSubset` : the geometric
  universal property — a continuous `φ : A → B` whose `Spa(φ)` factors through `R(T/s)` and whose
  `φ s` is a unit extends across `A → A⟨T/s⟩` in exactly one continuous way.
* `existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset` : **Wedhorn's Lemma 8.1** —
  the same, with the unit obtained from the geometric condition by step 1.
* `comap_mem_spa_completedPlusSubring` : a continuous valuation pulled back along a continuous
  map out of `A⟨T/s⟩` is a point of `Spa (A⟨T/s⟩, A_U⁺)` once it is sub-unit on the image of `A⁺`
  and its pullback to `A` lies in `R(T/s)`.

## The hypotheses on the target

Step 1 asks `(B, B⁺)` to be a complete Hausdorff Huber pair, which is what Wedhorn's *complete
affinoid ring* is, so it is free at the generality he states. Deriving the unit from an *open*
maximal ideal of `B` instead — the route of
`TauCeti.ValuationSpectrum.isUnit_of_forall_not_vle_zero` — is no option for the targets §8 is
about: by `TauCeti.Huber.IsTateRing.isOpen_iff_eq_top` an ideal of a Tate ring is open exactly
when it is `⊤`, so a nonzero Tate ring has no open maximal ideal at all, and the affinoid rings
§8 works with are Tate in its principal case.

## What this file consumes

Wedhorn's Proposition 7.52(1) — that `f ∈ B⁺` as soon as `|f(x)| ≤ 1` for all `x ∈ Spa B` — is
what turns the sub-unit bound on `φ t / φ s` into membership in `B⁺`. It is supplied, for a ring
of integral elements, by `TauCeti.Huber.IsRingOfIntegralElements.mem_of_forall_vle_one`; its
general form `TauCeti.ValuationSpectrum.mem_of_forall_vle_one` asks three things of the target:

* `IsOpen (Bplus : Set B)`,
* `[IsIntegrallyClosedIn Bplus B]`,
* `[IsHuberRing B]`.

The first two, together with `B⁺ ⊆ B°`, are the three fields of
`TauCeti.Huber.IsRingOfIntegralElements Bplus`, so the assembly below asks for that one bundled
hypothesis rather than spelling them out; with `[IsHuberRing B]` they are exactly a Huber pair on
`B`, and a consumer holding a `TauCeti.Huber.Pair B` passes its `isRingOfIntegralElements`
field. `[IsHuberRing B]` is not a restriction added to make the proof go
through: Wedhorn states Lemma 8.1 for a
continuous homomorphism into a *complete affinoid ring*, and an affinoid ring is a Huber pair.

Nonarchimedean-ness of `B` is used throughout but is not assumed: with `[IsHuberRing B]` already
present, `TauCeti.Huber.IsHuberRing.toNonarchimedeanRing` derives it from `[IsTopologicalRing B]`.
The target is therefore presented the same way as the source `A` in the same signature —
`[IsTopologicalRing _]` carrying the topology and `[IsHuberRing _]` (or a pair of definition)
carrying the Huber structure.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1, whose statement and
  three-step proof are quoted above, together with Propositions 7.18 and 7.52.

## Provenance

Developed here; nothing is ported. AINTLIB reaches the corresponding statement by a different
route — a height-one reduction pairing Wedhorn's Propositions 7.18 and 7.41 — which is not
followed.
-/

public section

open TauCeti.Localization

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

section Steps

variable {B : Type*} [CommRing B]

/-- **The denominator becomes a unit.** If every point of `Spa (B, B⁺)` pulls back into the
rational subset `R(T/s)`, then no point of `Spa (B, B⁺)` vanishes on `φ s`, so `φ s` is a unit
by Wedhorn's Proposition 7.52(2).

This is the first step of Wedhorn's Lemma 8.1. The form of 7.52(2) it uses,
`isUnit_iff_forall_mem_spa_notMem_supp`, asks the target to be a complete Hausdorff Huber pair,
which is what Wedhorn's *complete affinoid ring* supplies. -/
theorem isUnit_of_forall_comap_mem_rationalSubset [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [T2Space B] [CompleteSpace B] [Huber.IsHuberRing B] {φ : A →+* B}
    {Aplus : Subring A} {Bplus : Subring B} (T : Finset A)
    (hB : Huber.IsRingOfIntegralElements Bplus) {s : A}
    (hfac : ∀ w ∈ spa Bplus, comap φ w ∈ rationalSubset Aplus T s) :
    IsUnit (φ s) := by
  refine (isUnit_iff_forall_mem_spa_notMem_supp Bplus hB (φ s)).mpr fun w hw hsupp ↦ ?_
  refine ((mem_rationalSubset_iff Aplus T s _).mp (hfac w hw)).2.2 ?_
  rw [comap_vle, map_zero]
  exact (mem_supp_iff w (φ s)).mp hsupp

/-- **The fractions are sub-unit.** At a point of `Spv B` whose pullback lies in `R(T/s)`, the
fraction `φ t / φ s` has value at most `1`.

This is the second step of Wedhorn's Lemma 8.1: the pullback condition gives `|φ t|_w ≤ |φ s|_w`,
and dividing by the unit `φ s` — which `isUnit_of_forall_comap_mem_rationalSubset` supplies —
turns that into `|φ t / φ s|_w ≤ 1`. Nothing beyond the pullback condition is used, so the unit
enters as an argument rather than being re-derived.

The pullback condition is taken at the single point `w` where it is spent, not as a hypothesis
quantified over `spa B⁺`: the proof looks at no other point, and `Bplus` then plays no part in
the statement at all, so no topology on `B` is needed either. The assembly holds the quantified
form and passes `hfac w hw`. -/
theorem vle_one_of_comap_mem_rationalSubset {φ : A →+* B} {Aplus : Subring A}
    {T : Finset A} {s : A} (hs : IsUnit (φ s)) {w : Spv B}
    (hmem : comap φ w ∈ rationalSubset Aplus T s) {t : A} (ht : t ∈ T) :
    w.toValuativeRel.vle (φ t * ↑hs.unit⁻¹) 1 := by
  have hvle : w.toValuativeRel.vle (φ t) (φ s) := by
    have h := ((mem_rationalSubset_iff Aplus T s _).mp hmem).2.1 t ht
    rwa [comap_vle] at h
  have h := w.toValuativeRel.mul_vle_mul_left hvle (↑hs.unit⁻¹ : B)
  rwa [hs.mul_val_inv] at h

end Steps

/-! ### Lemma 8.1: the geometric universal property

The assembly. `S` is an algebraic localisation of `A` away from `s` carrying the localisation
topology, so that `A⟨T/s⟩` is its separated completion, and the three `letI`s naming the
uniformity and its two companions are the ones every statement about `A⟨T/s⟩` carries. -/

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

/-- **The geometric universal property of `A⟨T/s⟩`, with `φ s` a unit**: a continuous
`φ : A → B` into a complete `(B, B⁺)` whose `Spa(φ)` factors through the rational subset
`R(T/s)`, and for which `φ s` is a unit, extends across the structure map `ρ : A → A⟨T/s⟩` in
exactly one continuous way.

Of the two algebraic conditions of
`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_locTopology`, the
first is the hypothesis `hs`; the second is discharged from the geometric one: each fraction
`φ t / φ s` is sub-unit at every point of `Spa (B, B⁺)` by
`vle_one_of_comap_mem_rationalSubset`, hence lies in `B⁺` and so is power-bounded.

The passage from "sub-unit at every point of `Spa (B, B⁺)`" to "in `B⁺`" is Wedhorn's
Proposition 7.52(1), whose hypotheses on the target are openness of `B⁺`,
`[IsIntegrallyClosedIn Bplus B]` and `[IsHuberRing B]`; it is applied through
`IsRingOfIntegralElements.mem_of_forall_vle_one`. The proof also uses `B⁺ ⊆ B°`. Those three
conditions on `B⁺` are exactly the fields of `IsRingOfIntegralElements`, so they are carried by
the single hypothesis `hB` rather than spelled out one by one.

Asking `B` to be Huber is not a restriction added here: Wedhorn states Lemma 8.1 for a continuous
homomorphism into a *complete affinoid ring*, and an affinoid ring is a Huber pair.

The unit `φ s` is a hypothesis rather than something derived, so that a caller already holding it
need not go through step 1;
`isUnit_of_forall_comap_mem_rationalSubset` is that step, and the corollary below is the two
together, which is Wedhorn's own statement.

These are properties of the pair `(B, B⁺)` alone: they mention neither `φ` nor `T` nor `s`. The
per-morphism algebraic conditions of the universal property are replaced by the single geometric
condition `hfac`, at the cost of hypotheses on the target that are checked once. -/
theorem existsUnique_continuous_ringHom_of_isUnit_of_forall_comap_mem_rationalSubset
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsHuberRing B] [CompleteSpace B] [T0Space B] (Bplus : Subring B)
    (hB : IsRingOfIntegralElements Bplus) {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hs : IsUnit (φ s))
    (hfac : ∀ w ∈ spa Bplus, comap φ w ∈ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∃! g : UniformSpace.Completion S →+* B,
      Continuous g ∧ g.comp (toCompletionLoc P T s S hden) = φ :=
  existsUnique_continuous_ringHom_completion_locTopology P T s S hden hφ hs fun _ ht ↦
    hB.isPowerBounded_of_mem <| hB.mem_of_forall_vle_one fun w hw ↦
      vle_one_of_comap_mem_rationalSubset hs (hfac w hw) ht

/-- **Wedhorn's Lemma 8.1.** The geometric universal property in the shape Wedhorn states it: the
unit `φ s` is not assumed but derived from the factorisation, which is step 1. -/
theorem existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset [IsTopologicalRing A]
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsHuberRing B] [CompleteSpace B] [T0Space B] (Bplus : Subring B)
    (hB : IsRingOfIntegralElements Bplus) {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hfac : ∀ w ∈ spa Bplus, comap φ w ∈ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∃! g : UniformSpace.Completion S →+* B,
      Continuous g ∧ g.comp (toCompletionLoc P T s S hden) = φ :=
  existsUnique_continuous_ringHom_of_isUnit_of_forall_comap_mem_rationalSubset P Aplus T s S hden
    Bplus hB hφ (isUnit_of_forall_comap_mem_rationalSubset T hB hfac) hfac

-- **The plus ring of the localisation is sub-unit.** Let `w` be a point of `Spv B` that is
-- sub-unit on the image of `A⁺` under `φ` and on the images `ψ (t/s)` of the fractions, and let
-- `ψ : Aₛ → B` restrict along `algebraMap A Aₛ` to `φ`. Then `w` is sub-unit on the image under
-- `ψ` of the plus ring of `Aₛ` — the integral closure of `A⁺[t₁/s, …, tₙ/s]`.
--
-- The bound on the fractions is asked of `ψ` directly, so no unit hypothesis on `φ s` is needed;
-- a caller holding the bound as `φ t * (φ s)⁻¹` converts it with
-- `TauCeti.Localization.map_divBy_eq_mul_inv`.
--
-- `B` carries no topology and no `B⁺` appears: the two bounds enter as hypotheses on the single
-- point `w`, not as a quantifier over `spa B⁺`.
omit [TopologicalSpace A] in
private theorem vle_one_of_mem_integralClosure_adjoin_plus {B : Type*} [CommRing B]
    (Aplus : Subring A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S] {φ : A →+* B} {ψ : S →+* B}
    (hψ : ∀ a : A, ψ (algebraMap A S a) = φ a) {w : Spv B}
    (hA : ∀ a ∈ Aplus, w.toValuativeRel.vle (φ a) 1)
    (hT : ∀ t ∈ T, w.toValuativeRel.vle (ψ (divBy (t : A) s : S)) 1) {x : S}
    (hx : x ∈ integralClosure
      ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))) S) :
    w.toValuativeRel.vle (ψ x) 1 := by
  have key (y : S) : w.valuation.comap ψ y ≤ 1 ↔ w.toValuativeRel.vle (ψ y) 1 := by
    rw [Valuation.comap_apply, ← map_one w.valuation, valuation_le_iff]
  exact (key x).mp (Huber.le_one_of_mem_integralClosure_adjoin_plus S T s Aplus
    (fun a ha ↦ (key _).mpr (hψ a ▸ hA a ha))
    (fun t ht ↦ (key _).mpr (hT t ht)) hx)

/-- **A criterion for a pullback to lie in `Spa (A⟨T/s⟩, A_U⁺)`.** Let `σ : A⟨T/s⟩ → B` be a
continuous ring homomorphism and `w` a continuous valuation on `B` whose pullback to `A` along
`σ ∘ ρ`, where `ρ : A → A⟨T/s⟩` is the structure map, lies in `R(T/s)`. Then the pullback of `w`
along `σ` is a point of `Spa (A⟨T/s⟩, A_U⁺)`. The sub-unit condition on `A_U⁺` itself is not
asked: it follows from the sub-unit condition on `A⁺` and on the fractions `t/s`, both of which
hold because the pullback lies in `R(T/s)`. -/
theorem comap_mem_spa_completedPlusSubring [IsTopologicalRing A] (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) {B : Type*} [CommRing B]
    [TopologicalSpace B] :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (σ : UniformSpace.Completion S →+* B), Continuous σ → ∀ {w : Spv B}, w.IsContinuous →
      comap (σ.comp (toCompletionLoc P T s S hden)) w ∈ rationalSubset Aplus T s →
      comap σ w ∈ spa (completedPlusSubring P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro σ hσ w hw hfac
  have hψ : ∀ a : A, (σ.comp UniformSpace.Completion.coeRingHom) (algebraMap A S a) =
      (σ.comp (toCompletionLoc P T s S hden)) a := fun a ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, UniformSpace.Completion.coe_coeRingHom,
      ← toCompletionLoc_apply P T s S hden]
  -- `s` is already inverted in `S` by the `IsLocalization.Away` binder, so its image is a unit
  have hu : IsUnit ((σ.comp (toCompletionLoc P T s S hden)) s) :=
    hψ s ▸ (IsLocalization.Away.algebraMap_isUnit (S := S) s).map _
  have hA : ∀ a ∈ Aplus, w.toValuativeRel.vle (σ (toCompletionLoc P T s S hden a)) 1 :=
      fun a ha ↦ by
    simpa only [comap_vle, map_one, RingHom.comp_apply] using
      ((mem_spa_iff _ _).mp ((mem_rationalSubset_iff Aplus T s _).mp hfac).1).2 a ha
  have hcont := hw.comap hσ
  have hsub : completedPlusSubring P Aplus T s S hden =
      ((integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring.map
          UniformSpace.Completion.coeRingHom).topologicalClosure :=
    SetLike.coe_injective <| by
      rw [coe_completedPlusSubring, UniformSpace.Completion.coe_topologicalClosure_map_coeRingHom,
        Subalgebra.coe_toSubring]
  rw [hsub, spa_topologicalClosure,
    mem_spa_map_iff UniformSpace.Completion.continuous_coeRingHom _ hcont]
  refine (mem_spa_iff _ _).mpr
    ⟨hcont.comap UniformSpace.Completion.continuous_coeRingHom, fun x hx ↦ ?_⟩
  simpa only [comap_vle, map_one, RingHom.comp_apply] using
    vle_one_of_mem_integralClosure_adjoin_plus Aplus T s S hψ hA
      (fun t ht ↦ (map_divBy_eq_mul_inv (S := S) t s hψ).symm ▸
        vle_one_of_comap_mem_rationalSubset hu hfac ht) hx

end TauCeti.ValuationSpectrum
