/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral
public import TauCeti.RingTheory.Huber.Pair

import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Emptiness of the adic spectrum

For a Huber pair `(A, A⁺)`, Wedhorn Proposition 7.49(1) characterizes emptiness of the adic
spectrum by triviality of the separated quotient:

```text
Spa(A, A⁺) = ∅  ↔  A / closure {0} = 0.
```

Since `closure {0}` is the kernel of the map to the separated quotient, this is equivalent to
saying that the spectrum is empty exactly when `1` lies in `closure {0}`, that is, when `0` and
`1` are topologically indistinguishable. So a Huber pair carries a continuous valuation unless
its separated quotient is the zero ring.

For a Hausdorff Huber ring the closure of zero is `{0}`, giving the familiar criterion that the
adic spectrum is empty exactly when the ring is trivial. In this form the criteria are the usual
way to produce a point of `Spa(A, A⁺)`, hence a continuous valuation on `A`.

## Main results

* `TauCeti.ValuationSpectrum.spa_eq_empty_iff_one_mem_closure_zero`: the closure-of-zero form.
* `TauCeti.ValuationSpectrum.spa_eq_empty_iff_subsingleton_quotient_closure_zero`: the separated
  quotient form.
* `TauCeti.ValuationSpectrum.spa_eq_empty_iff_subsingleton`: the Hausdorff specialization.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.49(1).

## Provenance

Developed here; nothing is ported. No external formalization is followed.
-/

public section

namespace TauCeti.ValuationSpectrum

open Filter Topology TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- **The converse half of Wedhorn Proposition 7.49(1).** If the adic spectrum of a Huber pair
`(A, A⁺)` is empty, then `1` belongs to the closure of zero, so `0` and `1` are topologically
indistinguishable in `A`.

Emptiness is genuinely a Huber-pair phenomenon: `hplus` says `A⁺` is a ring of integral elements,
and without it a topological ring with no continuous valuation need not have `1 ∈ closure {0}`. -/
theorem one_mem_closure_zero_of_spa_eq_empty (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (hspa : spa Aplus = ∅) :
    (1 : A) ∈ closure ({0} : Set A) := by
  have hall_mem : ∀ a : A, a ∈ Aplus := by
    intro a
    let _ := hplus.isIntegrallyClosedIn
    apply mem_of_forall_vle_one hplus.isOpen
    intro v hv
    rw [hspa] at hv
    exact (Set.notMem_empty v hv).elim
  have hall_powerBounded : ∀ a : A, IsPowerBounded a := fun a ↦
    mem_powerBoundedSubring.mp (hplus.le_powerBoundedSubring (hall_mem a))
  let toPowerBounded : A →+* powerBoundedSubring A :=
    (RingHom.id A).codRestrict (powerBoundedSubring A) fun a ↦
      mem_powerBoundedSubring.mpr (hall_powerBounded a)
  let nilIdeal : Ideal A := (topologicallyNilpotentIdeal A).comap toPowerBounded
  let P : PairOfDefinition A := Classical.choice IsHuberRing.nonempty_pairOfDefinition
  have hopen : IsOpen (P.extendedIdealOfDefinition : Set A) :=
    (P.isOpen_iff_exists_pow_le P.extendedIdealOfDefinition).mpr ⟨1, by simp⟩
  have htop : P.extendedIdealOfDefinition = ⊤ :=
    eq_top_of_spa_eq_empty Aplus hopen hspa
  have hle : P.extendedIdealOfDefinition ≤ nilIdeal := by
    rw [P.extendedIdealOfDefinition_def]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
    simpa [nilIdeal, toPowerBounded] using
      P.isTopologicallyNilpotent_of_mem_idealOfDefinition ha
  have hone_nil : IsTopologicallyNilpotent (1 : A) := by
    have hmem := hle ((Ideal.eq_top_iff_one _).mp htop)
    simpa [nilIdeal, toPowerBounded] using hmem
  rw [← specializes_iff_mem_closure, specializes_comm, specializes_iff_pure]
  have htend : Tendsto (fun _ : ℕ ↦ (1 : A)) atTop (nhds 0) := by
    simpa [IsTopologicallyNilpotent] using hone_nil
  simpa only [Tendsto, Filter.map_const] using htend

/-- **Wedhorn Proposition 7.49(1), closure form.** The adic spectrum of a Huber pair is empty
exactly when `1` belongs to the closure of zero. -/
theorem spa_eq_empty_iff_one_mem_closure_zero (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) :
    spa Aplus = ∅ ↔ (1 : A) ∈ closure ({0} : Set A) :=
  ⟨one_mem_closure_zero_of_spa_eq_empty Aplus hplus,
    spa_eq_empty_of_one_mem_closure_zero Aplus⟩

/-- **Wedhorn Proposition 7.49(1), separated-quotient form.** The adic spectrum of a Huber pair
is empty exactly when the quotient by the closure of zero is the zero ring. -/
theorem spa_eq_empty_iff_subsingleton_quotient_closure_zero (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) :
    spa Aplus = ∅ ↔ Subsingleton (A ⧸ Ideal.closure (⊥ : Ideal A)) := by
  have hmem : (1 : A) ∈ Ideal.closure (⊥ : Ideal A) ↔ (1 : A) ∈ closure ({0} : Set A) := by
    rw [← SetLike.mem_coe, Ideal.coe_closure, Submodule.bot_coe]
  rw [spa_eq_empty_iff_one_mem_closure_zero Aplus hplus, Ideal.Quotient.subsingleton_iff,
    Ideal.eq_top_iff_one, hmem]

/-- For a Hausdorff Huber pair, the adic spectrum is empty exactly when the underlying ring is
trivial. -/
theorem spa_eq_empty_iff_subsingleton [T2Space A] (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) :
    spa Aplus = ∅ ↔ Subsingleton A := by
  rw [spa_eq_empty_iff_one_mem_closure_zero Aplus hplus, isClosed_singleton.closure_eq]
  simp only [Set.mem_singleton_iff]
  simpa only [eq_comm] using (subsingleton_iff_zero_eq_one (M₀ := A))

end TauCeti.ValuationSpectrum

end
