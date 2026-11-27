/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FiniteEtale.FiniteNormal
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.AlgebraicGeometry.FiniteEtale.Completion
import TauCeti.AlgebraicGeometry.FiniteEtale.Hypersurface
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.AdicCompletion.Principal
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.Normal
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Purity

/-!
# Purity for regular local rings

A regular local ring `A` of dimension at least two is pure. Every finite étale cover of its
punctured spectrum extends to a finite étale scheme over `Spec A`.

A regular local ring is a Noetherian integrally closed domain, so purity for `A` is equivalent to
the algebraic statement that every finite normal torsion-free `A`-algebra which is étale at every
prime not lying over the maximal ideal is étale over `A`
(`TauCeti.IsLocalRing.purityHolds_iff_forall_etale`). In dimension two, such an algebra is free
over `A` by miracle flatness, and a finite free algebra over a Noetherian local ring of dimension
at least two which is unramified away from the closed point is étale by the discriminant criterion
(`TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two`).
In higher dimension, extension descends from the maximal-ideal-adic completion. In the completion,
quotienting by a regular parameter reduces the dimension by one. Extension from that hypersurface
section follows from `TauCeti.IsLocalRing.extends_of_extends_quotient_of_isAdicComplete`.

## Main results

* `TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two`: purity holds for a regular local ring
  of dimension two.
* `TauCeti.IsLocalRing.purityHolds_of_two_le_of_le`: the same for every regular local ring of
  dimension between two and some `d ≤ 2`, the form in which purity hypotheses are stated.
* `TauCeti.IsLocalRing.purityHolds_of_isRegularLocalRing`: purity in every dimension at least two.
* `TauCeti.Algebra.etale_of_finiteNormal_of_isRegularLocalRing`: the corresponding algebraic
  purity theorem, with the torsion-freeness hypothesis on the finite algebra.

## References

* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA).
* A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et
  globaux* (SGA 2), Exposé X, Théorème 3.4.
-/

public section

universe u

open IsLocalRing

namespace TauCeti.IsLocalRing

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- **Purity for a two-dimensional regular local ring.** If `A` is a regular local ring of
dimension two, every finite étale cover of the punctured spectrum of `A` extends to a finite étale
scheme over `Spec A`. -/
@[stacks 0BMA "(1) in dimension two"]
theorem purityHolds_of_ringKrullDim_eq_two (hdim : ringKrullDim A = 2) : PurityHolds A := by
  refine (purityHolds_iff_forall_etale hdim.ge).mpr fun B ↦ ?_
  obtain ⟨_, _, hnormal, het⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.property
  exact TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two hdim (fun 𝔮 _ ↦ hnormal 𝔮)
    fun q _ hq ↦ have := het q hq; inferInstance

/-- **Purity in dimension at most two.** For `d ≤ 2`, purity holds for every regular local ring
of dimension at least two and at most `d`: such a ring has dimension exactly two. -/
theorem purityHolds_of_two_le_of_le {d : WithBot ℕ∞} (hd : d ≤ 2) :
    ∀ (B : Type u) [CommRing B] [IsRegularLocalRing B], 2 ≤ ringKrullDim B →
      ringKrullDim B ≤ d → PurityHolds B :=
  fun _ _ _ h₂ hle ↦ purityHolds_of_ringKrullDim_eq_two (le_antisymm (hle.trans hd) h₂)

private theorem purityHolds_of_ringKrullDim_eq_add_two (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      ringKrullDim R = (n + 2 : ℕ) → PurityHolds R := by
  induction n with
  | zero =>
    intro R _ _ hd
    exact purityHolds_of_ringKrullDim_eq_two (by simpa using hd)
  | succ n ih =>
    intro R _ _ hd
    let S := AdicCompletion (maximalIdeal R) R
    have hdim : ringKrullDim S = (n + 2 + 1 : ℕ) := by
      rw [TauCeti.AdicCompletion.ringKrullDim_eq (R := R) le_rfl, hd]
    -- Choose the parameter after completion, so the induction applies to its quotient directly.
    have hpos : 0 < ringKrullDim S := by
      rw [hdim]
      exact_mod_cast Nat.zero_lt_succ (n + 2)
    obtain ⟨f, hf, hf₂, -⟩ := exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes hpos
    have hfreg : f ∈ nonZeroDivisors S :=
      mem_nonZeroDivisors_of_ne_zero (by rintro rfl; exact hf₂ (zero_mem _))
    have := TauCeti.IsRegularLocalRing.quotient_span_singleton hf hf₂
    have hdim₀ : ringKrullDim (S ⧸ Ideal.span {f}) = (n + 2 : ℕ) := by
      have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        hfreg hf
      rwa [hdim, Nat.cast_succ, ENat.WithBot.add_one_cancel] at h
    have hdepth : 2 ≤ depth (ModuleCat.of R R) := by
      apply WithBot.coe_le_coe.mp
      rw [TauCeti.IsRegularLocalRing.depth_eq_ringKrullDim, hd]
      exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (by omega : (2 : ℕ) ≤ n.succ + 2))
    have hdepth₀ : 2 ≤ depth (ModuleCat.of (S ⧸ Ideal.span {f}) (S ⧸ Ideal.span {f})) := by
      apply WithBot.coe_le_coe.mp
      rw [TauCeti.IsRegularLocalRing.depth_eq_ringKrullDim, hdim₀]
      exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr (by omega : (2 : ℕ) ≤ n + 2))
    have : IsAdicComplete (Ideal.span {f}) S :=
      IsAdicComplete.span_singleton_of_mem (I := maximalIdeal S) hf
    refine (purityHolds_iff R).mpr fun V ↦
      (extends_iff_completion_extends_of_two_le_depth hdepth V).mpr ?_
    apply extends_of_extends_quotient_of_isAdicComplete
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hfreg) hdepth₀
    exact (purityHolds_iff _).mp (ih _ hdim₀) _

/-- **Purity for regular local rings.** If `A` is regular local of dimension at least two,
every finite étale cover of its punctured spectrum extends to a finite étale cover of `Spec A`. -/
@[stacks 0BMA "(1)"]
theorem purityHolds_of_isRegularLocalRing (hdim : 2 ≤ ringKrullDim A) : PurityHolds A := by
  have hdim_eq := _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
  have hdim_nat : 2 ≤ (maximalIdeal A).spanFinrank := by
    rw [← hdim_eq] at hdim
    exact_mod_cast hdim
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hdim_nat
  apply purityHolds_of_ringKrullDim_eq_add_two n A
  rw [← hdim_eq, hn, Nat.add_comm 2 n]

end TauCeti.IsLocalRing

/-- A finite torsion-free algebra over a regular local ring of dimension at least two is étale
if its localizations at maximal ideals are normal domains and it is étale away from the closed
point of the base. Torsion freeness supplies the missing hypothesis in Stacks, Lemma 58.21.3 (2). -/
@[stacks 0BMA "(2), with B torsion free over A"]
theorem TauCeti.Algebra.etale_of_finiteNormal_of_isRegularLocalRing {A B : Type u}
    [CommRing A] [IsRegularLocalRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] (hdim : 2 ≤ ringKrullDim A)
    (hnormal : ∀ (q : Ideal B) [q.IsMaximal],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (hetale : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A → Algebra.IsEtaleAt A q) :
    Algebra.Etale A B :=
  TauCeti.Algebra.etale_of_finiteNormal_of_purityHolds
    (TauCeti.IsLocalRing.purityHolds_of_isRegularLocalRing hdim) hdim hnormal hetale
