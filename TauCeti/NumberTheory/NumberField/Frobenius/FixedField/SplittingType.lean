/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Orbit.CycleType
public import TauCeti.NumberTheory.NumberField.FixedField
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.DecompositionOrbits
import TauCeti.GroupTheory.GroupAction.Orbit.Basic

/-!
# Frobenius cycle lengths and splitting in a fixed field

Let `L/K` be a finite Galois extension of number fields and `H` any subgroup of its Galois
group. At a prime unramified in `L`, the full cycle type of an arithmetic Frobenius acting on
`Gal(L/K) ⧸ H` is the multiset of residue degrees of the primes of `L ^ H` above it. Repeated
degrees are retained, and fixed cosets contribute parts equal to one. No normality of `H` is
required.

At a general maximal ideal `p` of `𝓞 K` — possibly ramified in `L` — an arithmetic Frobenius
modulo the inertia subgroup `I(Q) ◁ D(Q)` generates `D(Q) / I(Q)`, so its full cycle type on the
inertia-orbit space `I(Q) \ (Gal(L/K) ⧸ H)` is the multiset of `(D(Q) / I(Q))`-orbit sizes, which
equals the multiset of residue degrees of the primes of `L ^ H` above `p`
(`Ideal.fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg`).

## Main results

* `Ideal.fullCycleType_toPerm_quotient_eq_map_inertiaDeg`: at an unramified prime, the full cycle
  type of an arithmetic Frobenius on `Gal(L/K) ⧸ H` is the multiset of residue degrees in `L ^ H`.
* `Ideal.fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg`: at any maximal ideal
  (ramified or unramified), the full cycle type of an arithmetic Frobenius modulo `I(Q)` on the
  `I(Q)`-orbits of `Gal(L/K) ⧸ H` is the multiset of residue degrees in `L ^ H`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open MulAction IntermediateField NumberField
open scoped NumberField Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

open scoped Classical in
/-- The full cycle type of Frobenius on Galois cosets is the multiset of residue degrees
in the fixed field. This includes fixed points and counts repeated degrees with multiplicity. -/
theorem fullCycleType_toPerm_quotient_eq_map_inertiaDeg
    (p : Ideal (𝓞 K)) [p.IsMaximal] (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver p]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L))
    {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    (toPerm σ : Equiv.Perm ((L ≃ₐ[K] L) ⧸ H)).fullCycleType =
      (Finset.univ : Finset (p.primesOver (𝓞 ↥(fixedField H)))).val.map
        (fun P => P.val.inertiaDeg (𝓞 K)) := by
  have : Q.IsMaximal := IsMaximal.of_liesOver_isMaximal Q p
  rw [fullCycleType_toPerm_eq_map_card_orbit (X := (L ≃ₐ[K] L) ⧸ H) σ,
    zpowers_eq_stabilizer_of_isArithFrobAt Q hσ,
    map_card_orbit_stabilizer_eq_map_ramificationIdx_mul_inertiaDeg p Q H (𝓞 ↥(fixedField H))]
  apply Multiset.map_congr rfl
  intro P _
  -- Lift the fixed-field prime through the coset parametrization so that unramifiedness
  -- descends from a translate of the chosen prime of `L`.
  obtain ⟨x, hx⟩ := primesOverOfCoset_surjective p Q H (𝓞 ↥(fixedField H)) P
  induction x using QuotientGroup.induction_on with | H g => ?_
  have hP : P.val = (g⁻¹ • Q).under (𝓞 ↥(fixedField H)) := by
    rw [← hx, coe_primesOverOfCoset_mk]
  have : Algebra.IsUnramifiedAt (𝓞 K) (g⁻¹ • Q) :=
    (Q.isUnramifiedAt_pointwise_smul_iff g⁻¹).mpr inferInstance
  have : Algebra.IsUnramifiedAt (𝓞 K)
      ((g⁻¹ • Q).under (𝓞 ↥(fixedField H))) :=
    Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) _ (g⁻¹ • Q)
  rw [hP, ramificationIdx_eq_one_of_isUnramifiedAt, one_mul]

open scoped Classical in
/-- **Frobenius cycle lengths on inertia orbits give residue degrees at every prime.** For any
maximal ideal `p` of `𝓞 K` (ramified or unramified), a prime `Q` of `𝓞 L` above `p`, a subgroup
`H ≤ Gal(L/K)`, and an arithmetic Frobenius `σ` at `Q`, the full cycle type of the coset of `σ` in
`D(Q) / I(Q)` acting on the `I(Q)`-orbits of `Gal(L/K) ⧸ H` is the multiset of residue degrees of
the primes of `L ^ H` above `p`. -/
theorem fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg
    (p : Ideal (𝓞 K)) [p.IsMaximal] (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver p]
    (H : Subgroup (L ≃ₐ[K] L)) {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    (toPerm ((⟨σ, hσ.mem_stabilizer⟩ : stabilizer (L ≃ₐ[K] L) Q) :
        stabilizer (L ≃ₐ[K] L) Q ⧸ Q.inertia (stabilizer (L ≃ₐ[K] L) Q)) :
      Equiv.Perm (orbitRel.Quotient (Q.inertia (stabilizer (L ≃ₐ[K] L) Q))
        ((L ≃ₐ[K] L) ⧸ H))).fullCycleType =
      (Finset.univ : Finset (p.primesOver (𝓞 ↥(fixedField H)))).val.map
        (fun P => P.val.inertiaDeg (𝓞 K)) := by
  have : Q.IsMaximal := IsMaximal.of_liesOver_isMaximal Q p
  have : (Q.under (𝓞 K)).IsMaximal := Q.over_def p ▸ ‹p.IsMaximal›
  have : Finite (𝓞 K ⧸ Q.under (𝓞 K)) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ring.ne_bot_of_isMaximal_of_not_isField
      inferInstance (NumberField.RingOfIntegers.not_isField K))
  let _ : Field (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.Quotient.field _
  let _ : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field _
  have : Algebra.IsSeparable (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 L ⧸ Q) := inferInstance
  set D := stabilizer (L ≃ₐ[K] L) Q
  set I := Q.inertia D
  set frob : D ⧸ I := QuotientGroup.mk ⟨σ, hσ.mem_stabilizer⟩
  rw [fullCycleType_toPerm_eq_map_card_orbit frob,
    TauCeti.map_card_orbit_eq_of_orbit_eq
      (orbit_eq_of_eq_top (zpowers_mk_eq_top_of_isArithFrobAt Q hσ)),
    map_card_orbit_quotientInertia_eq_map_inertiaDeg p Q H (𝓞 ↥(fixedField H))]

end Ideal
