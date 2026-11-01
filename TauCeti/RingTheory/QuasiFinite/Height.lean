/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.ZariskisMainTheorem
public import TauCeti.RingTheory.KrullDimension.Integral
public import TauCeti.RingTheory.QuasiFinite.Basic

/-!
# Heights of primes along quasi-finite extensions over a normal base

Let `S` be a finite type `R`-algebra which is a domain containing `R`. At a prime `q` of `S` at
which `S` is quasi-finite over `R`, lying over a prime `p` of `R` with `R_p` integrally closed,
the heights of `q` and `p` agree. Geometrically: a quasi-finite dominant morphism of integral
schemes onto a scheme which is normal at the image point preserves the dimension of the local
rings. This is the dimension equality behind the purity of the branch locus, where the local ring
of the target is regular, hence normal.

For the equality, Zariski's main theorem
(`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`, Stacks 00Q9) gives a
module-finite subalgebra `S'` of `S` and `r ∈ S' ∖ q` with `S'[1/r] = S[1/r]`, so `q` has the same
height as `q ∩ S'`. The finite extension `R ⊆ S'` preserves heights over a normal `R_p`
(`Ideal.height_eq_height_of_isIntegral_of_isIntegrallyClosed`, through going down, Stacks 00H8).
No Noetherian hypothesis is needed.

Over a Noetherian base with `S_q` Noetherian (for instance, `S` of finite type), the inequality
`ht q ≤ ht p` needs neither normality nor injectivity: the fibre `S_q ⧸ p S_q` is Artinian, so
Mathlib's `Ideal.height_le_height_add_of_liesOver` (Stacks 00OM) applies with a fibre term zero.

## Main results

* `Ideal.height_le_height_of_quasiFiniteAt`: over a Noetherian ring, a prime `q` at which the
  algebra is quasi-finite, with `S_q` Noetherian, has height at most that of the prime below it.
* `Ideal.height_eq_height_of_quasiFiniteAt`: equality, for a domain containing `R` and a normal
  local ring `R_p`, over an arbitrary base.

## References

* [Stacks Project, Tag 00Q9](https://stacks.math.columbia.edu/tag/00Q9), Zariski's main theorem.
* [Stacks Project, Tag 00H8](https://stacks.math.columbia.edu/tag/00H8), going down for integral
  extensions of a normal domain.
* [Stacks Project, Tag 00OM](https://stacks.math.columbia.edu/tag/00OM), heights along an algebra
  and its fibres.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Let `S` be an algebra over a Noetherian ring `R` and `q` a prime of `S` over `p` at which `S`
is quasi-finite over `R`, with `S_q` Noetherian (for instance, `S` of finite type over `R`). Then
the height of `q` is at most the height of `p`. -/
theorem height_le_height_of_quasiFiniteAt [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    [IsNoetherianRing (Localization.AtPrime q)] : q.height ≤ p.height := by
  obtain rfl := q.over_def p
  let Sq := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal Sq
  let J := (q.under R).map (algebraMap R Sq)
  have hm : m.under R = q.under R := by
    rw [← under_under (B := S), Localization.AtPrime.under_maximalIdeal]
  have : m.LiesOver (q.under R) := ⟨hm.symm⟩
  have hJ : J ≤ m := by rw [map_le_iff_le_comap, ← under_def, hm]
  have h := height_le_height_add_of_liesOver (q.under R) m
  -- The fibre `S_q ⧸ (q.under R) S_q` is Artinian, so the image of `m` in it has height zero.
  have : (m.map (Ideal.Quotient.mk J)).IsPrime :=
    map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [mk_ker])
  have h0 : (m.map (Ideal.Quotient.mk J)).height = 0 := by
    have := (height_le_ringKrullDim_of_isPrime (I := m.map (Ideal.Quotient.mk J))).trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 (Sq ⧸ J)))
    exact nonpos_iff_eq_zero.mp (by exact_mod_cast this)
  rwa [h0, add_zero, ← IsLocalization.height_under q.primeCompl,
    Localization.AtPrime.under_maximalIdeal] at h

/-- Let `S` be a finite type `R`-algebra which is a domain containing `R`, and `q` a prime of `S`
over `p` at which `S` is quasi-finite over `R`. If `R_p` is integrally closed, then `q` and `p`
have the same height. No Noetherian hypothesis is needed. -/
theorem height_eq_height_of_quasiFiniteAt [Algebra.FiniteType R S]
    [IsDomain S] [FaithfulSMul R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra.QuasiFiniteAt R q] [IsIntegrallyClosed (Localization.AtPrime p)] :
    q.height = p.height := by
  obtain rfl := q.over_def p
  obtain ⟨S', hS', r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) q
  have : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'⟩
  have : FaithfulSMul R S' := (faithfulSMul_iff_algebraMap_injective R S').mpr fun a b h ↦
    FaithfulSMul.algebraMap_injective R S (congrArg Subtype.val h)
  have : (q.under S').LiesOver (q.under R) := ⟨(under_under (B := S') q).symm⟩
  rw [← height_eq_height_of_isIntegral_of_isIntegrallyClosed (q.under R) (q.under S')]
  -- `S'[1/r] ≃ S[1/r]` identifies the localizations of `q'` and `q` away from `r`.
  let e := RingEquiv.ofBijective _ hbij
  have hdisj : Disjoint (Submonoid.powers (S'.val.toRingHom r) : Set S) q :=
    (disjoint_powers_iff_notMem_of_isPrime _).mpr hrq
  let Q := q.map (algebraMap S (Localization.Away (S'.val.toRingHom r)))
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ q ‹_› hdisj
  have hcomp : (e : Localization.Away r →+* Localization.Away (S'.val.toRingHom r)).comp
      (algebraMap S' (Localization.Away r)) =
      (algebraMap S _).comp S'.val.toRingHom :=
    RingHom.ext fun x ↦ IsLocalization.map_eq (M := Submonoid.powers r)
      (S := Localization.Away r) (T := Submonoid.powers (S'.val.toRingHom r))
      (Q := Localization.Away (S'.val.toRingHom r))
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)) x
  -- Contracting `Q` along either side of `hcomp` gives the same ideal of `S'`.
  have hQS : (Q.comap e).under S' = (Q.under S).under S' := by
    simp only [under_def, ← comap_coe e, comap_comap, hcomp]
    rfl
  have hQ' : (Q.comap e).under S' = q.under S' := by
    rw [hQS, IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hdisj]
  rw [← hQ', IsLocalization.height_under (Submonoid.powers r), RingEquiv.height_comap,
    IsLocalization.height_map_of_disjoint _ q hdisj]

end Ideal
