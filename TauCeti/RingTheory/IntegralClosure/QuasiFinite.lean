/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ZariskisMainTheorem
public import TauCeti.RingTheory.Japanese

import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic
import TauCeti.RingTheory.Localization.Finiteness

/-!
# Finite integral closures over quasi-finite algebras

Let `P → A → B` be ring maps with `A` of finite type over `P`. If the integral closure of `P` in
`B` is a finite `P`-module, then the integral closure of `A` in `B` is finite over `A` near every
prime at which `A` is quasi-finite over `P`, and it is a finite `A`-module when `A` is
quasi-finite over `P` everywhere.

The input is Zariski's main theorem in Mathlib's algebraic form
(`Algebra.ZariskisMainProperty.of_finiteType`): near a prime `q` at which `A` is quasi-finite
over `P`, there is an `r ∉ q` such that every element of `A` times a power of `r` is integral over
`P`. Scaling the roots of an integral equation, every element of `B` integral over `A` then becomes
integral over `P` after multiplication by a power of `r`, so that after inverting `r` the integral
closure of `A` in `B` is spanned by that of `P`.

When `P` is a Noetherian N-1 domain, for instance a polynomial ring over a discrete valuation
ring, the finiteness of the integral closure of `P` in `B` holds as soon as `B` is torsion-free
over `P` with finite étale generic fibre
(`TauCeti.Ring.finite_integralClosure_of_isTorsionFree_of_etale`). No excellence or Japanese
hypothesis enters. This is the route to finiteness of the normalization of a flat finite type
algebra `A` over a possibly non-excellent discrete valuation ring `R` in its generic fibre
`B = A[1/π]` when `B` is smooth of relative dimension one over the fraction field `K`. Applying
these results requires constructing, near each point of the special fibre, a coordinate `x ∈ A`
such that `A` is quasi-finite over `R[x]`, `B` is torsion-free over `R[x]`, and
`K(x) ⊗[R[x]] B` is étale over `K(x)`. This coordinate construction is not supplied here.

## Main results

* `Algebra.QuasiFiniteAt.exists_notMem_finite_localizedModule_integralClosure`: if `A` is of finite
  type over `P` and quasi-finite at a prime `q`, and the integral closure of `P` in `B` is finite,
  then the integral closure of `A` in `B` becomes finite over `A_r` after inverting some `r ∉ q`.
* `TauCeti.finite_integralClosure_of_quasiFinite`: if moreover `A` is quasi-finite over `P`, the
  integral closure of `A` in `B` is a finite `A`-module.
* `TauCeti.finite_integralClosure_of_quasiFinite_of_etale`: the case of a Noetherian N-1 domain
  `P` and a torsion-free `P`-algebra `B` with finite étale generic fibre.

## References

* [Stacks Project, Tag 00Q9](https://stacks.math.columbia.edu/tag/00Q9), Zariski's main theorem
  in the algebraic form used here.
* [Stacks Project, Section 10.161 (0BI1)](https://stacks.math.columbia.edu/tag/0BI1), for
  finiteness of integral closures.
-/

public section

variable {P A B : Type*} [CommRing P] [CommRing A] [CommRing B] [Algebra P A] [Algebra A B]
  [Algebra P B] [IsScalarTower P A B]

/-- **The integral closure over a quasi-finite algebra is finite near a point.** Let `A` be a
finite type `P`-algebra that is quasi-finite over `P` at a prime `q`, and let `B` be an
`A`-algebra in which the integral closure of `P` is a finite `P`-module. Then there is `r ∉ q`
such that the integral closure of `A` in `B`, localized at `r`, is a finite `A_r`-module. -/
theorem Algebra.QuasiFiniteAt.exists_notMem_finite_localizedModule_integralClosure
    [Algebra.FiniteType P A] [Module.Finite P (integralClosure P B)] (q : Ideal A) [q.IsPrime]
    [Algebra.QuasiFiniteAt P q] :
    ∃ r ∉ q,
      Module.Finite (Localization.Away r) (LocalizedModule.Away r (integralClosure A B)) := by
  -- By Zariski's main theorem, every element of `A` times a power of some `r ∉ q` is integral
  -- over `P`; after inverting `r`, the integral closure of `A` in `B` is spanned by that of `P`.
  obtain ⟨r, hrq, H⟩ := zariskisMainProperty_iff'.mp (ZariskisMainProperty.of_finiteType (R := P) q)
  refine ⟨r, hrq, ?_⟩
  -- The integral closure of `P` in `B` lies in that of `A`, where it spans a finite submodule `N`.
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := P) (M := integralClosure P B)
  let incl (d : integralClosure P B) : integralClosure A B := ⟨d.1, d.2.tower_top⟩
  let N : Submodule A (integralClosure A B) := Submodule.span A (incl '' s)
  have hincl (d : integralClosure P B) : incl d ∈ N := by
    have hd : d ∈ Submodule.span P (s : Set (integralClosure P B)) := hs ▸ Submodule.mem_top
    induction hd using Submodule.span_induction with
    | mem d hd => exact Submodule.subset_span ⟨d, hd, rfl⟩
    | zero => exact N.zero_mem
    | add d e _ _ hd he => exact N.add_mem hd he
    | smul p d _ hd =>
      convert N.smul_mem (algebraMap P A p) hd using 1
      exact Subtype.ext (algebraMap_smul A p d.1).symm
  -- Every element of the integral closure of `A` lies in `N` up to a power of `r`.
  have hN (c : integralClosure A B) : ∃ n, r ^ n • c ∈ N := by
    obtain ⟨n, hn⟩ := c.2.exists_isIntegral_algebraMap_pow_mul H
    refine ⟨n, ?_⟩
    convert hincl ⟨_, hn⟩ using 1
    exact Subtype.ext (by simp [incl, Algebra.smul_def])
  have hloc : Submodule.localized (.powers r) N = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
    induction x using LocalizedModule.induction_on with | h c t =>
    obtain ⟨n, hn⟩ := hN c
    obtain ⟨_, k, rfl⟩ := t
    refine ⟨_, hn, ⟨r ^ n, n, rfl⟩ * ⟨r ^ k, k, rfl⟩, ?_⟩
    rw [← IsLocalizedModule.mk_eq_mk']
    exact LocalizedModule.mk_cancel_common_left (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
      ⟨r ^ k, k, rfl⟩ c
  exact ⟨hloc ▸ Submodule.localized'_fg _ _ _ (Submodule.fg_span (s.finite_toSet.image incl))⟩

namespace TauCeti

/-- **The integral closure over a quasi-finite algebra is finite.** Let `A` be a finite type
quasi-finite `P`-algebra and `B` an `A`-algebra in which the integral closure of `P` is a finite
`P`-module. Then the integral closure of `A` in `B` is a finite `A`-module. -/
theorem finite_integralClosure_of_quasiFinite [Algebra.FiniteType P A] [Algebra.QuasiFinite P A]
    [Module.Finite P (integralClosure P B)] : Module.Finite A (integralClosure A B) :=
  .of_forall_isMaximal_exists_notMem fun q _ ↦
    Algebra.QuasiFiniteAt.exists_notMem_finite_localizedModule_integralClosure (P := P) q

open scoped TensorProduct in
/-- **Finite integral closures over a quasi-finite algebra with étale generic fibre.** Let `P` be
a Noetherian N-1 domain with fraction field `K`, for instance an integrally closed Noetherian
domain, let `A` be a finite type quasi-finite `P`-algebra, and let `B` be an `A`-algebra that is
torsion-free over `P` with finite étale generic fibre `K ⊗[P] B`. Then the integral closure of `A`
in `B` is a finite `A`-module. -/
theorem finite_integralClosure_of_quasiFinite_of_etale [IsDomain P] [IsNoetherianRing P]
    [Ring.IsN1 P] (K : Type*) [Field K] [Algebra P K] [IsFractionRing P K]
    [Algebra.FiniteType P A] [Algebra.QuasiFinite P A] [Module.IsTorsionFree P B]
    [Algebra.Etale K (K ⊗[P] B)] : Module.Finite A (integralClosure A B) :=
  have := Ring.finite_integralClosure_of_isTorsionFree_of_etale (R := P) K B
  finite_integralClosure_of_quasiFinite (P := P)

end TauCeti
