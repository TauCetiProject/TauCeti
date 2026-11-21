/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.GenericFiber
public import TauCeti.RingTheory.IntegralClosure.QuasiFinite
public import TauCeti.RingTheory.Kaehler.SeparatingLift

import TauCeti.RingTheory.Ideal.MinimalPrime.Polynomial
import TauCeti.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.Unramified.Localization

/-!
# Finite normalization in a generic fibre smooth of dimension one

Let `R` be an integrally closed Noetherian domain with fraction field `K`, for instance a possibly
non-excellent discrete valuation ring, let `A` be a finite type `R`-algebra, and let
`B = A[1/π]` for some `π : R`, viewed as a `K`-algebra. Suppose that `B` is reduced, that
the residue field of every minimal prime of `B` is a transcendental extension of `K` with
one-dimensional Kähler differentials, and that the special fibre `A ⧸ πA` has dimension at most
one. This is the situation of an affine chart of a model of a smooth curve over a discrete
valuation ring. Then the integral closure of `A` in `B` is a finite `A`-module, without any
excellence or Japanese hypothesis on `R`.

The proof is local on `Spec A`. Away from `π` the integral closure is `B` itself. At a maximal
ideal `q` containing `π`, `TauCeti.exists_quasiFiniteAt_and_forall_isSeparable_adjoin` gives a
coordinate `x : A` which is quasi-finite at `q` and separating on every component of `B`. Through
`x`, the ring `B` becomes an `R[X]`-algebra which is torsion-free with finite étale generic fibre
(`TauCeti.isTorsionFree_polynomial_of_forall_transcendental` and
`TauCeti.etale_tensorProduct_polynomial_of_forall_isSeparable`). Since `R[X]` is an integrally
closed Noetherian domain, the integral closure of `R[X]` in `B` is finite
(`TauCeti.Ring.finite_integralClosure_of_isTorsionFree_of_etale`), and Zariski's main theorem
(`Algebra.QuasiFiniteAt.exists_notMem_finite_localizedModule_integralClosure`) makes the integral
closure of `A` in `B` finite near `q`.

## Main results

* `TauCeti.finite_integralClosure_of_forall_finrank_kaehlerDifferential_eq_one`: the integral
  closure of `A` in `B = A[1/π]` is a finite `A`-module.

## References

* The Stacks Project, Lemma 55.8.2, https://stacks.math.columbia.edu/tag/0C2T.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 4.1.2 (normalization).
-/

public section

open Polynomial
open scoped IntermediateField TensorProduct

namespace TauCeti

variable {R K A B : Type*} [CommRing R] [Field K] [Algebra R K] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Algebra K B]
  [IsScalarTower R K B]

/-- Near a prime `q`, a coordinate `x : A` that is quasi-finite at `q` over `R[X]` and separating on
every component of `B` makes the integral closure of `A` in `B` finite. Through `x`, the ring `B`
is a torsion-free `R[X]`-algebra with finite étale generic fibre, so the integral closure of `R[X]`
in `B` is finite, and Zariski's main theorem concludes. -/
private lemma exists_notMem_finite_of_quasiFiniteAt_of_forall_isSeparable [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsFractionRing R K] [Algebra.FiniteType R A]
    [Algebra.EssFiniteType K B] [IsReduced B] (x : A) (q : Ideal A) [q.IsPrime]
    (hx : letI := (aeval (R := R) x).toAlgebra; Algebra.QuasiFiniteAt R[X] q)
    (hsep : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B →
      Transcendental K (algebraMap A p.ResidueField x) ∧
        Algebra.IsSeparable K⟮algebraMap A p.ResidueField x⟯ p.ResidueField) :
    ∃ r ∉ q,
      Module.Finite (Localization.Away r) (LocalizedModule.Away r (integralClosure A B)) := by
  have := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  let : Algebra R[X] A := (aeval x).toAlgebra
  let : Algebra R[X] B := ((IsScalarTower.toAlgHom R A B).comp (aeval x)).toAlgebra
  have : IsScalarTower R[X] A B := .of_algebraMap_eq' <| by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      ← IsScalarTower.coe_toAlgHom R A B]
    exact AlgHom.comp_toRingHom _ _
  have : IsScalarTower R R[X] A := .of_algHom (aeval x)
  have : IsScalarTower R R[X] B := .of_algHom ((IsScalarTower.toAlgHom R A B).comp (aeval x))
  have : Algebra.FiniteType R[X] A := .of_restrictScalars_finiteType R R[X] A
  have hX (p : Ideal B) [p.IsPrime] :
      algebraMap R[X] p.ResidueField X = algebraMap A p.ResidueField x := by
    rw [IsScalarTower.algebraMap_apply R[X] A, RingHom.algebraMap_toAlgebra]
    exact congrArg _ (aeval_X x)
  have : Module.IsTorsionFree R[X] B := isTorsionFree_polynomial_of_forall_transcendental
    fun p _ hp ↦ hX p ▸ (hsep p hp).1.restrictScalars (IsFractionRing.injective R K)
  have : Algebra.Etale (FractionRing R[X]) (FractionRing R[X] ⊗[R[X]] B) :=
    etale_tensorProduct_polynomial_of_forall_isSeparable (K := K) fun p _ hp _ ↦ by
      rw [hX p]
      exact hsep p hp
  have := Ring.finite_integralClosure_of_isTorsionFree_of_etale (R := R[X]) (FractionRing R[X]) B
  have := hx
  exact Algebra.QuasiFiniteAt.exists_notMem_finite_localizedModule_integralClosure (P := R[X]) q

/-- **Finite normalization in a generically smooth curve.** Let `R` be an integrally closed
Noetherian domain with fraction field `K`, for instance a discrete valuation ring, let `A` be a
finite type `R`-algebra, and let `B = A[1/π]` for some `π : R`, carrying a compatible
`K`-algebra structure. Suppose that `A ⧸ πA` has dimension at most one, that `B` is reduced, and
that the residue field of every minimal prime of `B` is a transcendental extension of `K` with
one-dimensional Kähler differentials. Then the integral closure of `A` in `B` is a finite
`A`-module. No excellence or Japanese hypothesis on `R` is needed. -/
theorem finite_integralClosure_of_forall_finrank_kaehlerDifferential_eq_one [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsFractionRing R K] [Algebra.FiniteType R A]
    {π : R} [IsLocalization.Away (algebraMap R A π) B]
    [Ring.KrullDimLE 1 (A ⧸ Ideal.span {algebraMap R A π})] [IsReduced B]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B →
      Algebra.Transcendental K p.ResidueField ∧
        Module.finrank p.ResidueField Ω[p.ResidueField⁄K] = 1) :
    Module.Finite A (integralClosure A B) := by
  have := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  -- For `π = 0` the ring `B = A[1/0]` is zero.
  rcases eq_or_ne π 0 with rfl | hπ
  · have : Subsingleton B :=
      IsLocalization.subsingleton (M := .powers (algebraMap R A 0)) ⟨1, by simp⟩
    infer_instance
  refine .of_forall_isMaximal_exists_notMem fun q hq ↦ ?_
  by_cases hπq : algebraMap R A π ∉ q
  · exact ⟨_, hπq, IsLocalization.finite_localizedModule_integralClosure (.powers _)⟩
  rw [not_not] at hπq
  -- At a point of the special fibre, choose a coordinate `x`, quasi-finite at `q` and separating
  -- on every component of the generic fibre `B`.
  let f := Ideal.Quotient.mkₐ R (Ideal.span {algebraMap R A π})
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hkerf : RingHom.ker f = Ideal.span {algebraMap R A π} := Ideal.Quotient.mkₐ_ker R _
  have hπq' : Ideal.span {algebraMap R A π} ≤ q := (Ideal.span_singleton_le_iff_mem q).mpr hπq
  have : (q.map f).IsMaximal := hq.map_of_surjective_of_ker_le hf (hkerf.trans_le hπq')
  have hqf : (q.map f).comap f = q := Ideal.comap_map_mk hπq'
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing (.powers (algebraMap R A π)) B ‹_›
  have : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  have (i : minimalPrimes B) : i.val.IsPrime := i.property.1.1
  have : Algebra.EssFiniteType A B := .of_isLocalization B (.powers (algebraMap R A π))
  have : Algebra.EssFiniteType R B := .comp R A B
  have : Algebra.EssFiniteType K B := .of_comp R K B
  have (i : minimalPrimes B) : Algebra.EssFiniteType K i.val.ResidueField := .comp K B _
  have (i : minimalPrimes B) : Algebra.Transcendental K i.val.ResidueField :=
    (h i.val i.property).1
  have : Algebra.FormallyUnramified A B := .of_isLocalization (.powers (algebraMap R A π))
  have (i : minimalPrimes B) : Algebra.FormallyUnramified A i.val.ResidueField := .comp A B _
  obtain ⟨x, -, hx, hsep⟩ := exists_quasiFiniteAt_and_forall_isSeparable_adjoin (K := K)
    (fun i : minimalPrimes B ↦ i.val.ResidueField) f hf hπ
    ((f.commutes π).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self _))) (q.map f)
    (by rw [hqf, hkerf, Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_map_of_mem _ ((Ideal.mem_under R q).mpr hπq))
    (fun i ↦ (h i.val i.property).2)
  rw [← hqf]
  exact exists_notMem_finite_of_quasiFiniteAt_of_forall_isSeparable x _ hx
    fun p _ hp ↦ hsep ⟨p, hp⟩

end TauCeti
