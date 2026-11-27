/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

import Mathlib.RingTheory.Ideal.MonicSpan
import TauCeti.LinearAlgebra.Charpoly.Lsmul
import TauCeti.RingTheory.AdjoinRoot.Charpoly
import TauCeti.RingTheory.Semisimple.Charpoly

/-!
# Characteristic polynomials and semisimple endomorphisms

`IsSimpleModule.exists_linearEquiv_quot_of_charpoly_lsmul_X` identifies a simple polynomial
module with the quotient by the characteristic polynomial of multiplication by `X`. This uses
`AdjoinRoot.charpoly_lmul_root` and the description of simple modules as quotients by maximal
ideals. The factorization `IsSemisimpleModule.charpoly_lsmul_eq_prod` then recovers the multiplicity
of each simple summand in `IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_lsmul_X_eq`. Thus
`Module.End.IsSemisimple.exists_linearEquiv_conj_eq_of_charpoly_eq` classifies semisimple
endomorphisms up to change of basis over any field, including over imperfect fields.
-/

public section

open Module Polynomial TauCeti

/-- On a finite-dimensional simple `K[X]`-module, multiplication by `X` has irreducible
characteristic polynomial `p`, and the module is isomorphic to `K[X]/(p)`. -/
theorem IsSimpleModule.exists_linearEquiv_quot_of_charpoly_lsmul_X {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module K[X] V] [IsScalarTower K K[X] V] [FiniteDimensional K V]
    [IsSimpleModule K[X] V] :
    ∃ p : K[X], Irreducible p ∧ (Algebra.lsmul K K V (X : K[X])).charpoly = p ∧
      Nonempty (V ≃ₗ[K[X]] K[X] ⧸ Ideal.span {p}) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule K[X] V›
  obtain ⟨p, hp, hIp⟩ := exists_monic_span I
    (Ring.ne_bot_of_isMaximal_of_not_isField hI (Polynomial.not_isField K))
  let e' := e.trans (Submodule.quotEquivOfEq I (Ideal.span {p}) hIp)
  have hmax : (Ideal.span {p}).IsMaximal := hIp ▸ hI
  refine ⟨p, (Ideal.irreducible_iff_isMaximal_span_singleton_of_not_isField
    (Polynomial.not_isField K)).mpr hmax, ?_, ⟨e'⟩⟩
  have := hp.finite_quotient
  have := hp.finite_adjoinRoot
  have := hp.free_adjoinRoot
  -- In `AdjoinRoot p`, the scalar `X` acts by multiplication by the adjoined root.
  have hroot : (Algebra.lsmul K K (K[X] ⧸ Ideal.span {p}) (X : K[X])).charpoly = p :=
    AdjoinRoot.charpoly_lmul_root hp
  rw [e'.charpoly_lsmul_eq (X : K[X]), hroot]

/-- Two finite-dimensional semisimple `K[X]`-modules are isomorphic if multiplication by `X`
has the same characteristic polynomial on both modules. -/
theorem IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_lsmul_X_eq {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [Module K[X] M] [IsScalarTower K K[X] M]
    [FiniteDimensional K M] [IsSemisimpleModule K[X] M]
    [AddCommGroup N] [Module K N] [Module K[X] N] [IsScalarTower K K[X] N]
    [FiniteDimensional K N] [IsSemisimpleModule K[X] N]
    (h : (Algebra.lsmul K K M (X : K[X])).charpoly = (Algebra.lsmul K K N (X : K[X])).charpoly) :
    Nonempty (M ≃ₗ[K[X]] N) := by
  classical
  have := Module.Finite.of_restrictScalars_finite K K[X] M
  have := Module.Finite.of_restrictScalars_finite K K[X] N
  obtain ⟨ι, _, T, hTs, hT, hM, hN⟩ := IsSemisimpleModule.exists_simple_family (R := K[X]) M N
  have (i : ι) : FiniteDimensional K (T i) :=
    .of_injective ((T i).subtype.restrictScalars K) Subtype.val_injective
  have (i : ι) : IsSimpleModule K[X] (T i) := hTs i
  choose p hp hchar he using fun i : ι ↦
    IsSimpleModule.exists_linearEquiv_quot_of_charpoly_lsmul_X (K := K) (V := T i)
  have hmonic (i : ι) : (p i).Monic := hchar i ▸ LinearMap.charpoly_monic _
  have hinj : Function.Injective p := by
    intro i j hij
    by_contra hne
    obtain ⟨ei⟩ := he i
    obtain ⟨ej⟩ := he j
    exact (hT hne).false (ei.trans ((Submodule.quotEquivOfEq _ _ (by rw [hij])).trans ej.symm))
  have hmult (i : ι) (a : ι → ℕ) : emultiplicity (p i) (∏ j, p j ^ a j) = a i := by
    have hprime := (hp i).prime
    rw [Finset.emultiplicity_prod hprime, Finset.sum_eq_single i]
    · exact emultiplicity_pow_self_of_prime hprime _
    · intro j _ hji
      have hnd : ¬p i ∣ p j := fun hd ↦ hji.symm (hinj (eq_of_monic_of_associated
        (hmonic i) (hmonic j) (((hp i).dvd_irreducible_iff_associated (hp j)).mp hd)))
      rw [emultiplicity_pow hprime, emultiplicity_eq_zero.mpr hnd, mul_zero]
    · simp
  simp only [IsSemisimpleModule.charpoly_lsmul_eq_prod hT hM,
    IsSemisimpleModule.charpoly_lsmul_eq_prod hT hN, hchar] at h
  have hcounts (i : ι) : jordanHolderMultiplicity K[X] M (T i) =
      jordanHolderMultiplicity K[X] N (T i) := by
    simpa only [hmult, Nat.cast_inj] using congrArg (emultiplicity (p i)) h
  exact IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq M N
    (fun S _ _ _ ↦ apply_jordanHolderMultiplicity_eq_of_forall_eq id hM hN hcounts S)

/-- Over any field, semisimple endomorphisms of finite-dimensional spaces with the same
characteristic polynomial are conjugate by a linear equivalence. -/
theorem Module.End.IsSemisimple.exists_linearEquiv_conj_eq_of_charpoly_eq {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {f : End K V} {g : End K W} (hf : f.IsSemisimple) (hg : g.IsSemisimple)
    (h : f.charpoly = g.charpoly) : ∃ e : V ≃ₗ[K] W, e.conj f = g := by
  have : IsSemisimpleModule K[X] (AEval' f) := hf
  have : IsSemisimpleModule K[X] (AEval' g) := hg
  have hX : (Algebra.lsmul K K (AEval' f) (X : K[X])).charpoly =
      (Algebra.lsmul K K (AEval' g) (X : K[X])).charpoly := by
    simp only [LinearMap.charpoly_lsmul_X_aeval, h]
  obtain ⟨e⟩ := IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_lsmul_X_eq hX
  let c := (AEval'.of f).trans ((e.restrictScalars K).trans (AEval'.of g).symm)
  refine ⟨c, LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨v, rfl⟩ := c.surjective x
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simp only [c, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, ← AEval'.X_smul_of,
    e.map_smul]
  exact AEval'.of_symm_X_smul g (e (AEval'.of f v))
