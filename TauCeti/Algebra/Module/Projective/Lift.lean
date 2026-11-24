/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.Module.LinearMap.EndQuotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Finiteness.Projective
import TauCeti.RingTheory.AdicCompletion.Idempotent
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.Ideal.Operations

/-!
# Lifting projective modules from a reduction

Let `R` be a commutative Noetherian ring, complete with respect to a principal ideal `(r)`, and
`A` an `R`-algebra, possibly noncommutative, such as the group algebra `ℤ_p[G]` of a finite group
over `R = ℤ_p` with `r = p`. Let `N` be a projective `A`-module which is finitely generated over
`R`, for instance a finitely generated free `A`-module when `A` is finite over `R`. This file
proves that every direct summand of the reduction `N ⧸ r • N` is the reduction of a direct summand
of `N`. When `A` is finite over `R`, a finitely generated projective module over `A ⧸ r A` is a
direct summand of the reduction of a finitely generated free `A`-module, and is therefore the
reduction of a finitely generated projective `A`-module.

The summand of `N ⧸ r • N` is cut out by an idempotent endomorphism, which lifts to an idempotent
endomorphism of `N`. Reduction of endomorphisms is onto because `N` is projective
(`Ideal.endMapQ_surjective`), and its kernel is `r • End_A(N)`
(`Ideal.endMapQ_span_algebraMap_eq_zero_iff`). The results only assume that the ring
`End_A(N)` is `(r)`-adically complete, which holds in the setting above because `End_A(N)` is
then finite over `R`; `IsAdicComplete.exists_isIdempotentElem_eq` then lifts the
idempotent. Over a semiprimary ring the same lifting needs no completeness, the kernel being nil;
that case is used in `TauCeti/Algebra/Module/ProjectiveCover/Existence.lean`.

When `r` lies in the Jacobson radical of `A`, the lift is unique up to isomorphism by
`Ideal.nonempty_linearEquiv_of_quotient_smul_top`.

Over a commutative ring complete for any ideal `I`, finite projective modules over `R ⧸ I`
lift to finite projective `R`-modules without a Noetherian hypothesis. The proof uses a finite
free presentation and lifts its splitting idempotent; its endomorphism ring is complete because
it is a finite product of copies of `R`.

## Main results

* `TauCeti.exists_isIdempotentElem_endMapQ_eq`: idempotent endomorphisms of `N ⧸ r • N` lift to
  idempotent endomorphisms of `N`.
* `TauCeti.exists_projective_quotient_smul_top_linearEquiv`: every direct summand of
  `N ⧸ r • N` is the reduction of a projective submodule of `N`.
* `TauCeti.exists_finite_projective_lift`: finite projective modules over `R ⧸ I` lift over an
  `I`-adically complete commutative ring.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* T. Y. Lam, *A First Course in Noncommutative Rings*, §21 and §24.
* [Stacks Project, Lemma 15.13.1](https://stacks.math.columbia.edu/tag/0D4A).
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] (r : R) {A : Type*} [Ring A] [Algebra R A]
  {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  [Module.Projective A N] [IsAdicComplete (Ideal.span {r}) (Module.End A N)]

/-- **Idempotents lift from the reduction modulo `r`.** For a projective `A`-module `N` whose
endomorphism ring is `(r)`-adically complete, every idempotent endomorphism of `N ⧸ r • N` is the
reduction of an idempotent endomorphism of `N`.

The completeness hypothesis holds when `R` is Noetherian and `(r)`-adically complete and `N` is
finitely generated over `R`, by `TauCeti.isNoetherian_linearMap_of_finite` and
`IsAdicComplete.of_finite`. -/
theorem exists_isIdempotentElem_endMapQ_eq
    {e : Module.End A (N ⧸ Ideal.span {algebraMap R A r} • (⊤ : Submodule A N))}
    (he : IsIdempotentElem e) :
    ∃ f : Module.End A N, IsIdempotentElem f ∧
      Ideal.endMapQ (Ideal.span {algebraMap R A r}) N f = e := by
  refine IsAdicComplete.exists_isIdempotentElem_eq (Ideal.span {r}) _ (fun f ↦ ?_)
    (Ideal.endMapQ_surjective _ N e) he
  rw [Ideal.endMapQ_span_algebraMap_eq_zero_iff, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

/-- The range of a lifted idempotent reduces onto the original split summand, with the
expected kernel. This argument does not require the ambient module to be projective. -/
private theorem exists_surjective_range_endMapQ {B N : Type*} [Ring B] [AddCommGroup N]
    [Module B N] (J : Ideal B) {Y : Type*} [AddCommGroup Y] [Module B Y]
    {e : Module.End B N} (he : IsIdempotentElem e)
    (i : Y →ₗ[B] N ⧸ J • (⊤ : Submodule B N))
    (q : (N ⧸ J • (⊤ : Submodule B N)) →ₗ[B] Y)
    (hqi : q ∘ₗ i = LinearMap.id) (hee : Ideal.endMapQ J N e = i ∘ₗ q) :
    ∃ f : LinearMap.range e →ₗ[B] Y,
      Function.Surjective f ∧ LinearMap.ker f = J • ⊤ := by
  have hqi' (y : Y) : q (i y) = y := LinearMap.congr_fun hqi y
  have hred (x : N) : i (q (Submodule.Quotient.mk x)) = Submodule.Quotient.mk (e x) := by
    rw [← Ideal.endMapQ_mk, hee, LinearMap.comp_apply]
  have hfix (x : LinearMap.range e) : e x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff he).mp x.property
  let f : LinearMap.range e →ₗ[B] Y :=
    q ∘ₗ (J • (⊤ : Submodule B N)).mkQ ∘ₗ (LinearMap.range e).subtype
  have hle : J • (⊤ : Submodule B (LinearMap.range e)) ≤ LinearMap.ker f :=
    Submodule.smul_le.mpr fun a ha x _ ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.coe_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.smul_mem_smul ha Submodule.mem_top), map_zero]
  have hker : LinearMap.ker f ≤ J • ⊤ := by
    intro x hx
    have hx' : q (Submodule.Quotient.mk (x : N)) = 0 := by simpa [f] using hx
    have hx0 : (x : N) ∈ J • (⊤ : Submodule B N) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← hfix x, ← hred, hx', map_zero]
    have := Submodule.smul_top_le_comap_smul_top J e.rangeRestrict hx0
    have he' : e.rangeRestrict (x : N) = x := Subtype.ext (hfix x)
    simpa only [Submodule.mem_comap, he'] using this
  refine ⟨f, ?_, le_antisymm hker hle⟩
  intro y
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (i y)
  refine ⟨⟨e n, LinearMap.mem_range_self e n⟩, ?_⟩
  simp [f, ← hred, hn, hqi']

/-- **Direct summands lift from the reduction modulo `r`.** Let `N` be a projective `A`-module
whose endomorphism ring is `(r)`-adically complete, and let `Y` be a direct summand of
`N ⧸ r • N`, given by maps `i : Y → N ⧸ r • N` and `q : N ⧸ r • N → Y` with `q ∘ i = id`. Then
`Y ≃ X ⧸ r • X` for a projective submodule `X` of `N`, namely the range of an idempotent lifting
`i ∘ q`.

In particular, when `A` is finite over `R`, a finitely generated projective module over `A ⧸ r A`,
which is a direct summand of the reduction of a finitely generated free `A`-module, is the reduction
of a projective `A`-module, finitely generated when `R` is Noetherian. -/
theorem exists_projective_quotient_smul_top_linearEquiv {Y : Type*}
    [AddCommGroup Y] [Module A Y]
    (i : Y →ₗ[A] N ⧸ Ideal.span {algebraMap R A r} • (⊤ : Submodule A N))
    (q : (N ⧸ Ideal.span {algebraMap R A r} • (⊤ : Submodule A N)) →ₗ[A] Y)
    (hqi : q ∘ₗ i = LinearMap.id) :
    ∃ X : Submodule A N, Module.Projective A X ∧
      Nonempty ((X ⧸ Ideal.span {algebraMap R A r} • (⊤ : Submodule A X)) ≃ₗ[A] Y) := by
  obtain ⟨e, he, hee⟩ := exists_isIdempotentElem_endMapQ_eq r (e := i ∘ₗ q)
    (LinearMap.ext fun x ↦ congrArg i (LinearMap.congr_fun hqi (q x)))
  obtain ⟨f, hf, hker⟩ := exists_surjective_range_endMapQ _ he i q hqi hee
  have hfix (x : LinearMap.range e) : e x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff he).mp x.property
  refine ⟨LinearMap.range e,
    .of_split (LinearMap.range e).subtype e.rangeRestrict
      (LinearMap.ext fun x ↦ Subtype.ext (hfix x)),
    ⟨.ofBijective ((Ideal.span {algebraMap R A r} • ⊤ : Submodule A (LinearMap.range e)).liftQ f
      hker.ge) ⟨LinearMap.ker_eq_bot.mp ?_, ?_⟩⟩⟩
  · exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  · rw [← LinearMap.range_eq_top, Submodule.range_liftQ]
    exact LinearMap.range_eq_top.mpr hf

section ArbitraryIdeal

variable {S : Type*} [CommRing S] (I : Ideal S) {M : Type*}
  [AddCommGroup M] [Module S M]

/-- Idempotent endomorphisms lift modulo an arbitrary ideal for a module with a finite basis
and an adically complete endomorphism ring. -/
theorem exists_isIdempotentElem_endMapQ_eq_of_basis {ι : Type*} [Finite ι]
    (b : Module.Basis ι S M) [IsAdicComplete I (Module.End S M)]
    {e : Module.End S (M ⧸ I • (⊤ : Submodule S M))} (he : IsIdempotentElem e) :
    ∃ f : Module.End S M, IsIdempotentElem f ∧ Ideal.endMapQ I M f = e := by
  let := Module.Projective.of_basis b
  refine IsAdicComplete.exists_isIdempotentElem_eq I _ (fun f ↦ ?_)
    (Ideal.endMapQ_surjective I M e) he
  rw [← RingHom.mem_ker, Ideal.mem_ker_endMapQ_iff, b.mem_smul_top_linearMap_iff]
  exact ⟨fun h i ↦ h (LinearMap.mem_range_self f (b i)), fun h x hx ↦ by
    obtain ⟨y, rfl⟩ := hx
    exact LinearMap.apply_mem_smul_top_of_mem_smul_top
      (b.mem_smul_top_linearMap_iff.mpr h) y⟩

/-- A direct summand of a reduction lifts to a projective submodule when the ambient module
has a finite basis and its endomorphism ring is adically complete. -/
theorem exists_projective_lift_of_basis {ι : Type*} [Finite ι] (b : Module.Basis ι S M)
    [IsAdicComplete I (Module.End S M)] {Y : Type*} [AddCommGroup Y] [Module S Y]
    (i : Y →ₗ[S] M ⧸ I • (⊤ : Submodule S M))
    (q : (M ⧸ I • (⊤ : Submodule S M)) →ₗ[S] Y) (hqi : q ∘ₗ i = LinearMap.id) :
    ∃ X : Submodule S M, Module.Finite S X ∧ Module.Projective S X ∧
      ∃ f : X →ₗ[S] Y, Function.Surjective f ∧ LinearMap.ker f = I • ⊤ := by
  let := Module.Projective.of_basis b
  let := Module.Finite.of_basis b
  obtain ⟨e, he, hee⟩ := exists_isIdempotentElem_endMapQ_eq_of_basis I b (e := i ∘ₗ q)
    (LinearMap.ext fun x ↦ congrArg i (LinearMap.congr_fun hqi (q x)))
  have hfix (x : LinearMap.range e) : e x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff he).mp x.property
  exact ⟨LinearMap.range e, inferInstance,
    .of_split (LinearMap.range e).subtype e.rangeRestrict
      (LinearMap.ext fun x ↦ Subtype.ext (hfix x)),
    exists_surjective_range_endMapQ I he i q hqi hee⟩

end ArbitraryIdeal

/-- A finite projective module modulo an ideal of an adically complete ring lifts to a finite
projective module. The lift map is onto and has kernel `I • P`.

This is the existence part of Stacks Project, Lemma 15.13.1 (Tag 0D4A). -/
theorem exists_finite_projective_lift {S : Type u} [CommRing S] (I : Ideal S)
    [IsAdicComplete I S] (Y : Type*) [AddCommGroup Y] [Module S Y]
    [Module (S ⧸ I) Y] [IsScalarTower S (S ⧸ I) Y]
    [Module.Finite (S ⧸ I) Y] [Module.Projective (S ⧸ I) Y] :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module S P),
      Module.Finite S P ∧ Module.Projective S P ∧
      ∃ f : P →ₗ[S] Y, Function.Surjective f ∧ LinearMap.ker f = I • ⊤ := by
  classical
  obtain ⟨n, q, i, _, _, hqi⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (S ⧸ I) Y
  let b := Pi.basisFun S (Fin n)
  let c : Module.End S (Fin n → S) ≃ₗ[S] (Fin n → Fin n → S) := (b.constr S).symm
  have : IsAdicComplete I (Module.End S (Fin n → S)) := by
    apply AdicCompletion.of_bijective_iff.mp
    have hc : AdicCompletion.of I (Fin n → Fin n → S) ∘ c =
        AdicCompletion.congr I c ∘ AdicCompletion.of I (Module.End S (Fin n → S)) := rfl
    exact (Function.Bijective.of_comp_iff' (AdicCompletion.congr I c).bijective _).mp
      (hc ▸ (AdicCompletion.of_bijective I _).comp c.bijective)
  let p : (Fin n → S) →ₗ[S] (Fin n → S ⧸ I) :=
    LinearMap.pi fun j ↦ (Algebra.linearMap S (S ⧸ I)).comp (LinearMap.proj j)
  have hp : Function.Surjective p := fun x ↦ by
    choose y hy using fun j ↦ Ideal.Quotient.mk_surjective (x j)
    exact ⟨y, funext hy⟩
  have hker : LinearMap.ker p = I • (⊤ : Submodule S (Fin n → S)) := by
    ext x
    simp only [LinearMap.mem_ker, p, LinearMap.pi_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.proj_apply, Algebra.linearMap_apply,
      funext_iff, Pi.zero_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    simpa [b] using (b.mem_smul_top_iff (I := I) (x := x)).symm
  let d : ((Fin n → S) ⧸ I • (⊤ : Submodule S (Fin n → S))) ≃ₗ[S]
      (Fin n → S ⧸ I) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (p.quotKerEquivOfSurjective hp)
  obtain ⟨X, hfin, hproj, f, hf, hkerf⟩ := exists_projective_lift_of_basis I b
    (d.symm.toLinearMap.comp (i.restrictScalars S))
    ((q.restrictScalars S).comp d.toLinearMap) (by
      ext y
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact LinearMap.congr_fun hqi y)
  exact ⟨X, inferInstance, inferInstance, hfin, hproj, f, hf, hkerf⟩

end TauCeti
