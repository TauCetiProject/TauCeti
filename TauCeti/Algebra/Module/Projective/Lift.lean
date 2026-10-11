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
import Mathlib.LinearAlgebra.Projection
import TauCeti.RingTheory.AdicCompletion.Idempotent
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
then finite over `R`; `TauCeti.IsAdicComplete.exists_isIdempotentElem_eq` then lifts the
idempotent. Over a semiprimary ring the same lifting needs no completeness, the kernel being nil;
that case is used in `TauCeti/Algebra/Module/ProjectiveCover/Existence.lean`.

When `r` lies in the Jacobson radical of `A`, the lift is unique up to isomorphism by
`Ideal.nonempty_linearEquiv_of_quotient_smul_top`.

## Main results

* `TauCeti.exists_isIdempotentElem_endMapQ_eq`: idempotent endomorphisms of `N ⧸ r • N` lift to
  idempotent endomorphisms of `N`.
* `TauCeti.exists_projective_quotient_smul_top_linearEquiv`: every direct summand of
  `N ⧸ r • N` is the reduction of a projective submodule of `N`.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* T. Y. Lam, *A First Course in Noncommutative Rings*, §21 and §24.
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
finitely generated over `R`, by `Module.Finite.linearMap_of_isNoetherian` and
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
  have hqi' (y : Y) : q (i y) = y := LinearMap.congr_fun hqi y
  obtain ⟨e, he, hee⟩ := exists_isIdempotentElem_endMapQ_eq r (e := i ∘ₗ q)
    (LinearMap.ext fun x ↦ congrArg i (hqi' (q x)))
  -- `e` reduces to `i ∘ q` and fixes its range `X` pointwise.
  have hred (x : N) : i (q (Submodule.Quotient.mk x)) = Submodule.Quotient.mk (e x) := by
    rw [← Ideal.endMapQ_mk, hee, LinearMap.comp_apply]
  have hfix (x : LinearMap.range e) : e x = x :=
    (LinearMap.IsIdempotentElem.mem_range_iff he).mp x.2
  -- The composite `X → N ⧸ r • N → Y` descends to the required isomorphism `X ⧸ r • X ≃ Y`.
  let φ : LinearMap.range e →ₗ[A] Y :=
    q ∘ₗ (Ideal.span {algebraMap R A r} • (⊤ : Submodule A N)).mkQ ∘ₗ (LinearMap.range e).subtype
  have hle :
      Ideal.span {algebraMap R A r} • (⊤ : Submodule A (LinearMap.range e)) ≤ LinearMap.ker φ :=
    Submodule.smul_le.mpr fun a ha x _ ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.coe_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.smul_mem_smul ha Submodule.mem_top), map_zero]
  have hker : LinearMap.ker φ ≤ Ideal.span {algebraMap R A r} • ⊤ := by
    intro x hx
    have hx' : q (Submodule.Quotient.mk (x : N)) = 0 := by simpa [φ] using hx
    have hx0 : (x : N) ∈ Ideal.span {algebraMap R A r} • (⊤ : Submodule A N) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← hfix x, ← hred, hx', map_zero]
    obtain ⟨w, hw⟩ := (Submodule.mem_span_algebraMap_smul_top_iff r).mp hx0
    refine (Submodule.mem_span_algebraMap_smul_top_iff r).mpr
      ⟨⟨e w, LinearMap.mem_range_self e w⟩, Subtype.ext ?_⟩
    rw [Submodule.coe_smul_of_tower, ← LinearMap.map_smul_of_tower, hw, hfix]
  have hsurj : Function.Surjective φ := fun y ↦ by
    obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (i y)
    refine ⟨⟨e n, LinearMap.mem_range_self e n⟩, ?_⟩
    simp [φ, ← hred, hn, hqi']
  refine ⟨LinearMap.range e,
    .of_split (LinearMap.range e).subtype e.rangeRestrict (LinearMap.ext fun x ↦ Subtype.ext ?_),
    ⟨.ofBijective ((Ideal.span {algebraMap R A r} • ⊤ : Submodule A (LinearMap.range e)).liftQ φ
      hle) ⟨LinearMap.ker_eq_bot.mp ?_, ?_⟩⟩⟩
  · exact hfix x
  · exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  · rw [← LinearMap.range_eq_top, Submodule.range_liftQ]
    exact LinearMap.range_eq_top.mpr hsurj

end TauCeti
