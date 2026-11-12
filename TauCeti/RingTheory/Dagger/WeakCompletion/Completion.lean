/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WeakCompletion.Quotient
import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# The parameter-adic completion of a weak completion

The parameter-adic completion of the Monsky–Washnitzer weak completion `S†`
is canonically the parameter-adic completion of `S`. The comparison fixes
every element of `S†` in the ambient completion, and on each quotient is the
parameter-power quotient comparison.

This is an algebraic comparison of completions. No noetherianity,
completeness of the coefficient ring, or regularity of the parameter is needed.
It follows from the parameter-power quotient isomorphisms through
`AdicCompletion.mapₐ_bijective`.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23
  (1986), §2, (2.1)–(2.2), for weak completions and their quotient presentations.
-/

public section

namespace TauCeti.Dagger.weakCompletion

variable {O : Type*} [CommRing O] (π : O) (S : Type*) [CommRing S] [Algebra O S]
  [Algebra.FiniteType O S]

/-- The parameter-adic completion of the weak completion is the original
parameter-adic completion. It extends the inclusion of the weak completion. -/
noncomputable def adicCompletionEquiv :
    piAdicCompletion π (weakCompletion π S) ≃ₐ[O] piAdicCompletion π S :=
  let h : Ideal.span {algebraMap O S π} ≤
      (Ideal.span {algebraMap O (weakCompletion π S) π}).comap (of π S) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.subset_span rfl
  (AlgEquiv.ofBijective (AdicCompletion.mapₐ (of π S) h)
    (AdicCompletion.mapₐ_bijective (of π S) h fun n ↦ by
      convert (quotientPowEquiv π (S := S) n).symm.bijective using 1
      ext s
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      simp)).symm

variable {S}

/-- On each parameter-power quotient, the completion comparison is the
quotient comparison of the weak completion with the original algebra. -/
@[simp]
theorem evalₐ_adicCompletionEquiv (n : ℕ)
    (z : piAdicCompletion π (weakCompletion π S)) :
    AdicCompletion.evalₐ _ n (adicCompletionEquiv π S z) =
      quotientPowEquiv π n (AdicCompletion.evalₐ _ n z) := by
  have h (y : piAdicCompletion π S) :
      AdicCompletion.evalₐ _ n ((adicCompletionEquiv π S).symm y) =
        (quotientPowEquiv π (S := S) n).symm (AdicCompletion.evalₐ _ n y) := by
    rw [adicCompletionEquiv, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply,
      AdicCompletion.evalₐ_mapₐ]
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ n y)
    rw [← hs]
    simp
  apply (quotientPowEquiv π (S := S) n).symm.injective
  simpa only [AlgEquiv.symm_apply_apply] using (h (adicCompletionEquiv π S z)).symm

/-- The comparison fixes every weakly completed element in the ambient completion. -/
@[simp]
theorem adicCompletionEquiv_of (z : weakCompletion π S) :
    adicCompletionEquiv π S (AdicCompletion.of _ _ z) = (z : piAdicCompletion π S) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicCompletionEquiv, AdicCompletion.evalₐ_of, quotientPowEquiv_mk, eval_eq]

/-- The comparison extends the weak-completion inclusion along the algebra map.
This form also supports simplification of the native algebra-map presentation. -/
@[simp]
theorem adicCompletionEquiv_algebraMap (z : weakCompletion π S) :
    adicCompletionEquiv π S
      (algebraMap (weakCompletion π S) (piAdicCompletion π (weakCompletion π S)) z) =
      (z : piAdicCompletion π S) := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    adicCompletionEquiv_of]

/-- The inverse comparison sends a weakly completed element to its canonical
image in the parameter-adic completion of the weak completion. -/
@[simp]
theorem adicCompletionEquiv_symm_coe (z : weakCompletion π S) :
    (adicCompletionEquiv π S).symm (z : piAdicCompletion π S) =
      algebraMap (weakCompletion π S) (piAdicCompletion π (weakCompletion π S)) z := by
  rw [AlgEquiv.symm_apply_eq, adicCompletionEquiv_algebraMap]

end TauCeti.Dagger.weakCompletion
