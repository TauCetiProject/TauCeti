/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IsAlgClosed.Automorphism
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Embeddings into an algebraically closed field of large transcendence degree

Let `E` be a domain containing `R`, with transcendence basis `v`, and let `Ω` be an
algebraically closed `R`-algebra. Any algebraically independent family `w` in `Ω`, indexed like
`v`, is the image of `v` under an `R`-algebra homomorphism `E →ₐ[R] Ω`: first send the polynomial
ring on `v` to the polynomial ring on `w`, then extend along the algebraic extension
`E / R[v]` to the algebraically closed field `Ω`.

Over a base field `k`, comparing transcendence degrees gives the existence results:

* a domain `E` containing `k` maps to `Ω` over `k` as soon as `trdeg k E ≤ trdeg k Ω`; when `E`
  is a field such a map is a field embedding;
* two algebraically closed fields of the same transcendence degree over `k` are isomorphic over
  `k`;
* in either situation, a prescribed element `α ∈ E` transcendental over `k` may be sent to any
  prescribed element `z ∈ Ω` transcendental over `k`.

Over a countable field `k`, an uncountable algebraically closed field has transcendence degree
equal to its cardinality. Applied to `Ω = ℂ`, these statements extend a given embedding of a
countable field into `ℂ` to a field of cardinality at most the continuum.

## Main results

* `IsTranscendenceBasis.exists_algHom_apply_eq`: an algebra homomorphism sending a transcendence
  basis to a given algebraically independent family.
* `IsTranscendenceBasis.exists_algEquiv_apply_eq`: between algebraically closed fields, an
  isomorphism realising a bijection of transcendence bases.
* `TauCeti.IsAlgClosed.nonempty_algHom_of_lift_trdeg_le`,
  `TauCeti.IsAlgClosed.nonempty_algEquiv_of_lift_trdeg_eq`: homomorphisms and isomorphisms from
  transcendence degrees.
* `Transcendental.exists_isTranscendenceBasis_mem`: a transcendental element lies in a
  transcendence basis.
* `Transcendental.exists_algHom_apply_eq`, `Transcendental.exists_algEquiv_apply_eq`: the same,
  sending a transcendental element to a prescribed transcendental element.
* `TauCeti.IsAlgClosed.trdeg_eq_cardinalMk`: the transcendence degree of an uncountable
  algebraically closed field over a countable field is its cardinality.

The isomorphism statements specialise `IsTranscendenceBasis.exists_ringEquiv_comp_algebraMap`,
which follows Mathlib's `IsAlgClosed.equivOfTranscendenceBasis`; the homomorphism statements
replace its use of algebraic closures by Mathlib's `IsAlgClosed.lift`.

## References

* Serge Lang, *Algebra*, revised 3rd ed., Graduate Texts in Mathematics 211, Springer, 2002,
  Chapter VIII, §1 (transcendence bases).
* Pierre Deligne, *La conjecture de Weil. II*, Publications Mathématiques de l'IHÉS 52 (1980),
  Remarque (1.2.11).
-/

public section

universe u v

open Cardinal MvPolynomial Algebra

namespace IsTranscendenceBasis

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]

/-- If `v` is a transcendence basis of a domain `E` over `R` and `w` is an algebraically
independent family, indexed like `v`, in an algebraically closed `R`-algebra `Ω`, then some
`R`-algebra homomorphism `E →ₐ[R] Ω` sends each `v i` to `w i`. -/
theorem exists_algHom_apply_eq {E : Type*} [CommRing E] [IsDomain E] [Algebra R E] {ι : Type*}
    {v : ι → E} {w : ι → Ω} (hv : IsTranscendenceBasis R v) (hw : AlgebraicIndependent R w) :
    ∃ φ : E →ₐ[R] Ω, ∀ i, φ (v i) = w i := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R E)
  -- Evaluation at `w` on the subalgebra `R[v]`, identified with the polynomial ring on `v`.
  let ψ : Algebra.adjoin R (Set.range v) →ₐ[R] Ω := (aeval w).comp hv.1.repr
  have hψ : Function.Injective ψ :=
    (algebraicIndependent_iff_injective_aeval.1 hw).comp hv.1.aevalEquiv.symm.injective
  let : Algebra (Algebra.adjoin R (Set.range v)) Ω := ψ.toRingHom.toAlgebra
  have : Module.IsTorsionFree (Algebra.adjoin R (Set.range v)) Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hψ
  have := hv.isAlgebraic
  -- `E` is algebraic over `R[v]`, so `ψ` extends to `E`.
  let f : E →ₐ[Algebra.adjoin R (Set.range v)] Ω := IsAlgClosed.lift
  have hf (a : Algebra.adjoin R (Set.range v)) : f a = ψ a := f.commutes a
  refine ⟨{ f.toRingHom with commutes' := fun r ↦ (hf (algebraMap R _ r)).trans (ψ.commutes r) },
    fun i ↦ ?_⟩
  have hvi : v i ∈ Algebra.adjoin R (Set.range v) := Algebra.subset_adjoin (Set.mem_range_self i)
  have hrepr : hv.1.repr ⟨v i, hvi⟩ = X i :=
    algebraicIndependent_iff_injective_aeval.1 hv.1 (by simp)
  simpa [ψ, hrepr] using hf ⟨v i, hvi⟩

/-- If `v` and `w` are transcendence bases over `R` of the algebraically closed `R`-algebras `E`
and `Ω`, then each bijection `e` of their index types is realised by an `R`-algebra isomorphism
`E ≃ₐ[R] Ω` sending `v i` to `w (e i)`. -/
theorem exists_algEquiv_apply_eq {E : Type*} [Field E] [Algebra R E] [IsAlgClosed E]
    {ι κ : Type*} {v : ι → E} {w : κ → Ω} (hv : IsTranscendenceBasis R v)
    (hw : IsTranscendenceBasis R w) (e : ι ≃ κ) :
    ∃ φ : E ≃ₐ[R] Ω, ∀ i, φ (v i) = w (e i) := by
  obtain ⟨τ, hτ, hτv⟩ := hv.exists_ringEquiv_comp_algebraMap hw (RingEquiv.refl R) e
  exact ⟨AlgEquiv.ofRingEquiv (f := τ) fun r ↦ by simpa using RingHom.congr_fun hτ r, hτv⟩

end IsTranscendenceBasis

/-- An element transcendental over `R` lies in some transcendence basis over `R`. -/
theorem Transcendental.exists_isTranscendenceBasis_mem {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} (hx : Transcendental R x) :
    ∃ s : Set A, x ∈ s ∧ IsTranscendenceBasis R ((↑) : s → A) := by
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset (s := {x})
    ((algebraicIndependent_singleton_iff ⟨x, Set.mem_singleton x⟩).2 hx)
  exact ⟨s, hxs (Set.mem_singleton x), hs⟩

variable {k : Type*} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

namespace TauCeti.IsAlgClosed

/-- A domain `E` containing a field `k` maps over `k` to an algebraically closed extension
`Ω` of `k` whose transcendence degree over `k` is at least that of `E`. -/
theorem nonempty_algHom_of_lift_trdeg_le {E : Type u} [CommRing E] [IsDomain E] [Algebra k E]
    (h : Cardinal.lift.{v} (trdeg k E) ≤ Cardinal.lift.{u} (trdeg k Ω)) :
    Nonempty (E →ₐ[k] Ω) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k E
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis k Ω
  rw [← hs.cardinalMk_eq_trdeg, ← ht.cardinalMk_eq_trdeg] at h
  obtain ⟨f⟩ := lift_mk_le'.1 h
  obtain ⟨φ, -⟩ := hs.exists_algHom_apply_eq (ht.1.comp f f.injective)
  exact ⟨φ⟩

/-- Two algebraically closed extensions of `k` with the same transcendence degree over `k` are
isomorphic over `k`. -/
theorem nonempty_algEquiv_of_lift_trdeg_eq {E : Type u} [Field E] [Algebra k E] [IsAlgClosed E]
    (h : Cardinal.lift.{v} (trdeg k E) = Cardinal.lift.{u} (trdeg k Ω)) :
    Nonempty (E ≃ₐ[k] Ω) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k E
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis k Ω
  rw [← hs.cardinalMk_eq_trdeg, ← ht.cardinalMk_eq_trdeg] at h
  obtain ⟨e⟩ := lift_mk_eq'.1 h
  obtain ⟨φ, -⟩ := hs.exists_algEquiv_apply_eq ht e
  exact ⟨φ⟩

/-- The transcendence degree of an uncountable algebraically closed field `Ω` over a countable
field `k` is the cardinality of `Ω`. -/
theorem trdeg_eq_cardinalMk [Countable k] (hΩ : ℵ₀ < #Ω) : trdeg k Ω = #Ω := by
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis k Ω
  rw [← ht.cardinalMk_eq_trdeg]
  simpa using (_root_.IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht
    (mk_le_aleph0 (α := k)) hΩ).symm

end TauCeti.IsAlgClosed

namespace Transcendental

/-- If `trdeg k E ≤ trdeg k Ω` for a domain `E` containing `k`, then for elements `α ∈ E` and
`z ∈ Ω` transcendental over `k`, some `k`-algebra homomorphism `E →ₐ[k] Ω` sends `α` to `z`. -/
theorem exists_algHom_apply_eq {E : Type u} [CommRing E] [IsDomain E] [Algebra k E] {α : E}
    {z : Ω} (hα : Transcendental k α) (hz : Transcendental k z)
    (h : Cardinal.lift.{v} (trdeg k E) ≤ Cardinal.lift.{u} (trdeg k Ω)) :
    ∃ φ : E →ₐ[k] Ω, φ α = z := by
  classical
  obtain ⟨s, hαs, hs⟩ := hα.exists_isTranscendenceBasis_mem
  obtain ⟨t, hzt, ht⟩ := hz.exists_isTranscendenceBasis_mem
  rw [← hs.cardinalMk_eq_trdeg, ← ht.cardinalMk_eq_trdeg] at h
  obtain ⟨f⟩ := lift_mk_le'.1 h
  -- Compose with a transposition of `t` so that the embedding of bases sends `α` to `z`.
  let g : s ↪ t := f.trans (Equiv.swap (f ⟨α, hαs⟩) ⟨z, hzt⟩).toEmbedding
  obtain ⟨φ, hφ⟩ := hs.exists_algHom_apply_eq (ht.1.comp g g.injective)
  exact ⟨φ, by simpa [g] using hφ ⟨α, hαs⟩⟩

/-- If the algebraically closed extensions `E` and `Ω` of `k` have the same transcendence degree
over `k`, then for elements `α ∈ E` and `z ∈ Ω` transcendental over `k`, some isomorphism
`E ≃ₐ[k] Ω` sends `α` to `z`. -/
theorem exists_algEquiv_apply_eq {E : Type u} [Field E] [Algebra k E] [IsAlgClosed E] {α : E}
    {z : Ω} (hα : Transcendental k α) (hz : Transcendental k z)
    (h : Cardinal.lift.{v} (trdeg k E) = Cardinal.lift.{u} (trdeg k Ω)) :
    ∃ φ : E ≃ₐ[k] Ω, φ α = z := by
  classical
  obtain ⟨s, hαs, hs⟩ := hα.exists_isTranscendenceBasis_mem
  obtain ⟨t, hzt, ht⟩ := hz.exists_isTranscendenceBasis_mem
  rw [← hs.cardinalMk_eq_trdeg, ← ht.cardinalMk_eq_trdeg] at h
  obtain ⟨e⟩ := lift_mk_eq'.1 h
  -- Compose with a transposition of `t` so that the bijection of bases sends `α` to `z`.
  let e' : s ≃ t := e.trans (Equiv.swap (e ⟨α, hαs⟩) ⟨z, hzt⟩)
  obtain ⟨φ, hφ⟩ := hs.exists_algEquiv_apply_eq ht e'
  exact ⟨φ, by simpa [e'] using hφ ⟨α, hαs⟩⟩

end Transcendental
