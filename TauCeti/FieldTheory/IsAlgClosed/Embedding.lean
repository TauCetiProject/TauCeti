/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IsAlgClosed.Automorphism

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

Over a countable field `k`, an uncountable integral domain over `k` has transcendence degree equal
to its cardinality. Applied to `Ω = ℂ`, these statements extend a given embedding of a countable
field into `ℂ` to a field of cardinality at most the continuum.

## Main results

* `IsTranscendenceBasis.exists_algHom_apply_eq`: an algebra homomorphism sending a transcendence
  basis to a given algebraically independent family.
* `IsTranscendenceBasis.exists_algEquiv_apply_eq`: between algebraically closed fields, an
  isomorphism realising a bijection of transcendence bases.
* `TauCeti.IsAlgClosed.exists_algHom_injective_of_lift_trdeg_le`,
  `TauCeti.IsAlgClosed.nonempty_algHom_of_lift_trdeg_le`,
  `TauCeti.IsAlgClosed.nonempty_algEquiv_of_lift_trdeg_eq`: injective homomorphisms and
  isomorphisms from transcendence degrees over a commutative ring with faithful actions.
* `Transcendental.exists_algHom_apply_eq`, `Transcendental.exists_algEquiv_apply_eq`: the same,
  sending a transcendental element to a prescribed transcendental element.
* `TauCeti.IsAlgClosed.exists_ringEquiv_extend`: Steinitz extension of injective embeddings of a
  countable commutative ring into two uncountable algebraically closed fields of the same
  cardinality.
* `TauCeti.IsAlgClosed.exists_ringHom_extend_of_cardinal_le`: extension of an embedding of a
  countable commutative ring into an uncountable algebraically closed field `E` along an embedding
  into an integral domain `K` with `#K ≤ #E`, yielding an injective ring homomorphism `K →+* E`.

The isomorphism statements specialise `IsTranscendenceBasis.exists_ringEquiv_comp_algebraMap`,
which follows Mathlib's `IsAlgClosed.equivOfTranscendenceBasis`; the homomorphism statements
replace its use of algebraic closures by Mathlib's `IsAlgClosed.lift`.

## References

* E. Steinitz, *Algebraische Theorie der Körper*, J. Reine Angew. Math. **137** (1910), 167–309.
* Serge Lang, *Algebra*, revised 3rd ed., Graduate Texts in Mathematics 211, Springer, 2002,
  Chapter VIII, §1 (transcendence bases).
* Pierre Deligne, *La conjecture de Weil. II*, Publications Mathématiques de l'IHÉS 52 (1980),
  Remarque (1.2.11).
* `exists_ringEquiv_extend` and `exists_ringHom_extend_of_cardinal_le` adapted from
  `New.exists_ringEquiv_extend` and `New.exists_ringHom_complex_extend` in
  `src/Lib/General/Geometry/GaloisCovers.lean` of `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
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

variable {k : Type*} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

namespace TauCeti.IsAlgClosed

/-- A domain `E` over a commutative ring `R` acting faithfully on `E` and an algebraically closed
field `Ω` embeds over `R` into `Ω` whenever `trdeg R E ≤ trdeg R Ω`. -/
theorem exists_algHom_injective_of_lift_trdeg_le {R : Type*} {E : Type u} {Ω : Type v}
    [CommRing R] [CommRing E] [IsDomain E] [Algebra R E] [FaithfulSMul R E]
    [Field Ω] [Algebra R Ω] [IsAlgClosed Ω] [FaithfulSMul R Ω]
    (h : Cardinal.lift.{v} (trdeg R E) ≤ Cardinal.lift.{u} (trdeg R Ω)) :
    ∃ φ : E →ₐ[R] Ω, Function.Injective φ := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R E)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R E
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R Ω
  obtain ⟨f⟩ := hs.nonempty_embedding_of_lift_trdeg_le ht h
  have hw : AlgebraicIndependent R (((↑) : t → Ω) ∘ f) := ht.1.comp f f.injective
  obtain ⟨φ, hφ⟩ := hs.exists_algHom_apply_eq hw
  let A := Algebra.adjoin R (Set.range ((↑) : s → E))
  have hφA : (φ.comp A.val).comp hs.1.aevalEquiv.toAlgHom = aeval (((↑) : t → Ω) ∘ f) :=
    MvPolynomial.algHom_ext fun i ↦ by simpa using hφ i
  have hA_inj : Function.Injective (φ.comp A.val) := by
    have hcomp : Function.Injective ((φ.comp A.val) ∘ hs.1.aevalEquiv) := by
      have heq : ((φ.comp A.val) ∘ hs.1.aevalEquiv : MvPolynomial s R → Ω) =
          aeval (((↑) : t → Ω) ∘ f) := congrArg DFunLike.coe hφA
      rw [heq]
      exact algebraicIndependent_iff_injective_aeval.1 hw
    exact (Function.Injective.of_comp_iff' _ hs.1.aevalEquiv.bijective).1 hcomp
  algebraize [φ.toRingHom]
  have := hs.isAlgebraic
  have hinj : Function.Injective (algebraMap E Ω) :=
    Algebra.IsAlgebraic.injective_tower_top E (R := ↥A) fun a b hab ↦ hA_inj <| by
      simpa [IsScalarTower.algebraMap_apply (↥A) E Ω, RingHom.algebraMap_toAlgebra] using hab
  exact ⟨φ, by
    simpa only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hinj⟩

/-- A domain `E` over a commutative ring `R` acting faithfully on `E` and an algebraically closed
field `Ω` maps over `R` to `Ω` whenever `trdeg R E ≤ trdeg R Ω`. -/
theorem nonempty_algHom_of_lift_trdeg_le {R : Type*} {E : Type u} {Ω : Type v}
    [CommRing R] [CommRing E] [IsDomain E] [Algebra R E] [FaithfulSMul R E]
    [Field Ω] [Algebra R Ω] [IsAlgClosed Ω] [FaithfulSMul R Ω]
    (h : Cardinal.lift.{v} (trdeg R E) ≤ Cardinal.lift.{u} (trdeg R Ω)) :
    Nonempty (E →ₐ[R] Ω) :=
  let ⟨φ, _⟩ := exists_algHom_injective_of_lift_trdeg_le h; ⟨φ⟩

/-- Two algebraically closed fields over a commutative ring `R` acting faithfully on both with the
same transcendence degree over `R` are isomorphic over `R`. -/
theorem nonempty_algEquiv_of_lift_trdeg_eq {R : Type*} {E : Type u} {Ω : Type v}
    [CommRing R] [Field E] [Algebra R E] [IsAlgClosed E] [FaithfulSMul R E]
    [Field Ω] [Algebra R Ω] [IsAlgClosed Ω] [FaithfulSMul R Ω]
    (h : Cardinal.lift.{v} (trdeg R E) = Cardinal.lift.{u} (trdeg R Ω)) :
    Nonempty (E ≃ₐ[R] Ω) := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R E)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R E
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R Ω
  obtain ⟨e⟩ := hs.nonempty_equiv_of_lift_trdeg_eq ht h
  obtain ⟨φ, -⟩ := hs.exists_algEquiv_apply_eq ht e
  exact ⟨φ⟩

/-- **Steinitz extension for countable subrings.** Let `K` be a countable commutative ring, `E` and
`L` uncountable algebraically closed fields of the same cardinality, and `f : K →+* E`,
`g : K →+* L` injective ring homomorphisms. Then there is a ring isomorphism `σ : E ≃+* L`
satisfying `σ (f a) = g a` for every `a : K`. -/
theorem exists_ringEquiv_extend {E : Type u} {L : Type v} {K : Type*} [Field E] [IsAlgClosed E]
    [Field L] [IsAlgClosed L] [CommRing K] [Countable K]
    (hE : ℵ₀ < #E) (h_mk : Cardinal.lift.{v} #E = Cardinal.lift.{u} #L)
    (f : K →+* E) (g : K →+* L) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : E ≃+* L, ∀ a : K, σ (f a) = g a := by
  algebraize [f, g]
  have : FaithfulSMul K E := (faithfulSMul_iff_algebraMap_injective K E).2 <| by
    simpa only [RingHom.algebraMap_toAlgebra] using hf
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 <| by
    simpa only [RingHom.algebraMap_toAlgebra] using hg
  have hL : ℵ₀ < #L := Cardinal.aleph0_lt_lift.1 (h_mk ▸ Cardinal.aleph0_lt_lift.2 hE)
  obtain ⟨φ⟩ := nonempty_algEquiv_of_lift_trdeg_eq (R := K) (E := E) (Ω := L) <| by
    rw [TauCeti.trdeg_eq_cardinalMk hE, TauCeti.trdeg_eq_cardinalMk hL, h_mk]
  exact ⟨φ.toRingEquiv, fun a ↦ by
    simpa only [AlgEquiv.coe_toRingEquiv, RingHom.algebraMap_toAlgebra] using φ.commutes a⟩

/-- Let `D` be a countable commutative ring, `E` an uncountable algebraically closed field, `K` an
integral domain with `#K ≤ #E`, and `f : D →+* K`, `φ : D →+* E` injective ring homomorphisms.
Then `φ` extends along `f` to an injective ring homomorphism `ψ : K →+* E`. -/
theorem exists_ringHom_extend_of_cardinal_le {D : Type*} {K : Type u} {E : Type v} [CommRing D]
    [Countable D] [CommRing K] [IsDomain K] [Field E] [IsAlgClosed E] (hE : ℵ₀ < #E)
    {f : D →+* K} {φ : D →+* E} (hf : Function.Injective f) (hφ : Function.Injective φ)
    (h_le : Cardinal.lift.{v} #K ≤ Cardinal.lift.{u} #E) :
    ∃ ψ : K →+* E, Function.Injective ψ ∧ ψ.comp f = φ := by
  algebraize [f, φ]
  have : FaithfulSMul D K := (faithfulSMul_iff_algebraMap_injective D K).2 <| by
    simpa only [RingHom.algebraMap_toAlgebra] using hf
  have : FaithfulSMul D E := (faithfulSMul_iff_algebraMap_injective D E).2 <| by
    simpa only [RingHom.algebraMap_toAlgebra] using hφ
  have : Nontrivial D := f.domain_nontrivial
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis D K
  have htr : Cardinal.lift.{v} (trdeg D K) ≤ Cardinal.lift.{u} (trdeg D E) := by
    rw [← hs.cardinalMk_eq_trdeg, TauCeti.trdeg_eq_cardinalMk hE]
    exact (lift_le.2 (mk_set_le s)).trans h_le
  obtain ⟨ψ, hψ_inj⟩ := exists_algHom_injective_of_lift_trdeg_le htr
  exact ⟨ψ.toRingHom, hψ_inj, RingHom.ext fun d ↦ by
    simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RingHom.algebraMap_toAlgebra] using ψ.commutes d⟩

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
  obtain ⟨f⟩ := hs.nonempty_embedding_of_lift_trdeg_le ht h
  -- Redefine the embedding of bases at `α` so that it sends `α` to `z`.
  let g : s ↪ t := f.setValue ⟨α, hαs⟩ ⟨z, hzt⟩
  obtain ⟨φ, hφ⟩ := hs.exists_algHom_apply_eq (ht.1.comp g g.injective)
  exact ⟨φ, (hφ ⟨α, hαs⟩).trans (congrArg Subtype.val (f.setValue_eq _ _))⟩

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
  obtain ⟨e⟩ := hs.nonempty_equiv_of_lift_trdeg_eq ht h
  -- Redefine the bijection of bases at `α` so that it sends `α` to `z`.
  obtain ⟨φ, hφ⟩ := hs.exists_algEquiv_apply_eq ht (e.setValue ⟨α, hαs⟩ ⟨z, hzt⟩)
  exact ⟨φ, (hφ ⟨α, hαs⟩).trans (congrArg Subtype.val (e.setValue_eq _ _))⟩

end Transcendental
