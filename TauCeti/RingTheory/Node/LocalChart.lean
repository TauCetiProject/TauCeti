/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.CriticalChart
public import TauCeti.RingTheory.Node.Hypersurface
import TauCeti.RingTheory.FittingIdeal.BaseChange
import TauCeti.RingTheory.Kaehler.Hypersurface
import TauCeti.RingTheory.Localization.Away.Quotient
import TauCeti.RingTheory.Node.Hessian
import TauCeti.RingTheory.RingHom.Etale
import TauCeti.RingTheory.RingHom.Quotient

/-!
# The étale local chart of a nodal relative curve

Let `S` be an algebra over an arbitrary commutative ring `R`, presented with one more generator
than relations, as for a standard syntomic algebra of relative dimension one. Suppose that its
singular locus `S ⧸ Fitt₁(Ω[S⁄R])` is unramified over `R`, as for a nodal relative curve. Then
every point `q` of the singular locus has an étale neighbourhood that is étale over a node
`uv = h`, after an étale extension `R → R'` of the base: there are an étale `S`-algebra `T`, a
prime `Q` of `T` above `q`, and an étale `R'`-algebra map `R'[u, v] ⧸ (uv - h) → T` sending `u`
and `v` into `Q`.

This assembles three results. Zariski locally, `S` is a hypersurface `W ⧸ (f)` in a smooth
relative surface `W`
(`Algebra.Presentation.exists_hypersurface_localizationAway_of_formallyUnramified`).
Since the singular locus is unramified, `f` is critical with nondegenerate Hessian at every point
of the singular locus
(`Module.Basis.forall_mem_and_det_hessian_notMem_of_formallyUnramified`). At such a point the
hypersurface is étale locally a node after an étale extension of the base
(`Module.Basis.exists_etale_nodeAlgebra_hom_of_critical`).

## Main results

* `Algebra.Presentation.exists_etale_nodeAlgebra_hom_of_formallyUnramified`: a presented algebra
  with one more generator than relations and unramified singular locus is, étale locally around
  each point of its singular locus, étale over a node `uv = h` defined over an étale extension of
  the base.

## References

* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): the
  singular-locus criterion and étale local structure of families of nodal curves.
-/

public section

noncomputable section

open KaehlerDifferential MvPolynomial TauCeti

universe u v w t

namespace Algebra.Presentation

/-- If `W → T₀` is étale, `W ⧸ (f) ≅ S[1/a]` and `J` is the extension of `(f)` to `T₀`, then
`T₀ ⧸ J` is étale over `S` through `S → S[1/a] ≅ W ⧸ (f) → T₀ ⧸ J`. -/
private theorem etale_quotientMap_comp_localizationAway {R S : Type*} {W T₀ : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [CommRing W] [CommRing T₀] [Algebra R W]
    [Algebra W T₀] [Algebra.Etale W T₀] {f : W} {a : S}
    (e : (W ⧸ Ideal.span {f}) ≃ₐ[R] Localization.Away a) {J : Ideal T₀}
    (hJ : (Ideal.span {f}).map (algebraMap W T₀) = J) :
    (((Ideal.quotientMap J (algebraMap W T₀) (Ideal.map_le_iff_le_comap.1 hJ.le)).comp
      (e.symm : Localization.Away a →+* W ⧸ Ideal.span {f})).comp
        (algebraMap S (Localization.Away a))).Etale := by
  subst hJ
  have hS : (algebraMap S (Localization.Away a)).Etale := RingHom.etale_algebraMap.2 inferInstance
  have he : (e.symm : Localization.Away a →+* W ⧸ Ideal.span {f}).Etale :=
    .of_bijective e.symm.bijective
  have hW := RingHom.IsStableUnderBaseChange.quotientMap RingHom.Etale.isStableUnderBaseChange
    (algebraMap W T₀) (Ideal.span {f}) (RingHom.etale_algebraMap.2 inferInstance)
  exact (hW.comp he).comp hS

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S]
  [Algebra R S] [Algebra.EssFiniteType R S]
  [Algebra.FormallyUnramified R (S ⧸ fittingIdeal S Ω[S⁄R] 1)] [Finite ι] [Finite σ]

/-- Near a point `q` of the singular locus, `S` is a hypersurface `W ⧸ (f)` in a smooth relative
surface, up to inverting some `a ∉ q` (so that `q` is the contraction of its extension to
`S[1/a]`), and `f` is critical with nondegenerate Hessian at the point `P₀` of `W` above `q`. -/
private theorem exists_critical_hypersurface [Nonempty σ] (P : Presentation R S ι σ)
    (hP : Nat.card ι = 1 + Nat.card σ) (q : Ideal S) [q.IsPrime]
    (hq : fittingIdeal S Ω[S⁄R] 1 ≤ q) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Smooth R W)
      (bW : Module.Basis (Fin 2) W Ω[W⁄R]) (f : W) (a : S)
      (e : (W ⧸ Ideal.span {f}) ≃ₐ[R] Localization.Away a) (P₀ : Ideal W) (_ : P₀.IsPrime),
      (q.map (algebraMap S (Localization.Away a))).comap (algebraMap S _) = q ∧
      (∀ w, w ∈ P₀ ↔ e (Ideal.Quotient.mk _ w) ∈ q.map (algebraMap S _)) ∧ f ∈ P₀ ∧
      (∀ i, (bW.coord i).compDer (D R W) f ∈ P₀) ∧
      (hessian (fun i ↦ (bW.coord i).compDer (D R W)) f).det ∉ P₀ := by
  -- Reindexing the presentation by finite types in `Type` keeps `W` in the universe of `R`.
  obtain ⟨W, _, _, hW, bW, f, a, ha, ⟨e⟩⟩ :=
    (P.reindex (Finite.equivFin ι).symm (Finite.equivFin σ).symm
      ).exists_hypersurface_localizationAway_of_formallyUnramified (by simpa using hP) q
  have := hW.isStandardSmooth
  let Sa := Localization.Away a
  let B := W ⧸ Ideal.span {f}
  let qa : Ideal Sa := q.map (algebraMap S Sa)
  have : qa.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers a) Sa q ‹_›
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime a).2 ha)
  have hqa : qa.comap (algebraMap S Sa) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers a) Sa ‹_›
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime a).2 ha)
  let P₀ : Ideal W := (qa.comap e).comap (Ideal.Quotient.mk _)
  -- The singular locus of `W ⧸ (f)` is the localization of that of `S`, so it is unramified and
  -- contains the point above `q`.
  let ε : Sa →+* B := e.symm
  have hfit :
      fittingIdeal B Ω[B⁄R] 1 = (fittingIdeal S Ω[S⁄R] 1).map (ε.comp (algebraMap S Sa)) := by
    rw [fittingIdeal_kaehlerDifferential_eq_map_algEquiv e.symm,
      (isBaseChange_of_formallyEtale R S Sa).fittingIdeal_eq_map]
    exact Ideal.map_map (algebraMap S Sa) ε
  have : Algebra.FormallyUnramified R (B ⧸ fittingIdeal B Ω[B⁄R] (Fintype.card (Fin 2) - 1)) := by
    let I := fittingIdeal S Ω[S⁄R] 1
    have : Algebra.FormallyEtale (S ⧸ I) (Sa ⧸ I.map (algebraMap S Sa)) :=
      .of_isLocalization (Submonoid.powers (Ideal.Quotient.mk I a))
    have : IsScalarTower R (S ⧸ I) (Sa ⧸ I.map (algebraMap S Sa)) := .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R S (S ⧸ I), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.algebraMap_quotient_map_quotient, ← IsScalarTower.algebraMap_apply,
        Ideal.Quotient.mk_algebraMap]
    have : Algebra.FormallyUnramified R (Sa ⧸ I.map (algebraMap S Sa)) :=
      .comp R (S ⧸ I) _
    refine .of_equiv (Ideal.quotientEquivAlg (I.map (algebraMap S Sa)) _ e.symm ?_)
    simp only [Fintype.card_fin, Nat.reduceSub, hfit]
    exact (Ideal.map_map (algebraMap S Sa) ε).symm
  have hle : fittingIdeal B Ω[B⁄R] 1 ≤ qa.comap e := by
    rw [hfit, Ideal.map_le_iff_le_comap]
    intro x hx
    have hx' := hq hx
    rw [← hqa, Ideal.mem_comap] at hx'
    simpa [ε] using hx'
  -- So `f` is critical with nondegenerate Hessian at the point above `q`.
  have hcrit := bW.forall_mem_and_det_hessian_notMem_of_formallyUnramified f P₀
    (by simpa only [Fintype.card_fin] using Ideal.comap_mono hle)
  exact ⟨W, inferInstance, inferInstance, inferInstance, bW, f, a, e, P₀, inferInstance, hqa,
    fun _ ↦ Ideal.mem_comap.trans Ideal.mem_comap,
    by simp [P₀, Ideal.Quotient.mk_singleton_self], hcrit.1, hcrit.2⟩

/-- **The étale local chart of a nodal relative curve.** Let `S` have a presentation `P` over
`R` with one more generator than relations, and suppose that the singular locus
`S ⧸ Fitt₁(Ω[S⁄R])` is unramified over `R`. Let `q` be a prime of `S` in the singular locus.
Then there are an étale `R`-algebra `R'`, an étale `S`-algebra `T` which is also an
`R'`-algebra compatibly over `R`, a prime `Q` of `T` above `q`, `h ∈ R'`, and an étale
`R'`-algebra map `R'[u, v] ⧸ (uv - h) → T` sending both node coordinates into `Q`.

Standard syntomic algebras of relative dimension one have such presentations
(`TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.exists_presentation`). -/
theorem exists_etale_nodeAlgebra_hom_of_formallyUnramified (P : Presentation R S ι σ)
    (hP : Nat.card ι = 1 + Nat.card σ) (q : Ideal S) [q.IsPrime]
    (hq : fittingIdeal S Ω[S⁄R] 1 ≤ q) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (T : Type u) (_ : CommRing T) (_ : Algebra S T) (_ : Algebra.Etale S T)
      (_ : Algebra R' T) (_ : Algebra R T) (_ : IsScalarTower R S T)
      (_ : IsScalarTower R R' T) (Q : Ideal T) (_ : Q.IsPrime) (h : R')
      (φ : NodeAlgebra R' h →ₐ[R'] T),
      q = Q.comap (algebraMap S T) ∧ φ (NodeAlgebra.coord h 0) ∈ Q ∧
        φ (NodeAlgebra.coord h 1) ∈ Q ∧ φ.toRingHom.Etale := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · -- Without relations `S` is a polynomial ring in one variable, which has no singular point.
    refine absurd (top_le_iff.1 ?_) ‹q.IsPrime›.ne_top
    rwa [← P.fittingIdeal_kaehlerDifferential_eq_top (k := 1) (by simp [hP])]
  obtain ⟨W, _, _, _, bW, f, a, e, P₀, _, hqa, hP₀, hf₀, hf, hdet⟩ :=
    P.exists_critical_hypersurface hP q hq
  let Sa := Localization.Away a
  -- The hypersurface is étale locally a node `uv = h` over an étale extension of the base.
  obtain ⟨R', _, _, _, T₀, _, _, _, _, _, _, _, Q₀, _, h, s, t, φ, hPQ, hfQ, hs, ht, -,
      hφ₀, hφ₁, hφ⟩ := bW.exists_etale_nodeAlgebra_hom_of_critical f P₀ hf₀ hf hdet
  -- The chart is `T = T₀ ⧸ (f)`, étale over `S` through `S → S[1/a] ≅ W ⧸ (f) → T`.
  let J := Ideal.span {algebraMap W T₀ f}
  have hJ : (Ideal.span {f}).map (algebraMap W T₀) = J := by
    rw [Ideal.map_span, Set.image_singleton]
  let ψ : W ⧸ Ideal.span {f} →+* T₀ ⧸ J :=
    Ideal.quotientMap J (algebraMap W T₀) (Ideal.map_le_iff_le_comap.1 hJ.le)
  let : Algebra S (T₀ ⧸ J) := ((ψ.comp (e.symm : Sa →+* _)).comp (algebraMap S Sa)).toAlgebra
  have : Algebra.Etale S (T₀ ⧸ J) :=
    RingHom.etale_algebraMap.1 (etale_quotientMap_comp_localizationAway e hJ)
  have : IsScalarTower R S (T₀ ⧸ J) := .of_algebraMap_eq fun r ↦ by
    -- By construction, `algebraMap S T` is the composite `S → S[1/a] ≅ W ⧸ (f) → T`.
    change _ = ψ (e.symm (algebraMap S Sa (algebraMap R S r)))
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
      ← Ideal.Quotient.mk_algebraMap R (Ideal.span {f}), Ideal.quotientMap_mk,
      ← IsScalarTower.algebraMap_apply, Ideal.Quotient.mk_algebraMap]
  -- The prime of the chart lies above `q`.
  have hJQ : J ≤ Q₀ := (Ideal.span_singleton_le_iff_mem _).2 hfQ
  let Q := Q₀.map (Ideal.Quotient.mk J)
  have : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  have hψQ (y : W ⧸ Ideal.span {f}) : ψ y ∈ Q ↔ e y ∈ q.map (algebraMap S Sa) := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.quotientMap_mk, Ideal.mem_quotient_iff_mem hJQ, ← Ideal.mem_comap, ← hPQ, hP₀]
  refine ⟨R', inferInstance, inferInstance, inferInstance, T₀ ⧸ J, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, inferInstance,
    h, φ, ?_, ?_, ?_, hφ⟩
  · ext x
    -- By construction, `algebraMap S T` is the composite `S → S[1/a] ≅ W ⧸ (f) → T`.
    change x ∈ q ↔ ψ (e.symm (algebraMap S Sa x)) ∈ Q
    rw [hψQ, AlgEquiv.apply_symm_apply, ← Ideal.mem_comap, hqa]
  · rw [hφ₀]
    exact Ideal.mem_map_of_mem _ hs
  · rw [hφ₁]
    exact Ideal.mem_map_of_mem _ ht

end Algebra.Presentation
