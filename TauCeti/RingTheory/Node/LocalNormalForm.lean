/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FittingIdeal.Basic
public import TauCeti.RingTheory.Node.CriticalChart
public import TauCeti.RingTheory.Syntomic.StandardSyntomic
import TauCeti.RingTheory.FittingIdeal.BaseChange
import TauCeti.RingTheory.FittingIdeal.KaehlerDifferential
import TauCeti.RingTheory.Node.Cotangent.Basic
import TauCeti.RingTheory.Node.Hessian
import TauCeti.RingTheory.Node.Hypersurface
import TauCeti.RingTheory.RingHom.Quotient

/-!
# The étale local normal form of a nodal relative curve

Let `S` be an algebra over an arbitrary commutative ring `R`, presented with one more generator
than relations, for instance a standard syntomic algebra of relative dimension one, and suppose
that its singular locus `S ⧸ Fitt₁(Ω[S⁄R])` is unramified over `R`, as for a nodal relative
curve. This file shows that `S` is étale locally the node chart `R'[u, v] ⧸ (uv - h)` around
every point of its singular locus. More precisely, for every prime `q ⊇ Fitt₁(Ω[S⁄R])` of `S`
there are

* an étale `R`-algebra `R'` and an element `h ∈ R'`,
* an étale `S`-algebra `T` which is also an `R'`-algebra, compatibly over `R`, with a prime `Q`
  of `T` lying over `q`, and
* an étale `R'`-algebra map `R'[u, v] ⧸ (uv - h) → T` sending both coordinates into `Q`.

Geometrically, `Spec T → Spec S` is an étale neighbourhood of `q`, and it maps étale to the node
chart `Spec R'[u, v] ⧸ (uv - h)` over the étale extension `Spec R' → Spec R` of the base, sending
the point `Q` into the closed subscheme `u = v = 0` of the chart, which is `Spec R' ⧸ (h)`.

The proof assembles three results. Zariski locally around `q`, the algebra `S` is a hypersurface
`W ⧸ (f)` in a standard smooth relative surface `W` whose differentials have a basis: there is
`a ∉ q` with `S[1/a] ≃ W ⧸ (f)`
(`Algebra.Presentation.exists_hypersurface_localizationAway_of_formallyUnramified`). The
singular locus of `S[1/a]` is the localization of that of `S`, so it is again unramified, and
transporting it to `W ⧸ (f)` shows that `f` is critical with nondegenerate Hessian at the point
above `q` (`Module.Basis.forall_mem_and_det_hessian_notMem_of_formallyUnramified`). At such a
point the hypersurface `W ⧸ (f)` has an étale neighbourhood mapping étale to a node chart over an
étale extension of the base (`Module.Basis.exists_etale_quotient_nodeAlgebra_hom_of_critical`).
Composing with the étale map `S → S[1/a] ≃ W ⧸ (f)` gives the étale neighbourhood of `q`. When
the presentation has no relations, `S` has a single generator and its singular locus is empty.

## Main results

* `Algebra.Presentation.exists_etale_nodeAlgebra_hom_of_formallyUnramified`: the étale local
  normal form for a presentation with one more generator than relations.
* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.exists_etale_nodeAlgebra_hom`: the same
  for a standard syntomic algebra of relative dimension one.

## References

* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): the
  singular-locus criterion and the étale local structure of families of nodal curves.
-/

public section

noncomputable section

open KaehlerDifferential TauCeti

universe u

namespace Algebra.Presentation

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
  [Algebra.FormallyUnramified R (S ⧸ fittingIdeal S Ω[S⁄R] 1)] {ι σ : Type*} [Finite ι]
  [Finite σ]

/-- Near a point `q` of the singular locus, `S` is a hypersurface in a smooth relative surface
`W`: `S[1/a] ≃ W ⧸ (f)` for some `a`, and `f` has a nondegenerate critical point at the prime
`𝔭` of `W ⧸ (f)` which corresponds to `q` under `S → S[1/a] ≃ W ⧸ (f)`. -/
private theorem exists_hypersurface_critical [Nonempty σ] (P : Presentation R S ι σ)
    (hP : Nat.card ι = 1 + Nat.card σ) (q : Ideal S) [q.IsPrime]
    (hq : fittingIdeal S Ω[S⁄R] 1 ≤ q) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Smooth R W)
      (bW : Module.Basis (Fin 2) W Ω[W⁄R]) (f : W) (a : S)
      (e : (W ⧸ Ideal.span {f}) ≃ₐ[R] Localization.Away a) (𝔭 : Ideal (W ⧸ Ideal.span {f}))
      (_ : 𝔭.IsPrime),
      q = 𝔭.comap (e.symm.toRingHom.comp (algebraMap S _)) ∧
        (∀ i, (bW.coord i).compDer (D R W) f ∈ 𝔭.comap (Ideal.Quotient.mk _)) ∧
        (hessian (fun i ↦ (bW.coord i).compDer (D R W)) f).det ∉ 𝔭.comap (Ideal.Quotient.mk _) := by
  have : Nonempty (Fin (Nat.card σ)) := ⟨⟨0, Nat.card_pos⟩⟩
  obtain ⟨W, _, _, hW, bW, f, a, ha, ⟨e⟩⟩ :=
    exists_hypersurface_localizationAway_of_formallyUnramified
      (P.reindex (Finite.equivFin ι).symm (Finite.equivFin σ).symm) (by simpa using hP) q
  have := hW.isStandardSmooth
  let Sa := Localization.Away a
  set H := W ⧸ Ideal.span {f}
  -- The prime `q` survives in `S[1/a]`.
  have hdisj : Disjoint (Submonoid.powers a : Set S) q :=
    (Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).2 ha
  set qa := q.map (algebraMap S Sa)
  have := IsLocalization.isPrime_of_isPrime_disjoint (.powers a) Sa q ‹_› hdisj
  -- The singular locus of `W ⧸ (f) ≃ S[1/a]` is unramified and contained in `qa`.
  have hfitSa : fittingIdeal Sa Ω[Sa⁄R] 1 = (fittingIdeal S Ω[S⁄R] 1).map (algebraMap S Sa) :=
    (isBaseChange_of_formallyEtale R S Sa).fittingIdeal_eq_map 1
  have hfitH : fittingIdeal Sa Ω[Sa⁄R] 1 = (fittingIdeal H Ω[H⁄R] 1).map e :=
    fittingIdeal_kaehlerDifferential_eq_map_algEquiv e 1
  have : Algebra.FormallyUnramified R (Sa ⧸ fittingIdeal Sa Ω[Sa⁄R] 1) :=
    formallyUnramified_localization_quotient_fittingIdeal (K := R) (.powers a)
  have : Algebra.FormallyUnramified R (H ⧸ fittingIdeal H Ω[H⁄R] (Fintype.card (Fin 2) - 1)) :=
    .of_equiv (Ideal.quotientEquivAlg _ _ e hfitH).symm
  have hle : (fittingIdeal H Ω[H⁄R] (Fintype.card (Fin 2) - 1)).comap (Ideal.Quotient.mk _) ≤
      (qa.comap e).comap (Ideal.Quotient.mk _) := fun x hx ↦
    (hfitSa ▸ Ideal.map_mono hq :) (hfitH ▸ Ideal.mem_map_of_mem e hx)
  refine ⟨W, inferInstance, inferInstance, inferInstance, bW, f, a, e, qa.comap e, inferInstance,
    ?_, bW.forall_mem_and_det_hessian_notMem_of_formallyUnramified f _ hle⟩
  nth_rw 1 [← IsLocalization.under_map_of_isPrime_disjoint (.powers a) Sa ‹q.IsPrime› hdisj]
  ext x
  simp [qa, Sa]

/-- **The étale local normal form of a nodal relative curve.** Let `S` have a presentation `P`
over an arbitrary commutative ring `R` with one more generator than relations, and suppose that
the singular locus `S ⧸ Fitt₁(Ω[S⁄R])` is unramified over `R`. Let `q` be a prime of `S` in the
singular locus. Then there are an étale `R`-algebra `R'`, an étale `S`-algebra `T` which is an
`R'`-algebra compatibly over `R`, a prime `Q` of `T` lying over `q`, an element `h ∈ R'`, and an
étale `R'`-algebra map `φ : R'[u, v] ⧸ (uv - h) → T` sending both coordinates into `Q`. -/
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
  -- Without relations `S` is smooth, so its singular locus is empty.
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · exact absurd (top_le_iff.1 (P.fittingIdeal_kaehlerDifferential_eq_top
      (by rw [hP, Nat.card_of_isEmpty]) ▸ hq)) Ideal.IsPrime.ne_top'
  -- Near `q`, `S` is a hypersurface `W ⧸ (f)` with a nondegenerate critical point above `q`.
  obtain ⟨W, _, _, _, bW, f, a, e, 𝔭, _, hq𝔭, hcrit, hdet⟩ := exists_hypersurface_critical P hP q hq
  -- The hypersurface is étale locally a node chart; compose with `S → S[1/a] ≃ W ⧸ (f)`.
  obtain ⟨R', _, _, _, T, _, _, hHT, _, _, _, _, Q, hQ, h, φ, h𝔭Q, hφ₀, hφ₁, hφ⟩ :=
    bW.exists_etale_quotient_nodeAlgebra_hom_of_critical f 𝔭 hcrit hdet
  let : Algebra S T :=
    ((algebraMap (W ⧸ Ideal.span {f}) T).comp (e.symm.toRingHom.comp (algebraMap S _))).toAlgebra
  refine ⟨R', inferInstance, inferInstance, inferInstance, T, inferInstance, inferInstance,
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _
        (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway a))
        (RingHom.Etale.of_bijective e.symm.bijective))
      (RingHom.etale_algebraMap.2 hHT),
    inferInstance, inferInstance, .of_algebraMap_eq fun r ↦ ?_, inferInstance, Q, hQ, h, φ,
    by rw [hq𝔭, h𝔭Q, Ideal.comap_comap, RingHom.algebraMap_toAlgebra], hφ₀, hφ₁, hφ⟩
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply R S (Localization.Away a), RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

end Algebra.Presentation

namespace TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
  [Algebra.FormallyUnramified R (S ⧸ fittingIdeal S Ω[S⁄R] 1)]
  [IsStandardSyntomicOfRelativeDimension 1 R S]

/-- **The étale local normal form of a nodal relative curve.** Let `S` be a standard syntomic
`R`-algebra of relative dimension one whose singular locus `S ⧸ Fitt₁(Ω[S⁄R])` is unramified over
`R`, and let `q` be a prime of `S` in the singular locus. Then there are an étale `R`-algebra `R'`,
an étale `S`-algebra `T` which is an `R'`-algebra compatibly over `R`, a prime `Q` of `T` lying over
`q`, an element `h ∈ R'`, and an étale `R'`-algebra map `φ : R'[u, v] ⧸ (uv - h) → T` sending both
coordinates into `Q`. -/
theorem exists_etale_nodeAlgebra_hom (q : Ideal S) [q.IsPrime]
    (hq : fittingIdeal S Ω[S⁄R] 1 ≤ q) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : _root_.Algebra R R') (_ : _root_.Algebra.Etale R R')
      (T : Type u) (_ : CommRing T) (_ : _root_.Algebra S T) (_ : _root_.Algebra.Etale S T)
      (_ : _root_.Algebra R' T) (_ : _root_.Algebra R T) (_ : IsScalarTower R S T)
      (_ : IsScalarTower R R' T) (Q : Ideal T) (_ : Q.IsPrime) (h : R')
      (φ : NodeAlgebra R' h →ₐ[R'] T),
      q = Q.comap (algebraMap S T) ∧ φ (NodeAlgebra.coord h 0) ∈ Q ∧
        φ (NodeAlgebra.coord h 1) ∈ Q ∧ φ.toRingHom.Etale := by
  obtain ⟨ι, σ, _, _, P, hP⟩ := exists_presentation (n := 1) (R := R) (S := S)
  exact P.exists_etale_nodeAlgebra_hom_of_formallyUnramified hP q hq

end TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension
