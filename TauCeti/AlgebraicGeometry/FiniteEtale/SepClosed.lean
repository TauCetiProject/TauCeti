/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.FieldTheory.IsSepClosed
import TauCeti.Algebra.Algebra.Pi
import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.FieldTheory.IsSepClosed

/-!
# Points and fibres of finite étale schemes over a separably closed field

Every finite étale scheme `X` over a separably closed field `K` splits over `K` itself as the
spectrum of a finite product `Fin n → K` of copies of `K`
(`AlgebraicGeometry.Scheme.Hom.exists_iso_Spec_pi_of_isSepClosed`), combining
`AlgebraicGeometry.Scheme.Hom.exists_finiteEtale_algebra` with
`Algebra.IsFiniteSplit.nonempty_algEquiv_fun`. Via
`Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum` and `Pi.evalAlgHomEquiv`, the underlying space of
`X` is in bijection with `Fin n`, so the cardinality of `X` equals its rank over `Spec K`
(`AlgebraicGeometry.Scheme.Hom.natCard_eq_finrank_of_isSepClosed`).

Passing to scheme-theoretic fibres (`AlgebraicGeometry.Scheme.Hom.fiberHomeo` and
`AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd`), for any
finite étale morphism `p : E ⟶ S` and any point `s : S` with separably closed residue field, the
set-theoretic fibre `{e : E // p e = s}` has cardinality `p.finrank s`
(`AlgebraicGeometry.Scheme.Hom.natCard_preimage_eq_finrank_of_isSepClosed_residueField`); this
applies in particular whenever `S` is unramified (for instance étale) over a separably closed field
(`AlgebraicGeometry.Scheme.Hom.natCard_preimage_eq_finrank_of_isSepClosed`), without assuming `S` is
finite over `K` or that `p` has constant rank across `S`.

## References

* [The Stacks Project, Tag 03QR](https://stacks.math.columbia.edu/tag/03QR): schemes étale over a
  field.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Every finite étale scheme over a separably closed field splits over the ground field.** -/
theorem exists_iso_Spec_pi_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    ∃ (n : ℕ) (e : X ≅ Spec (.of (Fin n → K))),
      e.hom ≫ Spec.algebraMap K (Fin n → K) = f := by
  obtain ⟨A, ⟨e₀⟩⟩ := f.exists_finiteEtale_algebra
  obtain ⟨n, ⟨a⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K A.obj
  have hw : e₀.hom.left ≫ f = Spec.algebraMap K A.obj := Over.w e₀.hom
  let e : X ≅ Spec (.of (Fin n → K)) :=
    ((Over.forget _).mapIso e₀).symm ≪≫
      Scheme.Spec.mapIso a.toRingEquiv.toCommRingCatIso.symm.op
  refine ⟨n, e, ?_⟩
  have hmap : Scheme.Spec.map a.toRingEquiv.toCommRingCatIso.symm.op.hom ≫
      Spec.algebraMap K (Fin n → K) = Spec.algebraMap K A.obj := by
    simp only [Iso.op_hom, Iso.symm_hom, Scheme.Spec_map, Spec.algebraMap, ← Spec.map_comp]
    congr 1
    ext r
    exact a.symm.commutes r
  have he_hom : e.hom =
      e₀.inv.left ≫ Scheme.Spec.map a.toRingEquiv.toCommRingCatIso.symm.op.hom := by
    simp [e]
  rw [he_hom, Category.assoc, hmap]
  simp [← hw, ← Over.comp_left_assoc]

/-- **The points of a finite étale scheme over a separably closed field number its rank.** -/
theorem natCard_eq_finrank_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] (s : Spec (.of K)) :
    Nat.card X = f.finrank s := by
  obtain ⟨n, e, he⟩ := f.exists_iso_Spec_pi_of_isSepClosed
  let eqv : Fin n ≃ ↥(Spec (.of (Fin n → K))) :=
    (Pi.evalAlgHomEquiv K (Fin n)).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K (Fin n → K))
  have hcard : Nat.card X = n := by
    rw [Nat.card_congr e.hom.homeomorph.toEquiv, ← Nat.card_congr eqv, Nat.card_fin]
  have hef : e.inv ≫ f = Spec.algebraMap K (Fin n → K) := by simp [← he]
  have hfin : (Spec.algebraMap K (Fin n → K)).finrank s = n := by
    rw [Spec.algebraMap, finrank_SpecMap_algebraMap K (Fin n → K) s,
      congrFun Module.rankAtStalk_eq_finrank_of_free s]
    exact (Module.finrank_pi (R := K)).trans (Fintype.card_fin n)
  rw [hcard, ← finrank_comp_left_of_isIso e.inv f, hef, hfin]

/-- **The points in the fibre of a finite étale morphism over a point with separably closed residue
field number its rank at that point.** -/
theorem natCard_preimage_eq_finrank_of_isSepClosed_residueField
    {S E : Scheme.{u}} (p : E ⟶ S) [IsFinite p] [Etale p]
    (s : S) [IsSepClosed (S.residueField s)] :
    Nat.card {e : E // p e = s} = p.finrank s := by
  let pt : Spec (S.residueField s) := IsLocalRing.closedPoint (S.residueField s)
  have hcard : Nat.card {e : E // p e = s} = Nat.card (p.fiber s) :=
    (Nat.card_congr (p.fiberHomeo s).toEquiv).symm
  have hfib : Nat.card (p.fiber s) = (pullback.snd p (S.fromSpecResidueField s)).finrank pt :=
    (pullback.snd p (S.fromSpecResidueField s)).natCard_eq_finrank_of_isSepClosed
      (K := S.residueField s) pt
  have hrank : (pullback.snd p (S.fromSpecResidueField s)).finrank pt = p.finrank s := by
    rw [Scheme.Hom.finrank_pullback_snd p (S.fromSpecResidueField s) pt,
      Scheme.fromSpecResidueField_apply]
  exact hcard.trans (hfib.trans hrank)

/-- **The points in each fibre of a finite étale morphism over an unramified scheme over a
separably closed field number its rank at the base point.** -/
theorem natCard_preimage_eq_finrank_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    {S E : Scheme.{u}} (p : E ⟶ S) [IsFinite p] [Etale p]
    (f : S ⟶ Spec (.of K)) [FormallyUnramified f] [LocallyOfFiniteType f] (s : S) :
    Nat.card {e : E // p e = s} = p.finrank s := by
  have : (f s).asIdeal.IsMaximal :=
    (Subsingleton.elim (f s) (IsLocalRing.closedPoint K)) ▸ IsLocalRing.maximalIdeal.isMaximal K
  have hbij : Function.Bijective (algebraMap K (f s).asIdeal.ResidueField) :=
    ⟨RingHom.injective _, (Ideal.bijective_algebraMap_quotient_residueField (f s).asIdeal).2.comp
      Ideal.Quotient.mk_surjective⟩
  have : IsSepClosed (f s).asIdeal.ResidueField :=
    IsSepClosed.of_ringEquiv (RingEquiv.ofBijective _ hbij)
  have : IsSepClosed ((Spec (.of K)).residueField (f.base s)) :=
    IsSepClosed.of_ringEquiv (Spec.residueFieldIso (.of K) (f s)).commRingCatIsoToRingEquiv.symm
  let : Algebra ((Spec (.of K)).residueField (f.base s)) (S.residueField s) :=
    (f.residueFieldMap s).hom.toAlgebra
  have : IsSepClosed (S.residueField s) :=
    IsSepClosed.of_ringEquiv (RingEquiv.ofBijective _
      (IsSepClosed.algebraMap_bijective ((Spec (.of K)).residueField (f.base s))
        (S.residueField s)))
  exact p.natCard_preimage_eq_finrank_of_isSepClosed_residueField s

end AlgebraicGeometry.Scheme.Hom
