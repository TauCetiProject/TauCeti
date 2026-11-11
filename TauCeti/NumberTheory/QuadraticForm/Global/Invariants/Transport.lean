/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Invariants.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.Transport
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Transport of systems of local quadratic-form invariants

A field isomorphism transports a global discriminant and reindexes the finite Hasse signs and
real positive indices along the induced bijections of places. This file defines that operation
on `GlobalFormInvariants`, proves its inverse and composition laws, and shows that it preserves
admissibility. In particular the rank-two exception is tested at the corresponding finite place:
its local discriminant is transported along the isomorphism of adic completions.

The construction uses `RingHom.squareClassMap`, `HeightOneSpectrum.equivOfRingEquiv`,
`InfinitePlace.realEquivOfRingEquiv`, and `HeightOneSpectrum.adicCompletionCongr`. No choice of a
presentation of a form or of representatives of square classes enters the construction.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M]

/-- Transport a system of invariants along a field isomorphism, mapping the global discriminant
and moving each local invariant to the corresponding place. -/
def map (I : GlobalFormInvariants K) (e : K ≃+* L) : GlobalFormInvariants L where
  rank := I.rank
  discr := e.toRingHom.squareClassMap I.discr
  finiteHasse := I.finiteHasse ∘ (HeightOneSpectrum.equivOfRingEquiv
    (RingOfIntegers.mapRingEquiv e)).symm
  realPositiveIndex := I.realPositiveIndex ∘ (InfinitePlace.realEquivOfRingEquiv e).symm

/-- Transport preserves rank. -/
@[simp]
theorem map_rank (I : GlobalFormInvariants K) (e : K ≃+* L) : (I.map e).rank = I.rank :=
  (rfl)

/-- Transport maps the global discriminant along the field isomorphism. -/
@[simp]
theorem map_discr (I : GlobalFormInvariants K) (e : K ≃+* L) :
    (I.map e).discr = e.toRingHom.squareClassMap I.discr :=
  (rfl)

/-- The transported finite Hasse sign is read at the inverse image of the place. -/
@[simp]
theorem map_finiteHasse (I : GlobalFormInvariants K) (e : K ≃+* L)
    (v : HeightOneSpectrum (𝓞 L)) :
    (I.map e).finiteHasse v = I.finiteHasse
      ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm v) :=
  (rfl)

/-- The transported positive index is read at the inverse image of the real place. -/
@[simp]
theorem map_realPositiveIndex (I : GlobalFormInvariants K) (e : K ≃+* L)
    (w : {w : InfinitePlace L // w.IsReal}) :
    (I.map e).realPositiveIndex w =
      I.realPositiveIndex ((InfinitePlace.realEquivOfRingEquiv e).symm w) :=
  (rfl)

/-- At corresponding finite places the Hasse signs agree. -/
theorem map_finiteHasse_equivOfRingEquiv (I : GlobalFormInvariants K) (e : K ≃+* L)
    (v : HeightOneSpectrum (𝓞 K)) :
    (I.map e).finiteHasse
        (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) =
      I.finiteHasse v := by
  simp only [map_finiteHasse, Equiv.symm_apply_apply]

/-- At corresponding real places the positive indices agree. -/
theorem map_realPositiveIndex_realEquivOfRingEquiv (I : GlobalFormInvariants K) (e : K ≃+* L)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (I.map e).realPositiveIndex (InfinitePlace.realEquivOfRingEquiv e w) =
      I.realPositiveIndex w := by
  simp only [map_realPositiveIndex, Equiv.symm_apply_apply]

/-- Transport along the identity preserves the whole system. -/
@[simp]
theorem map_refl (I : GlobalFormInvariants K) : I.map (RingEquiv.refl K) = I := by
  apply GlobalFormInvariants.ext
  · rfl
  · simp
  · funext v
    simp only [map_finiteHasse, RingOfIntegers.mapRingEquiv_refl,
      HeightOneSpectrum.equivOfRingEquiv_refl, Equiv.refl_symm, Equiv.refl_apply]
  · funext w
    simp

/-- Transport along successive field isomorphisms agrees with transport along their composite. -/
@[simp]
theorem map_map (I : GlobalFormInvariants K) (e : K ≃+* L) (f : L ≃+* M) :
    (I.map e).map f = I.map (e.trans f) := by
  ext
  · rfl
  · exact (LinearMap.congr_fun (RingHom.squareClassMap_comp f.toRingHom e.toRingHom)
      I.discr).symm
  · simp only [map_finiteHasse, RingOfIntegers.mapRingEquiv_trans,
      HeightOneSpectrum.equivOfRingEquiv_trans, Equiv.symm_trans_apply]
  · simp only [map_realPositiveIndex, InfinitePlace.realEquivOfRingEquiv_symm,
      InfinitePlace.realEquivOfRingEquiv_trans_apply, RingEquiv.symm_trans]

/-- Transporting back along the inverse field isomorphism recovers the system. -/
theorem map_symm_map (I : GlobalFormInvariants K) (e : K ≃+* L) :
    (I.map e).map e.symm = I := by
  rw [map_map]
  simp

/-- At corresponding real places, transport leaves the localized discriminant unchanged. -/
theorem discrAtRealPlace_map (I : GlobalFormInvariants K) (e : K ≃+* L)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (I.map e).discrAtRealPlace (InfinitePlace.realEquivOfRingEquiv e w) =
      I.discrAtRealPlace w := by
  simp only [discrAtRealPlace_def, map_discr]
  rw [← LinearMap.comp_apply, ← RingHom.squareClassMap_comp]
  have h : (embedding_of_isReal (InfinitePlace.realEquivOfRingEquiv e w).2).comp
      e.toRingHom = embedding_of_isReal w.2 := by
    ext x
    simp
  rw [h]

/-- At corresponding finite places, the localized discriminant is carried by the induced
isomorphism of adic completions. -/
theorem discrAtFinitePlace_map (I : GlobalFormInvariants K) (e : K ≃+* L)
    (v : HeightOneSpectrum (𝓞 K)) :
    let w := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v
    let he : ∀ x, w.valuation L (e x) = v.valuation K x := fun x ↦ by
      dsimp only [w]
      simpa only [RingOfIntegers.ringEquivOfRingEquiv_mapRingEquiv] using
        valuation_ringEquivOfRingEquiv (K := K) (K' := L)
        (RingOfIntegers.mapRingEquiv e)
        (asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) x
    (I.map e).discrAtFinitePlace w =
      (adicCompletionCongr v w e he).toRingHom.squareClassMap (I.discrAtFinitePlace v) := by
  dsimp only
  simp only [discrAtFinitePlace_def, map_discr]
  simp only [← LinearMap.comp_apply, ← RingHom.squareClassMap_comp]
  apply congrArg (fun f : K →+* (HeightOneSpectrum.equivOfRingEquiv
    (RingOfIntegers.mapRingEquiv e) v).adicCompletion L ↦ f.squareClassMap I.discr)
  ext x
  simp

/-- The binary exceptional discriminant is preserved at corresponding finite places. -/
theorem discrAtFinitePlace_map_eq_neg_one_iff (I : GlobalFormInvariants K) (e : K ≃+* L)
    (v : HeightOneSpectrum (𝓞 K)) :
    (I.map e).discrAtFinitePlace
        (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) = squareClass (-1) ↔
      I.discrAtFinitePlace v = squareClass (-1) := by
  rw [discrAtFinitePlace_map]
  generalize adicCompletionCongr v
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) e _ = f
  have h := f.squareClassEquiv.injective.eq_iff
    (a := I.discrAtFinitePlace v) (b := squareClass (-1))
  have hneg : Units.map f.toRingHom.toMonoidHom (-1) = -1 := Units.map_neg_one f.toRingHom
  simpa only [RingEquiv.squareClassEquiv_apply, RingHom.squareClassMap_apply, hneg] using h

/-- Transport preserves the total Hasse product, including when the finite signs have infinite
support (in which case `finprod` uses its usual convention). -/
@[simp]
theorem hasseProduct_map (I : GlobalFormInvariants K) (e : K ≃+* L) :
    (I.map e).hasseProduct = I.hasseProduct := by
  classical
  simp only [hasseProduct_def]
  congr 1
  · rw [← finprod_comp_equiv (HeightOneSpectrum.equivOfRingEquiv
      (RingOfIntegers.mapRingEquiv e))]
    simp only [map_finiteHasse_equivOfRingEquiv]
  · rw [← Equiv.prod_comp (InfinitePlace.realEquivOfRingEquiv e)]
    simp only [realHasse_def, realNegativeIndex_def, map_rank,
      map_realPositiveIndex_realEquivOfRingEquiv]

/-- Transport of an admissible system is admissible. -/
theorem IsAdmissible.map {I : GlobalFormInvariants K} (hI : I.IsAdmissible) (e : K ≃+* L) :
    (I.map e).IsAdmissible := by
  refine ⟨hI.one_le_rank, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    exact hI.realPositiveIndex_le_rank _
  · intro w
    obtain ⟨w, rfl⟩ := (InfinitePlace.realEquivOfRingEquiv e).surjective w
    simpa only [discrAtRealPlace_map, realNegativeIndex_def, map_rank,
      map_realPositiveIndex_realEquivOfRingEquiv] using hI.discrAtRealPlace_eq w
  · exact Function.HasFiniteMulSupport.comp_of_injective
      (f := I.finiteHasse)
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm.injective
      hI.hasFiniteMulSupport_finiteHasse
  · intro hn v
    exact hI.finiteHasse_eq_one_of_rank_eq_one hn _
  · intro hn v hd
    obtain ⟨v, rfl⟩ := (HeightOneSpectrum.equivOfRingEquiv
      (RingOfIntegers.mapRingEquiv e)).surjective v
    simpa only [map_finiteHasse_equivOfRingEquiv] using
      hI.finiteHasse_eq_one_of_rank_eq_two hn v
      ((discrAtFinitePlace_map_eq_neg_one_iff I e v).mp hd)
  · simpa using hI.hasseProduct_eq_one

/-- Admissibility is invariant under field isomorphisms, with places reindexed accordingly. -/
@[simp]
theorem isAdmissible_map_iff (I : GlobalFormInvariants K) (e : K ≃+* L) :
    (I.map e).IsAdmissible ↔ I.IsAdmissible := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map e⟩
  simpa using h.map e.symm

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants
