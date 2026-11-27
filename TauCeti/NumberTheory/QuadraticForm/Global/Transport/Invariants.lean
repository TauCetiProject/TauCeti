/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Transport
public import TauCeti.NumberTheory.QuadraticForm.Global.FormInvariants
public import TauCeti.NumberTheory.QuadraticForm.Global.LocalRealization
public import TauCeti.NumberTheory.QuadraticForm.Global.Transport.Basic

/-!
# Transporting systems of local invariants along isomorphisms of number fields

A ring isomorphism `e : K ≃+* L` of number fields identifies the finite places of `K` with those of
`L` through `HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)`, and the real
places through `NumberField.InfinitePlace.realEquivOfRingEquiv e`. A system of local invariants
`I : GlobalFormInvariants K` therefore transports to the system `I.map e` over `L`: the same rank,
the global discriminant pushed forward along `e`, and at each place of `L` the Hasse sign or the
positive index of `I` at the corresponding place of `K`.

This reindexing is the one the invariants of quadratic forms undergo. The system of the transport
`Q.transport f` of a regular form along an `e`-semilinear equivalence `f` is the transported system
of `Q` (`QuadraticForm.globalInvariants_transport`). Admissibility is preserved and reflected
(`GlobalFormInvariants.isAdmissible_map_iff`). A family of local forms realizing `I` transports to
a family realizing `I.map e`: the form `U_v` over `K_v` is carried to `L_w`, for `w` the place
corresponding to `v`, along any ring isomorphism `K_v ≃+* L_w` extending `e`, such as
`IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr`, and the real forms are reindexed
(`GlobalFormInvariants.IsLocalRealization.map`). The discriminants match because the isomorphism
of completions agrees with `e` on `K`, and the local Hasse invariants because a ring isomorphism
preserves every Hilbert symbol (`TauCeti.RegularFormClass.localHasse_map`).

These statements carry the classification data of quadratic forms between isomorphic number
fields, for instance between a number field and a copy of it in another universe.

## Main definitions

* `TauCeti.NumberField.QuadraticForm.GlobalFormInvariants.map`: the system transported along a
  ring isomorphism of number fields.

## Main results

* `GlobalFormInvariants.discrAtFinitePlace_map`, `GlobalFormInvariants.discrAtRealPlace_map`: the
  local discriminants of the transported system are the transported local discriminants.
* `GlobalFormInvariants.hasseProduct_map`: the Hasse product is unchanged.
* `GlobalFormInvariants.map_symm_map`, `GlobalFormInvariants.map_map_symm`: transporting back along
  `e.symm` recovers the system.
* `GlobalFormInvariants.isAdmissible_map_iff`: a system is admissible exactly when its transport
  is.
* `GlobalFormInvariants.IsLocalRealization.map`,
  `GlobalFormInvariants.IsLocalRealization.exists_map`: a family realizing a system transports to a
  family realizing the transported system.
* `QuadraticForm.globalInvariants_transport`: the system of a transported regular form is the
  transported system.
-/

public section
noncomputable section

open Finset IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
  NumberField.InfinitePlace QuadraticMap

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace TauCeti.NumberField.QuadraticForm

namespace GlobalFormInvariants

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

-- The body is exposed so that the rank of `I.map e` is definitionally the rank of `I`: a family
-- realizing `I.map e` lives on `Fin (I.map e).rank → L_w`, and `IsLocalRealization.map` builds it
-- from forms on `Fin I.rank → K_v`.
/-- **The system transported along a ring isomorphism** `e : K ≃+* L` of number fields: the same
rank, the image of the global discriminant under the map of square-class groups induced by `e`,
and at each finite or real place of `L` the Hasse sign or positive index of the system at the
corresponding place of `K`. -/
@[expose] def map (e : K ≃+* L) (I : GlobalFormInvariants K) : GlobalFormInvariants L where
  rank := I.rank
  discr := (e : K →+* L).squareClassMap I.discr
  finiteHasse w :=
    I.finiteHasse ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm w)
  realPositiveIndex w := I.realPositiveIndex ((realEquivOfRingEquiv e).symm w)

variable (e : K ≃+* L) (I : GlobalFormInvariants K)

/-- The transported system has the same rank. -/
@[simp]
theorem rank_map : (I.map e).rank = I.rank :=
  (rfl)

/-- The discriminant of the transported system is the image of the discriminant. -/
@[simp]
theorem discr_map : (I.map e).discr = (e : K →+* L).squareClassMap I.discr :=
  (rfl)

/-- The Hasse sign of the transported system at a finite place `w` of `L` is the Hasse sign of the
system at the corresponding finite place of `K`. -/
theorem finiteHasse_map (w : HeightOneSpectrum (𝓞 L)) :
    (I.map e).finiteHasse w =
      I.finiteHasse ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm w) :=
  (rfl)

-- Not `@[simp]`: `HeightOneSpectrum.equivOfRingEquiv_apply` rewrites the place on the left.
/-- The Hasse sign of the transported system at the finite place corresponding to `v` is the Hasse
sign of the system at `v`. -/
theorem finiteHasse_map_equivOfRingEquiv (v : HeightOneSpectrum (𝓞 K)) :
    (I.map e).finiteHasse
        (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) =
      I.finiteHasse v := by
  rw [finiteHasse_map, Equiv.symm_apply_apply]

/-- The positive index of the transported system at a real place `w` of `L` is the positive index
of the system at the corresponding real place of `K`. -/
theorem realPositiveIndex_map (w : {w : InfinitePlace L // w.IsReal}) :
    (I.map e).realPositiveIndex w = I.realPositiveIndex ((realEquivOfRingEquiv e).symm w) :=
  (rfl)

/-- The positive index of the transported system at the real place corresponding to `w` is the
positive index of the system at `w`. -/
@[simp]
theorem realPositiveIndex_map_realEquivOfRingEquiv (w : {w : InfinitePlace K // w.IsReal}) :
    (I.map e).realPositiveIndex (realEquivOfRingEquiv e w) = I.realPositiveIndex w := by
  rw [realPositiveIndex_map, Equiv.symm_apply_apply]

-- Not `@[simp]`: `simp` proves it from `realNegativeIndex_def` and
-- `realPositiveIndex_map_realEquivOfRingEquiv`.
/-- The negative index of the transported system at the real place corresponding to `w` is the
negative index of the system at `w`. -/
theorem realNegativeIndex_map_realEquivOfRingEquiv (w : {w : InfinitePlace K // w.IsReal}) :
    (I.map e).realNegativeIndex (realEquivOfRingEquiv e w) = I.realNegativeIndex w := by
  simp

-- Not `@[simp]`: `simp` proves it from `realHasse_def` and
-- `realPositiveIndex_map_realEquivOfRingEquiv`.
/-- The real Hasse sign of the transported system at the real place corresponding to `w` is the
real Hasse sign of the system at `w`. -/
theorem realHasse_map_realEquivOfRingEquiv (w : {w : InfinitePlace K // w.IsReal}) :
    (I.map e).realHasse (realEquivOfRingEquiv e w) = I.realHasse w := by
  simp

/-- **Local discriminants of the transported system.** For finite places `v` of `K` and `w` of `L`
and a ring homomorphism `τ : K_v →+* L_w` extending `e`, the discriminant of the transported system
at `w` is the image under `τ` of the discriminant of the system at `v`. -/
theorem discrAtFinitePlace_map {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (τ : v.adicCompletion K →+* w.adicCompletion L)
    (hτ : ∀ x, τ (algebraMap K (v.adicCompletion K) x) = algebraMap L (w.adicCompletion L) (e x)) :
    (I.map e).discrAtFinitePlace w = τ.squareClassMap (I.discrAtFinitePlace v) := by
  have h : (algebraMap L (w.adicCompletion L)).comp (e : K →+* L) =
      (τ : _ →+* _).comp (algebraMap K (v.adicCompletion K)) :=
    RingHom.ext fun x ↦ (hτ x).symm
  rw [discrAtFinitePlace_def, discrAtFinitePlace_def, discr_map, ← LinearMap.comp_apply,
    ← RingHom.squareClassMap_comp, h, RingHom.squareClassMap_comp, LinearMap.comp_apply]

-- Not `@[simp]`: `simp` proves it from `discrAtRealPlace_def` and
-- `NumberField.InfinitePlace.embedding_of_isReal_equivOfRingEquiv`.
/-- The discriminant of the transported system at the real place corresponding to `w` is the
discriminant of the system at `w`. -/
theorem discrAtRealPlace_map (w : {w : InfinitePlace K // w.IsReal}) :
    (I.map e).discrAtRealPlace (realEquivOfRingEquiv e w) = I.discrAtRealPlace w := by
  have h : (embedding_of_isReal (realEquivOfRingEquiv e w).property).comp (e : K →+* L) =
      embedding_of_isReal w.property :=
    RingHom.ext fun x ↦ by simp [coe_realEquivOfRingEquiv]
  rw [discrAtRealPlace_def, discrAtRealPlace_def, discr_map, ← LinearMap.comp_apply,
    ← RingHom.squareClassMap_comp, h]

open scoped Classical in
/-- **The Hasse product is invariant under transport.** -/
@[simp]
theorem hasseProduct_map : (I.map e).hasseProduct = I.hasseProduct := by
  rw [hasseProduct_def, hasseProduct_def,
    ← finprod_comp_equiv (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e))
      (f := (I.map e).finiteHasse),
    ← Equiv.prod_comp (realEquivOfRingEquiv e) (I.map e).realHasse]
  simp only [finiteHasse_map_equivOfRingEquiv, realHasse_map_realEquivOfRingEquiv]

/-- Transporting along `e` and then back along `e.symm` recovers the system. -/
@[simp]
theorem map_symm_map : (I.map e).map e.symm = I := by
  have hψ (v : HeightOneSpectrum (𝓞 K)) :
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e.symm)).symm v =
        HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v :=
    HeightOneSpectrum.ext <| by
      rw [asIdeal_equivOfRingEquiv_symm, asIdeal_equivOfRingEquiv,
        ← RingOfIntegers.mapRingEquiv_symm, Ideal.comap_symm]
  refine GlobalFormInvariants.ext rfl (RingEquiv.squareClassMap_symm_squareClassMap e I.discr)
    (funext fun v ↦ ?_) (funext fun w ↦ ?_)
  · rw [finiteHasse_map, finiteHasse_map, hψ, Equiv.symm_apply_apply]
  · rw [realPositiveIndex_map, realPositiveIndex_map, realEquivOfRingEquiv_symm e.symm,
      RingEquiv.symm_symm, Equiv.symm_apply_apply]

/-- Transporting along `e.symm` and then along `e` recovers the system. -/
@[simp]
theorem map_map_symm (J : GlobalFormInvariants L) : (J.map e.symm).map e = J := by
  simpa using map_symm_map e.symm J

/-- Transport of systems along a ring isomorphism is injective. -/
theorem map_injective : Function.Injective (map (K := K) (L := L) e) :=
  Function.LeftInverse.injective (map_symm_map e)

/-- **Transport preserves admissibility.** -/
theorem IsAdmissible.map {I : GlobalFormInvariants K} (hI : I.IsAdmissible) :
    (I.map e).IsAdmissible where
  one_le_rank := hI.one_le_rank
  realPositiveIndex_le_rank w := hI.realPositiveIndex_le_rank _
  discrAtRealPlace_eq w := by
    obtain ⟨w, rfl⟩ := (realEquivOfRingEquiv e).surjective w
    rw [discrAtRealPlace_map, realNegativeIndex_map_realEquivOfRingEquiv, hI.discrAtRealPlace_eq]
  hasFiniteMulSupport_finiteHasse := by
    have h := hI.hasFiniteMulSupport_finiteHasse
    rw [Function.HasFiniteMulSupport] at h ⊢
    exact h.preimage
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm.injective.injOn
  finiteHasse_eq_one_of_rank_eq_one hn w := hI.finiteHasse_eq_one_of_rank_eq_one hn _
  finiteHasse_eq_one_of_rank_eq_two hn w hd := by
    rw [finiteHasse_map]
    refine hI.finiteHasse_eq_one_of_rank_eq_two hn _ ?_
    let τ := adicCompletionCongr _ w e (valuation_eq_valuation_equivOfRingEquiv_symm e w)
    rw [discrAtFinitePlace_map e I τ.toRingHom (adicCompletionCongr_algebraMap _),
      RingEquiv.toRingHom_eq_coe] at hd
    apply RingEquiv.squareClassMap_injective τ
    rw [hd, RingHom.squareClassMap_apply]
    congr 1
    ext
    simp
  hasseProduct_eq_one := by rw [hasseProduct_map, hI.hasseProduct_eq_one]

/-- **A system is admissible exactly when its transport is.** -/
@[simp]
theorem isAdmissible_map_iff : (I.map e).IsAdmissible ↔ I.IsAdmissible :=
  ⟨fun h ↦ by simpa using h.map e.symm, fun h ↦ h.map e⟩

namespace IsLocalRealization

variable {e} {I}
variable {U : ∀ v : HeightOneSpectrum (𝓞 K),
    _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
  {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}

/-- **Transport of local realizations.** Let a family `(U, R)` realize the system `I`, and for each
finite place `w` of `L` let `τ w : K_v ≃+* L_w` be a ring isomorphism extending `e`, where `v` is
the finite place of `K` corresponding to `w`. Transporting each `U_v` along the coordinatewise
equivalence induced by `τ w`, and reindexing the real forms along the bijection of real places,
gives a family realizing the transported system `I.map e`. -/
theorem map (hL : I.IsLocalRealization U R)
    (τ : ∀ w : HeightOneSpectrum (𝓞 L),
      ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm w).adicCompletion
        K ≃+* w.adicCompletion L)
    (hτ : ∀ w x, τ w (algebraMap K _ x) = algebraMap L (w.adicCompletion L) (e x)) :
    (I.map e).IsLocalRealization
      (fun w ↦ (U _).transport (LinearEquiv.piCongrRightₛₗ fun _ ↦ (τ w).toSemilinearEquiv))
      (fun w ↦ R ((realEquivOfRingEquiv e).symm w)) where
  nondegenerate_finite w := (nondegenerate_transport_iff _ _).mpr (hL.nondegenerate_finite _)
  discr_finite w :=
    (congrArg RegularFormClass.discr (QuadraticForm.formClass_transport (τ w) _ (U _)
      (hL.nondegenerate_finite _))).trans <| by
        rw [RegularFormClass.discr_map, hL.discr_finite,
          discrAtFinitePlace_map e I (τ w).toRingHom (hτ w),
          RingEquiv.toRingHom_eq_coe]
  localHasse_finite w := by
    let _ : Finite (𝓞 K ⧸
        ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm w).asIdeal) :=
      Ring.HasFiniteQuotients.finiteQuotient (HeightOneSpectrum.ne_bot _)
    let _ : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    refine (congrArg RegularFormClass.localHasse (QuadraticForm.formClass_transport (τ w) _ (U _)
      (hL.nondegenerate_finite _))).trans ?_
    rw [RegularFormClass.localHasse_map, hL.localHasse_finite, finiteHasse_map]
  nondegenerate_real w := hL.nondegenerate_real _
  sigPos_real w := hL.sigPos_real _

/-- A system realized by a family of local forms has a transport realized by a family of local
forms over `L`: the isomorphisms of completions `adicCompletionCongr` extend `e`. -/
theorem exists_map (hL : I.IsLocalRealization U R) (e : K ≃+* L) :
    ∃ (U' : ∀ w : HeightOneSpectrum (𝓞 L),
        _root_.QuadraticForm (w.adicCompletion L) (Fin (I.map e).rank → w.adicCompletion L))
      (R' : {w : InfinitePlace L // w.IsReal} → _root_.QuadraticForm ℝ (Fin (I.map e).rank → ℝ)),
      (I.map e).IsLocalRealization U' R' := by
  exact ⟨_, _, hL.map (fun w ↦ adicCompletionCongr _ w e
    (valuation_eq_valuation_equivOfRingEquiv_symm e w))
    fun w ↦ adicCompletionCongr_algebraMap (valuation_eq_valuation_equivOfRingEquiv_symm e w)⟩

end IsLocalRealization

end GlobalFormInvariants

end TauCeti.NumberField.QuadraticForm

namespace QuadraticForm

open TauCeti TauCeti.NumberField.QuadraticForm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable {V V' : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup V'] [Module L V'] [FiniteDimensional L V']

/-- **The system of a transported form is the transported system.** For a regular form `Q` over a
number field `K` and a semilinear equivalence `f : V ≃ₛₗ[e] V'` over a ring isomorphism
`e : K ≃+* L` of number fields, the system of local invariants of `Q.transport f` is the system of
`Q` transported along `e`: the same rank, the discriminant mapped by `e`, and the Hasse signs and
positive indices reindexed along the bijections of finite and real places. -/
theorem globalInvariants_transport (e : K ≃+* L) (f : V ≃ₛₗ[(e : K →+* L)] V')
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    (Q.transport f).globalInvariants ((nondegenerate_transport_iff f Q).mpr hQ) =
      (Q.globalInvariants hQ).map e := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (2 : L) := invertibleOfNonzero two_ne_zero
  obtain ⟨⟨n, a⟩, ha⟩ := exists_presentedForm_equivalent Q hQ
  rw [presentedForm_eq_weightedSumSquares_coe] at ha
  have ha' := ha.transport f (LinearEquiv.piCongrRightₛₗ fun _ ↦ e.toSemilinearEquiv)
  rw [transport_weightedSumSquares] at ha'
  replace ha' : (Q.transport f).Equivalent
      (weightedSumSquares L fun i ↦ (Units.map (e : K →* L) (a i) : L)) := by
    simpa only [Units.coe_map, MonoidHom.coe_ofClass] using ha'
  refine GlobalFormInvariants.ext ?_ ?_ (funext fun w ↦ ?_) (funext fun w ↦ ?_)
  · -- the rank: a semilinear equivalence over a ring isomorphism preserves the dimension
    have h := congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv (e : K → L) f.toAddEquiv
      e.bijective fun r m ↦ f.map_smulₛₗ r m)
    simpa [Module.finrank] using h.symm
  · rw [globalInvariants_discr, GlobalFormInvariants.discr_map, globalInvariants_discr,
      formClass_transport e f Q hQ, RegularFormClass.discr_map]
  · obtain ⟨v, rfl⟩ :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).surjective w
    rw [GlobalFormInvariants.finiteHasse_map_equivOfRingEquiv, globalInvariants_finiteHasse,
      globalInvariants_finiteHasse, finiteHasse_eq_prod_hilbertSymbol _ _ ha',
      finiteHasse_eq_prod_hilbertSymbol _ _ ha]
    simp only [hilbertSymbol_unitAtFinitePlace_equivOfRingEquiv]
  · obtain ⟨w, rfl⟩ := (realEquivOfRingEquiv e).surjective w
    rw [GlobalFormInvariants.realPositiveIndex_map_realEquivOfRingEquiv,
      globalInvariants_realPositiveIndex, globalInvariants_realPositiveIndex,
      ha'.realPositiveIndex_eq, ha.realPositiveIndex_eq, realPositiveIndex_weightedSumSquares,
      realPositiveIndex_weightedSumSquares]
    simp [coe_realEquivOfRingEquiv]

end QuadraticForm
