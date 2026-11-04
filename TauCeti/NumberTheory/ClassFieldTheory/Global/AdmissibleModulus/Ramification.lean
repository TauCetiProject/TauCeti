/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Compatibility
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor.Basic
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic

import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm

/-!
# Admissible moduli and ramification

Let `L/K` be a finite abelian extension of number fields and `𝔪` a modulus of `K` admissible for
`L/K`. This file shows that `𝔪` bounds the local conductors of `L/K` and, in particular, that
every prime of `K` ramified in `L` divides `𝔪`, and that every real place of `K` ramified in `L`
belongs to `𝔪`. Conversely, an extension unramified at every finite prime admits every modulus
carrying its ramified real places; this identifies the extensions admitting the trivial and the
narrow modulus.

Let `v` be a finite place of `K` and `w` a place of `L` above it. If `u ∈ K_vˣ` lies in the step
`U(K_v, n)` of the unit filtration, where `n` is the exponent of `v` in `𝔪`, then the idele
concentrated at `v` with component `u` satisfies the congruence conditions of `𝔪`. By
admissibility its class is a norm from `C_L`, so its global Artin symbol is trivial. By
local–global compatibility (`globalArtinMap_local`) that symbol is the local Artin symbol of `u`,
and for an abelian extension the local Artin symbols that vanish are exactly the norms from `L_w`
(`localArtinAt_eq_one_iff_mem_normGroup`). Hence `U(K_v, n) ⊆ N_{L_w/K_v}(L_wˣ)`, that is, the
conductor exponent of `L_w/K_v` is at most `n`
(`IsAdmissibleModulus.conductorExponent_le_exponent`).

If `v` is not in the support of `𝔪`, then `n = 0`, so every unit of `K_v` is a norm from `L_w`. By
the unramified criterion of local class field theory (`conductorExponent_eq_zero_iff`), `L_w/K_v`
is unramified, and since the local ramification index is the global one, so is `w` over `v`
(`IsAdmissibleModulus.isUnramifiedAt_of_notMem_support`). Contrapositively, a prime of `K` below
a ramified prime of `L` lies in the support of every admissible modulus
(`IsAdmissibleModulus.mem_support_of_ramified`). Equivalently, the support of an admissible
modulus contains the primes dividing the relative discriminant
(`IsAdmissibleModulus.ramifiedSupport_subset_support`); this applies in particular to the conductor
`abelianConductor K L`, which is admissible.

At an infinite place `v` of `K` outside the real places of `𝔪`, the idele class that is `-1` at
`v` lies in the ray subgroup of `𝔪`, hence is a norm, so its global Artin symbol vanishes. By
`globalArtinMap_infiniteLocal` that symbol is the local Artin symbol of `-1` at `v`, so `-1` is a
norm from `L_w` for a place `w` of `L` above `v` (`infiniteLocalArtinAt_eq_one_iff_mem_normGroup`).
If `w` were ramified, `L_w/K_v` would be `ℂ/ℝ`, whose norms are positive. Hence `w` is unramified
(`IsAdmissibleModulus.isUnramified_of_forall_ne`).

Conversely (`isAdmissibleModulus_of_isUnramifiedAt`), suppose that `L/K` is Galois and unramified
at every finite prime, and that the infinite places of `L` above the infinite places of `K`
outside the real places of `𝔪` are unramified. The finite components of a congruence idele `x`
for `𝔪` are units, so their local Artin symbols vanish at the unramified finite places
(`localArtinAt_eq_one_of_normalizedValuation_eq_one`). Its components at the real places of `𝔪`
are positive, and the places above the other infinite places are unramified, so its archimedean
local Artin symbols vanish too. By the local–global character formula, the global Artin symbol
of the class of `x` vanishes (`globalArtinMap_eq_zero_of_forall_eq_one`), that is, the class is a
norm. In particular, for `L/K` abelian, the trivial modulus is admissible exactly
when `L/K` is unramified at every finite prime and at every infinite place
(`isAdmissibleModulus_one_iff`), and the modulus `narrowModulus K` carrying every real place is
admissible exactly when `L/K` is unramified at every finite prime
(`isAdmissibleModulus_narrowModulus_iff`). These describe the abelian extensions contained in the
Hilbert class field and in the narrow Hilbert class field.

The abelian hypothesis cannot be dropped. By norm limitation, the norm group of `ℚ(∛2)/ℚ` is the
whole idele class group, so the trivial modulus is admissible for it, although `2` and `3` ramify.

## Main results

* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.conductorExponent_le_exponent`: the conductor
  exponent of `L_w/K_v` is at most the exponent of `v` in an admissible modulus.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.isUnramifiedAt_of_notMem_support`: a prime of `L`
  over a place outside the support of an admissible modulus is unramified.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.mem_support_of_ramified`: a prime of `K` below a
  ramified prime of `L` lies in the support of every admissible modulus.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.isUnramifiedAway`: the same, for every prime of
  `L` above a place outside the support, in the form taken by the ideal-theoretic Artin map.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.isUnramifiedAt_of_integralIdealsPrimeTo`: the
  same, for every prime of `L` above a prime ideal of `K` prime to `𝔪`.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.ramifiedSupport_subset_support`: the ramified
  support of `L/K` is contained in the support of every admissible modulus.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.isUnramified_of_forall_ne`: an infinite place of
  `L` over an infinite place outside the real places of an admissible modulus is unramified.
* `TauCeti.ClassFieldTheory.isAdmissibleModulus_of_isUnramifiedAt`: an extension unramified at
  every finite prime admits every modulus carrying its ramified real places.
* `TauCeti.ClassFieldTheory.isAdmissibleModulus_one_iff`: the trivial modulus is admissible
  exactly for extensions unramified at every finite and every infinite place.
* `TauCeti.ClassFieldTheory.isAdmissibleModulus_narrowModulus_iff`: the narrow modulus is
  admissible exactly for extensions unramified at every finite prime.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter V (the conductor of an abelian extension).
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField TauCeti.GlobalNumberFields
open scoped AdicCompletionExtension

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L] {𝔪 : Modulus K}

namespace IsAdmissibleModulus

/-- **An admissible modulus bounds the local conductors.** For an abelian extension `L/K`, a
modulus `𝔪` admissible for `L/K`, a finite place `v` of `K` and a place `w` of `L` above it, the
conductor exponent of `L_w/K_v` is at most the exponent of `v` in `𝔪`. -/
theorem conductorExponent_le_exponent (h : IsAdmissibleModulus K L 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    conductorExponent (v.adicCompletion K) (w.adicCompletion L) ≤ 𝔪.exponent v := by
  refine (conductorExponent_le_iff _ _).2 fun u hu ↦ ?_
  -- The idele concentrated at `v` with component `u` is a congruence idele for `𝔪`, so its class
  -- is a norm from `C_L` and its global Artin symbol vanishes.
  have hray : (IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleClassGroup (𝓞 K) K) ∈
      raySubgroup 𝔪 :=
    mem_raySubgroup_iff.2 ⟨_, ofAdicCompletion_mem_ideleCongruenceSubgroup_iff.2 hu, rfl⟩
  have hArt := (globalArtinMap_eq_zero_iff K L IsSepClosed.lift _).2
    (isAdmissibleModulus_iff.1 h hray)
  rw [globalArtinMap_local, ofMul_eq_zero] at hArt
  exact (localArtinAt_eq_one_iff_mem_normGroup v w u).1 hArt

/-- **Primes outside an admissible modulus are unramified.** For an abelian extension `L/K` and a
modulus `𝔪` admissible for `L/K`, every prime of `L` above a finite place `v` of `K` outside the
support of `𝔪` is unramified over `K`. -/
theorem isUnramifiedAt_of_notMem_support (h : IsAdmissibleModulus K L 𝔪)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ 𝔪.support) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  have hc : conductorExponent (v.adicCompletion K) (w.adicCompletion L) = 0 :=
    Nat.eq_zero_of_le_zero <| (h.conductorExponent_le_exponent v w).trans_eq <|
      not_not.1 (mt (Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).2 hv)
  rw [conductorExponent_eq_zero_iff, isUnramified_iff_ramificationIndex_eq_one,
    HeightOneSpectrum.ramificationIndex_adicCompletion] at hc
  exact Ideal.ramificationIdx_eq_one_iff.1 hc

/-- **Ramified primes divide every admissible modulus.** For an abelian extension `L/K` and a
modulus `𝔪` admissible for `L/K`, a finite place `v` of `K` below a prime of `L` ramified over `K`
lies in the support of `𝔪`. -/
theorem mem_support_of_ramified (h : IsAdmissibleModulus K L 𝔪) (v : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (hQ : ¬ Algebra.IsUnramifiedAt (𝓞 K) Q) :
    v ∈ 𝔪.support := by
  by_contra hv
  exact hQ (h.isUnramifiedAt_of_notMem_support hv
    ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩)

/-- **An admissible modulus bounds the ramification.** For an abelian extension `L/K` and a
modulus `𝔪` admissible for `L/K`, every prime of `L` above a finite place of `K` outside the
support of `𝔪` is unramified over `K`. This is the unramifiedness hypothesis of the
ideal-theoretic Artin map `NumberFieldArithmetic.artinHomAway` for the excluded set `𝔪.support`. -/
theorem isUnramifiedAway (h : IsAdmissibleModulus K L 𝔪) :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ 𝔪.support →
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q :=
  fun v hv Q _ _ ↦ not_not.1 fun hQ ↦ hv (h.mem_support_of_ramified v Q hQ)

/-- **Primes prime to an admissible modulus are unramified.** For an abelian extension `L/K` and a
modulus `𝔪` admissible for `L/K`, every prime of `L` above a prime ideal of `K` prime to `𝔪` is
unramified over `K`. -/
theorem isUnramifiedAt_of_integralIdealsPrimeTo (h : IsAdmissibleModulus K L 𝔪)
    (I : integralIdealsPrimeTo 𝔪) [(I : Ideal (𝓞 K)).IsMaximal]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (I : Ideal (𝓞 K))] :
    Algebra.IsUnramifiedAt (𝓞 K) Q := by
  obtain ⟨hI, hS⟩ := Modulus.isCoprimeTo_iff.mp (Modulus.mem_integralIdealsPrimeTo.mp I.2)
  let v : HeightOneSpectrum (𝓞 K) := ⟨I, inferInstance, hI⟩
  have : Q.LiesOver v.asIdeal := ‹Q.LiesOver (I : Ideal (𝓞 K))›
  exact h.isUnramifiedAway v (fun hv ↦ hS v hv dvd_rfl) Q

/-- **The ramified support lies in the support of every admissible modulus.** For an abelian
extension `L/K`, every prime of `K` dividing the relative discriminant of `L/K` divides every
modulus admissible for `L/K`, in particular the conductor `abelianConductor K L`. -/
theorem ramifiedSupport_subset_support (h : IsAdmissibleModulus K L 𝔪) :
    TauCeti.NumberField.ramifiedSupport K L ⊆ 𝔪.support := fun v hv ↦ by
  rw [TauCeti.NumberField.mem_ramifiedSupport,
    dvd_relDiscr_iff_exists_not_isUnramifiedAt v.ne_bot] at hv
  obtain ⟨⟨Q, _, _⟩, hQ⟩ := hv
  exact h.mem_support_of_ramified v Q hQ

/-- **Infinite places outside an admissible modulus are unramified.** For an abelian extension
`L/K` and a modulus `𝔪` admissible for `L/K`, every infinite place of `L` above an infinite place
`v` of `K` that is not one of the real places of `𝔪` is unramified over `K`: if `v` is real, the
places of `L` above it are real. -/
theorem isUnramified_of_forall_ne (h : IsAdmissibleModulus K L 𝔪) {v : InfinitePlace K}
    (hv : ∀ v' ∈ 𝔪.infinitePart, (v' : InfinitePlace K) ≠ v) (w : InfinitePlace L)
    [w.LiesOver v] :
    w.IsUnramified K := by
  by_contra hw
  have hw' : w.IsRamified K := hw
  have hvR : v.IsReal := hw'.liesOver_isReal_under w v
  -- The idele class that is `-1` at `v` satisfies the conditions of `𝔪`, so its global Artin
  -- symbol, which is the local Artin symbol of `-1` at `v`, vanishes.
  have hArt := (globalArtinMap_eq_zero_iff K L IsSepClosed.lift _).2
    (isAdmissibleModulus_iff.1 h (ofCompletion_mem_raySubgroup hv (-1)))
  rw [IdeleClassGroup.ofCompletion_apply, globalArtinMap_infiniteLocal, ofMul_eq_zero,
    infiniteLocalArtinAt_eq_one_iff_mem_normGroup v w,
    InfinitePlace.Completion.mem_normGroup_iff_of_isRamified hw' hvR] at hArt
  norm_num at hArt

end IsAdmissibleModulus

/-! ### Unramified extensions -/

omit [IsAbelianGalois K L] in
/-- **Unramified extensions admit every modulus carrying their ramified real places.** Let `L/K`
be a finite Galois extension of number fields that is unramified at every finite prime, and let
`𝔪` be a modulus such that every infinite place of `L` above an infinite place of `K` outside the
real places of `𝔪` is unramified. Then `𝔪` is admissible for `L/K`. -/
theorem isAdmissibleModulus_of_isUnramifiedAt [IsGalois K L]
    (hfin : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (hinf : ∀ v : InfinitePlace K, (∀ v' ∈ 𝔪.infinitePart, (v' : InfinitePlace K) ≠ v) →
      ∀ (w : InfinitePlace L) [w.LiesOver v], w.IsUnramified K) :
    IsAdmissibleModulus K L 𝔪 := by
  refine isAdmissibleModulus_iff.2 fun c hc ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.1 hc
  -- Every finite component of `x` is a unit, and `L` is unramified at every finite place, so the
  -- local Artin symbols of `x` at the finite places vanish.
  have hfin' (v : HeightOneSpectrum (𝓞 K)) : localArtinAt K L v (v.ideleFiniteCoord x) = 1 := by
    obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
    have := hfin w
    refine localArtinAt_eq_one_of_normalizedValuation_eq_one _ w <|
      (normalizedValuation_eq_one_iff _).2 <| (mem_unitFiltration_zero _).1 ?_
    exact unitFiltration_antitone (Nat.zero_le _)
      (ideleCongruenceSubgroup.ideleFiniteCoord_mem_unitFiltration hx _)
  -- At a real place of `𝔪` the component of `x` is positive; at any other infinite place the
  -- places of `L` above are unramified. Either way the local Artin symbol vanishes.
  have hinf' (v : InfinitePlace K) : infiniteLocalArtinAt K L v (v.ideleInfiniteCoord x) = 1 := by
    by_cases hv : ∃ v' ∈ 𝔪.infinitePart, (v' : InfinitePlace K) = v
    · obtain ⟨v', hv', rfl⟩ := hv
      exact infiniteLocalArtinAt_eq_one_of_pos v'.2
        ((mem_ideleCongruenceSubgroup_iff.1 hx).2.2 v' hv')
    · push Not at hv
      obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := L) v
      exact infiniteLocalArtinAt_eq_one_of_isUnramified _ w (hinf _ hv w) _
  -- By the local–global character formula, the global Artin symbol of the class of `x` vanishes.
  rw [QuotientGroup.mk'_apply, ← globalArtinMap_eq_zero_iff K L IsSepClosed.lift]
  exact globalArtinMap_eq_zero_of_forall_eq_one K L _ hfin' hinf'

/-- **The trivial modulus is admissible exactly for unramified extensions.** For an abelian
extension `L/K` of number fields, the trivial modulus is admissible for `L/K` exactly when `L/K`
is unramified at every finite prime and at every infinite place. -/
theorem isAdmissibleModulus_one_iff :
    IsAdmissibleModulus K L (Modulus.one K) ↔
      (∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) ∧
        IsUnramifiedAtInfinitePlaces K L := by
  refine ⟨fun h ↦ ⟨fun w ↦ h.isUnramifiedAt_of_notMem_support (v := w.under (𝓞 K)) (by simp) w,
    ⟨fun w ↦ h.isUnramified_of_forall_ne (v := w.comap (algebraMap K L)) (by simp) w⟩⟩,
    fun ⟨hfin, hinf⟩ ↦ ?_⟩
  exact isAdmissibleModulus_of_isUnramifiedAt hfin fun _ _ w _ ↦ hinf.isUnramified w

/-- **The narrow modulus is admissible exactly for extensions unramified at the finite primes.**
For an abelian extension `L/K` of number fields, the modulus `narrowModulus K`, trivial at the
finite places and carrying every real place, is admissible for `L/K` exactly when `L/K` is
unramified at every finite prime. -/
theorem isAdmissibleModulus_narrowModulus_iff :
    IsAdmissibleModulus K L (narrowModulus K) ↔
      ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  refine ⟨fun h w ↦ h.isUnramifiedAt_of_notMem_support (v := w.under (𝓞 K)) (by simp) w,
    fun hfin ↦ isAdmissibleModulus_of_isUnramifiedAt hfin fun v hv w _ ↦ ?_⟩
  -- A place of `K` outside the narrow modulus is complex, so the places above it are unramified.
  have hvC : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 fun hvR ↦
    hv ⟨v, hvR⟩ (mem_narrowModulus_infinitePart _) rfl
  rw [InfinitePlace.isUnramified_iff, InfinitePlace.LiesOver.comap_eq w v]
  exact Or.inr hvC

end TauCeti.ClassFieldTheory
