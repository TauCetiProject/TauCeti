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

/-!
# Admissible moduli and ramification

Let `L/K` be a finite abelian extension of number fields and `𝔪` a modulus of `K` admissible for
`L/K`. This file shows that the exponents of the conductor of `L/K` are its local conductor
exponents, so that `𝔪` bounds them, and, in particular, that every prime of `K` ramified in `L`
divides `𝔪`.

Let `v` be a finite place of `K` and `w` a place of `L` above it. The class of the idele
concentrated at `v` with component `u ∈ K_vˣ` is a norm from `C_L` exactly when its global Artin
symbol is trivial. By local–global compatibility (`globalArtinMap_local`) that symbol is the local
Artin symbol of `u`, and for an abelian extension the local Artin symbols that vanish are exactly
the norms from `L_w` (`localArtinAt_eq_one_iff_mem_normGroup`). So that class is a norm exactly
when `u` is a norm from `L_w` (`ofAdicCompletion_mem_range_ideleClassNormMap_iff`). Since the
exponent of `v` in the conductor is read off from these classes
(`exponent_abelianConductor_le_iff`), it is the conductor exponent of `L_w/K_v`
(`exponent_abelianConductor`). As `𝔪` is a multiple of the conductor, the conductor exponent of
`L_w/K_v` is at most the exponent of `v` in `𝔪`
(`IsAdmissibleModulus.conductorExponent_le_exponent`).

If `v` is not in the support of `𝔪`, then its exponent in `𝔪` is `0`, so every unit of `K_v` is a
norm from `L_w`. By the unramified criterion of local class field theory
(`conductorExponent_eq_zero_iff`), `L_w/K_v` is unramified, and since the local ramification
index is the global one, so is `w` over `v`
(`IsAdmissibleModulus.isUnramifiedAt_of_notMem_support`). Contrapositively, a prime of `K` below
a ramified prime of `L` lies in the support of every admissible modulus
(`IsAdmissibleModulus.mem_support_of_ramified`). Equivalently, the support of an admissible
modulus contains the primes dividing the relative discriminant
(`IsAdmissibleModulus.ramifiedSupport_subset_support`); this applies in particular to the conductor
`abelianConductor K L`, which is admissible.

The abelian hypothesis cannot be dropped. By norm limitation, the norm group of `ℚ(∛2)/ℚ` is the
whole idele class group, so the trivial modulus is admissible for it, although `2` and `3` ramify.

## Main results

* `TauCeti.ClassFieldTheory.ofAdicCompletion_mem_range_ideleClassNormMap_iff`: the class of an
  idele concentrated at `v` is a norm from `L` exactly when its component is a norm from `L_w`.
* `TauCeti.ClassFieldTheory.exponent_abelianConductor`: the exponent of `v` in the conductor of
  `L/K` is the conductor exponent of `L_w/K_v`.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.conductorExponent_le_exponent`: the conductor
  exponent of `L_w/K_v` is at most the exponent of `v` in an admissible modulus.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.isUnramifiedAt_of_notMem_support`: a prime of `L`
  over a place outside the support of an admissible modulus is unramified.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.mem_support_of_ramified`: a prime of `K` below a
  ramified prime of `L` lies in the support of every admissible modulus.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.isUnramifiedAway`: the same, for every prime of
  `L` above a place outside the support, in the form taken by the ideal-theoretic Artin map.
* `TauCeti.ClassFieldTheory.IsAdmissibleModulus.ramifiedSupport_subset_support`: the ramified
  support of `L/K` is contained in the support of every admissible modulus.

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

section LocalConductor

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- **Idele classes concentrated at one place that are norms.** For an abelian extension `L/K`, a
finite place `v` of `K` and a place `w` of `L` above it, the class of the idele concentrated at
`v` with component `u` is a norm from `L` exactly when `u` is a norm from `L_w`. -/
theorem ofAdicCompletion_mem_range_ideleClassNormMap_iff (u : (v.adicCompletion K)ˣ) :
    (IdeleGroup.ofAdicCompletion (𝓞 K) K v u : IdeleClassGroup (𝓞 K) K) ∈
        (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range ↔
      u ∈ normGroup (v.adicCompletion K) (w.adicCompletion L) := by
  rw [← globalArtinMap_eq_zero_iff K L IsSepClosed.lift, globalArtinMap_local, ofMul_eq_zero,
    localArtinAt_eq_one_iff_mem_normGroup v w]

/-- **The exponents of the conductor are the local conductor exponents.** For an
abelian extension `L/K`, a finite place `v` of `K` and a place `w` of `L` above it, the exponent
of `v` in the conductor of `L/K` is the conductor exponent of `L_w/K_v`. -/
theorem exponent_abelianConductor :
    (abelianConductor K L).exponent v =
      conductorExponent (v.adicCompletion K) (w.adicCompletion L) :=
  eq_of_forall_ge_iff fun n ↦ by
    rw [exponent_abelianConductor_le_iff, conductorExponent_le_iff]
    exact forall₂_congr fun u _ ↦ ofAdicCompletion_mem_range_ideleClassNormMap_iff v w u

end LocalConductor

namespace IsAdmissibleModulus

/-- **An admissible modulus bounds the local conductors.** For an abelian extension `L/K`, a
modulus `𝔪` admissible for `L/K`, a finite place `v` of `K` and a place `w` of `L` above it, the
conductor exponent of `L_w/K_v` is at most the exponent of `v` in `𝔪`. -/
theorem conductorExponent_le_exponent (h : IsAdmissibleModulus K L 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    conductorExponent (v.adicCompletion K) (w.adicCompletion L) ≤ 𝔪.exponent v :=
  (exponent_abelianConductor v w).symm.trans_le <|
    Modulus.exponent_mono ((isAdmissibleModulus_iff_abelianConductor_dvd 𝔪).1 h) v

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

/-- **The ramified support lies in the support of every admissible modulus.** For an abelian
extension `L/K`, every prime of `K` dividing the relative discriminant of `L/K` divides every
modulus admissible for `L/K`, in particular the conductor `abelianConductor K L`. -/
theorem ramifiedSupport_subset_support (h : IsAdmissibleModulus K L 𝔪) :
    TauCeti.NumberField.ramifiedSupport K L ⊆ 𝔪.support := fun v hv ↦ by
  rw [TauCeti.NumberField.mem_ramifiedSupport,
    dvd_relDiscr_iff_exists_not_isUnramifiedAt v.ne_bot] at hv
  obtain ⟨⟨Q, _, _⟩, hQ⟩ := hv
  exact h.mem_support_of_ramified v Q hQ

end IsAdmissibleModulus

end TauCeti.ClassFieldTheory
