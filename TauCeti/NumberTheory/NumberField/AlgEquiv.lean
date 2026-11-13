/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.RingTheory.Unramified.AlgEquiv
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport

/-!
# Transport between isomorphic number-field extensions

This file records how properties of primes of rings of integers transport along isomorphisms of
field extensions.

## Main results

* `AlgEquiv.forall_isUnramifiedAt_iff`: unramifiedness above a base prime is invariant under an
  isomorphism of extensions over a fixed base.
* `RingEquiv.forall_heightOneSpectrum_isUnramifiedAt_iff`: unramifiedness at every height-one prime
  is invariant under a commuting square of field isomorphisms.
-/

public section

open IsDedekindDomain
open scoped NumberField

namespace AlgEquiv

variable {K L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']

/-- **Unramifiedness above `𝔭` does not depend on the model of the extension.** -/
theorem forall_isUnramifiedAt_iff (e : L ≃ₐ[K] L') (𝔭 : Ideal (𝓞 K)) :
    (∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q) ↔
      ∀ (Q : Ideal (𝓞 L')) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q := by
  set ψ := NumberField.RingOfIntegers.mapAlgEquiv e
  constructor
  · intro h Q _ _
    exact (ψ.symm.isUnramifiedAt_iff_of_eq_comap (q := Q.comap ψ)
      (Ideal.comap_of_equiv ψ.symm.toRingEquiv).symm).2 (h _)
  · intro h Q _ _
    exact (ψ.isUnramifiedAt_iff_of_eq_comap (q := Q.comap ψ.symm)
      (Ideal.comap_of_equiv ψ.toRingEquiv).symm).2 (h _)

end AlgEquiv

namespace RingEquiv

variable {K L K' L' : Type*} [Field K] [Field L] [Algebra K L]
  [Field K'] [Field L'] [Algebra K' L']

/-- **Unramifiedness at every height-one prime transports across compatible field
isomorphisms.** -/
theorem forall_heightOneSpectrum_isUnramifiedAt_iff (eK : K ≃+* K') (eL : L ≃+* L')
    (he : (algebraMap K' L').comp (eK : K →+* K') = (eL : L →+* L').comp (algebraMap K L)) :
    (∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) ↔
      ∀ w : HeightOneSpectrum (𝓞 L'), Algebra.IsUnramifiedAt (𝓞 K') w.asIdeal := by
  set ψK := NumberField.RingOfIntegers.mapRingEquiv eK
  set ψL := NumberField.RingOfIntegers.mapRingEquiv eL
  have hint : (algebraMap (𝓞 K') (𝓞 L')).comp (ψK : 𝓞 K →+* 𝓞 K') =
      (ψL : 𝓞 L →+* 𝓞 L').comp (algebraMap (𝓞 K) (𝓞 L)) := by
    ext x
    exact RingHom.congr_fun he (x : K)
  have hsymm : (algebraMap (𝓞 K) (𝓞 L)).comp (ψK.symm : 𝓞 K' →+* 𝓞 K) =
      (ψL.symm : 𝓞 L' →+* 𝓞 L).comp (algebraMap (𝓞 K') (𝓞 L')) :=
    RingHom.ext fun x ↦ ψL.eq_symm_apply.mpr <| by
      simpa using (RingHom.congr_fun hint (ψK.symm x)).symm
  constructor
  · intro h w'
    let w : HeightOneSpectrum (𝓞 L) :=
      { asIdeal := w'.asIdeal.comap ψL
        isPrime := w'.isPrime.comap ψL
        ne_bot := (Ideal.comap_mapRingEquiv_eq_bot_iff w'.asIdeal eL).not.mpr w'.ne_bot }
    exact (RingEquiv.isUnramifiedAt_iff_of_eq_comap ψK ψL hint rfl).mp (h w)
  · intro h w
    let w' : HeightOneSpectrum (𝓞 L') :=
      { asIdeal := w.asIdeal.comap ψL.symm
        isPrime := w.isPrime.comap ψL.symm
        ne_bot := by
          rw [NumberField.RingOfIntegers.mapRingEquiv_symm]
          exact (Ideal.comap_mapRingEquiv_eq_bot_iff w.asIdeal eL.symm).not.mpr w.ne_bot }
    exact (RingEquiv.isUnramifiedAt_iff_of_eq_comap ψK.symm ψL.symm hsymm rfl).mp (h w')

end RingEquiv
