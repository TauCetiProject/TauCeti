/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction

/-!
# Transport of the idele norm

The normalized absolute values defining the global idele norm are compatible with field
isomorphisms. In fact, transport along an isomorphism is extension of ideles along a field
extension of degree one.
-/

public section

open NumberField

namespace TauCeti.GlobalNumberFields

/-- The global idele norm is unchanged by transport along a number field isomorphism. -/
@[simp]
theorem ideleNorm_map_adeleEquiv {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃+* L) (x : IdeleGroup (𝓞 K) K) :
    ideleNorm (Units.map ((adeleEquiv K L e : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L) :
      AdeleRing (𝓞 K) K →* AdeleRing (𝓞 L) L) x) = ideleNorm x := by
  let := e.toRingHom.toAlgebra
  have hi := eq_infiniteAdeleExtension_of_continuous K L
    (f := (infiniteAdeleEquiv K L e).toRingHom)
    (continuous_infiniteAdeleEquiv K L e) (infiniteAdeleEquiv_algebraMap K L e)
  have hf := IsDedekindDomain.eq_finiteAdeleExtension_of_continuous (𝓞 K) K (𝓞 L) L
    (f := (finiteAdeleEquiv K L e).toRingHom)
    (continuous_finiteAdeleEquiv K L e) (finiteAdeleEquiv_algebraMap K L e)
  have h : Units.map (adeleEquiv K L e).toMonoidHom x = ideleExtension K L x := by
    apply Units.ext
    rw [Units.coe_map, coe_ideleExtension]
    apply Prod.ext
    · calc
        _ = (adeleEquiv K L e (x : AdeleRing (𝓞 K) K)).1 := rfl
        _ = _ := by
          rw [adeleEquiv_fst, adeleExtension_fst]
          exact RingHom.congr_fun hi (x : AdeleRing (𝓞 K) K).1
    · calc
        _ = (adeleEquiv K L e (x : AdeleRing (𝓞 K) K)).2 := rfl
        _ = _ := by
          rw [adeleEquiv_snd, adeleExtension_snd]
          exact RingHom.congr_fun hf (x : AdeleRing (𝓞 K) K).2
  have hdeg : Module.finrank K L = 1 := Module.finrank_of_bijective_algebraMap e.bijective
  simp only [RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe] at h
  rw [h, ideleNorm_ideleExtension, hdeg, pow_one]

end TauCeti.GlobalNumberFields
