/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Faithful flatness through a quotient by a Jacobson ideal

A flat `A`-algebra `B` is faithfully flat as soon as, for some ideal `J` contained in the
Jacobson radical of `A`, the quotient map `A → A ⧸ J` factors through `B`. Every maximal ideal
`𝔪` of `A` contains `J`, so its image in `A ⧸ J` is proper; hence `𝔪 B` is proper as well.

The criterion needs no finiteness or locality hypothesis. It applies, for instance, to the
henselization of a pair `(A, J)` with `J` in the Jacobson radical, and to an adic completion of
`A` along such an ideal once that completion is known to be flat. In both cases the factorization
through `A ⧸ J` comes from the identification of the closed fibre.

## Main results

* `Module.FaithfullyFlat.of_le_jacobson_of_algHom`: the criterion above.
-/

public section

namespace Module.FaithfullyFlat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- A flat `A`-algebra `B` is faithfully flat if, for an ideal `J` in the Jacobson radical of
`A`, the quotient map `A → A ⧸ J` factors through an `A`-algebra map `B → A ⧸ J`. -/
theorem of_le_jacobson_of_algHom [Module.Flat A B] {J : Ideal A}
    (hJ : J ≤ (⊥ : Ideal A).jacobson) (f : B →ₐ[A] A ⧸ J) : Module.FaithfullyFlat A B := by
  refine ⟨fun m hm h ↦ hm.ne_top ?_⟩
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at h
  have hJm : J ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  -- The image of `m` in `A ⧸ J` is the image of `m B` under `f`, hence the unit ideal.
  have hmap : m.map (Ideal.Quotient.mk J) = ⊤ := by
    rw [← Ideal.Quotient.algebraMap_eq, ← f.comp_algebraMap, ← Ideal.map_map, h, Ideal.map_top]
  have := Ideal.comap_map_of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective m
  rwa [hmap, Ideal.comap_top, Ideal.mk_ker, sup_eq_left.mpr hJm, eq_comm] at this

end Module.FaithfullyFlat
