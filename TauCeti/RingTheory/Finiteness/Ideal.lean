/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Finitely generated ideals under bijective ring homomorphisms

Complements to `Mathlib.RingTheory.Finiteness.Ideal` on transporting finite generation of ideals
(`Ideal.FG`) along bijective ring homomorphisms and ring equivalences (`RingEquivClass`).

## Main results

* `Ideal.fg_map_iff_of_bijective`: extending an ideal along a bijective ring homomorphism preserves
  and reflects finite generation.
* `Ideal.fg_comap_iff_of_bijective`: pulling back an ideal along a bijective ring homomorphism
  preserves and reflects finite generation.
* `Ideal.fg_map_iff_of_equiv`, `Ideal.fg_comap_iff_of_equiv`: specializations to `RingEquivClass`.
* `Ideal.FG.comap_of_bijective`, `Ideal.FG.comap_of_equiv`: dot-notation forms preserving
  `Ideal.FG` under `Ideal.comap`.
-/

public section

namespace Ideal

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Extension along a bijective ring homomorphism preserves and reflects finite generation of
ideals. -/
theorem fg_map_iff_of_bijective {F : Type*} [FunLike F R S] [RingHomClass F R S]
    (f : F) (hf : Function.Bijective f) {I : Ideal R} :
    (I.map f).FG ↔ I.FG := by
  let e := RingEquiv.ofBijective f hf
  refine ⟨fun h ↦ ?_, fun h ↦ h.map (RingHomClass.toRingHom f)⟩
  have h' : (I.map (e : R →+* S)).map (e.symm : S →+* R) = I := map_of_equiv e
  exact h' ▸ h.map e.symm.toRingHom

/-- Pullback along a bijective ring homomorphism preserves and reflects finite generation of
ideals. -/
theorem fg_comap_iff_of_bijective {F : Type*} [FunLike F R S] [RingHomClass F R S]
    (f : F) (hf : Function.Bijective f) {K : Ideal S} :
    (K.comap f).FG ↔ K.FG := by
  let e := RingEquiv.ofBijective f hf
  have h : K.map e.symm.toRingHom = K.comap f := map_symm e
  rw [← h]
  exact fg_map_iff_of_bijective e.symm.toRingHom e.symm.bijective

/-- Extension along a ring equivalence preserves and reflects finite generation of ideals. -/
@[simp]
theorem fg_map_iff_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S]
    (e : E) {I : Ideal R} :
    (I.map e).FG ↔ I.FG :=
  fg_map_iff_of_bijective e (EquivLike.bijective e)

/-- Pullback along a ring equivalence preserves and reflects finite generation of ideals. -/
@[simp]
theorem fg_comap_iff_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S]
    (e : E) {K : Ideal S} :
    (K.comap e).FG ↔ K.FG :=
  fg_comap_iff_of_bijective e (EquivLike.bijective e)

/-- The pullback of a finitely generated ideal along a bijective ring homomorphism is finitely
generated. -/
theorem FG.comap_of_bijective {F : Type*} [FunLike F R S] [RingHomClass F R S]
    {K : Ideal S} (hK : K.FG) (f : F) (hf : Function.Bijective f) :
    (K.comap f).FG :=
  (fg_comap_iff_of_bijective f hf).mpr hK

/-- The pullback of a finitely generated ideal along a ring equivalence is finitely generated. -/
theorem FG.comap_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S]
    {K : Ideal S} (hK : K.FG) (e : E) :
    (K.comap e).FG :=
  (fg_comap_iff_of_equiv e).mpr hK

end Ideal
