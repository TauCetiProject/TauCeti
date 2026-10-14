/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisDescent
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension

/-!
# Galois descent for ideles

For an extension of number fields `L/K`, the extension map of ideles `I_K → I_L` is injective
(`ideleExtension_injective`). When `L/K` is Galois, its image is the set of ideles of `L` fixed by
`Gal(L/K)` (`mem_range_ideleExtension_iff`):

```text
I_K = (I_L)^{Gal(L/K)}.
```

Both are the corresponding statements for adeles (`adeleExtension_injective`,
`mem_range_adeleExtension_iff`), applied to an idele and to its inverse.

## Main results

* `TauCeti.GlobalNumberFields.ideleExtension_injective`: the extension map of ideles is
  injective.
* `TauCeti.GlobalNumberFields.mem_range_ideleExtension_iff`: for `L/K` Galois, an idele of `L`
  is extended from `K` exactly when it is fixed by `Gal(L/K)`.
* `TauCeti.GlobalNumberFields.ideleClassExtension_bijective`: when `algebraMap K L` is
  surjective, extension of idele classes is bijective.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The extension map of ideles is injective.** -/
theorem ideleExtension_injective : Function.Injective (ideleExtension K L) := fun a b h ↦
  Units.ext <| adeleExtension_injective K L <| by
    rw [← coe_ideleExtension, ← coe_ideleExtension, h]

/-- **Galois descent for ideles**: for a Galois extension `L/K`, an idele of `L` is extended from
an idele of `K` exactly when it is fixed by every element of `Gal(L/K)`. -/
theorem mem_range_ideleExtension_iff [IsGalois K L] {a : IdeleGroup (𝓞 L) L} :
    a ∈ (ideleExtension K L).range ↔
      ∀ σ : L ≃ₐ[K] L, adeleGaloisAction K L σ a = a := by
  refine ⟨?_, fun ha ↦ ?_⟩
  · rintro ⟨b, rfl⟩ σ
    rw [coe_ideleExtension]
    exact adeleGaloisAction_adeleExtension K L σ b
  -- The inverse of a fixed idele is fixed, so both the idele and its inverse descend.
  have ha' (σ : L ≃ₐ[K] L) :
      adeleGaloisAction K L σ (a⁻¹ : IdeleGroup (𝓞 L) L) = (a⁻¹ : IdeleGroup (𝓞 L) L) :=
    Units.eq_inv_of_mul_eq_one_left (by rw [← ha σ, ← map_mul, Units.mul_inv, map_one])
  obtain ⟨b, hb⟩ := (mem_range_adeleExtension_iff K L).2 ha
  obtain ⟨c, hc⟩ := (mem_range_adeleExtension_iff K L).2 ha'
  have hbc : b * c = 1 :=
    adeleExtension_injective K L (by rw [map_mul, hb, hc, Units.mul_inv, map_one])
  refine ⟨⟨b, c, hbc, mul_comm c b ▸ hbc⟩, Units.ext ?_⟩
  rw [coe_ideleExtension]
  exact hb

/-- **Extension of idele classes along a surjective `algebraMap` is bijective**: when every
element of `L` comes from `K`, a principal idele of `L` extended from `K` is the extension of a
principal idele of `K`, and every idele of `L` is fixed by the trivial group `Gal(L/K)`, so it
descends to `K`. -/
theorem ideleClassExtension_bijective (h : Function.Surjective (algebraMap K L)) :
    Function.Bijective (ideleClassExtension K L) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun x hx ↦ ?_, fun x ↦ ?_⟩
  · -- A principal idele of `L` extended from `K` is the extension of a principal idele of `K`.
    induction x using QuotientGroup.induction_on with | H a => ?_
    rw [ideleClassExtension_mk, QuotientGroup.eq_one_iff] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨c, hc⟩ := h y
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact y.ne_zero (by rw [← hc, map_zero])
    rw [QuotientGroup.eq_one_iff]
    refine ⟨Units.mk0 c hc0, ideleExtension_injective K L ?_⟩
    rw [ideleExtension_unitEmbedding, ← hy]
    exact congrArg _ (Units.ext hc)
  · -- Every idele of `L` is fixed by the trivial group `Gal(L/K)`, so it descends to `K`.
    induction x using QuotientGroup.induction_on with | H a => ?_
    have : IsGalois K L :=
      IsGalois.of_algEquiv (AlgEquiv.ofBijective (Algebra.ofId K L) ⟨(algebraMap K L).injective, h⟩)
    have hσ (σ : L ≃ₐ[K] L) : σ = 1 := AlgEquiv.ext fun x ↦ by
      obtain ⟨c, rfl⟩ := h x
      exact σ.commutes c
    obtain ⟨b, hb⟩ := (mem_range_ideleExtension_iff K L (a := a)).2 fun σ ↦ by
      rw [hσ σ, map_one, RingAut.one_apply]
    exact ⟨b, by rw [ideleClassExtension_mk, hb]⟩

end TauCeti.GlobalNumberFields
