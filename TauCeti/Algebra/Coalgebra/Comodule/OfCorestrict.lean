/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Comodules whose coaction takes values in a subcoalgebra

Let `ι : D →ₗc[R] C` be a coalgebra morphism and `M` a right `C`-comodule whose coaction takes
values in the image of `M ⊗ D → M ⊗ C`. When that map and its analogue for `D ⊗ D` are injective,
for instance over a field when `ι` is injective, the coaction lifts uniquely to a right
`D`-coaction on `M`. Its corestriction along `ι` is the original coaction, so this construction
is a one-sided inverse to `TauCeti.Comodule.Corestrict`.

For an affine group `G` with a quotient `G → Q`, this is how a representation of `G` on which the
kernel acts trivially becomes a representation of `Q`: its matrix coefficients are functions on
`G` pulled back from `Q`.

## Main declarations

* `TauCeti.Comodule.ofCorestrict`: the lifted `D`-comodule structure.
* `TauCeti.Comodule.lTensor_coact_ofCorestrict`: its corestriction along `ι` is the original
  coaction.
* `TauCeti.Comodule.Hom.ofCorestrict`: a `C`-comodule morphism between such comodules is a
  `D`-comodule morphism.
* `TauCeti.Comodule.mem_fixedSubcomodule_ofCorestrict_iff`: the lifted and original coactions
  have the same fixed vectors.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x y

variable {R : Type u} [CommSemiring R]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- A right `C`-comodule whose coaction takes values in `M ⊗ D`, for a coalgebra morphism
`ι : D →ₗc[R] C` with `M ⊗ D → M ⊗ C` and `M ⊗ (D ⊗ D) → M ⊗ (C ⊗ C)` injective, is a right
`D`-comodule. Its coaction is the unique lift of the original one. -/
@[implicit_reducible]
noncomputable def ofCorestrict (ι : D →ₗc[R] C)
    (hM : Function.Injective (ι.toLinearMap.lTensor M))
    (hMM : Function.Injective ((TensorProduct.map ι.toLinearMap ι.toLinearMap).lTensor M))
    (h : ∀ m : M, coact (R := R) (C := C) m ∈ LinearMap.range (ι.toLinearMap.lTensor M)) :
    Comodule R D M where
  coact := LinearMap.codRestrictOfInjective (coact (R := R) (C := C)) _ hM h
  coassoc := by
    set ρ := LinearMap.codRestrictOfInjective (coact (R := R) (C := C) (M := M)) _ hM h
    have hρ (m : M) : ι.toLinearMap.lTensor M (ρ m) = coact (R := R) (C := C) m :=
      LinearMap.codRestrictOfInjective_comp_apply _ _ hM h m
    have hcomp : ι.toLinearMap.lTensor M ∘ₗ ρ = coact (R := R) (C := C) :=
      LinearMap.codRestrictOfInjective_comp _ _ hM h
    ext m
    apply hMM
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    -- Both sides map to the two sides of coassociativity of the original coaction.
    have hl : (TensorProduct.map ι.toLinearMap ι.toLinearMap).lTensor M
        (TensorProduct.assoc R M D D (ρ.rTensor D (ρ m))) =
          TensorProduct.assoc R M C C ((coact (R := R) (C := C)).rTensor C
            (coact (R := R) (C := C) m)) := by
      rw [LinearMap.lTensor_map_assoc_rTensor_natural, hcomp, hρ]
    have hr : (TensorProduct.map ι.toLinearMap ι.toLinearMap).lTensor M
        (Coalgebra.comul.lTensor M (ρ m)) =
          Coalgebra.comul.lTensor M (coact (R := R) (C := C) m) := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ι.map_comp_comul,
        LinearMap.lTensor_comp, LinearMap.comp_apply, hρ]
    rw [hl, hr, coassoc_apply]
  lTensor_counit_comp_coact := by
    set ρ := LinearMap.codRestrictOfInjective (coact (R := R) (C := C) (M := M)) _ hM h
    have hρ (m : M) : ι.toLinearMap.lTensor M (ρ m) = coact (R := R) (C := C) m :=
      LinearMap.codRestrictOfInjective_comp_apply _ _ hM h m
    ext m
    calc
      Coalgebra.counit.lTensor M (ρ m) =
          (Coalgebra.counit ∘ₗ ι.toLinearMap).lTensor M (ρ m) := by rw [ι.counit_comp]
      _ = Coalgebra.counit.lTensor M (ι.toLinearMap.lTensor M (ρ m)) := by
        rw [LinearMap.lTensor_comp_apply]
      _ = Coalgebra.counit.lTensor M (coact (R := R) (C := C) m) := by rw [hρ]
      _ = m ⊗ₜ[R] 1 := Comodule.lTensor_counit_coact m

variable (ι : D →ₗc[R] C) (hM : Function.Injective (ι.toLinearMap.lTensor M))
    (hMM : Function.Injective ((TensorProduct.map ι.toLinearMap ι.toLinearMap).lTensor M))
    (h : ∀ m : M, coact (R := R) (C := C) m ∈ LinearMap.range (ι.toLinearMap.lTensor M))

/-- The lifted coaction maps back to the original one along `ι`. -/
@[simp]
theorem lTensor_coact_ofCorestrict (m : M) :
    letI := ofCorestrict ι hM hMM h
    (ι : D →ₗ[R] C).lTensor M (coact (R := R) (C := D) m) = coact (R := R) (C := C) m :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ hM h m

/-- The lifted coaction is the unique `D`-valued coaction mapping back to the original one. -/
theorem coact_ofCorestrict_eq_iff (m : M) (t : M ⊗[R] D) :
    letI := ofCorestrict ι hM hMM h
    coact (R := R) (C := D) m = t ↔ ι.toLinearMap.lTensor M t = coact (R := R) (C := C) m := by
  let := ofCorestrict ι hM hMM h
  rw [← lTensor_coact_ofCorestrict ι hM hMM h m]
  exact ⟨fun ht ↦ ht ▸ rfl, fun ht ↦ hM ht.symm⟩

/-- Corestricting the lifted comodule along `ι` recovers the original comodule. -/
theorem corestrict_ofCorestrict :
    (letI := ofCorestrict ι hM hMM h; Corestrict (M := M) ι) = ‹Comodule R C M› := by
  ext m
  exact lTensor_coact_ofCorestrict ι hM hMM h m

/-- The lifted and original coactions have the same fixed vectors, provided `ι` preserves the
distinguished elements. -/
theorem mem_fixedSubcomodule_ofCorestrict_iff [One C] [One D] (h1 : ι 1 = 1) {m : M} :
    m ∈ (letI := ofCorestrict ι hM hMM h; fixedSubcomodule R D M) ↔
      m ∈ fixedSubcomodule R C M := by
  let := ofCorestrict ι hM hMM h
  rw [mem_fixedSubcomodule, mem_fixedSubcomodule, coact_ofCorestrict_eq_iff,
    LinearMap.lTensor_tmul, CoalgHom.toLinearMap_eq_ofClass, CoalgHom.coe_linearMapOfClass, h1,
    eq_comm]

variable {N : Type y} [AddCommMonoid N] [Module R N] [Comodule R C N]
    (hN : Function.Injective (ι.toLinearMap.lTensor N))
    (hNN : Function.Injective ((TensorProduct.map ι.toLinearMap ι.toLinearMap).lTensor N))
    (h' : ∀ n : N, coact (R := R) (C := C) n ∈ LinearMap.range (ι.toLinearMap.lTensor N))

/-- A morphism of `C`-comodules is a morphism of the lifted `D`-comodules. -/
noncomputable def Hom.ofCorestrict (g : Hom R C M N) :
    letI := Comodule.ofCorestrict ι hM hMM h
    letI := Comodule.ofCorestrict ι hN hNN h'
    Hom R D M N :=
  letI := Comodule.ofCorestrict ι hM hMM h
  letI := Comodule.ofCorestrict ι hN hNN h'
  { toLinearMap := g.toLinearMap
    map_coact := by
      ext m
      apply hN
      have hcomm : ι.toLinearMap.lTensor N ∘ₗ TensorProduct.map g.toLinearMap LinearMap.id =
          TensorProduct.map g.toLinearMap LinearMap.id ∘ₗ ι.toLinearMap.lTensor M := by
        simpa only [LinearMap.lTensor] using
          LinearMap.lTensor_comp_map_id_comm g.toLinearMap ι.toLinearMap
      simp only [LinearMap.comp_apply]
      rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
      simp only [CoalgHom.toLinearMap_eq_ofClass]
      rw [lTensor_coact_ofCorestrict, lTensor_coact_ofCorestrict]
      exact Hom.map_coact_apply g m }

/-- The lifted morphism has the same underlying function. -/
@[simp]
theorem Hom.ofCorestrict_apply (g : Hom R C M N) (m : M) :
    Hom.ofCorestrict ι hM hMM h hN hNN h' g m = g m :=
  (rfl)

end TauCeti.Comodule
