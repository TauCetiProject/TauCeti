/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv

/-!
# Enlarging the ambient submonoid of a Hecke coset module

When `Δ₁ ≤ Δ₂` are submonoids of a group `G` and the subgroups `H₁, H₂, H₃ ≤ G` are held fixed,
widening the ambient submonoid from `Δ₁` to `Δ₂` embeds `HeckeCoset Δ₁ H₁ H₂` into
`HeckeCoset Δ₂ H₁ H₂` without merging any double cosets (`HeckeCoset.map_injective_of_le`): each
double coset `H₁gH₂` has the same underlying subset of `G` (`HeckeCoset.toSet_map_of_le`) and the
same decomposition quotients, and when `g ∈ Δ₁` and `h ∈ Δ₁` every double coset occurring with
nonzero multiplicity in `H₁gH₂hH₃` already lies in `Δ₁`.

Consequently, pushing finitely supported linear combinations forward along `HeckeCoset.map` gives
an injective `R`-linear map `HeckeCosetModule.mapSubmonoid` compatible with the bimodule
convolution product `HeckeCosetModule.mul`, and in the diagonal case `H₁ = H₂ = H` an injective
ring homomorphism `HeckeCosetModule.mapSubmonoidRingHom : 𝕋 Δ₁ H R →+* 𝕋 Δ₂ H R` over any
coefficient semiring `R`.

This is the abstract half of Shimura's Proposition 3.16 / Rhodes–Shemanske §2 embedding of an
integral Hecke ring (such as `H(SL_n(ℤ), M_n^+(ℤ))`) into its rational counterpart
(`H(SL_n(ℤ), GL_n^+(ℚ))`).

## Main definitions and results

* `HeckeCoset.toSet_map_of_le`, `HeckeCoset.map_injective_of_le`,
  `HeckeCoset.mem_range_map_of_le_iff`: keeping the subgroups fixed preserves the underlying
  double coset in `G`, so `HeckeCoset.map hΔ le_rfl le_rfl` is injective with range the double
  cosets whose representatives lie in `Δ₁`.
* `HeckeCosetModule.mapSubmonoid`: the injective `R`-linear map
  `HeckeCosetModule Δ₁ H₁ H₂ R →ₗ[R] HeckeCosetModule Δ₂ H₁ H₂ R` induced by `Δ₁ ≤ Δ₂`.
* `HeckeCosetModule.mapSubmonoid_mul`: `mapSubmonoid` intertwines the bimodule convolution product
  `HeckeCosetModule.mul`.
* `HeckeCosetModule.mapSubmonoidRingHom`: the injective ring homomorphism
  `𝕋 Δ₁ H R →+* 𝕋 Δ₂ H R` induced by `Δ₁ ≤ Δ₂`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1–3.2.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §2.
-/

public section

open DoubleCoset

namespace HeckeCoset

variable {G : Type*} [Group G] {Δ₁ Δ₂ : Submonoid G} {H₁ H₂ H H' : Subgroup G}

/-- Widening the ambient submonoid while keeping the left and right subgroups fixed leaves the
underlying subset `H₁gH₂ ⊆ G` unchanged. -/
@[simp]
theorem toSet_map_of_le (hΔ : Δ₁ ≤ Δ₂) (D : HeckeCoset Δ₁ H₁ H₂) :
    (D.map hΔ le_rfl le_rfl).toSet = D.toSet := by
  induction D using HeckeCoset.induction with | h g => simp

/-- Widening the ambient submonoid with the subgroups fixed injects `HeckeCoset Δ₁ H₁ H₂` into
`HeckeCoset Δ₂ H₁ H₂`: two elements of `Δ₁` spanning the same `(H₁, H₂)`-double coset in `G`
already define equal classes in `HeckeCoset Δ₁ H₁ H₂`. -/
theorem map_injective_of_le (hΔ : Δ₁ ≤ Δ₂) :
    Function.Injective (HeckeCoset.map hΔ (le_refl H₁) (le_refl H₂)) := fun D₁ D₂ h ↦
  toSet_injective (by rw [← toSet_map_of_le hΔ D₁, ← toSet_map_of_le hΔ D₂, h])

/-- For a Hecke triple `(H₁, Δ₁, H₂)` with `Δ₁ ≤ Δ₂`, a double coset of `Δ₂` lies in the image of
`HeckeCoset Δ₁ H₁ H₂` if and only if its chosen representative lies in `Δ₁`. -/
theorem mem_range_map_of_le_iff [IsHeckeTriple Δ₁ H₁ H₂] (hΔ : Δ₁ ≤ Δ₂)
    {E : HeckeCoset Δ₂ H₁ H₂} :
    E ∈ Set.range (HeckeCoset.map hΔ (le_refl H₁) (le_refl H₂)) ↔ (E.rep : G) ∈ Δ₁ := by
  refine ⟨?_, fun hE ↦ ⟨mk H₁ H₂ ⟨(E.rep : G), hE⟩, by rw [map_mk]; exact mk_rep E⟩⟩
  rintro ⟨D, rfl⟩
  have hmem : ((D.map hΔ le_rfl le_rfl).rep : G) ∈ doubleCoset (D.rep : G) H₁ H₂ := by
    rw [← toSet_eq_doubleCoset_rep, ← toSet_map_of_le hΔ]; exact rep_mem _
  exact IsHeckeTriple.mem_of_mem_doubleCoset D.rep.2 hmem

/-- `HeckeCoset.map` preserves the identity double coset. -/
@[simp]
theorem map_one (hΔ : Δ₁ ≤ Δ₂) (hH : H ≤ H') :
    HeckeCoset.map hΔ hH hH (1 : HeckeCoset Δ₁ H H) = (1 : HeckeCoset Δ₂ H' H') := by
  rw [one_def, one_def, map_mk]; rfl

end HeckeCoset

namespace HeckeCosetModule

open scoped HeckeCosetModule

variable {G : Type*} [Group G] {Δ₁ Δ₂ Δ₃ : Submonoid G} {H₁ H₂ H₃ H : Subgroup G}

section LinearMap

variable (R : Type*) [Semiring R]

/-- Push finitely supported double-coset combinations forward along a submonoid inclusion
`Δ₁ ≤ Δ₂` with the subgroups `H₁, H₂` held fixed. -/
noncomputable def mapSubmonoid (hΔ : Δ₁ ≤ Δ₂) :
    HeckeCosetModule Δ₁ H₁ H₂ R →ₗ[R] HeckeCosetModule Δ₂ H₁ H₂ R :=
  Finsupp.lmapDomain R R (HeckeCoset.map hΔ le_rfl le_rfl)

/-- Evaluating `mapSubmonoid R hΔ f` at an embedded coset recovers `f` at the source coset. -/
@[simp]
theorem mapSubmonoid_apply_map (hΔ : Δ₁ ≤ Δ₂) (f : HeckeCosetModule Δ₁ H₁ H₂ R)
    (D : HeckeCoset Δ₁ H₁ H₂) :
    mapSubmonoid R hΔ f (D.map hΔ le_rfl le_rfl) = f D :=
  Finsupp.mapDomain_apply_of_injective (HeckeCoset.map_injective_of_le hΔ) f D

/-- Outside the image of `HeckeCoset Δ₁ H₁ H₂`, `mapSubmonoid R hΔ f` vanishes. -/
theorem mapSubmonoid_apply_of_notMem_range (hΔ : Δ₁ ≤ Δ₂) (f : HeckeCosetModule Δ₁ H₁ H₂ R)
    {E : HeckeCoset Δ₂ H₁ H₂}
    (hE : E ∉ Set.range (HeckeCoset.map hΔ (le_refl H₁) (le_refl H₂))) :
    mapSubmonoid R hΔ f E = 0 :=
  Finsupp.mapDomain_of_notMem_range f E hE

/-- `mapSubmonoid` sends each basis element `single R D b` to the corresponding basis element in
`Δ₂`. -/
@[simp]
theorem mapSubmonoid_single (hΔ : Δ₁ ≤ Δ₂) (D : HeckeCoset Δ₁ H₁ H₂) (b : R) :
    mapSubmonoid R hΔ (single R D b) = single R (D.map hΔ le_rfl le_rfl) b := by
  classical
  ext E
  by_cases hE : E ∈ Set.range (HeckeCoset.map hΔ (le_refl H₁) (le_refl H₂))
  · obtain ⟨D', rfl⟩ := hE
    rw [mapSubmonoid_apply_map, single_apply, single_apply,
      (HeckeCoset.map_injective_of_le hΔ).eq_iff]
  · rw [mapSubmonoid_apply_of_notMem_range R hΔ _ hE, single_apply, ite_eq_right]
    rintro rfl; exact hE ⟨D, rfl⟩

/-- Enlarging the ambient submonoid embeds `HeckeCosetModule Δ₁ H₁ H₂ R` injectively into
`HeckeCosetModule Δ₂ H₁ H₂ R`. -/
theorem mapSubmonoid_injective (hΔ : Δ₁ ≤ Δ₂) :
    Function.Injective (mapSubmonoid R (H₁ := H₁) (H₂ := H₂) hΔ) :=
  Finsupp.mapDomain_injective (HeckeCoset.map_injective_of_le hΔ)

/-- `mapSubmonoid` acts as the identity along `Δ₁ ≤ Δ₁`. -/
@[simp]
theorem mapSubmonoid_id :
    mapSubmonoid R (H₁ := H₁) (H₂ := H₂) (le_refl Δ₁) = LinearMap.id := by
  ext f; induction f using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd _ _ h₁ h₂ => simp [h₁, h₂]
  | hsingle _ _ => simp

/-- `mapSubmonoid` is functorial along a chain `Δ₁ ≤ Δ₂ ≤ Δ₃`. -/
theorem mapSubmonoid_comp (h₁₂ : Δ₁ ≤ Δ₂) (h₂₃ : Δ₂ ≤ Δ₃) :
    (mapSubmonoid R (H₁ := H₁) (H₂ := H₂) h₂₃).comp (mapSubmonoid R h₁₂) =
      mapSubmonoid R (h₁₂.trans h₂₃) := by
  refine LinearMap.ext fun f ↦ ?_
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd _ _ h₁ h₂ => simp only [LinearMap.comp_apply, map_add] at h₁ h₂ ⊢; rw [h₁, h₂]
  | hsingle _ _ => simp

/-- `mapSubmonoid` preserves the multiplicative identity of a Hecke ring. -/
@[simp]
theorem mapSubmonoid_one (hΔ : Δ₁ ≤ Δ₂) :
    mapSubmonoid R hΔ (1 : 𝕋 Δ₁ H R) = (1 : 𝕋 Δ₂ H R) := by
  rw [one_def, one_def, mapSubmonoid_single, HeckeCoset.map_one]

/-- Pushing the structure constants at `(D₁, D₂)` along `Δ₁ ≤ Δ₂` yields the structure constants
at the mapped cosets. -/
theorem mapSubmonoid_structureConstants [IsHeckeTriple Δ₁ H₁ H₂] [IsHeckeTriple Δ₁ H₂ H₃]
    [IsHeckeTriple Δ₂ H₁ H₂] [IsHeckeTriple Δ₂ H₂ H₃] (hΔ : Δ₁ ≤ Δ₂)
    (D₁ : HeckeCoset Δ₁ H₁ H₂) (D₂ : HeckeCoset Δ₁ H₂ H₃) :
    mapSubmonoid R hΔ (structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep) =
      structureConstants R H₁ H₂ H₃ (D₁.map hΔ le_rfl le_rfl).rep
        (D₂.map hΔ le_rfl le_rfl).rep := by
  have hrep {A B : Subgroup G} (D : HeckeCoset Δ₁ A B) :
      (((D.map hΔ le_rfl le_rfl).rep : Δ₂) : G) ∈ doubleCoset (D.rep : G) A B := by
    rw [← HeckeCoset.toSet_eq_doubleCoset_rep, ← HeckeCoset.toSet_map_of_le hΔ]
    exact HeckeCoset.rep_mem _
  ext E
  by_cases hE : E ∈ Set.range (HeckeCoset.map hΔ (le_refl H₁) (le_refl H₃))
  · obtain ⟨D, rfl⟩ := hE
    rw [mapSubmonoid_apply_map, structureConstants_apply, structureConstants_apply,
      multiplicity_doubleCoset_congr_first H₁ H₂ H₃ _ _ (hrep D₁),
      multiplicity_doubleCoset_congr_second H₁ H₂ H₃ _ _ (hrep D₂),
      multiplicity_doubleCoset_congr _ _ (hrep D)]
  · rw [mapSubmonoid_apply_of_notMem_range R hΔ _ hE, structureConstants_apply,
      multiplicity_doubleCoset_congr_first H₁ H₂ H₃ _ _ (hrep D₁),
      multiplicity_doubleCoset_congr_second H₁ H₂ H₃ _ _ (hrep D₂)]
    suffices hm : multiplicity H₁ H₂ H₃ (D₁.rep : G) (D₂.rep : G) (E.rep : G) = 0 by
      rw [hm, Nat.cast_zero]
    by_contra hne
    obtain ⟨w, hw, k, hk, hEq⟩ := mem_doubleCoset.mp (multiplicity_ne_zero_iff.mp hne)
    have : IsHeckeTriple Δ₁ H₁ H₃ := IsHeckeTriple.trans (H₂ := H₂)
    exact hE ((HeckeCoset.mem_range_map_of_le_iff hΔ).mpr (hEq ▸
      Δ₁.mul_mem (Δ₁.mul_mem (IsHeckeTriple.mem_of_mem_doubleCoset D₁.rep.2 hw) D₂.rep.2)
        (IsHeckeTriple.mem_of_mem_right H₂ hk)))

/-- `mapSubmonoid` intertwines the bimodule convolution product `HeckeCosetModule.mul`. -/
theorem mapSubmonoid_mul [IsHeckeTriple Δ₁ H₁ H₂] [IsHeckeTriple Δ₁ H₂ H₃]
    [IsHeckeTriple Δ₂ H₁ H₂] [IsHeckeTriple Δ₂ H₂ H₃] (hΔ : Δ₁ ≤ Δ₂)
    (f : HeckeCosetModule Δ₁ H₁ H₂ R) (g : HeckeCosetModule Δ₁ H₂ H₃ R) :
    mapSubmonoid R hΔ (mul R f g) = mul R (mapSubmonoid R hΔ f) (mapSubmonoid R hΔ g) := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp [zero_mul]
  | hadd _ _ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
  | hsingle D₁ a =>
    induction g using HeckeCosetModule.induction_linear with
    | h0 => simp [mul_zero]
    | hadd _ _ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
    | hsingle D₂ b =>
      rw [mul_single_single, map_smul, map_smul, mapSubmonoid_structureConstants R hΔ,
        mapSubmonoid_single, mapSubmonoid_single, mul_single_single]

/-- Enlarging the ambient submonoid from `Δ₁` to `Δ₂` induces an injective ring homomorphism
`𝕋 Δ₁ H R →+* 𝕋 Δ₂ H R` over any coefficient semiring `R`. -/
noncomputable def mapSubmonoidRingHom [IsHeckeTriple Δ₁ H H] [IsHeckeTriple Δ₂ H H]
    (hΔ : Δ₁ ≤ Δ₂) : 𝕋 Δ₁ H R →+* 𝕋 Δ₂ H R where
  toFun := mapSubmonoid R hΔ
  map_one' := mapSubmonoid_one R hΔ
  map_mul' f g := mapSubmonoid_mul R hΔ f g
  map_zero' := map_zero _
  map_add' := map_add _

/-- `mapSubmonoidRingHom` coerces to `mapSubmonoid`. -/
@[simp]
theorem coe_mapSubmonoidRingHom [IsHeckeTriple Δ₁ H H] [IsHeckeTriple Δ₂ H H]
    (hΔ : Δ₁ ≤ Δ₂) :
    ⇑(mapSubmonoidRingHom R (H := H) hΔ) = mapSubmonoid R hΔ :=
  (rfl)

/-- `mapSubmonoidRingHom` sends a basis element `single R D b` to the mapped basis element. -/
@[simp]
theorem mapSubmonoidRingHom_single [IsHeckeTriple Δ₁ H H] [IsHeckeTriple Δ₂ H H]
    (hΔ : Δ₁ ≤ Δ₂) (D : HeckeCoset Δ₁ H H) (b : R) :
    mapSubmonoidRingHom R hΔ (single R D b) = single R (D.map hΔ le_rfl le_rfl) b :=
  mapSubmonoid_single R hΔ D b

/-- `mapSubmonoidRingHom` is injective. -/
theorem mapSubmonoidRingHom_injective [IsHeckeTriple Δ₁ H H] [IsHeckeTriple Δ₂ H H]
    (hΔ : Δ₁ ≤ Δ₂) :
    Function.Injective (mapSubmonoidRingHom R (H := H) hΔ) :=
  mapSubmonoid_injective R hΔ

/-- `mapSubmonoidRingHom` along `Δ₁ ≤ Δ₁` is the identity ring homomorphism. -/
@[simp]
theorem mapSubmonoidRingHom_id [IsHeckeTriple Δ₁ H H] :
    mapSubmonoidRingHom R (H := H) (le_refl Δ₁) = RingHom.id (𝕋 Δ₁ H R) :=
  RingHom.ext fun f ↦ DFunLike.congr_fun (mapSubmonoid_id R) f

/-- `mapSubmonoidRingHom` is functorial along `Δ₁ ≤ Δ₂ ≤ Δ₃`. -/
theorem mapSubmonoidRingHom_comp [IsHeckeTriple Δ₁ H H] [IsHeckeTriple Δ₂ H H]
    [IsHeckeTriple Δ₃ H H] (h₁₂ : Δ₁ ≤ Δ₂) (h₂₃ : Δ₂ ≤ Δ₃) :
    (mapSubmonoidRingHom R (H := H) h₂₃).comp (mapSubmonoidRingHom R h₁₂) =
      mapSubmonoidRingHom R (h₁₂.trans h₂₃) :=
  RingHom.ext fun f ↦ DFunLike.congr_fun (mapSubmonoid_comp R h₁₂ h₂₃) f

end LinearMap

end HeckeCosetModule

end
