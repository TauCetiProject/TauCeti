/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.Integral

/-!
# Valuation extensions from valuative relations

Mathlib has two compatible notions of one valuation extending another. `ValuativeExtension A B`
states the relation intrinsically, without choosing value groups, while
`Valuation.HasExtension vA vB` states that the pullback of `vB` is equivalent to `vA`.

This file supplies the canonical bridge for the valuations attached to valuative relations. It
allows Mathlib's valuation-extension API, including its algebra maps between valuation rings and
residue fields, to be used directly from a `ValuativeExtension` hypothesis: through it, Mathlib's
instance `Valuation.HasExtension.instAlgebraInteger` provides the algebra structure on the
valuation rings.

In an algebraic field extension, the nonzero values of the base field are coinitial among the
nonzero values of the extension. This provides the small base-field elements needed to compare
the two valuative topologies.

## Main results

* `ValuativeExtension.trans`: compatibility of valuative relations in an algebra tower.
* `ValuativeExtension.of_tower_top`: compatibility of the bottom step of a tower whose
  top step and composite are compatible.
* `ValuativeExtension.valuationHasExtension`: the canonical valuation on `B` extends the
  canonical valuation on `A`.
* `ValuativeRel.IsNontrivial.of_valuativeExtension`: a compatible extension of a nontrivial
  valuative relation is nontrivial.
* `TauCeti.residueFieldAlgebra`: the induced algebra structure on the residue fields.
* `TauCeti.algebraMap_comp_algebraMap_integerRing`: the structure maps of the valuation rings and
  of the fields form a commuting square.
* `TauCeti.algebraMap_integerRing_dvd_iff`: the map of valuation rings reflects divisibility.
* `TauCeti.aroots_eq_map_roots_integerRing`: the roots in `L` of a monic polynomial over the
  valuation ring of `K` are its roots in the valuation ring of `L`.
* `ValuativeExtension.valuation_algebraMap_le_one_iff` and
  `ValuativeExtension.valuation_algebraMap_lt_one_iff`: a compatible extension preserves and
  reflects `valuation · ≤ 1` and `valuation · < 1`.
* `ValuativeExtension.residueField_algebraMap_residue`: the induced map on residue fields
  intertwines the residue maps.
* `IsAlgebraic.exists_ne_zero_vle`: a nonzero algebraic element has value at least that of some
  nonzero base-field element.
* `AlgHom.aeval_residue_minpoly_eq_zero`: a residue embedding sends the residue of an integer to a
  root of the reduction of its minimal polynomial.
* `AlgEquiv.integerAlgEquivOfMemInteger`: restriction of a valuation-ring-preserving field
  automorphism `L ≃ₐ[K] L` to an integer-ring automorphism `𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]`.
-/

public section

open ValuativeRel

namespace ValuativeExtension

/-- Compatibility of valuative relations composes along an algebra tower. -/
theorem trans (A B C : Type*) [CommSemiring A] [CommSemiring B] [Semiring C]
    [ValuativeRel A] [ValuativeRel B] [ValuativeRel C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [ValuativeExtension A B] [ValuativeExtension B C] : ValuativeExtension A C where
  vle_iff_vle := by
    intro a b
    simp only [IsScalarTower.algebraMap_apply A B C, ValuativeExtension.vle_iff_vle]

/-- Compatibility of valuative relations descends to the bottom step of an algebra tower whose
top step and composite are compatible. -/
theorem of_tower_top (A B C : Type*) [CommSemiring A] [CommSemiring B]
    [Semiring C] [ValuativeRel A] [ValuativeRel B] [ValuativeRel C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [ValuativeExtension A C] [ValuativeExtension B C] : ValuativeExtension A B where
  vle_iff_vle := by
    intro a b
    rw [← ValuativeExtension.vle_iff_vle (A := B) (B := C), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, ValuativeExtension.vle_iff_vle]

variable {A B : Type*} [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/-- A compatible extension of valuative relations makes the canonical valuation on the larger
ring an extension, in Mathlib's valuation-level sense, of the canonical valuation on the base.
-/
instance valuationHasExtension :
    Valuation.HasExtension (valuation A) (valuation B) where
  val_isEquiv_comap :=
    (ValuativeRel.isEquiv ((valuation B).comap (algebraMap A B)) (valuation A)).symm

variable (A) in
/-- A compatible extension of a nontrivial valuative relation is nontrivial: the map of value
groups is strictly monotone, so it carries a value other than `0` and `1` to another such value.
-/
theorem _root_.ValuativeRel.IsNontrivial.of_valuativeExtension [IsNontrivial A] :
    IsNontrivial B := by
  obtain ⟨γ, h0, h1⟩ := IsNontrivial.condition (R := A)
  have hinj := (mapValueGroupWithZero_strictMono (A := A) (B := B)).injective
  exact ⟨mapValueGroupWithZero A B γ, by rwa [← map_zero (mapValueGroupWithZero A B), hinj.ne_iff],
    by rwa [← map_one (mapValueGroupWithZero A B), hinj.ne_iff]⟩

/-- A compatible extension preserves and reflects `valuation · ≤ 1`. -/
theorem valuation_algebraMap_le_one_iff (x : A) :
    valuation B (algebraMap A B x) ≤ 1 ↔ valuation A x ≤ 1 := by
  rw [← mapValueGroupWithZero_valuation, ← map_one (mapValueGroupWithZero A B),
    (mapValueGroupWithZero_strictMono (A := A) (B := B)).le_iff_le]

/-- A compatible extension preserves and reflects `valuation · < 1`. -/
theorem valuation_algebraMap_lt_one_iff (x : A) :
    valuation B (algebraMap A B x) < 1 ↔ valuation A x < 1 := by
  rw [← mapValueGroupWithZero_valuation, ← map_one (mapValueGroupWithZero A B),
    (mapValueGroupWithZero_strictMono (A := A) (B := B)).lt_iff_lt]

end ValuativeExtension

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

local notation "𝒪ᵥ[" K "]" => Valuation.integer (valuation K)
local notation "𝓀ᵥ[" K "]" => IsLocalRing.ResidueField ↥𝒪ᵥ[K]

/-- The local map on rings of integers induces the residue-field extension.

This is Mathlib's `IsLocalRing.ResidueField.instAlgebra`, which would also be found directly.
Declaring it here fixes its `IsLocalHom` witness once, in a context with no further hypotheses,
so the residue-field algebra elaborates to the same term whatever else is in context (an
`IsGalois K L` hypothesis, for instance, would otherwise enter the proof that the map of rings of
integers is local). -/
noncomputable instance residueFieldAlgebra : Algebra 𝓀ᵥ[K] 𝓀ᵥ[L] :=
  IsLocalRing.ResidueField.instAlgebra

/-- The square from `𝒪ᵥ[K]` to `L` through `𝒪ᵥ[L]` and through `K` commutes. -/
theorem algebraMap_comp_algebraMap_integerRing :
    (algebraMap 𝒪ᵥ[L] L).comp (algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L]) =
      (algebraMap K L).comp (algebraMap 𝒪ᵥ[K] K) := by
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- The integer-ring structure map reflects divisibility: an integer of `K` divides another in the
integers of `L` exactly when it does in the integers of `K`, since both say that its value is
at least the other's. -/
@[simp]
theorem algebraMap_integerRing_dvd_iff {x y : 𝒪ᵥ[K]} :
    algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L] x ∣ algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L] y ↔ x ∣ y := by
  rw [(Valuation.integer.integers _).dvd_iff_le, (Valuation.integer.integers _).dvd_iff_le,
    ← RingHom.comp_apply, ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq]
  simp only [IsScalarTower.algebraMap_apply 𝒪ᵥ[K] K L]
  exact Valuation.HasExtension.val_map_le_iff (vR := valuation K) (vA := valuation L) _ _

open Polynomial in
variable (L) in
/-- The roots in `L` of a monic polynomial over `𝒪ᵥ[K]` are integral, so they are the images of
its roots in `𝒪ᵥ[L]`, with the same multiplicities. -/
theorem aroots_eq_map_roots_integerRing {p : 𝒪ᵥ[K][X]} (hp : p.Monic) :
    (p.map (algebraMap 𝒪ᵥ[K] K)).aroots L =
      (p.map (algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L])).roots.map (algebraMap 𝒪ᵥ[L] L) := by
  classical
  set P := p.map (algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L])
  have hι : Function.Injective (algebraMap 𝒪ᵥ[L] L) := FaithfulSMul.algebraMap_injective _ _
  have hPL : (p.map (algebraMap 𝒪ᵥ[K] K)).map (algebraMap K L) = P.map (algebraMap 𝒪ᵥ[L] L) := by
    rw [map_map, map_map, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  rw [aroots_def, hPL, ← filter_roots_map_range_eq_map_roots hι, Multiset.filter_eq_self.2]
  intro x hx
  have hv := Valuation.integer.integers (valuation L)
  exact RingHom.mem_range.2 <| hv.exists_of_le_one <| hv.isIntegral_iff_v_le_one.1 <|
    roots_mem_integralClosure (hp.map _) (by rwa [aroots_def])

end TauCeti

variable {K L : Type*} [Field K] [Field L] [ValuativeRel L] [Algebra K L]

/-- In a valued field extension, every nonzero algebraic element has value at least
that of some nonzero base-field element. -/
theorem IsAlgebraic.exists_ne_zero_vle {y : L} (halg : IsAlgebraic K y) (hy : y ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ algebraMap K L x ≤ᵥ y := by
  -- Clear denominators over the base valuation ring, then use integrally closedness of the
  -- target valuation ring to bound the resulting multiple of `y⁻¹`.
  let v := (valuation L).comap (algebraMap K L)
  have : Valuation.HasExtension v (valuation L) := ⟨.refl⟩
  obtain ⟨a, ha⟩ := halg.inv.isIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors v.integer) y⁻¹
  have hai : IsIntegral (valuation L).integer (a • y⁻¹) := ha.tower_top
  have hav : valuation L (a • y⁻¹) ≤ 1 :=
    (Valuation.integer.integers (valuation L)).isIntegral_iff_v_le_one.mp hai
  have hyv : 0 < valuation L y := zero_lt_iff.mpr (by simpa using hy)
  refine ⟨a, ?_, ?_⟩
  · exact_mod_cast (nonZeroDivisors.ne_zero a.property)
  · rw [(valuation L).vle_iff_le]
    simpa [Submonoid.smul_def, Algebra.smul_def,
      IsScalarTower.algebraMap_apply v.integer K L,
      Algebra.algebraMap_ofSubring, mul_inv_le_iff₀ hyv] using hav

namespace AlgHom

variable {K L M : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
  [ValuativeExtension K L] [Field M] [ValuativeRel M] [Algebra K M] [ValuativeExtension K M]

local notation "𝒪ᵥ[" K "]" => Valuation.integer (valuation K)
local notation "𝓀ᵥ[" K "]" => IsLocalRing.ResidueField ↥𝒪ᵥ[K]

/-- The image under a residue embedding `φ` of the residue of `z ∈ 𝒪ᵥ[L]` is a root of the
reduction of the minimal polynomial of `z` over `𝒪ᵥ[K]`. -/
@[simp]
theorem aeval_residue_minpoly_eq_zero (φ : 𝓀ᵥ[L] →ₐ[𝓀ᵥ[K]] 𝓀ᵥ[M]) (z : 𝒪ᵥ[L]) :
    Polynomial.aeval (φ (IsLocalRing.residue 𝒪ᵥ[L] z)) (minpoly 𝒪ᵥ[K] (z : L)) = 0 := by
  have hz : (z : L) = algebraMap 𝒪ᵥ[L] L z :=
    (Algebra.algebraMap_ofSubsemiring_apply 𝒪ᵥ[L] z).symm
  rw [hz, minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective 𝒪ᵥ[L] L) z]
  exact minpoly.aeval_algHom (A := 𝒪ᵥ[K])
    ((φ.restrictScalars 𝒪ᵥ[K]).comp (IsScalarTower.toAlgHom 𝒪ᵥ[K] 𝒪ᵥ[L] 𝓀ᵥ[L])) z

end AlgHom

section ResidueAndAlgEquiv

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

local notation "𝒪ᵥ[" K "]" => Valuation.integer (valuation K)
local notation "𝓀ᵥ[" K "]" => IsLocalRing.ResidueField ↥𝒪ᵥ[K]

/-- The induced map on residue fields of a `ValuativeExtension` intertwines the residue maps. -/
theorem ValuativeExtension.residueField_algebraMap_residue (x : 𝒪ᵥ[K]) :
    algebraMap 𝓀ᵥ[K] 𝓀ᵥ[L] (IsLocalRing.residue 𝒪ᵥ[K] x) =
      IsLocalRing.residue 𝒪ᵥ[L] (algebraMap 𝒪ᵥ[K] 𝒪ᵥ[L] x) :=
  Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap (valuation K) (valuation L) x

namespace AlgEquiv

/-- Restriction of a `K`-algebra automorphism `σ : L ≃ₐ[K] L` preserving `𝒪[L]` in both directions
to an `𝒪[K]`-algebra automorphism of `𝒪[L]`. -/
noncomputable def integerAlgEquivOfMemInteger (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪ᵥ[L] ↔ z ∈ 𝒪ᵥ[L]) :
    𝒪ᵥ[L] ≃ₐ[𝒪ᵥ[K]] 𝒪ᵥ[L] where
  toFun x := ⟨σ x.1, (hσ x.1).2 x.2⟩
  invFun x := ⟨σ.symm x.1, (hσ (σ.symm x.1)).1 (by rw [σ.apply_symm_apply]; exact x.2)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (map_mul σ x.1 y.1)
  map_add' x y := Subtype.ext (map_add σ x.1 y.1)
  commutes' r := Subtype.ext (by
    simp only [Valuation.HasExtension.val_algebraMap]
    exact σ.commutes (r : K))

@[simp]
theorem coe_integerAlgEquivOfMemInteger_apply (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪ᵥ[L] ↔ z ∈ 𝒪ᵥ[L]) (x : 𝒪ᵥ[L]) :
    (σ.integerAlgEquivOfMemInteger hσ x : L) = σ (x : L) :=
  (rfl)

@[simp]
theorem coe_integerAlgEquivOfMemInteger_symm_apply (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪ᵥ[L] ↔ z ∈ 𝒪ᵥ[L]) (x : 𝒪ᵥ[L]) :
    ((σ.integerAlgEquivOfMemInteger hσ).symm x : L) = σ.symm (x : L) :=
  (rfl)

theorem coe_integerAlgEquivOfMemInteger_pow_apply (σ : L ≃ₐ[K] L)
    (hσ : ∀ z : L, σ z ∈ 𝒪ᵥ[L] ↔ z ∈ 𝒪ᵥ[L]) (n : ℕ) (x : 𝒪ᵥ[L]) :
    ((σ.integerAlgEquivOfMemInteger hσ ^ n) x : L) = (σ ^ n) (x : L) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply,
      coe_integerAlgEquivOfMemInteger_apply, ih]

end AlgEquiv

end ResidueAndAlgEquiv
