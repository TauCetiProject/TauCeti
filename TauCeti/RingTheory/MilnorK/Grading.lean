/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import TauCeti.LinearAlgebra.TensorSquare
public import TauCeti.RingTheory.MilnorK.Homogeneous
public import TauCeti.RingTheory.MilnorK.SteinbergPairing

import Mathlib.LinearAlgebra.Quotient.Basic
import TauCeti.Algebra.Group.TypeTags.Hom
import TauCeti.Algebra.Module.LinearMap.Defs
import TauCeti.Algebra.Ring.Hom

/-!
# Graded maps and degree-two symbol-group identification for Milnor K-theory

Building on the homogeneous tensor-power presentation `TauCeti.MilnorK.degreeEquiv` and internal
`ℕ`-grading `TauCeti.MilnorK.instGradedRingDegree` in `TauCeti.RingTheory.MilnorK.Homogeneous`,
this file provides:

* the graded universal property `MilnorK.gradedLift`, graded functoriality `MilnorK.gradedMap`
  (with extensionality `MilnorK.gradedRingHom_ext`), and the degree-`n` restriction
  `MilnorK.degreeMap`;
* the canonical identification `MilnorK.degreeTwoEquiv : MilnorK.degree R 2 ≃ₗ[ℤ] SymbolGroup R`,
  complementing `MilnorK.degreeZeroEquiv` and `MilnorK.degreeOneEquiv` in
  `TauCeti.RingTheory.MilnorK.Basic`, together with its naturality `MilnorK.degreeTwoEquiv_map`;
* functoriality `MilnorK.quotTensorPowerMap` on the tensor-power quotients
  `(⨂[ℤ]^n (Additive Rˣ)) ⧸ steinbergRelations R n` and naturality of `MilnorK.degreeEquiv` in
  arbitrary degree (`MilnorK.degreeEquiv_map`).

## Main definitions

* `TauCeti.MilnorK.gradedLift`: graded universal property for maps into any `ℕ`-graded ring.
* `TauCeti.MilnorK.gradedMap`: graded ring homomorphism induced by a ring homomorphism `R →+* S`.
* `TauCeti.MilnorK.degreeMap`: `ℤ`-linear map `degree R n →ₗ[ℤ] degree S n` induced by `R →+* S`.
* `TauCeti.MilnorK.degreeTwoEquiv`: identification of degree `2` with `SymbolGroup R`.
* `TauCeti.MilnorK.quotTensorPowerMap`: functoriality on degree-`n` tensor-power quotients.

## Main results

* `TauCeti.MilnorK.map_symbolGroupRelations_eq`: `TauCeti.SymbolGroup.relations R` corresponds to
  `TauCeti.MilnorK.steinbergRelations R 2` under `TauCeti.tensorProductEquivTensorSquare`.
* `TauCeti.MilnorK.degreeTwoEquiv_map`: naturality of `degreeTwoEquiv` with respect to ring
  homomorphisms.
* `TauCeti.MilnorK.degreeEquiv_map`: naturality of `degreeEquiv` in arbitrary degree `n`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Ch. III, §7.1.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.MilnorK

universe u v w

section Ring

variable {R : Type u} [CommRing R]

/-! ### Graded universal property and graded functoriality -/

/-- Two graded ring homomorphisms out of `MilnorK R` agree if they agree on every `ofUnit a`. -/
theorem gradedRingHom_ext {A : Type v} {σ : Type*} [Ring A] [SetLike σ A]
    {𝒜 : ℕ → σ} {f g : degree R →+*ᵍ 𝒜}
    (h : ∀ a : Rˣ, f (ofUnit a) = g (ofUnit a)) : f = g :=
  GradedRingHom.toRingHom_injective (ringHom_ext h)

/-- **Graded universal property of `MilnorK R`.** An additive homomorphism `f : Additive Rˣ →+ A`
into the degree-`1` piece of an `ℕ`-graded ring whose values on complementary units multiply to
zero extends uniquely to a graded ring homomorphism `MilnorK.degree R →+*ᵍ 𝒜`. -/
def gradedLift {A : Type v} {σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0) :
    degree R →+*ᵍ 𝒜 where
  __ := lift f hf_rel
  map_mem hx := lift_mem_of_mem_degree f hf_rel hf_deg hx

/-- Evaluating `MilnorK.gradedLift` on `ofUnit a` recovers `f (Additive.ofMul a)`. -/
@[simp]
theorem gradedLift_ofUnit {A : Type v} {σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)
    (a : Rˣ) :
    gradedLift 𝒜 f hf_deg hf_rel (ofUnit a) = f (Additive.ofMul a) :=
  lift_ofUnit f hf_rel a

/-- The underlying ring homomorphism of `MilnorK.gradedLift` is that of `MilnorK.lift`. -/
@[simp]
theorem toRingHom_gradedLift {A : Type v} {σ : Type*} [Ring A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0) :
    (gradedLift 𝒜 f hf_deg hf_rel).toRingHom = lift f hf_rel :=
  ringHom_ext fun a ↦ by
    simp only [GradedRingHom.coe_toRingHom, gradedLift_ofUnit, lift_ofUnit]

/-- Evaluating `MilnorK.gradedLift` on a symbol multiplies the images of its entries. -/
@[simp]
theorem gradedLift_symbol {A : Type v} {σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [SetLike.GradedMonoid 𝒜] (f : Additive Rˣ →+ A)
    (hf_deg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ 𝒜 1)
    (hf_rel : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)
    (l : List Rˣ) :
    gradedLift 𝒜 f hf_deg hf_rel (symbol l) = (l.map fun a ↦ f (Additive.ofMul a)).prod :=
  lift_symbol f hf_rel l

/-- Functoriality of `MilnorK` as a graded ring homomorphism `degree R →+*ᵍ degree S`. -/
def gradedMap {S : Type w} [CommRing S] (f : R →+* S) : degree R →+*ᵍ degree S where
  __ := map f
  map_mem hx := map_mem_degree f hx

/-- Evaluating `MilnorK.gradedMap f` on `ofUnit a` gives `ofUnit (Units.map f a)`. -/
@[simp]
theorem gradedMap_ofUnit {S : Type w} [CommRing S] (f : R →+* S) (a : Rˣ) :
    gradedMap f (ofUnit a) = ofUnit (Units.map f.toMonoidHom a) :=
  map_ofUnit f a

/-- The underlying ring homomorphism of `MilnorK.gradedMap f` is that of `MilnorK.map f`. -/
@[simp]
theorem toRingHom_gradedMap {S : Type w} [CommRing S] (f : R →+* S) :
    (gradedMap f).toRingHom = map f :=
  ringHom_ext fun a ↦ by
    simp only [GradedRingHom.coe_toRingHom, gradedMap_ofUnit, map_ofUnit,
      RingHom.toMonoidHom_eq_coe]

/-- Evaluating `MilnorK.gradedMap f` on a symbol maps its entries in unchanged order. -/
@[simp]
theorem gradedMap_symbol {S : Type w} [CommRing S] (f : R →+* S) (l : List Rˣ) :
    gradedMap f (symbol l) = symbol (l.map (Units.map f.toMonoidHom)) :=
  map_symbol f l

/-- The identity ring homomorphism induces the identity graded ring homomorphism on `MilnorK`. -/
@[simp]
theorem gradedMap_id (R : Type u) [CommRing R] :
    gradedMap (RingHom.id R) = GradedRingHom.id (degree R) :=
  GradedRingHom.toRingHom_injective (by simp [map_id])

/-- `MilnorK.gradedMap` respects composition of ring homomorphisms. -/
theorem gradedMap_comp {S : Type v} {T : Type w} [CommRing S] [CommRing T]
    (g : S →+* T) (f : R →+* S) :
    gradedMap (g.comp f) = (gradedMap g).comp (gradedMap f) := by
  refine GradedRingHom.toRingHom_injective ?_
  calc (gradedMap (g.comp f) : MilnorK R →+* MilnorK T)
      = map (g.comp f) := toRingHom_gradedMap (g.comp f)
    _ = (map g).comp (map f) := map_comp g f
    _ = ((gradedMap g).comp (gradedMap f) : MilnorK R →+* MilnorK T) := by
      ext a
      simp

/-- The `ℤ`-linear map `degree R n →ₗ[ℤ] degree S n` obtained by restricting `MilnorK.map f` to
degree `n`. -/
def degreeMap {S : Type w} [CommRing S] (f : R →+* S) (n : ℕ) : degree R n →ₗ[ℤ] degree S n :=
  (map f).toIntAlgHom.toLinearMap.restrict fun _ hx ↦ map_mem_degree f hx

/-- Coercing `MilnorK.degreeMap f n x` to `MilnorK S` gives `MilnorK.map f x`. -/
@[simp]
theorem coe_degreeMap {S : Type w} [CommRing S] (f : R →+* S) (n : ℕ) (x : degree R n) :
    (degreeMap f n x : MilnorK S) = map f x :=
  LinearMap.coe_restrict_apply _ x

/-- The identity ring homomorphism induces the identity on each degree `MilnorK.degree R n`. -/
@[simp]
theorem degreeMap_id (R : Type u) [CommRing R] (n : ℕ) :
    degreeMap (RingHom.id R) n = LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext (by simp)

/-- `MilnorK.degreeMap` respects composition of ring homomorphisms. -/
theorem degreeMap_comp {S : Type v} {T : Type w} [CommRing S] [CommRing T]
    (g : S →+* T) (f : R →+* S) (n : ℕ) :
    degreeMap (g.comp f) n = (degreeMap g n).comp (degreeMap f n) :=
  LinearMap.ext fun x ↦ Subtype.ext (by simp)

/-! ### Degree-two identification `K₂ᴹ ≃ SymbolGroup R` -/

/-- Normalizing `Additive.ofMul` on a two-entry vector of units inside a tensor square. -/
private theorem tprod_ofMul_fin_two (a b : Rˣ) :
    PiTensorProduct.tprod ℤ (fun k : Fin 2 ↦ Additive.ofMul (![a, b] k)) =
      PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b] := by
  simpa using TauCeti.tprod_fin_two (R := ℤ) (fun k : Fin 2 ↦ Additive.ofMul (![a, b] k))

/-- Under `TauCeti.tensorProductEquivTensorSquare`, the binary Steinberg relation submodule
`TauCeti.SymbolGroup.relations R` corresponds to `TauCeti.MilnorK.steinbergRelations R 2`. -/
theorem map_symbolGroupRelations_eq (R : Type u) [CommRing R] :
    (SymbolGroup.relations R).map
      (TauCeti.tensorProductEquivTensorSquare ℤ (Additive Rˣ)).toLinearMap =
      steinbergRelations R 2 := by
  refine le_antisymm ?_ ?_
  · rw [SymbolGroup.relations_eq_span]
    refine (Submodule.map_span_le _ _ _).mpr ?_
    rintro _ ⟨a, b, hab, rfl⟩
    rw [LinearEquiv.coe_coe, TauCeti.tensorProductEquivTensorSquare_tmul, ← tprod_ofMul_fin_two]
    exact tprod_mem_steinbergRelations ![a, b] 0 (by decide) (by simpa using hab)
  · rw [steinbergRelations_eq_span, Submodule.span_le]
    rintro _ ⟨f, i, hi, hab, rfl⟩
    have hi0 : i = 0 := by omega
    subst hi0
    refine (Submodule.mem_map_equiv _).mpr ?_
    rw [TauCeti.tensorProductEquivTensorSquare_symm_tprod, SymbolGroup.relations_eq_span]
    exact Submodule.subset_span ⟨f 0, f 1, hab, rfl⟩

/-- Canonical identification `MilnorK.degree R 2 ≃ₗ[ℤ] SymbolGroup R`. -/
noncomputable def degreeTwoEquiv (R : Type u) [CommRing R] :
    degree R 2 ≃ₗ[ℤ] SymbolGroup R :=
  (degreeEquiv R 2).symm.trans
    (Submodule.Quotient.equiv (SymbolGroup.relations R) (steinbergRelations R 2)
      -- Re-synthesize `[Ring ℤ]` / `AddCommGroup.toIntModule` instances expected by
      -- `Submodule.Quotient.equiv` at `implicit` transparency (unlike
      -- `tensorProductEquivTensorSquare`, which carries `[CommSemiring ℤ]` and
      -- `TensorProduct.instModule` / `PiTensorProduct.instModule`).
      (TauCeti.tensorProductEquivTensorSquare ℤ (Additive Rˣ)).toAddEquiv.toIntLinearEquiv
      (by
        -- Both `Submodule.map` applications agree definitionally (same underlying map, differing
        -- only in those `ℤ`-module instance wrappers).
        rw [← map_symbolGroupRelations_eq R]
        congr 1)).symm

/-- `degreeTwoEquiv` sends the product `ofUnit a * ofUnit b` to `SymbolGroup.symbol a b`. -/
@[simp]
theorem degreeTwoEquiv_ofUnit_mul (a b : Rˣ) :
    degreeTwoEquiv R
      ⟨ofUnit a * ofUnit b,
        SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ =
      SymbolGroup.symbol a b := by
  have hsym : (⟨ofUnit a * ofUnit b,
      SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ :
      degree R 2) =
      ⟨symbol (List.ofFn ![a, b]), by simpa using symbol_mem_degree (List.ofFn ![a, b])⟩ :=
    Subtype.ext (by simp [mul_one])
  rw [degreeTwoEquiv, LinearEquiv.trans_apply, hsym, degreeEquiv_symm_symbol, tprod_ofMul_fin_two]
  simp [AddEquiv.coe_symm_toIntLinearEquiv]

/-- The inverse of `degreeTwoEquiv` sends `SymbolGroup.symbol a b` to `ofUnit a * ofUnit b`. -/
@[simp]
theorem coe_degreeTwoEquiv_symm_symbol (a b : Rˣ) :
    ((degreeTwoEquiv R).symm (SymbolGroup.symbol a b) : MilnorK R) = ofUnit a * ofUnit b := by
  simpa only [degreeTwoEquiv_ofUnit_mul] using congrArg Subtype.val
    ((degreeTwoEquiv R).symm_apply_apply
      ⟨ofUnit a * ofUnit b,
        SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩)

/-- Naturality of `degreeTwoEquiv`: for any ring homomorphism `f : R →+* S`, `degreeMap f 2`
corresponds to `SymbolGroup.map f`. -/
theorem degreeTwoEquiv_map {S : Type w} [CommRing S] (f : R →+* S) (x : degree R 2) :
    degreeTwoEquiv S (degreeMap f 2 x) = SymbolGroup.map f (degreeTwoEquiv R x) := by
  have h :
      (degreeTwoEquiv S).toLinearMap ∘ₗ degreeMap f 2 ∘ₗ (degreeTwoEquiv R).symm.toLinearMap =
        SymbolGroup.map f := by
    refine SymbolGroup.linearMap_ext fun a b ↦ ?_
    have hval :
        degreeMap f 2 ((degreeTwoEquiv R).symm (SymbolGroup.symbol a b)) =
          ⟨ofUnit (Units.map f.toMonoidHom a) * ofUnit (Units.map f.toMonoidHom b),
            SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one _) (ofUnit_mem_degree_one _)⟩ :=
      Subtype.ext (by simp)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hval, degreeTwoEquiv_ofUnit_mul,
      SymbolGroup.map_symbol]
  simpa using LinearMap.congr_fun h (degreeTwoEquiv R x)

end Ring

/-! ### Arbitrary-degree naturality -/

/-- Applying a ring homomorphism entrywise on `⨂[ℤ]^n (Additive Rˣ)` preserves
`steinbergRelations`. -/
theorem map_steinbergRelations_le {R : Type u} [CommRing R] {S : Type w} [CommRing S]
    (f : R →+* S) (n : ℕ) :
    (steinbergRelations R n).map (PiTensorProduct.map fun _ : Fin n ↦
        (Units.map f.toMonoidHom).toAdditive.toIntLinearMap) ≤ steinbergRelations S n := by
  rw [Submodule.map_le_iff_le_comap, steinbergRelations_eq_span, Submodule.span_le]
  rintro _ ⟨g, k, hk, hab, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, PiTensorProduct.map_tprod]
  have hfun : (fun i : Fin n ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap
      (Additive.ofMul (g i))) = fun k ↦ Additive.ofMul ((Units.map f.toMonoidHom ∘ g) k) := by
    funext i
    simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive, toMul_ofMul,
      Function.comp_apply]
  rw [hfun]
  exact tprod_mem_steinbergRelations (Units.map f.toMonoidHom ∘ g) k hk (by simp [← map_add, hab])

/-- Functoriality on the degree-`n` tensor-power quotient: a ring homomorphism `f : R →+* S`
induces a `ℤ`-linear map
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ steinbergRelations R n →ₗ[ℤ]
  (⨂[ℤ]^n (Additive Sˣ)) ⧸ steinbergRelations S n`. -/
noncomputable def quotTensorPowerMap {R : Type u} [CommRing R] {S : Type w} [CommRing S]
    (f : R →+* S) (n : ℕ) :
    ((⨂[ℤ]^n (Additive Rˣ)) ⧸ steinbergRelations R n) →ₗ[ℤ]
      ((⨂[ℤ]^n (Additive Sˣ)) ⧸ steinbergRelations S n) :=
  Submodule.mapQ (steinbergRelations R n) (steinbergRelations S n)
    (PiTensorProduct.map fun _ : Fin n ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap)
    (Submodule.map_le_iff_le_comap.mp (map_steinbergRelations_le f n))

/-- Evaluating `quotTensorPowerMap f n` on `Submodule.Quotient.mk w` applies
`PiTensorProduct.map` entrywise. -/
theorem quotTensorPowerMap_mk {R : Type u} [CommRing R] {S : Type w} [CommRing S]
    (f : R →+* S) {n : ℕ} (w : ⨂[ℤ]^n (Additive Rˣ)) :
    quotTensorPowerMap f n (Submodule.Quotient.mk w) = Submodule.Quotient.mk
      (PiTensorProduct.map (fun _ : Fin n ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap)
        w) :=
  Submodule.mapQ_apply _ _ _ w

/-- `quotTensorPowerMap f n` sends the quotient class of a pure tensor of units to the pure
tensor of mapped units. -/
@[simp]
theorem quotTensorPowerMap_mk_tprod {R : Type u} [CommRing R] {S : Type w} [CommRing S]
    (f : R →+* S) {n : ℕ} (a : Fin n → Rˣ) :
    quotTensorPowerMap f n (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ a))) =
      Submodule.Quotient.mk
        (PiTensorProduct.tprod ℤ (Additive.ofMul ∘ (Units.map f.toMonoidHom ∘ a))) := by
  rw [quotTensorPowerMap_mk, PiTensorProduct.map_tprod]
  simp only [Function.comp_def, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
    toMul_ofMul]

/-- The identity ring homomorphism induces the identity on
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ steinbergRelations R n`. -/
@[simp]
theorem quotTensorPowerMap_id (R : Type u) [CommRing R] (n : ℕ) :
    quotTensorPowerMap (RingHom.id R) n = LinearMap.id := by
  unfold quotTensorPowerMap
  simp_rw [RingHom.toMonoidHom_eq_coe, RingHom.toMonoidHom_id, Units.map_id,
    MonoidHom.toAdditive_id, AddMonoidHom.toIntLinearMap_id, PiTensorProduct.map_id]
  apply Submodule.mapQ_id

/-- `quotTensorPowerMap` respects composition of ring homomorphisms. -/
theorem quotTensorPowerMap_comp {R : Type u} [CommRing R] {S : Type v} {T : Type w}
    [CommRing S] [CommRing T] (g : S →+* T) (f : R →+* S) (n : ℕ) :
    quotTensorPowerMap (g.comp f) n = (quotTensorPowerMap g n).comp (quotTensorPowerMap f n) := by
  unfold quotTensorPowerMap
  simp_rw [RingHom.toMonoidHom_comp, Units.map_comp, MonoidHom.toAdditive_comp,
    AddMonoidHom.toIntLinearMap_comp, PiTensorProduct.map_comp]
  apply Submodule.mapQ_comp

/-- Naturality of `degreeEquiv` in arbitrary degree `n`: for any ring homomorphism `f : R →+* S`,
`degreeMap f n` corresponds to `quotTensorPowerMap f n`. -/
theorem degreeEquiv_map {R : Type u} [CommRing R] {S : Type w} [CommRing S]
    (f : R →+* S) (n : ℕ) (x : (⨂[ℤ]^n (Additive Rˣ)) ⧸ steinbergRelations R n) :
    degreeMap f n (degreeEquiv R n x) = degreeEquiv S n (quotTensorPowerMap f n x) := by
  have h :
      degreeMap f n ∘ₗ (degreeEquiv R n).toLinearMap =
        (degreeEquiv S n).toLinearMap ∘ₗ quotTensorPowerMap f n := by
    apply Submodule.quot_hom_ext
    refine LinearMap.congr_fun (?_ :
      (degreeMap f n ∘ₗ (degreeEquiv R n).toLinearMap).comp (steinbergRelations R n).mkQ =
        ((degreeEquiv S n).toLinearMap ∘ₗ quotTensorPowerMap f n).comp
          (steinbergRelations R n).mkQ)
    refine PiTensorProduct.ext (MultilinearMap.ext fun a ↦ Subtype.ext ?_)
    have ha : a = Additive.ofMul ∘ fun k ↦ (a k).toMul :=
      funext fun k ↦ (ofMul_toMul (a k)).symm
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
      LinearMap.compMultilinearMap_apply, coe_degreeMap, coe_degreeEquiv_mk]
    conv_lhs => rw [ha, Function.comp_def, ofTensorPower_tprod, map_symbol, List.map_ofFn]
    conv_rhs =>
      rw [ha, quotTensorPowerMap_mk_tprod, coe_degreeEquiv_mk, Function.comp_def,
        ofTensorPower_tprod]
    simp only [Function.comp_def, RingHom.toMonoidHom_eq_coe]
  exact LinearMap.congr_fun h x

end TauCeti.MilnorK
