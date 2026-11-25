/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Order.Group.Cone
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import TauCeti.Order.WellFounded.Set

/-!
# Hahn series supported below finitely many translated cones

Let `M` be an abelian group and `C` a pointed submonoid of `M`, a cone with `C ∩ -C = 0`. When `C`
is finitely generated, series `∑ c_μ e^μ` over `M` whose support lies in a finite union of
translated negative cones `λ - C` form a ring under convolution: for two such series and a target
`ξ`, only finitely many pairs of exponents in the supports add up to `ξ`. This is the ring in which
the characters of representations with weights bounded above, such as highest-weight modules, are
multiplied.

This file realizes that ring as Mathlib's Hahn series, rather than building the convolution
again. The exponent type `TauCeti.ConeExponent hC` is a copy of `M` ordered by `μ ≤ ν ↔ μ - ν ∈ C`,
so that the lower cone `λ - C` is the interval `Ici λ`; the order is the reverse of the usual
order with positive cone `C`, because Hahn series have supports bounded below. A partially
well-ordered set is covered by finitely many sets `Ici λ`, so the support of every Hahn series
over `TauCeti.ConeExponent hC` lies in finitely many translated negative cones. When `C` is
finitely generated each `Ici λ` is partially well-ordered by Dickson's lemma, so conversely every
function supported in finitely many translated negative cones is a Hahn series
(`HahnSeries.ofConeBounded`). The ring `HahnSeries (TauCeti.ConeExponent hC) R` is therefore the
ring of cone-supported series, with Mathlib's convolution product.

An injective additive map `f : M → M'` that pulls `C'` back to `C` is an order embedding of the
exponent types (`TauCeti.ConeExponent.map_le_map_iff`), so extension by zero along it is an
injective ring homomorphism of cone-supported series (`HahnSeries.embDomainRingHom`).

## Main definitions

* `TauCeti.ConeExponent hC`: `M` ordered by `μ ≤ ν ↔ μ - ν ∈ C`.
* `TauCeti.ConeExponent.map`: the additive map of exponent types induced by `f : M →+ M'`.
* `HahnSeries.ofConeBounded`: the Hahn series attached to a function supported in finitely many
  translated negative cones of a finitely generated cone.

## Main results

* `TauCeti.ConeExponent.toConeExponent_le_toConeExponent_iff`: `μ ≤ ν ↔ μ - ν ∈ C`.
* `TauCeti.ConeExponent.isPWO_Ici`: for a finitely generated cone, `λ - C` is partially
  well-ordered.
* `TauCeti.ConeExponent.isPWO_iff_exists_finset`: for a finitely generated cone, a set of
  exponents is partially well-ordered exactly when it lies in finitely many translated negative
  cones.
* `HahnSeries.exists_finset_sub_mem_of_coeff_ne_zero`: the support of a Hahn series over
  `TauCeti.ConeExponent hC` lies in finitely many translated negative cones.
* `TauCeti.ConeExponent.map_le_map_iff`: an additive map pulling `C'` back to `C` reflects and
  preserves the order.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §9.7 (the algebra `ℰ` of formal
  characters supported in finitely many cones `λ - Q₊`).
-/

public section

namespace TauCeti

variable {M : Type*} [AddCommGroup M] {C : AddSubmonoid M}

/-- The exponents of series supported in finitely many translated negative cones `λ - C`: a copy
of `M`, ordered by `μ ≤ ν ↔ μ - ν ∈ C`. With this order `λ - C` is the interval `Ici λ`. Every
Hahn series over `TauCeti.ConeExponent hC` is cone-supported, and when `C` is finitely generated,
Hahn series over `TauCeti.ConeExponent hC` are exactly the cone-supported series. -/
structure ConeExponent (hC : C.IsPointed) where
  /-- The exponent attached to an element of `M`. -/
  toConeExponent ::
  /-- The element of `M` underlying an exponent. -/
  ofConeExponent : M

namespace ConeExponent

variable {hC : C.IsPointed}

@[simp]
theorem ofConeExponent_toConeExponent (a : M) :
    (toConeExponent a : ConeExponent hC).ofConeExponent = a := (rfl)

@[simp]
theorem toConeExponent_ofConeExponent (x : ConeExponent hC) :
    toConeExponent x.ofConeExponent = x := (rfl)

theorem ofConeExponent_injective :
    Function.Injective (ofConeExponent : ConeExponent hC → M) :=
  fun _ _ h ↦ congrArg toConeExponent h

@[ext]
theorem ext {x y : ConeExponent hC} (h : x.ofConeExponent = y.ofConeExponent) : x = y :=
  ofConeExponent_injective h

/-! ### The group structure -/

instance : Zero (ConeExponent hC) := ⟨toConeExponent 0⟩
instance : Add (ConeExponent hC) := ⟨fun x y ↦ toConeExponent (x.ofConeExponent + y.ofConeExponent)⟩
instance : Neg (ConeExponent hC) := ⟨fun x ↦ toConeExponent (-x.ofConeExponent)⟩
instance : Sub (ConeExponent hC) := ⟨fun x y ↦ toConeExponent (x.ofConeExponent - y.ofConeExponent)⟩
instance : SMul ℕ (ConeExponent hC) := ⟨fun n x ↦ toConeExponent (n • x.ofConeExponent)⟩
instance : SMul ℤ (ConeExponent hC) := ⟨fun n x ↦ toConeExponent (n • x.ofConeExponent)⟩

instance : AddCommGroup (ConeExponent hC) :=
  ofConeExponent_injective.addCommGroup _ (rfl) (fun _ _ ↦ (rfl)) (fun _ ↦ (rfl))
    (fun _ _ ↦ (rfl)) (fun _ _ ↦ (rfl)) (fun _ _ ↦ (rfl))

variable (hC) in
/-- The additive equivalence between `M` and its exponent type. -/
def addEquiv : M ≃+ ConeExponent hC where
  toFun := toConeExponent
  invFun := ofConeExponent
  map_add' _ _ := (rfl)

@[simp]
theorem addEquiv_apply (a : M) : addEquiv hC a = toConeExponent a := (rfl)

@[simp]
theorem addEquiv_symm_apply (x : ConeExponent hC) : (addEquiv hC).symm x = x.ofConeExponent :=
  (rfl)

@[simp]
theorem ofConeExponent_zero : (0 : ConeExponent hC).ofConeExponent = 0 := (rfl)

@[simp]
theorem ofConeExponent_add (x y : ConeExponent hC) :
    (x + y).ofConeExponent = x.ofConeExponent + y.ofConeExponent := (rfl)

@[simp]
theorem ofConeExponent_neg (x : ConeExponent hC) : (-x).ofConeExponent = -x.ofConeExponent :=
  (rfl)

@[simp]
theorem ofConeExponent_sub (x y : ConeExponent hC) :
    (x - y).ofConeExponent = x.ofConeExponent - y.ofConeExponent := (rfl)

@[simp]
theorem toConeExponent_zero : (toConeExponent 0 : ConeExponent hC) = 0 := (rfl)

@[simp]
theorem toConeExponent_add (a b : M) :
    (toConeExponent (a + b) : ConeExponent hC) = toConeExponent a + toConeExponent b := (rfl)

@[simp]
theorem toConeExponent_neg (a : M) :
    (toConeExponent (-a) : ConeExponent hC) = -toConeExponent a := (rfl)

@[simp]
theorem toConeExponent_sub (a b : M) :
    (toConeExponent (a - b) : ConeExponent hC) = toConeExponent a - toConeExponent b := (rfl)

@[simp]
theorem ofConeExponent_nsmul (n : ℕ) (x : ConeExponent hC) :
    (n • x).ofConeExponent = n • x.ofConeExponent := (rfl)

@[simp]
theorem ofConeExponent_zsmul (n : ℤ) (x : ConeExponent hC) :
    (n • x).ofConeExponent = n • x.ofConeExponent := (rfl)

@[simp]
theorem toConeExponent_nsmul (n : ℕ) (a : M) :
    (toConeExponent (n • a) : ConeExponent hC) = n • toConeExponent a := (rfl)

@[simp]
theorem toConeExponent_zsmul (n : ℤ) (a : M) :
    (toConeExponent (n • a) : ConeExponent hC) = n • toConeExponent a := (rfl)

/-! ### The order -/

/-- The order of `TauCeti.ConeExponent hC` is the dual of Mathlib's order on `M` with positive
cone `C` (`PartialOrder.ofAddSubmonoid`), transported along `ofConeExponent`. -/
instance : PartialOrder (ConeExponent hC) :=
  letI := PartialOrder.ofAddSubmonoid hC
  PartialOrder.lift (fun x ↦ OrderDual.toDual x.ofConeExponent)
    (OrderDual.toDual.injective.comp ofConeExponent_injective)

theorem le_def {x y : ConeExponent hC} : x ≤ y ↔ x.ofConeExponent - y.ofConeExponent ∈ C :=
  Iff.rfl

/-- The order on exponents: `μ ≤ ν` when `μ - ν` lies in the cone, that is, when `ν` lies in
the translated negative cone `μ - C`. -/
@[simp]
theorem toConeExponent_le_toConeExponent_iff {a b : M} :
    (toConeExponent a : ConeExponent hC) ≤ toConeExponent b ↔ a - b ∈ C :=
  Iff.rfl

instance : IsOrderedAddMonoid (ConeExponent hC) :=
  letI := PartialOrder.ofAddSubmonoid hC
  haveI := IsOrderedAddMonoid.ofAddSubmonoid hC
  Function.Injective.isOrderedAddMonoid (fun x ↦ OrderDual.toDual x.ofConeExponent)
    (fun _ _ ↦ (rfl)) Iff.rfl

/-- `Ici λ` is the translated negative cone `λ - C`. -/
theorem mem_Ici_iff {x y : ConeExponent hC} :
    y ∈ Set.Ici x ↔ x.ofConeExponent - y.ofConeExponent ∈ C :=
  Iff.rfl

/-- **Dickson's lemma for a cone**: if `C` is finitely generated, each translated negative cone
`λ - C`, the interval `Ici λ`, is partially well-ordered. -/
theorem isPWO_Ici [IsAddFG C] (x : ConeExponent hC) : (Set.Ici x).IsPWO := by
  classical
  obtain ⟨S, rfl⟩ := AddSubmonoid.exists_of_isAddFG C
  -- The elements of `λ - C` are `λ - ∑ₛ aₛ • s`, monotonically in the coefficients `a : S → ℕ`.
  let f : (S → ℕ) → ConeExponent hC := fun a ↦ x - toConeExponent (∑ s : S, a s • (s : M))
  have hf : Monotone f := by
    intro a b hab
    rw [le_def]
    simp only [f, ofConeExponent_sub, sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
    refine AddSubmonoid.sum_mem _ fun s _ ↦ ?_
    rw [← Nat.sub_add_cancel (hab s), add_nsmul, add_sub_cancel_right]
    exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure s.prop) _
  refine ((Set.isPWO_univ_iff.mpr inferInstance).image_of_monotone hf).mono fun y hy ↦ ?_
  rw [mem_Ici_iff, AddSubmonoid.mem_closure_finset'] at hy
  obtain ⟨a, ha⟩ := hy
  refine ⟨a, Set.mem_univ _, ext ?_⟩
  simp only [f, ofConeExponent_sub, ← ha, sub_sub_cancel]

/-- For a finitely generated cone, a set of exponents is partially well-ordered exactly when it
lies in finitely many translated negative cones `λ - C`. -/
theorem isPWO_iff_exists_finset [IsAddFG C] {s : Set (ConeExponent hC)} :
    s.IsPWO ↔ ∃ t : Finset M, ∀ x ∈ s, ∃ a ∈ t, a - x.ofConeExponent ∈ C := by
  classical
  rw [Set.isPWO_iff_exists_finset_subset_biUnion_Ici isPWO_Ici]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t.image ofConeExponent, fun x hx ↦ ?_⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact ⟨a.ofConeExponent, Finset.mem_image_of_mem _ ha, hxa⟩
  · rintro ⟨t, ht⟩
    refine ⟨t.image toConeExponent, fun x hx ↦ ?_⟩
    obtain ⟨a, ha, hxa⟩ := ht x hx
    exact Set.mem_iUnion₂.mpr ⟨toConeExponent a, Finset.mem_image_of_mem _ ha, hxa⟩

/-! ### Changing the group -/

variable {M' : Type*} [AddCommGroup M'] {C' : AddSubmonoid M'} {hC' : C'.IsPointed}

/-- The additive map of exponent types induced by an additive map `f : M →+ M'`. It is an order
embedding when `f` is injective and pulls `C'` back to `C`. -/
def map (f : M →+ M') : ConeExponent hC →+ ConeExponent hC' :=
  ((addEquiv hC').toAddMonoidHom.comp f).comp (addEquiv hC).symm.toAddMonoidHom

@[simp]
theorem map_toConeExponent (f : M →+ M') (a : M) :
    map (hC := hC) (hC' := hC') f (toConeExponent a) = toConeExponent (f a) := (rfl)

@[simp]
theorem ofConeExponent_map (f : M →+ M') (x : ConeExponent hC) :
    (map (hC' := hC') f x).ofConeExponent = f x.ofConeExponent := (rfl)

theorem map_injective {f : M →+ M'} (hf : Function.Injective f) :
    Function.Injective (map (hC := hC) (hC' := hC') f) :=
  fun _ _ h ↦ ext (hf (congrArg ofConeExponent h))

/-- An additive map pulling the cone `C'` back to `C` preserves and reflects the order on
exponents. -/
theorem map_le_map_iff {f : M →+ M'} (hf : ∀ a, f a ∈ C' ↔ a ∈ C) {x y : ConeExponent hC} :
    map (hC' := hC') f x ≤ map f y ↔ x ≤ y := by
  rw [le_def, le_def, ofConeExponent_map, ofConeExponent_map, ← map_sub]
  exact hf _

end ConeExponent

end TauCeti

namespace HahnSeries

open TauCeti TauCeti.ConeExponent

variable {M R : Type*} [AddCommGroup M] {C : AddSubmonoid M} {hC : C.IsPointed} [Zero R]

/-- **The support of a cone-supported series is bounded**: the exponents of a Hahn series over
`TauCeti.ConeExponent hC` with nonzero coefficient lie in finitely many translated negative cones
`λ - C`. -/
theorem exists_finset_sub_mem_of_coeff_ne_zero (x : HahnSeries (ConeExponent hC) R) :
    ∃ t : Finset M, ∀ a : M, x.coeff (toConeExponent a) ≠ 0 → ∃ b ∈ t, b - a ∈ C := by
  classical
  obtain ⟨t, -, ht⟩ := x.isPWO_support.exists_finset_subset_biUnion_Ici
  refine ⟨t.image ofConeExponent, fun a ha ↦ ?_⟩
  obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.mp (ht ha)
  exact ⟨b.ofConeExponent, Finset.mem_image_of_mem _ hb, hab⟩

variable [IsAddFG C]

/-- The Hahn series `∑ f(μ) e^μ` attached to a function `f : M → R` supported in finitely many
translated negative cones `λ - C`, `λ ∈ t`, of a finitely generated cone `C`. -/
def ofConeBounded (f : M → R) (t : Finset M) (hf : ∀ a, f a ≠ 0 → ∃ b ∈ t, b - a ∈ C) :
    HahnSeries (ConeExponent hC) R where
  coeff x := f x.ofConeExponent
  isPWO_support' := isPWO_iff_exists_finset.mpr ⟨t, fun _ hx ↦ hf _ hx⟩

@[simp]
theorem coeff_ofConeBounded (f : M → R) (t : Finset M)
    (hf : ∀ a, f a ≠ 0 → ∃ b ∈ t, b - a ∈ C) (a : M) :
    (ofConeBounded (hC := hC) f t hf).coeff (toConeExponent a) = f a := (rfl)

/-- Every Hahn series over `TauCeti.ConeExponent hC` arises from its coefficient function. -/
@[simp]
theorem ofConeBounded_coeff (x : HahnSeries (ConeExponent hC) R) (t : Finset M)
    (hf : ∀ a, x.coeff (toConeExponent a) ≠ 0 → ∃ b ∈ t, b - a ∈ C) :
    ofConeBounded (fun a ↦ x.coeff (toConeExponent a)) t hf = x :=
  HahnSeries.ext (rfl)

end HahnSeries
