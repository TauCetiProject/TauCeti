/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.Average

/-!
# Maximal orders

Let `R` be a domain with fraction field `F` and `E` a finite-dimensional `F`-algebra. An `R`-order
`Λ` in `E` is *maximal* if it is not properly contained in another `R`-order in `E`. Maximal orders
play, for noncommutative algebras, the role that rings of integers play for number fields.

In a commutative algebra every order consists of integral elements, so it lies in the integral
closure of `R`. Whenever that integral closure is itself an order, it is therefore the unique
maximal order. This applies to the integral closure of an integrally closed noetherian `R` in a
finite separable field extension of `F`, and in particular to `R` itself inside `F`.

In general an algebra has many maximal orders, and an order need not be maximal even when the
algebra is commutative. For a finite group `G` whose order is invertible in `F` but not in `R`,
the averaging idempotent `e = #G⁻¹ ∑ g` of `F[G]` is integral over `R` and absorbed by every group
element, so `R[G] + R e` is an order strictly containing `R[G]`; thus `R[G]` is not maximal. The
hypothesis on `#G` cannot be dropped: over `R = F = 𝔽_p` and `G = C_p` the group ring `R[G]` is the
only order in `F[G]`.

## Main definitions

* `TauCeti.IntegralOrder.IsMaximalOrder F Λ`: the `R`-order `Λ` in `E` is maximal among `R`-orders.

## Main results

* `TauCeti.IntegralOrder.isMaximalOrder_iff_eq_integralClosure`: in a commutative algebra in which
  the integral closure of `R` is an order, the integral closure is the unique maximal order.
* `TauCeti.IntegralOrder.integralClosure_isMaximalOrder`: the integral closure of an integrally
  closed noetherian domain in a finite separable extension of its fraction field is a maximal
  order.
* `TauCeti.IntegralOrder.isMaximalOrder_bot`: an integrally closed domain is a maximal order in its
  fraction field.
* `TauCeti.IntegralOrder.groupRing_not_isMaximalOrder`: if `#G` is invertible in `F` but not a unit
  of `R`, the group ring `R[G]` is not a maximal order in `F[G]`.

## References

* H. Johnston, *Notes on Galois modules*, Definition 13.6 and Examples 13.7.
* J. Voight, *Quaternion algebras*, Definition 10.4.1.
-/

public section

open Module Submodule MonoidAlgebra

namespace TauCeti.IntegralOrder

section Basic

variable {R : Type*} (F : Type*) {E : Type*} [CommRing R] [CommRing F] [Ring E]
  [Algebra R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]

/-- An `R`-subalgebra `Λ` of an `F`-algebra `E` is a maximal `R`-order in `E` if it is an `R`-order
in `E` and is not properly contained in another `R`-order in `E`. The definition is exposed, so the
API of `Maximal` applies to it directly, e.g. `h.eq_of_le` and `h.not_gt` for `Maximal.eq_of_le` and
`Maximal.not_gt`. -/
@[expose] def IsMaximalOrder (Λ : Subalgebra R E) : Prop :=
  Maximal (IsOrder F) Λ

variable {F} {Λ : Subalgebra R E}

/-- A maximal order is a maximal element among the orders (this is the definition of
`IsMaximalOrder`). -/
theorem isMaximalOrder_iff_maximal : IsMaximalOrder F Λ ↔ Maximal (IsOrder F) Λ :=
  Iff.rfl

namespace IsMaximalOrder

/-- A maximal order is an order. -/
theorem isOrder (h : IsMaximalOrder F Λ) : IsOrder F Λ :=
  h.prop

end IsMaximalOrder

end Basic

section Commutative

variable {R F E : Type*} [CommRing R] [CommRing F] [CommRing E]
  [Algebra R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]

/-- **Uniqueness of the maximal order of a commutative algebra.** If the integral closure of `R` in
a commutative `F`-algebra `E` is an `R`-order, then it is the unique maximal `R`-order in `E`. -/
theorem isMaximalOrder_iff_eq_integralClosure (h : IsOrder F (integralClosure R E))
    {Λ : Subalgebra R E} : IsMaximalOrder F Λ ↔ Λ = integralClosure R E :=
  maximal_iff_eq h fun _ hΓ => hΓ.le_integralClosure

/-- If the integral closure of `R` in a commutative `F`-algebra `E` is an `R`-order, then it is a
maximal `R`-order. -/
theorem isMaximalOrder_integralClosure_of_isOrder (h : IsOrder F (integralClosure R E)) :
    IsMaximalOrder F (integralClosure R E) :=
  (isMaximalOrder_iff_eq_integralClosure h).2 rfl

end Commutative

section Field

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]

/-- **Integral closures are maximal orders.** The integral closure of an integrally closed
noetherian domain `R` in a finite separable extension `L` of its fraction field `F` is a maximal
`R`-order in `L`, and by `isMaximalOrder_iff_eq_integralClosure` it is the only one. -/
theorem integralClosure_isMaximalOrder [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (L : Type*) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] : IsMaximalOrder F (integralClosure R L) :=
  isMaximalOrder_integralClosure_of_isOrder (integralClosure_isOrder L)

/-- An integrally closed domain `R` is a maximal `R`-order in its fraction field. -/
theorem isMaximalOrder_bot [IsIntegrallyClosed R] : IsMaximalOrder F (⊥ : Subalgebra R F) := by
  rw [← IsIntegrallyClosed.integralClosure_eq_bot R F]
  refine isMaximalOrder_integralClosure_of_isOrder ?_
  rw [IsIntegrallyClosed.integralClosure_eq_bot]
  exact isOrder_bot

end Field

section GroupRing

variable {R F G : Type*} [CommRing R] [CommRing F] [Algebra R F] [Group G]

/-- **Group rings are not maximal orders.** Let `G` be a finite group whose order is invertible in
`F` but is not a unit of `R`, where `R → F` is injective. Then the group ring `R[G]` is not a
maximal `R`-order in `F[G]`: adjoining the averaging idempotent `#G⁻¹ ∑ g` gives a strictly
larger order. -/
theorem groupRing_not_isMaximalOrder [Fintype G] [FaithfulSMul R F]
    [Invertible (Fintype.card G : F)] (hG : ¬IsUnit (Fintype.card G : R)) :
    ¬IsMaximalOrder F (groupRingSubalgebra R F G) := by
  classical
  set e := GroupAlgebra.average F G
  -- the group elements together with `e` form a finite multiplicatively closed set
  set S : Set (MonoidAlgebra F G) := insert e (Set.range fun g : G => single g (1 : F))
  have hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro x (rfl | ⟨g, rfl⟩) y (rfl | ⟨h, rfl⟩)
    · exact .inl (GroupAlgebra.isIdempotentElem_average F G).eq
    · exact .inl (GroupAlgebra.mul_average_right F G h)
    · exact .inl (GroupAlgebra.mul_average_left F G g)
    · exact .inr ⟨g * h, by simp [single_mul_single]⟩
  -- so the `R`-subalgebra it generates is its `R`-span `R[G] + R e`
  let Γ := Algebra.adjoin R S
  have hΓ : Subalgebra.toSubmodule Γ = span R S :=
    Algebra.adjoin_eq_span_of_subset R fun _ hx => subset_span <|
      Submonoid.closure_induction (fun _ h => h) (.inr ⟨1, one_def.symm⟩)
        (fun _ _ _ _ ha hb => hS _ ha _ hb) hx
  have : Module.Finite R Γ :=
    Module.Finite.iff_fg.2 <| hΓ ▸ fg_span ((Set.finite_range _).insert e)
  have hle : groupRingSubalgebra R F G ≤ Γ := fun x hx => by
    rw [← Subalgebra.mem_toSubmodule, toSubmodule_groupRingSubalgebra] at hx
    rw [← Subalgebra.mem_toSubmodule, hΓ]
    exact span_mono (Set.subset_insert _ _) hx
  -- `e ∉ R[G]`: its coefficients are `#G⁻¹`, which would otherwise make `#G` a unit of `R`
  have he : e ∉ groupRingSubalgebra R F G := fun he => by
    obtain ⟨r, hr⟩ := mem_groupRingSubalgebra.1 he 1
    refine hG (IsUnit.of_mul_eq_one r (FaithfulSMul.algebraMap_injective R F ?_))
    rw [GroupAlgebra.coeff_average] at hr
    simp [hr]
  exact fun h => Maximal.not_gt h ((groupRing_isOrder R F G).of_le hle)
    (lt_of_le_of_ne hle fun h => he (h ▸ Algebra.subset_adjoin (Set.mem_insert e _)))

/-- `ℤ[G]` is not a maximal order in `ℚ[G]` for a nontrivial finite group `G`. -/
theorem groupRing_int_not_isMaximalOrder [Finite G] [Nontrivial G] :
    ¬IsMaximalOrder ℚ (groupRingSubalgebra ℤ ℚ G) := by
  have := Fintype.ofFinite G
  have : Invertible (Fintype.card G : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  refine groupRing_not_isMaximalOrder fun h => ?_
  have := Fintype.one_lt_card (α := G)
  rcases Int.isUnit_iff.1 h with h | h <;> omega

end GroupRing

end TauCeti.IntegralOrder
