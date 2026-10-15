/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import TauCeti.Algebra.TensorProduct.Ideal

/-!
# Hopf ideals

This file defines Hopf ideals in a Hopf algebra over a commutative semiring. A Hopf ideal is
an ideal `I` whose comultiplication lands in `I ⊗ H + H ⊗ I`, whose counit vanishes on `I`,
and which is stable under the antipode.

Closed subgroup schemes of an affine group scheme are represented on coordinate rings by
quotient Hopf algebras, and the ideal being quotiented must satisfy exactly these Hopf-ideal
closure conditions.

## Main definitions

* `TauCeti.HopfIdeal`: a Hopf ideal in a Hopf algebra over a commutative semiring.
* `⊥ : HopfIdeal R H`: the zero Hopf ideal.
* `I ⊔ J : HopfIdeal R H`: the sum of two Hopf ideals.
* `sSup S : HopfIdeal R H` and `⨆ i, I i : HopfIdeal R H`: arbitrary suprema of Hopf ideals,
  with underlying ideal the supremum of the underlying ideals.
* `TauCeti.HopfIdeal.instIsCoideal`, `TauCeti.HopfIdeal.instIsHopfIdeal`: over a commutative
  ring, the bridge instances exhibiting `I.toIdeal` as a coideal and a Hopf ideal in Mathlib's
  sense, so that Mathlib's quotient coalgebra/bialgebra/Hopf instances fire on `H ⧸ I.toIdeal`.

## References

This follows the standard Hopf-algebra definition of a Hopf ideal; see Sweedler,
*Hopf Algebras*, Chapter 1. The formalization uses Mathlib's Hopf-algebra and tensor-product
ideal API. The arbitrary-supremum lattice construction follows the local pattern from
`TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice` and
`TauCeti.Algebra.Coalgebra.Subcomodule.Lattice`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable (R : Type u) (H : Type v)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- A Hopf ideal in a Hopf algebra over a commutative semiring.

The comultiplication condition is stated in the ambient tensor product algebra as
`Δ(I) ⊆ I ⊗ H + H ⊗ I`. Over a commutative ring, the bridge instances
`HopfIdeal.instIsCoideal` and `HopfIdeal.instIsHopfIdeal` below let Mathlib endow the
quotient `H ⧸ I.toIdeal` with its Hopf-algebra structure. -/
structure HopfIdeal where
  /-- The underlying ideal. -/
  carrier : Ideal H
  /-- The underlying ideal is two-sided. -/
  isTwoSided' : carrier.IsTwoSided
  /-- The comultiplication of an element of the ideal lies in `I ⊗ H + H ⊗ I`. -/
  comul_mem' :
    ∀ ⦃x : H⦄, x ∈ carrier →
      Coalgebra.comul (R := R) x ∈
        Ideal.leftTensorIdeal (R := R) (H := H) carrier ⊔
          Ideal.rightTensorIdeal (R := R) (H := H) carrier
  /-- The counit vanishes on the ideal. -/
  counit_eq_zero' : ∀ ⦃x : H⦄, x ∈ carrier → Coalgebra.counit (R := R) x = 0
  /-- The antipode preserves the ideal. -/
  antipode_mem' :
    ∀ ⦃x : H⦄, x ∈ carrier → HopfAlgebra.antipode R x ∈ carrier

namespace HopfIdeal

variable {R H}

instance : SetLike (HopfIdeal R H) H where
  coe I := I.carrier
  coe_injective I J h := by
    cases I with
    | mk carrier htwo hcomul hcounit hantipode =>
    cases J with
    | mk carrier' htwo' hcomul' hcounit' hantipode' =>
    congr
    exact SetLike.ext' h

instance : AddSubmonoidClass (HopfIdeal R H) H where
  add_mem {I} := I.carrier.add_mem
  zero_mem I := I.carrier.zero_mem

instance : SMulMemClass (HopfIdeal R H) H H where
  smul_mem {I} h {_} hx := I.carrier.mul_mem_left h hx

instance : PartialOrder (HopfIdeal R H) :=
  .ofSetLike (HopfIdeal R H)

/-- The underlying ideal of a Hopf ideal. -/
@[expose] def toIdeal (I : HopfIdeal R H) : Ideal H :=
  I.carrier

instance (I : HopfIdeal R H) : I.toIdeal.IsTwoSided :=
  I.isTwoSided'

@[simp]
theorem mem_carrier {I : HopfIdeal R H} {x : H} : x ∈ I.carrier ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem mem_toIdeal {I : HopfIdeal R H} {x : H} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

theorem toIdeal_carrier (I : HopfIdeal R H) : I.toIdeal = I.carrier :=
  rfl

theorem le_def {I J : HopfIdeal R H} : I ≤ J ↔ ∀ ⦃x : H⦄, x ∈ I → x ∈ J :=
  Iff.rfl

theorem toIdeal_le_toIdeal {I J : HopfIdeal R H} :
    I.toIdeal ≤ J.toIdeal ↔ I ≤ J :=
  Iff.rfl

/-- Two Hopf ideals are equal when they contain the same elements. -/
@[ext]
theorem ext {I J : HopfIdeal R H} (h : ∀ x : H, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

/-- Constructor from an ideal and the three Hopf-ideal closure conditions. -/
@[expose] def ofIdeal (I : Ideal H) [I.IsTwoSided]
    (hcomul :
      ∀ ⦃x : H⦄, x ∈ I →
        Coalgebra.comul (R := R) x ∈
          Ideal.leftTensorIdeal (R := R) (H := H) I ⊔ Ideal.rightTensorIdeal (R := R) (H := H) I)
    (hcounit : ∀ ⦃x : H⦄, x ∈ I → Coalgebra.counit (R := R) x = 0)
    (hantipode : ∀ ⦃x : H⦄, x ∈ I → HopfAlgebra.antipode R x ∈ I) :
    HopfIdeal R H where
  carrier := I
  isTwoSided' := inferInstance
  comul_mem' := hcomul
  counit_eq_zero' := hcounit
  antipode_mem' := hantipode

@[simp]
theorem ofIdeal_carrier (I : Ideal H) [I.IsTwoSided] (hcomul hcounit hantipode) :
    (ofIdeal (R := R) (H := H) I hcomul hcounit hantipode).carrier = I :=
  rfl

@[simp]
theorem mem_ofIdeal {I : Ideal H} [I.IsTwoSided] {hcomul hcounit hantipode} {x : H} :
    x ∈ ofIdeal (R := R) (H := H) I hcomul hcounit hantipode ↔ x ∈ I :=
  Iff.rfl

/-- Construct the Hopf ideal spanned by a set of generators by checking the three Hopf-ideal
closure conditions only on those generators. -/
def ofSpan (S : Set H) [hS : (Ideal.span S).IsTwoSided]
    (hcomul : ∀ x ∈ S,
      Coalgebra.comul (R := R) x ∈
        Ideal.leftTensorIdeal (R := R) (H := H) (Ideal.span S) ⊔
          Ideal.rightTensorIdeal (R := R) (H := H) (Ideal.span S))
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := R) x = 0)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode R x ∈ Ideal.span S) :
    HopfIdeal R H :=
  ofIdeal (Ideal.span S)
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem x hx => exact hcomul x hx
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
          rw [smul_eq_mul, Bialgebra.comul_mul]
          exact Ideal.mul_mem_left _ _ hx)
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem x hx => exact hcounit x hx
      | zero => rw [map_zero]
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_eq_mul, Bialgebra.counit_mul, hx, mul_zero])
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem x hx => exact hantipode x hx
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
          rw [smul_eq_mul, HopfAlgebra.antipode_mul_antidistrib]
          exact Ideal.mul_mem_right _ _ hx)

/-- The ideal underlying `ofSpan S` is the ideal span of `S`. -/
@[simp]
theorem ofSpan_toIdeal (S : Set H) [hS : (Ideal.span S).IsTwoSided]
    (hcomul hcounit hantipode) :
    (ofSpan (R := R) (H := H) S hcomul hcounit hantipode).toIdeal = Ideal.span S :=
  by rw [toIdeal_carrier, ofSpan, ofIdeal_carrier]

/-- The comultiplication of an element of a Hopf ideal lies in `I ⊗ H + H ⊗ I`. -/
theorem comul_mem (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    Coalgebra.comul (R := R) x ∈
      Ideal.leftTensorIdeal (R := R) (H := H) I.toIdeal ⊔
        Ideal.rightTensorIdeal (R := R) (H := H) I.toIdeal :=
  I.comul_mem' hx

/-- The counit vanishes on a Hopf ideal. -/
theorem counit_eq_zero (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    Coalgebra.counit (R := R) x = 0 :=
  I.counit_eq_zero' hx

/-- The antipode preserves a Hopf ideal. -/
theorem antipode_mem (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    HopfAlgebra.antipode R x ∈ I :=
  I.antipode_mem' hx

/-- A Hopf ideal absorbs multiplication on the right as well as on the left. -/
theorem mul_mem_right (I : HopfIdeal R H) {x : H} (hx : x ∈ I) (y : H) :
    x * y ∈ I :=
  I.toIdeal.mul_mem_right y hx

/-- The zero ideal as a Hopf ideal. -/
instance instBot : Bot (HopfIdeal R H) where
  bot :=
    { carrier := ⊥
      isTwoSided' := inferInstance
      comul_mem' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp
      counit_eq_zero' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp
      antipode_mem' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp }

@[simp]
theorem bot_toIdeal : (⊥ : HopfIdeal R H).toIdeal = (⊥ : Ideal H) :=
  rfl

@[simp]
theorem mem_bot {x : H} : x ∈ (⊥ : HopfIdeal R H) ↔ x = 0 :=
  Ideal.mem_bot

/-- The zero Hopf ideal is contained in every Hopf ideal. -/
instance : OrderBot (HopfIdeal R H) where
  bot := ⊥
  bot_le I x hx := by
    rw [mem_bot] at hx
    rw [hx]
    exact zero_mem I

/-- The sum of two Hopf ideals is a Hopf ideal. -/
instance instMax : Max (HopfIdeal R H) where
  max I J :=
    { carrier := I.toIdeal ⊔ J.toIdeal
      isTwoSided' := by
        refine ⟨fun {x} b hx => ?_⟩
        rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
        rw [add_mul]
        exact Submodule.add_mem_sup (I.mul_mem_right hy b) (J.mul_mem_right hz b)
      comul_mem' := by
        intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
        rw [map_add]
        refine add_mem ?_ ?_
        · exact
            (sup_le_sup
                (Ideal.leftTensorIdeal_mono (R := R) (H := H) (I := I.toIdeal)
                  (J := I.toIdeal ⊔ J.toIdeal) le_sup_left)
                (Ideal.rightTensorIdeal_mono (R := R) (H := H) (I := I.toIdeal)
                  (J := I.toIdeal ⊔ J.toIdeal) le_sup_left))
              (I.comul_mem hy)
        · exact
            (sup_le_sup
                (Ideal.leftTensorIdeal_mono (R := R) (H := H) (I := J.toIdeal)
                  (J := I.toIdeal ⊔ J.toIdeal) le_sup_right)
                (Ideal.rightTensorIdeal_mono (R := R) (H := H) (I := J.toIdeal)
                  (J := I.toIdeal ⊔ J.toIdeal) le_sup_right))
              (J.comul_mem hz)
      counit_eq_zero' := by
        intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
        simp [I.counit_eq_zero hy, J.counit_eq_zero hz]
      antipode_mem' := by
        intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
        rw [map_add]
        exact Submodule.add_mem_sup (I.antipode_mem hy) (J.antipode_mem hz) }

/-- The underlying ideal of the join of two Hopf ideals is the join of their underlying
ideals. -/
@[simp]
theorem sup_toIdeal (I J : HopfIdeal R H) : (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal :=
  rfl

/-- Membership in the join of two Hopf ideals. -/
theorem mem_sup {I J : HopfIdeal R H} {x : H} :
    x ∈ I ⊔ J ↔ ∃ y ∈ I, ∃ z ∈ J, y + z = x := by
  rw [← mem_toIdeal, sup_toIdeal, Submodule.mem_sup]
  rfl

/-- Hopf ideals form a semilattice under ideal sum, with `⊔` given by the sum
construction. -/
instance instSemilatticeSup : SemilatticeSup (HopfIdeal R H) where
  sup := (· ⊔ ·)
  le_sup_left I J := by
    intro x hx
    exact Ideal.mem_sup_left hx
  le_sup_right I J := by
    intro x hx
    exact Ideal.mem_sup_right hx
  sup_le I J K hIK hJK := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    exact add_mem (hIK hy) (hJK hz)

/-- The supremum of a set of Hopf ideals has underlying ideal the supremum of the underlying
ideals. The four proof obligations are the implementation of this construction, so they are
discharged inline rather than as standalone lemmas. -/
instance instSupSet : SupSet (HopfIdeal R H) where
  sSup S :=
    { carrier := ⨆ I : S, (I : HopfIdeal R H).toIdeal
      isTwoSided' := by
        classical
        refine ⟨fun {x} b hx => ?_⟩
        rw [Submodule.mem_iSup_iff_exists_finsupp] at hx
        rcases hx with ⟨f, hf, rfl⟩
        rw [Finsupp.sum, Finset.sum_mul]
        exact Submodule.sum_mem _ fun I _ =>
          Submodule.mem_iSup_of_mem I ((I : HopfIdeal R H).mul_mem_right (hf I) b)
      comul_mem' := fun _ hx => by
        classical
        rw [Submodule.mem_iSup_iff_exists_finsupp] at hx
        rcases hx with ⟨f, hf, rfl⟩
        rw [Finsupp.sum, map_sum]
        refine Submodule.sum_mem _ fun I _ => ?_
        exact sup_le_sup
          (Ideal.leftTensorIdeal_mono (R := R) (H := H)
            (le_iSup (fun I : S => (I : HopfIdeal R H).toIdeal) I))
          (Ideal.rightTensorIdeal_mono (R := R) (H := H)
            (le_iSup (fun I : S => (I : HopfIdeal R H).toIdeal) I))
          ((I : HopfIdeal R H).comul_mem (hf I))
      counit_eq_zero' := fun _ hx => by
        classical
        rw [Submodule.mem_iSup_iff_exists_finsupp] at hx
        rcases hx with ⟨f, hf, rfl⟩
        rw [Finsupp.sum, map_sum]
        exact Finset.sum_eq_zero fun I _ => (I : HopfIdeal R H).counit_eq_zero (hf I)
      antipode_mem' := fun _ hx => by
        classical
        rw [Submodule.mem_iSup_iff_exists_finsupp] at hx
        rcases hx with ⟨f, hf, rfl⟩
        rw [Finsupp.sum, map_sum]
        exact Submodule.sum_mem _ fun I _ =>
          Submodule.mem_iSup_of_mem I ((I : HopfIdeal R H).antipode_mem (hf I)) }

/-- The underlying ideal of a supremum of a set of Hopf ideals is the supremum of the
underlying ideals indexed by that set. -/
@[simp]
theorem sSup_toIdeal (S : Set (HopfIdeal R H)) :
    (sSup S).toIdeal = ⨆ I : S, (I : HopfIdeal R H).toIdeal :=
  rfl

/-- Membership in the supremum of a set of Hopf ideals. -/
theorem mem_sSup {S : Set (HopfIdeal R H)} {x : H} :
    x ∈ sSup S ↔
      ∃ f : S →₀ H, (∀ I : S, f I ∈ (I : HopfIdeal R H)) ∧ f.sum (fun _ y => y) = x := by
  rw [← mem_toIdeal, sSup_toIdeal]
  exact Submodule.mem_iSup_iff_exists_finsupp (fun I : S => (I : HopfIdeal R H).toIdeal) x

/-- The underlying ideal of a supremum of a family of Hopf ideals is the supremum of the
underlying ideals. -/
@[simp]
theorem iSup_toIdeal {ι : Sort*} (I : ι → HopfIdeal R H) :
    (⨆ i, I i).toIdeal = ⨆ i, (I i).toIdeal := by
  rw [iSup, sSup_toIdeal]
  ext x
  simp [Submodule.mem_iSup]

/-- Membership in the supremum of a family of Hopf ideals. -/
theorem mem_iSup {ι : Type*} {I : ι → HopfIdeal R H} {x : H} :
    x ∈ ⨆ i, I i ↔ ∃ f : ι →₀ H, (∀ i, f i ∈ I i) ∧ f.sum (fun _ y => y) = x := by
  rw [← mem_toIdeal, iSup_toIdeal]
  exact Submodule.mem_iSup_iff_exists_finsupp (fun i => (I i).toIdeal) x

/-- Hopf ideals have arbitrary suprema, computed on underlying ideals. -/
instance instCompleteSemilatticeSup : CompleteSemilatticeSup (HopfIdeal R H) where
  sSup := sSup
  isLUB_sSup S :=
    ⟨fun I hI x hx => by
      rw [← mem_toIdeal, sSup_toIdeal]
      exact Submodule.mem_iSup_of_mem ⟨I, hI⟩ ((mem_toIdeal).2 hx),
    fun I hI x hx => by
      rw [← mem_toIdeal, sSup_toIdeal] at hx
      rw [← mem_toIdeal]
      have hle : (⨆ J : S, (J : HopfIdeal R H).toIdeal) ≤ I.toIdeal :=
        iSup_le fun J : S => toIdeal_le_toIdeal.2 (hI J.2)
      exact hle hx⟩

end HopfIdeal

section Bridge

variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

namespace HopfIdeal

/-- A `HopfIdeal` gives Mathlib's coideal structure on the underlying `R`-submodule, so that
Mathlib's quotient `Coalgebra`/`Bialgebra` instances fire on `H ⧸ I.toIdeal`. -/
instance instIsCoideal (I : HopfIdeal R H) :
    (I.toIdeal.restrictScalars R).IsCoideal := by
  rw [Submodule.isCoideal_iff_comul_mem]
  refine ⟨fun _ hx => I.counit_eq_zero hx, fun _ hx => ?_⟩
  have := I.comul_mem hx
  rw [← Submodule.restrictScalars_mem R, Submodule.restrictScalars_sup,
    Ideal.leftTensorIdeal_def, Ideal.rightTensorIdeal_def] at this
  simp only [AlgHom.toRingHom_eq_coe, ← AlgHom.coe_ideal_map] at this
  rw [Ideal.map_includeLeft_eq, Ideal.map_includeRight_eq] at this
  simpa only [sup_comm] using this

/-- A `HopfIdeal` gives Mathlib's `Ideal.IsHopfIdeal`, so that Mathlib's quotient
`HopfAlgebra` instance fires on `H ⧸ I.toIdeal`. -/
instance instIsHopfIdeal (I : HopfIdeal R H) : I.toIdeal.IsHopfIdeal R where
  __ := instIsCoideal I
  antipode_mem := fun _ hx => I.antipode_mem hx

end HopfIdeal

end Bridge

end TauCeti
