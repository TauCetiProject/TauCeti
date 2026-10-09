/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.FiniteAdelic
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Basic

/-!
# Orthogonal and Spin points away from a set of primes

For a rational quadratic space and compatible compact-open reference families, this file forms
`O`, `SO` and `Spin` over the adeles away from `S`. Here `S` contains only finite primes: the
archimedean place is omitted throughout. Each carrier is the generic restricted product over
`{p : Nat.Primes // p ∉ S}`, with the inherited local groups and reference subgroups.

Restriction from the finite adeles is continuous and commutes with the componentwise maps
`Spin → SO → O`. The inclusion `SO → O` is injective, with image exactly the points proper at
every retained prime. These maps allow rational diagonals and local comparisons to be used after
forgetting a set of places. No finiteness, nondegeneracy or positive-dimension hypothesis is
needed for the constructions; omitting every prime gives trivial groups.

The group operations, topology and extensionality are those of `RestrictedProductGroupAway`.
In particular, `RestrictedProduct.ext` compares elements by their retained coordinates.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q) (S : Set Nat.Primes)

/-- Orthogonal adelic points away from `S`, with the real place also omitted. -/
abbrev awayAdelicOrthogonal : Type _ :=
  RestrictedProductGroupAway S U.orthogonal

/-- Special orthogonal adelic points away from `S`, with the real place also omitted. -/
abbrev awayAdelicSpecialOrthogonal : Type _ :=
  RestrictedProductGroupAway S U.specialOrthogonal

/-- Spin adelic points away from `S`, with the real place also omitted. -/
abbrev awayAdelicSpin : Type _ :=
  RestrictedProductGroupAway S U.spin

/-- The retained orthogonal reference subgroups are open. -/
instance factIsOpenAwayOrthogonal :
    Fact (∀ p : {p : Nat.Primes // p ∉ S},
      IsOpen (U.orthogonal p.1 : Set (orthogonalGroup (Q.baseChange ℚ_[(p.1 : ℕ)])))) :=
  ⟨fun p ↦ U.isOpen_orthogonal p.1⟩

/-- The retained special orthogonal reference subgroups are open. -/
instance factIsOpenAwaySpecialOrthogonal :
    Fact (∀ p : {p : Nat.Primes // p ∉ S}, IsOpen (U.specialOrthogonal p.1 :
      Set (specialOrthogonalGroup (Q.baseChange ℚ_[(p.1 : ℕ)])))) :=
  ⟨fun p ↦ U.isOpen_specialOrthogonal p.1⟩

/-- The retained Spin reference subgroups are open. -/
instance factIsOpenAwaySpin :
    Fact (∀ p : {p : Nat.Primes // p ∉ S},
      IsOpen (U.spin p.1 : Set (spinGroup (Q.baseChange ℚ_[(p.1 : ℕ)])))) :=
  ⟨fun p ↦ U.isOpen_spin p.1⟩

/-- Forget the orthogonal components at the primes in `S`. -/
def finiteAdelicOrthogonalToAway : U.finiteAdelicOrthogonal →* U.awayAdelicOrthogonal S :=
  restrictAway S U.orthogonal

/-- Forget the special orthogonal components at the primes in `S`. -/
def finiteAdelicSpecialOrthogonalToAway :
    U.finiteAdelicSpecialOrthogonal →* U.awayAdelicSpecialOrthogonal S :=
  restrictAway S U.specialOrthogonal

/-- Forget the Spin components at the primes in `S`. -/
def finiteAdelicSpinToAway : U.finiteAdelicSpin →* U.awayAdelicSpin S :=
  restrictAway S U.spin

/-- Restriction retains the orthogonal coordinates outside `S`. -/
@[simp]
theorem finiteAdelicOrthogonalToAway_apply (x : U.finiteAdelicOrthogonal)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.finiteAdelicOrthogonalToAway S x p = x p.1 :=
  restrictAway_apply _ _ _ _

/-- Restriction retains the special orthogonal coordinates outside `S`. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalToAway_apply (x : U.finiteAdelicSpecialOrthogonal)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.finiteAdelicSpecialOrthogonalToAway S x p = x p.1 :=
  restrictAway_apply _ _ _ _

/-- Restriction retains the Spin coordinates outside `S`. -/
@[simp]
theorem finiteAdelicSpinToAway_apply (x : U.finiteAdelicSpin)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.finiteAdelicSpinToAway S x p = x p.1 :=
  restrictAway_apply _ _ _ _

/-- Orthogonal restriction is continuous in the restricted-product topologies. -/
theorem continuous_finiteAdelicOrthogonalToAway :
    Continuous (U.finiteAdelicOrthogonalToAway S) :=
  continuous_restrictAway _ _

/-- Special orthogonal restriction is continuous in the restricted-product topologies. -/
theorem continuous_finiteAdelicSpecialOrthogonalToAway :
    Continuous (U.finiteAdelicSpecialOrthogonalToAway S) :=
  continuous_restrictAway _ _

/-- Spin restriction is continuous in the restricted-product topologies. -/
theorem continuous_finiteAdelicSpinToAway : Continuous (U.finiteAdelicSpinToAway S) :=
  continuous_restrictAway _ _

/-- Apply the local Spin projection at every retained prime. Compatibility of the reference
families at every prime ensures that integral points remain integral. -/
def awayAdelicSpinToSpecialOrthogonal :
    U.awayAdelicSpin S →* U.awayAdelicSpecialOrthogonal S :=
  restrictedProductMapOfForall (fun p : {p : Nat.Primes // p ∉ S} ↦ U.spin p.1)
    (fun p ↦ U.specialOrthogonal p.1)
    (fun p ↦ CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)]))
    (fun p ↦ U.mapsTo_specialOrthogonal p.1)

/-- Apply the local special orthogonal inclusion at every retained prime. -/
def awayAdelicSpecialOrthogonalToOrthogonal :
    U.awayAdelicSpecialOrthogonal S →* U.awayAdelicOrthogonal S :=
  restrictedProductMapOfForall (fun p : {p : Nat.Primes // p ∉ S} ↦ U.specialOrthogonal p.1)
    (fun p ↦ U.orthogonal p.1)
    (fun p ↦ specialOrthogonalToOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)]))
    (fun p _ hg ↦ (U.mem_specialOrthogonal_iff p.1 _).mp hg)

/-- The away adelic Spin projection is the local projection at each retained prime. -/
@[simp]
theorem awayAdelicSpinToSpecialOrthogonal_apply (x : U.awayAdelicSpin S)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicSpinToSpecialOrthogonal S x p =
      CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)]) (x p) :=
  restrictedProductMapOfForall_apply _ _ _ _ _ _

/-- The away adelic inclusion is the local inclusion at each retained prime. -/
@[simp]
theorem awayAdelicSpecialOrthogonalToOrthogonal_apply (x : U.awayAdelicSpecialOrthogonal S)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicSpecialOrthogonalToOrthogonal S x p =
      specialOrthogonalToOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)]) (x p) :=
  restrictedProductMapOfForall_apply _ _ _ _ _ _

/-- The away adelic Spin projection is continuous. -/
theorem continuous_awayAdelicSpinToSpecialOrthogonal [FiniteDimensional ℚ V] :
    Continuous (U.awayAdelicSpinToSpecialOrthogonal S) :=
  continuous_restrictedProductMapOfForall _ _ _ _
    fun p ↦ CliffordAlgebra.continuous_spinToSpecialOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)])

/-- The away adelic special orthogonal inclusion is continuous. -/
theorem continuous_awayAdelicSpecialOrthogonalToOrthogonal :
    Continuous (U.awayAdelicSpecialOrthogonalToOrthogonal S) :=
  continuous_restrictedProductMapOfForall _ _ _ _
    fun p ↦ continuous_specialOrthogonalToOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)])

/-- Restriction away from `S` commutes with the Spin projection. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalToAway_comp_finiteAdelicSpinToSpecialOrthogonal :
    (U.finiteAdelicSpecialOrthogonalToAway S).comp U.finiteAdelicSpinToSpecialOrthogonal =
      (U.awayAdelicSpinToSpecialOrthogonal S).comp (U.finiteAdelicSpinToAway S) := by
  ext x p : 2
  simp

/-- Restriction away from `S` commutes with the special orthogonal inclusion. -/
@[simp]
theorem finiteAdelicOrthogonalToAway_comp_finiteAdelicSpecialOrthogonalToOrthogonal :
    (U.finiteAdelicOrthogonalToAway S).comp U.finiteAdelicSpecialOrthogonalToOrthogonal =
      (U.awayAdelicSpecialOrthogonalToOrthogonal S).comp
        (U.finiteAdelicSpecialOrthogonalToAway S) := by
  ext x p : 2
  simp

/-- The away adelic special orthogonal inclusion is injective. -/
theorem awayAdelicSpecialOrthogonalToOrthogonal_injective :
    Function.Injective (U.awayAdelicSpecialOrthogonalToOrthogonal S) := by
  intro x y h
  ext p : 1
  apply specialOrthogonalToOrthogonal_injective
  simpa using congrArg (fun z ↦ z p) h

/-- An away adelic orthogonal point comes from `SO` exactly when it is proper at every retained
prime. Properness imposes no additional integrality condition because the `SO` reference
subgroups are the preimages of the orthogonal ones. -/
theorem mem_range_awayAdelicSpecialOrthogonalToOrthogonal_iff (x : U.awayAdelicOrthogonal S) :
    x ∈ (U.awayAdelicSpecialOrthogonalToOrthogonal S).range ↔
      ∀ p : {p : Nat.Primes // p ∉ S},
        x p ∈ specialOrthogonalWithin (Q.baseChange ℚ_[(p.1 : ℕ)]) := by
  constructor
  · rintro ⟨y, rfl⟩ p
    rw [awayAdelicSpecialOrthogonalToOrthogonal_apply, ← range_specialOrthogonalToOrthogonal]
    exact ⟨y p, rfl⟩
  · intro hx
    simp_rw [← range_specialOrthogonalToOrthogonal, MonoidHom.mem_range] at hx
    choose y hy using hx
    refine ⟨⟨y, ?_⟩, ?_⟩
    · filter_upwards [x.2] with p hp
      rw [SetLike.mem_coe, mem_specialOrthogonal_iff, hy p]
      exact hp
    · ext p : 1
      exact (U.awayAdelicSpecialOrthogonalToOrthogonal_apply S _ p).trans (hy p)

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
