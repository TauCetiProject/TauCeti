/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.FiniteAdelic
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Basic

/-!
# Orthogonal, special orthogonal, and Spin points of the adeles away from a set of primes

Let `Q` be a quadratic form on a finite-dimensional rational vector space `V`, let `U` be a
compatible family of compact-open reference subgroups of the local orthogonal and Spin groups
(`TauCeti.QuadraticMap.OrthogonalCompactOpens`), and let `S` be a set of primes. For a finite set
of places containing the archimedean one, `S` is the set of its finite places, and the adelic
points away from it are the restricted products over the primes **outside** `S` of the local
groups of `Q ⊗ ℚ_p`, relative to `U`. This file forms them for each of `O`, `SO` and `Spin`, as
`RestrictedProductGroupAway S` of the reference families already used for the finite adelic
groups, so that the away groups are the factors split off by `awayDecomposition`. No finiteness
of `S` is needed for any of the constructions.

Every reference subgroup is open, so each away group is a Hausdorff topological group, locally
compact for `O` and `Spin`. The local projections `Spin(V_p) → SO(V_p) → O(V_p)` assemble into
continuous componentwise homomorphisms of away groups, and these commute with the restrictions
`restrictAway S` from the finite adelic groups, which forget the components at `S`. As for the
finite adelic groups, `SO(V)(𝔸^S) → O(V)(𝔸^S)` is injective with image cut out by the
determinant at every prime outside `S`, and for a nondegenerate form on a nonzero space the
kernel of `Spin(V)(𝔸^S) → SO(V)(𝔸^S)` consists of the elements whose every component is `1` or
`-1`.

## Main definitions

* `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicOrthogonal`,
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpecialOrthogonal`,
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpin`: the point groups away from `S`.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpinToSpecialOrthogonal` and
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpecialOrthogonalToOrthogonal`: the
  componentwise projections.

## Main results

* `OrthogonalCompactOpens.awayAdelicSpinToSpecialOrthogonal_comp_restrictAway` and
  `OrthogonalCompactOpens.awayAdelicSpecialOrthogonalToOrthogonal_comp_restrictAway`: the
  restrictions from the finite adelic groups commute with the componentwise projections.
* `OrthogonalCompactOpens.mem_range_awayAdelicSpecialOrthogonalToOrthogonal_iff`: the image of
  `SO` in `O` away from `S` is cut out by the determinant at every prime outside `S`.
* `OrthogonalCompactOpens.mem_ker_awayAdelicSpinToSpecialOrthogonal_iff`: the kernel of
  `Spin → SO` away from `S` is the componentwise `±1`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti
namespace QuadraticMap

open _root_.QuadraticMap
open scoped RestrictedProduct TensorProduct

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

namespace OrthogonalCompactOpens

variable {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q) (S : Set Nat.Primes)

/-! ### The three point groups away from `S` -/

/-- The orthogonal group `O(V)(𝔸^S)` of the adeles away from `S`: the restricted product over the
primes outside `S` of the local orthogonal groups relative to the reference subgroups
`U.orthogonal p`. -/
abbrev awayAdelicOrthogonal : Type _ :=
  RestrictedProductGroupAway S U.orthogonal

/-- The special orthogonal group `SO(V)(𝔸^S)` of the adeles away from `S`: the restricted product
over the primes outside `S` of the local special orthogonal groups relative to the derived
reference subgroups `U.specialOrthogonal p`. -/
abbrev awayAdelicSpecialOrthogonal : Type _ :=
  RestrictedProductGroupAway S U.specialOrthogonal

/-- The Spin group `Spin(V)(𝔸^S)` of the adeles away from `S`: the restricted product over the
primes outside `S` of the local Spin groups relative to the reference subgroups `U.spin p`. -/
abbrev awayAdelicSpin : Type _ :=
  RestrictedProductGroupAway S U.spin

/-! ### Topology -/

/-- The orthogonal reference subgroups at the primes outside `S` are open, which makes the
orthogonal group away from `S` a topological group. -/
instance factIsOpenOrthogonalAway :
    Fact (∀ p : {p : Nat.Primes // p ∉ S},
      IsOpen (U.orthogonal p.1 : Set (orthogonalGroup (Q.baseChange ℚ_[p.1])))) :=
  ⟨fun p ↦ U.isOpen_orthogonal p.1⟩

/-- The special orthogonal reference subgroups at the primes outside `S` are open, which makes the
special orthogonal group away from `S` a topological group. -/
instance factIsOpenSpecialOrthogonalAway :
    Fact (∀ p : {p : Nat.Primes // p ∉ S}, IsOpen (U.specialOrthogonal p.1 :
      Set (specialOrthogonalGroup (Q.baseChange ℚ_[p.1])))) :=
  ⟨fun p ↦ U.isOpen_specialOrthogonal p.1⟩

/-- The Spin reference subgroups at the primes outside `S` are open, which makes the Spin group
away from `S` a topological group. -/
instance factIsOpenSpinAway :
    Fact (∀ p : {p : Nat.Primes // p ∉ S},
      IsOpen (U.spin p.1 : Set (spinGroup (Q.baseChange ℚ_[p.1])))) :=
  ⟨fun p ↦ U.isOpen_spin p.1⟩

/-! ### The componentwise projections -/

/-- The componentwise projection `Spin(V)(𝔸^S) → SO(V)(𝔸^S)`, assembled from the local Spin
projections at the primes outside `S`. -/
def awayAdelicSpinToSpecialOrthogonal :
    U.awayAdelicSpin S →* U.awayAdelicSpecialOrthogonal S :=
  restrictedProductMapOfForall (fun p : {p : Nat.Primes // p ∉ S} ↦ U.spin p.1)
    (fun p ↦ U.specialOrthogonal p.1)
    (fun p ↦ CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[p.1]))
    fun p ↦ U.mapsTo_specialOrthogonal p.1

/-- The Spin projection away from `S` is the local Spin projection at every prime outside `S`. -/
@[simp]
theorem awayAdelicSpinToSpecialOrthogonal_apply (x : U.awayAdelicSpin S)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicSpinToSpecialOrthogonal S x p =
      CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[p.1]) (x p) :=
  restrictedProductMapOfForall_apply _ _ _ _ x p

/-- The Spin projection away from `S` is continuous. -/
theorem continuous_awayAdelicSpinToSpecialOrthogonal [FiniteDimensional ℚ V] :
    Continuous (U.awayAdelicSpinToSpecialOrthogonal S) :=
  continuous_restrictedProductMapOfForall _ _ _ _ fun p : {p : Nat.Primes // p ∉ S} ↦
    CliffordAlgebra.continuous_spinToSpecialOrthogonal (Q.baseChange ℚ_[p.1])

/-- The componentwise inclusion `SO(V)(𝔸^S) → O(V)(𝔸^S)`. It is well defined because the special
orthogonal reference subgroups are the preimages of the orthogonal ones. -/
def awayAdelicSpecialOrthogonalToOrthogonal :
    U.awayAdelicSpecialOrthogonal S →* U.awayAdelicOrthogonal S :=
  restrictedProductMapOfForall (fun p : {p : Nat.Primes // p ∉ S} ↦ U.specialOrthogonal p.1)
    (fun p ↦ U.orthogonal p.1)
    (fun p ↦ specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p.1]))
    fun p _ hg ↦ (U.mem_specialOrthogonal_iff p.1 _).mp hg

/-- The inclusion of `SO` into `O` away from `S` is the local inclusion at every prime outside
`S`. -/
@[simp]
theorem awayAdelicSpecialOrthogonalToOrthogonal_apply (x : U.awayAdelicSpecialOrthogonal S)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicSpecialOrthogonalToOrthogonal S x p =
      specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p.1]) (x p) :=
  restrictedProductMapOfForall_apply _ _ _ _ x p

/-- The inclusion of `SO` into `O` away from `S` is continuous. -/
theorem continuous_awayAdelicSpecialOrthogonalToOrthogonal :
    Continuous (U.awayAdelicSpecialOrthogonalToOrthogonal S) :=
  continuous_restrictedProductMapOfForall _ _ _ _ fun p : {p : Nat.Primes // p ∉ S} ↦
    continuous_specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p.1])

/-! ### Compatibility with the restrictions from the finite adeles -/

/-- Restricting a finite adelic Spin point away from `S` commutes with projecting it to `SO`. -/
@[simp]
theorem awayAdelicSpinToSpecialOrthogonal_comp_restrictAway :
    (U.awayAdelicSpinToSpecialOrthogonal S).comp (restrictAway S U.spin) =
      (restrictAway S U.specialOrthogonal).comp U.finiteAdelicSpinToSpecialOrthogonal := by
  ext x p
  simp

/-- Restricting a finite adelic special orthogonal point away from `S` commutes with including it
in `O`. -/
@[simp]
theorem awayAdelicSpecialOrthogonalToOrthogonal_comp_restrictAway :
    (U.awayAdelicSpecialOrthogonalToOrthogonal S).comp (restrictAway S U.specialOrthogonal) =
      (restrictAway S U.orthogonal).comp U.finiteAdelicSpecialOrthogonalToOrthogonal := by
  ext x p
  simp

/-! ### The image of `SO` and the kernel of the Spin projection -/

/-- The inclusion of `SO` into `O` away from `S` is injective. -/
theorem awayAdelicSpecialOrthogonalToOrthogonal_injective :
    Function.Injective (U.awayAdelicSpecialOrthogonalToOrthogonal S) := by
  intro x y h
  ext p : 1
  apply specialOrthogonalToOrthogonal_injective
  rw [← awayAdelicSpecialOrthogonalToOrthogonal_apply,
    ← awayAdelicSpecialOrthogonalToOrthogonal_apply, h]

/-- An orthogonal point away from `S` comes from the special orthogonal group away from `S`
exactly when each of its components has determinant one. As for the finite adelic groups, the
derived reference subgroups make this exact: a proper local isometry in `U.orthogonal p` lies in
`U.specialOrthogonal p`. -/
theorem mem_range_awayAdelicSpecialOrthogonalToOrthogonal_iff (x : U.awayAdelicOrthogonal S) :
    x ∈ (U.awayAdelicSpecialOrthogonalToOrthogonal S).range ↔
      ∀ p : {p : Nat.Primes // p ∉ S},
        x p ∈ specialOrthogonalWithin (Q.baseChange ℚ_[p.1]) := by
  constructor
  · rintro ⟨y, rfl⟩ p
    rw [awayAdelicSpecialOrthogonalToOrthogonal_apply,
      ← range_specialOrthogonalToOrthogonal]
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

/-- For a nondegenerate form on a nonzero space, a Spin point away from `S` projects to the
identity of `SO(V)(𝔸^S)` exactly when each of its components is `1` or `-1` in the local Clifford
algebra. -/
theorem mem_ker_awayAdelicSpinToSpecialOrthogonal_iff [FiniteDimensional ℚ V] [Nontrivial V]
    (hQ : Q.Nondegenerate) (x : U.awayAdelicSpin S) :
    x ∈ (U.awayAdelicSpinToSpecialOrthogonal S).ker ↔
      ∀ p : {p : Nat.Primes // p ∉ S},
        ((x p : spinGroup (Q.baseChange ℚ_[p.1])) : CliffordAlgebra (Q.baseChange ℚ_[p.1])) =
            1 ∨
          ((x p : spinGroup (Q.baseChange ℚ_[p.1])) : CliffordAlgebra (Q.baseChange ℚ_[p.1])) =
            -1 := by
  rw [MonoidHom.mem_ker, RestrictedProduct.ext_iff]
  refine forall_congr' fun p ↦ ?_
  have : Nontrivial (ℚ_[p.1] ⊗[ℚ] V) := Module.nontrivial_of_finrank_pos <| by
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  have hQp : (Q.baseChange ℚ_[p.1]).Nondegenerate :=
    _root_.QuadraticForm.Nondegenerate.baseChange hQ
  rw [awayAdelicSpinToSpecialOrthogonal_apply, RestrictedProduct.one_apply, ← MonoidHom.mem_ker,
    CliffordAlgebra.mem_ker_spinToSpecialOrthogonal_iff _ hQp]
  simp only [Subtype.ext_iff, OneMemClass.coe_one, CliffordAlgebra.spinGroup.coe_negOne]

end OrthogonalCompactOpens

end

end QuadraticMap
end TauCeti
