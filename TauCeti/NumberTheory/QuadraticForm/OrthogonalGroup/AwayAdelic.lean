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

Local isometries `Q ⊗ ℚ_p ≃ Q' ⊗ ℚ_p` at the primes outside `S`, carrying the reference subgroups
onto one another at almost every such prime, give isomorphisms of topological groups between the
groups away from `S` of `Q` and of `Q'`, compatible with the maps `Spin → SO → O`. When the local
isometries are given at every prime, restricting away from `S` turns the finite adelic transport
`TauCeti.restrictedProductCongrRight` into the transport away from `S`.

## Main definitions

* `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicOrthogonal`,
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpecialOrthogonal`,
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpin`: the point groups away from `S`.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpinToSpecialOrthogonal` and
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpecialOrthogonalToOrthogonal`: the
  componentwise projections.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicOrthogonalCongr`,
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpecialOrthogonalCongr`,
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.awayAdelicSpinCongr`: transport of points away from
  `S` along local isometries.

## Main results

* `OrthogonalCompactOpens.awayAdelicSpinToSpecialOrthogonal_comp_restrictAway` and
  `OrthogonalCompactOpens.awayAdelicSpecialOrthogonalToOrthogonal_comp_restrictAway`: the
  restrictions from the finite adelic groups commute with the componentwise projections.
* `OrthogonalCompactOpens.mem_range_awayAdelicSpecialOrthogonalToOrthogonal_iff`: the image of
  `SO` in `O` away from `S` is cut out by the determinant at every prime outside `S`.
* `OrthogonalCompactOpens.mem_ker_awayAdelicSpinToSpecialOrthogonal_iff`: the kernel of
  `Spin → SO` away from `S` is the componentwise `±1`.
* `awayAdelicSpecialOrthogonalCongr_comp_awayAdelicSpinToSpecialOrthogonal` and
  `awayAdelicSpecialOrthogonalToOrthogonal_comp_awayAdelicSpecialOrthogonalCongr`, in the
  namespace `OrthogonalCompactOpens`: transport away from `S` commutes with `Spin → SO → O`.
* `OrthogonalCompactOpens.awayAdelicOrthogonalCongr_comp_restrictAway` and its special
  orthogonal and Spin versions: restriction away from `S` intertwines finite adelic transport with
  transport away from `S`.

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

/-! ### Transport along local isometries -/

section Congr

open Filter

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {Q' : QuadraticForm ℚ W}
  (U' : OrthogonalCompactOpens Q')
  (e : ∀ p : {p : Nat.Primes // p ∉ S},
    (Q.baseChange ℚ_[p.1]).IsometryEquiv (Q'.baseChange ℚ_[p.1]))

/-- The isomorphism of orthogonal groups away from `S` induced by local isometries at the primes
outside `S` which carry the orthogonal reference subgroups onto one another at almost every such
prime. -/
def awayAdelicOrthogonalCongr
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p.1) (U'.orthogonal p.1)) :
    U.awayAdelicOrthogonal S ≃ₜ* U'.awayAdelicOrthogonal S where
  toMulEquiv := restrictedProductCongrRight (fun p : {p : Nat.Primes // p ∉ S} ↦ U.orthogonal p.1)
    (fun p ↦ U'.orthogonal p.1) (fun p ↦ (e p).orthogonalGroupCongr) he
  continuous_toFun :=
    continuous_restrictedProductCongrRight _ _ _ he fun p ↦ (e p).continuous_orthogonalGroupCongr
  continuous_invFun := continuous_restrictedProductCongrRight_symm _ _ _ he fun p ↦ by
    rw [(e p).orthogonalGroupCongr_symm]
    exact (e p).symm.continuous_orthogonalGroupCongr

/-- Orthogonal transport away from `S` applies the local isometry at every prime outside `S`. -/
@[simp]
theorem awayAdelicOrthogonalCongr_apply
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p.1) (U'.orthogonal p.1))
    (x : U.awayAdelicOrthogonal S) (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicOrthogonalCongr S U' e he x p = (e p).orthogonalGroupCongr (x p) :=
  restrictedProductCongrRight_apply _ _ _ he x p

/-- Inverse orthogonal transport away from `S` applies the inverse local isometries. -/
@[simp]
theorem awayAdelicOrthogonalCongr_symm_apply
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p.1) (U'.orthogonal p.1))
    (y : U'.awayAdelicOrthogonal S) (p : {p : Nat.Primes // p ∉ S}) :
    (U.awayAdelicOrthogonalCongr S U' e he).symm y p = (e p).orthogonalGroupCongr.symm (y p) :=
  restrictedProductCongrRight_symm_apply _ _ _ he y p

/-- The isomorphism of special orthogonal groups away from `S` induced by local isometries at
the primes outside `S` which carry the special orthogonal reference subgroups onto one another at
almost every such prime. -/
def awayAdelicSpecialOrthogonalCongr
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p.1) (U'.specialOrthogonal p.1)) :
    U.awayAdelicSpecialOrthogonal S ≃ₜ* U'.awayAdelicSpecialOrthogonal S where
  toMulEquiv := restrictedProductCongrRight
    (fun p : {p : Nat.Primes // p ∉ S} ↦ U.specialOrthogonal p.1)
    (fun p ↦ U'.specialOrthogonal p.1) (fun p ↦ (e p).specialOrthogonalGroupCongr) hso
  continuous_toFun := continuous_restrictedProductCongrRight _ _ _ hso fun p ↦
    (e p).continuous_specialOrthogonalGroupCongr
  continuous_invFun := continuous_restrictedProductCongrRight_symm _ _ _ hso fun p ↦ by
    rw [(e p).specialOrthogonalGroupCongr_symm]
    exact (e p).symm.continuous_specialOrthogonalGroupCongr

/-- Special orthogonal transport away from `S` applies the local isometry at every prime outside
`S`. -/
@[simp]
theorem awayAdelicSpecialOrthogonalCongr_apply
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p.1) (U'.specialOrthogonal p.1))
    (x : U.awayAdelicSpecialOrthogonal S) (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicSpecialOrthogonalCongr S U' e hso x p =
      (e p).specialOrthogonalGroupCongr (x p) :=
  restrictedProductCongrRight_apply _ _ _ hso x p

/-- Inverse special orthogonal transport away from `S` applies the inverse local isometries. -/
@[simp]
theorem awayAdelicSpecialOrthogonalCongr_symm_apply
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p.1) (U'.specialOrthogonal p.1))
    (y : U'.awayAdelicSpecialOrthogonal S) (p : {p : Nat.Primes // p ∉ S}) :
    (U.awayAdelicSpecialOrthogonalCongr S U' e hso).symm y p =
      (e p).specialOrthogonalGroupCongr.symm (y p) :=
  restrictedProductCongrRight_symm_apply _ _ _ hso y p

/-- The isomorphism of Spin groups away from `S` induced by local isometries at the primes
outside `S` which carry the Spin reference subgroups onto one another at almost every such
prime. -/
def awayAdelicSpinCongr
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p.1) (U'.spin p.1)) :
    U.awayAdelicSpin S ≃ₜ* U'.awayAdelicSpin S where
  toMulEquiv := restrictedProductCongrRight (fun p : {p : Nat.Primes // p ∉ S} ↦ U.spin p.1)
    (fun p ↦ U'.spin p.1) (fun p ↦ (e p).spinGroupEquiv) hs
  continuous_toFun :=
    continuous_restrictedProductCongrRight _ _ _ hs fun p ↦ (e p).continuous_spinGroupEquiv
  continuous_invFun := continuous_restrictedProductCongrRight_symm _ _ _ hs fun p ↦ by
    rw [(e p).spinGroupEquiv_symm]
    exact (e p).symm.continuous_spinGroupEquiv

/-- Spin transport away from `S` applies the local isometry at every prime outside `S`. -/
@[simp]
theorem awayAdelicSpinCongr_apply
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p.1) (U'.spin p.1))
    (x : U.awayAdelicSpin S) (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicSpinCongr S U' e hs x p = (e p).spinGroupEquiv (x p) :=
  restrictedProductCongrRight_apply _ _ _ hs x p

/-- Inverse Spin transport away from `S` applies the inverse local isometries. -/
@[simp]
theorem awayAdelicSpinCongr_symm_apply
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p.1) (U'.spin p.1))
    (y : U'.awayAdelicSpin S) (p : {p : Nat.Primes // p ∉ S}) :
    (U.awayAdelicSpinCongr S U' e hs).symm y p = (e p).spinGroupEquiv.symm (y p) :=
  restrictedProductCongrRight_symm_apply _ _ _ hs y p

/-- Transport away from `S` intertwines the Spin projections away from `S`. -/
theorem awayAdelicSpecialOrthogonalCongr_comp_awayAdelicSpinToSpecialOrthogonal
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p.1) (U'.spin p.1))
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p.1) (U'.specialOrthogonal p.1)) :
    (U.awayAdelicSpecialOrthogonalCongr S U' e hso :
        U.awayAdelicSpecialOrthogonal S →* U'.awayAdelicSpecialOrthogonal S).comp
        (U.awayAdelicSpinToSpecialOrthogonal S) =
      (U'.awayAdelicSpinToSpecialOrthogonal S).comp
        (U.awayAdelicSpinCongr S U' e hs : U.awayAdelicSpin S →* U'.awayAdelicSpin S) := by
  ext x p : 2
  simp

/-- Transport away from `S` intertwines the inclusions of `SO` into `O` away from `S`. -/
theorem awayAdelicSpecialOrthogonalToOrthogonal_comp_awayAdelicSpecialOrthogonalCongr
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p.1) (U'.orthogonal p.1))
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p.1) (U'.specialOrthogonal p.1)) :
    (U'.awayAdelicSpecialOrthogonalToOrthogonal S).comp
        (U.awayAdelicSpecialOrthogonalCongr S U' e hso :
          U.awayAdelicSpecialOrthogonal S →* U'.awayAdelicSpecialOrthogonal S) =
      (U.awayAdelicOrthogonalCongr S U' e he :
          U.awayAdelicOrthogonal S →* U'.awayAdelicOrthogonal S).comp
        (U.awayAdelicSpecialOrthogonalToOrthogonal S) := by
  ext g p : 2
  simp

end Congr

/-! ### Compatibility of transport with the restrictions from the finite adeles -/

section CongrRestrict

open Filter

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {Q' : QuadraticForm ℚ W}
  (U' : OrthogonalCompactOpens Q')
  (e : ∀ p : Nat.Primes, (Q.baseChange ℚ_[p]).IsometryEquiv (Q'.baseChange ℚ_[p]))

/-- Restricting away from `S` turns finite adelic orthogonal transport into orthogonal transport
away from `S`. -/
@[simp]
theorem awayAdelicOrthogonalCongr_comp_restrictAway
    (he : ∀ᶠ p in cofinite, Set.BijOn (e p).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) :
    (U.awayAdelicOrthogonalCongr S U' (fun p ↦ e p.1)
        (Subtype.val_injective.tendsto_cofinite.eventually he) :
        U.awayAdelicOrthogonal S →* U'.awayAdelicOrthogonal S).comp
        (restrictAway S U.orthogonal) =
      (restrictAway S U'.orthogonal).comp
        (restrictedProductCongrRight U.orthogonal U'.orthogonal
          (fun p ↦ (e p).orthogonalGroupCongr) he :
          U.finiteAdelicOrthogonal →* U'.finiteAdelicOrthogonal) := by
  ext x p : 2
  simp

/-- Restricting away from `S` turns finite adelic special orthogonal transport into special
orthogonal transport away from `S`. -/
@[simp]
theorem awayAdelicSpecialOrthogonalCongr_comp_restrictAway
    (hso : ∀ᶠ p in cofinite, Set.BijOn (e p).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    (U.awayAdelicSpecialOrthogonalCongr S U' (fun p ↦ e p.1)
        (Subtype.val_injective.tendsto_cofinite.eventually hso) :
        U.awayAdelicSpecialOrthogonal S →* U'.awayAdelicSpecialOrthogonal S).comp
        (restrictAway S U.specialOrthogonal) =
      (restrictAway S U'.specialOrthogonal).comp
        (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p ↦ (e p).specialOrthogonalGroupCongr) hso :
          U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal) := by
  ext x p : 2
  simp

/-- Restricting away from `S` turns finite adelic Spin transport into Spin transport away from
`S`. -/
@[simp]
theorem awayAdelicSpinCongr_comp_restrictAway
    (hs : ∀ᶠ p in cofinite, Set.BijOn (e p).spinGroupEquiv (U.spin p) (U'.spin p)) :
    (U.awayAdelicSpinCongr S U' (fun p ↦ e p.1)
        (Subtype.val_injective.tendsto_cofinite.eventually hs) :
        U.awayAdelicSpin S →* U'.awayAdelicSpin S).comp (restrictAway S U.spin) =
      (restrictAway S U'.spin).comp
        (restrictedProductCongrRight U.spin U'.spin (fun p ↦ (e p).spinGroupEquiv) hs :
          U.finiteAdelicSpin →* U'.finiteAdelicSpin) := by
  ext x p : 2
  simp

end CongrRestrict

end OrthogonalCompactOpens

end

end QuadraticMap
end TauCeti
