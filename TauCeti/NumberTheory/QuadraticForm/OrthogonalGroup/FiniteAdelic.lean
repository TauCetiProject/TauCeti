/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.CompactOpen
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Projection
public import TauCeti.Topology.Algebra.RestrictedProduct.Map

/-!
# Finite adelic orthogonal, special orthogonal, and Spin groups

Let `Q` be a quadratic form on a finite-dimensional rational vector space `V`, and let `U` be a
compatible family of compact-open reference subgroups of the local orthogonal and Spin groups
(`TauCeti.QuadraticMap.OrthogonalCompactOpens`). This file forms the three finite adelic point
groups `O(V)(𝔸_f)`, `SO(V)(𝔸_f)` and `Spin(V)(𝔸_f)`: the restricted products over the primes of
the local groups of `Q ⊗ ℚ_p` relative to `U`, the special orthogonal reference subgroups being the
ones derived from the orthogonal family.

Every reference subgroup is open, so each of the three restricted products is a Hausdorff
topological group for its restricted-product topology, and the orthogonal and Spin ones are
locally compact because their reference subgroups are compact. The local topologies are the
canonical ones on linear automorphisms and on the Clifford algebra, so the compactness and
openness recorded in `U` are statements about these adelic groups.

The local projections `Spin(V_p) → SO(V_p) → O(V_p)` carry the reference subgroups into one
another at every prime, so they assemble into continuous componentwise homomorphisms of finite
adelic groups. The map `SO(V)(𝔸_f) → O(V)(𝔸_f)` is injective, and its image is exactly the
finite adelic isometries whose every component has determinant one: a proper isometry lying in
`U_p^O` lies in the derived subgroup `U_p^{SO}` by definition, so no integrality is lost. For a
nondegenerate form on a nonzero space, the kernel of `Spin(V)(𝔸_f) → SO(V)(𝔸_f)` consists of the
finite adeles whose every component is `1` or `-1`.

## Main definitions

* `TauCeti.QuadraticMap.OrthogonalCompactOpens.finiteAdelicOrthogonal`,
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.finiteAdelicSpecialOrthogonal`,
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.finiteAdelicSpin`: the finite adelic point groups.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.finiteAdelicSpinToSpecialOrthogonal` and
  `TauCeti.QuadraticMap.OrthogonalCompactOpens.finiteAdelicSpecialOrthogonalToOrthogonal`: the
  componentwise projections.

## Main results

* `OrthogonalCompactOpens.mem_range_finiteAdelicSpecialOrthogonalToOrthogonal_iff`: the image of
  adelic `SO` in adelic `O` is cut out by the determinant at every prime.
* `OrthogonalCompactOpens.mem_ker_finiteAdelicSpinToSpecialOrthogonal_iff`: the kernel of adelic
  `Spin → SO` is the componentwise `±1`.

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

variable {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-! ### The three finite adelic groups -/

/-- The finite adelic orthogonal group `O(V)(𝔸_f)`: the restricted product of the local
orthogonal groups `O(V_p)` relative to the reference subgroups `U.orthogonal p`. -/
abbrev finiteAdelicOrthogonal : Type _ :=
  RestrictedProductGroup U.orthogonal

/-- The finite adelic special orthogonal group `SO(V)(𝔸_f)`: the restricted product of the local
special orthogonal groups relative to the derived reference subgroups `U.specialOrthogonal p`. -/
abbrev finiteAdelicSpecialOrthogonal : Type _ :=
  RestrictedProductGroup U.specialOrthogonal

/-- The finite adelic Spin group `Spin(V)(𝔸_f)`: the restricted product of the local Spin groups
relative to the reference subgroups `U.spin p`. -/
abbrev finiteAdelicSpin : Type _ :=
  RestrictedProductGroup U.spin

/-! ### Topology -/

/-- The orthogonal reference subgroups are open, which makes the finite adelic orthogonal group a
topological group. -/
instance factIsOpenOrthogonal :
    Fact (∀ p : Nat.Primes,
      IsOpen (U.orthogonal p : Set (orthogonalGroup (Q.baseChange ℚ_[p])))) :=
  ⟨U.isOpen_orthogonal⟩

/-- The special orthogonal reference subgroups are open, which makes the finite adelic special
orthogonal group a topological group. -/
instance factIsOpenSpecialOrthogonal :
    Fact (∀ p : Nat.Primes, IsOpen (U.specialOrthogonal p :
      Set (specialOrthogonalGroup (Q.baseChange ℚ_[p])))) :=
  ⟨U.isOpen_specialOrthogonal⟩

/-- The Spin reference subgroups are open, which makes the finite adelic Spin group a topological
group. -/
instance factIsOpenSpin :
    Fact (∀ p : Nat.Primes, IsOpen (U.spin p : Set (spinGroup (Q.baseChange ℚ_[p])))) :=
  ⟨U.isOpen_spin⟩

/-- The orthogonal reference subgroups are compact spaces. -/
instance compactSpace_orthogonal (p : Nat.Primes) : CompactSpace (U.orthogonal p) :=
  isCompact_iff_compactSpace.mp (U.isCompact_orthogonal p)

/-- The Spin reference subgroups are compact spaces. -/
instance compactSpace_spin (p : Nat.Primes) : CompactSpace (U.spin p) :=
  isCompact_iff_compactSpace.mp (U.isCompact_spin p)

/-! ### The componentwise projections -/

/-- The componentwise projection `Spin(V)(𝔸_f) → SO(V)(𝔸_f)`, assembled from the local Spin
projections, which carry `U.spin p` into the derived subgroup `U.specialOrthogonal p`. -/
def finiteAdelicSpinToSpecialOrthogonal :
    U.finiteAdelicSpin →* U.finiteAdelicSpecialOrthogonal :=
  restrictedProductMapOfForall U.spin U.specialOrthogonal
    (fun p ↦ CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[p]))
    U.mapsTo_specialOrthogonal

/-- The adelic Spin projection is the local Spin projection at every prime. -/
@[simp]
theorem finiteAdelicSpinToSpecialOrthogonal_apply (x : U.finiteAdelicSpin) (p : Nat.Primes) :
    U.finiteAdelicSpinToSpecialOrthogonal x p =
      CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[p]) (x p) :=
  restrictedProductMapOfForall_apply _ _ _ _ x p

/-- The adelic Spin projection is continuous. -/
theorem continuous_finiteAdelicSpinToSpecialOrthogonal [FiniteDimensional ℚ V] :
    Continuous U.finiteAdelicSpinToSpecialOrthogonal :=
  continuous_restrictedProductMapOfForall _ _ _ _
    fun p : Nat.Primes ↦ CliffordAlgebra.continuous_spinToSpecialOrthogonal (Q.baseChange ℚ_[p])

/-- The componentwise inclusion `SO(V)(𝔸_f) → O(V)(𝔸_f)`. It is well defined because the special
orthogonal reference subgroups are the preimages of the orthogonal ones. -/
def finiteAdelicSpecialOrthogonalToOrthogonal :
    U.finiteAdelicSpecialOrthogonal →* U.finiteAdelicOrthogonal :=
  restrictedProductMapOfForall U.specialOrthogonal U.orthogonal
    (fun p ↦ specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p]))
    (fun p _ hg ↦ (U.mem_specialOrthogonal_iff p _).mp hg)

/-- The adelic inclusion of `SO` into `O` is the local inclusion at every prime. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalToOrthogonal_apply (x : U.finiteAdelicSpecialOrthogonal)
    (p : Nat.Primes) :
    U.finiteAdelicSpecialOrthogonalToOrthogonal x p =
      specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p]) (x p) :=
  restrictedProductMapOfForall_apply _ _ _ _ x p

/-- The adelic inclusion of `SO` into `O` is continuous. -/
theorem continuous_finiteAdelicSpecialOrthogonalToOrthogonal :
    Continuous U.finiteAdelicSpecialOrthogonalToOrthogonal :=
  continuous_restrictedProductMapOfForall _ _ _ _
    fun p : Nat.Primes ↦ continuous_specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p])

/-- The adelic inclusion of `SO` into `O` is injective. -/
theorem finiteAdelicSpecialOrthogonalToOrthogonal_injective :
    Function.Injective U.finiteAdelicSpecialOrthogonalToOrthogonal := by
  intro x y h
  ext p : 1
  apply specialOrthogonalToOrthogonal_injective
  rw [← finiteAdelicSpecialOrthogonalToOrthogonal_apply,
    ← finiteAdelicSpecialOrthogonalToOrthogonal_apply, h]

/-- A finite adelic isometry comes from the finite adelic special orthogonal group exactly when
each of its components has determinant one. The derived reference subgroups make this exact:
a proper local isometry in `U.orthogonal p` lies in `U.specialOrthogonal p`. -/
theorem mem_range_finiteAdelicSpecialOrthogonalToOrthogonal_iff (x : U.finiteAdelicOrthogonal) :
    x ∈ U.finiteAdelicSpecialOrthogonalToOrthogonal.range ↔
      ∀ p : Nat.Primes, x p ∈ specialOrthogonalWithin (Q.baseChange ℚ_[p]) := by
  constructor
  · rintro ⟨y, rfl⟩ p
    rw [finiteAdelicSpecialOrthogonalToOrthogonal_apply,
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
      exact (U.finiteAdelicSpecialOrthogonalToOrthogonal_apply _ p).trans (hy p)

/-- For a nondegenerate form on a nonzero space, a finite adelic Spin element projects to the
identity of `SO(V)(𝔸_f)` exactly when each of its components is `1` or `-1` in the local Clifford
algebra. -/
theorem mem_ker_finiteAdelicSpinToSpecialOrthogonal_iff [FiniteDimensional ℚ V] [Nontrivial V]
    (hQ : Q.Nondegenerate)
    (x : U.finiteAdelicSpin) :
    x ∈ U.finiteAdelicSpinToSpecialOrthogonal.ker ↔
      ∀ p : Nat.Primes,
        ((x p : spinGroup (Q.baseChange ℚ_[p])) : CliffordAlgebra (Q.baseChange ℚ_[p])) = 1 ∨
          ((x p : spinGroup (Q.baseChange ℚ_[p])) : CliffordAlgebra (Q.baseChange ℚ_[p])) = -1 := by
  rw [MonoidHom.mem_ker, RestrictedProduct.ext_iff]
  refine forall_congr' fun p ↦ ?_
  have : Nontrivial (ℚ_[p] ⊗[ℚ] V) := Module.nontrivial_of_finrank_pos <| by
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  have hQp : (Q.baseChange ℚ_[p]).Nondegenerate := _root_.QuadraticForm.Nondegenerate.baseChange hQ
  rw [finiteAdelicSpinToSpecialOrthogonal_apply, RestrictedProduct.one_apply,
    ← MonoidHom.mem_ker]
  refine (CliffordAlgebra.mem_ker_spinToSpecialOrthogonal_iff _ hQp _).trans ?_
  constructor
  · rintro (hx | hx)
    · left
      simp only [hx, OneMemClass.coe_one]
    · right
      simp only [hx, CliffordAlgebra.spinGroup.coe_negOne]
  · rintro (hx | hx)
    · left
      apply Subtype.ext
      simpa only [OneMemClass.coe_one] using hx
    · right
      apply Subtype.ext
      simpa only [CliffordAlgebra.spinGroup.coe_negOne] using hx

end OrthogonalCompactOpens

end

end QuadraticMap
end TauCeti
