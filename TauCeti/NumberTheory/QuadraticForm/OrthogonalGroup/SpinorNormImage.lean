/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.CompactOpen
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.LowRank
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Isometry
import Mathlib.NumberTheory.Padics.LocalField
import TauCeti.Algebra.Group.PowMonoidHom
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open

/-!
# Spinor-norm images of compact-open subgroups

For compatible compact-open reference subgroups of the local orthogonal and Spin groups, the
reference subgroup in the square-class group is the image of the derived special orthogonal
subgroup under the local spinor norm. This file packages that restricted homomorphism and its
range, and proves that the range is open. The latter follows from the local-field theorem that the
squares form an open subgroup of the units, hence the square-class quotient is discrete.

In dimension at most one the local special orthogonal spinor norm is trivial, so every reference
image is trivial. Thus openness alone does not identify the reference image with any particular
nontrivial subgroup of local square classes.

Isometric transport of a local special orthogonal reference subgroup preserves its spinor-norm
image, allowing these reference families to be compared across quadratic coordinates.

## Main definitions

* `TauCeti.QuadraticMap.OrthogonalCompactOpens.localSpinorNorm`: the spinor norm restricted to the
  derived local special orthogonal reference subgroup.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.localSpinorNormImage`: its range in the local
  square-class group.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
-/

public section

namespace TauCeti
namespace QuadraticMap

open _root_.QuadraticMap
open scoped TensorProduct

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-- The local spinor norm restricted to the derived special orthogonal reference subgroup. -/
def OrthogonalCompactOpens.localSpinorNorm (hQ : Q.Nondegenerate) (p : Nat.Primes) :
    U.specialOrthogonal p →* Multiplicative (SquareClassGroup ℚ_[p]) :=
  (CliffordAlgebra.spinorNorm (Q.baseChange ℚ_[p])
    (QuadraticForm.Nondegenerate.baseChange hQ)).comp (U.specialOrthogonal p).subtype

/-- The restricted local spinor norm agrees with the ambient spinor norm. -/
@[simp]
theorem OrthogonalCompactOpens.localSpinorNorm_apply (hQ : Q.Nondegenerate)
    (p : Nat.Primes) (g : U.specialOrthogonal p) :
    U.localSpinorNorm hQ p g = CliffordAlgebra.spinorNorm (Q.baseChange ℚ_[p])
      (QuadraticForm.Nondegenerate.baseChange hQ) g := by
  rw [localSpinorNorm, MonoidHom.comp_apply, Subgroup.subtype_apply]

/-- The reference subgroup in the local square-class group is the image of the derived special
orthogonal reference subgroup under the spinor norm. -/
def OrthogonalCompactOpens.localSpinorNormImage (hQ : Q.Nondegenerate) (p : Nat.Primes) :
    Subgroup (Multiplicative (SquareClassGroup ℚ_[p])) :=
  (U.localSpinorNorm hQ p).range

/-- Membership in the local spinor-norm image is witnessed by a point of the derived special
orthogonal reference subgroup. -/
theorem OrthogonalCompactOpens.mem_localSpinorNormImage_iff (hQ : Q.Nondegenerate)
    (p : Nat.Primes) (x : Multiplicative (SquareClassGroup ℚ_[p])) :
    x ∈ U.localSpinorNormImage hQ p ↔
      ∃ g : U.specialOrthogonal p,
        CliffordAlgebra.spinorNorm (Q.baseChange ℚ_[p])
          (QuadraticForm.Nondegenerate.baseChange hQ) g = x := by
  simp only [localSpinorNormImage, MonoidHom.mem_range, localSpinorNorm_apply]

/-- The local spinor-norm reference image is open in the square-class group. -/
theorem OrthogonalCompactOpens.isOpen_localSpinorNormImage (hQ : Q.Nondegenerate)
    (p : Nat.Primes) :
    IsOpen (U.localSpinorNormImage hQ p :
      Set (Multiplicative (SquareClassGroup ℚ_[p]))) := by
  let : DiscreteTopology (SquareClassGroup ℚ_[p]) :=
    QuotientAddGroup.discreteTopology (by
      -- `SquareClassGroup` is the additive quotient of `Additive ℚ_[p]ˣ` by
      -- `(Subgroup.square ℚ_[p]ˣ).toAddSubgroup`. Both `Additive` and `Subgroup.toAddSubgroup`
      -- are identity wrappers on carriers and topology, so this `change` is definitional
      -- unfolding to the multiplicative statement about the square subgroup of `ℚ_[p]ˣ`.
      change IsOpen (Subgroup.square ℚ_[p]ˣ : Set ℚ_[p]ˣ)
      rw [square_eq_range_powMonoidHom]
      exact isOpen_range_powMonoidHom (K := ℚ_[p]) (n := 2) two_ne_zero)
  exact isOpen_discrete _

/-- In dimension at most one every local spinor-norm reference image is trivial. -/
theorem OrthogonalCompactOpens.localSpinorNormImage_eq_bot_of_finrank_le_one
    (hQ : Q.Nondegenerate) (hV : Module.finrank ℚ V ≤ 1) (p : Nat.Primes) :
    U.localSpinorNormImage hQ p = ⊥ := by
  have hdim : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] V) ≤ 1 := by
    simpa only [Module.finrank_baseChange] using hV
  have hnorm := CliffordAlgebra.spinorNorm_eq_one_of_finrank_le_one
    (Q.baseChange ℚ_[p]) (QuadraticForm.Nondegenerate.baseChange hQ) hdim
  rw [localSpinorNormImage, localSpinorNorm, hnorm]
  exact MonoidHom.range_one

end

section Isometry

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
  {Q : QuadraticForm ℚ V} {Q' : QuadraticForm ℚ W}

/-- Isometric transport of a local special orthogonal reference subgroup preserves its
spinor-norm image. -/
theorem OrthogonalCompactOpens.localSpinorNormImage_eq_of_isometry
    (U : OrthogonalCompactOpens Q) (U' : OrthogonalCompactOpens Q')
    (hQ : Q.Nondegenerate) (p : Nat.Primes)
    (e : (Q.baseChange ℚ_[p]).IsometryEquiv (Q'.baseChange ℚ_[p]))
    (he : Set.BijOn e.specialOrthogonalGroupCongr (U.specialOrthogonal p)
      (U'.specialOrthogonal p)) :
    U.localSpinorNormImage hQ p = U'.localSpinorNormImage
      (QuadraticForm.Nondegenerate.of_baseChange
        (e.nondegenerate_iff.mp (QuadraticForm.Nondegenerate.baseChange hQ))) p := by
  have hmap : (U.specialOrthogonal p).map (e.specialOrthogonalGroupCongr : _ →* _) =
      U'.specialOrthogonal p := SetLike.coe_injective he.image_eq
  simp only [localSpinorNormImage, localSpinorNorm, MonoidHom.range_comp,
    _root_.Subgroup.range_subtype]
  rw [← hmap, _root_.Subgroup.map_map]
  congr 1
  ext g
  exact (e.spinorNorm_specialOrthogonalGroupCongr
    (QuadraticForm.Nondegenerate.baseChange hQ) g).symm

end Isometry

end QuadraticMap
end TauCeti
