/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.FiniteAdelic
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.SpinorNormImage
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinorNorm
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open
import Mathlib.NumberTheory.Padics.LocalField

/-!
# The finite adelic spinor norm

For a nondegenerate rational quadratic space and compatible compact-open data `U`, the local
spinor norms assemble into a continuous homomorphism on the finite adelic special orthogonal
group. Its codomain is the restricted product of local square-class groups relative to the
images of `U.specialOrthogonal p` under the local spinor norms. These reference subgroups are
derived from `U`, rather than independently chosen: this ensures that every reference point
maps into the reference subgroup at every prime.

The adelic spinor kernel consists exactly of the adelic proper isometries with trivial spinor
norm at every prime. The finite adelic Spin projection lands in this kernel. In dimension at
most one the spinor norm is trivial on the entire finite adelic special orthogonal group.

The construction uses `restrictedProductMapOfForall` and its continuity theorem, the local
reference images from `SpinorNormImage`, and `CliffordAlgebra.continuous_spinorNorm`.

## Main definitions and results

* `OrthogonalCompactOpens.finiteAdelicSquareClasses`: the square-class restricted product with
  the spinor-norm reference images.
* `OrthogonalCompactOpens.adelicSpinorNorm` and `OrthogonalCompactOpens.adelicSpinorNorm_apply`:
  the adelic spinor norm and its coordinate evaluation rule.
* `OrthogonalCompactOpens.adelicSpinorKernel` and
  `OrthogonalCompactOpens.mem_adelicSpinorKernel_iff`: the kernel and its local characterization.
* `OrthogonalCompactOpens.finiteAdelicSpinToSpinorKernel`: the adelic Spin projection with
  codomain restricted to the adelic spinor kernel.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap
open scoped TensorProduct

noncomputable section

private instance invertibleTwoRat : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
private instance invertibleTwoPadic (p : Nat.Primes) : Invertible (2 : ℚ_[p]) :=
  invertibleOfNonzero two_ne_zero

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q) (hQ : Q.Nondegenerate)

/-- The restricted product of local square-class groups relative to the spinor-norm images
of the special orthogonal reference subgroups. -/
abbrev finiteAdelicSquareClasses : Type _ :=
  RestrictedProductGroup (U.localSpinorNormImage hQ)

/-- The spinor-norm reference images are open, so their restricted product is a topological
group for the restricted-product topology. -/
instance factIsOpenLocalSpinorNormImage :
    Fact (∀ p : Nat.Primes, IsOpen (U.localSpinorNormImage hQ p :
      Set (Multiplicative (SquareClassGroup ℚ_[p])))) :=
  ⟨U.isOpen_localSpinorNormImage hQ⟩

/-- The finite adelic spinor norm on the special orthogonal group, formed componentwise from
the local spinor norms. -/
def adelicSpinorNorm : U.finiteAdelicSpecialOrthogonal →* U.finiteAdelicSquareClasses hQ :=
  restrictedProductMapOfForall U.specialOrthogonal (U.localSpinorNormImage hQ)
    (fun p ↦ CliffordAlgebra.spinorNorm (Q.baseChange ℚ_[p])
      (QuadraticForm.Nondegenerate.baseChange hQ))
    (fun p g hg ↦ (U.mem_localSpinorNormImage_iff hQ p _).mpr ⟨⟨g, hg⟩, rfl⟩)

/-- Each component of the adelic spinor norm is the corresponding local spinor norm. -/
@[simp]
theorem adelicSpinorNorm_apply (g : U.finiteAdelicSpecialOrthogonal) (p : Nat.Primes) :
    U.adelicSpinorNorm hQ g p = CliffordAlgebra.spinorNorm (Q.baseChange ℚ_[p])
      (QuadraticForm.Nondegenerate.baseChange hQ) (g p) :=
  restrictedProductMapOfForall_apply _ _ _ _ g p

/-- The finite adelic spinor norm is continuous for the restricted-product topologies. -/
theorem continuous_adelicSpinorNorm : Continuous (U.adelicSpinorNorm hQ) := by
  apply continuous_restrictedProductMapOfForall
  intro p
  apply CliffordAlgebra.continuous_spinorNorm
  rw [square_eq_range_powMonoidHom]
  exact isOpen_range_powMonoidHom (K := ℚ_[p]) (n := 2) two_ne_zero

/-- The kernel of the finite adelic spinor norm in the finite adelic special orthogonal group. -/
def adelicSpinorKernel : Subgroup U.finiteAdelicSpecialOrthogonal :=
  (U.adelicSpinorNorm hQ).ker

/-- The adelic spinor kernel is the kernel of the adelic spinor-norm homomorphism. -/
theorem adelicSpinorKernel_def :
    U.adelicSpinorKernel hQ = (U.adelicSpinorNorm hQ).ker :=
  (rfl)

/-- Membership in the adelic spinor kernel means that the spinor norm is trivial at every
finite prime. -/
@[simp]
theorem mem_adelicSpinorKernel_iff (g : U.finiteAdelicSpecialOrthogonal) :
    g ∈ U.adelicSpinorKernel hQ ↔ ∀ p : Nat.Primes,
      CliffordAlgebra.spinorNorm (Q.baseChange ℚ_[p])
        (QuadraticForm.Nondegenerate.baseChange hQ) (g p) = 1 := by
  rw [adelicSpinorKernel_def, MonoidHom.mem_ker, RestrictedProduct.ext_iff]
  simp only [adelicSpinorNorm_apply, RestrictedProduct.one_apply]

/-- The adelic Spin projection has trivial adelic spinor norm. -/
@[simp]
theorem adelicSpinorNorm_finiteAdelicSpinToSpecialOrthogonal (x : U.finiteAdelicSpin) :
    U.adelicSpinorNorm hQ (U.finiteAdelicSpinToSpecialOrthogonal x) = 1 := by
  ext p : 1
  simp only [adelicSpinorNorm_apply, finiteAdelicSpinToSpecialOrthogonal_apply,
    CliffordAlgebra.spinorNorm_spinToSpecialOrthogonal, RestrictedProduct.one_apply]

/-- The finite adelic Spin projection with codomain restricted to the adelic spinor kernel. -/
def finiteAdelicSpinToSpinorKernel : U.finiteAdelicSpin →* U.adelicSpinorKernel hQ :=
  U.finiteAdelicSpinToSpecialOrthogonal.codRestrict _ fun x ↦
    MonoidHom.mem_ker.mpr (U.adelicSpinorNorm_finiteAdelicSpinToSpecialOrthogonal hQ x)

/-- The corestricted adelic Spin projection agrees with the projection into adelic `SO`. -/
@[simp]
theorem coe_finiteAdelicSpinToSpinorKernel_apply (x : U.finiteAdelicSpin) :
    (U.finiteAdelicSpinToSpinorKernel hQ x : U.finiteAdelicSpecialOrthogonal) =
      U.finiteAdelicSpinToSpecialOrthogonal x := by
  rfl

/-- The adelic Spin projection remains continuous after restricting its codomain to the kernel. -/
theorem continuous_finiteAdelicSpinToSpinorKernel :
    Continuous (U.finiteAdelicSpinToSpinorKernel hQ) := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, coe_finiteAdelicSpinToSpinorKernel_apply] using
    U.continuous_finiteAdelicSpinToSpecialOrthogonal

/-- In dimension zero or one the finite adelic special orthogonal spinor norm is trivial. -/
theorem adelicSpinorNorm_eq_one_of_finrank_le_one (hV : Module.finrank ℚ V ≤ 1) :
    U.adelicSpinorNorm hQ = 1 := by
  ext g p : 2
  have hdim : Module.finrank ℚ_[p] (ℚ_[p] ⊗[ℚ] V) ≤ 1 := by
    simpa only [Module.finrank_baseChange] using hV
  simp only [adelicSpinorNorm_apply, MonoidHom.one_apply, RestrictedProduct.one_apply,
    CliffordAlgebra.spinorNorm_eq_one_of_finrank_le_one _ _ hdim]

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
