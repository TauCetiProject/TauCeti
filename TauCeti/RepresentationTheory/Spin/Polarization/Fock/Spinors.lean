/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Hilbert
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import TauCeti.Geometry.Symplectic.Finrank

/-!
# Dimension and dedicated Hilbert carrier of the Fock spinor module

Because `ExteriorAlgebra ℂ W` is an `abbrev` for `CliffordAlgebra 0`, modules that import
`TauCeti.Topology.Algebra.CliffordAlgebra.Basic` (such as smooth `Spinᶜ` representation and bundle
files) already carry `CliffordAlgebra.instTopologicalSpaceCliffordAlgebra` on `⋀ W`. To provide a
diamond-free carrier with no preexisting `TopologicalSpace` instance, this file packages `⋀ W` into
`TauCeti.AlmostComplexStructure.FockSpinors` with global `AddCommGroup`, `Module ℂ`,
`FiniteDimensional ℂ`, and `Nontrivial` instances, `toExterior` algebraic projection simplification
lemmas, Clifford action `fockSpinorAction`, and named abbreviations `fockSpinorsNormedAddCommGroup`
and `fockSpinorsInnerProductSpace` for local installation given `hQ`.

It also records the complex spinor dimensions `finrank_fock` and `finrank_fockSpinors`, together
with the four-dimensional chirality eigenspace dimension
`Orientation.finrank_eigenspace_fockSpinorAction_chirality`.

## Main definitions

* `TauCeti.AlmostComplexStructure.FockSpinors`: dedicated carrier of the normalized Fock spinor
  module of `J` with global `AddCommGroup`, `Module ℂ`, `FiniteDimensional ℂ`, and `Nontrivial`
  instances, plus named abbreviations `fockSpinorsNormedAddCommGroup` and
  `fockSpinorsInnerProductSpace` installed locally given `hQ`.
* `TauCeti.AlmostComplexStructure.fockSpinorsLinearEquiv` and
  `TauCeti.AlmostComplexStructure.fockSpinorsLinearIsometryEquiv`: linear and unitary equivalences
  `J.FockSpinors hQJ hQnd ≃ ⋀ W`.
* `TauCeti.AlmostComplexStructure.fockSpinorAction`: the real Clifford algebra action on
  `J.FockSpinors hQJ hQnd`.

## Main results

* `TauCeti.AlmostComplexStructure.finrank_fock` and
  `TauCeti.AlmostComplexStructure.finrank_fockSpinors`: complex dimension `2 ^ (finrank ℝ V / 2)`.
* `TauCeti.AlmostComplexStructure.liftBaseChange_fockSpinorAction_surjective` and
  `TauCeti.AlmostComplexStructure.adjoint_fockSpinorAction_ι`: surjectivity of the complexified
  action and skew-adjointness of real vector generators on `FockSpinors`.
* `Orientation.finrank_eigenspace_fockSpinorAction_chirality`: in dimension four with
  `Q v = -‖v‖²`, both `±1` chirality eigenspaces of `J.FockSpinors` have complex dimension two.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Module
open scoped InnerProductSpace

section Carrier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)

/-- The Fock spinor module `⋀ W` of an orthogonal complex structure `J` has complex dimension
`2 ^ (finrank ℝ V / 2)`. -/
theorem finrank_fock :
    finrank ℂ (ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) =
      2 ^ (finrank ℝ V / 2) := by
  rw [TauCeti.ExteriorAlgebra.finrank_eq_two_pow, J.finrank_spinPolarizationData_W hQJ hQnd]

/-- Dedicated carrier for the normalized Fock spinor module of `J`. Unlike the `abbrev`
`ExteriorAlgebra ℂ W` (`= CliffordAlgebra 0`), `FockSpinors` does not trigger
`CliffordAlgebra.instTopologicalSpaceCliffordAlgebra`, so installing its Fock Hilbert-space metric
locally in topological and Lie-group `Spinᶜ` files produces no `TopologicalSpace` diamond. -/
@[ext]
structure FockSpinors : Type _ where
  /-- The underlying element of the exterior algebra `⋀ W`. -/
  toExterior : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W

/-- Additive group structure on `J.FockSpinors hQJ hQnd` transported from `⋀ W`. -/
instance instAddCommGroupFockSpinors : AddCommGroup (J.FockSpinors hQJ hQnd) where
  zero := ⟨0⟩
  add x y := ⟨x.toExterior + y.toExterior⟩
  neg x := ⟨-x.toExterior⟩
  sub x y := ⟨x.toExterior - y.toExterior⟩
  nsmul n x := ⟨n • x.toExterior⟩
  zsmul n x := ⟨n • x.toExterior⟩
  add_assoc _ _ _ := FockSpinors.ext (add_assoc _ _ _)
  zero_add _ := FockSpinors.ext (zero_add _)
  add_zero _ := FockSpinors.ext (add_zero _)
  nsmul_zero _ := FockSpinors.ext (zero_smul ℕ _)
  nsmul_succ n x := FockSpinors.ext (succ_nsmul x.toExterior n)
  zsmul_zero' _ := FockSpinors.ext (zero_smul ℤ _)
  zsmul_succ' n x := FockSpinors.ext (SubNegMonoid.zsmul_succ' n x.toExterior)
  zsmul_neg' n x := FockSpinors.ext (SubNegMonoid.zsmul_neg' n x.toExterior)
  sub_eq_add_neg _ _ := FockSpinors.ext (sub_eq_add_neg _ _)
  neg_add_cancel _ := FockSpinors.ext (neg_add_cancel _)
  add_comm _ _ := FockSpinors.ext (add_comm _ _)

/-- Complex vector space structure on `J.FockSpinors hQJ hQnd` transported from `⋀ W`. -/
instance instModuleFockSpinors : Module ℂ (J.FockSpinors hQJ hQnd) where
  smul c x := ⟨c • x.toExterior⟩
  one_smul _ := FockSpinors.ext (one_smul ℂ _)
  mul_smul _ _ _ := FockSpinors.ext (mul_smul _ _ _)
  smul_zero _ := FockSpinors.ext (smul_zero _)
  smul_add _ _ _ := FockSpinors.ext (smul_add _ _ _)
  add_smul _ _ _ := FockSpinors.ext (add_smul _ _ _)
  zero_smul _ := FockSpinors.ext (zero_smul ℂ _)

namespace FockSpinors

variable {J hQJ hQnd}

/-- `toExterior` sends `0` to `0`. -/
@[simp]
theorem toExterior_zero : (0 : J.FockSpinors hQJ hQnd).toExterior = 0 := (rfl)

/-- `toExterior` preserves addition. -/
@[simp]
theorem toExterior_add (x y : J.FockSpinors hQJ hQnd) :
    (x + y).toExterior = x.toExterior + y.toExterior := (rfl)

/-- `toExterior` preserves negation. -/
@[simp]
theorem toExterior_neg (x : J.FockSpinors hQJ hQnd) : (-x).toExterior = -x.toExterior := (rfl)

/-- `toExterior` preserves subtraction. -/
@[simp]
theorem toExterior_sub (x y : J.FockSpinors hQJ hQnd) :
    (x - y).toExterior = x.toExterior - y.toExterior := (rfl)

/-- `toExterior` commutes with complex scalar multiplication. -/
@[simp]
theorem toExterior_smul (c : ℂ) (x : J.FockSpinors hQJ hQnd) :
    (c • x).toExterior = c • x.toExterior := (rfl)

/-- `toExterior` commutes with natural-number scalar multiplication. -/
@[simp]
theorem toExterior_nsmul (n : ℕ) (x : J.FockSpinors hQJ hQnd) :
    (n • x).toExterior = n • x.toExterior := (rfl)

/-- `toExterior` commutes with integer scalar multiplication. -/
@[simp]
theorem toExterior_zsmul (n : ℤ) (x : J.FockSpinors hQJ hQnd) :
    (n • x).toExterior = n • x.toExterior := (rfl)

end FockSpinors

/-- The underlying `ℂ`-linear equivalence `J.FockSpinors hQJ hQnd ≃ₗ[ℂ] ⋀ W`. -/
def fockSpinorsLinearEquiv :
    J.FockSpinors hQJ hQnd ≃ₗ[ℂ] ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W where
  toFun := FockSpinors.toExterior
  invFun := FockSpinors.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `fockSpinorsLinearEquiv` evaluates to the `toExterior` projection. -/
@[simp] theorem fockSpinorsLinearEquiv_apply (ψ : J.FockSpinors hQJ hQnd) :
    J.fockSpinorsLinearEquiv hQJ hQnd ψ = ψ.toExterior := (rfl)

/-- `(fockSpinorsLinearEquiv ...).symm` wraps an exterior-algebra element into `FockSpinors`. -/
@[simp] theorem fockSpinorsLinearEquiv_symm_apply
    (s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    (J.fockSpinorsLinearEquiv hQJ hQnd).symm s = ⟨s⟩ := (rfl)

/-- Finite-dimensionality of `J.FockSpinors hQJ hQnd` over `ℂ`. -/
instance instFiniteDimensionalFockSpinors : FiniteDimensional ℂ (J.FockSpinors hQJ hQnd) :=
  (J.fockSpinorsLinearEquiv hQJ hQnd).symm.finiteDimensional

/-- Nontriviality of `J.FockSpinors hQJ hQnd` (since `1 ≠ 0` in `⋀ W`). -/
instance instNontrivialFockSpinors : Nontrivial (J.FockSpinors hQJ hQnd) :=
  (J.fockSpinorsLinearEquiv hQJ hQnd).symm.injective.nontrivial

/-- The real Clifford algebra action on `J.FockSpinors hQJ hQnd`. -/
def fockSpinorAction : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (J.FockSpinors hQJ hQnd) :=
  ((J.fockSpinorsLinearEquiv hQJ hQnd).symm.conjAlgEquiv ℝ).toAlgHom.comp
    (J.realFockAction hQJ hQnd)

/-- `toExterior` intertwines `fockSpinorAction` and `realFockAction`. -/
@[simp] theorem toExterior_fockSpinorAction_apply (a : CliffordAlgebra Q)
    (ψ : J.FockSpinors hQJ hQnd) :
    (J.fockSpinorAction hQJ hQnd a ψ).toExterior = J.realFockAction hQJ hQnd a ψ.toExterior := by
  simp [fockSpinorAction, LinearEquiv.conjAlgEquiv_apply]

/-- `fockSpinorsLinearEquiv` intertwines `fockSpinorAction` and `realFockAction`. -/
theorem fockSpinorsLinearEquiv_fockSpinorAction_apply (a : CliffordAlgebra Q)
    (ψ : J.FockSpinors hQJ hQnd) :
    J.fockSpinorsLinearEquiv hQJ hQnd (J.fockSpinorAction hQJ hQnd a ψ) =
      J.realFockAction hQJ hQnd a (J.fockSpinorsLinearEquiv hQJ hQnd ψ) :=
  J.toExterior_fockSpinorAction_apply hQJ hQnd a ψ

/-- `J.FockSpinors hQJ hQnd` has complex dimension `2 ^ (finrank ℝ V / 2)`. -/
theorem finrank_fockSpinors : finrank ℂ (J.FockSpinors hQJ hQnd) = 2 ^ (finrank ℝ V / 2) := by
  rw [(J.fockSpinorsLinearEquiv hQJ hQnd).finrank_eq, J.finrank_fock hQJ hQnd]

/-- `liftBaseChange ℂ Q (J.fockSpinorAction hQJ hQnd)` is surjective onto
`Module.End ℂ (J.FockSpinors hQJ hQnd)`. -/
theorem liftBaseChange_fockSpinorAction_surjective :
    Function.Surjective (liftBaseChange ℂ Q (J.fockSpinorAction hQJ hQnd)) := by
  have heq : liftBaseChange ℂ Q (J.fockSpinorAction hQJ hQnd) =
      ((J.fockSpinorsLinearEquiv hQJ hQnd).symm.conjAlgEquiv ℂ).toAlgHom.comp
        (J.fockAction hQJ hQnd) := by
    symm
    rw [eq_liftBaseChange_iff]
    intro x
    rw [AlgHom.comp_apply, ← J.liftBaseChange_realFockAction hQJ hQnd,
      liftBaseChange_ofBaseChangeAux]
    ext ψ
    simp [LinearEquiv.conjAlgEquiv_apply]
  rw [heq]
  exact ((J.fockSpinorsLinearEquiv hQJ hQnd).symm.conjAlgEquiv ℂ).surjective.comp
    (J.fockAction_bijective hQJ hQnd).surjective

/-- The normalized Fock inner product core transported to `J.FockSpinors hQJ hQnd`. -/
@[instance_reducible]
def fockSpinorsInnerProductCore (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    InnerProductSpace.Core ℂ (J.FockSpinors hQJ hQnd) where
  inner x y := (J.fockInnerProductCore hQJ hQnd hQ).inner x.toExterior y.toExterior
  conj_inner_symm _ _ := (J.fockInnerProductCore hQJ hQnd hQ).conj_inner_symm _ _
  re_inner_nonneg _ := (J.fockInnerProductCore hQJ hQnd hQ).re_inner_nonneg _
  add_left _ _ _ := (J.fockInnerProductCore hQJ hQnd hQ).add_left _ _ _
  smul_left _ _ r := (J.fockInnerProductCore hQJ hQnd hQ).smul_left _ _ r
  definite _ hx := FockSpinors.ext ((J.fockInnerProductCore hQJ hQnd hQ).definite _ hx)

/-- Normed group structure of the normalized Fock metric on `J.FockSpinors hQJ hQnd`. -/
abbrev fockSpinorsNormedAddCommGroup (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    NormedAddCommGroup (J.FockSpinors hQJ hQnd) :=
  (J.fockSpinorsInnerProductCore hQJ hQnd hQ).toNormedAddCommGroup

/-- Complex inner product space structure of the normalized Fock metric on
`J.FockSpinors hQJ hQnd`. -/
abbrev fockSpinorsInnerProductSpace (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    InnerProductSpace ℂ (J.FockSpinors hQJ hQnd) :=
  InnerProductSpace.ofCore (J.fockSpinorsInnerProductCore hQJ hQnd hQ).toCore

/-- The inner product on `J.FockSpinors hQJ hQnd` equals the native Fock inner product of the
underlying exterior-algebra elements. -/
@[simp] theorem inner_fockSpinors (hQ : ∀ v, Q v = -‖v‖ ^ 2) (x y : J.FockSpinors hQJ hQnd) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    ⟪x, y⟫_ℂ = ⟪x.toExterior, y.toExterior⟫_ℂ := (rfl)

/-- `fockSpinorsLinearEquiv` upgraded to a linear isometry equivalence onto the Hermitian Fock
module `⋀ W`. -/
def fockSpinorsLinearIsometryEquiv (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    J.FockSpinors hQJ hQnd ≃ₗᵢ[ℂ] ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  exact (J.fockSpinorsLinearEquiv hQJ hQnd).isometryOfInner fun x y ↦
    (J.inner_fockSpinors hQJ hQnd hQ x y).symm

/-- `fockSpinorsLinearIsometryEquiv` evaluates to the `toExterior` projection. -/
@[simp] theorem fockSpinorsLinearIsometryEquiv_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (ψ : J.FockSpinors hQJ hQnd) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    J.fockSpinorsLinearIsometryEquiv hQJ hQnd hQ ψ = ψ.toExterior := (rfl)

/-- `(fockSpinorsLinearIsometryEquiv ...).symm` wraps an exterior-algebra element into
`FockSpinors`. -/
@[simp] theorem fockSpinorsLinearIsometryEquiv_symm_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    (J.fockSpinorsLinearIsometryEquiv hQJ hQnd hQ).symm s = ⟨s⟩ := (rfl)

/-- Real Clifford generators act skew-adjointly on `J.FockSpinors hQJ hQnd`. -/
theorem adjoint_fockSpinorAction_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2) (v : V) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    LinearMap.adjoint (J.fockSpinorAction hQJ hQnd (ι Q v)) =
      -J.fockSpinorAction hQJ hQnd (ι Q v) := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  let e := J.fockSpinorsLinearIsometryEquiv hQJ hQnd hQ
  have he (x : J.FockSpinors hQJ hQnd) :
      e (J.fockSpinorAction hQJ hQnd (ι Q v) x) = J.realFockAction hQJ hQnd (ι Q v) (e x) :=
    J.fockSpinorsLinearEquiv_fockSpinorAction_apply hQJ hQnd (ι Q v) x
  symm
  refine (LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_
  rw [← e.inner_map_map, ← e.inner_map_map, LinearMap.neg_apply, map_neg, he, he,
    inner_neg_left, ← LinearMap.adjoint_inner_right,
    J.adjoint_realFockAction_ι hQJ hQnd hQ v, LinearMap.neg_apply, inner_neg_right, neg_neg]

end Carrier

end TauCeti.AlmostComplexStructure

namespace Orientation

open CliffordAlgebra Module Module.End TauCeti

section DimensionFour

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)

/-- Four-dimensionality gives `FiniteDimensional ℝ V`. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

include hQ in
/-- In dimension four with `Q v = -‖v‖²`, both chirality eigenspaces (`ε = 1` and `ε = -1`) of
`J.FockSpinors` have complex dimension two for every `Q`-orthogonal complex structure `J`. -/
theorem finrank_eigenspace_fockSpinorAction_chirality
    (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)
    {ε : ℂ} (hε : ε = 1 ∨ ε = -1) :
    finrank ℂ (eigenspace (J.fockSpinorAction hQJ hQnd (chirality Q o)) ε) = 2 := by
  have hpos_two : finrank ℂ (positiveHalfSpinors o (J.fockSpinorAction hQJ hQnd)) = 2 := by
    have h4 : finrank ℂ (J.FockSpinors hQJ hQnd) = 4 := by
      rw [J.finrank_fockSpinors hQJ hQnd, (Fact.out : finrank ℝ V = 4)]
      norm_num
    rw [finrank_eq_two_mul_finrank_positiveHalfSpinors o (J.fockSpinorAction hQJ hQnd) hQ] at h4
    omega
  rcases hε with rfl | rfl
  · rwa [← positiveHalfSpinors_eq_eigenspace]
  · rw [finrank_eigenspace_chirality_neg o (J.fockSpinorAction hQJ hQnd) 1,
      ← positiveHalfSpinors_eq_eigenspace]
    exact hpos_two

end DimensionFour

end Orientation

end
