/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Isotypic
public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction

import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.HighestWeight.Existence
import TauCeti.Algebra.Lie.HighestWeight.Weyl.Dimension
import TauCeti.Algebra.Lie.UniversalEnveloping.Multiplicity
import TauCeti.Algebra.Lie.Weights.Dimension
import TauCeti.Algebra.Lie.Weights.Rank
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
import TauCeti.RepresentationTheory.Spin.Irreducible

/-!
# Kostant's isotypy theorem for the spinor module

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form `κ` over an
algebraically closed field of characteristic zero, of dimension `d` and rank `l`, and let `P` be a
polarization of `κ`, with Fock module `S = ⋀·W`. Along the adjoint quadratic lift
`CliffordAlgebra.adjointCliffordHom`, the spinor action `TauCeti.spinAction` makes `S` an
`L`-module. This module is isotypic of type `L(ρ)`, with multiplicity `2 ^ (l / 2)`.

The spinor module is a quotient of Kostant's module: acting on a nonzero spinor is a surjective
morphism from the left-regular Clifford algebra onto `S`
(`TauCeti.SpinPolarizationData.kostantSpinOrbitMap_surjective`). Kostant's module is completely
reducible, so highest weight vectors lift along this surjection
(`TauCeti.IsHighestWeightVector.exists_isHighestWeightVector_apply_eq`), and every highest weight
of `S` is a highest weight of Kostant's module, hence `ρ`. The multiplicity is then read off the
dimensions: `dim S = 2 ^ (d / 2)`, `dim L(ρ) = 2 ^ ((d - l) / 2)`, and `d = l + 2 * #Δ⁺`. In
positive even dimension `S` is the sum of the two half-spin modules; in odd dimension it is a single
spinor module, and in both cases the exponent is `l / 2` rounded down.

## Main definitions

* `TauCeti.SpinPolarizationData.kostantSpinRep`: the action of `L` on the spinor module, the
  composite of `TauCeti.spinAction` with the adjoint quadratic lift.
* `TauCeti.SpinPolarizationData.kostantSpinLieRingModule` and
  `TauCeti.SpinPolarizationData.kostantSpinLieModule`: the scoped `L`-module structure it defines.
* `TauCeti.SpinPolarizationData.kostantSpinOrbitMap`: acting on a fixed spinor, as a morphism from
  Kostant's module.

## Main results

* `TauCeti.SpinPolarizationData.eq_weylVector_of_isHighestWeightVector_kostantSpin`: every highest
  weight vector of the spinor module has weight `ρ`.
* `TauCeti.SpinPolarizationData.isIsotypicOfType_irreducibleQuotient_weylVector_kostantSpin`: the
  spinor module is isotypic of type `L(ρ)`.
* `TauCeti.SpinPolarizationData.isotypicMultiplicity_irreducibleQuotient_weylVector_kostantSpin`:
  the multiplicity of `L(ρ)` is `2 ^ (l / 2)`.
* `TauCeti.SpinPolarizationData.kostantSpinRep_isotypic` and
  `TauCeti.SpinPolarizationData.kostantSpinRep_multiplicity`: the same statements with no choice of
  Cartan subalgebra or base, the decomposition into `2 ^ (l / 2)` copies of an irreducible Lie
  submodule of dimension `2 ^ ((d - l) / 2)`.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem, the ρ-decomposition
  `C(𝔤) = End V_ρ ⊗ C(P)`, and the `𝔤`-module structure of `⋀𝔤`*, Adv. Math. 125 (1997), 275--350.
* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013).
-/

public section

universe u v

open LieAlgebra LieModule Module TauCeti.LieAlgebra CliffordAlgebra
open scoped CliffordAlgebra DirectSum

namespace TauCeti.SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {L : Type v} [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [IsKilling K L]
  (P : SpinPolarizationData (killingQuadraticForm K L))

/-- **The spinor module of the Killing form as an `L`-module.** `L` acts on the Fock module `⋀·W`
of a polarization of its Killing form through the adjoint quadratic lift
`CliffordAlgebra.adjointCliffordHom`, followed by the spinor action `TauCeti.spinAction`. -/
noncomputable def kostantSpinRep : L →ₗ⁅K⁆ Module.End K (ExteriorAlgebra K P.W) :=
  (spinAction (killingQuadraticForm K L) P).toLieHom.comp (adjointCliffordHom K L)

@[simp, grind =]
theorem kostantSpinRep_apply (x : L) :
    P.kostantSpinRep x = spinAction (killingQuadraticForm K L) P (adjointCliffordHom K L x) :=
  (rfl)

/-- **The spinor module of Kostant's theorem.** The Fock module of a polarization of the Killing
form, acted on by `L` through `TauCeti.SpinPolarizationData.kostantSpinRep`. Scoped, like Kostant's
module `CliffordAlgebra.kostantLieRingModule`: the exterior algebra of a subspace of `L` is not
otherwise an `L`-module. -/
noncomputable scoped instance kostantSpinLieRingModule :
    LieRingModule L (ExteriorAlgebra K P.W) :=
  LieRingModule.compLieHom _ P.kostantSpinRep

/-- The spinor module of Kostant's theorem is a Lie module over the base field. -/
noncomputable scoped instance kostantSpinLieModule : LieModule K L (ExteriorAlgebra K P.W) :=
  LieModule.compLieHom _ P.kostantSpinRep

/-- **The defining equation of the spinor module**: `L` acts through the spinor action of the
adjoint quadratic lift. -/
@[simp, grind =]
theorem kostantSpin_lie_def (x : L) (s : ExteriorAlgebra K P.W) :
    ⁅x, s⁆ = spinAction (killingQuadraticForm K L) P (adjointCliffordHom K L x) s :=
  (rfl)

/-- **Acting on a fixed spinor, as a morphism out of Kostant's module**: `c ↦ c • s`, from the
Clifford algebra of the Killing form under left multiplication to the spinor module. -/
noncomputable def kostantSpinOrbitMap (s : ExteriorAlgebra K P.W) :
    CliffordAlgebra (killingQuadraticForm K L) →ₗ⁅K,L⁆ ExteriorAlgebra K P.W where
  toFun c := spinAction (killingQuadraticForm K L) P c s
  map_add' c d := by rw [map_add, LinearMap.add_apply]
  map_smul' a c := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]
  map_lie' {x c} := by rw [kostant_lie_def, kostantSpin_lie_def, map_mul, mul_apply_eq_comp]

@[simp, grind =]
theorem kostantSpinOrbitMap_apply (s : ExteriorAlgebra K P.W)
    (c : CliffordAlgebra (killingQuadraticForm K L)) :
    P.kostantSpinOrbitMap s c = spinAction (killingQuadraticForm K L) P c s :=
  (rfl)

/-- **The spinor module is a quotient of Kostant's module**: acting on a nonzero spinor is onto. -/
theorem kostantSpinOrbitMap_surjective {s : ExteriorAlgebra K P.W} (hs : s ≠ 0) :
    Function.Surjective (P.kostantSpinOrbitMap s) :=
  exists_spinAction_eq P hs

variable [CharZero K] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **The only highest weight of the spinor module is `ρ`**: every highest weight vector of the
spinor module of a polarization of the Killing form has weight the half-sum of the positive
roots. -/
theorem eq_weylVector_of_isHighestWeightVector_kostantSpin [IsTriangularizable K H L]
    {base : (IsKilling.rootSystem H).Base} {lam : Dual K H} {s : ExteriorAlgebra K P.W}
    (hs : IsHighestWeightVector base lam s) :
    lam = weylVector (IsKilling.rootSystem H) base := by
  have := complementedLattice_lieSubmodule_of_isKilling K L
    (CliffordAlgebra (killingQuadraticForm K L))
  obtain ⟨c, hc, -⟩ :=
    hs.exists_isHighestWeightVector_apply_eq (P.kostantSpinOrbitMap_surjective hs.ne_zero)
  exact eq_weylVector_of_isHighestWeightVector_kostant hc

variable [IsAlgClosed K]

section Base

variable (base : (IsKilling.rootSystem H).Base)

attribute [local instance] complementedLattice_lieSubmodule_of_isKilling

/-- **The spinor module is isotypic of type `L(ρ)`.** Every irreducible Lie submodule of the spinor
module of a polarization of the Killing form is a copy of `L(ρ)`. -/
theorem isIsotypicOfType_irreducibleQuotient_weylVector_kostantSpin :
    IsIsotypicOfType K L (ExteriorAlgebra K P.W)
      (irreducibleQuotient base (weylVector (IsKilling.rootSystem H) base)) :=
  isIsotypicOfType_of_forall_isHighestWeightVector
    (isHighestWeightVector_irreducibleQuotientGenerator base _)
    fun _ _ hu ↦ P.eq_weylVector_of_isHighestWeightVector_kostantSpin hu

/-- **The multiplicity of `L(ρ)` in the spinor module** is `2 ^ (l / 2)`, for `L` of rank `l`. The
spinor module has dimension `2 ^ (d / 2)` and `L(ρ)` has dimension `2 ^ ((d - l) / 2)`, for `L` of
dimension `d`, and `d - l` is even. -/
@[simp]
theorem isotypicMultiplicity_irreducibleQuotient_weylVector_kostantSpin :
    isotypicMultiplicity K L (ExteriorAlgebra K P.W)
      (irreducibleQuotient base (weylVector (IsKilling.rootSystem H) base)) =
      2 ^ (LieAlgebra.rank K L / 2) := by
  have _ := finiteDimensional_irreducibleQuotient_weylVector base
  have hdim := finrank_of_isIsotypicOfType (M := ExteriorAlgebra K P.W) _
    (P.isIsotypicOfType_irreducibleQuotient_weylVector_kostantSpin base)
  rw [TauCeti.ExteriorAlgebra.finrank_eq_two_pow, finrank_irreducibleQuotient_weylVector] at hdim
  have hd := finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots H base
  have hW := P.finrank_eq_two_mul_finrank_W_add_finrank_line
  have hline := P.finrank_line_le_one
  rw [H.rank_eq_finrank_cartan]
  refine Nat.eq_of_mul_eq_mul_right (pow_pos two_pos ((finrank K L - finrank K H) / 2))
    (hdim.symm.trans ?_)
  rw [← pow_add]
  congr 1
  omega

/-- **The decomposition of the spinor module.** The spinor module of a polarization of the Killing
form is a direct sum of `2 ^ (l / 2)` copies of `L(ρ)`, for `L` of rank `l`. -/
theorem nonempty_lieModuleEquiv_directSum_irreducibleQuotient_weylVector_kostantSpin :
    Nonempty (ExteriorAlgebra K P.W ≃ₗ⁅K,L⁆
      ⨁ _ : Fin (2 ^ (LieAlgebra.rank K L / 2)),
        irreducibleQuotient base (weylVector (IsKilling.rootSystem H) base)) := by
  have _ := finiteDimensional_irreducibleQuotient_weylVector base
  rw [← P.isotypicMultiplicity_irreducibleQuotient_weylVector_kostantSpin base]
  exact nonempty_lieModuleEquiv_of_isIsotypicOfType _
    (P.isIsotypicOfType_irreducibleQuotient_weylVector_kostantSpin base)

end Base

/-- **Kostant's isotypy theorem for the spinor module.** Any two irreducible Lie submodules of the
spinor module of a polarization of the Killing form are isomorphic. -/
theorem kostantSpinRep_isotypic : IsIsotypic K L (ExteriorAlgebra K P.W) := by
  obtain ⟨_, _, ⟨b⟩⟩ := exists_isCartanSubalgebra_base K L
  exact (P.isIsotypicOfType_irreducibleQuotient_weylVector_kostantSpin b).isIsotypic

/-- **Kostant's multiplicity theorem for the spinor module.** The spinor module of a polarization
of the Killing form is a direct sum of `2 ^ (l / 2)` copies of an irreducible Lie submodule of
dimension `2 ^ ((d - l) / 2)`, for `L` of dimension `d` and rank `l`. -/
theorem kostantSpinRep_multiplicity :
    ∃ S : LieSubmodule K L (ExteriorAlgebra K P.W),
      IsIrreducible K L S ∧
      finrank K S = 2 ^ ((finrank K L - LieAlgebra.rank K L) / 2) ∧
      Nonempty (ExteriorAlgebra K P.W ≃ₗ⁅K,L⁆
        ⨁ _ : Fin (2 ^ (LieAlgebra.rank K L / 2)), S) := by
  obtain ⟨H, _, ⟨b⟩⟩ := exists_isCartanSubalgebra_base K L
  -- The spinor module is nonzero, so it has a highest weight vector, and its weight is `ρ`.
  obtain ⟨lam, s, hs⟩ := exists_isHighestWeightVector (M := ExteriorAlgebra K P.W) b
  obtain rfl := P.eq_weylVector_of_isHighestWeightVector_kostantSpin hs
  obtain ⟨e⟩ := lieSpan_equiv_irreducibleQuotient_of_isHighestWeightVector hs
  obtain ⟨E⟩ := P.nonempty_lieModuleEquiv_directSum_irreducibleQuotient_weylVector_kostantSpin b
  refine ⟨LieSubmodule.lieSpan K L {s}, isIrreducible_lieSpan_of_isHighestWeightVector hs, ?_,
    ⟨E.trans (DirectSum.lieModuleEquivCongrRight fun _ ↦ e.symm)⟩⟩
  rw [e.toLinearEquiv.finrank_eq, finrank_irreducibleQuotient_weylVector,
    H.rank_eq_finrank_cartan]

end TauCeti.SpinPolarizationData
