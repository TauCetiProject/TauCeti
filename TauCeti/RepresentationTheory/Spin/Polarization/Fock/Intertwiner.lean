/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.HalfSpinor
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Hilbert
import TauCeti.Geometry.Symplectic.Finrank

/-!
# Unitary polarization independence and Hilbert carrier of the Fock spinor module

For an orthogonal complex structure `J` on a finite-dimensional real inner product space `V` with
`Q v = -‖v‖²`, `TauCeti.AlmostComplexStructure.fockInnerProductSpace` equips the Fock spinor
module `⋀ W` (`W` the holomorphic `i`-eigenspace of `J`) with a canonical Hermitian inner product
under which real Clifford generators act skew-adjointly.

While the carrier `⋀ W` depends on the choice of orthogonal complex structure `J`, this file shows
that the resulting Hermitian Clifford module is **independent of `J` up to a `Circle`-torsor of
unitary intertwiners** — and more generally, for any linear isometry `f : V ≃ₗᵢ[ℝ] V'` between
real inner product spaces carrying orthogonal complex structures `J` and `J'`, the Fock modules of
`J` and `J'` are intertwined along `f` by a complex linear isometry equivalence, unique up to a
phase in `Circle`.

In addition, because `ExteriorAlgebra ℂ W` is an `abbrev` for `CliffordAlgebra 0`, modules that
import `TauCeti.Topology.Algebra.CliffordAlgebra.Basic` (such as smooth `Spinᶜ` representation and
bundle files) already carry `CliffordAlgebra.instTopologicalSpaceCliffordAlgebra` on `⋀ W`. To
provide a diamond-free Hilbert-space model with global `NormedAddCommGroup` and
`InnerProductSpace ℂ` instances, this file also packages `⋀ W` into the dedicated carrier
`TauCeti.AlmostComplexStructure.FockSpinors` with Clifford action `fockSpinorAction`.

## Main definitions

* `TauCeti.AlmostComplexStructure.FockSpinors`: dedicated Hilbert-space carrier of the normalized
  Fock spinor module of `J`, carrying global `NormedAddCommGroup`, `InnerProductSpace ℂ`, and
  `FiniteDimensional ℂ` instances.
* `TauCeti.AlmostComplexStructure.fockSpinorsLinearEquiv`: the `ℂ`-linear equivalence
  `J.FockSpinors hQJ hQnd ≃ₗ[ℂ] ⋀ W`.
* `TauCeti.AlmostComplexStructure.fockSpinorAction`: the real Clifford algebra action on
  `J.FockSpinors hQJ hQnd`.

## Main results

* `TauCeti.AlmostComplexStructure.finrank_fock`,
  `TauCeti.AlmostComplexStructure.finrank_fockSpinors`: complex dimension `2 ^ (finrank ℝ V / 2)`.
* `TauCeti.AlmostComplexStructure.complexifyAction_realFockAction`: complexifying `realFockAction`
  recovers `fockAction`.
* `TauCeti.AlmostComplexStructure.exists_unitary_intertwiner_realFockAction`,
  `TauCeti.AlmostComplexStructure.existsUnique_circle_smul_intertwiner_realFockAction`: existence
  and `Circle`-uniqueness of unitary Fock intertwiners on `⋀ W`.
* `TauCeti.AlmostComplexStructure.exists_unitary_intertwiner_fockSpinorAction`,
  `TauCeti.AlmostComplexStructure.existsUnique_circle_smul_intertwiner_fockSpinorAction`: the same
  on the global Hilbert-space carrier `FockSpinors`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Module
open scoped TensorProduct

section Dimension

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)

/-- The Fock spinor module `⋀ W` of an orthogonal complex structure `J` has complex dimension
`2 ^ (finrank ℝ V / 2)`. -/
theorem finrank_fock :
    finrank ℂ (ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) =
      2 ^ (finrank ℝ V / 2) := by
  rw [TauCeti.ExteriorAlgebra.finrank_eq_two_pow, J.finrank_spinPolarizationData_W hQJ hQnd]

/-- Complexifying `realFockAction` via `CliffordAlgebra.complexifyAction` recovers `fockAction`. -/
@[simp]
theorem complexifyAction_realFockAction :
    complexifyAction (J.realFockAction hQJ hQnd) = J.fockAction hQJ hQnd := by
  refine CliffordAlgebra.hom_ext ?_
  ext v
  simp [realFockAction_ι]

end Dimension

section Intertwiner

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  (J : AlmostComplexStructure V) (J' : AlmostComplexStructure V')
  {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ V'}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hQJ' : ∀ v, Q' (J' v) = Q' v) (hQnd' : Q'.Nondegenerate) (hQ' : ∀ v, Q' v = -‖v‖ ^ 2)

/-- **Existence of unitary Fock intertwiners**: for any linear isometry `f : V ≃ₗᵢ[ℝ] V'`, the
native Hermitian Fock spinor modules of `J` and `J'` are intertwined along `f` by a complex linear
isometry equivalence. -/
theorem exists_unitary_intertwiner_realFockAction (f : V ≃ₗᵢ[ℝ] V') :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    letI := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
    letI := J'.fockInnerProductSpace hQJ' hQnd' hQ'
    ∃ U : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W ≃ₗᵢ[ℂ]
        ExteriorAlgebra ℂ (J'.spinPolarizationData hQJ' hQnd').W,
      ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ J.realFockAction hQJ hQnd (ι Q v) =
        J'.realFockAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  let := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockInnerProductSpace hQJ' hQnd' hQ'
  have hV : finrank ℝ V = 2 * (finrank ℝ V / 2) :=
    (Nat.two_mul_div_two_of_even J.even_finrank_real).symm
  have hS' : finrank ℂ (ExteriorAlgebra ℂ (J'.spinPolarizationData hQJ' hQnd').W) =
      2 ^ (finrank ℝ V / 2) := by
    rw [J'.finrank_fock hQJ' hQnd', f.toLinearEquiv.finrank_eq]
  exact exists_unitary_intertwiner_of_finrank_eq hQ hQ' f hV
    (J.adjoint_realFockAction_ι hQJ hQnd hQ) (J'.adjoint_realFockAction_ι hQJ' hQnd' hQ')
    (J.finrank_fock hQJ hQnd) hS'

/-- **Uniqueness of unitary Fock intertwiners up to `Circle`**: any two unitary intertwiners
between the Hermitian Fock modules of `J` and `J'` along a map `f : V → V'` differ by a unique
phase in `Circle`. -/
theorem existsUnique_circle_smul_intertwiner_realFockAction {f : V → V'} :
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    letI := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
    letI := J'.fockInnerProductSpace hQJ' hQnd' hQ'
    ∀ U₁ U₂ : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W ≃ₗᵢ[ℂ]
        ExteriorAlgebra ℂ (J'.spinPolarizationData hQJ' hQnd').W,
      (∀ v, U₁.toLinearEquiv.toLinearMap ∘ₗ J.realFockAction hQJ hQnd (ι Q v) =
        J'.realFockAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U₁.toLinearEquiv.toLinearMap) →
      (∀ v, U₂.toLinearEquiv.toLinearMap ∘ₗ J.realFockAction hQJ hQnd (ι Q v) =
        J'.realFockAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U₂.toLinearEquiv.toLinearMap) →
      ∃! z : Circle, ∀ s, U₂ s = (z : ℂ) • U₁ s := by
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  let := J'.fockNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockInnerProductSpace hQJ' hQnd' hQ'
  intro U₁ U₂ hU₁ hU₂
  have hsurj : Function.Surjective (complexifyAction (J.realFockAction hQJ hQnd)) := by
    rw [J.complexifyAction_realFockAction hQJ hQnd]
    exact (J.fockAction_bijective hQJ hQnd).surjective
  exact existsUnique_circle_smul_intertwiner hsurj U₁ U₂ hU₁ hU₂

end Intertwiner

/-! ### Dedicated Hilbert-space carrier `FockSpinors` -/

section Carrier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (J : AlmostComplexStructure V) {Q : QuadraticForm ℝ V}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)

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

/-- The underlying `ℂ`-linear equivalence `J.FockSpinors hQJ hQnd ≃ₗ[ℂ] ⋀ W`. -/
def fockSpinorsLinearEquiv :
    J.FockSpinors hQJ hQnd ≃ₗ[ℂ]
      ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W where
  toFun := FockSpinors.toExterior
  invFun := FockSpinors.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `fockSpinorsLinearEquiv` evaluates to the `toExterior` projection. -/
@[simp]
theorem fockSpinorsLinearEquiv_apply (ψ : J.FockSpinors hQJ hQnd) :
    J.fockSpinorsLinearEquiv hQJ hQnd ψ = ψ.toExterior :=
  (rfl)

/-- `(fockSpinorsLinearEquiv ...).symm` wraps an exterior-algebra element into `FockSpinors`. -/
@[simp]
theorem fockSpinorsLinearEquiv_symm_apply
    (s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    (J.fockSpinorsLinearEquiv hQJ hQnd).symm s = ⟨s⟩ :=
  (rfl)

/-- Finite-dimensionality of `J.FockSpinors hQJ hQnd` over `ℂ`. -/
instance instFiniteDimensionalFockSpinors :
    FiniteDimensional ℂ (J.FockSpinors hQJ hQnd) :=
  (J.fockSpinorsLinearEquiv hQJ hQnd).symm.finiteDimensional

/-- Nontriviality of `J.FockSpinors hQJ hQnd` (since `1 ≠ 0` in `⋀ W`). -/
instance instNontrivialFockSpinors :
    Nontrivial (J.FockSpinors hQJ hQnd) :=
  (J.fockSpinorsLinearEquiv hQJ hQnd).symm.injective.nontrivial

/-- The real Clifford algebra action on `J.FockSpinors hQJ hQnd`. -/
def fockSpinorAction :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (J.FockSpinors hQJ hQnd) :=
  ((J.fockSpinorsLinearEquiv hQJ hQnd).symm.conjAlgEquiv ℝ).toAlgHom.comp
    (J.realFockAction hQJ hQnd)

/-- `toExterior` intertwines `fockSpinorAction` and `realFockAction`. -/
@[simp]
theorem toExterior_fockSpinorAction_apply (a : CliffordAlgebra Q)
    (ψ : J.FockSpinors hQJ hQnd) :
    (J.fockSpinorAction hQJ hQnd a ψ).toExterior =
      J.realFockAction hQJ hQnd a ψ.toExterior := by
  simp [fockSpinorAction, LinearEquiv.conjAlgEquiv_apply]

/-- `fockSpinorsLinearEquiv` intertwines `fockSpinorAction` and `realFockAction`. -/
theorem fockSpinorsLinearEquiv_fockSpinorAction_apply (a : CliffordAlgebra Q)
    (ψ : J.FockSpinors hQJ hQnd) :
    J.fockSpinorsLinearEquiv hQJ hQnd (J.fockSpinorAction hQJ hQnd a ψ) =
      J.realFockAction hQJ hQnd a (J.fockSpinorsLinearEquiv hQJ hQnd ψ) :=
  J.toExterior_fockSpinorAction_apply hQJ hQnd a ψ

/-- `J.FockSpinors hQJ hQnd` has complex dimension `2 ^ (finrank ℝ V / 2)`. -/
theorem finrank_fockSpinors :
    finrank ℂ (J.FockSpinors hQJ hQnd) = 2 ^ (finrank ℝ V / 2) := by
  rw [(J.fockSpinorsLinearEquiv hQJ hQnd).finrank_eq, J.finrank_fock hQJ hQnd]

/-- `complexifyAction (J.fockSpinorAction hQJ hQnd)` is surjective onto
`Module.End ℂ (J.FockSpinors hQJ hQnd)`. -/
theorem complexifyAction_fockSpinorAction_surjective :
    Function.Surjective (complexifyAction (J.fockSpinorAction hQJ hQnd)) :=
  (complexifyAction_bijective_of_finrank_eq (J.fockSpinorAction hQJ hQnd) hQnd
    (Nat.two_mul_div_two_of_even J.even_finrank_real).symm
    (J.finrank_fockSpinors hQJ hQnd)).surjective

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

/-- `fockSpinorsLinearEquiv` upgraded to a linear isometry equivalence onto the Hermitian Fock
module `⋀ W`. -/
def fockSpinorsLinearIsometryEquiv (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    J.FockSpinors hQJ hQnd ≃ₗᵢ[ℂ]
      ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  let := J.fockNormedAddCommGroup hQJ hQnd hQ
  let := J.fockInnerProductSpace hQJ hQnd hQ
  refine { J.fockSpinorsLinearEquiv hQJ hQnd with norm_map' := fun x ↦ ?_ }
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  rfl

/-- `fockSpinorsLinearIsometryEquiv` evaluates to the `toExterior` projection. -/
@[simp]
theorem fockSpinorsLinearIsometryEquiv_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (ψ : J.FockSpinors hQJ hQnd) :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J.fockNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockInnerProductSpace hQJ hQnd hQ
    J.fockSpinorsLinearIsometryEquiv hQJ hQnd hQ ψ = ψ.toExterior :=
  (rfl)

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
      e (J.fockSpinorAction hQJ hQnd (ι Q v) x) =
        J.realFockAction hQJ hQnd (ι Q v) (e x) :=
    J.fockSpinorsLinearEquiv_fockSpinorAction_apply hQJ hQnd (ι Q v) x
  symm
  refine (LinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ ?_
  rw [← e.inner_map_map, ← e.inner_map_map, LinearMap.neg_apply, map_neg, he, he,
    inner_neg_left, ← LinearMap.adjoint_inner_right,
    J.adjoint_realFockAction_ι hQJ hQnd hQ v, LinearMap.neg_apply, inner_neg_right, neg_neg]

end Carrier

section CarrierIntertwiner

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  (J : AlmostComplexStructure V) (J' : AlmostComplexStructure V')
  {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ V'}
  (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hQJ' : ∀ v, Q' (J' v) = Q' v) (hQnd' : Q'.Nondegenerate) (hQ' : ∀ v, Q' v = -‖v‖ ^ 2)

/-- Along any linear isometry `f : V ≃ₗᵢ[ℝ] V'`, the Hilbert Fock spinor spaces `FockSpinors` of
`J` and `J'` are intertwined by a unitary equivalence. -/
theorem exists_unitary_intertwiner_fockSpinorAction (f : V ≃ₗᵢ[ℝ] V') :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J'.fockSpinorsNormedAddCommGroup hQJ' hQnd' hQ'
    letI := J'.fockSpinorsInnerProductSpace hQJ' hQnd' hQ'
    ∃ U : J.FockSpinors hQJ hQnd ≃ₗᵢ[ℂ] J'.FockSpinors hQJ' hQnd',
      ∀ v, U.toLinearEquiv.toLinearMap ∘ₗ J.fockSpinorAction hQJ hQnd (ι Q v) =
        J'.fockSpinorAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U.toLinearEquiv.toLinearMap := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  let := J'.fockSpinorsNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockSpinorsInnerProductSpace hQJ' hQnd' hQ'
  have hV : finrank ℝ V = 2 * (finrank ℝ V / 2) :=
    (Nat.two_mul_div_two_of_even J.even_finrank_real).symm
  have hS' : finrank ℂ (J'.FockSpinors hQJ' hQnd') = 2 ^ (finrank ℝ V / 2) := by
    rw [J'.finrank_fockSpinors hQJ' hQnd', f.toLinearEquiv.finrank_eq]
  exact exists_unitary_intertwiner_of_finrank_eq hQ hQ' f hV
    (J.adjoint_fockSpinorAction_ι hQJ hQnd hQ) (J'.adjoint_fockSpinorAction_ι hQJ' hQnd' hQ')
    (J.finrank_fockSpinors hQJ hQnd) hS'

/-- Any two unitary intertwiners between `J.FockSpinors` and `J'.FockSpinors` along `f : V → V'`
differ by a unique phase in `Circle`. -/
theorem existsUnique_circle_smul_intertwiner_fockSpinorAction {f : V → V'} :
    letI := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
    letI := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
    letI := J'.fockSpinorsNormedAddCommGroup hQJ' hQnd' hQ'
    letI := J'.fockSpinorsInnerProductSpace hQJ' hQnd' hQ'
    ∀ U₁ U₂ : J.FockSpinors hQJ hQnd ≃ₗᵢ[ℂ] J'.FockSpinors hQJ' hQnd',
      (∀ v, U₁.toLinearEquiv.toLinearMap ∘ₗ J.fockSpinorAction hQJ hQnd (ι Q v) =
        J'.fockSpinorAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U₁.toLinearEquiv.toLinearMap) →
      (∀ v, U₂.toLinearEquiv.toLinearMap ∘ₗ J.fockSpinorAction hQJ hQnd (ι Q v) =
        J'.fockSpinorAction hQJ' hQnd' (ι Q' (f v)) ∘ₗ U₂.toLinearEquiv.toLinearMap) →
      ∃! z : Circle, ∀ ψ, U₂ ψ = (z : ℂ) • U₁ ψ := by
  let := J.fockSpinorsNormedAddCommGroup hQJ hQnd hQ
  let := J.fockSpinorsInnerProductSpace hQJ hQnd hQ
  let := J'.fockSpinorsNormedAddCommGroup hQJ' hQnd' hQ'
  let := J'.fockSpinorsInnerProductSpace hQJ' hQnd' hQ'
  intro U₁ U₂ hU₁ hU₂
  exact existsUnique_circle_smul_intertwiner
    (J.complexifyAction_fockSpinorAction_surjective hQJ hQnd) U₁ U₂ hU₁ hU₂

end CarrierIntertwiner

end TauCeti.AlmostComplexStructure
