/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic

/-!
# Invariants of point representations and comodules

Let `H` be a commutative Hopf algebra over a commutative ring `R`, representing an affine group
`G`, and let `V` be an `R`-module. A natural point representation of `G` on `V` makes the group
`G(A)` of points with values in a commutative `R`-algebra `A` act on the scalar extension
`A ⊗[R] V`. Its invariants are the vectors `v : V` for which `1 ⊗ v` is fixed by `G(A)` for
every `A`. They play the role for the group functor that Mathlib's `Representation.invariants`
plays for a single group.

This file defines these invariants and compares them with the invariants of the corresponding
comodule, the vectors `v` with `coact v = v ⊗ 1`. Under the correspondence between natural point
representations and right `H`-comodule structures on `V`, the two submodules of `V` are equal.
Since the coaction is the action of the universal point, the identity of `H`, a vector is
invariant as soon as the universal point fixes it. Neither `V` nor `H` is assumed flat or
finite, and the test algebras include the nonreduced ones. A linear map whose scalar extensions
intertwine two point representations sends invariants to invariants.

The comodule form of these statements, for an explicit comodule and with no antipode, is in
`TauCeti.Algebra.Coalgebra.Comodule.PointsAction`.

## Main declarations

* `TauCeti.HopfAlgebra.PointRepresentation.invariants`: the submodule of vectors fixed by every
  point of every value algebra.
* `TauCeti.HopfAlgebra.PointRepresentation.mem_invariants_iff_universal`: the universal point
  detects the invariants.
* `TauCeti.HopfAlgebra.PointRepresentation.invariants_ofComodule`: the invariants of the point
  representation of a comodule are the fixed vectors of the comodule.
* `TauCeti.HopfAlgebra.PointRepresentation.invariants_eq_toSubmodule_fixedSubcomodule`: the
  invariants of a point representation are the fixed vectors of its comodule.
* `TauCeti.HopfAlgebra.PointRepresentation.apply_mem_invariants`: equivariant linear maps
  preserve invariants.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.8 and I.2.10(1)–(2).
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra.PointRepresentation

universe u v w

variable {R : Type u} {H : Type v} {V : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V]

/-- The invariants of a natural point representation on `V`: the vectors `v` whose scalar
extension `1 ⊗ v` is fixed by every point with values in every commutative algebra. -/
noncomputable def invariants (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    Submodule R V :=
  ⨅ (A : CommAlgCat.{max u v w} R) (x : points (H := H) A),
    LinearMap.eqLocus ((Theta.action A x).val.restrictScalars R ∘ₗ TensorProduct.mk R A V 1)
      (TensorProduct.mk R A V 1)

/-- A vector is invariant exactly when every point of every value algebra fixes its scalar
extension. -/
@[simp]
theorem mem_invariants {Theta : PointRepresentation (R := R) (H := H) (V := V)} {v : V} :
    v ∈ Theta.invariants ↔
      ∀ (A : CommAlgCat.{max u v w} R) (x : points (H := H) A),
        (Theta.action A x).val (1 ⊗ₜ[R] v) = 1 ⊗ₜ[R] v := by
  simp [invariants]

/-- A vector of a comodule whose scalar extension is fixed by the universal point is fixed by the
coaction. -/
private theorem mem_fixedSubcomodule_of_ofComodule_action_universal (rho : Comodule R H V) {v : V}
    (hv : ((ofComodule rho).action (CommAlgCat.of R (ULift.{max u v w} H))
      (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v) = 1 ⊗ₜ[R] v) :
    v ∈ Comodule.fixedSubcomodule R H V := by
  rw [ofComodule_action_val_eq_endOfPoint, ofConv_toConv] at hv
  exact (Comodule.mem_fixedSubcomodule_iff_endOfPoint_algEquiv ULift.algEquiv.symm).mpr hv

/-- The invariants of the point representation of a comodule are the fixed vectors of the
comodule: every point of every value algebra fixes `1 ⊗ v` exactly when `coact v = v ⊗ 1`. -/
@[simp]
theorem invariants_ofComodule (rho : Comodule R H V) :
    (ofComodule rho).invariants = (Comodule.fixedSubcomodule R H V).toSubmodule := by
  ext v
  rw [mem_invariants, Subcomodule.mem_toSubmodule]
  refine ⟨fun h ↦ mem_fixedSubcomodule_of_ofComodule_action_universal rho (h _ _),
    fun hv A x ↦ ?_⟩
  rw [ofComodule_action_val_eq_endOfPoint]
  exact Comodule.endOfPoint_tmul_of_coact_eq_tmul_one (Comodule.mem_fixedSubcomodule.mp hv) _ 1

/-- The invariants of a natural point representation are the fixed vectors of the comodule
structure it corresponds to. -/
theorem invariants_eq_toSubmodule_fixedSubcomodule
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    Theta.invariants =
      letI : Comodule R H V := toComodule Theta
      (Comodule.fixedSubcomodule R H V).toSubmodule := by
  simpa only [ofComodule_toComodule] using invariants_ofComodule (toComodule Theta)

/-- The universal point detects the invariants of a natural point representation: a vector is
invariant as soon as the universal point of `ULift H` fixes its scalar extension. -/
theorem mem_invariants_iff_universal {Theta : PointRepresentation (R := R) (H := H) (V := V)}
    {v : V} :
    v ∈ Theta.invariants ↔
      (Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
        (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v) = 1 ⊗ₜ[R] v := by
  refine ⟨fun hv ↦ mem_invariants.mp hv _ _, fun hv ↦ ?_⟩
  obtain ⟨rho, rfl⟩ : ∃ rho, Theta = ofComodule rho :=
    ⟨toComodule Theta, (ofComodule_toComodule Theta).symm⟩
  rw [invariants_ofComodule rho]
  exact Subcomodule.mem_toSubmodule.mpr
    (mem_fixedSubcomodule_of_ofComodule_action_universal rho hv)

/-- A linear map whose scalar extensions intertwine two natural point representations sends
invariants to invariants. -/
theorem apply_mem_invariants {W : Type w} [AddCommMonoid W] [Module R W]
    {Theta : PointRepresentation (R := R) (H := H) (V := V)}
    {Psi : PointRepresentation (R := R) (H := H) (V := W)} (f : V →ₗ[R] W)
    (hf : ∀ (A : CommAlgCat.{max u v w} R) (x : points (H := H) A),
      f.baseChange A ∘ₗ (Theta.action A x).val = (Psi.action A x).val ∘ₗ f.baseChange A)
    {v : V} (hv : v ∈ Theta.invariants) : f v ∈ Psi.invariants := by
  rw [mem_invariants] at hv ⊢
  intro A x
  simpa [hv A x] using (LinearMap.congr_fun (hf A x) (1 ⊗ₜ[R] v)).symm

end TauCeti.HopfAlgebra.PointRepresentation
