/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra.SymmetricAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Invariant polynomial functions on rational orbits and their closures

Let `M` be a finite projective comodule over a commutative Hopf algebra `H` over `R`. Equipping
`Module.Dual R M` with the contragredient comodule structure (`TauCeti.Comodule.dual`) makes the
polynomial algebra `Sym(M*)` an `H`-comodule algebra
(`TauCeti.ComoduleAlgebra.symmetricAlgebra`).

* On any coinvariant polynomial `p ∈ Sym(M*)^H`, the orbit coordinate map at `m ∈ M` takes the
  constant value `algebraMap R H (p(m))` (`TauCeti.Comodule.orbitCoordinates_of_mem_coinvariants`),
  so rational group translations preserve `p(m)`
  (`TauCeti.Comodule.lift_eval_basePointsRepresentation_of_mem_coinvariants`).
* Over an algebraically closed field `k`, when `H` is of finite type, every coinvariant polynomial
  `p ∈ Sym(M*)^H` is constant across the closure order on `TauCeti.Comodule.VectorOrbit k H M`: if
  `VectorOrbit.mk w ≤ VectorOrbit.mk v`, then `p(w) = p(v)`
  (`TauCeti.Comodule.VectorOrbit.lift_eval_eq_of_mk_le_mk_of_mem_coinvariants`).

## Main results

* `TauCeti.Comodule.orbitCoordinates_eq_lift_symmetricAlgebraCoact`: orbit coordinates expressed
  through the contragredient symmetric-algebra coaction and the antipode.
* `TauCeti.Comodule.orbitCoordinates_of_mem_coinvariants`: coinvariant polynomials have scalar orbit
  coordinates.
* `TauCeti.Comodule.lift_eval_basePointsRepresentation_of_mem_coinvariants`: coinvariant polynomials
  are invariant on rational orbits.
* `TauCeti.Comodule.VectorOrbit.lift_eval_eq_of_mk_le_mk_of_mem_coinvariants`: coinvariant
  polynomials are constant on orbit closures.

## References

* A. Borel, *Linear Algebraic Groups* (2nd ed.), Springer GTM 126, §1.8.
* J. C. Jantzen, *Representations of Algebraic Groups* (2nd ed.), AMS, Part I, §2.10.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

section Semiring

variable {R : Type u} {H : Type v} {M : Type w}
  [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M] [Module.Finite R M] [Module.Projective R M]

attribute [local instance] dual ComoduleAlgebra.symmetricAlgebra

/-- The orbit coordinate map at `m` factors through the contragredient symmetric-algebra coaction
followed by evaluation at `m` on the polynomial leg and the antipode on `H`. -/
theorem orbitCoordinates_eq_lift_symmetricAlgebraCoact (m : M)
    (p : SymmetricAlgebra R (Module.Dual R M)) :
    orbitCoordinates (H := H) m p =
      Algebra.TensorProduct.lift
        ((Algebra.ofId R H).comp (SymmetricAlgebra.lift (Module.Dual.eval R M m)))
        (_root_.HopfAlgebra.antipodeAlgHom R H) (fun _ _ ↦ Commute.all _ _)
        (symmetricAlgebraCoact R H (Module.Dual R M) p) := by
  let Φ : SymmetricAlgebra R (Module.Dual R M) ⊗[R] H →ₐ[R] H :=
    Algebra.TensorProduct.lift
      ((Algebra.ofId R H).comp (SymmetricAlgebra.lift (Module.Dual.eval R M m)))
      (_root_.HopfAlgebra.antipodeAlgHom R H) (fun _ _ ↦ Commute.all _ _)
  suffices orbitCoordinates (H := H) m =
      Φ.comp (symmetricAlgebraCoact R H (Module.Dual R M)) from
    DFunLike.congr_fun this p
  ext φ
  simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    orbitCoordinates_ι, AlgHom.comp_apply, symmetricAlgebraCoact_ι, dual_coact]
  have key (t : Module.Dual R M ⊗[R] H) :
      Φ ((SymmetricAlgebra.ι R (Module.Dual R M)).rTensor H t) =
        _root_.HopfAlgebra.antipodeAlgHom R H (dualTensorHom R M H t m) := by
    induction t using TensorProduct.inductionOn with
    | tmul ψ h =>
      simp only [Φ, LinearMap.rTensor_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        SymmetricAlgebra.lift_ι_apply, Module.Dual.eval_apply, Algebra.ofId_apply,
        dualTensorHom_apply, Algebra.smul_def, map_mul, AlgHom.commutes]
    | add x y hx hy => simp [hx, hy]
  rw [key, _root_.HopfAlgebra.antipodeAlgHom_apply, dualTensorHom_dualCoact_apply]
  exact (TauCeti.HopfAlgebra.antipode_antipode _).symm

/-- **Coinvariant polynomials have constant orbit coordinates.** -/
theorem orbitCoordinates_of_mem_coinvariants (m : M)
    {p : SymmetricAlgebra R (Module.Dual R M)}
    (hp : p ∈ ComoduleAlgebra.coinvariants R H (SymmetricAlgebra R (Module.Dual R M))) :
    orbitCoordinates (H := H) m p =
      algebraMap R H (SymmetricAlgebra.lift (Module.Dual.eval R M m) p) := by
  have hcoact : symmetricAlgebraCoact R H (Module.Dual R M) p = p ⊗ₜ[R] (1 : H) := by
    simpa [ComoduleAlgebra.mem_coinvariants, ComoduleAlgebra.symmetricAlgebra_coact] using hp
  rw [orbitCoordinates_eq_lift_symmetricAlgebraCoact m p, hcoact]
  simp

/-- **Coinvariant polynomials are invariant under rational group points.** -/
theorem lift_eval_basePointsRepresentation_of_mem_coinvariants (m : M)
    (g : WithConv (H →ₐ[R] R)) {p : SymmetricAlgebra R (Module.Dual R M)}
    (hp : p ∈ ComoduleAlgebra.coinvariants R H (SymmetricAlgebra R (Module.Dual R M))) :
    SymmetricAlgebra.lift (Module.Dual.eval R M (basePointsRepresentation M g m)) p =
      SymmetricAlgebra.lift (Module.Dual.eval R M m) p := by
  rw [← comp_orbitCoordinates, AlgHom.comp_apply, orbitCoordinates_of_mem_coinvariants m hp,
    AlgHom.commutes, Algebra.algebraMap_self_apply]

end Semiring

section Closure

attribute [local instance] dual ComoduleAlgebra.symmetricAlgebra

namespace VectorOrbit

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **Coinvariant polynomials are constant on orbit closures.** Over an algebraically closed field,
if the rational orbit of `w` lies in the closure of the rational orbit of `v`, then every
`H`-coinvariant polynomial function on `M` takes the same value at `w` and at `v`. -/
theorem lift_eval_eq_of_mk_le_mk_of_mem_coinvariants {v w : M}
    (h : (mk w : VectorOrbit k H M) ≤ mk v) {p : SymmetricAlgebra k (Module.Dual k M)}
    (hp : p ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k M))) :
    SymmetricAlgebra.lift (Module.Dual.eval k M w) p =
      SymmetricAlgebra.lift (Module.Dual.eval k M v) p := by
  have h0 :=
    lift_eval_eq_zero_of_mk_le_mk_of_forall_lift_eval_basePointsRepresentation_eq_zero h
      (p := p - algebraMap k _ (SymmetricAlgebra.lift (Module.Dual.eval k M v) p)) fun g ↦ by
        simp [lift_eval_basePointsRepresentation_of_mem_coinvariants v g hp]
  simpa [sub_eq_zero] using h0

end VectorOrbit

end Closure

end TauCeti.Comodule
