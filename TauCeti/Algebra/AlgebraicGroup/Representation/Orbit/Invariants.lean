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
  (`TauCeti.Comodule.VectorOrbit.lift_eval_eq_of_mk_le_mk`).

## Main results

* `TauCeti.Comodule.orbitCoordinates_eq_lift_symmetricAlgebraCoact`: orbit coordinates expressed
  through the contragredient symmetric-algebra coaction and the antipode.
* `TauCeti.Comodule.orbitCoordinates_of_mem_coinvariants`: coinvariant polynomials have scalar orbit
  coordinates.
* `TauCeti.Comodule.lift_eval_basePointsRepresentation_of_mem_coinvariants`: coinvariant polynomials
  are invariant on rational orbits.
* `TauCeti.Comodule.VectorOrbit.lift_eval_eq_of_mk_le_mk`: coinvariant polynomials are constant on
  orbit closures.

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

attribute [local instance] prodTrivial dual ComoduleAlgebra.symmetricAlgebra

private theorem lift_comp_ι_mem_homogeneousSubmodule {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)
    {n : ℕ} {s : SymmetricAlgebra R M}
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n) :
    SymmetricAlgebra.lift (SymmetricAlgebra.ι R N ∘ₗ f) s ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R N n := by
  induction hs using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y _ _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x _ ih =>
    obtain ⟨y, rfl⟩ := hm
    rw [map_mul, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
      TauCeti.SymmetricAlgebra.homogeneousSubmodule, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (f y)) ih

namespace VectorOrbit

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

omit [IsAlgClosed k] [Algebra.FiniteType k H] [Module.Finite k M] in
private theorem orbitCoordinates_mk_one_comp_lift_fst (v : M) :
    (orbitCoordinates (H := H) ((v, 1) : M × k)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι k (Module.Dual k (M × k)) ∘ₗ (LinearMap.fst k M k).dualMap)) =
      orbitCoordinates (H := H) v := by
  ext φ
  simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.comp_apply, SymmetricAlgebra.lift_ι_apply, orbitCoordinates_ι,
    matrixCoefficient_prodTrivial]
  have hzero : ((LinearMap.fst k M k).dualMap φ) (0, 1) = 0 := by simp
  have hf : (LinearMap.fst k M k).dualMap φ ∘ₗ LinearMap.inl k M k = φ := by ext; simp
  rw [hzero, map_zero, add_zero, hf]

/-- A homogeneous coinvariant polynomial takes the same value at `w` and `v` whenever
`VectorOrbit.mk w ≤ VectorOrbit.mk v`. -/
private theorem lift_eval_eq_of_mk_le_mk_of_mem_homogeneousSubmodule {v w : M}
    (h : (mk w : VectorOrbit k H M) ≤ mk v) {n : ℕ}
    {s : SymmetricAlgebra k (Module.Dual k M)}
    (hs : s ∈ TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M) n)
    (hinv : s ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k M))) :
    SymmetricAlgebra.lift (Module.Dual.eval k M w) s =
      SymmetricAlgebra.lift (Module.Dual.eval k M v) s := by
  rcases n with _ | d
  · obtain ⟨r, rfl⟩ : ∃ r : k, algebraMap k (SymmetricAlgebra k (Module.Dual k M)) r = s :=
      ⟨TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv k (Module.Dual k M) ⟨s, hs⟩,
        TauCeti.SymmetricAlgebra.algebraMap_homogeneousSubmoduleZeroEquiv_apply _ _ _⟩
    simp
  · -- Homogenize `s - s(v)` against the trivial projective coordinate `t` on `M × k`.
    let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (M × k))
    let F := SymmetricAlgebra.lift
      (SymmetricAlgebra.ι k (Module.Dual k (M × k)) ∘ₗ (LinearMap.fst k M k).dualMap)
    let t : SymmetricAlgebra k (Module.Dual k (M × k)) :=
      SymmetricAlgebra.ι k (Module.Dual k (M × k)) (LinearMap.snd k M k)
    let P : SymmetricAlgebra k (Module.Dual k (M × k)) :=
      F s - SymmetricAlgebra.lift (Module.Dual.eval k M v) s • t ^ (d + 1)
    have hP : P ∈ 𝒜 (d + 1) :=
      sub_mem (lift_comp_ι_mem_homogeneousSubmodule _ hs)
        (Submodule.smul_mem _ _
          (Submodule.pow_mem_pow _ (LinearMap.mem_range_self _ (LinearMap.snd k M k)) (d + 1)))
    have hcoord : orbitCoordinates (H := H) ((v, 1) : M × k) P = 0 := by
      have hs_coord := DFunLike.congr_fun (orbitCoordinates_mk_one_comp_lift_fst (H := H) v) s
      rw [AlgHom.comp_apply, orbitCoordinates_of_mem_coinvariants v hinv] at hs_coord
      simp [P, F, t, hs_coord, matrixCoefficient_prodTrivial, Algebra.algebraMap_eq_smul_one]
    have hcl := mk_le_mk_iff.mp h
    have h1 : (1 : WithConv (H →ₐ[k] k)).ofConv = Bialgebra.counitAlgHom k H := by
      ext; simp [AlgHom.convOne_def]
    rw [← h1] at hcl
    change projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
        (AlgHom.kernelPoint (1 : WithConv (H →ₐ[k] k)).ofConv) ∈
      closure (Set.range (projectiveOrbitMap (H := H) ((v, 1) : M × k)
        (Module.isUnimodular_mk_one v)) : Set (ProjectiveSpectrum 𝒜)) at hcl
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hcl
    have hP_mem : P ∈ (projectiveOrbitMap (H := H) ((w, 1) : M × k) (Module.isUnimodular_mk_one w)
        (AlgHom.kernelPoint (1 : WithConv (H →ₐ[k] k)).ofConv)).asHomogeneousIdeal :=
      hcl ((ProjectiveSpectrum.mem_vanishingIdeal _ _).mpr fun _ ⟨x, hx⟩ ↦
        hx ▸ (mem_projectiveOrbitMap_iff _ _ x d.succ_pos hP).mpr (by simp [hcoord]))
    have heval := (mem_projectiveOrbitMap_kernelPoint_iff ((w, 1) : M × k)
      (Module.isUnimodular_mk_one w) 1 hP).mp hP_mem
    have hmap_eval : (SymmetricAlgebra.lift (Module.Dual.eval k (M × k) (w, 1))).comp F =
        SymmetricAlgebra.lift (Module.Dual.eval k M w) := by ext; simp [F]
    have hw := DFunLike.congr_fun hmap_eval s
    rw [AlgHom.comp_apply] at hw
    simpa [P, t, hw, sub_eq_zero] using heval

/-- **Coinvariant polynomials are constant on orbit closures.** Over an algebraically closed field,
if the rational orbit of `w` lies in the closure of the rational orbit of `v`, then every
`H`-coinvariant polynomial function on `M` takes the same value at `w` and at `v`. -/
theorem lift_eval_eq_of_mk_le_mk {v w : M} (h : (mk w : VectorOrbit k H M) ≤ mk v)
    {p : SymmetricAlgebra k (Module.Dual k M)}
    (hp : p ∈ ComoduleAlgebra.coinvariants k H (SymmetricAlgebra k (Module.Dual k M))) :
    SymmetricAlgebra.lift (Module.Dual.eval k M w) p =
      SymmetricAlgebra.lift (Module.Dual.eval k M v) p := by
  classical
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)
  rw [← DirectSum.sum_support_decompose 𝒜 p, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  exact lift_eval_eq_of_mk_le_mk_of_mem_homogeneousSubmodule h (SetLike.coe_mem _)
    (ComoduleAlgebra.decompose_mem_coinvariants_symmetricAlgebra hp n)

end VectorOrbit

end Closure

end TauCeti.Comodule
