/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Basic
public import TauCeti.RingTheory.Spectrum.Prime.Action
public import TauCeti.Topology.Connected.Components.Action
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Galois action on geometric component groups

For a finite-type affine group over a field `k`, take the connected components after
extension to `k̄`. The absolute Galois group acts through the scalar factor of its coordinate
ring. This action preserves the component-group multiplication, and the surjection from
geometric points to components is equivariant for postcomposition on points.

The action is continuous for the discrete quotient topology: a finite set of algebra
generators of the coordinate ring has values with a common open Galois stabilizer.
Group homomorphisms induce equivariant homomorphisms on geometric component groups.
These finite groups with Galois action are the geometric data for descending the component
group from an algebraic closure to the ground field. Smoothness and reducedness are not
required.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5 (the group of connected components).
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6.7 and 16.

The construction uses `ScalarAut.instMulSemiringAction`, the action of automorphisms on
`PrimeSpectrum`, and `rationalComponentMap` over the algebraic closure.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct Pointwise

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- The finite group of geometric connected components of a finite-type affine group. -/
noncomputable abbrev geometricComponentGroup (H : FiniteTypeCommHopfAlgCat.{u, u} k) :=
  ConnectedComponents (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))

/-- The geometric component group has the component-group structure over the algebraic closure.
The explicit instance retains the bundled coordinate algebra needed by that construction. -/
noncomputable instance (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Group (geometricComponentGroup H) :=
  instGroupConnectedComponents (baseChange (K := AlgebraicClosure k) H)

/-- There are finitely many geometric connected components. -/
instance (H : FiniteTypeCommHopfAlgCat.{u, u} k) : Finite (geometricComponentGroup H) :=
  instFiniteConnectedComponents (baseChange (K := AlgebraicClosure k) H)

/-- Send a geometric point to the component of its associated rational point after base change.
-/
noncomputable def geometricComponentMap (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    WithConv (H →ₐ[k] AlgebraicClosure k) →* geometricComponentGroup H :=
  (rationalComponentMap (baseChange (K := AlgebraicClosure k) H)).comp
    (AlgHom.baseChangePointsMulEquiv (K := AlgebraicClosure k)).toMonoidHom

/-- On geometric points the component map is the rational component map after the usual
base-change adjunction. Use with `rw` to retain the geometric-point API under `simp`. -/
theorem geometricComponentMap_apply (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : WithConv (H →ₐ[k] AlgebraicClosure k)) :
    geometricComponentMap H g =
      rationalComponentMap (baseChange (K := AlgebraicClosure k) H)
        (AlgHom.baseChangePointsMulEquiv (K := AlgebraicClosure k) g) := (rfl)

/-- Every geometric component contains a geometric point. -/
theorem geometricComponentMap_surjective (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Function.Surjective (geometricComponentMap H) :=
  (rationalComponentMap_surjective _).comp
    AlgHom.baseChangePointsMulEquiv.surjective

/-- Applying a Galois automorphism to a geometric point moves its component by the action
induced from the scalar factor of the coordinate ring. -/
@[simp↓]
theorem geometricComponentMap_mapValue (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (σ : Field.absoluteGaloisGroup k) (g : WithConv (H →ₐ[k] AlgebraicClosure k)) :
    geometricComponentMap H
        (AlgHom.mapValue (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ).toAlgHom g) =
      σ • geometricComponentMap H g := by
  let e := AlgHom.baseChangePointsMulEquiv (k := k) (K := AlgebraicClosure k)
    (A := H) (R := AlgebraicClosure k)
  let τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := σ
  have heval (x : AlgebraicClosure k ⊗[k] H) :
      (e (AlgHom.mapValue τ.toAlgHom g)).ofConv x =
        τ ((e g).ofConv (σ⁻¹ • x)) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul a h =>
      -- The absolute-Galois wrapper uses the existing scalar-factor action on tensors.
      change _ = τ ((e g).ofConv (τ⁻¹ • (a ⊗ₜ[k] h)))
      simp [e, ScalarAut.smul_tmul, AlgHom.mapValue_apply, smul_eq_mul]
  rw [geometricComponentMap_apply, geometricComponentMap_apply,
    rationalComponentMap_apply, rationalComponentMap_apply, ConnectedComponents.smul_mk]
  apply congrArg ConnectedComponents.mk
  apply PrimeSpectrum.ext
  ext x
  rw [PrimeSpectrum.asIdeal_smul, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [rationalKernelPoint, AlgHom.kernelPoint_asIdeal, RingHom.mem_ker]
  -- Kernel points are scheme points in their defining API. Their ideals and the
  -- scalar action here are on the underlying tensor-product ring.
  change (e (AlgHom.mapValue τ.toAlgHom g)).ofConv x = 0 ↔
    (e g).ofConv (σ⁻¹ • (x : AlgebraicClosure k ⊗[k] H)) = 0
  rw [heval]
  exact τ.map_eq_zero_iff

/-- Galois symmetries preserve the group structure on geometric connected components. -/
noncomputable instance (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    MulDistribMulAction (Field.absoluteGaloisGroup k) (geometricComponentGroup H) where
  smul_one σ := by
    rw [← map_one (geometricComponentMap H), ← geometricComponentMap_mapValue, map_one,
      map_one]
  smul_mul σ x y := by
    obtain ⟨g, rfl⟩ := geometricComponentMap_surjective H x
    obtain ⟨h, rfl⟩ := geometricComponentMap_surjective H y
    rw [← map_mul, ← geometricComponentMap_mapValue, map_mul, map_mul,
      geometricComponentMap_mapValue, geometricComponentMap_mapValue]

/-- Every geometric component has an open stabilizer for the Krull topology. -/
theorem isOpen_stabilizer_geometricComponent (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : geometricComponentGroup H) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) := by
  obtain ⟨g, rfl⟩ := geometricComponentMap_surjective H x
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := H)
  let U : Subgroup (Field.absoluteGaloisGroup k) :=
    ⨅ a : s, MulAction.stabilizer (Field.absoluteGaloisGroup k) (g.ofConv a)
  have hU : IsOpen (U : Set (Field.absoluteGaloisGroup k)) := by
    rw [Subgroup.coe_iInf]
    apply isOpen_iInter_of_finite
    intro a
    exact stabilizer_isOpen_of_isIntegral (g.ofConv a)
  apply Subgroup.isOpen_mono (H₁ := U) (H₂ :=
    MulAction.stabilizer (Field.absoluteGaloisGroup k) (geometricComponentMap H g)) ?_ hU
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff, ← geometricComponentMap_mapValue]
  apply congrArg (geometricComponentMap H)
  apply WithConv.ext
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro a ha
  have hfix := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_iInf.mp hσ ⟨a, ha⟩)
  -- The absolute-Galois wrapper's transported action is the algebra-equivalence action.
  change (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) • g.ofConv a =
    g.ofConv a at hfix
  rw [AlgEquiv.smul_def] at hfix
  simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  -- Keep the underlying algebra equivalence explicit across the opaque group wrapper.
  change (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) (g.ofConv a) = g.ofConv a
  exact hfix

/-- The absolute-Galois action on geometric components is continuous. -/
instance (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ContinuousSMul (Field.absoluteGaloisGroup k) (geometricComponentGroup H) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (isOpen_stabilizer_geometricComponent H)

/-- A group homomorphism over the ground field induces a homomorphism of geometric
component groups, contravariantly in the coordinate algebras. -/
noncomputable def mapGeometricComponentGroup {H L : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ L) : geometricComponentGroup L →* geometricComponentGroup H :=
  mapComponentGroup ((baseChangeFunctor (K := AlgebraicClosure k)).map f)

/-- The map on geometric components agrees with precomposition on geometric points. -/
@[simp]
theorem mapGeometricComponentGroup_geometricComponentMap
    {H L : FiniteTypeCommHopfAlgCat.{u, u} k} (f : H ⟶ L)
    (g : WithConv (L →ₐ[k] AlgebraicClosure k)) :
    mapGeometricComponentGroup f (geometricComponentMap L g) =
      geometricComponentMap H (BialgHom.mapDomain f.hom.hom g) := by
  rw [mapGeometricComponentGroup, geometricComponentMap_apply,
    mapComponentGroup_rationalComponentMap, geometricComponentMap_apply]
  exact congrArg (rationalComponentMap (baseChange (K := AlgebraicClosure k) H))
    (BialgHom.baseChangePointsMulEquiv_mapDomain f.hom.hom g).symm

/-- Homomorphisms over the ground field induce Galois-equivariant maps on geometric
component groups. -/
@[simp]
theorem mapGeometricComponentGroup_smul
    {H L : FiniteTypeCommHopfAlgCat.{u, u} k} (f : H ⟶ L)
    (σ : Field.absoluteGaloisGroup k) (x : geometricComponentGroup L) :
    mapGeometricComponentGroup f (σ • x) = σ • mapGeometricComponentGroup f x := by
  obtain ⟨g, rfl⟩ := geometricComponentMap_surjective L x
  rw [← geometricComponentMap_mapValue, mapGeometricComponentGroup_geometricComponentMap,
    mapGeometricComponentGroup_geometricComponentMap, ← geometricComponentMap_mapValue]
  exact congrArg (geometricComponentMap H)
    (DFunLike.congr_fun (BialgHom.mapValue_mapDomain f.hom.hom
      (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ).toAlgHom) g)

/-- The identity homomorphism induces the identity on geometric component groups. -/
@[simp]
theorem mapGeometricComponentGroup_id (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    mapGeometricComponentGroup (𝟙 H) = MonoidHom.id (geometricComponentGroup H) := by
  unfold mapGeometricComponentGroup
  rw [(baseChangeFunctor (K := AlgebraicClosure k)).map_id, mapComponentGroup_id]

/-- Composition induces reverse composition on geometric component groups. -/
@[simp]
theorem mapGeometricComponentGroup_comp {H L M : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ L) (g : L ⟶ M) :
    mapGeometricComponentGroup (f ≫ g) =
      (mapGeometricComponentGroup f).comp (mapGeometricComponentGroup g) := by
  unfold mapGeometricComponentGroup
  rw [(baseChangeFunctor (K := AlgebraicClosure k)).map_comp, mapComponentGroup_comp]

end TauCeti.FiniteTypeCommHopfAlgCat
