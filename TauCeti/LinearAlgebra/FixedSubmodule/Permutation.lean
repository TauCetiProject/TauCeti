/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Perm.Cycle.Factors
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Fixed vectors of coordinate permutations

Functions on the cycle quotient identify linearly with the fixed submodule of
precomposition by a permutation. The underlying bijection is the existing
invariant-colouring equivalence; no enumeration of cycles is needed. The orbit basis
requires only finitely many cycles, even when their elements form an infinite type.

For finitely many coordinates, the orbit mean `Equiv.Perm.orbitMean σ O` rescales the indicator
of a cycle `O` by `|O|⁻¹`. Read as the folded simple root `β_O = |O|⁻¹ ∑_{i ∈ O} αᵢ` of a
diagram automorphism, these vectors are linearly independent
(`Equiv.Perm.linearIndependent_orbitMean`).
-/

public noncomputable section

open Equiv

namespace Equiv.Perm

open LinearEquiv

variable {R M I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Functions on permutation cycles are precisely the fixed vectors of precomposition. -/
def permutationFixedEquiv (σ : Perm I) :
    (Quotient (Perm.SameCycle.setoid σ) → M) ≃ₗ[R]
      (funCongrLeft R M σ).toLinearMap.fixedSubmodule where
  toFun a := ⟨(TauCeti.invariantColouringEquiv σ a).val, by
    apply LinearMap.mem_fixedSubmodule_iff.mpr
    funext i
    simpa only [coe_coe, funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
      using congrFun (TauCeti.invariantColouringEquiv σ a).property i⟩
  invFun v := (TauCeti.invariantColouringEquiv σ).symm ⟨v.val, by
    funext i
    simpa only [coe_coe, funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
      using congrFun (LinearMap.mem_fixedSubmodule_iff.mp v.property) i⟩
  left_inv a := (TauCeti.invariantColouringEquiv σ).symm_apply_apply a
  right_inv v := by
    apply Subtype.ext
    exact congrArg Subtype.val ((TauCeti.invariantColouringEquiv σ).apply_symm_apply _)
  map_add' a b := by
    apply Subtype.ext
    funext i
    simp only [Submodule.coe_add, Pi.add_apply, TauCeti.invariantColouringEquiv_apply_coe]
  map_smul' r a := by
    apply Subtype.ext
    funext i
    simp only [Submodule.coe_smul, Pi.smul_apply, TauCeti.invariantColouringEquiv_apply_coe,
      RingHom.id_apply]

/-- The fixed-vector equivalence reads the coordinate of the containing cycle. -/
@[simp]
theorem permutationFixedEquiv_apply (σ : Perm I)
    (a : Quotient (Perm.SameCycle.setoid σ) → M) (i : I) :
    (permutationFixedEquiv (R := R) (M := M) σ a).val i = a (Quotient.mk _ i) :=
  TauCeti.invariantColouringEquiv_apply_coe σ a i

/-- Inverse coordinates recover every ambient coordinate of a fixed vector. -/
@[simp]
theorem permutationFixedEquiv_symm_apply (σ : Perm I)
    (v : (funCongrLeft R M σ).toLinearMap.fixedSubmodule) (i : I) :
    (permutationFixedEquiv (R := R) (M := M) σ).symm v (Quotient.mk _ i) = v.val i :=
  TauCeti.invariantColouringEquiv_symm_apply σ _ i

/-- The coordinate of a cycle is the value at its chosen representative. -/
theorem permutationFixedEquiv_symm_apply_out (σ : Perm I)
    (v : (funCongrLeft R M σ).toLinearMap.fixedSubmodule)
    (c : Quotient (Perm.SameCycle.setoid σ)) :
    (permutationFixedEquiv (R := R) (M := M) σ).symm v c = v.val c.out := by
  simpa only [Quotient.out_eq] using permutationFixedEquiv_symm_apply σ v c.out

/-- The orbit indicator vectors form a basis of the fixed submodule. -/
def permutationFixedBasis (σ : Perm I)
    [Finite (Quotient (Perm.SameCycle.setoid σ))] :
    Module.Basis (Quotient (Perm.SameCycle.setoid σ)) R
      (funCongrLeft R R σ).toLinearMap.fixedSubmodule :=
  Module.Basis.ofEquivFun (permutationFixedEquiv (R := R) (M := R) σ).symm

/-- A fixed vector's orbit coordinate is its value at any member of that orbit. -/
@[simp]
theorem permutationFixedBasis_repr (σ : Perm I)
    [Finite (Quotient (Perm.SameCycle.setoid σ))]
    (v : (funCongrLeft R R σ).toLinearMap.fixedSubmodule) (i : I) :
    (permutationFixedBasis (R := R) σ).repr v (Quotient.mk _ i) = v.val i := by
  rw [permutationFixedBasis, Module.Basis.ofEquivFun_repr_apply]
  exact permutationFixedEquiv_symm_apply σ v i

/-- An orbit basis vector is the indicator of its cycle, which may be infinite. -/
@[simp]
theorem permutationFixedBasis_apply (σ : Perm I)
    [Finite (Quotient (Perm.SameCycle.setoid σ))]
    [DecidableEq (Quotient (Perm.SameCycle.setoid σ))]
    (c : Quotient (Perm.SameCycle.setoid σ)) (i : I) :
    (permutationFixedBasis (R := R) σ c).val i =
      if Quotient.mk _ i = c then 1 else 0 := by
  have h := permutationFixedBasis_repr σ (permutationFixedBasis (R := R) σ c) i
  simpa only [Module.Basis.repr_self, Finsupp.single_apply, eq_comm] using h.symm

/-- Each basis vector is the literal sum of coordinate vectors in its cycle. -/
theorem permutationFixedBasis_eq_sum [Fintype I] [DecidableEq I] (σ : Perm I)
    [DecidableEq (Quotient (Perm.SameCycle.setoid σ))]
    (c : Quotient (Perm.SameCycle.setoid σ)) :
    (permutationFixedBasis (R := R) σ c).val =
      ∑ i ∈ Finset.univ.filter (fun i ↦ Quotient.mk _ i = c), Pi.single i (1 : R) := by
  ext i
  rw [permutationFixedBasis_apply]
  simp [Finset.sum_apply, Pi.single_apply, eq_comm]

/-- Read one chosen coordinate per cycle, then extend it constantly along that cycle.
A section of the quotient map makes this a retraction; the map depends on that section. -/
def permutationFixedProjection (σ : Perm I)
    (r : Quotient (Perm.SameCycle.setoid σ) → I) :
    (I → M) →ₗ[R] (funCongrLeft R M σ).toLinearMap.fixedSubmodule :=
  (permutationFixedEquiv (R := R) (M := M) σ).toLinearMap.comp (LinearMap.funLeft R M r)

/-- The chosen representative determines every coordinate of the projection. -/
@[simp]
theorem permutationFixedProjection_apply (σ : Perm I)
    (r : Quotient (Perm.SameCycle.setoid σ) → I) (v : I → M) (i : I) :
    (permutationFixedProjection (R := R) σ r v).val i =
      v (r (Quotient.mk _ i)) := by
  simp only [permutationFixedProjection, LinearMap.comp_apply, coe_coe,
    permutationFixedEquiv_apply, LinearMap.funLeft_apply]

/-- A section-based projection fixes every vector in the fixed submodule. -/
@[simp]
theorem permutationFixedProjection_fixed (σ : Perm I)
    (r : Quotient (Perm.SameCycle.setoid σ) → I)
    (hr : Function.RightInverse r (Quotient.mk (Perm.SameCycle.setoid σ)))
    (v : (funCongrLeft R M σ).toLinearMap.fixedSubmodule) :
    permutationFixedProjection (R := R) σ r v.val = v := by
  apply Subtype.ext
  funext i
  rw [permutationFixedProjection_apply,
    ← permutationFixedEquiv_symm_apply σ v (r (Quotient.mk _ i)), hr,
    permutationFixedEquiv_symm_apply]

/-- The section-based projection is a linear retraction of the actual fixed-submodule inclusion. -/
theorem permutationFixedProjection_comp_subtype (σ : Perm I)
    (r : Quotient (Perm.SameCycle.setoid σ) → I)
    (hr : Function.RightInverse r (Quotient.mk (Perm.SameCycle.setoid σ))) :
    (permutationFixedProjection (R := R) (M := M) σ r).comp
      (funCongrLeft R M σ).toLinearMap.fixedSubmodule.subtype = LinearMap.id := by
  ext v i
  exact congrFun (congrArg Subtype.val (permutationFixedProjection_fixed σ r hr v)) i

/-! ### Orbit means -/

section OrbitMean

open _root_.Finset Matrix

variable {I : Type*} [Fintype I] [DecidableEq I] (σ : Perm I)

/-- The folded simple root `β_O = |O|⁻¹ ∑_{i ∈ O} αᵢ` of a `σ`-orbit `O` of vertices: the mean of
the coordinate vectors of the vertices in `O`, as a vector of coordinates in the basis `αᵢ`. -/
def orbitMean (O : Quotient (SameCycle.setoid σ)) : I → ℚ :=
  fun i ↦ if σ.SameCycle i O.out then (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ else 0

theorem orbitMean_apply (O : Quotient (SameCycle.setoid σ)) (i : I) :
    σ.orbitMean O i = if σ.SameCycle i O.out then (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ else 0 :=
  (rfl)

/-- The dot product with a folded simple root is the mean over the orbit. -/
theorem orbitMean_dotProduct (O : Quotient (SameCycle.setoid σ)) (v : I → ℚ) :
    σ.orbitMean O ⬝ᵥ v =
      (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ * ∑ i with σ.SameCycle i O.out, v i := by
  simp [dotProduct, orbitMean_apply, ite_mul, sum_filter, mul_sum]

/-- The dot product with a folded simple root is the mean over the orbit. -/
theorem dotProduct_orbitMean (O : Quotient (SameCycle.setoid σ)) (v : I → ℚ) :
    v ⬝ᵥ σ.orbitMean O =
      (#{j | σ.SameCycle j O.out} : ℚ)⁻¹ * ∑ i with σ.SameCycle i O.out, v i := by
  rw [dotProduct_comm, orbitMean_dotProduct]

/-- **The folded simple roots are linearly independent.** -/
theorem linearIndependent_orbitMean : LinearIndependent ℚ σ.orbitMean :=
  -- The orbits are disjoint and nonempty, so pairing with the coordinate vector of the
  -- representative of `O` only sees `β_O`.
  TauCeti.linearIndependent_of_dotProduct_diagonal (w := fun O ↦ Pi.single O.out 1)
    (c := fun O ↦ (#{j | σ.SameCycle j O.out} : ℚ)⁻¹)
    (fun O ↦ (IsRegular.of_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr
      (σ.card_sameCycle_out_pos O).ne'))).right)
    (fun O ↦ by simp [orbitMean_apply, SameCycle.refl])
    (fun O P hOP ↦ by
      have : ¬σ.SameCycle P.out O.out := fun h ↦
        ne_of_sameCycle_out h (SameCycle.refl σ P.out) hOP rfl
      simp [orbitMean_apply, this])

end OrbitMean

end Equiv.Perm
