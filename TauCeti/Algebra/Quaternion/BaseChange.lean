/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Base change of quaternion algebras

Extending scalars in a quaternion algebra amounts to applying the algebra map to its three
parameters. The equivalence `TauCeti.QuaternionAlgebra.baseChange` identifies
`S ⊗[R] ℍ[R,a,b,c]` with `ℍ[S,algebraMap R S a,algebraMap R S b,algebraMap R S c]`.
It lets quaternion algebras and their splitting isomorphisms be transported along extensions.
The construction works over arbitrary commutative rings, including in characteristic two.

The formula `baseChange_tmul` sends a pure tensor to the scalar multiple of the coefficientwise
image. The inverse formula `baseChange_symm_mk` expands a quaternion in the basis `1, i, j, k`.
-/

public section

open scoped Quaternion TensorProduct

namespace TauCeti.QuaternionAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Apply a ring homomorphism to the coefficients of a quaternion. -/
def map (a b c : R) (f : R →+* S) :
    ℍ[R,a,b,c] →+* ℍ[S,f a,f b,f c] where
  toFun q := ⟨f q.re, f q.imI, f q.imJ, f q.imK⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

@[simp]
theorem map_mk (a b c : R) (f : R →+* S) (w x y z : R) :
    map a b c f ⟨w, x, y, z⟩ = ⟨f w, f x, f y, f z⟩ := (rfl)

@[simp]
theorem re_map (a b c : R) (f : R →+* S) (q : ℍ[R,a,b,c]) :
    (map a b c f q).re = f q.re := (rfl)

@[simp]
theorem imI_map (a b c : R) (f : R →+* S) (q : ℍ[R,a,b,c]) :
    (map a b c f q).imI = f q.imI := (rfl)

@[simp]
theorem imJ_map (a b c : R) (f : R →+* S) (q : ℍ[R,a,b,c]) :
    (map a b c f q).imJ = f q.imJ := (rfl)

@[simp]
theorem imK_map (a b c : R) (f : R →+* S) (q : ℍ[R,a,b,c]) :
    (map a b c f q).imK = f q.imK := (rfl)

@[simp]
theorem map_star (a b c : R) (f : R →+* S) (q : ℍ[R,a,b,c]) :
    map a b c f (star q) = star (map a b c f q) := by
  ext <;> simp

@[simp]
theorem map_coe (a b c : R) (f : R →+* S) (r : R) :
    map a b c f (r : ℍ[R,a,b,c]) = (f r : ℍ[S,f a,f b,f c]) := by
  ext <;> simp

@[simp]
theorem map_id (a b c : R) :
    map a b c (RingHom.id R) = RingHom.id ℍ[R,a,b,c] := (rfl)

@[simp]
theorem map_comp {T : Type*} [CommRing T] (a b c : R) (f : R →+* S) (g : S →+* T) :
    map a b c (g.comp f) = (map (f a) (f b) (f c) g).comp (map a b c f) := (rfl)

variable (R S) [Algebra R S] (a b c : R)

private noncomputable def baseChangeHom :
    S ⊗[R] ℍ[R,a,b,c] →ₐ[S]
      ℍ[S,algebraMap R S a,algebraMap R S b,algebraMap R S c] := by
  let f : ℍ[R,a,b,c] →ₐ[R]
      ℍ[S,algebraMap R S a,algebraMap R S b,algebraMap R S c] :=
    { map a b c (algebraMap R S) with
      commutes' r := by
        rw [IsScalarTower.algebraMap_apply R S
          ℍ[S,algebraMap R S a,algebraMap R S b,algebraMap R S c]]
        ext <;> simp [_root_.QuaternionAlgebra.algebraMap_eq] }
  exact AlgHom.liftEquiv R S _ _ f

private theorem baseChangeHom_tmul (s : S) (q : ℍ[R,a,b,c]) :
    baseChangeHom R S a b c (s ⊗ₜ[R] q) = s • map a b c (algebraMap R S) q := by
  exact AlgHom.liftEquiv_tmul _ s q

/-- Extending scalars in a quaternion algebra applies the algebra map to its parameters. -/
noncomputable def baseChange :
    S ⊗[R] ℍ[R,a,b,c] ≃ₐ[S]
      ℍ[S,algebraMap R S a,algebraMap R S b,algebraMap R S c] := by
  let g := baseChangeHom R S a b c
  -- The underlying linear equivalence uses Mathlib's `QuaternionAlgebra.linearEquivTuple`
  -- and `TensorProduct.piScalarRight`; `AlgHom.liftEquiv` supplies multiplicativity.
  let e := (LinearEquiv.baseChange R S _ _
      (_root_.QuaternionAlgebra.linearEquivTuple a b c)).trans
    ((TensorProduct.piScalarRight R S S (Fin 4)).trans
      (_root_.QuaternionAlgebra.linearEquivTuple
        (algebraMap R S a) (algebraMap R S b) (algebraMap R S c)).symm)
  have h : g.toLinearMap = e.toLinearMap := by
    ext : 2
    ext <;> simp [g, baseChangeHom_tmul, e, Algebra.smul_def, mul_comm,
      _root_.QuaternionAlgebra.equivTuple]
  have he : (g : _ → _) = e := congrArg DFunLike.coe h
  exact AlgEquiv.ofBijective g (he.symm ▸ e.bijective)

/-- Base change sends a pure tensor to the scalar multiple of the coefficientwise image. -/
@[simp]
theorem baseChange_tmul (s : S) (q : ℍ[R,a,b,c]) :
    baseChange R S a b c (s ⊗ₜ[R] q) = s • map a b c (algebraMap R S) q := by
  exact baseChangeHom_tmul R S a b c s q

/-- The inverse base-change equivalence expands a quaternion in the basis `1, i, j, k`. -/
@[simp]
theorem baseChange_symm_mk (w x y z : S) :
    (baseChange R S a b c).symm ⟨w, x, y, z⟩ =
      w ⊗ₜ[R] (1 : ℍ[R,a,b,c]) + x ⊗ₜ[R] ⟨0, 1, 0, 0⟩ +
        y ⊗ₜ[R] ⟨0, 0, 1, 0⟩ + z ⊗ₜ[R] ⟨0, 0, 0, 1⟩ := by
  apply (baseChange R S a b c).injective
  simp only [AlgEquiv.apply_symm_apply, map_add, baseChange_tmul, map_one, map_mk,
    map_zero]
  ext <;> simp

end TauCeti.QuaternionAlgebra
