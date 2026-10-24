/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.Dual
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule

/-!
# The Killing identification of `S(L)` with the polynomial functions on `L`

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ` is
nondegenerate. The Killing form is invariant, `κ ⁅x, y⁆ z = -κ y ⁅x, z⁆`, so `x ↦ κ x` is an
equivalence of Lie modules from the adjoint module `L` to the coadjoint module `L*`. It induces an
algebra equivalence from the symmetric algebra `S(L)` to the algebra `S(L*)` of polynomial
functions on `L`, sending a generator `x` to the linear function `κ x`, and this equivalence
intertwines the adjoint action of `L` on `S(L)` with the coadjoint action on `S(L*)`. Hence it
carries the adjoint invariants `S(L)^L` onto the invariant polynomial functions `S(L*)^L`.

This is the identification under which polynomial functions on `L`, such as the trace
polynomials `x ↦ tr (ρ(x) ^ m)` of a representation `ρ`, are compared with the leading symbols of
central elements of the enveloping algebra, which live in `S(L)^L`, in the proof of the
Harish-Chandra isomorphism by Chevalley's restriction theorem.

## Main definitions

* `TauCeti.killingDuality`: the Killing form as a Lie module equivalence `L ≃ L*`.
* `TauCeti.killingSymmetricEquiv`: the induced algebra equivalence `S(L) ≃ S(L*)`.

## Main results

* `TauCeti.killingSymmetricEquiv_ι`: a generator `x` goes to the linear function `κ x`.
* `TauCeti.killingSymmetricEquiv_symm_ι`: conversely, a linear function `f` goes back to the
  generator `x` with `κ x = f`.
* `TauCeti.killingSymmetricEquiv_lieModuleDerivation`: the equivalence intertwines the adjoint
  action on `S(L)` with the coadjoint action on `S(L*)`.
* `TauCeti.map_killingSymmetricEquiv_lieInvariants`: it carries the invariants `S(L)^L` onto the
  invariant polynomial functions `S(L*)^L`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1 and
  §23.3.
* J. Dixmier, *Enveloping Algebras*, §7.3.
-/

public section

namespace TauCeti

open LieAlgebra Module _root_.SymmetricAlgebra TauCeti.SymmetricAlgebra

variable (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L]

/-- The **Killing duality** of a Lie algebra with nondegenerate Killing form `κ`: the equivalence
`x ↦ κ x` of the adjoint module `L` with the coadjoint module `L*`. -/
noncomputable def killingDuality : L ≃ₗ⁅K,L⁆ Dual K L :=
  (killingForm K L).lieModuleEquivDual (IsKilling.killingForm_nondegenerate K L)
    (LieModule.traceForm_lieInvariant K L L)

/-- The Killing duality sends `x` to the linear form `y ↦ κ(x, y)`. -/
@[simp]
theorem killingDuality_apply (x y : L) : killingDuality K L x y = killingForm K L x y :=
  LinearMap.BilinForm.lieModuleEquivDual_apply _ _ _ x y

/-- The inverse of the Killing duality sends a linear form `f` to the element `x` with
`κ(x, y) = f y` for all `y`. -/
@[simp]
theorem killingForm_killingDuality_symm_apply (f : Dual K L) (y : L) :
    killingForm K L ((killingDuality K L).symm f) y = f y :=
  LinearMap.BilinForm.apply_lieModuleEquivDual_symm_apply _ _ _ f y

/-- The linear map underlying the Killing duality is the Killing form, read as a linear map
`L → L*`. -/
theorem toLinearMap_killingDuality :
    ((killingDuality K L : L ≃ₗ[K] Dual K L) : L →ₗ[K] Dual K L) = killingForm K L :=
  LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ killingDuality_apply K L x y

/-- The algebra equivalence of the symmetric algebra `S(L)` with the algebra `S(L*)` of polynomial
functions on `L` induced by the Killing duality. -/
noncomputable def killingSymmetricEquiv :
    SymmetricAlgebra K L ≃ₐ[K] SymmetricAlgebra K (Dual K L) :=
  mapEquiv K (killingDuality K L : L ≃ₗ[K] Dual K L)

/-- The Killing equivalence `S(L) ≃ S(L*)` is the symmetric-algebra map of the Killing form,
read as a linear map `L → L*`. -/
theorem killingSymmetricEquiv_apply (p : SymmetricAlgebra K L) :
    killingSymmetricEquiv K L p = map K (killingForm K L) p := by
  rw [killingSymmetricEquiv, mapEquiv_apply, toLinearMap_killingDuality]

/-- The Killing equivalence `S(L) ≃ S(L*)` sends a generator `x` to the linear function `κ x`. -/
@[simp]
theorem killingSymmetricEquiv_ι (x : L) :
    killingSymmetricEquiv K L (ι K L x) = ι K (Dual K L) (killingForm K L x) := by
  rw [killingSymmetricEquiv_apply, map_apply_ι]

/-- The inverse of the Killing equivalence `S(L) ≃ S(L*)` is the symmetric-algebra equivalence
induced by the inverse of the Killing duality. -/
theorem killingSymmetricEquiv_symm :
    (killingSymmetricEquiv K L).symm =
      mapEquiv K ((killingDuality K L).symm : Dual K L ≃ₗ[K] L) := by
  rw [killingSymmetricEquiv, mapEquiv_symm]
  exact congrArg (mapEquiv K) <|
    LinearEquiv.ext fun f ↦ (killingDuality K L : L ≃ₗ[K] Dual K L).injective (by simp)

/-- The inverse of the Killing equivalence `S(L) ≃ S(L*)` sends a linear function `f` to the
generator `x` with `κ x = f`. -/
@[simp]
theorem killingSymmetricEquiv_symm_ι (f : Dual K L) :
    (killingSymmetricEquiv K L).symm (ι K (Dual K L) f) = ι K L ((killingDuality K L).symm f) := by
  rw [killingSymmetricEquiv_symm, mapEquiv_ι, LieModuleEquiv.coe_toLinearEquiv]

/-- **The Killing equivalence intertwines the adjoint and coadjoint actions**: it carries the
adjoint derivation of `x` on `S(L)` to the coadjoint derivation of `x` on `S(L*)`. -/
theorem killingSymmetricEquiv_lieModuleDerivation (x : L) (p : SymmetricAlgebra K L) :
    killingSymmetricEquiv K L (lieModuleDerivation K L L x p) =
      lieModuleDerivation K L (Dual K L) x (killingSymmetricEquiv K L p) := by
  rw [killingSymmetricEquiv, mapEquiv_apply, mapEquiv_apply]
  exact (killingDuality K L).map_apply_lieModuleDerivation x p

/-- An element of `S(L)` is invariant exactly when its image in `S(L*)` under the Killing
equivalence is an invariant polynomial function. -/
@[simp]
theorem killingSymmetricEquiv_mem_lieInvariants_iff {p : SymmetricAlgebra K L} :
    killingSymmetricEquiv K L p ∈ lieInvariants K L (Dual K L) ↔ p ∈ lieInvariants K L L := by
  rw [killingSymmetricEquiv, mapEquiv_apply]
  exact (killingDuality K L).map_mem_lieInvariants_iff

/-- **The Killing equivalence identifies the invariants**: it carries `S(L)^L` onto the invariant
polynomial functions `S(L*)^L`. -/
theorem map_killingSymmetricEquiv_lieInvariants :
    (lieInvariants K L L).map
        (killingSymmetricEquiv K L : SymmetricAlgebra K L →ₐ[K] SymmetricAlgebra K (Dual K L)) =
      lieInvariants K L (Dual K L) := by
  rw [killingSymmetricEquiv, ← (killingDuality K L).map_lieInvariants, ← mapEquiv_toAlgHom]

end TauCeti
