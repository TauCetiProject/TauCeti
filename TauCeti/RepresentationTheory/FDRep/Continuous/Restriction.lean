/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.CategoryTheory.Action.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Subcategory
public import TauCeti.RepresentationTheory.FDRep.Continuous

/-!
# Restriction of continuous finite-dimensional representations along continuous homomorphisms

Let `φ : G →ₜ* H` be a continuous homomorphism of topological monoids and `k` a topological field.
Restricting a finite-dimensional representation of `H` along `φ` keeps its matrix coefficients
continuous, since they are the matrix coefficients of the original representation precomposed with
`φ` (`FDRep.isContinuous_res`). So restriction along `φ` is a functor
`TauCeti.ContFDRep.res k φ : ContFDRep k H ⥤ ContFDRep k G` between the categories of continuous
finite-dimensional representations. Like restriction of all finite-dimensional representations, it
is additive and monoidal, with the comparison isomorphisms of `CategoryTheory.Action.res`.

## Main definitions

* `TauCeti.ContFDRep.res`: restriction of continuous finite-dimensional representations along a
  continuous homomorphism.

## Main statements

* `FDRep.isContinuous_res`: the restriction of a continuous representation along a continuous
  homomorphism is continuous.

## References

* G. Segal, *Equivariant K-theory*, Publ. Math. IHÉS 34 (1968), §2, for continuous
  representations of a compact group and their restrictions.
-/

public section

open CategoryTheory

universe u v v'

namespace FDRep

variable {k : Type u} [Field k] [TopologicalSpace k] {G : Type v} {H : Type v'} [Monoid G]
  [TopologicalSpace G] [Monoid H] [TopologicalSpace H]

/-- **The restriction of a continuous representation along a continuous homomorphism is
continuous**: its matrix coefficients are those of the original representation precomposed with
the homomorphism. -/
theorem isContinuous_res {φ : G →* H} (hφ : Continuous φ) {V : FDRep k H}
    (hV : isContinuous k H V) : isContinuous k G ((Action.res (FGModuleCat.{u} k) φ).obj V) :=
  isContinuous_iff.2 fun f v ↦ (isContinuous_iff.1 hV f v).comp hφ

end FDRep

namespace TauCeti

variable (k : Type u) [Field k] [TopologicalSpace k] {G : Type v} {H : Type v'}
  [Monoid G] [TopologicalSpace G] [Monoid H] [TopologicalSpace H]

/-- **Restriction of continuous finite-dimensional representations** along a continuous
homomorphism `φ : G →ₜ* H`: Mathlib's restriction functor `CategoryTheory.Action.res` along `φ`,
lifted to the categories of continuous representations by `FDRep.isContinuous_res`. -/
noncomputable def ContFDRep.res (φ : G →ₜ* H) : ContFDRep k H ⥤ ContFDRep k G :=
  (FDRep.isContinuous k G).lift
    ((FDRep.isContinuous k H).ι ⋙ Action.res (FGModuleCat.{u} k) φ.toMonoidHom)
    fun V ↦ FDRep.isContinuous_res φ.continuous V.property

variable {k}

/-- The underlying representation of a restricted continuous representation is the restriction of
the underlying representation. -/
@[simp]
theorem ContFDRep.res_obj_obj (φ : G →ₜ* H) (V : ContFDRep k H) :
    ((ContFDRep.res k φ).obj V).obj = (Action.res (FGModuleCat.{u} k) φ.toMonoidHom).obj V.obj :=
  (rfl)

variable [ContinuousAdd k]

/-- Restriction of continuous representations is additive. -/
instance (φ : G →ₜ* H) : (ContFDRep.res k φ).Additive :=
  inferInstanceAs ((FDRep.isContinuous k G).lift
    ((FDRep.isContinuous k H).ι ⋙ Action.res (FGModuleCat.{u} k) φ.toMonoidHom)
    fun V ↦ FDRep.isContinuous_res φ.continuous V.property).Additive

variable [ContinuousMul k]

/-- Restriction of continuous representations is monoidal, with the comparison isomorphisms of
`CategoryTheory.Action.res`. -/
noncomputable instance (φ : G →ₜ* H) : (ContFDRep.res k φ).Monoidal :=
  inferInstanceAs ((FDRep.isContinuous k G).lift
    ((FDRep.isContinuous k H).ι ⋙ Action.res (FGModuleCat.{u} k) φ.toMonoidHom)
    fun V ↦ FDRep.isContinuous_res φ.continuous V.property).Monoidal

end TauCeti
