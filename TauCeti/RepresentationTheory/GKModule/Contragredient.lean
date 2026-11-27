/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GKModule.Hom

/-!
# Contragredients of `(𝔤, K)`-modules

Let `K` be a group acting on a finite-dimensional Lie algebra `𝔤` by Lie algebra automorphisms
through `Ad`, and `M` a `(𝔤, K)`-module on `V`. The algebraic dual `Dual k V` is a `𝔤`-module
(`⁅x, f⁆ = -f ∘ ⁅x, ·⁆`) and a representation of `K` (`Representation.dual`), and the two actions
are covariant, but a linear form need not be `K`-finite. The **contragredient** `M^∨` is the
`K`-finite part of `Dual k V`: it is stable under `𝔤` because `𝔤` is finite-dimensional, since
`g • ⁅x, f⁆ = ⁅Ad g x, g • f⁆` lies in the span of the brackets of a basis of `𝔤` with the orbit
of `f`.

A morphism `φ : M → N` of `(𝔤, K)`-modules (`TauCeti.GKModule.Hom`) has a transpose
`φ^∨ : N^∨ → M^∨`, and transposition is contravariantly functorial.

## Main definitions

* `TauCeti.GKModule.contragredientSubmodule M`: the `K`-finite linear forms, a Lie submodule of
  `Dual k V`.
* `TauCeti.GKModule.contragredient M`: the contragredient `(𝔤, K)`-module `M^∨`.
* `TauCeti.GKModule.Hom.dualMap φ`: the transpose `N^∨ → M^∨` of a morphism `φ : M → N`.

## Main statements

* `TauCeti.GKModule.dual_lie`: the dual actions of `K` and `𝔤` are covariant.
* `TauCeti.GKModule.contragredientSubmodule_eq_top`: for finite-dimensional `V` the contragredient
  is the whole dual.
* `TauCeti.GKModule.Hom.dualMap_id`, `TauCeti.GKModule.Hom.dualMap_comp`: transposition is a
  contravariant functor.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
-/

public section

namespace TauCeti

open Representation Module

variable {k 𝔤 K : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Group K]
  {Ad : Representation k K 𝔤} [IsLieAction Ad]
  {V : Type*} [AddCommGroup V] [Module k V] [LieRingModule 𝔤 V] [LieModule k 𝔤 V]
  {W : Type*} [AddCommGroup W] [Module k W] [LieRingModule 𝔤 W] [LieModule k 𝔤 W]
  {U : Type*} [AddCommGroup U] [Module k U] [LieRingModule 𝔤 U] [LieModule k 𝔤 U]

namespace GKModule

/-! ### The contragredient -/

variable (M : GKModule Ad V)

/-- **Covariance of the dual actions.** For the dual actions of `K` and `𝔤` on `Dual k V`,
`g • ⁅x, f⁆ = ⁅Ad g x, g • f⁆`. -/
theorem dual_lie (g : K) (x : 𝔤) (f : Dual k V) :
    M.ρ.dual g ⁅x, f⁆ = ⁅Ad g x, M.ρ.dual g f⁆ := by
  ext v
  simp only [dual_apply, Dual.transpose_apply, LinearMap.coe_comp, Function.comp_apply,
    Module.Dual.lie_apply, M.map_lie, inv_self_apply]

/-- The `K`-finite linear forms on `V`, a Lie submodule of `Dual k V` when `𝔤` is
finite-dimensional: by covariance (`dual_lie`) they are stable under `𝔤`
(`Representation.IsGFinite.lie`). -/
def contragredientSubmodule [FiniteDimensional k 𝔤] : LieSubmodule k 𝔤 (Dual k V) where
  toSubmodule := M.ρ.dual.gFiniteSubrepresentation.toSubmodule
  lie_mem {x _} hf := M.ρ.dual.mem_gFiniteSubrepresentation.2
    ((M.ρ.dual.mem_gFiniteSubrepresentation.1 hf).lie M.dual_lie x)

@[simp]
theorem mem_contragredientSubmodule [FiniteDimensional k 𝔤] {f : Dual k V} :
    f ∈ M.contragredientSubmodule ↔ M.ρ.dual.IsGFinite f :=
  M.ρ.dual.mem_gFiniteSubrepresentation

/-- For a finite-dimensional `V`, every linear form is `K`-finite, so the contragredient is the
whole dual. -/
theorem contragredientSubmodule_eq_top [FiniteDimensional k 𝔤] [FiniteDimensional k V] :
    M.contragredientSubmodule = ⊤ :=
  LieSubmodule.toSubmodule_injective
    (M.ρ.dual.toSubmodule_gFiniteSubrepresentation.trans M.ρ.dual.gFiniteSubmodule_eq_top)

/-- **The contragredient `(𝔤, K)`-module** `M^∨`: the `K`-finite linear forms on `V`, with the
dual actions of `𝔤` and `K`. -/
def contragredient [FiniteDimensional k 𝔤] : GKModule Ad M.contragredientSubmodule where
  ρ := M.ρ.dual.gFiniteSubrepresentation.toRepresentation
  map_lie g x f := Subtype.ext (M.dual_lie g x f)
  isGFinite := M.ρ.dual.isGFinite_gFiniteSubrepresentation

@[simp]
theorem contragredient_ρ_apply_coe [FiniteDimensional k 𝔤] (g : K)
    (f : M.contragredientSubmodule) :
    ((M.contragredient.ρ g f : M.contragredientSubmodule) : Dual k V) = M.ρ.dual g f :=
  (rfl)

namespace Hom

variable [FiniteDimensional k 𝔤] {M} {N : GKModule Ad W} {P : GKModule Ad U}

/-- The transpose `N^∨ → M^∨` of a morphism `φ : M → N`, `f ↦ f ∘ φ`. -/
def dualMap (φ : Hom M N) : Hom N.contragredient M.contragredient where
  toFun f := ⟨φ.toIntertwiningMap.dualMap (f : Dual k W),
    M.mem_contragredientSubmodule.2
      ((N.mem_contragredientSubmodule.1 f.prop).map φ.toIntertwiningMap.dualMap)⟩
  map_add' f f' := Subtype.ext (map_add φ.toIntertwiningMap.dualMap (f : Dual k W) f')
  map_smul' c f := Subtype.ext (map_smul φ.toIntertwiningMap.dualMap c (f : Dual k W))
  map_lie' {x f} := Subtype.ext <| LinearMap.ext fun v ↦ by
    simp
  map_ρ g f := Subtype.ext (IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap.dualMap g f)

@[simp]
theorem coe_dualMap_apply (φ : Hom M N) (f : N.contragredientSubmodule) (v : V) :
    (φ.dualMap f : Dual k V) v = (f : Dual k W) (φ v) :=
  (φ.toIntertwiningMap.dualMap_apply_apply f v).trans (by rw [coe_toIntertwiningMap])

@[simp]
theorem dualMap_id : (id M).dualMap = id M.contragredient :=
  ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

@[simp]
theorem dualMap_comp (ψ : Hom N P) (φ : Hom M N) : (ψ.comp φ).dualMap = φ.dualMap.comp ψ.dualMap :=
  ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

end Hom

end GKModule

end TauCeti
