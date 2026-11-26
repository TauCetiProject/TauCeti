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
* `TauCeti.GKModule.isGFinite_dual_lie`: a `K`-finite linear form stays `K`-finite under `𝔤`.
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

/-- **The `K`-finite linear forms are stable under `𝔤`.** For a finite-dimensional `𝔤`, if `f`
is `K`-finite then so is `⁅x, f⁆`: its orbit lies in the span of the brackets of a basis of `𝔤`
with the orbit of `f`. -/
theorem isGFinite_dual_lie [FiniteDimensional k 𝔤] {f : Dual k V} (hf : M.ρ.dual.IsGFinite f)
    (x : 𝔤) : M.ρ.dual.IsGFinite ⁅x, f⁆ := by
  have := (isGFinite_iff _ _).1 hf
  let b := Module.finBasis k 𝔤
  let O := Submodule.span k (Set.range fun g : K ↦ M.ρ.dual g f)
  refine IsGFinite.of_forall_apply_mem
    (W := ⨆ j, O.map (LieModule.toEnd k 𝔤 (Dual k V) (b j))) fun g ↦ ?_
  rw [dual_lie, ← b.sum_repr (Ad g x), sum_lie]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [smul_lie]
  exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j
    (Submodule.mem_map_of_mem (Submodule.subset_span ⟨g, rfl⟩)))

/-- The `K`-finite linear forms on `V`, a Lie submodule of `Dual k V` when `𝔤` is
finite-dimensional. -/
def contragredientSubmodule [FiniteDimensional k 𝔤] : LieSubmodule k 𝔤 (Dual k V) where
  toSubmodule := M.ρ.dual.gFiniteSubmodule
  lie_mem {x _} hf :=
    M.ρ.dual.mem_gFiniteSubmodule.2 (M.isGFinite_dual_lie (M.ρ.dual.mem_gFiniteSubmodule.1 hf) x)

@[simp]
theorem mem_contragredientSubmodule [FiniteDimensional k 𝔤] {f : Dual k V} :
    f ∈ M.contragredientSubmodule ↔ M.ρ.dual.IsGFinite f :=
  M.ρ.dual.mem_gFiniteSubmodule

/-- For a finite-dimensional `V`, every linear form is `K`-finite, so the contragredient is the
whole dual. -/
theorem contragredientSubmodule_eq_top [FiniteDimensional k 𝔤] [FiniteDimensional k V] :
    M.contragredientSubmodule = ⊤ :=
  LieSubmodule.toSubmodule_injective M.ρ.dual.gFiniteSubmodule_eq_top

/-- The `K`-finite linear forms, as a subrepresentation of the dual representation. -/
def contragredientSubrepresentation [FiniteDimensional k 𝔤] : Subrepresentation M.ρ.dual where
  toSubmodule := M.contragredientSubmodule.toSubmodule
  apply_mem_toSubmodule g _ hf := apply_mem_gFiniteSubmodule M.ρ.dual hf g

/-- **The contragredient `(𝔤, K)`-module** `M^∨`: the `K`-finite linear forms on `V`, with the
dual actions of `𝔤` and `K`. -/
def contragredient [FiniteDimensional k 𝔤] : GKModule Ad M.contragredientSubmodule where
  ρ := M.contragredientSubrepresentation.toRepresentation
  map_lie g x f := Subtype.ext (M.dual_lie g x f)
  isGFinite f := IsGFinite.of_injective M.contragredientSubrepresentation.subtype
    M.contragredientSubrepresentation.subtype_injective
      (by
        have h := congrFun (Subrepresentation.coe_subtype M.contragredientSubrepresentation) f
        exact h ▸ M.mem_contragredientSubmodule.1 f.prop)

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
  φ.toIntertwiningMap.dualMap_apply_apply f v

@[simp]
theorem dualMap_id : (id M).dualMap = id M.contragredient :=
  ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

@[simp]
theorem dualMap_comp (ψ : Hom N P) (φ : Hom M N) : (ψ.comp φ).dualMap = φ.dualMap.comp ψ.dualMap :=
  ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

end Hom

end GKModule

end TauCeti
