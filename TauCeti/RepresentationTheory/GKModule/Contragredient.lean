/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GKModule.Basic

/-!
# Morphisms and contragredients of `(𝔤, K)`-modules

Let `K` be a group acting on a finite-dimensional Lie algebra `𝔤` by Lie algebra automorphisms
through `Ad`, and `M` a `(𝔤, K)`-module on `V`. The algebraic dual `Dual k V` is a `𝔤`-module
(`⁅x, f⁆ = -f ∘ ⁅x, ·⁆`) and a representation of `K` (`Representation.dual`), and the two actions
are covariant, but a linear form need not be `K`-finite. The **contragredient** `M^∨` is the
`K`-finite part of `Dual k V`: it is stable under `𝔤` because `𝔤` is finite-dimensional, since
`g • ⁅x, f⁆ = ⁅Ad g x, g • f⁆` lies in the span of the brackets of a basis of `𝔤` with the orbit
of `f`.

A **morphism** of `(𝔤, K)`-modules is a linear map commuting with both actions. A morphism
`φ : M → N` has a transpose `φ^∨ : N^∨ → M^∨`, and transposition is contravariantly functorial.

## Main definitions

* `TauCeti.GKModule.Hom M N`: the morphisms of `(𝔤, K)`-modules, with `id` and `comp`.
* `TauCeti.GKModule.contragredientSubmodule M`: the `K`-finite linear forms, a Lie submodule of
  `Dual k V`.
* `TauCeti.GKModule.contragredient M`: the contragredient `(𝔤, K)`-module `M^∨`.
* `TauCeti.GKModule.Hom.dual φ`: the transpose `N^∨ → M^∨` of a morphism `φ : M → N`.

## Main statements

* `TauCeti.GKModule.dual_lie`: the dual actions of `K` and `𝔤` are covariant.
* `TauCeti.GKModule.isGFinite_dual_lie`: a `K`-finite linear form stays `K`-finite under `𝔤`.
* `TauCeti.GKModule.contragredientSubmodule_eq_top`: for finite-dimensional `V` the contragredient
  is the whole dual.
* `TauCeti.GKModule.Hom.dual_id`, `TauCeti.GKModule.Hom.dual_comp`: transposition is a
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

/-! ### Morphisms -/

/-- A **morphism of `(𝔤, K)`-modules**: a `𝔤`-module morphism commuting with the actions of
`K`. -/
structure Hom (M : GKModule Ad V) (N : GKModule Ad W) extends V →ₗ⁅k,𝔤⁆ W where
  /-- The morphism commutes with the actions of `K`. -/
  map_ρ (g : K) (v : V) : toLieModuleHom (M.ρ g v) = N.ρ g (toLieModuleHom v)

namespace Hom

variable {M : GKModule Ad V} {N : GKModule Ad W} {P : GKModule Ad U}

/-- A morphism of `(𝔤, K)`-modules is a function through its underlying `𝔤`-module morphism. -/
instance instFunLike : FunLike (Hom M N) V W where
  coe φ := φ.toLieModuleHom
  coe_injective φ ψ h := by
    obtain ⟨φ, _⟩ := φ
    obtain ⟨ψ, _⟩ := ψ
    congr
    exact LieModuleHom.coe_injective h

@[simp]
theorem coe_toLieModuleHom (φ : Hom M N) : ⇑φ.toLieModuleHom = φ :=
  (rfl)

@[ext]
theorem ext {φ ψ : Hom M N} (h : ∀ v, φ v = ψ v) : φ = ψ :=
  DFunLike.ext _ _ h

@[simp]
theorem map_lie (φ : Hom M N) (x : 𝔤) (v : V) : φ ⁅x, v⁆ = ⁅x, φ v⁆ :=
  φ.toLieModuleHom.map_lie x v

@[simp]
theorem map_ρ_apply (φ : Hom M N) (g : K) (v : V) : φ (M.ρ g v) = N.ρ g (φ v) :=
  φ.map_ρ g v

variable (M) in
/-- The identity morphism. -/
def id : Hom M M where
  toLieModuleHom := LieModuleHom.id
  map_ρ _ _ := rfl

@[simp]
theorem id_apply (v : V) : id M v = v :=
  (rfl)

/-- The composite of two morphisms. -/
def comp (ψ : Hom N P) (φ : Hom M N) : Hom M P where
  toLieModuleHom := ψ.toLieModuleHom.comp φ.toLieModuleHom
  map_ρ g v := by
    change ψ (φ (M.ρ g v)) = P.ρ g (ψ (φ v))
    rw [map_ρ_apply, map_ρ_apply]

@[simp]
theorem comp_apply (ψ : Hom N P) (φ : Hom M N) (v : V) : ψ.comp φ v = ψ (φ v) :=
  (rfl)

end Hom

/-! ### The contragredient -/

variable (M : GKModule Ad V)

/-- **Covariance of the dual actions.** For the dual actions of `K` and `𝔤` on `Dual k V`,
`g • ⁅x, f⁆ = ⁅Ad g x, g • f⁆`. -/
theorem dual_lie (g : K) (x : 𝔤) (f : Dual k V) :
    M.ρ.dual g ⁅x, f⁆ = ⁅Ad g x, M.ρ.dual g f⁆ := by
  ext v
  have hx : Ad g⁻¹ (Ad g x) = x := by
    change (Ad g⁻¹ * Ad g) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  simp only [dual_apply, Dual.transpose_apply, LinearMap.coe_comp, Function.comp_apply,
    Module.Dual.lie_apply, M.map_lie, hx]

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
  lie_mem {x f} hf := by
    change f ∈ M.ρ.dual.gFiniteSubmodule at hf
    change ⁅x, f⁆ ∈ M.ρ.dual.gFiniteSubmodule
    rw [mem_gFiniteSubmodule] at hf ⊢
    exact M.isGFinite_dual_lie hf x

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
def dual (φ : Hom M N) : Hom N.contragredient M.contragredient where
  toFun f := ⟨(f : Dual k W) ∘ₗ φ.toLieModuleHom.toLinearMap, by
    have := (isGFinite_iff _ _).1 (N.mem_contragredientSubmodule.1 f.prop)
    refine M.mem_contragredientSubmodule.2 (IsGFinite.of_apply_eq
      (φ.toLieModuleHom.toLinearMap.dualMap) (u := fun g ↦ N.ρ.dual g f) fun g ↦ ?_)
    ext v
    simp [dual_apply, Dual.transpose_apply]⟩
  map_add' f f' := Subtype.ext (LinearMap.add_comp _ _ _)
  map_smul' c f := Subtype.ext (LinearMap.smul_comp _ _ _)
  map_lie' {x f} := Subtype.ext <| LinearMap.ext fun v ↦ by
    simp
  map_ρ g f := Subtype.ext <| LinearMap.ext fun v ↦ by
    simp [dual_apply, Dual.transpose_apply]

@[simp]
theorem coe_dual_apply (φ : Hom M N) (f : N.contragredientSubmodule) (v : V) :
    (φ.dual f : Dual k V) v = (f : Dual k W) (φ v) :=
  (rfl)

@[simp]
theorem dual_id : (id M).dual = id M.contragredient :=
  ext fun _ ↦ rfl

@[simp]
theorem dual_comp (ψ : Hom N P) (φ : Hom M N) : (ψ.comp φ).dual = φ.dual.comp ψ.dual :=
  ext fun _ ↦ rfl

end Hom

end GKModule

end TauCeti
