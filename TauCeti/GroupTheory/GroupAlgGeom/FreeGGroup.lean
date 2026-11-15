/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Basic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.Algebra.Group.ULift

/-!
# Free `G`-groups

A group `H` receiving the coefficients through `ι : G →* H` is a *free `G`-group* when it is
isomorphic over `G` to `G[Y] = G ∗ F(Y)` for some set `Y` of free generators. Over trivial
coefficients these are the free groups, and `G` itself is the free `G`-group on no generators.
Free `G`-groups are the groups whose `G`-homomorphisms to any target are unconstrained
specialisations of the free generators; they label the leaves of Makanin–Razborov diagrams.

## Main definitions

* `TauCeti.GroupAlgGeom.IsFreeGGroup ι`: `ι : G →* H` exhibits `H` as a free `G`-group.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.Generators`, `TauCeti.GroupAlgGeom.IsFreeGGroup.of`: a
  chosen family of free generators of a free `G`-group.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.homEquiv`: the universal property, `G`-homomorphisms out of a
  free `G`-group correspond to maps out of its free generators.
* `TauCeti.GroupAlgGeom.GX.mulEquivFreeGroupSum`: for a free group basis `b : FreeGroupBasis A G`,
  the canonical isomorphism `G[X] ≃* FreeGroup (X ⊕ A)`.

## Main results

* `TauCeti.GroupAlgGeom.GX.eval_eq_lift_mulEquivFreeGroupSum`: under `GX.mulEquivFreeGroupSum`,
  evaluation in `G[X]` is `FreeGroup.lift`.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.of_mulEquiv`: a group isomorphic over `G` to `G[Y]`, for a
  type `Y` in any universe, is a free `G`-group.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.of_unique_lift`: conversely, a group with a family of
  elements that may be sent to arbitrary elements of any group under `G` by a unique
  `G`-homomorphism is a free `G`-group.
* `TauCeti.GroupAlgGeom.isFreeGGroup_inl`: `G[Y]` is a free `G`-group.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.of_bijective_gHom`: a free `G`-group stays free along a
  bijective `G`-homomorphism.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.of_bijective`: a bijective coefficient map exhibits a free
  `G`-group on no generators.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.injective`: the coefficient map of a free `G`-group is
  injective.
* `TauCeti.GroupAlgGeom.isFreeGGroup_iff_isFreeGroup`: over trivial coefficients, the free
  `G`-groups are the free groups.
* `TauCeti.GroupAlgGeom.IsFreeGGroup.isFreeGroup`: a free `G`-group over a free group `G` is a
  free group.

## Implementation notes

The predicate and its API are the relative version over `G` of Mathlib's `IsFreeGroup` and
`FreeGroupBasis` (`Mathlib.GroupTheory.FreeGroup.IsFreeGroup`), which they follow:
`IsFreeGGroup.of_mulEquiv`, `IsFreeGGroup.Generators`, `IsFreeGGroup.mulEquiv`,
`IsFreeGGroup.of`, `IsFreeGGroup.homEquiv`, `IsFreeGGroup.unique_lift` and
`IsFreeGGroup.of_unique_lift` correspond to `IsFreeGroup.ofMulEquiv`, `IsFreeGroup.Generators`,
`IsFreeGroup.mulEquiv`, `IsFreeGroup.of`, `IsFreeGroup.lift`, `IsFreeGroup.unique_lift` and
`IsFreeGroup.ofUniqueLift`.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §1.2 (free `G`-groups `G[X] = G ∗ F(X)`).
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.2 (`G[X]` as the free object of the category of `G`-groups).
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod

universe u v w

variable {G : Type v} [Group G] {H : Type u} [Group H]

namespace GX

/-- For a free group basis `b : FreeGroupBasis A G`, the free `G`-group `G[X]` is naturally
isomorphic to `FreeGroup (X ⊕ A)`. -/
noncomputable def mulEquivFreeGroupSum {A : Type*} (b : FreeGroupBasis A G) (X : Type*) :
    GX G X ≃* FreeGroup (X ⊕ A) :=
  MonoidHom.toMulEquiv
    (lift (b.lift (FreeGroup.of ∘ Sum.inr)) (FreeGroup.map Sum.inl))
    (FreeGroup.lift (Sum.elim (inr ∘ FreeGroup.of) (inl ∘ b)))
    (hom_ext (b.ext_hom _ _ fun _ => by simp) (FreeGroup.ext_hom _ _ fun _ => by simp))
    (FreeGroup.ext_hom _ _ fun z => by cases z <;> simp)

/-- `GX.mulEquivFreeGroupSum` sends a coefficient `g` to its representation on the right
summand. -/
@[simp]
theorem mulEquivFreeGroupSum_inl {A : Type*} (b : FreeGroupBasis A G) (X : Type*) (g : G) :
    mulEquivFreeGroupSum b X (inl g) = FreeGroup.map Sum.inr (b.repr g) := by
  simp [mulEquivFreeGroupSum, FreeGroup.map_eq_lift]

/-- `GX.mulEquivFreeGroupSum` sends a word `w` in the variables to `FreeGroup.map Sum.inl w`. -/
@[simp]
theorem mulEquivFreeGroupSum_inr {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (w : FreeGroup X) : mulEquivFreeGroupSum b X (inr w) = FreeGroup.map Sum.inl w := by
  simp [mulEquivFreeGroupSum]

/-- `GX.mulEquivFreeGroupSum` sends the coefficient `b c` to `FreeGroup.of (Sum.inr c)`. -/
theorem mulEquivFreeGroupSum_inl_coe {A : Type*} (b : FreeGroupBasis A G) (X : Type*) (c : A) :
    mulEquivFreeGroupSum b X (inl (b c)) = FreeGroup.of (Sum.inr c) := by
  simp

/-- `GX.mulEquivFreeGroupSum` sends the variable `x` to `FreeGroup.of (Sum.inl x)`. -/
theorem mulEquivFreeGroupSum_inr_of {A : Type*} (b : FreeGroupBasis A G) (X : Type*) (x : X) :
    mulEquivFreeGroupSum b X (inr (FreeGroup.of x)) = FreeGroup.of (Sum.inl x) := by
  simp

/-- `(GX.mulEquivFreeGroupSum b X).symm` sends `FreeGroup.of (Sum.inl x)` to the variable `x`. -/
@[simp]
theorem mulEquivFreeGroupSum_symm_of_inl {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (x : X) :
    (mulEquivFreeGroupSum b X).symm (FreeGroup.of (Sum.inl x)) = inr (FreeGroup.of x) := by
  simp [mulEquivFreeGroupSum]

/-- `(GX.mulEquivFreeGroupSum b X).symm` sends `FreeGroup.of (Sum.inr c)` to the coefficient
`b c`. -/
@[simp]
theorem mulEquivFreeGroupSum_symm_of_inr {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (c : A) : (mulEquivFreeGroupSum b X).symm (FreeGroup.of (Sum.inr c)) = inl (b c) := by
  simp [mulEquivFreeGroupSum]

/-- `(GX.mulEquivFreeGroupSum b X).symm` sends `FreeGroup.map Sum.inl w` to `inr w`. -/
@[simp]
theorem mulEquivFreeGroupSum_symm_map_inl {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (w : FreeGroup X) : (mulEquivFreeGroupSum b X).symm (FreeGroup.map Sum.inl w) = inr w :=
  (mulEquivFreeGroupSum b X).injective <| by simp

/-- `(GX.mulEquivFreeGroupSum b X).symm` sends `FreeGroup.map Sum.inr w` to `inl (b.repr.symm w)`.
-/
@[simp]
theorem mulEquivFreeGroupSum_symm_map_inr {A : Type*} (b : FreeGroupBasis A G) (X : Type*)
    (w : FreeGroup A) :
    (mulEquivFreeGroupSum b X).symm (FreeGroup.map Sum.inr w) = inl (b.repr.symm w) :=
  (mulEquivFreeGroupSum b X).injective <| by simp

/-- Under `GX.mulEquivFreeGroupSum`, evaluation of a word in `G[X]` is `FreeGroup.lift` sending
variables along `v` and basis generators along `ι ∘ b`. -/
theorem eval_eq_lift_mulEquivFreeGroupSum {A X : Type*} (b : FreeGroupBasis A G)
    (ι : G →* H) (v : X → H) (w : GX G X) :
    eval ι v w = FreeGroup.lift (Sum.elim v (ι ∘ b)) (mulEquivFreeGroupSum b X w) := by
  have : eval ι v = (FreeGroup.lift (Sum.elim v (ι ∘ b))).comp
      (mulEquivFreeGroupSum b X).toMonoidHom :=
    hom_ext (b.ext_hom _ _ fun c => by simp) (FreeGroup.ext_hom _ _ fun x => by simp)
  exact DFunLike.congr_fun this w

end GX

/-- The coefficient map `ι : G →* H` exhibits `H` as a *free `G`-group*: there are a type `Y` and
an isomorphism `G[Y] ≃* H` restricting to `ι` on the coefficients. -/
def IsFreeGGroup (ι : G →* H) : Prop :=
  ∃ (Y : Type u) (e : GX G Y ≃* H), ∀ g, e (inl g) = ι g

theorem isFreeGGroup_iff {ι : G →* H} :
    IsFreeGGroup ι ↔ ∃ (Y : Type u) (e : GX G Y ≃* H), ∀ g, e (inl g) = ι g :=
  Iff.rfl

namespace IsFreeGGroup

/-- A group isomorphic over `G` to `G[Y]` is a free `G`-group, whatever the universe of `Y`: the
free generators may be taken to be their images in `H`. -/
theorem of_mulEquiv {Y : Type w} {ι : G →* H} (e : GX G Y ≃* H) (he : ∀ g, e (inl g) = ι g) :
    IsFreeGGroup ι := by
  let f : Y → H := fun y => e (inr (FreeGroup.of y))
  have hf : Function.Injective f := e.injective.comp (inr_injective.comp FreeGroup.of_injective)
  exact ⟨Set.range f,
    (MulEquiv.coprodCongr (.refl G) (FreeGroup.freeGroupCongr (Equiv.ofInjective f hf))).symm.trans
      e, fun g => by simp [he]⟩

/-- A free `G`-group stays free along a bijective `G`-homomorphism. -/
theorem of_bijective_gHom {K : Type w} [Group K] {ι : G →* H} {κ : G →* K} (h : IsFreeGGroup ι)
    (φ : GHom ι κ) (hφ : Function.Bijective φ) : IsFreeGGroup κ := by
  obtain ⟨Y, e, he⟩ := h
  exact of_mulEquiv (e.trans (MulEquiv.ofBijective (φ : H →* K) hφ)) fun g => by simp [he]

/-- A bijective coefficient map exhibits its target as the free `G`-group on no generators. -/
theorem of_bijective {ι : G →* H} (hι : Function.Bijective ι) : IsFreeGGroup ι :=
  ⟨PEmpty, GX.equivOfIsEmpty.trans (MulEquiv.ofBijective ι hι), fun g => by simp⟩

/-- `G` is the free `G`-group on no generators. -/
@[simp]
protected theorem id (G : Type u) [Group G] : IsFreeGGroup (MonoidHom.id G) :=
  of_bijective Function.bijective_id

/-- The coefficient map of a free `G`-group is injective. -/
theorem injective {ι : G →* H} (h : IsFreeGGroup ι) : Function.Injective ι := by
  obtain ⟨Y, e, he⟩ := h
  intro a b hab
  exact inl_injective (e.injective (by rw [he, he, hab]))

/-- Over trivial coefficients, every free group is a free `G`-group. -/
theorem of_subsingleton [Subsingleton G] [IsFreeGroup H] (ι : G →* H) : IsFreeGGroup ι :=
  ⟨IsFreeGroup.Generators H,
    (GX.equivFreeGroup G _).trans (IsFreeGroup.toFreeGroup H).symm, fun g => by
      rw [Subsingleton.elim g 1, map_one, map_one, map_one]⟩

/-- A group under `G` is a free `G`-group as soon as some family `y` of its elements may be sent to
arbitrary elements of any group `K` under `G` by a unique `G`-homomorphism. -/
theorem of_unique_lift {ι : G →* H} {Y : Type w} (y : Y → H)
    (hy : ∀ {K : Type (max u v w)} [Group K] (κ : G →* K) (v : Y → K),
      ∃! φ : GHom ι κ, ∀ i, φ (y i) = v i) :
    IsFreeGGroup ι := by
  let up₁ : GX G Y ≃* ULift.{u} (GX G Y) := MulEquiv.ulift.symm
  let up₂ : H ≃* ULift.{max v w} H := MulEquiv.ulift.symm
  obtain ⟨φ, hφ, -⟩ := hy (up₁.toMonoidHom.comp inl) fun i => up₁ (inr (FreeGroup.of i))
  let f : GHom ι (inl : G →* GX G Y) := (GHom.ofMulEquiv up₁.symm fun g => by simp).comp φ
  have hfy (i : Y) : f (y i) = inr (FreeGroup.of i) := by
    rw [GHom.coe_comp, Function.comp_apply, hφ, GHom.coe_ofMulEquiv, MulEquiv.symm_apply_apply]
  have h₁ : (f : H →* GX G Y).comp (eval ι y) = .id _ := GX.ext_hom (by simp) (by simp [hfy])
  -- Two `G`-homomorphisms `H → ULift H` agreeing on `y` are equal.
  let ψ : GHom ι (up₂.toMonoidHom.comp ι) := .ofMulEquiv up₂ fun g => by simp
  have hψ (x : H) : ψ x = up₂ x := congrFun (GHom.coe_ofMulEquiv ..) x
  have h₂ := (hy (up₂.toMonoidHom.comp ι) fun i => up₂ (y i)).unique
    (y₁ := ψ.comp ((evalGHom ι y).comp f)) (y₂ := ψ)
    (fun i => by simp only [GHom.coe_comp, Function.comp_apply, hfy, coe_evalGHom, eval_inr_of, hψ])
    fun i => hψ (y i)
  refine of_mulEquiv (MonoidHom.toMulEquiv (eval ι y) f h₁ (MonoidHom.ext fun x => ?_))
    (eval_inl ι y)
  apply up₂.injective
  simpa only [GHom.coe_comp, Function.comp_apply, coe_evalGHom, hψ, MonoidHom.comp_apply,
    MonoidHom.id_apply, MonoidHom.coe_ofClass] using DFunLike.congr_fun h₂ x

section Generators

variable {ι : G →* H} (h : IsFreeGGroup ι)

/-- A type of free generators of a free `G`-group, chosen once and for all. -/
protected def Generators : Type u :=
  (isFreeGGroup_iff.1 h).choose

/-- The chosen isomorphism over `G` from `G[Y]`, for `Y` the chosen free generators, to a free
`G`-group. -/
noncomputable def mulEquiv : GX G h.Generators ≃* H :=
  (isFreeGGroup_iff.1 h).choose_spec.choose

@[simp]
theorem mulEquiv_inl (g : G) : h.mulEquiv (inl g) = ι g :=
  (isFreeGGroup_iff.1 h).choose_spec.choose_spec g

/-- The chosen free generators of a free `G`-group, as elements of it. -/
noncomputable def of (y : h.Generators) : H :=
  h.mulEquiv (inr (FreeGroup.of y))

@[simp]
theorem mulEquiv_inr_of (y : h.Generators) : h.mulEquiv (inr (FreeGroup.of y)) = h.of y :=
  (rfl)

variable {K : Type w} [Group K] (κ : G →* K)

/-- The universal property of a free `G`-group: its `G`-homomorphisms to a group `K` under `G`
correspond to the maps from its free generators to `K`, by restriction. -/
noncomputable def homEquiv : GHom ι κ ≃ (h.Generators → K) where
  toFun φ y := φ (h.of y)
  invFun v := (evalGHom κ v).comp
    (.ofMulEquiv h.mulEquiv.symm fun g => by rw [MulEquiv.symm_apply_eq, mulEquiv_inl])
  left_inv φ := by
    have : eval κ (fun y => φ (h.of y)) = (φ : H →* K).comp h.mulEquiv.toMonoidHom :=
      GX.ext_hom (by simp) (by simp)
    ext x
    simpa using DFunLike.congr_fun this (h.mulEquiv.symm x)
  right_inv v := funext fun y => by simp [← mulEquiv_inr_of]

@[simp]
theorem homEquiv_apply (φ : GHom ι κ) (y : h.Generators) : h.homEquiv κ φ y = φ (h.of y) :=
  (rfl)

@[simp]
theorem homEquiv_symm_apply_of (v : h.Generators → K) (y : h.Generators) :
    (h.homEquiv κ).symm v (h.of y) = v y :=
  congrFun ((h.homEquiv κ).apply_symm_apply v) y

/-- The free generators of a free `G`-group may be sent to arbitrary elements of any group under
`G` by a unique `G`-homomorphism. -/
theorem unique_lift (v : h.Generators → K) : ∃! φ : GHom ι κ, ∀ y, φ (h.of y) = v y :=
  ⟨(h.homEquiv κ).symm v, h.homEquiv_symm_apply_of κ v,
    fun _ hφ => (h.homEquiv κ).eq_symm_apply.2 (funext hφ)⟩

variable {κ} in
/-- `G`-homomorphisms out of a free `G`-group agreeing on its free generators are equal. -/
theorem gHom_ext {φ ψ : GHom ι κ} (hφψ : ∀ y, φ (h.of y) = ψ (h.of y)) : φ = ψ :=
  (h.homEquiv κ).injective (funext hφψ)

end Generators

/-- Over trivial coefficients, a free `G`-group is a free group. -/
theorem isFreeGroup_of_subsingleton [Subsingleton G] {ι : G →* H} (h : IsFreeGGroup ι) :
    IsFreeGroup H :=
  .ofMulEquiv ((GX.equivFreeGroup G _).symm.trans h.mulEquiv)

/-- A free `G`-group over a free group `G` is a free group: `G ∗ F(Y)` is free on a basis of `G`
together with `Y`. -/
theorem isFreeGroup [IsFreeGroup G] {ι : G →* H} (h : IsFreeGGroup ι) : IsFreeGroup H :=
  (FreeGroupBasis.ofRepr (h.mulEquiv.symm.trans
    (GX.mulEquivFreeGroupSum (IsFreeGroup.basis G) h.Generators))).isFreeGroup

end IsFreeGGroup

/-- Over trivial coefficients, the free `G`-groups are the free groups. -/
theorem isFreeGGroup_iff_isFreeGroup [Subsingleton G] {ι : G →* H} :
    IsFreeGGroup ι ↔ IsFreeGroup H :=
  ⟨IsFreeGGroup.isFreeGroup_of_subsingleton, fun _ => .of_subsingleton ι⟩

/-- The free `G`-group `G[Y]` is a free `G`-group. -/
@[simp]
theorem isFreeGGroup_inl (Y : Type w) : IsFreeGGroup (inl : G →* GX G Y) :=
  .of_mulEquiv (.refl _) fun _ => rfl

end TauCeti.GroupAlgGeom
