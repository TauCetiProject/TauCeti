/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Crossed modules of groups

A **crossed module** `∂ : T → H` is a group homomorphism together with an action of `H` on `T`
by group automorphisms, written `h • x`, such that

* `∂` is equivariant for conjugation on `H`: `∂ (h • x) = h * ∂ x * h⁻¹`;
* the **Peiffer identity** holds: `∂ x • y = x * y * x⁻¹`.

The basic examples are the inclusion of a normal subgroup, with `H` acting by conjugation, and
an `H`-module `T`, that is a commutative group with an action of `H`, with the trivial boundary.
For a connected reductive group `G`, the map `G_sc → G` from the simply connected cover of its
derived group is a crossed module, and the Galois cohomology of crossed modules is the setting of
the abelianized Galois cohomology of reductive groups (Borovoi, Labesse).

Two consequences of the axioms make the kernel and cokernel of `∂` behave like the homotopy groups
of a two-term complex. The kernel of `∂` is central in `T`, hence commutative
(`CrossedModule.ker_le_center`), and stable under `H`; the range of `∂` is a normal subgroup of
`H`, so the cokernel `H ⧸ ∂.range` is a group. The quotient groupoid, whose isomorphism classes
form the cokernel and whose automorphism groups are the kernel, is in
`TauCeti/Algebra/Group/CrossedModule/QuotientCategory.lean`.

A morphism of crossed modules is a pair of homomorphisms commuting with the boundaries and the
actions (`CrossedModule.Hom`). It induces homomorphisms of kernels and of cokernels. The bundled
category of crossed modules, with the kernel and cokernel functors, is in
`TauCeti/Algebra/Category/CrossedModuleCat/Basic.lean`.

## Main definitions

* `TauCeti.CrossedModule T H`: a crossed module structure `∂ : T →* H` with an action of `H` on
  `T` by automorphisms.
* `TauCeti.CrossedModule.ofNormal`: the crossed module of a normal subgroup.
* `TauCeti.CrossedModule.ofCommGroup`: the crossed module of an `H`-module, with trivial boundary.
* `TauCeti.CrossedModule.Hom`: morphisms of crossed modules, with identities `Hom.id` and
  composition `Hom.comp`.
* `TauCeti.CrossedModule.Hom.kerMap`, `TauCeti.CrossedModule.Hom.cokerMap`: the homomorphisms
  induced by a morphism on the kernels and on the cokernels of the boundaries.

## Main results

* `TauCeti.CrossedModule.act_comp_boundary`: the Peiffer identity says that `∂` followed by the
  action is conjugation.
* `TauCeti.CrossedModule.ker_le_center`: the kernel of `∂` is central.
* `TauCeti.CrossedModule.act_mem_ker`: the kernel of `∂` is stable under `H`.
* `TauCeti.CrossedModule.normal_range_boundary`: the range of `∂` is normal.

## References

* M. Kisin, *Mod p points on Shimura varieties of abelian type*, J. Amer. Math. Soc. 30 (2017),
  §3.2.1.
* J.-P. Labesse, *Cohomologie, stabilisation et changement de base*, Astérisque 257 (1999), §1.1.
* M. Borovoi, *Abelian Galois cohomology of reductive groups*, Mem. Amer. Math. Soc. 626 (1998),
  §3.
-/

public section

namespace TauCeti

/-- A **crossed module** `∂ : T → H`: a group homomorphism `boundary`, together with an action
`act` of `H` on `T` by group automorphisms, such that `∂ (h • x) = h * ∂ x * h⁻¹` and
`∂ x • y = x * y * x⁻¹` (the Peiffer identity). -/
@[ext]
structure CrossedModule (T H : Type*) [Group T] [Group H] where
  /-- The boundary homomorphism `∂ : T →* H`. -/
  boundary : T →* H
  /-- The action of `H` on `T` by group automorphisms. -/
  act : H →* MulAut T
  /-- The boundary is equivariant for the conjugation action of `H` on itself. -/
  boundary_act (h : H) (x : T) : boundary (act h x) = h * boundary x * h⁻¹
  /-- The Peiffer identity: the action of a boundary is conjugation. -/
  act_boundary (x y : T) : act (boundary x) y = x * y * x⁻¹

namespace CrossedModule

attribute [simp] boundary_act act_boundary

variable {T H : Type*} [Group T] [Group H] (M : CrossedModule T H)

/-- The Peiffer identity, as an equality of homomorphisms: `∂` followed by the action of `H` on
`T` is the conjugation action of `T` on itself. -/
theorem act_comp_boundary : M.act.comp M.boundary = MulAut.conj := by
  ext x y
  simp

/-- The kernel of the boundary of a crossed module is central. -/
theorem ker_le_center : M.boundary.ker ≤ Subgroup.center T := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have h := M.act_boundary x y
  rw [MonoidHom.mem_ker.mp hx, map_one, MulAut.one_apply] at h
  exact eq_mul_inv_iff_mul_eq.mp h

/-- The kernel of the boundary of a crossed module is commutative. -/
instance isMulCommutative_ker : IsMulCommutative M.boundary.ker :=
  IsMulCommutative.of_setLike_mul_comm fun _ hx y _ ↦
    ((Subgroup.mem_center_iff.mp (M.ker_le_center hx) y)).symm

/-- The kernel of the boundary of a crossed module is stable under the action of `H`. -/
theorem act_mem_ker {x : T} (hx : x ∈ M.boundary.ker) (h : H) : M.act h x ∈ M.boundary.ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  simp [hx]

/-- The range of the boundary of a crossed module is a normal subgroup, so the cokernel
`H ⧸ M.boundary.range` is a group. -/
instance normal_range_boundary : M.boundary.range.Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ h
    exact ⟨M.act h x, M.boundary_act h x⟩

section Examples

/-- The **crossed module of a normal subgroup** `N` of `H`: the inclusion of `N`, with `H`
acting on `N` by conjugation. -/
def ofNormal (N : Subgroup H) [N.Normal] : CrossedModule N H where
  boundary := N.subtype
  act := MulAut.conjNormal
  boundary_act h x := by simp
  act_boundary x y := by ext; simp

@[simp]
theorem ofNormal_boundary (N : Subgroup H) [N.Normal] : (ofNormal N).boundary = N.subtype :=
  (rfl)

@[simp]
theorem ofNormal_act (N : Subgroup H) [N.Normal] : (ofNormal N).act = MulAut.conjNormal :=
  (rfl)

/-- The **crossed module of an `H`-module**: a commutative group `A` on which `H` acts by
automorphisms, with the trivial boundary `A →* H`. -/
def ofCommGroup {A : Type*} [CommGroup A] (ρ : H →* MulAut A) : CrossedModule A H where
  boundary := 1
  act := ρ
  boundary_act h x := by simp
  act_boundary x y := by simp [mul_inv_cancel_comm]

@[simp]
theorem ofCommGroup_boundary {A : Type*} [CommGroup A] (ρ : H →* MulAut A) :
    (ofCommGroup ρ).boundary = 1 :=
  (rfl)

@[simp]
theorem ofCommGroup_act {A : Type*} [CommGroup A] (ρ : H →* MulAut A) : (ofCommGroup ρ).act = ρ :=
  (rfl)

end Examples

section Hom

variable {T' H' T'' H'' T''' H''' : Type*} [Group T'] [Group H'] [Group T''] [Group H'']
  [Group T'''] [Group H''']

/-- A **morphism of crossed modules** from `∂ : T → H` to `∂' : T' → H'`: homomorphisms
`left : T →* T'` and `right : H →* H'` with `∂' ∘ left = right ∘ ∂` and
`left (h • x) = right h • left x`. -/
@[ext]
structure Hom (M : CrossedModule T H) (M' : CrossedModule T' H') where
  /-- The homomorphism on the sources of the boundaries. -/
  left : T →* T'
  /-- The homomorphism on the targets of the boundaries. -/
  right : H →* H'
  /-- The square formed by the boundaries commutes. -/
  boundary_left (x : T) : M'.boundary (left x) = right (M.boundary x)
  /-- The homomorphism `left` is equivariant along `right`. -/
  left_act (h : H) (x : T) : left (M.act h x) = M'.act (right h) (left x)

attribute [simp] Hom.boundary_left Hom.left_act

namespace Hom

/-- The identity morphism of a crossed module. -/
protected def id : Hom M M where
  left := MonoidHom.id T
  right := MonoidHom.id H
  boundary_left _ := rfl
  left_act _ _ := rfl

@[simp]
theorem id_left : (Hom.id M).left = MonoidHom.id T :=
  (rfl)

@[simp]
theorem id_right : (Hom.id M).right = MonoidHom.id H :=
  (rfl)

variable {M} {M' : CrossedModule T' H'} {M'' : CrossedModule T'' H''}
  {M''' : CrossedModule T''' H'''}

/-- The composite of two morphisms of crossed modules. -/
def comp (g : Hom M' M'') (f : Hom M M') : Hom M M'' where
  left := g.left.comp f.left
  right := g.right.comp f.right
  boundary_left x := by simp
  left_act h x := by simp

@[simp]
theorem comp_left (g : Hom M' M'') (f : Hom M M') : (g.comp f).left = g.left.comp f.left :=
  (rfl)

@[simp]
theorem comp_right (g : Hom M' M'') (f : Hom M M') : (g.comp f).right = g.right.comp f.right :=
  (rfl)

@[simp]
theorem id_comp (f : Hom M M') : (Hom.id M').comp f = f :=
  (rfl)

@[simp]
theorem comp_id (f : Hom M M') : f.comp (Hom.id M) = f :=
  (rfl)

theorem comp_assoc (h : Hom M'' M''') (g : Hom M' M'') (f : Hom M M') :
    (h.comp g).comp f = h.comp (g.comp f) :=
  (rfl)

/-- The square of boundaries of a morphism of crossed modules, as an equality of
homomorphisms. -/
theorem boundary_comp_left (f : Hom M M') : M'.boundary.comp f.left = f.right.comp M.boundary :=
  MonoidHom.ext f.boundary_left

/-- The homomorphism induced by a morphism of crossed modules on the kernels of the
boundaries. -/
def kerMap (f : Hom M M') : M.boundary.ker →* M'.boundary.ker :=
  (f.left.domRestrict M.boundary.ker).codRestrict M'.boundary.ker fun x ↦ by
    simp [MonoidHom.mem_ker.mp x.2]

@[simp]
theorem coe_kerMap_apply (f : Hom M M') (x : M.boundary.ker) : (f.kerMap x : T') = f.left x :=
  (rfl)

@[simp]
theorem kerMap_id : (Hom.id M).kerMap = MonoidHom.id _ :=
  (rfl)

theorem kerMap_comp (g : Hom M' M'') (f : Hom M M') :
    (g.comp f).kerMap = g.kerMap.comp f.kerMap :=
  (rfl)

/-- A morphism of crossed modules maps the range of the first boundary into the range of the
second. -/
theorem range_le_comap_range (f : Hom M M') :
    M.boundary.range ≤ M'.boundary.range.comap f.right := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f.left x, f.boundary_left x⟩

/-- The homomorphism induced by a morphism of crossed modules on the cokernels of the
boundaries. -/
def cokerMap (f : Hom M M') : H ⧸ M.boundary.range →* H' ⧸ M'.boundary.range :=
  QuotientGroup.map _ _ f.right f.range_le_comap_range

@[simp]
theorem cokerMap_mk (f : Hom M M') (h : H) : f.cokerMap (h : H ⧸ M.boundary.range) = f.right h :=
  (rfl)

@[simp]
theorem cokerMap_id : (Hom.id M).cokerMap = MonoidHom.id _ := by
  ext
  simp

theorem cokerMap_comp (g : Hom M' M'') (f : Hom M M') :
    (g.comp f).cokerMap = g.cokerMap.comp f.cokerMap := by
  ext
  simp

end Hom

end Hom

end CrossedModule

end TauCeti
