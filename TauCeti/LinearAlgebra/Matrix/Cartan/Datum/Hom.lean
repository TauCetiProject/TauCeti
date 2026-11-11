/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Basic

/-!
# Morphisms of Cartan data

A compatible morphism of root data `(X, Y) → (X', Y')` consists of a map of weight lattices
`X' → X` and a map of coweight lattices `Y → Y'`, transpose to each other for the two pairings and
carrying roots to roots and coroots to coroots. These conditions say nothing about the central
directions: a central isogeny is such a morphism whose lattice maps are moreover injective with
finite cokernel, whereas a general morphism may, for instance, be zero between two rootless tori.
Because the pairings are perfect, the map of weights is determined by the map of coweights. This
file therefore defines a morphism of Cartan data `TauCeti.CartanDatum.Hom D D'` as a linear map
`Y → Y'` carrying `hᵢ` to `h'ᵢ`, under which each `α'ᵢ` pulls back to `αᵢ`, and which keeps the
symmetrizer; the map of weights is recovered as its transpose `TauCeti.CartanDatum.Hom.weightMap`.

The coweight lattice indexes the toral generators `K_y` of a quantized enveloping algebra, and a
morphism of data supplies what an assignment `K_y ↦ K_(f y)`, `Eᵢ ↦ Eᵢ`, `Fᵢ ↦ Fᵢ` of quantum
groups needs: it preserves the Cartan matrix (`TauCeti.CartanDatum.Hom.cartan_eq`), the pairing of
every root with every coweight (`TauCeti.CartanDatum.Hom.pairing_root_map`), the toral directions
(`TauCeti.CartanDatum.Hom.map_simpleTorus`) and the simple reflections
(`TauCeti.CartanDatum.Hom.map_coreflection`). Morphisms compose, functorially on weights and on
coweights.

## Main definitions

* `TauCeti.CartanDatum.Hom D D'`: morphisms of Cartan data with the same index type.
* `TauCeti.CartanDatum.Hom.weightMap`: the induced map `X' → X` of weight lattices.
* `TauCeti.CartanDatum.Hom.id` and `TauCeti.CartanDatum.Hom.comp`.

## Main results

* `TauCeti.CartanDatum.Hom.pairing_weightMap`: `⟨f^* λ', y⟩ = ⟨λ', f y⟩`, and
  `TauCeti.CartanDatum.Hom.eq_weightMap`: this characterizes `f^*`.
* `TauCeti.CartanDatum.Hom.weightMap_root`: `f^* α'ᵢ = αᵢ`.
* `TauCeti.CartanDatum.Hom.weightMap_reflection`: `f^*` intertwines the reflections of weights.
* `TauCeti.CartanDatum.Hom.weightMap_comp`: `(g ∘ f)^* = f^* ∘ g^*`.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §2.2 (root data).
-/

public section

namespace TauCeti

namespace CartanDatum

variable {ι X Y X' Y' X'' Y'' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X']
  [AddCommGroup Y'] [AddCommGroup X''] [AddCommGroup Y'']

/-- A **morphism of Cartan data** `D → D'` with the same index type: a linear map of coweight
lattices `f : Y → Y'` with `f hᵢ = h'ᵢ` and `⟨α'ᵢ, f y⟩ = ⟨αᵢ, y⟩`, preserving the symmetrizer. Its
transpose `TauCeti.CartanDatum.Hom.weightMap : X' → X` carries `α'ᵢ` to `αᵢ`. -/
@[ext]
structure Hom (D : CartanDatum ι X Y) (D' : CartanDatum ι X' Y') where
  /-- The underlying map of coweight lattices. -/
  toLinearMap : Y →ₗ[ℤ] Y'
  map_coroot (i : ι) : toLinearMap (D.coroot i) = D'.coroot i
  pairing_root_map (i : ι) (y : Y) : D'.pairing (D'.root i) (toLinearMap y) = D.pairing (D.root i) y
  symmetrizer_eq : D'.symmetrizer = D.symmetrizer

namespace Hom

variable {D : CartanDatum ι X Y} {D' : CartanDatum ι X' Y'} {D'' : CartanDatum ι X'' Y''}

attribute [simp] map_coroot pairing_root_map

/-- The identity morphism of a Cartan datum. -/
def id (D : CartanDatum ι X Y) : Hom D D where
  toLinearMap := .id
  map_coroot _ := rfl
  pairing_root_map _ _ := rfl
  symmetrizer_eq := rfl

/-- The composite of two morphisms of Cartan data. -/
def comp (g : Hom D' D'') (f : Hom D D') : Hom D D'' where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_coroot i := by simp
  pairing_root_map i y := by simp
  symmetrizer_eq := g.symmetrizer_eq.trans f.symmetrizer_eq

-- `(rfl)`, not `rfl`: the bodies of `id` and `comp` are not exposed, and the parenthesised form
-- keeps these proofs out of the exported definitional-equality check.
@[simp]
lemma id_toLinearMap (D : CartanDatum ι X Y) : (Hom.id D).toLinearMap = .id := (rfl)

@[simp]
lemma comp_toLinearMap (g : Hom D' D'') (f : Hom D D') :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap := (rfl)

@[simp]
lemma comp_id (f : Hom D D') : f.comp (Hom.id D) = f := by
  ext
  simp

@[simp]
lemma id_comp (f : Hom D D') : (Hom.id D').comp f = f := by
  ext
  simp

lemma comp_assoc {X''' Y''' : Type*} [AddCommGroup X'''] [AddCommGroup Y''']
    {D''' : CartanDatum ι X''' Y'''} (h : Hom D'' D''') (g : Hom D' D'') (f : Hom D D') :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  simp

variable (f : Hom D D')

include f in
/-- A morphism preserves the Cartan matrix. -/
lemma cartan_eq : D'.cartan = D.cartan := by
  ext i j
  rw [cartan_apply, ← f.map_coroot, f.pairing_root_map, pairing_root_coroot]

@[simp]
lemma map_simpleTorus (i : ι) : f.toLinearMap (D.simpleTorus i) = D'.simpleTorus i := by
  rw [simpleTorus_def, map_nsmul, f.map_coroot, simpleTorus_def, f.symmetrizer_eq]

/-- A morphism intertwines the simple reflections of the coweight lattices. -/
@[simp]
lemma map_coreflection (i : ι) (y : Y) :
    f.toLinearMap (D.coreflection i y) = D'.coreflection i (f.toLinearMap y) := by
  rw [coreflection_apply, coreflection_apply, map_sub, map_zsmul, f.map_coroot,
    f.pairing_root_map]

/-- The induced map of weight lattices `X' → X`: the transpose of `f` for the two perfect
pairings. -/
noncomputable def weightMap : X' →ₗ[ℤ] X :=
  D.pairing.toPerfPair.symm.toLinearMap ∘ₗ f.toLinearMap.dualMap ∘ₗ
    D'.pairing.toPerfPair.toLinearMap

/-- The defining property of the transpose: `⟨f^* λ', y⟩ = ⟨λ', f y⟩`. -/
@[simp]
lemma pairing_weightMap (x : X') (y : Y) :
    D.pairing (f.weightMap x) y = D'.pairing x (f.toLinearMap y) := by
  simp [weightMap]

/-- The transpose is the only map of weights adjoint to `f`. -/
lemma eq_weightMap {g : X' →ₗ[ℤ] X}
    (hg : ∀ x y, D.pairing (g x) y = D'.pairing x (f.toLinearMap y)) : g = f.weightMap := by
  ext x
  apply (LinearMap.IsPerfPair.bijective_left D.pairing).injective
  ext y
  rw [hg, pairing_weightMap]

@[simp]
lemma weightMap_root (i : ι) : f.weightMap (D'.root i) = D.root i := by
  apply (LinearMap.IsPerfPair.bijective_left D.pairing).injective
  ext y
  rw [pairing_weightMap, pairing_root_map]

/-- The transpose of a morphism intertwines the simple reflections of the weight lattices. -/
@[simp]
lemma weightMap_reflection (i : ι) (x : X') :
    f.weightMap (D'.reflection i x) = D.reflection i (f.weightMap x) := by
  rw [reflection_apply, reflection_apply, map_sub, map_zsmul, weightMap_root, pairing_weightMap,
    f.map_coroot]

@[simp]
lemma weightMap_id : (Hom.id D).weightMap = .id :=
  ((Hom.id D).eq_weightMap (g := .id) fun _ _ ↦ rfl).symm

/-- Taking transposes is contravariant: `(g ∘ f)^* = f^* ∘ g^*`. -/
lemma weightMap_comp (g : Hom D' D'') : (g.comp f).weightMap = f.weightMap ∘ₗ g.weightMap :=
  ((g.comp f).eq_weightMap fun _ _ ↦ by simp).symm

end Hom

end CartanDatum

end TauCeti
