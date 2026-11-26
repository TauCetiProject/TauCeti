/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Endpoint-preserving subcategories of the simplex category

This file defines the three endpoint-preserving wide subcategories of `SimplexCategory` (`Δ`):

* `TauCeti.SimplexCategory.LastPreserving` (`Δ_top`): all nonempty finite ordinals `⦋n⦌`, with
  monotone maps preserving the greatest element `Fin.last n`.
* `TauCeti.SimplexCategory.ZeroPreserving` (`Δ_bot`): all nonempty finite ordinals `⦋n⦌`, with
  monotone maps preserving the least element `0`.
* `TauCeti.SimplexCategory.EndpointPreserving` (`Δ_∂`): all nonempty finite ordinals `⦋n⦌`
  (including `⦋0⦌`, where the two endpoints coincide), with monotone maps preserving both `0` and
  `Fin.last n`.

It also records the generator characterizations (`δ` and `σ`), reversal symmetries, terminal
object `⦋0⦌`, faithful inclusions from `EndpointPreserving` into `LastPreserving` and
`ZeroPreserving`, and strict-containment witnesses. The top/bottom duality `Δ_topᵒᵖ ≅ Δ_bot` and
the finite-ordinal cut duality `Δ₊ᵒᵖ ≅ Δ_∂` live in
`TauCeti.AlgebraicTopology.SimplexCategory.Endpoint.Adjoint` and
`TauCeti.AlgebraicTopology.SimplexCategory.Endpoint.Cut`.

## References

* S. Schanuel and R. Street, *The free adjunction*, Cahiers de Topologie et Géométrie
  Différentielle Catégoriques **27** (1986), 81–83.
* E. Riehl and D. Verity, *Elements of ∞-Category Theory*, Proposition 3.3.4, Observation 3.3.6,
  and Remark 3.3.8.
-/

public section

open CategoryTheory
open scoped Simplicial

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-! ### Endpoint-preserving morphism properties -/

/-- The property of a morphism in `SimplexCategory` preserving the initial vertex `0`. -/
def preservesZero : MorphismProperty _root_.SimplexCategory :=
  fun {_ _} f ↦ f.toOrderHom 0 = 0

/-- The property of a morphism in `SimplexCategory` preserving the final vertex `Fin.last`. -/
def preservesLast : MorphismProperty _root_.SimplexCategory :=
  fun {x y} f ↦ f.toOrderHom (Fin.last x.len) = Fin.last y.len

/-- The property of a morphism in `SimplexCategory` preserving both endpoints `0` and
`Fin.last`. -/
def preservesEndpoints : MorphismProperty _root_.SimplexCategory :=
  preservesZero ⊓ preservesLast

instance : preservesZero.IsMultiplicative where
  id_mem _ := rfl
  comp_mem _ _ hf hg := (congrArg _ hf).trans hg

instance : preservesLast.IsMultiplicative where
  id_mem _ := rfl
  comp_mem _ _ hf hg := (congrArg _ hf).trans hg

instance : preservesEndpoints.IsMultiplicative :=
  inferInstanceAs ((preservesZero ⊓ preservesLast).IsMultiplicative)

end TauCeti.SimplexCategory

namespace SimplexCategory.Hom

open TauCeti.SimplexCategory

/-- Characterization of `TauCeti.SimplexCategory.preservesZero`: `f` preserves the initial
vertex `0`. -/
theorem preservesZero_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesZero f ↔ f.toOrderHom 0 = 0 :=
  Iff.rfl

/-- Characterization of `TauCeti.SimplexCategory.preservesLast`: `f` preserves the final
vertex `Fin.last`. -/
theorem preservesLast_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesLast f ↔ f.toOrderHom (Fin.last x.len) = Fin.last y.len :=
  Iff.rfl

/-- Characterization of `TauCeti.SimplexCategory.preservesEndpoints`: `f` preserves both `0` and
`Fin.last`. -/
theorem preservesEndpoints_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesEndpoints f ↔
      f.toOrderHom 0 = 0 ∧ f.toOrderHom (Fin.last x.len) = Fin.last y.len :=
  Iff.rfl

/-- Reversal exchanges `preservesZero` with `preservesLast`. -/
@[simp]
theorem preservesZero_rev_map_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesZero (SimplexCategory.rev.map f) ↔ preservesLast f := by
  simp only [preservesZero_iff, preservesLast_iff, SimplexCategory.rev_map_apply,
    SimplexCategory.rev_obj, ← Fin.rev_last, Fin.rev_rev, Fin.rev_inj]

/-- Reversal exchanges `preservesLast` with `preservesZero`. -/
@[simp]
theorem preservesLast_rev_map_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesLast (SimplexCategory.rev.map f) ↔ preservesZero f := by
  simp only [preservesLast_iff, preservesZero_iff, SimplexCategory.rev_map_apply,
    SimplexCategory.rev_obj, ← Fin.rev_zero, Fin.rev_rev, Fin.rev_inj]

/-- Reversal preserves `preservesEndpoints`. -/
@[simp]
theorem preservesEndpoints_rev_map_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesEndpoints (SimplexCategory.rev.map f) ↔ preservesEndpoints f :=
  ((preservesZero_rev_map_iff f).and (preservesLast_rev_map_iff f)).trans and_comm

end SimplexCategory.Hom

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-- A coface map `δ i` preserves `0` if and only if it does not omit vertex `0` (`i ≠ 0`). -/
@[simp]
theorem preservesZero_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesZero (δ i) ↔ i ≠ 0 := by
  simp only [Hom.preservesZero_iff, δ, mkHom, Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  exact ⟨fun h hi ↦ by simp [hi] at h, fun hi ↦ Fin.succAbove_ne_zero_zero hi⟩

/-- A coface map `δ i` preserves `Fin.last` if and only if it does not omit the last vertex
(`i ≠ Fin.last (n + 1)`). -/
@[simp]
theorem preservesLast_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesLast (δ i) ↔ i ≠ Fin.last (n + 1) := by
  simp only [Hom.preservesLast_iff, δ, mkHom, Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, len_mk]
  exact ⟨fun h hi ↦ by simp [hi, Fin.ext_iff] at h, fun hi ↦ Fin.succAbove_ne_last_last hi⟩

/-- A coface map `δ i` preserves both endpoints if and only if it omits a strictly interior
vertex (`i ≠ 0 ∧ i ≠ Fin.last (n + 1)`). -/
@[simp]
theorem preservesEndpoints_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesEndpoints (δ i) ↔ i ≠ 0 ∧ i ≠ Fin.last (n + 1) := by
  rw [Hom.preservesEndpoints_iff, ← Hom.preservesZero_iff, ← Hom.preservesLast_iff,
    preservesZero_δ_iff, preservesLast_δ_iff]

/-- Every codegeneracy map `σ i` preserves `0`. -/
@[simp]
theorem preservesZero_σ {n : ℕ} (i : Fin (n + 1)) : preservesZero (σ i) := by
  rw [Hom.preservesZero_iff]
  exact Fin.predAbove_right_zero (i := i)

/-- Every codegeneracy map `σ i` preserves `Fin.last`. -/
@[simp]
theorem preservesLast_σ {n : ℕ} (i : Fin (n + 1)) : preservesLast (σ i) := by
  rw [Hom.preservesLast_iff]
  exact Fin.predAbove_right_last

/-- Every codegeneracy map `σ i` preserves both endpoints `0` and `Fin.last`. -/
@[simp]
theorem preservesEndpoints_σ {n : ℕ} (i : Fin (n + 1)) : preservesEndpoints (σ i) :=
  ⟨preservesZero_σ i, preservesLast_σ i⟩

/-- The constant morphism at `0` preserves the initial vertex `0`. -/
theorem preservesZero_const_zero (x y : _root_.SimplexCategory) :
    preservesZero (const x y 0) :=
  (Hom.preservesZero_iff _).mpr rfl

/-- The constant morphism at `Fin.last y.len` preserves the final vertex. -/
theorem preservesLast_const_last (x y : _root_.SimplexCategory) :
    preservesLast (const x y (Fin.last y.len)) :=
  (Hom.preservesLast_iff _).mpr rfl

/-- The unique morphism `x ⟶ ⦋0⦌` preserves both endpoints. -/
@[simp]
theorem preservesEndpoints_const_to_zero (x : _root_.SimplexCategory) :
    preservesEndpoints (const x ⦋0⦌ 0) :=
  ⟨preservesZero_const_zero x ⦋0⦌,
    (Hom.preservesLast_iff _).mpr (Subsingleton.elim (α := Fin 1) _ _)⟩

/-! ### Endpoint wide subcategories -/

/-- The wide subcategory `Δ_top` of `SimplexCategory` whose morphisms preserve the greatest
element `Fin.last`. -/
abbrev LastPreserving : Type := WideSubcategory preservesLast

/-- The wide subcategory `Δ_bot` of `SimplexCategory` whose morphisms preserve the least element
`0`. -/
abbrev ZeroPreserving : Type := WideSubcategory preservesZero

/-- The wide subcategory `Δ_∂` of `SimplexCategory` (including `⦋0⦌`) whose morphisms preserve both
endpoints `0` and `Fin.last`. -/
abbrev EndpointPreserving : Type := WideSubcategory preservesEndpoints

namespace LastPreserving

/-- Construct a morphism in `LastPreserving` from a morphism in `SimplexCategory` preserving the
greatest element. -/
def homMk {x y : LastPreserving} (f : x.obj ⟶ y.obj)
    (hf : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) : x ⟶ y :=
  ⟨f, hf⟩

/-- Underlying simplex-category morphism of `LastPreserving.homMk`. -/
@[simp]
theorem homMk_hom {x y : LastPreserving} (f : x.obj ⟶ y.obj)
    (hf : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) :
    (homMk f hf).hom = f :=
  (rfl)

/-- A morphism in `LastPreserving` fixes `Fin.last`. -/
@[simp]
theorem toOrderHom_last {x y : LastPreserving} (f : x ⟶ y) :
    f.hom.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len :=
  f.property

/-- Restricted coface maps `δ i.castSucc : ⦋n⦌ ⟶ ⦋n + 1⦌` in `Δ_top`, omitting a non-last
vertex. -/
def δ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n⦌⟩ : LastPreserving) ⟶ ⟨⦋n + 1⦌⟩ :=
  ⟨_root_.SimplexCategory.δ i.castSucc,
    (preservesLast_δ_iff i.castSucc).mpr (Fin.castSucc_lt_last i).ne⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_top`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : LastPreserving) ⟶ ⟨⦋n⦌⟩ :=
  ⟨_root_.SimplexCategory.σ i, preservesLast_σ i⟩

/-- Underlying simplex-category coface map of `LastPreserving.δ`. -/
@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) :
    (LastPreserving.δ i).hom = _root_.SimplexCategory.δ i.castSucc :=
  (rfl)

/-- Underlying simplex-category codegeneracy map of `LastPreserving.σ`. -/
@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) :
    (LastPreserving.σ i).hom = _root_.SimplexCategory.σ i :=
  (rfl)

/-- `⟨⦋0⦌⟩` is terminal in `LastPreserving`. -/
instance {x : LastPreserving} : Unique (x ⟶ ⟨⦋0⦌⟩) where
  default := ⟨const x.obj ⦋0⦌ 0,
    (Hom.preservesLast_iff _).mpr
      ((Hom.preservesEndpoints_iff _).mp (preservesEndpoints_const_to_zero x.obj)).2⟩
  uniq f := WideSubcategory.hom_ext _ (eq_const_to_zero f.hom)

/-- `LastPreserving.δ 0` sends `0` to `1 ≠ 0`, witnessing that `Δ_∂` is strictly contained in
`Δ_top`. -/
theorem δ_zero_hom_toOrderHom_zero_eq_one :
    (LastPreserving.δ (0 : Fin 1)).hom.toOrderHom 0 = 1 :=
  (rfl)

end LastPreserving

namespace ZeroPreserving

/-- Construct a morphism in `ZeroPreserving` from a morphism in `SimplexCategory` preserving
`0`. -/
def homMk {x y : ZeroPreserving} (f : x.obj ⟶ y.obj) (hf : f.toOrderHom 0 = 0) : x ⟶ y :=
  ⟨f, hf⟩

/-- Underlying simplex-category morphism of `ZeroPreserving.homMk`. -/
@[simp]
theorem homMk_hom {x y : ZeroPreserving} (f : x.obj ⟶ y.obj) (hf : f.toOrderHom 0 = 0) :
    (homMk f hf).hom = f :=
  (rfl)

/-- A morphism in `ZeroPreserving` fixes `0`. -/
@[simp]
theorem toOrderHom_zero {x y : ZeroPreserving} (f : x ⟶ y) : f.hom.toOrderHom 0 = 0 :=
  f.property

/-- Restricted coface maps `δ i.succ : ⦋n⦌ ⟶ ⦋n + 1⦌` in `Δ_bot`, omitting a nonzero vertex. -/
def δ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n⦌⟩ : ZeroPreserving) ⟶ ⟨⦋n + 1⦌⟩ :=
  ⟨_root_.SimplexCategory.δ i.succ, (preservesZero_δ_iff i.succ).mpr (Fin.succ_ne_zero i)⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_bot`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : ZeroPreserving) ⟶ ⟨⦋n⦌⟩ :=
  ⟨_root_.SimplexCategory.σ i, preservesZero_σ i⟩

/-- Underlying simplex-category coface map of `ZeroPreserving.δ`. -/
@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) :
    (ZeroPreserving.δ i).hom = _root_.SimplexCategory.δ i.succ :=
  (rfl)

/-- Underlying simplex-category codegeneracy map of `ZeroPreserving.σ`. -/
@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) :
    (ZeroPreserving.σ i).hom = _root_.SimplexCategory.σ i :=
  (rfl)

/-- `⟨⦋0⦌⟩` is terminal in `ZeroPreserving`. -/
instance {x : ZeroPreserving} : Unique (x ⟶ ⟨⦋0⦌⟩) where
  default := ⟨const x.obj ⦋0⦌ 0, preservesZero_const_zero x.obj ⦋0⦌⟩
  uniq f := WideSubcategory.hom_ext _ (eq_const_to_zero f.hom)

end ZeroPreserving

namespace EndpointPreserving

/-- The faithful inclusion `Δ_∂ ⥤ Δ_top`. -/
@[expose] def toLastPreserving : EndpointPreserving ⥤ LastPreserving where
  obj x := ⟨x.obj⟩
  map f := ⟨f.hom,
    (Hom.preservesLast_iff f.hom).mpr ((Hom.preservesEndpoints_iff f.hom).mp f.property).2⟩

instance : toLastPreserving.Faithful where
  map_injective h := WideSubcategory.hom_ext _ (congrArg (fun g ↦ g.hom) h)

/-- Object map of `EndpointPreserving.toLastPreserving`. -/
@[simp]
theorem toLastPreserving_obj (x : EndpointPreserving) : toLastPreserving.obj x = ⟨x.obj⟩ := (rfl)

/-- Morphism projection of `EndpointPreserving.toLastPreserving`. -/
@[simp]
theorem toLastPreserving_map_hom {x y : EndpointPreserving} (f : x ⟶ y) :
    (toLastPreserving.map f).hom = f.hom := (rfl)

/-- Composing `toLastPreserving` with the inclusion of `LastPreserving` into `SimplexCategory`
recovers the inclusion of `EndpointPreserving`. -/
@[simp]
theorem toLastPreserving_comp_inclusion :
    toLastPreserving ⋙ wideSubcategoryInclusion preservesLast =
      wideSubcategoryInclusion preservesEndpoints := (rfl)

/-- The faithful inclusion `Δ_∂ ⥤ Δ_bot`. -/
@[expose] def toZeroPreserving : EndpointPreserving ⥤ ZeroPreserving where
  obj x := ⟨x.obj⟩
  map f := ⟨f.hom,
    (Hom.preservesZero_iff f.hom).mpr ((Hom.preservesEndpoints_iff f.hom).mp f.property).1⟩

instance : toZeroPreserving.Faithful where
  map_injective h := WideSubcategory.hom_ext _ (congrArg (fun g ↦ g.hom) h)

/-- Object map of `EndpointPreserving.toZeroPreserving`. -/
@[simp]
theorem toZeroPreserving_obj (x : EndpointPreserving) : toZeroPreserving.obj x = ⟨x.obj⟩ := (rfl)

/-- Morphism projection of `EndpointPreserving.toZeroPreserving`. -/
@[simp]
theorem toZeroPreserving_map_hom {x y : EndpointPreserving} (f : x ⟶ y) :
    (toZeroPreserving.map f).hom = f.hom := (rfl)

/-- Composing `toZeroPreserving` with the inclusion of `ZeroPreserving` into `SimplexCategory`
recovers the inclusion of `EndpointPreserving`. -/
@[simp]
theorem toZeroPreserving_comp_inclusion :
    toZeroPreserving ⋙ wideSubcategoryInclusion preservesZero =
      wideSubcategoryInclusion preservesEndpoints := (rfl)

/-- Construct a morphism in `EndpointPreserving` from a morphism in `SimplexCategory` preserving
both endpoints `0` and `Fin.last`. -/
def homMk {x y : EndpointPreserving} (f : x.obj ⟶ y.obj) (h0 : f.toOrderHom 0 = 0)
    (hlast : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) : x ⟶ y :=
  ⟨f, ⟨h0, hlast⟩⟩

/-- Underlying simplex-category morphism of `EndpointPreserving.homMk`. -/
@[simp]
theorem homMk_hom {x y : EndpointPreserving} (f : x.obj ⟶ y.obj) (h0 : f.toOrderHom 0 = 0)
    (hlast : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) :
    (homMk f h0 hlast).hom = f :=
  (rfl)

/-- A morphism in `EndpointPreserving` fixes `0`. -/
@[simp]
theorem toOrderHom_zero {x y : EndpointPreserving} (f : x ⟶ y) : f.hom.toOrderHom 0 = 0 :=
  f.property.1

/-- A morphism in `EndpointPreserving` fixes `Fin.last`. -/
@[simp]
theorem toOrderHom_last {x y : EndpointPreserving} (f : x ⟶ y) :
    f.hom.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len :=
  f.property.2

/-- Restricted inner coface maps `δ i.succ.castSucc : ⦋n + 1⦌ ⟶ ⦋n + 2⦌` in `Δ_∂`, omitting
a strictly interior vertex. -/
def δ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋n + 2⦌⟩ :=
  ⟨_root_.SimplexCategory.δ i.succ.castSucc, (preservesEndpoints_δ_iff i.succ.castSucc).mpr
    ⟨Fin.castSucc_ne_zero_iff.mpr (Fin.succ_ne_zero i),
      (Fin.castSucc_lt_last i.succ).ne⟩⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_∂`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : EndpointPreserving) ⟶ ⟨⦋n⦌⟩ :=
  ⟨_root_.SimplexCategory.σ i, preservesEndpoints_σ i⟩

/-- Underlying simplex-category coface map of `EndpointPreserving.δ`. -/
@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) :
    (EndpointPreserving.δ i).hom = _root_.SimplexCategory.δ i.succ.castSucc :=
  (rfl)

/-- Underlying simplex-category codegeneracy map of `EndpointPreserving.σ`. -/
@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) :
    (EndpointPreserving.σ i).hom = _root_.SimplexCategory.σ i :=
  (rfl)

/-- The unique morphism to the terminal object `⟨⦋0⦌⟩` in `EndpointPreserving`. -/
def constToZero (x : _root_.SimplexCategory) : (⟨x⟩ : EndpointPreserving) ⟶ ⟨⦋0⦌⟩ :=
  ⟨const x ⦋0⦌ 0, preservesEndpoints_const_to_zero x⟩

/-- Underlying simplex-category morphism of `EndpointPreserving.constToZero`. -/
@[simp]
theorem constToZero_hom (x : _root_.SimplexCategory) : (constToZero x).hom = const x ⦋0⦌ 0 :=
  (rfl)

/-- `⟨⦋0⦌⟩` is terminal in `EndpointPreserving`. -/
instance {x : EndpointPreserving} : Unique (x ⟶ ⟨⦋0⦌⟩) where
  default := constToZero x.obj
  uniq f := WideSubcategory.hom_ext _ ((eq_const_to_zero f.hom).trans (constToZero_hom x.obj).symm)

/-- There is no endpoint-preserving map `⦋0⦌ ⟶ ⦋m + 1⦌`. -/
theorem isEmpty_hom_zero_succ (m : ℕ) : IsEmpty ((⟨⦋0⦌⟩ : EndpointPreserving) ⟶ ⟨⦋m + 1⦌⟩) :=
  ⟨fun f ↦ by
    have h0 : f.hom.toOrderHom 0 = 0 := toOrderHom_zero f
    have hl : f.hom.toOrderHom 0 = Fin.last (m + 1) := by simpa using toOrderHom_last f
    exact (Fin.last_pos (n := m)).ne' (hl.symm.trans h0)⟩

end EndpointPreserving

end TauCeti.SimplexCategory
