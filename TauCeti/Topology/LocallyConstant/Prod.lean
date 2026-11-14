/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Products of locally constant functions

Two locally constant functions `f : LocallyConstant X Y` and `g : LocallyConstant X Z` assemble
into a locally constant function `f.prodMk g : LocallyConstant X (Y × Z)` via
`IsLocallyConstant.prodMk`. Together with postcomposition by the coordinate projections, this
identifies `LocallyConstant X (Y × Z)` with `LocallyConstant X Y × LocallyConstant X Z`
(`LocallyConstant.prodEquiv`), and gives two-argument pushforward `LocallyConstant.map₂`.
-/

public section

namespace LocallyConstant

variable {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X]

/-- Pair two locally constant functions on a common domain into a product-valued locally constant
function. -/
-- Expose so dependent families indexed by `(f.prodMk g) x` reduce to `(f x, g x)`.
@[expose, implicit_reducible]
def prodMk (f : LocallyConstant X Y) (g : LocallyConstant X Z) : LocallyConstant X (Y × Z) :=
  ⟨fun x ↦ (f x, g x), f.isLocallyConstant.prodMk g.isLocallyConstant⟩

@[simp]
theorem coe_prodMk (f : LocallyConstant X Y) (g : LocallyConstant X Z) :
    ⇑(f.prodMk g) = fun x ↦ (f x, g x) :=
  (rfl)

theorem prodMk_apply (f : LocallyConstant X Y) (g : LocallyConstant X Z) (x : X) :
    f.prodMk g x = (f x, g x) :=
  (rfl)

@[simp]
theorem map_fst_prodMk (f : LocallyConstant X Y) (g : LocallyConstant X Z) :
    (f.prodMk g).map Prod.fst = f :=
  ext fun _ ↦ rfl

@[simp]
theorem map_snd_prodMk (f : LocallyConstant X Y) (g : LocallyConstant X Z) :
    (f.prodMk g).map Prod.snd = g :=
  ext fun _ ↦ rfl

@[simp]
theorem prodMk_map_fst_map_snd (h : LocallyConstant X (Y × Z)) :
    (h.map Prod.fst).prodMk (h.map Prod.snd) = h :=
  ext fun _ ↦ rfl

@[simp]
theorem comap_prodMk (k : C(W, X)) (f : LocallyConstant X Y) (g : LocallyConstant X Z) :
    (f.prodMk g).comap k = (f.comap k).prodMk (g.comap k) :=
  ext fun _ ↦ rfl

@[simp]
theorem const_prodMk_const (y : Y) (z : Z) :
    (const X y).prodMk (const X z) = const X (y, z) :=
  ext fun _ ↦ rfl

/-- Locally constant functions into a product correspond to pairs of locally constant functions. -/
def prodEquiv : LocallyConstant X (Y × Z) ≃ LocallyConstant X Y × LocallyConstant X Z where
  toFun h := (h.map Prod.fst, h.map Prod.snd)
  invFun p := p.1.prodMk p.2
  left_inv := prodMk_map_fst_map_snd
  right_inv _ := Prod.ext (map_fst_prodMk _ _) (map_snd_prodMk _ _)

@[simp]
theorem prodEquiv_apply (h : LocallyConstant X (Y × Z)) :
    prodEquiv h = (h.map Prod.fst, h.map Prod.snd) :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (p : LocallyConstant X Y × LocallyConstant X Z) :
    prodEquiv.symm p = p.1.prodMk p.2 :=
  (rfl)

/-- Push forward two locally constant functions along a two-argument map. -/
-- Expose so dependent families indexed by `(map₂ h f g) x` reduce to `h (f x) (g x)`.
@[expose, implicit_reducible]
def map₂ {V : Type*} (h : Y → Z → V) (f : LocallyConstant X Y) (g : LocallyConstant X Z) :
    LocallyConstant X V :=
  ⟨fun x ↦ h (f x) (g x), (f.prodMk g).isLocallyConstant.comp (Function.uncurry h)⟩

@[simp]
theorem coe_map₂ {V : Type*} (h : Y → Z → V) (f : LocallyConstant X Y)
    (g : LocallyConstant X Z) : ⇑(map₂ h f g) = fun x ↦ h (f x) (g x) :=
  (rfl)

theorem map₂_apply {V : Type*} (h : Y → Z → V) (f : LocallyConstant X Y)
    (g : LocallyConstant X Z) (x : X) : map₂ h f g x = h (f x) (g x) :=
  (rfl)

@[simp]
theorem comap_map₂ {V : Type*} (k : C(W, X)) (h : Y → Z → V) (f : LocallyConstant X Y)
    (g : LocallyConstant X Z) :
    (map₂ h f g).comap k = map₂ h (f.comap k) (g.comap k) :=
  ext fun _ ↦ rfl

end LocallyConstant
