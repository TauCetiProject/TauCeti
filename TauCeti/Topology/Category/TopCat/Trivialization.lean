/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.Topology.Category.TopCat.Fiber
public import TauCeti.Topology.Category.TopCat.Monoidal

/-!
# Fibre inclusions of trivializations in `TopCat`

For a morphism `p : E ⟶ B` in `TopCat`, a trivialization `t` of `p` with model fibre `F` and a point
`x` of the base set of `t`, `Bundle.Trivialization.fiberInclusion t hx : F ⟶ E` is the inclusion
`f ↦ t⁻¹(x, f)` of the model fibre as the fibre of `p` over `x`: Mathlib's
`Bundle.Trivialization.preimageSingletonHomeomorph` followed by the fibre inclusion
`TopCat.Hom.fiberι`. Its composite with `p` is the constant map at
`x`.

Over a subset `S` of the base set of `t`, `Bundle.Trivialization.preimageIso t hS : S ⊗ F ≅ p⁻¹ S`
is the homeomorphism `p⁻¹ S ≃ S × F` of `t` as an isomorphism in `TopCat`. It identifies the
restriction of `p` over `S` with the first projection
(`Bundle.Trivialization.preimageIso_hom_comp`), and the fibre inclusion
`TopCat.prodFiberInclusion` of `S × F` at `x` with the fibre inclusion of `t` over `x`
(`Bundle.Trivialization.prodFiberInclusion_comp_preimageIso_hom`).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory TopCat

universe u

namespace Bundle.Trivialization

variable {E B F : TopCat.{u}} {p : E ⟶ B}

/-- The inclusion `f ↦ t⁻¹(x, f)` of the model fibre `F` into `E` as the fibre of `p` over a point
`x` of the base set of a trivialization `t` of `p`. -/
def fiberInclusion (t : Bundle.Trivialization F p) {x : B} (hx : x ∈ t.baseSet) : F ⟶ E :=
  (isoOfHomeo (t.preimageSingletonHomeomorph hx)).inv ≫ p.fiberι x

@[simp]
theorem fiberInclusion_apply (t : Bundle.Trivialization F p) {x : B} (hx : x ∈ t.baseSet) (f : F) :
    t.fiberInclusion hx f = t.toOpenPartialHomeomorph.symm (x, f) := by
  rw [fiberInclusion, ConcreteCategory.comp_apply, Hom.fiberι_apply]
  exact congrArg Subtype.val (t.preimageSingletonHomeomorph_symm_apply hx f)

/-- The fibre inclusion of a trivialization lies over the constant map at `x`. -/
@[reassoc (attr := simp)]
theorem fiberInclusion_comp (t : Bundle.Trivialization F p) {x : B} (hx : x ∈ t.baseSet) :
    t.fiberInclusion hx ≫ p = TopCat.const x := by
  rw [fiberInclusion, Category.assoc, Hom.fiberι_comp]
  ext f
  rw [ConcreteCategory.comp_apply, TopCat.const_apply, TopCat.const_apply]

/-- Over a subset `S` of the base set of a trivialization `t` of `p`, the isomorphism
`S × F ≅ p⁻¹ S` in `TopCat` given by the homeomorphism `p⁻¹ S ≃ S × F` of `t`. -/
def preimageIso (t : Bundle.Trivialization F p) {S : Set B} (hS : S ⊆ t.baseSet) :
    of S ⊗ F ≅ of (p ⁻¹' S) :=
  isoOfHomeo (t.preimageHomeomorph hS).symm

/-- The continuous map underlying `(t.preimageIso hS).hom` is `y ↦ t⁻¹(y.1, y.2)`. This is the
form `simp` uses: a lemma about `(t.preimageIso hS).hom y` itself is not found by `simp`, because
the carrier of `of S ⊗ F` is not reducibly `S × F`. -/
@[simp]
theorem hom_preimageIso_hom (t : Bundle.Trivialization F p) {S : Set B} (hS : S ⊆ t.baseSet) :
    (t.preimageIso hS).hom.hom =
      ⟨fun y ↦ (t.preimageHomeomorph hS).symm (y.1, y.2),
        (t.preimageHomeomorph hS).symm.continuous⟩ :=
  (rfl)

theorem preimageIso_hom_apply (t : Bundle.Trivialization F p) {S : Set B} (hS : S ⊆ t.baseSet)
    (y : ↑(of S ⊗ F)) :
    (t.preimageIso hS).hom y = (t.preimageHomeomorph hS).symm (y.1, y.2) := (rfl)

@[simp]
theorem preimageIso_inv_apply (t : Bundle.Trivialization F p) {S : Set B} (hS : S ⊆ t.baseSet)
    (y : of (p ⁻¹' S)) :
    (t.preimageIso hS).inv y = t.preimageHomeomorph hS y := (rfl)

/-- The isomorphism `S × F ≅ p⁻¹ S` of a trivialization lies over `S`: followed by the restriction
of `p` over `S`, it is the first projection. -/
@[reassoc (attr := simp)]
theorem preimageIso_hom_comp (t : Bundle.Trivialization F p) {S : Set B} (hS : S ⊆ t.baseSet) :
    (t.preimageIso hS).hom ≫ ofHom (p.hom.restrictPreimage S) = fst (of S) F := by
  ext y
  rw [ConcreteCategory.comp_apply, preimageIso_hom_apply]
  -- The restriction of `p` applies `p` to the point `t⁻¹(y.1, y.2)`, and `fst` sends `y` to `y.1`.
  exact t.proj_symm_apply' (hS y.1.property)

/-- Over a subset `S` of the base set of a trivialization `t`, the fibre inclusion
`f ↦ (x, f)` of `S × F`, followed by the isomorphism `S × F ≅ p⁻¹ S` of `t` and the inclusion of
`p⁻¹ S` into `E`, is the fibre inclusion of `t` over `x`. -/
@[reassoc (attr := simp)]
theorem prodFiberInclusion_comp_preimageIso_hom (t : Bundle.Trivialization F p) {S : Set B}
    (hS : S ⊆ t.baseSet) (x : S) :
    prodFiberInclusion (of S) F x ≫ (t.preimageIso hS).hom ≫
        ofHom (ContinuousMap.subtypeVal (p ⁻¹' S)) =
      t.fiberInclusion (hS x.property) := by
  ext f
  simp

end Bundle.Trivialization
