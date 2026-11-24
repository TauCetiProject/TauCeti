/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.Topology.Category.TopCat.Monoidal

/-!
# Fibre inclusions of trivializations in `TopCat`

For a morphism `p : E ⟶ B` in `TopCat`, a trivialization `t` of `p` with model fibre `F` and a point
`x` of the base set of `t`, `TopCat.trivializationFiberInclusion t hx : F ⟶ E` is the inclusion
`f ↦ t⁻¹(x, f)` of the model fibre as the fibre of `p` over `x`, built from Mathlib's
`Bundle.Trivialization.preimageSingletonHomeomorph`. Its composite with `p` is the constant map at
`x`.

Over a subset `S` of the base set of `t`, `TopCat.trivializationPreimageIso t hS : S ⊗ F ≅ p⁻¹ S`
is the homeomorphism `p⁻¹ S ≃ S × F` of `t` as an isomorphism in `TopCat`. It identifies the
restriction of `p` over `S` with the first projection
(`TopCat.trivializationPreimageIso_hom_comp`), and the fibre inclusion `TopCat.prodFiberInclusion`
of `S × F` at `x` with the fibre inclusion of `t` over `x`
(`TopCat.prodFiberInclusion_comp_trivializationPreimageIso_hom`).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

namespace TopCat

variable {E B F : TopCat.{u}} {p : E ⟶ B}

/-- The inclusion `f ↦ t⁻¹(x, f)` of the model fibre `F` into `E` as the fibre of `p` over a point
`x` of the base set of a trivialization `t` of `p`. -/
def trivializationFiberInclusion (t : Bundle.Trivialization F p) {x : B} (hx : x ∈ t.baseSet) :
    F ⟶ E :=
  ofHom ((ContinuousMap.subtypeVal (p ⁻¹' {x})).comp (t.preimageSingletonHomeomorph hx).symm)

@[simp]
theorem trivializationFiberInclusion_apply (t : Bundle.Trivialization F p) {x : B}
    (hx : x ∈ t.baseSet) (f : F) :
    trivializationFiberInclusion t hx f = t.toOpenPartialHomeomorph.symm (x, f) := (rfl)

/-- The fibre inclusion of a trivialization lies over the constant map at `x`. -/
@[reassoc (attr := simp)]
theorem trivializationFiberInclusion_comp (t : Bundle.Trivialization F p) {x : B}
    (hx : x ∈ t.baseSet) : trivializationFiberInclusion t hx ≫ p = TopCat.const x := by
  ext f
  rw [ConcreteCategory.comp_apply, trivializationFiberInclusion_apply, TopCat.const_apply]
  exact t.proj_symm_apply' hx

/-- Over a subset `S` of the base set of a trivialization `t` of `p`, the isomorphism
`S × F ≅ p⁻¹ S` in `TopCat` given by the homeomorphism `p⁻¹ S ≃ S × F` of `t`. -/
def trivializationPreimageIso (t : Bundle.Trivialization F p) {S : Set B} (hS : S ⊆ t.baseSet) :
    of S ⊗ F ≅ of (p ⁻¹' S) :=
  isoOfHomeo (t.preimageHomeomorph hS).symm

@[simp]
theorem trivializationPreimageIso_hom_apply (t : Bundle.Trivialization F p) {S : Set B}
    (hS : S ⊆ t.baseSet) (y : ↑(of S ⊗ F)) :
    (trivializationPreimageIso t hS).hom y = (t.preimageHomeomorph hS).symm (y.1, y.2) := (rfl)

/-- The isomorphism `S × F ≅ p⁻¹ S` of a trivialization lies over `S`: followed by the restriction
of `p` over `S`, it is the first projection. -/
@[reassoc (attr := simp)]
theorem trivializationPreimageIso_hom_comp (t : Bundle.Trivialization F p) {S : Set B}
    (hS : S ⊆ t.baseSet) :
    (trivializationPreimageIso t hS).hom ≫ ofHom (p.hom.restrictPreimage S) = fst (of S) F := by
  ext y
  rw [ConcreteCategory.comp_apply, trivializationPreimageIso_hom_apply]
  -- The restriction of `p` applies `p` to the point `t⁻¹(y.1, y.2)`, and `fst` sends `y` to `y.1`.
  exact t.proj_symm_apply' (hS y.1.property)

/-- Over a subset `S` of the base set of a trivialization `t`, the fibre inclusion
`f ↦ (x, f)` of `S × F`, followed by the isomorphism `S × F ≅ p⁻¹ S` of `t` and the inclusion of
`p⁻¹ S` into `E`, is the fibre inclusion of `t` over `x`. -/
@[reassoc (attr := simp)]
theorem prodFiberInclusion_comp_trivializationPreimageIso_hom (t : Bundle.Trivialization F p)
    {S : Set B} (hS : S ⊆ t.baseSet) (x : S) :
    prodFiberInclusion (of S) F x ≫ (trivializationPreimageIso t hS).hom ≫
        ofHom (ContinuousMap.subtypeVal (p ⁻¹' S)) =
      trivializationFiberInclusion t (hS x.property) := by
  ext f
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    trivializationPreimageIso_hom_apply, prodFiberInclusion_apply,
    trivializationFiberInclusion_apply, t.preimageHomeomorph_symm_apply]
  simp only [ConcreteCategory.hom_ofHom, ContinuousMap.subtypeVal_apply]

end TopCat
