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
`x`, `t` sends it back to `(x, f)`, and over a subset `S` of the base set it is the fibre inclusion
`TopCat.prodFiberInclusion` of `S × F` read through the homeomorphism `p⁻¹ S ≃ S × F` of `t`
(`TopCat.prodFiberInclusion_comp_preimageHomeomorph_symm`).
-/

public section

open CategoryTheory MonoidalCategory

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

/-- The trivialization `t` sends the image of `f` under its fibre inclusion over `x` to `(x, f)`. -/
theorem apply_trivializationFiberInclusion (t : Bundle.Trivialization F p) {x : B}
    (hx : x ∈ t.baseSet) (f : F) : t (trivializationFiberInclusion t hx f) = (x, f) := by
  rw [trivializationFiberInclusion_apply]
  exact t.apply_symm_apply' hx

/-- Over a subset `S` of the base set of a trivialization `t`, the fibre inclusion
`f ↦ (x, f)` of `S × F`, followed by the homeomorphism `S × F ≃ p⁻¹ S` of `t` and the inclusion of
`p⁻¹ S` into `E`, is the fibre inclusion of `t` over `x`. -/
theorem prodFiberInclusion_comp_preimageHomeomorph_symm (t : Bundle.Trivialization F p)
    {S : Set B} (hS : S ⊆ t.baseSet) (x : S) :
    prodFiberInclusion (of S) F x ≫ (isoOfHomeo (t.preimageHomeomorph hS).symm).hom ≫
        ofHom (ContinuousMap.subtypeVal (p ⁻¹' S)) =
      trivializationFiberInclusion t (hS x.property) := by
  ext f
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, prodFiberInclusion_apply,
    trivializationFiberInclusion_apply]
  -- `isoOfHomeo h` applies `h`; the carrier of `of S ⊗ F` is `S × F` only up to unfolding.
  change ((t.preimageHomeomorph hS).symm (x, f)).val = _
  rw [t.preimageHomeomorph_symm_apply]

end TopCat
