/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.RepresentationTheory.FunLeft

/-!
# The representation of a group on smooth functions

Let a group `G` act on a manifold `M` by `C^n` maps. Then `G` acts linearly on the `C^n` maps
`f : M → F` into a normed space by translating the argument, `(g • f) x = f (g⁻¹ • x)`; this is
the representation `TauCeti.smoothFunctionRep`, the restriction to `C^n` maps of the translation
representation `Representation.funLeft` on all functions. Its invariant vectors are the `C^n` maps
constant on orbits, and restricting it to a subgroup gives the representation of the subgroup.
The smooth functions on an orbit space are identified with its invariant vectors in
`TauCeti.Geometry.Manifold.Quotient.SmoothFunctions`.

## Main definitions and results

* `TauCeti.smoothFunctionRep`: the representation `(g • f) x = f (g⁻¹ • x)` of `G` on the `C^n`
  maps `M → F`.
* `TauCeti.mem_invariants_smoothFunctionRep_iff`: its invariant vectors are the maps with
  `f (g • x) = f x`.
* `TauCeti.smoothFunctionRep_comp_subtype`: its restriction to a subgroup `K` is the
  representation of `K`.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}
  {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I n G M]

variable (𝕜 I M F n G) in
/-- The representation of `G` on the `C^n` maps `f : M → F` by translation of the argument,
`(g • f) x = f (g⁻¹ • x)`. -/
def smoothFunctionRep : Representation 𝕜 G C^n⟮I, M; 𝓘(𝕜, F), F⟯ where
  toFun g :=
    { toFun f := ⟨fun x ↦ f (g⁻¹ • x), f.contMDiff.comp (contMDiff_const_smul g⁻¹)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := LinearMap.ext fun f ↦ ContMDiffMap.ext fun x ↦ congrArg f (by rw [inv_one, one_smul])
  map_mul' g h := LinearMap.ext fun f ↦ ContMDiffMap.ext fun x ↦
    congrArg f (by rw [mul_inv_rev, mul_smul])

@[simp]
theorem smoothFunctionRep_apply_apply (g : G) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x : M) :
    smoothFunctionRep 𝕜 I M F n G g f x = f (g⁻¹ • x) :=
  (rfl)

/-- On underlying functions, `TauCeti.smoothFunctionRep` is the translation representation
`Representation.funLeft` of `G` on all functions `M → F`, for the trivial action on `F`. -/
theorem coe_smoothFunctionRep_apply (g : G) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    ⇑(smoothFunctionRep 𝕜 I M F n G g f) = (Representation.trivial 𝕜 G F).funLeft M g f := by
  ext x
  simp

/-- The invariant vectors of `TauCeti.smoothFunctionRep` are the `C^n` maps that are constant on
the orbits of `G`. It has `high` priority so that `simp` prefers it to the generic
`Representation.mem_invariants`. -/
@[simp high]
theorem mem_invariants_smoothFunctionRep_iff {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} :
    f ∈ (smoothFunctionRep 𝕜 I M F n G).invariants ↔ ∀ (g : G) (x : M), f (g • x) = f x := by
  rw [Representation.mem_invariants]
  refine ⟨fun h g x ↦ ?_, fun h g ↦ ContMDiffMap.ext fun x ↦ ?_⟩
  · simpa using DFunLike.congr_fun (h g⁻¹) x
  · simpa using h g⁻¹ x

/-- Restricting `TauCeti.smoothFunctionRep` to a subgroup `K` gives the representation of `K`
acting on `M` by restriction. -/
@[simp]
theorem smoothFunctionRep_comp_subtype (K : Subgroup G) :
    (smoothFunctionRep 𝕜 I M F n G).comp K.subtype = smoothFunctionRep 𝕜 I M F n K :=
  MonoidHom.ext fun k ↦ LinearMap.ext fun f ↦ ContMDiffMap.ext fun x ↦ by simp [Subgroup.smul_def]

end TauCeti
