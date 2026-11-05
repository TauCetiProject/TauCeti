/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Pullback of orthonormal frame bundles

An orthonormal frame of the fibre of `f *ᵖ E` at `x` is precisely a frame of `E` at `f x`.
`TauCeti.OrthonormalFrameBundle.pullbackHomeomorph` identifies the frame bundle of the
pullback with the topological fibre product of `f` and the frame-bundle projection.
The comparison respects the base point, frame evaluation and the right unitary action.
The canonical map to the original frame bundle is `pullbackLift`.

The comparison uses the pointwise topology on frames and Mathlib's induced topology on
`Bundle.TotalSpace F (f *ᵖ E)`. Consequently it needs neither finite-dimensionality nor
local triviality, and even works for a base map not assumed continuous. For a continuous
map of bases and a Riemannian or Hermitian vector bundle it is the usual frame-bundle pullback
square.
In particular, the construction includes zero-dimensional fibres without choosing an
orientation sign.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Chapter 4 (pullbacks of principal bundles).
-/

public section

open Bundle MulOpposite

namespace TauCeti.OrthonormalFrameBundle

variable {𝕜 : Type*} [RCLike 𝕜] {B B' : Type*} {F : Type*} {E : B → Type*}
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The canonical map from frames of a pullback bundle to frames of the original bundle. -/
def pullbackLift (f : B' → B) (p : OrthonormalFrameBundle 𝕜 F (f *ᵖ E) V) :
    OrthonormalFrameBundle 𝕜 F E V :=
  ⟨f p.proj, p.frame⟩

@[simp]
theorem pullbackLift_mk (f : B' → B) (x : B') (φ : V ≃ₗᵢ[𝕜] E (f x)) :
    pullbackLift f (⟨x, φ⟩ : OrthonormalFrameBundle 𝕜 F (f *ᵖ E) V) = ⟨f x, φ⟩ :=
  (rfl)

@[simp]
theorem proj_pullbackLift (f : B' → B) (p : OrthonormalFrameBundle 𝕜 F (f *ᵖ E) V) :
    (pullbackLift f p).proj = f p.proj :=
  (rfl)

/-- Evaluating a lifted frame agrees with lifting its evaluation to the original total space. -/
@[simp]
theorem totalSpaceMk_pullbackLift_frame (f : B' → B)
    (p : OrthonormalFrameBundle 𝕜 F (f *ᵖ E) V) (v : V) :
    (⟨(pullbackLift f p).proj, (pullbackLift f p).frame v⟩ : TotalSpace F E) =
      Pullback.lift f (⟨p.proj, p.frame v⟩ : TotalSpace F (f *ᵖ E)) :=
  (rfl)

/-- Lifting a frame commutes with the right unitary action. -/
@[simp]
theorem pullbackLift_smul [CompleteSpace V] (f : B' → B)
    (g : (unitary (V →L[𝕜] V))ᵐᵒᵖ) (p : OrthonormalFrameBundle 𝕜 F (f *ᵖ E) V) :
    pullbackLift f (g • p) = g • pullbackLift f p :=
  (rfl)

/-- The canonical frame lift for the identity base map is the identity. -/
@[simp]
theorem pullbackLift_id (p : OrthonormalFrameBundle 𝕜 F E V) :
    pullbackLift (id : B → B) p = p := by
  cases p
  rfl

/-- The canonical lifts for successive base changes compose. -/
theorem pullbackLift_comp {B'' : Type*} (f : B' → B) (g : B'' → B')
    (p : OrthonormalFrameBundle 𝕜 F (g *ᵖ (f *ᵖ E)) V) :
    pullbackLift f (pullbackLift g p) = pullbackLift (f ∘ g) p :=
  (rfl)

variable [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)]

/-- The canonical map from the pulled-back frame bundle to the original one is continuous. -/
theorem continuous_pullbackLift (f : B' → B) :
    Continuous (pullbackLift f : OrthonormalFrameBundle 𝕜 F (f *ᵖ E) V → _) :=
  continuous_iff.2 fun v ↦ (Pullback.continuous_lift F E f).comp
    (continuous_totalSpaceMk_frame v)

/-- Frames of the pullback are homeomorphic to the fibre product of the base map and the
original frame-bundle projection. The fibre product has the subtype topology in the product
of the new base and the original frame bundle. -/
def pullbackHomeomorph (f : B' → B) :
    OrthonormalFrameBundle 𝕜 F (f *ᵖ E) V ≃ₜ
      {q : B' × OrthonormalFrameBundle 𝕜 F E V // q.2.proj = f q.1} where
  toFun p := ⟨(p.proj, pullbackLift f p), rfl⟩
  -- State the target fibre explicitly so transport uses the fibre-product equation rather
  -- than trying to rewrite through the pullback type synonym.
  invFun q := ⟨q.1.1, (q.2 ▸ q.1.2.frame : V ≃ₗᵢ[𝕜] E (f q.1.1))⟩
  left_inv p := by cases p; rfl
  right_inv q := by
    rcases q with ⟨⟨x, ⟨y, φ⟩⟩, h⟩
    dsimp only at h
    cases h
    rfl
  continuous_toFun :=
    (((Pullback.continuous_proj F E f).comp (continuous_totalSpaceMk_frame 0)).prodMk
      (continuous_pullbackLift f)).subtype_mk _
  continuous_invFun := by
    refine continuous_iff.2 fun v ↦
      (inducing_pullbackTotalSpaceEmbedding F E f).continuous_iff.2 ?_
    refine ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_totalSpaceMk_frame v).comp
        (continuous_snd.comp continuous_subtype_val))).congr fun q ↦ ?_
    rcases q with ⟨⟨x, ⟨y, φ⟩⟩, h⟩
    dsimp only at h
    cases h
    rfl

/-- The pullback comparison retains both the new base point and the lifted frame. -/
@[simp]
theorem pullbackHomeomorph_apply (f : B' → B)
    (p : OrthonormalFrameBundle 𝕜 F (f *ᵖ E) V) :
    pullbackHomeomorph f p = ⟨(p.proj, pullbackLift f p), proj_pullbackLift f p⟩ :=
  (rfl)

/-- The inverse comparison views a frame at `f x` as a frame of the pullback fibre at `x`. -/
@[simp]
theorem pullbackHomeomorph_symm_mk (f : B' → B) (x : B') (φ : V ≃ₗᵢ[𝕜] E (f x)) :
    (pullbackHomeomorph (𝕜 := 𝕜) (F := F) f).symm ⟨(x, ⟨f x, φ⟩), rfl⟩ = ⟨x, φ⟩ :=
  (rfl)

/-- The inverse comparison keeps the new base point. -/
@[simp]
theorem proj_pullbackHomeomorph_symm (f : B' → B)
    (q : {q : B' × OrthonormalFrameBundle 𝕜 F E V // q.2.proj = f q.1}) :
    ((pullbackHomeomorph f).symm q).proj = q.1.1 :=
  (rfl)

/-- Lifting the frame given by the inverse comparison recovers the original frame. -/
@[simp]
theorem pullbackLift_pullbackHomeomorph_symm (f : B' → B)
    (q : {q : B' × OrthonormalFrameBundle 𝕜 F E V // q.2.proj = f q.1}) :
    pullbackLift f ((pullbackHomeomorph f).symm q) = q.1.2 := by
  have h := congrArg (fun q ↦ q.1.2) ((pullbackHomeomorph f).apply_symm_apply q)
  simpa only [pullbackHomeomorph_apply] using h

end TauCeti.OrthonormalFrameBundle
