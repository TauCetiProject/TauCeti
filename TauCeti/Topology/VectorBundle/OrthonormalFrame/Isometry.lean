/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Pullback

/-!
# Naturality of orthonormal frame bundles under bundle isometries

Let `E` and `E'` be Riemannian vector bundles over the same base `B`, and let
`Φ b : E b ≃ₗᵢ[ℝ] E' b` be a family of linear isometric equivalences of the fibres. Composing
frames with `Φ` maps orthonormal frames of `E` to orthonormal frames of `E'`
(`TauCeti.OrthonormalFrameBundle.map`). This map covers the identity of `B`, commutes with the
right action of the orthogonal group, is functorial in `Φ` and commutes with the canonical lifts
of frames along pullbacks.

Conversely, when every fibre of `E` admits an orthonormal frame modelled on `V`, every map of
frame bundles covering the identity and commuting with the orthogonal action comes from a unique
such family (`TauCeti.OrthonormalFrameBundle.exists_eq_map`,
`TauCeti.OrthonormalFrameBundle.map_injective`). Morphisms of the principal orthogonal frame
bundles over `B` are therefore exactly the fibrewise isometries of the vector bundles.

The correspondence respects topology. If `Φ` is continuous as a map of total spaces then so is
the induced map of frame bundles (`TauCeti.OrthonormalFrameBundle.continuous_map`), and a family
continuous in both directions gives an equivariant homeomorphism
(`TauCeti.OrthonormalFrameBundle.mapHomeomorph`). For locally trivial bundles with fibres of the
dimension of `V` the converse holds as well: applying frames to vectors is a quotient map onto
the total space, so `Φ` is continuous on total spaces exactly when the induced map of frame
bundles is continuous (`TauCeti.OrthonormalFrameBundle.continuous_map_iff`).

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 4, §§2–5 (morphisms of principal bundles and of their associated bundles) and
  Chapter 5, §§4–5 (the principal bundle of orthonormal frames).
-/

public noncomputable section

open Bundle MulOpposite

namespace TauCeti.OrthonormalFrameBundle

variable {B : Type*} {F F' F'' : Type*} {E E' E'' : B → Type*}
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)]
  [∀ b, NormedAddCommGroup (E'' b)] [∀ b, InnerProductSpace ℝ (E'' b)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The map of orthonormal frame bundles induced by a family of linear isometric equivalences
`Φ b : E b ≃ₗᵢ[ℝ] E' b`: a frame `φ` of `E b` is sent to the frame `Φ b ∘ φ` of `E' b`. -/
def map (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b) (p : OrthonormalFrameBundle ℝ F E V) :
    OrthonormalFrameBundle ℝ F' E' V :=
  ⟨p.proj, p.frame.trans (Φ p.proj)⟩

@[simp]
theorem map_mk (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b) (b : B) (φ : V ≃ₗᵢ[ℝ] E b) :
    map (F := F) (F' := F') Φ ⟨b, φ⟩ = ⟨b, φ.trans (Φ b)⟩ :=
  (rfl)

/-- The induced map covers the identity of the base. -/
@[simp]
theorem proj_map (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b) (p : OrthonormalFrameBundle ℝ F E V) :
    (map (F' := F') Φ p).proj = p.proj :=
  (rfl)

/-- The induced frame applies `Φ` after the original frame. -/
@[simp]
theorem totalSpaceMk_map_frame (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b) (p : OrthonormalFrameBundle ℝ F E V)
    (v : V) :
    (⟨(map (F' := F') Φ p).proj, (map (F' := F') Φ p).frame v⟩ : TotalSpace F' E') =
      ⟨p.proj, Φ p.proj (p.frame v)⟩ :=
  (rfl)

/-- The identity isometries induce the identity of the frame bundle. -/
@[simp]
theorem map_refl (p : OrthonormalFrameBundle ℝ F E V) :
    map (F' := F) (fun b ↦ LinearIsometryEquiv.refl ℝ (E b)) p = p :=
  mk_eq_mk_iff.2 (LinearIsometryEquiv.trans_refl _)

/-- The induced maps compose as the families of isometries do. -/
@[simp]
theorem map_map (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b) (Ψ : ∀ b, E' b ≃ₗᵢ[ℝ] E'' b)
    (p : OrthonormalFrameBundle ℝ F E V) :
    map (F' := F'') Ψ (map (F' := F') Φ p) = map (fun b ↦ (Φ b).trans (Ψ b)) p :=
  mk_eq_mk_iff.2 (LinearIsometryEquiv.trans_assoc _ _ _)

/-- The induced map commutes with the right action of the orthogonal group. -/
@[simp]
theorem map_smul [CompleteSpace V] (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (g : (unitary (V →L[ℝ] V))ᵐᵒᵖ) (p : OrthonormalFrameBundle ℝ F E V) :
    map (F' := F') Φ (g • p) = g • map Φ p :=
  mk_eq_mk_iff.2 (LinearIsometryEquiv.trans_assoc _ _ _)

/-- Lifting frames along a pullback commutes with the maps induced by isometries: the frame map
induced by the pulled-back isometries `Φ (f x)` lifts to the frame map induced by `Φ`. -/
@[simp]
theorem pullbackLift_map {B' : Type*} (f : B' → B) (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (p : OrthonormalFrameBundle ℝ F (f *ᵖ E) V) :
    pullbackLift (F := F') f
        (map (E' := f *ᵖ E') (fun x ↦ Φ (f x)) p) = map Φ (pullbackLift f p) := by
  obtain ⟨x, φ⟩ := p
  exact (pullbackLift_mk (F := F') f x (φ.trans (Φ (f x)))).trans
    (congrArg (map Φ) (pullbackLift_mk f x φ)).symm

/-- Families of fibrewise isometries are determined by their induced frame maps, once every fibre
of `E` admits an orthonormal frame modelled on `V`. -/
theorem map_injective (hV : ∀ b, Nonempty (V ≃ₗᵢ[ℝ] E b)) :
    Function.Injective
      (map : (∀ b, E b ≃ₗᵢ[ℝ] E' b) →
        OrthonormalFrameBundle ℝ F E V → OrthonormalFrameBundle ℝ F' E' V) := by
  intro Φ Ψ h
  funext b
  obtain ⟨φ⟩ := hV b
  have hφ : φ.trans (Φ b) = φ.trans (Ψ b) :=
    mk_eq_mk_iff.1 (congrFun h (⟨b, φ⟩ : OrthonormalFrameBundle ℝ F E V))
  ext x
  simpa using congrArg (fun ψ : V ≃ₗᵢ[ℝ] E' b ↦ ψ (φ.symm x)) hφ

/-- Every map of orthonormal frame bundles covering the identity of the base and commuting with
the right action of the orthogonal group is induced by a family of linear isometric equivalences
of the fibres, once every fibre of `E` admits an orthonormal frame modelled on `V`. -/
theorem exists_eq_map [CompleteSpace V] (hV : ∀ b, Nonempty (V ≃ₗᵢ[ℝ] E b))
    (ψ : OrthonormalFrameBundle ℝ F E V → OrthonormalFrameBundle ℝ F' E' V)
    (hproj : ∀ p, (ψ p).proj = p.proj)
    (hsmul : ∀ (g : (unitary (V →L[ℝ] V))ᵐᵒᵖ) p, ψ (g • p) = g • ψ p) :
    ∃ Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b, ψ = map Φ := by
  -- Read `Φ b` off the image of one chosen frame `φ b` over `b`.
  let φ (b : B) : V ≃ₗᵢ[ℝ] E b := (hV b).some
  have hb (b : B) : (ψ ⟨b, φ b⟩).proj = b := hproj _
  let Φ b : E b ≃ₗᵢ[ℝ] E' b := (φ b).symm.trans (hb b ▸ (ψ ⟨b, φ b⟩).frame)
  have hΦ (b : B) : ψ ⟨b, φ b⟩ = map (F := F) Φ ⟨b, φ b⟩ := by
    rw [eq_mk_of_proj_eq (ψ ⟨b, φ b⟩) (hb b), map_mk, mk_eq_mk_iff]
    ext v
    simp [Φ]
  refine ⟨Φ, funext fun p ↦ ?_⟩
  -- Every other frame over `b` is a translate of `φ b`, and both maps are equivariant.
  obtain ⟨g, hg⟩ := (exists_smul_eq_iff (p := ⟨p.proj, φ p.proj⟩) (q := p)).2 rfl
  rw [← hg, hsmul, map_smul, hΦ]

section Topology

variable [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E')]

/-- If the isometries `Φ` form a continuous map of total spaces, the induced map of orthonormal
frame bundles is continuous. -/
theorem continuous_map {Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b}
    (hΦ : Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E')) :
    Continuous (map (F := F) (F' := F') (V := V) Φ) :=
  continuous_iff.2 fun v ↦ hΦ.comp (continuous_totalSpaceMk_frame v)

/-- A family of linear isometric equivalences of the fibres that is continuous in both directions
as a map of total spaces induces a homeomorphism of orthonormal frame bundles. It covers the
identity of the base and commutes with the right action of the orthogonal group
(`TauCeti.OrthonormalFrameBundle.map_smul`). -/
def mapHomeomorph (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (hΦ : Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E'))
    (hΦsymm : Continuous fun x : TotalSpace F' E' ↦
      (⟨x.proj, (Φ x.proj).symm x.2⟩ : TotalSpace F E)) :
    OrthonormalFrameBundle ℝ F E V ≃ₜ OrthonormalFrameBundle ℝ F' E' V where
  toFun := map Φ
  invFun := map fun b ↦ (Φ b).symm
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_map hΦ
  continuous_invFun := continuous_map hΦsymm

@[simp]
theorem mapHomeomorph_apply (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (hΦ : Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E'))
    (hΦsymm : Continuous fun x : TotalSpace F' E' ↦
      (⟨x.proj, (Φ x.proj).symm x.2⟩ : TotalSpace F E)) (p : OrthonormalFrameBundle ℝ F E V) :
    mapHomeomorph Φ hΦ hΦsymm p = map Φ p :=
  (rfl)

@[simp]
theorem mapHomeomorph_symm_apply (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)
    (hΦ : Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E'))
    (hΦsymm : Continuous fun x : TotalSpace F' E' ↦
      (⟨x.proj, (Φ x.proj).symm x.2⟩ : TotalSpace F E)) (p : OrthonormalFrameBundle ℝ F' E' V) :
    (mapHomeomorph Φ hΦ hΦsymm).symm p = map (fun b ↦ (Φ b).symm) p :=
  (rfl)

variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiberBundle F' E'] [VectorBundle ℝ F' E']

/-- When the fibres of `E` have the dimension of `V`, a family of linear isometric equivalences of
the fibres is continuous as a map of total spaces exactly when the induced map of orthonormal
frame bundles is continuous. The reverse implication reconstructs the total space of `E` from
its frames: applying frames to vectors is a quotient map. -/
theorem continuous_map_iff [FiniteDimensional ℝ F] [FiniteDimensional ℝ V]
    (h : Module.finrank ℝ V = Module.finrank ℝ F) {Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b} :
    Continuous (map (F := F) (F' := F') (V := V) Φ) ↔
      Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E') := by
  refine ⟨fun hc ↦ ?_, continuous_map⟩
  -- Precomposed with applying frames of `E` to vectors, the total-space map applies the
  -- induced frames of `E'` to the same vectors.
  refine (isOpenQuotientMap_totalSpaceMk_frame_apply (E := E) h).isQuotientMap.continuous_iff.2 ?_
  exact continuous_totalSpaceMk_frame_apply.comp (hc.prodMap continuous_id)

end Topology

end TauCeti.OrthonormalFrameBundle
