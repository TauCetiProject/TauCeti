/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Topology.VectorBundle.Associated.Metric
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Isometry
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Principal

/-!
# Associated-bundle reconstruction and fibrewise naturality of orthonormal frames

Let `E → B` be a vector bundle over an `RCLike` field `𝕜` with finite-dimensional model fibre `F`
and fibre inner products with continuous norm, and let `V` be an inner product space with the
dimension of `F`. In `TauCeti.Topology.VectorBundle.OrthonormalFrame.Principal`, the orthonormal
frames of `E` modelled on `V` form a principal bundle `TauCeti.OrthonormalFrameBundle.Fiber 𝕜 F E V`
with structure group `unitary (V →L[𝕜] V)`. Meanwhile, `unitary (V →L[𝕜] V)` acts on `V` by linear
isometries (`Unitary.instIsIsometricSMul`), so the general associated-vector-bundle construction
(`TauCeti.AssociatedBundle`) produces a Riemannian or Hermitian vector bundle
`AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V` with model fibre `V`.

This file connects the two constructions and supplies the `Fiber`-level naturality under bundle
isometries:

* A family of fibrewise linear isometric equivalences `Φ b : E b ≃ₗᵢ[𝕜] E' b` acts on the principal
  bundle fibres by postcomposition (`TauCeti.OrthonormalFrameBundle.Fiber.map`), commuting with the
  right action of `unitary (V →L[𝕜] V)`. On total spaces, `totalSpaceMap Φ` is continuous if and
  only if `Φ` is continuous on the vector bundle total spaces
  (`TauCeti.OrthonormalFrameBundle.continuous_totalSpaceMap_iff`), and bundle isometries that are
  homeomorphisms on total spaces induce equivariant homeomorphisms on frame-bundle total spaces
  (`TauCeti.OrthonormalFrameBundle.totalSpaceMapHomeomorph`).
* Evaluating frames on vectors descends to a family of linear isometric equivalences
  `TauCeti.OrthonormalFrameBundle.associatedLinearIsometryEquiv 𝕜 F E V b` from the fibres of
  `AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V` onto the fibres `E b`, sending
  `[φ, v]` to `φ v`. In the preferred trivialization at `b₀`, the fibre coordinate of `u` in the
  associated bundle is the coordinate vector of `associatedLinearIsometryEquiv 𝕜 F E V b u` in the
  Gram–Schmidt frame of `E`
  (`TauCeti.OrthonormalFrameBundle.trivializationAt_associatedBundle_snd`).
  On total spaces, these fibrewise linear isometries assemble into a bundle-preserving homeomorphism
  `TauCeti.OrthonormalFrameBundle.associatedBundleHomeomorph 𝕜 F E V`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.Fiber.map`: action of fibrewise linear isometries on `Fiber`.
* `TauCeti.OrthonormalFrameBundle.Fiber.mapEquiv`: fibrewise equivalence induced by `Φ`.
* `TauCeti.OrthonormalFrameBundle.totalSpaceMap`: induced map on `TotalSpace` of `Fiber`.
* `TauCeti.OrthonormalFrameBundle.totalSpaceMapHomeomorph`: induced homeomorphism on `TotalSpace`
  of `Fiber`.
* `TauCeti.OrthonormalFrameBundle.associatedLinearIsometryEquiv`: canonical linear isometric
  equivalence `AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V b ≃ₗᵢ[𝕜] E b`.
* `TauCeti.OrthonormalFrameBundle.associatedBundleHomeomorph`: canonical homeomorphism between the
  total space of `AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V` and `TotalSpace F E`.

## Main results

* `TauCeti.OrthonormalFrameBundle.continuous_totalSpace_iff`: universal property of the topology on
  `TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)`.
* `TauCeti.OrthonormalFrameBundle.continuous_totalSpaceMap_iff`: `totalSpaceMap Φ` is continuous if
  and only if `Φ` is continuous on vector-bundle total spaces.
* `TauCeti.OrthonormalFrameBundle.associatedLinearIsometryEquiv_mk`,
  `TauCeti.OrthonormalFrameBundle.associatedLinearIsometryEquiv_symm_apply`: evaluation and inverse
  formulas in any orthonormal frame.
* `TauCeti.OrthonormalFrameBundle.trivializationAt_associatedBundle_snd`: preferred chart coordinate
  of the associated bundle in terms of the Gram–Schmidt frame of `E`.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer (1994),
  Chapter 4, §5 and Chapter 5, §§4–5.
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, volume I, Interscience (1963),
  Chapter I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §10.7.
-/

public noncomputable section

open Bundle MulOpposite Set

namespace TauCeti.OrthonormalFrameBundle

section FiberMap

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} {F F' F'' : Type*} {E E' E'' : B → Type*}
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)]
  [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace 𝕜 (E' b)]
  [∀ b, NormedAddCommGroup (E'' b)] [∀ b, InnerProductSpace 𝕜 (E'' b)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

namespace Fiber

/-- Postcomposing an orthonormal frame of `E b` with a linear isometric equivalence
`Φ b : E b ≃ₗᵢ[𝕜] E' b` gives an orthonormal frame of `E' b`. -/
def map (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) {b : B} (φ : Fiber 𝕜 F E V b) : Fiber 𝕜 F' E' V b :=
  ofFrame (φ.frame.trans (Φ b))

@[simp]
theorem frame_map (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) {b : B} (φ : Fiber 𝕜 F E V b) :
    (map (F' := F') Φ φ).frame = φ.frame.trans (Φ b) :=
  (rfl)

@[simp]
theorem map_ofFrame (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) {b : B} (φ : V ≃ₗᵢ[𝕜] E b) :
    map (F := F) (F' := F') Φ (ofFrame φ) = ofFrame (φ.trans (Φ b)) :=
  (rfl)

/-- The identity family of fibre isometries acts as the identity on frames. -/
@[simp]
theorem map_refl {b : B} (φ : Fiber 𝕜 F E V b) :
    map (F' := F) (fun b ↦ LinearIsometryEquiv.refl 𝕜 (E b)) φ = φ :=
  Fiber.ext (LinearIsometryEquiv.trans_refl _)

/-- Postcomposition of frames is functorial in the family of fibre isometries. -/
@[simp]
theorem map_map (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) (Ψ : ∀ b, E' b ≃ₗᵢ[𝕜] E'' b)
    {b : B} (φ : Fiber 𝕜 F E V b) :
    map (F' := F'') Ψ (map (F' := F') Φ φ) = map (fun b ↦ (Φ b).trans (Ψ b)) φ :=
  Fiber.ext (LinearIsometryEquiv.trans_assoc _ _ _)

/-- Postcomposing frames with fibre isometries commutes with the right action of the unitary
group. -/
@[simp]
theorem map_smul [CompleteSpace V] (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b)
    {b : B} (g : (unitary (V →L[𝕜] V))ᵐᵒᵖ) (φ : Fiber 𝕜 F E V b) :
    map (F' := F') Φ (g • φ) = g • map Φ φ :=
  Fiber.ext (LinearIsometryEquiv.trans_assoc _ _ _)

variable (F F' V) in
/-- The equivalence of frame fibres over `b` induced by `Φ`. -/
def mapEquiv (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) (b : B) : Fiber 𝕜 F E V b ≃ Fiber 𝕜 F' E' V b where
  toFun := map Φ
  invFun := map fun x ↦ (Φ x).symm
  left_inv φ := by simp
  right_inv φ := by simp

@[simp]
theorem mapEquiv_apply (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) {b : B} (φ : Fiber 𝕜 F E V b) :
    mapEquiv F F' V Φ b φ = map (F' := F') Φ φ :=
  (rfl)

@[simp]
theorem mapEquiv_symm (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) (b : B) :
    (mapEquiv F F' V Φ b).symm = mapEquiv F' F V (fun x ↦ (Φ x).symm) b :=
  (rfl)

end Fiber

section TotalSpaceMap

variable [CompleteSpace V]

/-- The map on frame-bundle total spaces induced by a family of fibrewise linear isometries `Φ`. -/
def totalSpaceMap (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b)
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F' E' V) :=
  ⟨p.proj, Fiber.map Φ p.2⟩

@[simp]
theorem proj_totalSpaceMap (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b)
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    (totalSpaceMap (F' := F') Φ p).proj = p.proj :=
  (rfl)

theorem totalSpaceMap_apply (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b)
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    totalSpaceMap (F' := F') Φ p = ⟨p.proj, Fiber.map Φ p.2⟩ :=
  (rfl)

@[simp]
theorem totalSpaceMap_mk (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) (b : B) (φ : Fiber 𝕜 F E V b) :
    totalSpaceMap (F' := F') Φ ⟨b, φ⟩ = ⟨b, Fiber.map Φ φ⟩ :=
  (rfl)

@[simp]
theorem totalSpaceMap_refl (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    totalSpaceMap (F' := F) (fun b ↦ LinearIsometryEquiv.refl 𝕜 (E b)) p = p := by
  obtain ⟨b, φ⟩ := p
  simp

@[simp]
theorem totalSpaceMap_totalSpaceMap (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) (Ψ : ∀ b, E' b ≃ₗᵢ[𝕜] E'' b)
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    totalSpaceMap (F' := F'') Ψ (totalSpaceMap (F' := F') Φ p) =
      totalSpaceMap (fun b ↦ (Φ b).trans (Ψ b)) p := by
  obtain ⟨b, φ⟩ := p
  simp

@[simp]
theorem totalSpaceMap_smul (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) (g : (unitary (V →L[𝕜] V))ᵐᵒᵖ)
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    totalSpaceMap (F' := F') Φ (g • p) = g • totalSpaceMap (F' := F') Φ p := by
  obtain ⟨b, φ⟩ := p
  simp

theorem totalSpaceEquiv_totalSpaceMap (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b)
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    totalSpaceEquiv (totalSpaceMap (F' := F') Φ p) = ⟨p.proj, p.2.frame.trans (Φ p.proj)⟩ := by
  obtain ⟨b, φ⟩ := p
  simp

/-- Over `ℝ`, `totalSpaceEquiv` intertwines `totalSpaceMap` with `OrthonormalFrameBundle.map`. -/
theorem totalSpaceEquiv_totalSpaceMap_real {F F' : Type*} {E E' : B → Type*}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
    [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b) (p : TotalSpace (unitary (V →L[ℝ] V)) (Fiber ℝ F E V)) :
    totalSpaceEquiv (totalSpaceMap (F' := F') Φ p) = map Φ (totalSpaceEquiv p) := by
  obtain ⟨b, φ⟩ := p
  simp

variable [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E')]

/-- Universal property of the topology on `TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)`: a map
into the total space of orthonormal frames is continuous if and only if applying the frame to each
fixed vector `v : V` gives a continuous map into `TotalSpace F E`. -/
theorem continuous_totalSpace_iff {X : Type*} [TopologicalSpace X]
    {f : X → TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)} :
    Continuous f ↔
      ∀ v : V, Continuous fun x ↦ (⟨(f x).proj, (f x).2.frame v⟩ : TotalSpace F E) := by
  rw [totalSpaceHomeomorph.isEmbedding.continuous_iff]
  simp [Function.comp_def, continuous_iff]

/-- Evaluating a point of `TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)` on a vector `v : V`
is jointly continuous. -/
theorem continuous_totalSpace_frame_apply [TopologicalSpace B] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiberBundle F E] [VectorBundle 𝕜 F E] [FiniteDimensional 𝕜 V] :
    Continuous fun q : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) × V ↦
      (⟨q.1.proj, q.1.2.frame q.2⟩ : TotalSpace F E) := by
  refine (continuous_totalSpaceMk_frame_apply.comp
    (totalSpaceHomeomorph.continuous.prodMap continuous_id)).congr fun ⟨⟨b, φ⟩, v⟩ ↦ ?_
  have hp : totalSpaceHomeomorph (⟨b, φ⟩ : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) =
      ⟨b, φ.frame⟩ := by simp
  exact congrArg
    (fun p : OrthonormalFrameBundle 𝕜 F E V ↦ (⟨p.proj, p.frame v⟩ : TotalSpace F E)) hp

/-- If the fibrewise isometries `Φ` are continuous on vector-bundle total spaces, the induced map on
frame-bundle total spaces is continuous. -/
theorem continuous_totalSpaceMap {Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b}
    (hΦ : Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E')) :
    Continuous (totalSpaceMap (F := F) (F' := F') (V := V) Φ) :=
  continuous_totalSpace_iff.2 fun v ↦
    hΦ.comp (continuous_totalSpace_iff.1 continuous_id v)

variable (V) in
/-- A family of fibrewise linear isometries continuous in both directions on vector-bundle total
spaces induces a homeomorphism of frame-bundle total spaces. -/
def totalSpaceMapHomeomorph (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b)
    (hΦ : Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E'))
    (hΦ' : Continuous fun x : TotalSpace F' E' ↦
      (⟨x.proj, (Φ x.proj).symm x.2⟩ : TotalSpace F E)) :
    TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) ≃ₜ
      TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F' E' V) where
  toFun := totalSpaceMap Φ
  invFun := totalSpaceMap fun b ↦ (Φ b).symm
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_totalSpaceMap hΦ
  continuous_invFun := continuous_totalSpaceMap hΦ'

@[simp]
theorem totalSpaceMapHomeomorph_apply (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b)
    (hΦ : Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E'))
    (hΦ' : Continuous fun x : TotalSpace F' E' ↦
      (⟨x.proj, (Φ x.proj).symm x.2⟩ : TotalSpace F E))
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    totalSpaceMapHomeomorph V Φ hΦ hΦ' p = totalSpaceMap Φ p :=
  (rfl)

@[simp]
theorem totalSpaceMapHomeomorph_symm (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b)
    (hΦ : Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E'))
    (hΦ' : Continuous fun x : TotalSpace F' E' ↦
      (⟨x.proj, (Φ x.proj).symm x.2⟩ : TotalSpace F E)) :
    (totalSpaceMapHomeomorph V Φ hΦ hΦ').symm =
      totalSpaceMapHomeomorph V (fun b ↦ (Φ b).symm) hΦ' hΦ :=
  (rfl)

/-- For locally trivial Riemannian or Hermitian vector bundles whose fibres have the dimension of
`V`, the induced map `totalSpaceMap Φ` on frame-bundle total spaces is continuous if and only if
`Φ` is continuous on vector-bundle total spaces. -/
theorem continuous_totalSpaceMap_iff [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [FiberBundle F' E'] [VectorBundle 𝕜 F' E']
    [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 V] (hV : Module.finrank 𝕜 V = Module.finrank 𝕜 F)
    {Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b} :
    Continuous (totalSpaceMap (F := F) (F' := F') (V := V) Φ) ↔
      Continuous fun x : TotalSpace F E ↦ (⟨x.proj, Φ x.proj x.2⟩ : TotalSpace F' E') := by
  refine ⟨fun h ↦ ?_, continuous_totalSpaceMap⟩
  rw [(isOpenQuotientMap_totalSpaceMk_frame_apply (E := E) hV).isQuotientMap.continuous_iff]
  refine (continuous_totalSpace_frame_apply.comp
    ((h.comp totalSpaceHomeomorph.symm.continuous).prodMap continuous_id)).congr
    fun ⟨⟨b, φ⟩, v⟩ ↦ ?_
  have hp : totalSpaceMap (F' := F') Φ
      (totalSpaceHomeomorph.symm (⟨b, φ⟩ : OrthonormalFrameBundle 𝕜 F E V)) =
      ⟨b, .ofFrame (φ.trans (Φ b))⟩ := by simp
  exact congrArg (fun p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F' E' V) ↦
    (⟨p.proj, p.2.frame v⟩ : TotalSpace F' E')) hp

end TotalSpaceMap

end FiberMap

/-! ### Reconstruction of `E` as an associated bundle -/

section Associated

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} {E : B → Type*}
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

section Principal

variable [TopologicalSpace (TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V))]
  [∀ b, TopologicalSpace (Fiber 𝕜 F E V b)]
  [FiberBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)]
  [PrincipalBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)]

variable (𝕜 F E V) in
/-- The canonical linear isometric equivalence identifying the fibre over `b` of the associated
vector bundle `AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V` with `E b`: every class
`[φ, v]` is sent to `φ v` (`associatedLinearIsometryEquiv_mk`). -/
def associatedLinearIsometryEquiv (b : B) :
    AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V b ≃ₗᵢ[𝕜] E b :=
  let p₀ := (FiberBundle.homeomorphAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) b).symm 1
  (AssociatedBundle.mkLinearIsometryEquiv 𝕜 (unitary (V →L[𝕜] V)) p₀).symm.trans p₀.frame

/-- Evaluating `associatedLinearIsometryEquiv` on the class `[φ, v]` of an orthonormal frame `φ`
and a model vector `v` applies `φ` to `v`. -/
@[simp]
theorem associatedLinearIsometryEquiv_mk {b : B} (φ : Fiber 𝕜 F E V b) (v : V) :
    associatedLinearIsometryEquiv 𝕜 F E V b
      (AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ v) = φ.frame v := by
  dsimp only [associatedLinearIsometryEquiv, LinearIsometryEquiv.trans_apply]
  rw [AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk, division_eq]
  simp [Submonoid.smul_def, ← Unitary.coe_linearIsometryEquiv_apply]

/-- The inverse of `associatedLinearIsometryEquiv` expresses a vector `w : E b` in any orthonormal
frame `φ` of `E b` as the class `[φ, φ⁻¹ w]`. -/
theorem associatedLinearIsometryEquiv_symm_apply {b : B} (φ : Fiber 𝕜 F E V b) (w : E b) :
    (associatedLinearIsometryEquiv 𝕜 F E V b).symm w =
      AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ (φ.frame.symm w) :=
  (associatedLinearIsometryEquiv 𝕜 F E V b).injective <| by simp

/-- Naturality of `associatedLinearIsometryEquiv` with respect to fibrewise linear isometries. -/
theorem associatedLinearIsometryEquiv_mk_map {F' : Type*} {E' : B → Type*}
    [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace 𝕜 (E' b)]
    [TopologicalSpace (TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F' E' V))]
    [∀ b, TopologicalSpace (Fiber 𝕜 F' E' V b)]
    [FiberBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F' E' V)]
    [PrincipalBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F' E' V)]
    (Φ : ∀ b, E b ≃ₗᵢ[𝕜] E' b) {b : B} (φ : Fiber 𝕜 F E V b) (v : V) :
    associatedLinearIsometryEquiv 𝕜 F' E' V b
        (AssociatedBundle.mk (unitary (V →L[𝕜] V)) (Fiber.map (F' := F') Φ φ) v) =
      Φ b (associatedLinearIsometryEquiv 𝕜 F E V b
        (AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ v)) := by
  simp

end Principal

section VectorBundle

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
  [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 V]
  [hV : Fact (Module.finrank 𝕜 V = Module.finrank 𝕜 F)]

/-- Over `(trivializationAt F E b₀).baseSet`, the group coordinate of a frame `p` in
`trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) b₀` acts on `v : V` by applying `p` to `v`
and reading the result in the Gram–Schmidt frame of `trivializationAt F E b₀`. -/
theorem trivializationAt_fiber_snd_apply {b₀ : B}
    {p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)}
    (hp : p.proj ∈ (trivializationAt F E b₀).baseSet) (v : V) :
    ((trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) b₀ p).2 : V →L[𝕜] V) v =
      ((trivializationAt F E b₀).orthonormalFrameAt
        (Module.finBasisOfFinrankEq 𝕜 F hV.out.symm) (stdOrthonormalBasis 𝕜 V) p.proj).symm
        (p.2.frame v) := by
  obtain ⟨b, φ⟩ := p
  have h : trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) b₀ ⟨b, φ⟩ =
      (trivializationAt F E b₀).orthonormalFrameBundle
        (Module.finBasisOfFinrankEq 𝕜 F hV.out.symm) (stdOrthonormalBasis 𝕜 V)
        ⟨b, φ.frame⟩ := by
    rw [trivializationAt_fiber, trivializationAtFiber_apply, totalSpaceEquiv_apply]
  rw [h, Trivialization.orthonormalFrameBundle_apply_mk _ _ _ ⟨b, hp⟩ φ.frame,
    Trivialization.orthonormalFrameAt_of_mem _ _ _ hp]
  simp [← Unitary.coe_linearIsometryEquiv_apply]

/-- Over the base set of `trivializationAt F E b₀`, the Gram–Schmidt frame `orthonormalFrameAt` has
identity group coordinate in `trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) b₀`. -/
theorem trivializationAt_fiber_orthonormalFrameAt_snd {b₀ b : B}
    (hb : b ∈ (trivializationAt F E b₀).baseSet) :
    (trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) b₀
      ⟨b, .ofFrame ((trivializationAt F E b₀).orthonormalFrameAt
        (Module.finBasisOfFinrankEq 𝕜 F hV.out.symm) (stdOrthonormalBasis 𝕜 V) b)⟩).2 = 1 := by
  rw [trivializationAt_fiber, trivializationAtFiber_apply, totalSpaceEquiv_apply,
    Trivialization.orthonormalFrameAt_of_mem _ _ _ hb]
  exact congrArg Prod.snd
    (Trivialization.orthonormalFrameBundle_apply_orthonormalFrame _ _ _ ⟨b, hb⟩)

/-- In the preferred trivialization of the associated bundle at `b₀`, the fibre coordinate of a
class `u` over `b ∈ (trivializationAt F E b₀).baseSet` is the coordinate vector of
`associatedLinearIsometryEquiv 𝕜 F E V b u` in the Gram–Schmidt frame of `trivializationAt F E b₀`.
-/
theorem trivializationAt_associatedBundle_snd {b₀ b : B}
    (hb : b ∈ (trivializationAt F E b₀).baseSet)
    (u : AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V b) :
    (trivializationAt V (AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V) b₀ ⟨b, u⟩).2 =
      ((trivializationAt F E b₀).orthonormalFrameAt
        (Module.finBasisOfFinrankEq 𝕜 F hV.out.symm) (stdOrthonormalBasis 𝕜 V) b).symm
        (associatedLinearIsometryEquiv 𝕜 F E V b u) := by
  let σ : Fiber 𝕜 F E V b := .ofFrame ((trivializationAt F E b₀).orthonormalFrameAt
    (Module.finBasisOfFinrankEq 𝕜 F hV.out.symm) (stdOrthonormalBasis 𝕜 V) b)
  have hu : u = AssociatedBundle.mk (unitary (V →L[𝕜] V)) σ
      (σ.frame.symm (associatedLinearIsometryEquiv 𝕜 F E V b u)) := by
    rw [← associatedLinearIsometryEquiv_symm_apply, LinearIsometryEquiv.symm_apply_apply]
  have hb' : b ∈ (trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) b₀).baseSet := by
    rwa [baseSet_trivializationAt_fiber (𝕜 := 𝕜) (F := F) (E := E) (V := V)]
  conv_lhs => rw [hu]
  rw [AssociatedBundle.trivializationAt_mk_snd hb',
    trivializationAt_fiber_orthonormalFrameAt_snd hb, one_smul]

/-- Over `(trivializationAt F E b₀).baseSet`, `associatedLinearIsometryEquiv` evaluates the
Gram–Schmidt frame of `trivializationAt F E b₀` at the preferred chart coordinate of the associated
bundle. -/
theorem associatedLinearIsometryEquiv_eq_orthonormalFrameAt_apply {b₀ b : B}
    (hb : b ∈ (trivializationAt F E b₀).baseSet)
    (u : AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V b) :
    associatedLinearIsometryEquiv 𝕜 F E V b u =
      (trivializationAt F E b₀).orthonormalFrameAt
        (Module.finBasisOfFinrankEq 𝕜 F hV.out.symm) (stdOrthonormalBasis 𝕜 V) b
        (trivializationAt V (AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V)
          b₀ ⟨b, u⟩).2 := by
  rw [trivializationAt_associatedBundle_snd hb, LinearIsometryEquiv.apply_symm_apply]

variable (𝕜 F E V) in
/-- The canonical homeomorphism from the total space of the associated vector bundle
`AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V` onto `TotalSpace F E`, acting on each
fibre by the linear isometric equivalence `associatedLinearIsometryEquiv`. -/
def associatedBundleHomeomorph :
    TotalSpace V (AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V) ≃ₜ TotalSpace F E where
  toFun u := ⟨u.proj, associatedLinearIsometryEquiv 𝕜 F E V u.proj u.2⟩
  invFun x := ⟨x.proj, (associatedLinearIsometryEquiv 𝕜 F E V x.proj).symm x.2⟩
  left_inv := fun ⟨b, u⟩ ↦
    congrArg (TotalSpace.mk' V b) ((associatedLinearIsometryEquiv 𝕜 F E V b).symm_apply_apply u)
  right_inv := fun ⟨b, x⟩ ↦
    congrArg (TotalSpace.mk' F b) ((associatedLinearIsometryEquiv 𝕜 F E V b).apply_symm_apply x)
  continuous_toFun := by
    rw [(AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk (unitary (V →L[𝕜] V))
      (Fiber 𝕜 F E V) V).isQuotientMap.continuous_iff]
    refine continuous_totalSpace_frame_apply.congr fun ⟨⟨b, φ⟩, v⟩ ↦ ?_
    simp
  continuous_invFun := by
    rw [(isOpenQuotientMap_totalSpaceMk_frame_apply (E := E) hV.out).isQuotientMap.continuous_iff]
    have hmk : Continuous fun q : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) × V ↦
        (⟨q.1.proj, AssociatedBundle.mk (unitary (V →L[𝕜] V)) q.1.2 q.2⟩ :
          TotalSpace V (AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V)) :=
      (AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk (unitary (V →L[𝕜] V))
        (Fiber 𝕜 F E V) V).continuous
    refine (hmk.comp (totalSpaceHomeomorph.symm.continuous.prodMap continuous_id)).congr
      fun ⟨⟨b, φ⟩, v⟩ ↦ ?_
    have hp : totalSpaceHomeomorph.symm (⟨b, φ⟩ : OrthonormalFrameBundle 𝕜 F E V) =
        ⟨b, .ofFrame φ⟩ := by simp
    exact (congrArg (fun p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) ↦
      (⟨p.proj, AssociatedBundle.mk (unitary (V →L[𝕜] V)) p.2 v⟩ :
        TotalSpace V (AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V))) hp).trans
      (by simp [associatedLinearIsometryEquiv_symm_apply (.ofFrame φ) (φ v)])

@[simp]
theorem associatedBundleHomeomorph_apply
    (u : TotalSpace V (AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V)) :
    associatedBundleHomeomorph 𝕜 F E V u =
      ⟨u.proj, associatedLinearIsometryEquiv 𝕜 F E V u.proj u.2⟩ :=
  (rfl)

theorem proj_associatedBundleHomeomorph
    (u : TotalSpace V (AssociatedBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) V)) :
    (associatedBundleHomeomorph 𝕜 F E V u).proj = u.proj :=
  (rfl)

@[simp]
theorem associatedBundleHomeomorph_symm_apply (x : TotalSpace F E) :
    (associatedBundleHomeomorph 𝕜 F E V).symm x =
      ⟨x.proj, (associatedLinearIsometryEquiv 𝕜 F E V x.proj).symm x.2⟩ :=
  (rfl)

theorem proj_associatedBundleHomeomorph_symm (x : TotalSpace F E) :
    ((associatedBundleHomeomorph 𝕜 F E V).symm x).proj = x.proj :=
  (rfl)

theorem associatedBundleHomeomorph_mk {b : B} (φ : Fiber 𝕜 F E V b) (v : V) :
    associatedBundleHomeomorph 𝕜 F E V ⟨b, AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ v⟩ =
      ⟨b, φ.frame v⟩ := by
  simp

theorem associatedBundleHomeomorph_symm_mk_apply {b : B} (φ : Fiber 𝕜 F E V b) (w : E b) :
    (associatedBundleHomeomorph 𝕜 F E V).symm ⟨b, w⟩ =
      ⟨b, AssociatedBundle.mk (unitary (V →L[𝕜] V)) φ (φ.frame.symm w)⟩ := by
  rw [associatedBundleHomeomorph_symm_apply, associatedLinearIsometryEquiv_symm_apply]

end VectorBundle

end Associated

end TauCeti.OrthonormalFrameBundle
