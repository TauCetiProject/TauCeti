/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Subbundle

/-!
# The differential image of a smooth embedding as a `C^m` vector subbundle

Applying the differential-image frame construction from
`TauCeti.Geometry.Manifold.VectorBundle.Tangent.Subbundle` to a `C^n` `SmoothEmbedding` `f : M → N`
(`n ≠ 0`, `m + 1 ≤ n`) with finite-dimensional source model `E` yields `C^m` local subbundle frames
of `x ↦ f.isImmersion.tangentRange x hn` inside `f *ᵖ TangentSpace J`
(`TauCeti.SmoothEmbedding.hasLocalContMDiffSubbundleFrames_tangentRange`). Over `ℝ` or `ℂ`, this
equips `x ↦ f.isImmersion.tangentRange x hn` with its canonical `C^m` vector subbundle structure
(`tangentRangeContMDiffVectorBundle`) and induces a `C^m` bundle diffeomorphism
`f.tangentBundleDiffeomorphTangentRange` from `TangentSpace I` onto
`x ↦ f.isImmersion.tangentRange x hn`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Proposition 10.34.
-/

public noncomputable section

open Bundle Set Function Topology
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  {n m : ℕ∞ω} [IsManifold J 1 N] [IsManifold I (m + 1) M]

/-- For a `C^n` smooth embedding `f` (`n ≠ 0`, `m + 1 ≤ n`) with finite-dimensional source model
`E`, `x ↦ f.isImmersion.tangentRange x hn` admits `C^m` local subbundle frames inside
`f *ᵖ TangentSpace J`. -/
theorem hasLocalContMDiffSubbundleFrames_tangentRange [FiniteDimensional 𝕜 E]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    HasLocalContMDiffSubbundleFrames (E := (f : M → N) *ᵖ (TangentSpace J)) I m V
      (Fin (Module.finrank 𝕜 E)) (fun x ↦ f.isImmersion.tangentRange x hn) :=
  f.isImmersion.hasLocalContMDiffSubbundleFrames_range_mfderiv hn hm

section BundleDiffeomorph

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E]

omit [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I (m + 1) M] in
/-- The subspace topology on the total space of `x ↦ f.isImmersion.tangentRange x hn` induced from
`TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))`. Install with `letI`. -/
@[instance_reducible]
def tangentRangeTopology (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) :
    TopologicalSpace
      (TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.isImmersion.tangentRange x hn)) :=
  subbundleTopology V (E := (f : M → N) *ᵖ (TangentSpace J))
    (F' := Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.isImmersion.tangentRange x hn)

variable (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)

/-- The fibre-bundle structure on `x ↦ f.isImmersion.tangentRange x hn` given by its `C^m` local
subbundle frames. Install with `letI`. -/
@[instance_reducible]
def tangentRangeFiberBundle :
    letI := f.tangentRangeTopology (E := E) (V := V) hn
    FiberBundle (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.isImmersion.tangentRange x hn) :=
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).fiberBundle

/-- The `𝕜`-vector bundle structure on `x ↦ f.isImmersion.tangentRange x hn` as a subbundle of
`f *ᵖ TangentSpace J`. -/
theorem tangentRangeVectorBundle :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    VectorBundle 𝕜 (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.isImmersion.tangentRange x hn) :=
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).vectorBundle

variable [IsManifold J (m + 1) N]

local instance : ContMDiffVectorBundle m V (TangentSpace J : N → Type _) J :=
  TangentBundle.contMDiffVectorBundle

/-- **The differential image `x ↦ f.isImmersion.tangentRange x hn` is a `C^m` vector subbundle of
`f *ᵖ TangentSpace J`.** -/
theorem tangentRangeContMDiffVectorBundle :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    letI := f.tangentRangeVectorBundle hn hm
    ContMDiffVectorBundle m (Fin (Module.finrank 𝕜 E) → 𝕜)
      (fun x ↦ f.isImmersion.tangentRange x hn) I :=
  letI := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J)
    (f.contMDiff.of_le ((le_add_right le_rfl).trans hm))
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiffVectorBundle (𝕜 := 𝕜)

/-- The canonical inclusion of the subbundle `x ↦ f.isImmersion.tangentRange x hn` into
`f *ᵖ TangentSpace J` is `C^m` on total spaces. -/
theorem contMDiff_totalSpace_inclusion_tangentRange :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    ContMDiff (I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)) (I.prod 𝓘(𝕜, V)) m
      (fun v : TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜)
          (fun x ↦ f.isImmersion.tangentRange x hn) ↦
        (⟨v.proj, v.snd.val⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) :=
  letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
  letI := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J)
    (f.contMDiff.of_le ((le_add_right le_rfl).trans hm))
  (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiff_totalSpace_inclusion (𝕜 := 𝕜)

variable [IsManifold I 1 M]

local instance : CompleteSpace 𝕜 :=
  letI := IsRCLikeNormedField.rclike 𝕜; inferInstance
local instance : ContMDiffVectorBundle m E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

private theorem contMDiff_tangentSpaceEquivTangentRange :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)) m
      (fun q : TotalSpace E (TangentSpace I : M → Type _) ↦
        TotalSpace.mk' (Fin (Module.finrank 𝕜 E) → 𝕜) (E := fun x ↦ f.isImmersion.tangentRange x hn)
          q.proj (f.isImmersion.tangentSpaceEquivTangentRange q.proj hn q.snd)) := by
  let := f.tangentRangeTopology (E := E) (V := V) hn
  let := f.tangentRangeFiberBundle hn hm
  let := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J)
    (f.contMDiff.of_le ((le_add_right le_rfl).trans hm))
  intro p
  have hfm := (f.contMDiff.of_le ((le_add_right le_rfl).trans hm)).contMDiffAt (x := p.proj)
  have hw : ContMDiffAt (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, V)) m
      (fun q : TotalSpace E (TangentSpace I : M → Type _) ↦
        TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) q.proj
          (mfderiv I J (f : M → N) q.proj q.snd)) p :=
    (Pullback.contMDiffAt_iff f hfm).2 ⟨contMDiffAt_proj (TangentSpace I : M → Type _),
      (ContMDiff.contMDiff_tangentMap f.contMDiff hm).contMDiffAt⟩
  have hmk : ContMDiffAt (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)) m
      (fun q : TotalSpace E (TangentSpace I : M → Type _) ↦
        TotalSpace.mk' (Fin (Module.finrank 𝕜 E) → 𝕜) (E := fun x ↦ f.isImmersion.tangentRange x hn)
          q.proj ⟨mfderiv I J (f : M → N) q.proj q.snd, ⟨q.snd, rfl⟩⟩) p :=
    (f.hasLocalContMDiffSubbundleFrames_tangentRange hn hm).contMDiffAt_totalSpace_mk le_rfl
      hw fun q ↦ ⟨q.snd, rfl⟩
  exact hmk.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq <| funext fun q ↦
    congrArg (TotalSpace.mk' _ q.proj) <|
      Subtype.ext (f.isImmersion.coe_tangentSpaceEquivTangentRange_apply q.proj hn q.snd))

private def tangentBundleDiffeomorphTangentRangeData :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    { d : TotalSpace E (TangentSpace I : M → Type _) ≃ₘ^m⟮I.prod 𝓘(𝕜, E),
          I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)⟯
          TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.isImmersion.tangentRange x hn) //
      (∀ p, d p = ⟨p.proj, f.isImmersion.tangentSpaceEquivTangentRange p.proj hn p.snd⟩) ∧
        ∀ p, d.symm p =
          ⟨p.proj, (f.isImmersion.tangentSpaceEquivTangentRange p.proj hn).symm p.snd⟩ } :=
  letI := f.tangentRangeTopology (E := E) (V := V) hn
  letI := f.tangentRangeFiberBundle hn hm; letI := f.tangentRangeVectorBundle hn hm
  letI := f.tangentRangeContMDiffVectorBundle hn hm
  ⟨bundleDiffeomorph (fun x : M ↦ f.isImmersion.tangentSpaceEquivTangentRange x hn)
      (f.contMDiff_tangentSpaceEquivTangentRange hn hm),
    bundleDiffeomorph_apply _ _, bundleDiffeomorph_symm_apply _ _⟩

/-- **The tangent bundle of an embedded submanifold is `C^m`-isomorphic to its differential image
subbundle.** Over `ℝ` or `ℂ` (`[IsRCLikeNormedField 𝕜]`),
`f.isImmersion.tangentSpaceEquivTangentRange` induces a `C^m` diffeomorphism of total spaces from
`TangentSpace I` onto `x ↦ f.isImmersion.tangentRange x hn` equipped with its subbundle structure
inside `f *ᵖ TangentSpace J`. -/
def tangentBundleDiffeomorphTangentRange :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    TotalSpace E (TangentSpace I : M → Type _) ≃ₘ^m⟮I.prod 𝓘(𝕜, E),
      I.prod 𝓘(𝕜, Fin (Module.finrank 𝕜 E) → 𝕜)⟯
      TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.isImmersion.tangentRange x hn) :=
  (f.tangentBundleDiffeomorphTangentRangeData hn hm).val

@[simp] theorem tangentBundleDiffeomorphTangentRange_apply
    (p : TotalSpace E (TangentSpace I : M → Type _)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    f.tangentBundleDiffeomorphTangentRange hn hm p =
      ⟨p.proj, f.isImmersion.tangentSpaceEquivTangentRange p.proj hn p.snd⟩ :=
  (f.tangentBundleDiffeomorphTangentRangeData hn hm).property.left p

@[simp] theorem tangentBundleDiffeomorphTangentRange_symm_apply
    (p : TotalSpace (Fin (Module.finrank 𝕜 E) → 𝕜) (fun x ↦ f.isImmersion.tangentRange x hn)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    (f.tangentBundleDiffeomorphTangentRange (E := E) hn hm).symm p =
      ⟨p.proj, (f.isImmersion.tangentSpaceEquivTangentRange p.proj hn).symm p.snd⟩ :=
  (f.tangentBundleDiffeomorphTangentRangeData hn hm).property.right p

/-- Composing `f.tangentBundleDiffeomorphTangentRange` with subbundle inclusion and
`Bundle.Pullback.lift f` recovers `tangentMap I J f`. -/
theorem lift_mk'_tangentBundleDiffeomorphTangentRange_eq_tangentMap
    (p : TotalSpace E (TangentSpace I : M → Type _)) :
    letI := f.tangentRangeTopology (E := E) (V := V) hn; letI := f.tangentRangeFiberBundle hn hm
    Pullback.lift f (TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J))
      (f.tangentBundleDiffeomorphTangentRange hn hm p).proj
      (f.tangentBundleDiffeomorphTangentRange hn hm p).snd.val) =
      tangentMap I J (f : M → N) p := by
  obtain ⟨x, v⟩ := p
  rw [f.tangentBundleDiffeomorphTangentRange_apply hn hm ⟨x, v⟩]
  simp only [Pullback.lift_mk, f.isImmersion.coe_tangentSpaceEquivTangentRange_apply]
  exact TotalSpace.ext (tangentMap_proj (I := I) (I' := J) (p := ⟨x, v⟩)).symm
    (heq_of_eq (tangentMap_snd (I := I) (I' := J) (f := (f : M → N)) (X := v)).symm)

end BundleDiffeomorph

end TauCeti.SmoothEmbedding
