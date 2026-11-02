/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Transposes and bidual extensions of bounded bilinear maps

`ContinuousLinearMap.bilinearTranspose` transposes a bounded bilinear map
`B : E →L[𝕜] F →L[𝕜] G` to the map `(f, x, y) ↦ f (B x y)`.
Three successive transposes give `ContinuousLinearMap.arensExtension`, the extension to
the biduals with the first variable evaluated last. Flipping before and after this
construction gives the other order of evaluation. These constructions underlie the
two Arens products of a normed algebra.

The construction uses Mathlib's bounded composition and precomposition maps.
See H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.6.
-/

public noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

-- These local shortcuts keep nested dual operator searches within the synthesis depth limit.
/-- The inherited seminormed group on a continuous dual, used locally for iterated duals. -/
local instance arensDualSeminormedAddCommGroup (X : Type*)
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] :
    SeminormedAddCommGroup (StrongDual 𝕜 X) := inferInstance

/-- The inherited scalar action on a continuous dual, used locally for iterated duals. -/
local instance arensDualNormedSpace (X : Type*)
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

/-- The inherited seminormed group on a bidual, used locally to shorten instance search. -/
local instance arensBidualSeminormedAddCommGroup (X : Type*)
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] :
    SeminormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance

/-- The inherited scalar action on a bidual, used locally to shorten instance search. -/
local instance arensBidualNormedSpace (X : Type*)
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance

/-- Transpose a bounded bilinear map by pairing its value with a continuous functional. -/
def bilinearTranspose (B : E →L[𝕜] F →L[𝕜] G) :
    StrongDual 𝕜 G →L[𝕜] E →L[𝕜] StrongDual 𝕜 F :=
  (precompR E (compL 𝕜 F G 𝕜)).flip B

@[simp]
theorem bilinearTranspose_apply (B : E →L[𝕜] F →L[𝕜] G)
    (f : StrongDual 𝕜 G) (x : E) (y : F) :
    B.bilinearTranspose f x y = f (B x y) := (rfl)

/-- Transposition does not increase the bilinear operator norm. -/
theorem norm_bilinearTranspose_le (B : E →L[𝕜] F →L[𝕜] G) :
    ‖B.bilinearTranspose‖ ≤ ‖B‖ := by
  refine opNorm_le_bound _ (norm_nonneg B) fun f => ?_
  refine opNorm_le_bound _ (by positivity) fun x => ?_
  refine opNorm_le_bound _ (by positivity) fun y => ?_
  calc
    ‖B.bilinearTranspose f x y‖ ≤ ‖f‖ * ‖B x y‖ := f.le_opNorm _
    _ ≤ ‖f‖ * (‖B‖ * ‖x‖ * ‖y‖) := by gcongr; exact B.le_opNorm₂ x y
    _ = ‖B‖ * ‖f‖ * ‖x‖ * ‖y‖ := by ring

/-- The Arens extension of a bounded bilinear map, evaluating the second bidual argument
inside the first. -/
def arensExtension (B : E →L[𝕜] F →L[𝕜] G) :
    StrongDual 𝕜 (StrongDual 𝕜 E) →L[𝕜]
      StrongDual 𝕜 (StrongDual 𝕜 F) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G) :=
  B.bilinearTranspose.bilinearTranspose.bilinearTranspose

/-- The defining iterated-dual formula for the Arens extension. -/
@[simp]
theorem arensExtension_apply (B : E →L[𝕜] F →L[𝕜] G)
    (x : StrongDual 𝕜 (StrongDual 𝕜 E)) (y : StrongDual 𝕜 (StrongDual 𝕜 F))
    (f : StrongDual 𝕜 G) :
    B.arensExtension x y f = x (B.bilinearTranspose.bilinearTranspose y f) := (rfl)

/-- The bidual extension has at most the norm of the original bilinear map. -/
theorem norm_arensExtension_le (B : E →L[𝕜] F →L[𝕜] G) :
    ‖B.arensExtension‖ ≤ ‖B‖ :=
  (norm_bilinearTranspose_le _).trans
    ((norm_bilinearTranspose_le _).trans (norm_bilinearTranspose_le B))

/-- The pointwise norm estimate for the bidual extension of a bounded bilinear map. -/
theorem norm_arensExtension_apply_le (B : E →L[𝕜] F →L[𝕜] G)
    (x : StrongDual 𝕜 (StrongDual 𝕜 E)) (y : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    ‖B.arensExtension x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  calc
    _ ≤ ‖B.arensExtension‖ * ‖x‖ * ‖y‖ := B.arensExtension.le_opNorm₂ x y
    _ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by gcongr; exact norm_arensExtension_le B

/-- The extension agrees with the original bilinear map on the canonical bidual images. -/
@[simp]
theorem arensExtension_inclusionInDoubleDual (B : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) :
    B.arensExtension (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y) =
        NormedSpace.inclusionInDoubleDual 𝕜 G (B x y) := by
  ext f
  simp

/-- The Arens extension is weak-star continuous in its first bidual variable. -/
theorem continuous_toWeakDual_arensExtension_left (B : E →L[𝕜] F →L[𝕜] G)
    (y : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    Continuous (fun x : WeakDual 𝕜 (StrongDual 𝕜 E) =>
      StrongDual.toWeakDual (B.arensExtension x.toStrongDual y)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact WeakDual.eval_continuous (B.bilinearTranspose.bilinearTranspose y f)

/-- If the first argument is in the original space, the extension is also weak-star
continuous in its second variable. -/
theorem continuous_toWeakDual_arensExtension_right (B : E →L[𝕜] F →L[𝕜] G) (x : E) :
    Continuous (fun y : WeakDual 𝕜 (StrongDual 𝕜 F) =>
      StrongDual.toWeakDual
        (B.arensExtension (NormedSpace.inclusionInDoubleDual 𝕜 E x) y.toStrongDual)) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact WeakDual.eval_continuous (B.bilinearTranspose f x)

end ContinuousLinearMap
