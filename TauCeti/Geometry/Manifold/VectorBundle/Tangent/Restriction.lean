/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Restricting tangent Hom fields to open products

The canonical tangent-space identifications of open submanifolds preserve the native Hom-section
regularity, at every order (`restrictOpenTangentSpaceHom`, `restrictOpenTangentSpaceEnd`, and
`restrictOpenTargetTangentHom` for arbitrary source vector bundles). The coordinate comparison uses
the inherited tangent charts and applies to arbitrary normed models, without completeness or
finite-dimensionality assumptions.
-/

public noncomputable section

open Bundle FiberBundle TopologicalSpace
open scoped Manifold ContDiff Topology

namespace TauCeti.Manifold
variable {𝕜 E H M F H' N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]

/-- Read a tangent Hom field restricted to open submanifolds in the inherited coordinates. -/
theorem inCoordinates_openTangentSpaceHom_eq {U : Opens M} {V : Opens N} {x y : U} {x' y' : V}
    (A : TangentSpace I (y : M) →L[𝕜] TangentSpace I' (y' : N))
    (hy' : y' ∈ (trivializationAt F (TangentSpace I' : V → Type _) x').baseSet)
    (hyN : (y' : N) ∈ (trivializationAt F (TangentSpace I' : N → Type _) (x' : N)).baseSet)
    (hs : ∀ v : E, tangentSpaceOpenEquiv (I := I) y
      ((trivializationAt E (TangentSpace I : U → Type _) x).symmL 𝕜 y v) =
        (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL 𝕜 (y : M) v)
    (ht : ∀ v : F, tangentSpaceOpenEquiv (I := I') y'
      ((trivializationAt F (TangentSpace I' : V → Type _) x').symmL 𝕜 y' v) =
        (trivializationAt F (TangentSpace I' : N → Type _) (x' : N)).symmL 𝕜 (y' : N) v) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I : U → Type _) F
      (TangentSpace I' : V → Type _) x y x' y'
      ((tangentSpaceOpenEquiv (I := I') y').symm.toContinuousLinearMap.comp
        (A.comp (tangentSpaceOpenEquiv (I := I) y).toContinuousLinearMap)) =
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F
      (TangentSpace I' : N → Type _) (x : M) (y : M) (x' : N) (y' : N) A := by
  have hout (w : TangentSpace I' (y' : N)) :
      (trivializationAt F (TangentSpace I' : V → Type _) x').continuousLinearMapAt 𝕜 y'
        ((tangentSpaceOpenEquiv (I := I') y').symm w) =
      (trivializationAt F (TangentSpace I' : N → Type _) (x' : N)).continuousLinearMapAt 𝕜
        (y' : N) w := by
    let z := (trivializationAt F (TangentSpace I' : N → Type _) (x' : N)).continuousLinearMapAt
      𝕜 (y' : N) w
    have hw : (tangentSpaceOpenEquiv (I := I') y').symm w =
        (trivializationAt F (TangentSpace I' : V → Type _) x').symmL 𝕜 y' z := by
      apply (tangentSpaceOpenEquiv (I := I') y').injective
      rw [ContinuousLinearEquiv.apply_symm_apply, ht]
      exact (Trivialization.symmL_continuousLinearMapAt
        (trivializationAt F (TangentSpace I' : N → Type _) (x' : N)) hyN w).symm
    rw [hw, Trivialization.continuousLinearMapAt_symmL _ hy']
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [hs, hout]

/-- The inherited tangent Hom coordinates agree with the ambient coordinates near every pair
of points of open submanifolds. The field itself need not be regular. -/
theorem eventually_inCoordinates_openTangentSpaceHom_eq {U : Opens M} {V : Opens N}
    (x : U) (x' : V) :
    ∀ᶠ q : U × V in 𝓝 (x, x'), ∀ A :
      TangentSpace I (q.1 : M) →L[𝕜] TangentSpace I' (q.2 : N),
      ContinuousLinearMap.inCoordinates E (TangentSpace I : U → Type _) F
        (TangentSpace I' : V → Type _) x q.1 x' q.2
        ((tangentSpaceOpenEquiv (I := I') q.2).symm.toContinuousLinearMap.comp
          (A.comp (tangentSpaceOpenEquiv (I := I) q.1).toContinuousLinearMap)) =
      ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F
        (TangentSpace I' : N → Type _) (x : M) (q.1 : M) (x' : N) (q.2 : N) A := by
  filter_upwards [continuousAt_fst.eventually
    (eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) x),
    continuousAt_snd.eventually
      (eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I') x'),
    continuousAt_snd.eventually
      ((trivializationAt F (TangentSpace I' : V → Type _) x').open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F (TangentSpace I' : V → Type _) x')),
    (continuousAt_subtype_val.comp continuousAt_snd).eventually
      ((trivializationAt F (TangentSpace I' : N → Type _) (x' : N)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F (TangentSpace I' : N → Type _) (x' : N)))]
      with q hs ht hqV hqN
  exact fun A ↦ inCoordinates_openTangentSpaceHom_eq A hqV hqN hs ht

/-- Restrict a tangent Hom field on a product to open submanifolds in both factors. -/
def restrictOpenTangentSpaceHom
    (A : ∀ q : M × N, TangentSpace I q.1 →L[𝕜] TangentSpace I' q.2)
    (U : Opens M) (V : Opens N) (q : U × V) :
    TangentSpace I q.1 →L[𝕜] TangentSpace I' q.2 :=
  (tangentSpaceOpenEquiv (I := I') q.2).symm.toContinuousLinearMap.comp
    ((A (q.1, q.2)).comp (tangentSpaceOpenEquiv (I := I) q.1).toContinuousLinearMap)

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
@[simp]
theorem restrictOpenTangentSpaceHom_apply
    (A : ∀ q : M × N, TangentSpace I q.1 →L[𝕜] TangentSpace I' q.2)
    (U : Opens M) (V : Opens N) (q : U × V) (v : TangentSpace I q.1) :
    restrictOpenTangentSpaceHom A U V q v = (tangentSpaceOpenEquiv (I := I') q.2).symm
      (A (q.1, q.2) (tangentSpaceOpenEquiv (I := I) q.1 v)) := (rfl)

/-- Restricting a native tangent Hom section to open products preserves its exact regularity. -/
theorem contMDiff_restrictOpenTangentSpaceHom {n : ℕ∞ω}
    (A : ∀ q : M × N, TangentSpace I q.1 →L[𝕜] TangentSpace I' q.2)
    (U : Opens M) (V : Opens N)
    (hA : ContMDiff (I.prod I') ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] F)) n
      (fun q : M × N ↦ TotalSpace.mk' (E →L[𝕜] F)
        (E := fun q : M × N ↦
          (((ContMDiffMap.fst : C^∞⟮I.prod I', M × N; I, M⟯) : M × N → M) *ᵖ
            (TangentSpace I)) q →L[𝕜]
          (((ContMDiffMap.snd : C^∞⟮I.prod I', M × N; I', N⟯) : M × N → N) *ᵖ
            (TangentSpace I')) q) q (A q))) :
    ContMDiff (I.prod I') ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] F)) n
      (fun q : U × V ↦ TotalSpace.mk' (E →L[𝕜] F)
        (E := fun q : U × V ↦
          (((ContMDiffMap.fst : C^∞⟮I.prod I', U × V; I, U⟯) : U × V → U) *ᵖ
            (TangentSpace I)) q →L[𝕜]
          (((ContMDiffMap.snd : C^∞⟮I.prod I', U × V; I', V⟯) : U × V → V) *ᵖ
            (TangentSpace I')) q) q (restrictOpenTangentSpaceHom A U V q)) := by
  have hinc : ContMDiff (I.prod I') (I.prod I') n
      (fun q : U × V ↦ ((q.1 : M), (q.2 : N))) :=
    ((contMDiff_subtype_val (I := I) (U := U)).comp contMDiff_fst).prodMk
      ((contMDiff_subtype_val (I := I') (U := V)).comp contMDiff_snd)
  intro q
  have ha := (contMDiffAt_hom_bundle _).mp ((hA.comp hinc) q)
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ha.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [eventually_inCoordinates_openTangentSpaceHom_eq (I := I) (I' := I') q.1 q.2,
    (continuousAt_subtype_val.comp continuousAt_fst).eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (q.1 : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (q.1 : M))),
    (continuousAt_subtype_val.comp continuousAt_snd).eventually
      ((trivializationAt F (TangentSpace I' : N → Type _) (q.2 : N)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F (TangentSpace I' : N → Type _) (q.2 : N))),
    continuousAt_fst.eventually
      ((trivializationAt E (TangentSpace I : U → Type _) q.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) q.1)),
    continuousAt_snd.eventually
      ((trivializationAt F (TangentSpace I' : V → Type _) q.2).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F (TangentSpace I' : V → Type _) q.2))]
      with y he hyM hyN hyU hyV
  -- `erw` identifies each pulled-back tangent fibre with the original model instance.
  erw [ContinuousLinearMap.inCoordinates_pullback_of_mem
    (ContMDiffMap.fst : C^∞⟮I.prod I', M × N; I, M⟯)
    (ContMDiffMap.snd : C^∞⟮I.prod I', M × N; I', N⟯) _ _ _ hyM hyN,
    ContinuousLinearMap.inCoordinates_pullback_of_mem
      (ContMDiffMap.fst : C^∞⟮I.prod I', U × V; I, U⟯)
      (ContMDiffMap.snd : C^∞⟮I.prod I', U × V; I', V⟯) _ _ _ hyU hyV]
  exact he (A (y.1, y.2))

section Endomorphism

variable {ES HS S : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
  [TopologicalSpace HS] {IS : ModelWithCorners 𝕜 ES HS}
  [TopologicalSpace S] [ChartedSpace HS S]

/-- Restrict a parameter-dependent tangent endomorphism to an open target submanifold. -/
def restrictOpenTangentSpaceEnd
    (A : ∀ q : S × M, TangentSpace I q.2 →L[𝕜] TangentSpace I q.2)
    (U : Opens M) (q : S × U) : TangentSpace I q.2 →L[𝕜] TangentSpace I q.2 :=
  (tangentSpaceOpenEquiv (I := I) q.2).symm.toContinuousLinearMap.comp
    ((A (q.1, q.2)).comp (tangentSpaceOpenEquiv (I := I) q.2).toContinuousLinearMap)

omit [IsManifold I 1 M] [IsManifold I' 1 N] [TopologicalSpace S] in
@[simp]
theorem restrictOpenTangentSpaceEnd_apply
    (A : ∀ q : S × M, TangentSpace I q.2 →L[𝕜] TangentSpace I q.2)
    (U : Opens M) (q : S × U) (v : TangentSpace I q.2) :
    restrictOpenTangentSpaceEnd A U q v = (tangentSpaceOpenEquiv (I := I) q.2).symm
      (A (q.1, q.2) (tangentSpaceOpenEquiv (I := I) q.2 v)) := (rfl)

/-- Open restriction preserves the joint finite regularity of a parameter-dependent tangent
endomorphism field, including continuous fields. -/
theorem contMDiff_restrictOpenTangentSpaceEnd {n : ℕ∞ω}
    (A : ∀ q : S × M, TangentSpace I q.2 →L[𝕜] TangentSpace I q.2) (U : Opens M)
    (hA : ContMDiff (IS.prod I) (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
      (fun q : S × M ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun x : M ↦ TangentSpace I x →L[𝕜] TangentSpace I x) q.2 (A q))) :
    ContMDiff (IS.prod I) (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
      (fun q : S × U ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun x : U ↦ TangentSpace I x →L[𝕜] TangentSpace I x) q.2
        (restrictOpenTangentSpaceEnd A U q)) := by
  have hinc : ContMDiff (IS.prod I) (IS.prod I) n
      (fun q : S × U ↦ (q.1, (q.2 : M))) :=
    contMDiff_fst.prodMk ((contMDiff_subtype_val (I := I) (U := U)).comp contMDiff_snd)
  intro q
  have ha := (contMDiffAt_hom_bundle _).mp ((hA.comp hinc) q)
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ha.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [continuousAt_snd.eventually
    (eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) q.2),
    continuousAt_snd.eventually
      ((trivializationAt E (TangentSpace I : U → Type _) q.2).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) q.2)),
    (continuousAt_subtype_val.comp continuousAt_snd).eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (q.2 : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (q.2 : M)))]
      with y hs hyU hyM
  exact inCoordinates_openTangentSpaceHom_eq (A (y.1, y.2)) hyU hyM hs hs

end Endomorphism

section TargetTangentHom

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {W : M → Type*}
  [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [FiberBundle G W] [VectorBundle 𝕜 G W]

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
/-- Restrict a Hom field valued in the tangent bundle to an open submanifold `U`, landing in
continuous linear maps from the restricted source bundle to `TangentSpace I` on `U`. -/
def restrictOpenTargetTangentHom
    (A : ∀ x : M, W x →L[𝕜] TangentSpace I x) (U : Opens M) (x : U) :
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ W) x →L[𝕜] TangentSpace I x :=
  (tangentSpaceOpenEquiv (I := I) x).symm.toContinuousLinearMap.comp (A x)

omit [IsManifold I 1 M] [IsManifold I' 1 N] in
@[simp]
theorem restrictOpenTargetTangentHom_apply
    (A : ∀ x : M, W x →L[𝕜] TangentSpace I x) (U : Opens M) (x : U)
    (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ W) x) :
    dsimp% only [ContinuousMap.coe_mk]
      (restrictOpenTargetTangentHom A U x v = (tangentSpaceOpenEquiv (I := I) x).symm (A x v)) :=
  (rfl)

omit [IsManifold I' 1 N] in
/-- Near any point `x` of an open submanifold `U`, the Hom coordinates of
`restrictOpenTargetTangentHom A U` agree with the ambient Hom coordinates of `A`. -/
theorem eventually_inCoordinates_openTargetTangentHom_eq
    (A : ∀ x : M, W x →L[𝕜] TangentSpace I x) (U : Opens M) (x : U) :
    (fun y : U ↦ ContinuousLinearMap.inCoordinates G
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ W) E
        (TangentSpace I : U → Type _) x y x y (restrictOpenTargetTangentHom A U y)) =ᶠ[𝓝 x]
      (fun y : U ↦ ContinuousLinearMap.inCoordinates G W E
        (TangentSpace I : M → Type _) (x : M) (y : M) (x : M) (y : M) (A y)) := by
  let ι : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
  filter_upwards [eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) x,
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtype_val.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (x : M))),
    continuousAt_subtype_val.eventually
      ((trivializationAt G W (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt G W (x : M)))]
      with y ht hyU hyM hyW
  have hout (w : TangentSpace I (y : M)) :
      (trivializationAt E (TangentSpace I : U → Type _) x).continuousLinearMapAt 𝕜 y
        ((tangentSpaceOpenEquiv (I := I) y).symm w) =
      (trivializationAt E (TangentSpace I : M → Type _) (x : M)).continuousLinearMapAt 𝕜
        (y : M) w := by
    let z := (trivializationAt E (TangentSpace I : M → Type _) (x : M)).continuousLinearMapAt
      𝕜 (y : M) w
    have hw : (tangentSpaceOpenEquiv (I := I) y).symm w =
        (trivializationAt E (TangentSpace I : U → Type _) x).symmL 𝕜 y z := by
      apply (tangentSpaceOpenEquiv (I := I) y).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, ht]
      exact (Trivialization.symmL_continuousLinearMapAt
        (trivializationAt E (TangentSpace I : M → Type _) (x : M)) hyM w).symm
    rw [hw, Trivialization.continuousLinearMapAt_symmL _ hyU]
  have hin (v : G) :
      (trivializationAt G (ι *ᵖ W) x).symmL 𝕜 y v =
        (trivializationAt G W (x : M)).symmL 𝕜 (y : M) v := by
    have hyW' : y ∈ (trivializationAt G (ι *ᵖ W) x).baseSet := hyW
    rw [← Trivialization.symm_continuousLinearEquivAt_eq _ hyW',
      ← Trivialization.symm_continuousLinearEquivAt_eq _ hyW]
    simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
      Trivialization.continuousLinearEquivAt_pullback]
    rfl
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousMap.coe_mk, restrictOpenTargetTangentHom_apply]
  -- `erw` identifies the pulled-back source fibre `(ι *ᵖ W) y` with `W y`.
  erw [hin v]
  exact hout _

omit [IsManifold I' 1 N] in
/-- A Hom field valued in the tangent bundle is `C^n` at a point `x` of an open submanifold `U`
exactly when its open restriction `restrictOpenTargetTangentHom A U` is `C^n` at `x`. -/
theorem contMDiffAt_restrictOpenTargetTangentHom_iff {n : ℕ∞ω}
    (A : ∀ x : M, W x →L[𝕜] TangentSpace I x) (U : Opens M) (x : U) :
    ContMDiffAt I (I.prod 𝓘(𝕜, G →L[𝕜] E)) n
      (fun y : U ↦ TotalSpace.mk' (G →L[𝕜] E)
        (E := fun y : U ↦
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ W) y →L[𝕜] TangentSpace I y)
        y (restrictOpenTargetTangentHom A U y)) x ↔
    ContMDiffAt I (I.prod 𝓘(𝕜, G →L[𝕜] E)) n
      (fun z : M ↦ TotalSpace.mk' (G →L[𝕜] E)
        (E := fun z : M ↦ W z →L[𝕜] TangentSpace I z) z (A z)) (x : M) := by
  rw [← contMDiffAt_subtype_iff (x := x), contMDiffAt_hom_bundle, contMDiffAt_hom_bundle]
  have heq := eventually_inCoordinates_openTargetTangentHom_eq (G := G) A U x
  exact ⟨fun ⟨_, h⟩ ↦ ⟨contMDiff_subtype_val.contMDiffAt, h.congr_of_eventuallyEq heq.symm⟩,
    fun ⟨_, h⟩ ↦ ⟨contMDiffAt_id, h.congr_of_eventuallyEq heq⟩⟩

omit [IsManifold I' 1 N] in
/-- Restricting a Hom section with values in the tangent bundle to an open submanifold preserves
its exact `C^n` regularity, without finite-rank or smooth-bundle assumptions on the source. -/
theorem contMDiff_restrictOpenTargetTangentHom {n : ℕ∞ω}
    (A : ∀ x : M, W x →L[𝕜] TangentSpace I x) (U : Opens M)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, G →L[𝕜] E)) n
      (fun x : M ↦ TotalSpace.mk' (G →L[𝕜] E)
        (E := fun x : M ↦ W x →L[𝕜] TangentSpace I x) x (A x))) :
    ContMDiff I (I.prod 𝓘(𝕜, G →L[𝕜] E)) n
      (fun x : U ↦ TotalSpace.mk' (G →L[𝕜] E)
        (E := fun x : U ↦
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ W) x →L[𝕜] TangentSpace I x)
        x (restrictOpenTargetTangentHom A U x)) := fun x ↦
  (contMDiffAt_restrictOpenTargetTangentHom_iff (G := G) A U x).2 (hA (x : M))

end TargetTangentHom

end TauCeti.Manifold

