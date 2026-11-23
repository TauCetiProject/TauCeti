/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.Pullback.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Restricting tangent fields to open submanifolds

The canonical tangent-space identifications of open submanifolds preserve regularity, at every
order. Near every point, the tangent-bundle trivialization of an open submanifold reads tangent
vectors as the ambient one does
(`TauCeti.Manifold.eventually_trivializationAt_tangentSpace_opens_eq`). So a map into the tangent
bundle of an open submanifold is `C^n` exactly when it is as a map into the ambient tangent
bundle (`TauCeti.Manifold.contMDiffAt_tangentBundle_opens_iff`), and the same holds for native Hom
sections restricted to open products and for restricted vector fields
(`TauCeti.Manifold.contMDiffAt_restrictOpen_vectorField`). The coordinate comparison uses the
inherited tangent charts and applies to arbitrary normed models, without completeness or
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

section RestrictOpenSection

/-! ### Sections of the tangent bundle over open submanifolds -/

/-- Near a point `x` of an open submanifold `U`, the tangent-bundle trivialization of `U` at `x`
reads every tangent vector as the ambient trivialization of `M` at `x` does. -/
theorem eventually_trivializationAt_tangentSpace_opens_eq {U : Opens M} (x : U) :
    ∀ᶠ y in 𝓝 x, ∀ v : E,
      (trivializationAt E (TangentSpace I : U → Type _) x ⟨y, v⟩).2 =
        (trivializationAt E (TangentSpace I : M → Type _) (x : M) ⟨(y : M), v⟩).2 := by
  filter_upwards [eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) x,
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtypeVal.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (x : M)))]
    with y hs hyU hyM v
  -- The ambient inverse trivialization sends the coordinates of `v` in `U` back to `v`, so the
  -- ambient trivialization sends `v` to them.
  have h₁ := Trivialization.symm_apply_apply_mk
    (trivializationAt E (TangentSpace I : U → Type _) x) hyU (v : TangentSpace I y)
  have h := hs (trivializationAt E (TangentSpace I : U → Type _) x ⟨y, v⟩).2
  rw [Trivialization.symmL_apply _ hyU, Trivialization.symmL_apply _ hyM, h₁] at h
  -- `tangentSpaceOpenEquiv y` is the identity of the model space `E`.
  have h' : v = (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symm (y : M)
      (trivializationAt E (TangentSpace I : U → Type _) x ⟨y, v⟩).2 :=
    (tangentSpaceOpenEquiv_apply y v).symm.trans h
  calc (trivializationAt E (TangentSpace I : U → Type _) x ⟨y, v⟩).2
      = (trivializationAt E (TangentSpace I : M → Type _) (x : M) ⟨(y : M),
          (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symm (y : M)
            (trivializationAt E (TangentSpace I : U → Type _) x ⟨y, v⟩).2⟩).2 := by
        rw [Trivialization.apply_mk_symm _ hyM]
    _ = (trivializationAt E (TangentSpace I : M → Type _) (x : M) ⟨(y : M), v⟩).2 := by
        rw [← h']

/-- **Regularity of restrictions to open submanifolds.** A map `q ↦ (g q, V q)` into the tangent
bundle of an open submanifold `U` is `C^n` at a point exactly when the same map into the tangent
bundle of the ambient manifold is: the tangent spaces of `U` and `M` are the same, and so are
their trivializations near every point. -/
theorem contMDiffAt_tangentBundle_opens_iff {G N' : Type*} [TopologicalSpace G]
    {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N'] [ChartedSpace G N'] {n : ℕ∞ω}
    {U : Opens M} {g : N' → U} {V : N' → E} {q : N'} :
    ContMDiffAt J I.tangent n (fun q ↦ (⟨g q, V q⟩ : TangentBundle I U)) q ↔
      ContMDiffAt J I.tangent n (fun q ↦ (⟨(g q : M), V q⟩ : TangentBundle I M)) q := by
  rw [contMDiffAt_totalSpace_iff, contMDiffAt_totalSpace_iff]
  simp only
  rw [← ContMDiffAt.subtypeVal_comp_iff U g q]
  refine and_congr_right fun hg ↦ Filter.EventuallyEq.contMDiffAt_iff ?_
  -- Near `q`, the point `g` stays where the two trivializations agree.
  filter_upwards [((ContMDiffAt.subtypeVal_comp_iff U g q).1 hg).continuousAt.eventually
    (eventually_trivializationAt_tangentSpace_opens_eq (I := I) (g q))] with y hy
  exact hy (V y)

end RestrictOpenSection

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
    (continuousAt_subtypeVal.comp continuousAt_snd).eventually
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
    ((contMDiff_subtypeVal (I := I) (U := U)).comp contMDiff_fst).prodMk
      ((contMDiff_subtypeVal (I := I') (U := V)).comp contMDiff_snd)
  intro q
  have ha := (contMDiffAt_hom_bundle _).mp ((hA.comp hinc) q)
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ha.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [eventually_inCoordinates_openTangentSpaceHom_eq (I := I) (I' := I') q.1 q.2,
    (continuousAt_subtypeVal.comp continuousAt_fst).eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (q.1 : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (q.1 : M))),
    (continuousAt_subtypeVal.comp continuousAt_snd).eventually
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
    (ContMDiffMap.snd : C^∞⟮I.prod I', M × N; I', N⟯) _ _ _ _ _ hyM hyN,
    ContinuousLinearMap.inCoordinates_pullback_of_mem
      (ContMDiffMap.fst : C^∞⟮I.prod I', U × V; I, U⟯)
      (ContMDiffMap.snd : C^∞⟮I.prod I', U × V; I', V⟯) _ _ _ _ _ hyU hyV]
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
    contMDiff_fst.prodMk ((contMDiff_subtypeVal (I := I) (U := U)).comp contMDiff_snd)
  intro q
  have ha := (contMDiffAt_hom_bundle _).mp ((hA.comp hinc) q)
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ha.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [continuousAt_snd.eventually
    (eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) q.2),
    continuousAt_snd.eventually
      ((trivializationAt E (TangentSpace I : U → Type _) q.2).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) q.2)),
    (continuousAt_subtypeVal.comp continuousAt_snd).eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (q.2 : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (q.2 : M)))]
      with y hs hyU hyM
  exact inCoordinates_openTangentSpaceHom_eq (A (y.1, y.2)) hyU hyM hs hs

end Endomorphism

section VectorField

/-- Restricting a vector field to an open submanifold, through the canonical tangent-space
identification, preserves `C^n` regularity at a point. -/
theorem contMDiffAt_restrictOpen_vectorField {n : ℕ∞ω} {X : Π x : M, TangentSpace I x}
    {U : Opens M} {x : U} (hX : ContMDiffAt I I.tangent n (T% X) (x : M)) :
    ContMDiffAt I I.tangent n
      (T% fun y : U ↦ (tangentSpaceOpenEquiv (I := I) y).symm (X y)) x := by
  rw [contMDiffAt_section_iff]
  refine (contMDiffAt_subtype_iff.2 ((contMDiffAt_section_iff (x : M)).1 hX)).congr_of_eventuallyEq
    ?_
  filter_upwards [
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtypeVal.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (x : M))),
    eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) x] with y hyU hyM hsymm
  -- Both sides read the same vector in trivializations which agree under the identification.
  have hw : (tangentSpaceOpenEquiv (I := I) y).symm (X y) =
      (trivializationAt E (TangentSpace I : U → Type _) x).symmL 𝕜 y
        ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).continuousLinearMapAt 𝕜
          (y : M) (X y)) := by
    apply (tangentSpaceOpenEquiv (I := I) y).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, hsymm,
      Trivialization.symmL_continuousLinearMapAt _ hyM]
  rw [hw, ← congrFun (Trivialization.coe_linearMapAt_of_mem (R := 𝕜) _ hyU),
    ← congrFun (Trivialization.coe_linearMapAt_of_mem (R := 𝕜) _ hyM)]
  exact Trivialization.continuousLinearMapAt_symmL _ hyU _

end VectorField

end TauCeti.Manifold
