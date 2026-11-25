/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CoulombGauge
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic

/-!
# Coulomb gauge on compact manifolds

Every smooth one-form on a compact boundaryless oriented Riemannian manifold admits a
global Coulomb gauge. The proof restricts the one-form to each connected component, solves
the connected gauge equation there, and glues the resulting potentials.

## Main results

* `TauCeti.SmoothForm.codifferential_mpullback_subtypeVal`: the codifferential commutes
  with restriction to an open submanifold.
* `TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero_of_compactSpace`:
  subtracting the exterior derivative of some smooth function makes a one-form coclosed.
-/

public section

noncomputable section

open Bundle Manifold MeasureTheory TopologicalSpace
open scoped ContDiff Manifold TauCeti

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

section Restriction

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

private theorem formHodgeStar_compContinuousLinearMap
    {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℝ V] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] {m k l : ℕ}
    [Fact (Module.finrank ℝ V = m)] [Fact (Module.finrank ℝ W = m)]
    (o : Orientation ℝ V (Fin m)) (D : V ≃ₗᵢ[ℝ] W)
    (hV : k + l = Module.finrank ℝ V) (hW : k + l = Module.finrank ℝ W)
    (a : W [⋀^Fin k]→L[ℝ] ℝ) :
    ((Orientation.map (Fin m) D.toLinearEquiv o).formHodgeStar hW a).compContinuousLinearMap
        D.toLinearIsometry.toContinuousLinearMap =
      o.formHodgeStar hV (a.compContinuousLinearMap D.toLinearIsometry.toContinuousLinearMap) := by
  obtain ⟨u, rfl⟩ := ((alternatingFormEquiv W k).surjective.comp
    (exteriorPower.map_surjective (n := k) D.surjective)) a
  have hmusical (j : ℕ) (v : ⋀[ℝ]^j V) :
      (alternatingFormEquiv W j (exteriorPower.map j D.toLinearMap v)).compContinuousLinearMap
          D.toLinearIsometry.toContinuousLinearMap = alternatingFormEquiv V j v :=
    D.toLinearIsometry.alternatingFormEquiv_map v
  dsimp only [Function.comp_apply]
  rw [hmusical, Orientation.formHodgeStar_alternatingFormEquiv, o.hodgeStar_map D hV hW,
    hmusical, Orientation.formHodgeStar_alternatingFormEquiv]

private theorem hodgeStar_mpullback_subtypeVal {m k l : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (U : Opens M) (a : SmoothForm I M ℝ k) :
    hodgeStar (o.restrict U) hkl (mpullback (Subtype.val : U → M) contMDiff_subtypeVal a) =
      mpullback (Subtype.val : U → M) contMDiff_subtypeVal (hodgeStar o hkl a) := by
  apply Subtype.ext
  funext x
  let D := Manifold.tangentSpaceOpenEquiv (I := I) x
  have ho := (Manifold.Orientation.isOrientationPreservingAt_iff_of_coe_eq
    (o.restrict U) o (Subtype.val : U → M) x D (Manifold.mfderiv_subtype_val x).symm).1
      (o.isOrientationPreservingAt_restrict U x)
  let e := D.toLinearEquiv.isometryOfInner fun v w ↦
    (Manifold.inner_tangentSpace_open U x v w).symm
  let := (o.restrict U).fact_finrank_tangentSpace x
  let := o.fact_finrank_tangentSpace (x : M)
  have hD : e.toLinearIsometry.toContinuousLinearMap = mfderiv I I (Subtype.val : U → M) x := by
    rw [Manifold.mfderiv_subtype_val]
    rfl
  simp only [coe_hodgeStar, coe_mpullback, RoughForm.hodgeStar_apply,
    TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, ← hD]
  have h := formHodgeStar_compContinuousLinearMap ((o.restrict U).orientationAt x) e
    (hkl.trans ((o.restrict U).fact_finrank_tangentSpace x).out.symm)
    (hkl.trans (o.fact_finrank_tangentSpace (x : M)).out.symm) (a.val x)
  rw [show e.toLinearEquiv = D.toLinearEquiv from rfl, ho] at h
  exact h.symm

/-- The codifferential commutes with restriction to an open submanifold. -/
theorem codifferential_mpullback_subtypeVal {m k l : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (U : Opens M) (a : SmoothForm I M ℝ (k + 1)) :
    codifferential (o.restrict U) hkl (mpullback (Subtype.val : U → M) contMDiff_subtypeVal a) =
      mpullback (Subtype.val : U → M) contMDiff_subtypeVal (codifferential o hkl a) := by
  have hlk : l + 1 + k = m := by omega
  rw [codifferential_apply (o.restrict U) hkl hlk, codifferential_apply o hkl hlk,
    hodgeStar_mpullback_subtypeVal, mextDerivₗ_mpullback, hodgeStar_mpullback_subtypeVal, map_smul]

end Restriction

private theorem exists_zeroForm_mpullback_eq_of_partition {U : M → Opens M}
    (hx : ∀ x, x ∈ U x) (hU : ∀ {x y}, y ∈ U x → U y = U x)
    (f : (V : Set.range U) → SmoothForm I V.val ℝ 0) :
    ∃ F : SmoothForm I M ℝ 0, ∀ x,
      mpullback (Subtype.val : U x → M) contMDiff_subtypeVal F = f ⟨U x, ⟨x, rfl⟩⟩ := by
  let C (x : M) : Set.range U := ⟨U x, ⟨x, rfl⟩⟩
  let w (V : Set.range U) : M → ℝ :=
    (Subtype.val : V.val → M).extend (fun y ↦ (f V).val y 0) 0
  let u (x : M) := w (C x) x
  have heq (x : M) (y : U x) : u y = (f (C x)).val y 0 := by
    have hC : C y = C x := Subtype.ext (hU y.property)
    exact (congrArg (fun V ↦ w V y) hC).trans
      (Subtype.val_injective.extend_apply _ _ y)
  have hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u := by
    intro x
    let y : U x := ⟨x, hx x⟩
    apply (contMDiffAt_subtype_iff (x := y)).1
    exact (contMDiff_apply_zero (f (C x)) y).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z ↦ heq x z)
  let F := ofFunction (I := I) ⟨u, hu⟩
  refine ⟨F, fun x ↦ ?_⟩
  apply Subtype.ext
  funext z
  rw [coe_mpullback_subtype_val_apply]
  ext v
  rw [Subsingleton.elim v 0]
  exact (congrFun (ofFunction_apply_zero ⟨u, hu⟩) z).trans (heq x z)

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [CompactSpace M] [T2Space M]

/-- Every smooth one-form on a closed oriented Riemannian manifold is the sum of an exact form
and a coclosed form. The potential is obtained by solving the connected Coulomb gauge equation
on each component. -/
theorem exists_codifferential_sub_mextDerivₗ_eq_zero_of_compactSpace {m l : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (hkl : 0 + 1 + l = m)
    (a : SmoothForm I M ℝ 1) :
    ∃ f : SmoothForm I M ℝ 0, codifferential o hkl (a - mextDerivₗ I 0 f) = 0 := by
  let : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  let U (x : M) : Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hsolve (V : Set.range U) :
      ∃ f : SmoothForm I V.val ℝ 0, codifferential (o.restrict V.val) hkl
        (mpullback (Subtype.val : V.val → M) contMDiff_subtypeVal a - mextDerivₗ I 0 f) = 0 := by
    obtain ⟨V, x, rfl⟩ := V
    let : CompactSpace (U x) :=
      isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
    let : PreconnectedSpace (U x) :=
      isPreconnected_iff_preconnectedSpace.mp isConnected_connectedComponent.isPreconnected
    let : MeasurableSpace (U x) := borel (U x)
    let : BorelSpace (U x) := ⟨rfl⟩
    obtain ⟨f, -, hf⟩ :=
      exists_codifferential_sub_mextDerivₗ_eq_zero (o.restrict (U x)) hkl
        (mpullback (Subtype.val : U x → M) contMDiff_subtypeVal a)
    exact ⟨f, hf⟩
  choose f hf using hsolve
  obtain ⟨F, hF⟩ := exists_zeroForm_mpullback_eq_of_partition (I := I)
    (fun x ↦ show x ∈ U x from mem_connectedComponent)
    (fun h ↦ SetLike.coe_injective (connectedComponent_eq h).symm) f
  refine ⟨F, ?_⟩
  apply Subtype.ext
  funext x
  let y : U x := ⟨x, mem_connectedComponent⟩
  have hpullδ : mpullback (Subtype.val : U x → M) contMDiff_subtypeVal
      (codifferential o hkl (a - mextDerivₗ I 0 F)) = 0 := by
    rw [← codifferential_mpullback_subtypeVal, map_sub, ← mextDerivₗ_mpullback, hF x]
    exact hf ⟨U x, ⟨x, rfl⟩⟩
  ext v
  rw [Subsingleton.elim v 0]
  simp only [Submodule.coe_zero, Pi.zero_apply, ContinuousAlternatingMap.coe_zero]
  change (codifferential o hkl (a - mextDerivₗ I 0 F)).val x 0 = (0 : ℝ)
  have h := congrArg (β := ℝ) (fun b : SmoothForm I (U x) ℝ 0 ↦ b.val y 0) hpullδ
  simp only [coe_mpullback_subtype_val_apply, Submodule.coe_zero, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero] at h
  exact h

end TauCeti.SmoothForm
