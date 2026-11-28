/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Jet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Restriction of higher jets to open subsets

For an open subset `U` of a manifold `M` with a boundaryless model, the jets over `x ∈ U`
of a vector bundle `V` are canonically identified with the jets of its restriction `V|_U`.
`Opens.restrictJetEquiv` keeps the derivative tuple in the inherited chart and
trivialization. This identifies the jets of a section and its restriction
(`TopologicalSpace.Opens.restrictJetEquiv_jet`) and commutes with jet truncation
(`TopologicalSpace.Opens.truncate_restrictJetEquiv`). On a common chart domain,
`TopologicalSpace.Opens.coordChange_restrictJet` identifies the inherited and ambient
coordinate changes using `TauCeti.symmetricJetCoordChange_congr`.
The comparison uses `TopologicalSpace.Opens.localRep_restrict_eq_of_mem_extChartAt_target`
and the symmetric derivative tuples of `TauCeti.JetBundle`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5 and 12.16–12.17, for jets of local sections.
-/

public section

noncomputable section

open Bundle Filter Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TopologicalSpace.Opens

open TauCeti TauCeti.JetBundle

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommMonoid (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {r : ℕ}

/-- In the source of the inherited extended chart at `j`, the restricted jet coordinate change
equals the ambient coordinate change, in particular on the overlap of the two jet charts. -/
theorem coordChange_restrictJet (U : Opens M) {i j y : U}
    (hy : y ∈ (extChartAt I j).source) :
    coordChange I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) r i j y =
      coordChange I F V r (i : M) (j : M) (y : M) := by
  have htarget := extChartAt_target_mem_nhds' ((extChartAt I j).map_source hy)
  rw [coordChange_def, coordChange_def, ← U.extChartAt_apply j y]
  apply symmetricJetCoordChange_congr
  · filter_upwards [htarget] with z hz
    simp only [Function.comp_apply, U.extChartAt_apply, U.coe_extChartAt_symm_apply j hz]
  · filter_upwards [htarget] with z hz
    have hinv := U.coe_extChartAt_symm_apply j hz
    let e := trivializationAt F V (i : M)
    let e' := trivializationAt F V (j : M)
    let f : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let b := (extChartAt I j).symm z
    ext w
    have hcompare : (e.pullback f).coordChangeL 𝕜 (e'.pullback f) b w =
        e.coordChangeL 𝕜 e' (f b) w := by
      by_cases hb : f b ∈ e.baseSet ∩ e'.baseSet
      · have hp : b ∈ (e.pullback f).baseSet ∩ (e'.pullback f).baseSet := hb
        rw [(e.pullback f).coordChangeL_apply' _ hp, e.coordChangeL_apply' _ hb]
        exact e.coordChange_pullback e' f hb.1 w
      · have hp : b ∉ (e.pullback f).baseSet ∩ (e'.pullback f).baseSet := hb
        rw [(e.pullback f).coordChangeL_of_notMem 𝕜 _ hp, e.coordChangeL_of_notMem 𝕜 e' hb]
    simp only [FirstJetBundle.fiberCoordChange_apply, trivializationAt,
      FiberBundle.pullback_trivializationAt', ContinuousLinearEquiv.coe_coe]
    exact hcompare.trans (congrArg (fun p : M ↦ e.coordChangeL 𝕜 e' p w) hinv)

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

variable (I F V r) in
/-- Over a manifold with a boundaryless model, the `r`-jet of a vector bundle at `x ∈ U` is
identified with the `r`-jet of its restriction to `U` by keeping the same derivative tuple. -/
def restrictJetEquiv (U : Opens M) (x : U) :
    JetBundle I F V r (x : M) ≃L[𝕜]
      JetBundle I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) r x :=
  ContinuousLinearEquiv.refl 𝕜 (SymmetricJet 𝕜 E F r)

-- Use pre-simplification so the rules match before simp rewrites the dependent pullback types.
/-- Restricting a jet preserves its derivative tuple in the inherited chart. -/
@[simp↓]
theorem toJets_restrictJetEquiv (U : Opens M) (x : U) (a : JetBundle I F V r (x : M)) :
    SymmetricJet.toJets 𝕜 E F r (restrictJetEquiv I F V r U x a) =
      SymmetricJet.toJets 𝕜 E F r a :=
  (rfl)

/-- Restricting the jet of a section gives the jet of its restriction to the open subset. -/
@[simp↓]
theorem restrictJetEquiv_jet (U : Opens M) (x : U) (s : ∀ y, V y) :
    restrictJetEquiv I F V r U x (jet I F r s (x : M)) =
      jet (V := ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) I F r
        (fun y : U ↦ s (y : M)) x := by
  let t : ∀ y : U, ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) y :=
    fun y ↦ s (y : M)
  have hrep : FirstJetBundle.localRep (M := U) I F t x =ᶠ[𝓝 (extChartAt I x x)]
      FirstJetBundle.localRep I F s (x : M) := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target (I := I) x)] with z hz
    exact U.localRep_restrict_eq_of_mem_extChartAt_target s x hz
  have hrestricted := jet_eq_symmetrizeJets_of_eventuallyEq (r := r) hrep
  have hambient := jet_eq_symmetrizeJets_of_eventuallyEq (I := I) (F := F) (r := r)
    (s := s) (x := (x : M)) Filter.EventuallyEq.rfl
  rw [U.extChartAt_apply] at hrestricted
  apply SymmetricJet.toJets_injective
  rw [toJets_restrictJetEquiv, hrestricted, hambient]

/-- Restriction of jets commutes with truncation to any lower order. -/
@[simp↓]
theorem truncate_restrictJetEquiv {r' : ℕ}
    (U : Opens M) (hr : r' ≤ r) (x : U) (a : JetBundle I F V r (x : M)) :
    haveI : IsManifold I r' M := .of_le (n := r) (by exact_mod_cast hr)
    haveI : ContMDiffVectorBundle r' F V I := .of_le (n := r) (by exact_mod_cast hr)
    truncate hr x (restrictJetEquiv I F V r U x a) =
      restrictJetEquiv I F V r' U x (truncate hr (x : M) a) := by
  apply SymmetricJet.toJets_injective
  simp only [toJets_truncate, toJets_restrictJetEquiv]

/-- The inverse restriction equivalence preserves the derivative tuple. -/
@[simp↓]
theorem toJets_restrictJetEquiv_symm (U : Opens M) (x : U)
    (a : JetBundle I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) r x) :
    SymmetricJet.toJets 𝕜 E F r ((restrictJetEquiv I F V r U x).symm a) =
      SymmetricJet.toJets 𝕜 E F r a :=
  (rfl)

/-- Restricting a jet preserves its value in the original bundle fiber. -/
@[simp↓]
theorem value_restrictJetEquiv (U : Opens M) (x : U) (a : JetBundle I F V r (x : M)) :
    @Eq (V (x : M)) (value x (restrictJetEquiv I F V r U x a)) (value (x : M) a) := by
  rw [value_apply, value_apply, toJets_restrictJetEquiv]
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt']
  exact (trivializationAt F V (x : M)).symm_pullback (ContinuousMap.subtypeVal (U : Set M))
    (mem_baseSet_trivializationAt F V (x : M)) _

end TopologicalSpace.Opens
