/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Jet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Pullback

/-!
# Restriction of higher jets to open subsets

For an open subset `U` of a manifold `M`, the jets over `x ∈ U` of a vector bundle `V` are
canonically identified with the jets of its restriction `V|_U`.
`Opens.restrictJetEquiv` keeps the derivative tuple in the inherited chart and
trivialization. This identifies the jets of a section and its restriction
(`TopologicalSpace.Opens.restrictJetEquiv_jet`) and commutes with jet truncation
(`TopologicalSpace.Opens.truncate_restrictJetEquiv`).
The comparison uses `TopologicalSpace.Opens.localRep_restrict_eq_of_mem_extChartAt_target`
and the symmetric derivative tuples of `TauCeti.JetBundle`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5 and 12.16–12.17, for jets of local sections.
-/

public section

noncomputable section

open Bundle Filter TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TopologicalSpace.Opens

open TauCeti TauCeti.JetBundle

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommMonoid (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {r : ℕ} [IsManifold I r M] [ContMDiffVectorBundle r F V I]

variable (I F V r) in
/-- The `r`-jet over `x ∈ U` of a vector bundle is identified with the `r`-jet of its
restriction to `U` by keeping the same derivative tuple in the inherited chart. -/
def restrictJetEquiv (U : Opens M) (x : U) :
    JetBundle I F V r (x : M) ≃L[𝕜]
      JetBundle I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) r x :=
  ContinuousLinearEquiv.refl 𝕜 (SymmetricJet 𝕜 E F r)

/-- Restricting a jet preserves its derivative tuple in the inherited chart. -/
theorem toJets_restrictJetEquiv (U : Opens M) (x : U) (a : JetBundle I F V r (x : M)) :
    SymmetricJet.toJets 𝕜 E F r (restrictJetEquiv I F V r U x a) =
      SymmetricJet.toJets 𝕜 E F r a :=
  (rfl)

/-- Restricting the jet of a section gives the jet of its restriction to the open subset. -/
theorem restrictJetEquiv_jet (U : Opens M) (x : U) (s : ∀ y, V y) :
    restrictJetEquiv I F V r U x (jet I F r s (x : M)) =
      jet (V := ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) I F r
        (fun y : U ↦ s (y : M)) x := by
  let t : ∀ y, ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) y :=
    fun y ↦ s (y : M)
  have hrep : FirstJetBundle.localRep I F t x =ᶠ[𝓝 (extChartAt I x x)]
      FirstJetBundle.localRep I F s (x : M) := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target (I := I) x)] with z hz
    exact U.localRep_restrict_eq_of_mem_extChartAt_target s x hz
  have hjet : restrictJetEquiv I F V r U x (jet I F r s (x : M)) = jet I F r t x := by
    apply SymmetricJet.toJets_injective
    rw [toJets_restrictJetEquiv]
    funext k
    rw [toJets_jet_apply, toJets_jet_apply, ← U.extChartAt_apply x x,
      (hrep.iteratedFDeriv 𝕜 k.val).eq_of_nhds]
  exact hjet

/-- Restriction of jets commutes with truncation to any lower order. -/
theorem truncate_restrictJetEquiv {r' : ℕ} [IsManifold I r' M] [ContMDiffVectorBundle r' F V I]
    (U : Opens M) (hr : r' ≤ r) (x : U) (a : JetBundle I F V r (x : M)) :
    truncate hr x (restrictJetEquiv I F V r U x a) =
      restrictJetEquiv I F V r' U x (truncate hr (x : M) a) := by
  apply SymmetricJet.toJets_injective
  simp only [toJets_truncate, toJets_restrictJetEquiv]

/-- The inverse restriction equivalence preserves the derivative tuple. -/
theorem toJets_restrictJetEquiv_symm (U : Opens M) (x : U)
    (a : JetBundle I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) r x) :
    SymmetricJet.toJets 𝕜 E F r ((restrictJetEquiv I F V r U x).symm a) =
      SymmetricJet.toJets 𝕜 E F r a :=
  (rfl)

/-- Restricting a jet preserves its value in the original bundle fiber. -/
theorem value_restrictJetEquiv (U : Opens M) (x : U) (a : JetBundle I F V r (x : M)) :
    value x (restrictJetEquiv I F V r U x a) = value (x : M) a := by
  obtain ⟨s, -, rfl⟩ := exists_contMDiffAt_jet_eq (n := ∞) (x : M) a
  rw [restrictJetEquiv_jet, value_jet]
  exact value_jet (I := I) (F := F)
    (V := ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) (fun y ↦ s (y : M)) x

end TopologicalSpace.Opens
