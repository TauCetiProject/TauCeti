/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothLink
public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopy.Basic

/-!
# Ambient isotopy of smooth link presentations

A smooth link is a finite labelled family of embedded oriented circles.  Its geometric
 equivalence must move every component by one ambient isotopy; allowing a separate isotopy for
each component would lose the complement data that knot invariants detect.  This file packages
that relation and its quotient setoid, the first equivalence object for the geometric presentation
in Layer 4 of the geometric-topology roadmap.
-/

public section

noncomputable section

namespace TauCeti

open scoped Manifold

namespace SmoothLinkEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] {I : ModelWithCorners ℝ E H} {n : ℕ}
  [ChartedSpace H M]
  {L K P : SmoothLinkEmbedding I M n}

/-- Two smooth link presentations are equivalent when one ambient isotopy carries every labelled
component of the first to the corresponding component of the second. -/
def ContinuousAmbientIsotopic (L K : SmoothLinkEmbedding I M n) : Prop :=
  ∃ Φ : AmbientIsotopy M, ∀ i,
    Φ.final.comp (L i).toContinuousMap = (K i).toContinuousMap

/-- An ambient isotopy witnessing link equivalence, with the endpoint equation oriented as
`K = Φ.final ∘ L`. -/
theorem continuousAmbientIsotopic_def :
    ContinuousAmbientIsotopic L K ↔
      ∃ Φ : AmbientIsotopy M, ∀ i,
        (K i).toContinuousMap = Φ.final.comp (L i).toContinuousMap := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    exact ⟨Φ, fun i => (hΦ i).symm⟩
  · rintro ⟨Φ, hΦ⟩
    exact ⟨Φ, fun i => (hΦ i).symm⟩

namespace ContinuousAmbientIsotopic

/-- Ambient-isotopic smooth links have homeomorphic complements. The homeomorphism is the
restriction of the final homeomorphism of the shared ambient-isotopy witness. -/
theorem nonempty_complementHomeomorph (hLK : ContinuousAmbientIsotopic L K) :
    Nonempty (↑(L.range)ᶜ ≃ₜ ↑(K.range)ᶜ) := by
  rcases hLK with ⟨Φ, hΦ⟩
  let e := Φ.finalHomeomorph
  have hmem (x : M) : x ∈ L.range ↔ e x ∈ K.range := by
    constructor
    · intro hx
      rcases (L.mem_range_iff x).mp hx with ⟨i, y, hy⟩
      apply (K.mem_range_iff (e x)).mpr
      refine ⟨i, y, ?_⟩
      have hi := congrArg (fun f ↦ f y) (hΦ i)
      simpa [e, hy] using hi.symm
    · intro hx
      rcases (K.mem_range_iff (e x)).mp hx with ⟨i, y, hy⟩
      apply (L.mem_range_iff x).mpr
      refine ⟨i, y, e.injective ?_⟩
      have hi := congrArg (fun f ↦ f y) (hΦ i)
      simpa [e] using hi.trans hy
  exact ⟨e.subtype fun x ↦ not_congr (hmem x)⟩

/-- The identity ambient isotopy witnesses reflexivity. -/
@[refl] theorem refl (L : SmoothLinkEmbedding I M n) : ContinuousAmbientIsotopic L L := by
  refine ⟨AmbientIsotopy.refl M, ?_⟩
  intro i
  ext x
  exact_mod_cast (AmbientIsotopy.final_refl ((L i).toContinuousMap x))

/-- Ambient link equivalence is symmetric. -/
@[symm] theorem symm (hLK : ContinuousAmbientIsotopic L K) :
    ContinuousAmbientIsotopic K L := by
  rcases hLK with ⟨Φ, hΦ⟩
  refine ⟨Φ.symm, ?_⟩
  intro i
  ext x
  have hx := congrArg (fun f => Φ.symm.final (f x)) (hΦ i)
  change Φ.symm.final (Φ.final ((L i).toContinuousMap x)) = _ at hx
  exact hx.symm.trans (Φ.symm_final_final _)

/-- Ambient link equivalence is transitive. -/
@[trans] theorem trans (hLK : ContinuousAmbientIsotopic L K)
    (hKP : ContinuousAmbientIsotopic K P) : ContinuousAmbientIsotopic L P := by
  rcases hLK with ⟨Φ, hΦ⟩
  rcases hKP with ⟨Ψ, hΨ⟩
  refine ⟨Φ.trans Ψ, ?_⟩
  intro i
  ext x
  change (Φ.trans Ψ).final ((L i).toContinuousMap x) = (P i).toContinuousMap x
  rw [AmbientIsotopy.final_trans]
  have hx := congrArg (fun f => f x) (hΦ i)
  have hy := congrArg (fun f => f x) (hΨ i)
  change Φ.final ((L i).toContinuousMap x) = (K i).toContinuousMap x at hx
  change Ψ.final ((K i).toContinuousMap x) = (P i).toContinuousMap x at hy
  exact (congrArg Ψ.final hx).trans hy

/-- The relation on labelled smooth links is an equivalence relation. -/
theorem equivalence :
    Equivalence (ContinuousAmbientIsotopic (I := I) (M := M) (n := n)) :=
  ⟨refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The quotient of smooth link presentations by ambient isotopy. -/
def setoid (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (n : ℕ) : Setoid (SmoothLinkEmbedding I M n) where
  r := ContinuousAmbientIsotopic
  iseqv := equivalence

@[simp] theorem setoid_r_iff {L K : SmoothLinkEmbedding I M n} :
    (setoid I M n).r L K ↔ ContinuousAmbientIsotopic L K := Iff.rfl

end ContinuousAmbientIsotopic

end SmoothLinkEmbedding

end TauCeti
