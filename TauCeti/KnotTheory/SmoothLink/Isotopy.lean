/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothLink.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic

/-! # Smooth ambient isotopy of smooth links

This file specializes the smooth ambient-isotopy relation to labeled smooth links.  A single
diffeotopy of the ambient manifold must carry every component to its counterpart; this is the
relation used for equivalence of geometric link presentations.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., Chapter 1, for ambient isotopy as
  knot and link equivalence.
* M. Hirsch, *Differential Topology*, Chapter 8, for smooth isotopies.
-/

public section
noncomputable section
namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothLinkEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} {L K T : SmoothLinkEmbedding I M n}

/-- Two smooth links are smoothly ambient isotopic when one ambient diffeotopy carries every
component of the first to the corresponding component of the second. -/
def SmoothAmbientIsotopic (L K : SmoothLinkEmbedding I M n) : Prop :=
  ∃ Φ : Diffeotopy I ∞ M, ∀ i x, Φ.final (L i x) = K i x

/-- Characterization of smooth ambient isotopy by a single componentwise diffeotopy witness. -/
theorem smoothAmbientIsotopic_def :
    SmoothAmbientIsotopic L K ↔ ∃ Φ : Diffeotopy I ∞ M, ∀ i x, Φ.final (L i x) = K i x :=
  Iff.rfl

/-- A diffeotopy witnessing the componentwise ambient transport gives link isotopy. -/
theorem SmoothAmbientIsotopic.of_diffeotopy (Φ : Diffeotopy I ∞ M)
    (hΦ : ∀ i x, Φ.final (L i x) = K i x) : SmoothAmbientIsotopic L K :=
  smoothAmbientIsotopic_def.mpr ⟨Φ, hΦ⟩

/-- Smooth ambient isotopy of links is reflexive. -/
@[refl] theorem SmoothAmbientIsotopic.refl (L : SmoothLinkEmbedding I M n) :
    SmoothAmbientIsotopic L L :=
  smoothAmbientIsotopic_def.mpr ⟨Diffeotopy.refl I ∞ M, fun _ _ ↦ by simp⟩

/-- Smooth ambient isotopy of links is symmetric. -/
@[symm] theorem SmoothAmbientIsotopic.symm
    (hLK : SmoothAmbientIsotopic L K) : SmoothAmbientIsotopic K L := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  apply smoothAmbientIsotopic_def.mpr
  refine ⟨Φ.symm, fun i x => ?_⟩
  rw [← hΦ i x, Φ.final_symm]
  exact Φ.final.symm_apply_apply (L i x)

/-- Smooth ambient isotopy of links is transitive. -/
@[trans] theorem SmoothAmbientIsotopic.trans
    (hLK : SmoothAmbientIsotopic L K) (hKT : SmoothAmbientIsotopic K T) :
    SmoothAmbientIsotopic L T := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  obtain ⟨Ψ, hΨ⟩ := smoothAmbientIsotopic_def.mp hKT
  apply smoothAmbientIsotopic_def.mpr
  refine ⟨Φ.trans Ψ, fun i x => ?_⟩
  rw [Diffeotopy.final_trans]
  calc
    Φ.final.trans Ψ.final (L i x) = Ψ.final (Φ.final (L i x)) := by
      simpa only [Function.comp_apply] using
        congr_fun (_root_.Diffeomorph.coe_trans Φ.final Ψ.final) (L i x)
    _ = T i x := by rw [hΦ i x, hΨ i x]

/-- Smooth ambient isotopy is an equivalence relation on labeled smooth links. -/
theorem SmoothAmbientIsotopic.equivalence :
    Equivalence (SmoothAmbientIsotopic (I := I) (M := M) (n := n)) :=
  ⟨SmoothAmbientIsotopic.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The smooth ambient-isotopy setoid on labeled smooth links. -/
def SmoothAmbientIsotopic.setoid (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (n : ℕ) :
    Setoid (SmoothLinkEmbedding I M n) where
  r := SmoothAmbientIsotopic
  iseqv := SmoothAmbientIsotopic.equivalence

/-- The setoid relation unfolds to smooth ambient isotopy of links. -/
@[simp] theorem SmoothAmbientIsotopic.setoid_r_iff (L K : SmoothLinkEmbedding I M n) :
    (SmoothAmbientIsotopic.setoid I M n).r L K ↔ SmoothAmbientIsotopic L K := Iff.rfl

end SmoothLinkEmbedding
end TauCeti
