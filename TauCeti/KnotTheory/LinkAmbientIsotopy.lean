/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothLink
public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopy.Basic
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Complement
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Naturality

/-!
# Ambient isotopy of smooth link presentations

A smooth link is a finite labelled family of embedded oriented circles. Its geometric
equivalence must move every component by one ambient isotopy; allowing a separate isotopy for
each component would lose the complement data that knot invariants detect. This file represents
the whole link by the continuous map from the disjoint union of its circles and specializes the
general ambient-isotopy relation to that map.

## Main definitions

* `TauCeti.SmoothLinkEmbedding.toContinuousMap`: the map from the disjoint union of the link's
  component circles into the ambient manifold.
* `TauCeti.SmoothLinkEmbedding.ContinuousAmbientIsotopic`: simultaneous continuous ambient
  isotopy of labelled smooth links.
* `TauCeti.SmoothLinkEmbedding.ContinuousAmbientIsotopic.setoid`: the ambient-isotopy relation
  packaged as a setoid.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, especially Definition 1.2 and the discussion of knot complements.
-/

public section

noncomputable section

namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothLinkEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] {I : ModelWithCorners ℝ E H} {n : ℕ}
  [ChartedSpace H M]
  {L K P : SmoothLinkEmbedding I M n}

/-- Two smooth link presentations are equivalent when one ambient isotopy carries their
disjoint-union maps into one another, and hence simultaneously carries every labelled component
of the first to the corresponding component of the second. -/
def ContinuousAmbientIsotopic (L K : SmoothLinkEmbedding I M n) : Prop :=
  TauCeti.AmbientIsotopic L.toContinuousMap K.toContinuousMap

namespace ContinuousAmbientIsotopic

/-- An ambient isotopy whose final map carries one link to the other witnesses link ambient
isotopy. -/
theorem of_ambientIsotopy (Φ : TauCeti.AmbientIsotopy M)
    (hΦ : Φ.final.comp L.toContinuousMap = K.toContinuousMap) : ContinuousAmbientIsotopic L K :=
  TauCeti.ambientIsotopic_def.mpr ⟨Φ, hΦ⟩


/-- Project a simultaneous ambient isotopy of links to any labelled component. -/
theorem component (hLK : ContinuousAmbientIsotopic L K) (i : Fin n) :
    SmoothEmbedding.ContinuousAmbientIsotopic (L i) (K i) := by
  let j := ContinuousMap.sigmaMk (X := fun _ : Fin n ↦ Circle) i
  have hL : L.toContinuousMap.comp j = (L i).toContinuousMap := by
    ext x
    simp [j]
  have hK : K.toContinuousMap.comp j = (K i).toContinuousMap := by
    ext x
    simp [j]
  rw [SmoothEmbedding.continuousAmbientIsotopic_def]
  apply ambientIsotopic_def.mp
  rw [← hL, ← hK]
  exact hLK.precomp j

/-- For one-component links, simultaneous ambient isotopy is exactly the existing ambient-isotopy
relation on smooth circle embeddings. -/
@[simp]
theorem singleton_iff {f g : SmoothCircleEmbedding I M} :
    ContinuousAmbientIsotopic (singleton f) (singleton g) ↔
      SmoothEmbedding.ContinuousAmbientIsotopic f g := by
  constructor
  · intro h
    simpa only [singleton_apply] using h.component 0
  · intro h
    have h' : AmbientIsotopic f.toContinuousMap g.toContinuousMap :=
      ambientIsotopic_def.mpr (SmoothEmbedding.continuousAmbientIsotopic_def.mp h)
    let p := ContinuousMap.sigma fun _ : Fin 1 ↦ ContinuousMap.id Circle
    have hf : f.toContinuousMap.comp p = (singleton f).toContinuousMap := by
      ext ⟨i, x⟩
      simp [p]
    have hg : g.toContinuousMap.comp p = (singleton g).toContinuousMap := by
      ext ⟨i, x⟩
      simp [p]
    rw [ContinuousAmbientIsotopic, ← hf, ← hg]
    exact h'.precomp p

/-- Ambient-isotopic smooth links have homeomorphic complements. -/
theorem nonempty_complementHomeomorph (hLK : ContinuousAmbientIsotopic L K) :
    Nonempty (↑(L.range)ᶜ ≃ₜ ↑(K.range)ᶜ) := by
  rw [← range_toContinuousMap L, ← range_toContinuousMap K]
  exact TauCeti.AmbientIsotopic.nonempty_complementHomeomorph hLK

/-- The identity ambient isotopy witnesses reflexivity. -/
@[refl]
theorem refl (L : SmoothLinkEmbedding I M n) : ContinuousAmbientIsotopic L L :=
  AmbientIsotopic.refl L.toContinuousMap

/-- Ambient link equivalence is symmetric. -/
@[symm]
theorem symm (hLK : ContinuousAmbientIsotopic L K) :
    ContinuousAmbientIsotopic K L :=
  AmbientIsotopic.symm hLK

/-- Ambient link equivalence is transitive. -/
@[trans]
theorem trans (hLK : ContinuousAmbientIsotopic L K)
    (hKP : ContinuousAmbientIsotopic K P) : ContinuousAmbientIsotopic L P :=
  AmbientIsotopic.trans hLK hKP

/-- Simultaneously relabelling corresponding components preserves ambient link equivalence. -/
theorem relabel (hLK : ContinuousAmbientIsotopic L K) (e : Equiv.Perm (Fin n)) :
    ContinuousAmbientIsotopic (L.relabel e) (K.relabel e) := by
  let e' : C((Σ _ : Fin n, Circle), (Σ _ : Fin n, Circle)) :=
    ContinuousMap.sigma fun i ↦
      ContinuousMap.sigmaMk (X := fun _ : Fin n ↦ Circle) (e.symm i)
  have hL : (L.relabel e).toContinuousMap = L.toContinuousMap.comp e' := by
    ext ⟨i, x⟩
    simp [e']
  have hK : (K.relabel e).toContinuousMap = K.toContinuousMap.comp e' := by
    ext ⟨i, x⟩
    simp [e']
  rw [ContinuousAmbientIsotopic, hL, hK]
  exact hLK.precomp e'

/-- Simultaneous component relabelling preserves and reflects ambient link equivalence. -/
@[simp]
theorem relabel_iff (e : Equiv.Perm (Fin n)) :
    ContinuousAmbientIsotopic (L.relabel e) (K.relabel e) ↔ ContinuousAmbientIsotopic L K := by
  constructor
  · intro h
    simpa using h.relabel e.symm
  · exact fun h ↦ h.relabel e

/-- Simultaneously reversing every component orientation preserves ambient link equivalence. -/
theorem reverse (hLK : ContinuousAmbientIsotopic L K) :
    ContinuousAmbientIsotopic L.reverse K.reverse := by
  let r : C((Σ _ : Fin n, Circle), (Σ _ : Fin n, Circle)) :=
    ContinuousMap.sigma fun i ↦
      (ContinuousMap.sigmaMk i).comp (circleReflection.toHomeomorph : C(Circle, Circle))
  have hL : L.reverse.toContinuousMap = L.toContinuousMap.comp r := by
    ext ⟨i, x⟩
    simp [r]
  have hK : K.reverse.toContinuousMap = K.toContinuousMap.comp r := by
    ext ⟨i, x⟩
    simp [r]
  rw [ContinuousAmbientIsotopic, hL, hK]
  exact hLK.precomp r

/-- Simultaneous orientation reversal preserves and reflects ambient link equivalence. -/
@[simp]
theorem reverse_iff :
    ContinuousAmbientIsotopic L.reverse K.reverse ↔ ContinuousAmbientIsotopic L K := by
  constructor
  · intro h
    simpa using h.reverse
  · exact fun h ↦ h.reverse

section Ambient

variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

/-- Transporting both links through the same ambient diffeomorphism preserves ambient link
equivalence. -/
theorem transDiffeomorph (hLK : ContinuousAmbientIsotopic L K) (e : M ≃ₘ⟮I, I⟯ Q) :
    ContinuousAmbientIsotopic (L.transDiffeomorph e) (K.transDiffeomorph e) := by
  have hL : (L.transDiffeomorph e).toContinuousMap =
      (e.toHomeomorph : C(M, Q)).comp L.toContinuousMap := by
    ext ⟨i, x⟩
    simp
  have hK : (K.transDiffeomorph e).toContinuousMap =
      (e.toHomeomorph : C(M, Q)).comp K.toContinuousMap := by
    ext ⟨i, x⟩
    simp
  rw [ContinuousAmbientIsotopic, hL, hK]
  exact hLK.postcomp_homeomorph e.toHomeomorph

variable [IsManifold I ∞ M] in
/-- Simultaneous ambient transport preserves and reflects ambient link equivalence. -/
@[simp]
theorem transDiffeomorph_iff (e : M ≃ₘ⟮I, I⟯ Q) :
    ContinuousAmbientIsotopic (L.transDiffeomorph e) (K.transDiffeomorph e) ↔
      ContinuousAmbientIsotopic L K := by
  constructor
  · intro h
    simpa using h.transDiffeomorph e.symm
  · exact fun h ↦ h.transDiffeomorph e

end Ambient

/-- The relation on labelled smooth links is an equivalence relation. -/
theorem equivalence :
    Equivalence (ContinuousAmbientIsotopic (I := I) (M := M) (n := n)) :=
  AmbientIsotopic.equivalence.comap SmoothLinkEmbedding.toContinuousMap

/-- The ambient-isotopy equivalence relation on smooth link presentations, packaged as a
`Setoid`. -/
def setoid (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (n : ℕ) : Setoid (SmoothLinkEmbedding I M n) :=
  (AmbientIsotopic.setoid (Σ _ : Fin n, Circle) M).comap
    SmoothLinkEmbedding.toContinuousMap

end ContinuousAmbientIsotopic

end SmoothLinkEmbedding

end TauCeti
