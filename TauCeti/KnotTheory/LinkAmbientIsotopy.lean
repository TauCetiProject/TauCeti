/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothLink
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Complement
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Naturality

/-!
# Ambient isotopy of smooth link presentations

A smooth link is a finite labelled family of embedded oriented circles. Its geometric
equivalence moves every component by one smooth ambient isotopy: a single `Diffeotopy` of the
ambient manifold carries all corresponding components at time one. Allowing a separate witness
for each component would lose the complement data that knot invariants detect. The smooth
relation specializes the existing diffeotopy witness componentwise and agrees with smooth ambient
isotopy of embeddings for singleton links.

The auxiliary continuous relation specializes general continuous ambient isotopy to the map from
the disjoint union of component circles. Forgetting smoothness maps the smooth relation to this
continuous relation, so its complement-preservation theorem applies to smooth link equivalence.

## Main definitions

* `TauCeti.SmoothLinkEmbedding.toContinuousMap`: the map from the disjoint union of the link's
  component circles into the ambient manifold.
* `TauCeti.SmoothLinkEmbedding.ContinuousAmbientIsotopic`: simultaneous continuous ambient
  isotopy of labelled smooth links.
* `TauCeti.SmoothLinkEmbedding.SmoothAmbientIsotopic`: simultaneous smooth ambient isotopy.
* `TauCeti.SmoothLinkEmbedding.SmoothAmbientIsotopic.setoid`: the smooth geometric-presentation
  equivalence packaged as a setoid.

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

/-- Two smooth link presentations are continuously ambient isotopic when one ambient isotopy
carries their
disjoint-union maps into one another, and hence simultaneously carries every labelled component
of the first to the corresponding component of the second. -/
def ContinuousAmbientIsotopic (L K : SmoothLinkEmbedding I M n) : Prop :=
  TauCeti.AmbientIsotopic L.toContinuousMap K.toContinuousMap

/-- Continuous link ambient isotopy is witnessed by one ambient isotopy carrying every
corresponding component pointwise at time one. -/
theorem continuousAmbientIsotopic_def :
    ContinuousAmbientIsotopic L K ↔
      ∃ Φ : TauCeti.AmbientIsotopy M, ∀ i x, Φ.final (L i x) = K i x := by
  rw [ContinuousAmbientIsotopic, TauCeti.ambientIsotopic_def]
  constructor
  · rintro ⟨Φ, hΦ⟩
    refine ⟨Φ, fun i x ↦ ?_⟩
    simpa only [ContinuousMap.comp_apply, toContinuousMap_apply] using
      DFunLike.congr_fun hΦ ⟨i, x⟩
  · rintro ⟨Φ, hΦ⟩
    refine ⟨Φ, ContinuousMap.ext fun ⟨i, x⟩ ↦ ?_⟩
    simpa only [ContinuousMap.comp_apply, toContinuousMap_apply] using hΦ i x

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

/-- The continuous pullback setoid exposes its underlying relation. -/
@[simp]
theorem setoid_r_iff : (setoid I M n).r L K ↔ ContinuousAmbientIsotopic L K :=
  AmbientIsotopic.setoid_r_iff

end ContinuousAmbientIsotopic

/-- Two smooth link presentations are smoothly ambient isotopic when a single diffeotopy of
the ambient manifold carries every labelled component of the first to the corresponding
component of the second at time one. -/
def SmoothAmbientIsotopic (L K : SmoothLinkEmbedding I M n) : Prop :=
  ∃ Φ : Diffeotopy I ∞ M, ∀ i x, Φ.final (L i x) = K i x

/-- Smooth link ambient isotopy is witnessed by one diffeotopy carrying every corresponding
component pointwise at time one. -/
theorem smoothAmbientIsotopic_def :
    SmoothAmbientIsotopic L K ↔
      ∃ Φ : Diffeotopy I ∞ M, ∀ i x, Φ.final (L i x) = K i x :=
  Iff.rfl

namespace SmoothAmbientIsotopic

/-- A diffeotopy simultaneously carrying the labelled components witnesses smooth link
ambient isotopy. -/
theorem of_diffeotopy (Φ : Diffeotopy I ∞ M) (hΦ : ∀ i x, Φ.final (L i x) = K i x) :
    SmoothAmbientIsotopic L K :=
  smoothAmbientIsotopic_def.mpr ⟨Φ, hΦ⟩

/-- The identity diffeotopy witnesses reflexivity. -/
@[refl]
theorem refl (L : SmoothLinkEmbedding I M n) : SmoothAmbientIsotopic L L := by
  apply of_diffeotopy (Diffeotopy.refl I ∞ M)
  intro i x
  simp

/-- Inverting the shared diffeotopy witnesses symmetry. -/
@[symm]
theorem symm (hLK : SmoothAmbientIsotopic L K) : SmoothAmbientIsotopic K L := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  apply of_diffeotopy Φ.symm
  intro i x
  rw [Φ.final_symm, ← hΦ i x]
  exact Φ.final.symm_apply_apply (L i x)

/-- Composing the shared diffeotopies witnesses transitivity. -/
@[trans]
theorem trans (hLK : SmoothAmbientIsotopic L K) (hKP : SmoothAmbientIsotopic K P) :
    SmoothAmbientIsotopic L P := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  obtain ⟨Ψ, hΨ⟩ := smoothAmbientIsotopic_def.mp hKP
  apply of_diffeotopy (Φ.trans Ψ)
  intro i x
  rw [Diffeotopy.final_trans, _root_.Diffeomorph.coe_trans, Function.comp_apply, hΦ, hΨ]

/-- Forgetting the smoothness of the shared diffeotopy yields continuous ambient isotopy. -/
theorem continuousAmbientIsotopic (hLK : SmoothAmbientIsotopic L K) :
    ContinuousAmbientIsotopic L K := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  apply continuousAmbientIsotopic_def.mpr
  refine ⟨Φ.toAmbientIsotopy, fun i x ↦ ?_⟩
  rw [Diffeotopy.toAmbientIsotopy_final_apply]
  exact hΦ i x

/-- The shared diffeotopy smoothly carries each labelled component. -/
theorem component (hLK : SmoothAmbientIsotopic L K) (i : Fin n) :
    SmoothEmbedding.SmoothAmbientIsotopic (L i) (K i) := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  exact SmoothEmbedding.SmoothAmbientIsotopic.of_diffeotopy Φ (hΦ i)

/-- For singleton links, smooth link equivalence agrees with smooth ambient isotopy of
circle embeddings. -/
@[simp]
theorem singleton_iff {f g : SmoothCircleEmbedding I M} :
    SmoothAmbientIsotopic (singleton f) (singleton g) ↔
      SmoothEmbedding.SmoothAmbientIsotopic f g := by
  constructor
  · intro h
    simpa only [singleton_apply] using h.component 0
  · intro h
    obtain ⟨Φ, hΦ⟩ := SmoothEmbedding.smoothAmbientIsotopic_def.mp h
    apply of_diffeotopy Φ
    simpa only [singleton_apply] using fun (_ : Fin 1) ↦ hΦ

/-- Smoothly ambient isotopic links have homeomorphic complements. -/
theorem nonempty_complementHomeomorph (hLK : SmoothAmbientIsotopic L K) :
    Nonempty (↑(L.range)ᶜ ≃ₜ ↑(K.range)ᶜ) :=
  hLK.continuousAmbientIsotopic.nonempty_complementHomeomorph

/-- Simultaneously relabelling components preserves the shared smooth ambient motion. -/
theorem relabel (hLK : SmoothAmbientIsotopic L K) (e : Equiv.Perm (Fin n)) :
    SmoothAmbientIsotopic (L.relabel e) (K.relabel e) := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  apply of_diffeotopy Φ
  simpa only [relabel_apply] using fun i x ↦ hΦ (e.symm i) x

/-- Simultaneous relabelling preserves and reflects smooth link equivalence. -/
@[simp]
theorem relabel_iff (e : Equiv.Perm (Fin n)) :
    SmoothAmbientIsotopic (L.relabel e) (K.relabel e) ↔ SmoothAmbientIsotopic L K := by
  constructor
  · intro h
    simpa using h.relabel e.symm
  · exact fun h ↦ h.relabel e

/-- Simultaneously reversing all component orientations preserves smooth link equivalence. -/
theorem reverse (hLK : SmoothAmbientIsotopic L K) :
    SmoothAmbientIsotopic L.reverse K.reverse := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hLK
  apply of_diffeotopy Φ
  simpa only [reverse_apply, SmoothCircleEmbedding.reverse_apply] using
    fun i x ↦ hΦ i x⁻¹

/-- Simultaneous orientation reversal preserves and reflects smooth link equivalence. -/
@[simp]
theorem reverse_iff :
    SmoothAmbientIsotopic L.reverse K.reverse ↔ SmoothAmbientIsotopic L K := by
  constructor
  · intro h
    simpa using h.reverse
  · exact fun h ↦ h.reverse

/-- Smooth ambient isotopy is an equivalence relation on labelled smooth links. -/
theorem equivalence : Equivalence (SmoothAmbientIsotopic (I := I) (M := M) (n := n)) :=
  ⟨refl, fun h ↦ h.symm, fun h h' ↦ h.trans h'⟩

/-- The smooth ambient-isotopy equivalence relation on geometric link presentations. -/
def setoid (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (n : ℕ) : Setoid (SmoothLinkEmbedding I M n) where
  r := SmoothAmbientIsotopic
  iseqv := equivalence

/-- The geometric-presentation setoid relation is smooth ambient isotopy. -/
@[simp]
theorem setoid_r_iff : (setoid I M n).r L K ↔ SmoothAmbientIsotopic L K :=
  Iff.rfl

end SmoothAmbientIsotopic

/-- Transporting every component by the final diffeomorphism of a single diffeotopy
preserves smooth link equivalence. -/
theorem smoothAmbientIsotopic_transDiffeomorph_final [IsManifold I ∞ M]
    (L : SmoothLinkEmbedding I M n) (Φ : Diffeotopy I ∞ M) :
    SmoothAmbientIsotopic L (L.transDiffeomorph Φ.final) := by
  apply SmoothAmbientIsotopic.of_diffeotopy Φ
  intro i x
  simp

end SmoothLinkEmbedding

end TauCeti
