/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothAmbientIsotopic.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Smooth isotopies induced by diffeotopies

Restrict an ambient diffeotopy to a smooth embedding to obtain a smooth isotopy
through embeddings. The motion is jointly smooth, and every slice is the original
embedding followed by a diffeomorphism. This connects smooth ambient isotopy to
the general smooth isotopy type without assuming an isotopy extension theorem.
Dually, moving the source of an embedding `f` by a diffeotopy `Ψ` of the source gives a smooth
isotopy `x ↦ f (Ψ (t, x))` from `f` to its reparametrization by `Ψ.final`
(`TauCeti.SmoothEmbedding.smoothIsotopic_compDiffeomorph_final`).

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1.

The construction uses Tau Ceti's `Diffeotopy.timeSlice` and the smooth-embedding
invariance theorem `isSmoothEmbedding_diffeomorph_comp`.
-/

public section

noncomputable section

namespace TauCeti

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}
  [IsManifold J n N]

/-- An ambient diffeotopy restricts to a smooth isotopy of any smooth embedding. -/
def Diffeotopy.smoothIsotopy (Φ : Diffeotopy J n N) (f : C^n⟮I, M; J, N⟯)
    (hf : Manifold.IsSmoothEmbedding I J n f) :
    SmoothIsotopy f (Φ.final.toContMDiffMap.comp f) where
  toContMDiffMap := ⟨fun p => Φ (p.1, f p.2),
    Φ.contMDiff.comp (contMDiff_fst.prodMk (f.contMDiff.comp contMDiff_snd))⟩
  map_zero_left x := Φ.apply_zero (f x)
  map_one_left x := (Φ.final_apply (f x)).symm
  isSmoothEmbedding t := by
    dsimp
    simpa only [Diffeotopy.timeSlice_apply, Function.comp_def] using
      isSmoothEmbedding_diffeomorph_comp hf (Φ.timeSlice t)

/-- Restricting a diffeotopy evaluates the ambient motion on the embedded point. -/
@[simp]
theorem Diffeotopy.smoothIsotopy_apply (Φ : Diffeotopy J n N) (f : C^n⟮I, M; J, N⟯)
    (hf : Manifold.IsSmoothEmbedding I J n f) (p : unitInterval × M) :
    Φ.smoothIsotopy f hf p = Φ (p.1, f p.2) := (rfl)

/-- Smooth ambient isotopy of an embedding is witnessed by a smooth isotopy through embeddings. -/
theorem SmoothAmbientIsotopic.smoothIsotopic {f g : C^n⟮I, M; J, N⟯}
    (h : SmoothAmbientIsotopic f g) (hf : Manifold.IsSmoothEmbedding I J n f) :
    SmoothIsotopic f g := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp h
  rw [← hΦ]
  exact smoothIsotopic_def.mpr ⟨Φ.smoothIsotopy f hf⟩

omit [IsManifold J n N] in
/-- **Reparametrization along a diffeotopy is an isotopy.** An embedding `f` is smoothly isotopic
to its reparametrization by the final map of a diffeotopy `Ψ` of the source, through the
embeddings `x ↦ f (Ψ (t, x))`. -/
theorem SmoothEmbedding.smoothIsotopic_compDiffeomorph_final [IsManifold I n M]
    (f : SmoothEmbedding I J n M N) (Ψ : Diffeotopy I n M) :
    SmoothIsotopic f.toContMDiffMap (f.compDiffeomorph Ψ.final).toContMDiffMap :=
  smoothIsotopic_def.2 ⟨{
    toContMDiffMap := ⟨fun p => f (Ψ p), f.contMDiff.comp Ψ.contMDiff⟩
    map_zero_left := fun x => by simp
    map_one_left := fun x => by simp
    isSmoothEmbedding := fun t => by
      simpa [Function.comp_def] using (f.compDiffeomorph (Ψ.timeSlice t)).isSmoothEmbedding }⟩

end TauCeti
