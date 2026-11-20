/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.FiberBundle.Associated.Pullback
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Invariant bilinear maps on associated vector bundles

Let `P` be a principal `G`-bundle and let `G` act linearly on a normed space `F`. A continuous
bilinear map `β : F × F → W` which is invariant under `G`, `β (g • u) (g • v) = β u v`, induces a
continuous bilinear map on every fibre of the associated vector bundle `P ×_G F`
(`TauCeti.AssociatedBundle.bilinForm`): in every principal frame `p` it reads

`β_b ([p, u], [p, v]) = β (u, v)`

(`TauCeti.AssociatedBundle.bilinForm_mk`). Invariance is exactly what makes this independent of
the frame, since `[p • g, u] = [p, g • u]`. The main example is an `Ad`-invariant bilinear form on
the Lie algebra of the structure group, which induces a fibre pairing on the adjoint bundle.

* Associated charts carry the fibre map to `β`
  (`TauCeti.AssociatedBundle.bilinForm_trivializationAt`).
* The fibre map is nondegenerate exactly when `β` is
  (`TauCeti.AssociatedBundle.separatingLeft_bilinForm_iff`,
  `TauCeti.AssociatedBundle.separatingRight_bilinForm_iff`,
  `TauCeti.AssociatedBundle.nondegenerate_bilinForm_iff`), and positive definite when `β` is
  (`TauCeti.AssociatedBundle.bilinForm_self_pos`).
* It commutes with pullback along continuous maps of the base
  (`TauCeti.AssociatedBundle.bilinForm_pullbackEquiv`).

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public section

noncomputable section

open Bundle Set

namespace TauCeti.AssociatedBundle

variable {𝕜 B G F W : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [ContinuousSMul G F]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {β : F →L[𝕜] F →L[𝕜] W}

variable (G P) in
/-- The bilinear map induced on the fibre over `b` of the associated bundle `P ×_G F` by a bilinear
map `β` on `F`: `β` read in the preferred chart at `b`. When `β` is invariant under `G` it reads
`β` in every principal frame, `β_b ([p, u], [p, v]) = β (u, v)`
(`TauCeti.AssociatedBundle.bilinForm_mk`), and so does not depend on the chart. -/
def bilinForm (β : F →L[𝕜] F →L[𝕜] W) (b : B) :
    AssociatedBundle G P F b →L[𝕜] AssociatedBundle G P F b →L[𝕜] W :=
  -- The fibre is a type synonym of `F`, with the topology and linear structure of `F`.
  β

/-- **The induced fibre map in a principal frame.** For a `G`-invariant bilinear map `β`, the
fibre map takes the classes `[p, u]` and `[p, v]` to `β u v`, for every principal frame `p`. -/
theorem bilinForm_mk (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v) {b : B} (p : P b)
    (u v : F) : bilinForm G P β b (mk G p u) (mk G p v) = β u v := by
  rw [mk_def, mk_def]
  -- In the preferred chart at `b`, the classes have coordinates `g • u` and `g • v`.
  exact hβ _ u v

/-- **The induced fibre map in associated charts.** On the base set of the associated chart at
`i`, the fibre map is `β` applied to the chart coordinates. -/
theorem bilinForm_trivializationAt (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    {i b : B} (hb : b ∈ (trivializationAt G P i).baseSet) (u v : AssociatedBundle G P F b) :
    β (trivializationAt F (AssociatedBundle G P F) i ⟨b, u⟩).2
        (trivializationAt F (AssociatedBundle G P F) i ⟨b, v⟩).2 =
      bilinForm G P β b u v := by
  let p := (FiberBundle.homeomorphAt G P b).symm 1
  obtain ⟨u, rfl⟩ := (mk_bijective (G := G) (F := F) p).2 u
  obtain ⟨v, rfl⟩ := (mk_bijective (G := G) (F := F) p).2 v
  rw [trivializationAt_mk_snd hb, trivializationAt_mk_snd hb, hβ, bilinForm_mk hβ]

/-! ### Nondegeneracy and positivity -/

/-- The fibre map of a `G`-invariant bilinear map is left-separating exactly when the bilinear
map is. -/
theorem separatingLeft_bilinForm_iff (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (b : B) :
    (bilinForm G P β b).toLinearMap₁₂.SeparatingLeft ↔ β.toLinearMap₁₂.SeparatingLeft := by
  let p := (FiberBundle.homeomorphAt G P b).symm 1
  have hp := mk_bijective (G := G) (F := F) p
  constructor
  · intro h u hu
    refine hp.1 ((h (mk G p u) fun y ↦ ?_).trans (mk_zero p).symm)
    obtain ⟨v, rfl⟩ := hp.2 y
    simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, bilinForm_mk hβ] using hu v
  · intro h x hx
    obtain ⟨u, rfl⟩ := hp.2 x
    rw [h u fun v ↦ ?_, mk_zero]
    simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, bilinForm_mk hβ] using
      hx (mk G p v)

/-- The fibre map of a `G`-invariant bilinear map is right-separating exactly when the bilinear
map is. -/
theorem separatingRight_bilinForm_iff (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (b : B) :
    (bilinForm G P β b).toLinearMap₁₂.SeparatingRight ↔ β.toLinearMap₁₂.SeparatingRight := by
  let p := (FiberBundle.homeomorphAt G P b).symm 1
  have hp := mk_bijective (G := G) (F := F) p
  constructor
  · intro h v hv
    refine hp.1 ((h (mk G p v) fun x ↦ ?_).trans (mk_zero p).symm)
    obtain ⟨u, rfl⟩ := hp.2 x
    simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, bilinForm_mk hβ] using hv u
  · intro h y hy
    obtain ⟨v, rfl⟩ := hp.2 y
    rw [h v fun u ↦ ?_, mk_zero]
    simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, bilinForm_mk hβ] using
      hy (mk G p u)

/-- **Nondegenerate invariant bilinear maps induce nondegenerate fibre maps**, and conversely. -/
theorem nondegenerate_bilinForm_iff (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v)
    (b : B) :
    (bilinForm G P β b).toLinearMap₁₂.Nondegenerate ↔ β.toLinearMap₁₂.Nondegenerate :=
  and_congr (separatingLeft_bilinForm_iff hβ b) (separatingRight_bilinForm_iff hβ b)

/-- **Positive definite invariant forms induce positive definite fibre forms.** -/
theorem bilinForm_self_pos [NormedSpace ℝ F] {β : F →L[ℝ] F →L[ℝ] ℝ}
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v) (hpos : ∀ u, u ≠ 0 → 0 < β u u)
    {b : B} {x : AssociatedBundle G P F b} (hx : x ≠ 0) : 0 < bilinForm G P β b x x := by
  obtain ⟨p, u, rfl⟩ := exists_mk x
  rw [bilinForm_mk hβ]
  exact hpos u fun hu ↦ hx (by rw [hu, mk_zero])

/-! ### Pullback -/

/-- **The induced fibre map commutes with pullback.** For a continuous map `f` of the bases, the
comparison between the bundle associated with the pullback principal bundle and the pullback of the
associated bundle carries the fibre map of the former to that of the latter. -/
theorem bilinForm_pullbackEquiv [∀ b, Nonempty (P b)] {B' : Type*} [TopologicalSpace B']
    {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K)
    (hβ : ∀ (g : G) (u v : F), β (g • u) (g • v) = β u v) (x : B')
    (u v : AssociatedBundle G ((f : B' → B) *ᵖ P) F x) :
    bilinForm G P β (f x) (pullbackEquiv f x u) (pullbackEquiv f x v) =
      bilinForm G ((f : B' → B) *ᵖ P) β x u v := by
  let p : ((f : B' → B) *ᵖ P) x := (FiberBundle.homeomorphAt G P (f x)).symm 1
  obtain ⟨u, rfl⟩ := (mk_bijective (G := G) (P := (f : B' → B) *ᵖ P) (F := F) p).2 u
  obtain ⟨v, rfl⟩ := (mk_bijective (G := G) (P := (f : B' → B) *ᵖ P) (F := F) p).2 v
  rw [pullbackEquiv_mk, pullbackEquiv_mk, bilinForm_mk hβ, bilinForm_mk hβ]

end TauCeti.AssociatedBundle
