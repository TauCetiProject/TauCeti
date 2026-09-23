/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Topological concordance of locally flat embeddings

This file records the topological analogue of the collared smooth concordance in
`TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance`. A track from `f` to `g` is a locally flat
embedding of `M × ℝ` into `N × ℝ` which is a product at both ends and preserves the open slab
`(0, 1)`. The use of the real line keeps the two product collars disjoint and avoids introducing
manifolds with corners.

The complementary model of the locally flat track is explicit data, as it is in
`IsLocallyFlat`; no smooth structure is smuggled into the topological relation. Reversing the real
parameter and the ambient time coordinate gives the symmetry operation. Stacking tracks requires
the locally flat gluing input supplied by the later 4-dimensional cobordism development, so it is
deliberately not asserted here.

The relation is intended for the locally flat concordance variant of the knot concordance layer:
specialising `M` to the circle and `N` to `S³` gives the topological concordance relation on the
geometric knot presentations.

## Main definitions

* `TauCeti.TopologicalConcordance F F' f g` is a locally flat, globally collared track from `f`
  to `g`, with complementary model `F'`.
* `TauCeti.TopologicalConcordance.symm` reverses a track in time.
* `TauCeti.TopologicallyConcordant` is the existence relation associated to these tracks.

## Main results

* `TauCeti.TopologicalConcordance.symm_symm` identifies double time reversal with the original
  track.
* `TauCeti.TopologicalConcordance.isEmbedding_left` and
  `TauCeti.TopologicalConcordance.isEmbedding_right` recover the endpoint embeddings from the
  locally flat track.
* `TauCeti.TopologicallyConcordant.symm` proves symmetry of the relation.

The definition and the time-reversal construction follow Hudson, *Concordance, isotopy, and
diffeotopy*, Annals of Mathematics 91 (1970), and Livingston, *A survey of classical knot
concordance*, Section 2.
-/

public section

namespace TauCeti

open Set Topology

variable {M N F F' : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace F] [TopologicalSpace F'] [Zero F']

/-- A locally flat, globally collared topological concordance from `f` to `g`.

The track is a locally flat embedding of `M × ℝ` into `N × ℝ`. It agrees with the product of the
initial (respectively final) map and the identity on a positive-width end collar, and its time
coordinate stays in `(0, 1)` over the open slab. The complementary model `F'` is part of the
parameters, matching `IsLocallyFlat F F'`.
-/
structure TopologicalConcordance (F F' : Type*) [TopologicalSpace F] [TopologicalSpace F']
    [Zero F'] (f g : M → N) where
  /-- The locally flat track of the concordance. -/
  toFun : M × ℝ → N × ℝ
  /-- The track is locally flat with the chosen complementary model. -/
  isLocallyFlat : IsLocallyFlat (F × ℝ) F' toFun
  /-- The initial product collar. -/
  exists_pos_apply_eq_left' :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), t ≤ ε → toFun (x, t) = (f x, t)
  /-- The final product collar. -/
  exists_pos_apply_eq_right' :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), 1 - ε ≤ t → toFun (x, t) = (g x, t)
  /-- The track maps the open slab into the open slab. -/
  snd_apply_mem_Ioo' (x : M) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (toFun (x, t)).2 ∈ Ioo 0 1

namespace TopologicalConcordance

instance instFunLike {f g : M → N} :
    FunLike (TopologicalConcordance F F' f g) (M × ℝ) (N × ℝ) where
  coe C := C.toFun
  coe_injective := by
    intro C D h
    cases C
    cases D
    cases h
    rfl

variable {f g h : M → N}

/-! ### Endpoint embeddings -/

/-- The initial map of a topological concordance is an embedding, because it is the zero-time
slice of the locally flat track. -/
theorem isEmbedding_left (C : TopologicalConcordance F F' f g) : IsEmbedding f := by
  obtain ⟨ε, hε, hC⟩ := C.exists_pos_apply_eq_left'
  have htrack : IsEmbedding (fun x : M => C.toFun (x, 0)) :=
    C.isLocallyFlat.isEmbedding.comp (isEmbedding_prodMkLeft (0 : ℝ))
  have hzero : ∀ x : M, C.toFun (x, 0) = (f x, 0) :=
    fun x => hC x 0 (le_of_lt hε)
  have hprod : IsEmbedding ((fun y : N => (y, (0 : ℝ))) ∘ f) := by
    simpa only [Function.comp_def, hzero] using htrack
  exact (isEmbedding_prodMkLeft (0 : ℝ)).of_comp_iff.mp hprod

/-- The final map of a topological concordance is an embedding, because it is the unit-time slice
of the locally flat track. -/
theorem isEmbedding_right (C : TopologicalConcordance F F' f g) : IsEmbedding g := by
  obtain ⟨ε, hε, hC⟩ := C.exists_pos_apply_eq_right'
  have htrack : IsEmbedding (fun x : M => C.toFun (x, 1)) :=
    C.isLocallyFlat.isEmbedding.comp (isEmbedding_prodMkLeft (1 : ℝ))
  have hone : ∀ x : M, C.toFun (x, 1) = (g x, 1) :=
    fun x => hC x 1 (by linarith)
  have hprod : IsEmbedding ((fun y : N => (y, (1 : ℝ))) ∘ g) := by
    simpa only [Function.comp_def, hone] using htrack
  exact (isEmbedding_prodMkLeft (1 : ℝ)).of_comp_iff.mp hprod

private def timeReverse : ℝ ≃ₜ ℝ where
  toFun t := 1 - t
  invFun t := 1 - t
  left_inv t := by ring
  right_inv t := by ring
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

private def sourceTimeReverse : (M × ℝ) ≃ₜ (M × ℝ) :=
  Homeomorph.prodCongr (Homeomorph.refl M) timeReverse

private def targetTimeReverse : (N × ℝ) ≃ₜ (N × ℝ) :=
  Homeomorph.prodCongr (Homeomorph.refl N) timeReverse

/-- Reverse a topological concordance by reflecting both source and target time. -/
def symm (C : TopologicalConcordance F F' f g) : TopologicalConcordance F F' g f where
  toFun p := targetTimeReverse (C.toFun (sourceTimeReverse p))
  isLocallyFlat := by
    have hsource := C.isLocallyFlat.comp_homeomorph sourceTimeReverse
    have htarget := hsource.homeomorph_comp targetTimeReverse
    simpa only [Function.comp_def] using htarget
  exists_pos_apply_eq_left' := by
    obtain ⟨ε, hε, hC⟩ := C.exists_pos_apply_eq_right'
    refine ⟨ε, hε, fun x t ht => ?_⟩
    have ht' : 1 - ε ≤ 1 - t := by linarith
    change targetTimeReverse (C.toFun (x, 1 - t)) = (g x, t)
    rw [hC x (1 - t) ht']
    change (g x, 1 - (1 - t)) = (g x, t)
    apply Prod.ext
    · rfl
    · ring
  exists_pos_apply_eq_right' := by
    obtain ⟨ε, hε, hC⟩ := C.exists_pos_apply_eq_left'
    refine ⟨ε, hε, fun x t ht => ?_⟩
    have ht' : 1 - t ≤ ε := by linarith
    change targetTimeReverse (C.toFun (x, 1 - t)) = (f x, t)
    rw [hC x (1 - t) ht']
    change (f x, 1 - (1 - t)) = (f x, t)
    apply Prod.ext
    · rfl
    · ring
  snd_apply_mem_Ioo' x t ht := by
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hC := C.snd_apply_mem_Ioo' x (1 - t) ht'
    change (1 - (C.toFun (x, 1 - t)).2) ∈ Ioo (0 : ℝ) 1
    constructor <;> linarith [hC.1, hC.2]

@[simp]
theorem symm_apply (C : TopologicalConcordance F F' f g) (x : M) (t : ℝ) :
    C.symm (x, t) = ((C (x, 1 - t)).1, 1 - (C (x, 1 - t)).2) :=
  by
    change targetTimeReverse (C.toFun (x, 1 - t)) = _
    rfl

@[simp]
theorem symm_symm (C : TopologicalConcordance F F' f g) : C.symm.symm = C := by
  apply DFunLike.coe_injective
  funext ⟨x, t⟩
  simp [symm_apply]

end TopologicalConcordance

/-- Two maps are topologically concordant when a locally flat collared track connects them. -/
def TopologicallyConcordant (F F' : Type*) [TopologicalSpace F] [TopologicalSpace F'] [Zero F']
    (f g : M → N) : Prop :=
  Nonempty (TopologicalConcordance F F' f g)

namespace TopologicallyConcordant

variable {f g : M → N}

/-! The relation is intentionally exposed before transitivity: stacking requires the locally flat
gluing theorem for 4-dimensional tracks, which is a separate prerequisite of the concordance
group. -/

/-- Topological concordance is symmetric by reversing the time coordinate. -/
@[symm]
theorem symm (h : TopologicallyConcordant F F' f g) :
    TopologicallyConcordant F F' g f :=
  h.elim fun C => ⟨C.symm⟩

end TopologicallyConcordant

end TauCeti
