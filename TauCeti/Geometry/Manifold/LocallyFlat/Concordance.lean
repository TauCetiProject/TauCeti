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
`(0, 1)`. The real parameter avoids a source with boundary, while the collar conditions make the
track a product for `t ≤ ε` and `t ≥ 1 − ε`.

The complementary model of the locally flat track is explicit data, as it is in
`IsLocallyFlat`; no smooth structure is smuggled into the topological relation. Reversing the real
parameter and the ambient time coordinate gives the symmetry operation.

This is the relation underlying topological knot concordance: specialising `M` to the circle and
`N` to `S³` gives the topological concordance relation on geometric knot presentations.

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
coordinate stays in `(0, 1)` over the open slab. Here `F` is the model of `M`, so the track is
locally flat with source model `F × ℝ` and complementary model `F'`.
-/
structure TopologicalConcordance (F F' : Type*) [TopologicalSpace F] [TopologicalSpace F']
    [Zero F'] (f g : M → N) where
  /-- The locally flat track of the concordance. -/
  toFun : M × ℝ → N × ℝ
  /-- The track is locally flat with the chosen complementary model. -/
  isLocallyFlat' : IsLocallyFlat (F × ℝ) F' toFun
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

@[simp]
theorem toFun_eq_coe (C : TopologicalConcordance F F' f g) : C.toFun = ⇑C :=
  rfl

@[ext]
theorem ext {C D : TopologicalConcordance F F' f g} (h : ∀ p, C p = D p) : C = D :=
  DFunLike.coe_injective (funext h)

variable (C : TopologicalConcordance F F' f g)

/-- The underlying track is locally flat with the chosen complementary model. -/
theorem isLocallyFlat : IsLocallyFlat (F × ℝ) F' (⇑C) :=
  C.isLocallyFlat'

/-! ### Collar API -/

/-- A topological concordance is the product of its initial map on a positive-width collar. -/
theorem exists_pos_apply_eq_left :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), t ≤ ε → C (x, t) = (f x, t) := by
  rcases C.exists_pos_apply_eq_left' with ⟨ε, hε, hC⟩
  exact ⟨ε, hε, hC⟩

/-- A topological concordance is the product of its final map on a positive-width collar. -/
theorem exists_pos_apply_eq_right :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : M) (t : ℝ), 1 - ε ≤ t → C (x, t) = (g x, t) := by
  rcases C.exists_pos_apply_eq_right' with ⟨ε, hε, hC⟩
  exact ⟨ε, hε, hC⟩

/-- A topological concordance is the product of its initial map for nonpositive times. -/
theorem apply_of_nonpos (x : M) {t : ℝ} (ht : t ≤ 0) : C (x, t) = (f x, t) := by
  rcases C.exists_pos_apply_eq_left with ⟨ε, hε, hC⟩
  exact hC x t (ht.trans hε.le)

/-- A topological concordance is the product of its final map for times at least one. -/
theorem apply_of_one_le (x : M) {t : ℝ} (ht : 1 ≤ t) : C (x, t) = (g x, t) := by
  rcases C.exists_pos_apply_eq_right with ⟨ε, hε, hC⟩
  exact hC x t (by linarith)

/-- At time `0` a topological concordance is its initial map. -/
@[simp]
theorem apply_zero (x : M) : C (x, 0) = (f x, 0) :=
  C.apply_of_nonpos x le_rfl

/-- At time `1` a topological concordance is its final map. -/
@[simp]
theorem apply_one (x : M) : C (x, 1) = (g x, 1) :=
  C.apply_of_one_le x le_rfl

/-- The time coordinate of the track lies in the open slab at interior source times. -/
theorem snd_apply_mem_Ioo (x : M) (t : ℝ) (ht : t ∈ Ioo 0 1) :
    (C (x, t)).2 ∈ Ioo 0 1 :=
  C.snd_apply_mem_Ioo' x t ht

/-- A topological concordance maps the open slab into the open slab and conversely. -/
theorem snd_apply_mem_Ioo_iff (x : M) {t : ℝ} :
    (C (x, t)).2 ∈ Ioo 0 1 ↔ t ∈ Ioo 0 1 := by
  constructor
  · intro h
    constructor
    · by_contra ht
      have ht' : t ≤ 0 := le_of_not_gt ht
      have htime : (C (x, t)).2 = t := congrArg Prod.snd (C.apply_of_nonpos x ht')
      linarith [h.1]
    · by_contra ht
      have ht' : 1 ≤ t := le_of_not_gt ht
      have htime : (C (x, t)).2 = t := congrArg Prod.snd (C.apply_of_one_le x ht')
      linarith [h.2]
  · exact C.snd_apply_mem_Ioo x t

private theorem isEmbedding_of_slice {φ : M → N} {c : ℝ}
    (h : ∀ x : M, C (x, c) = (φ x, c)) : IsEmbedding φ := by
  have htrack : IsEmbedding (fun x : M => C (x, c)) :=
    C.isLocallyFlat.isEmbedding.comp (isEmbedding_prodMkLeft c)
  have hprod : IsEmbedding ((fun y : N => (y, c)) ∘ φ) := by
    simpa only [Function.comp_def, h] using htrack
  exact (isEmbedding_prodMkLeft c).of_comp_iff.mp hprod

/-! ### Symmetry -/

/-- Reverse a topological concordance by reflecting both source and target time. -/
def symm (C : TopologicalConcordance F F' f g) : TopologicalConcordance F F' g f where
  toFun p :=
    Homeomorph.prodCongr (Homeomorph.refl N) (Homeomorph.subLeft (1 : ℝ))
      (C (Homeomorph.prodCongr (Homeomorph.refl M) (Homeomorph.subLeft (1 : ℝ)) p))
  isLocallyFlat' := by
    have hsource := C.isLocallyFlat.comp_homeomorph
      (Homeomorph.prodCongr (Homeomorph.refl M) (Homeomorph.subLeft (1 : ℝ)))
    have htarget := hsource.homeomorph_comp
      (Homeomorph.prodCongr (Homeomorph.refl N) (Homeomorph.subLeft (1 : ℝ)))
    simpa only [Function.comp_def] using htarget
  exists_pos_apply_eq_left' := by
    obtain ⟨ε, hε, hC⟩ := C.exists_pos_apply_eq_right
    refine ⟨ε, hε, fun x t ht => ?_⟩
    have ht' : 1 - ε ≤ 1 - t := by linarith
    simp only [Homeomorph.coe_prodCongr, Prod.map_apply,
      Homeomorph.refl_apply, id_eq, Homeomorph.subLeft_apply, hC x (1 - t) ht']
    apply Prod.ext
    · rfl
    · ring
  exists_pos_apply_eq_right' := by
    obtain ⟨ε, hε, hC⟩ := C.exists_pos_apply_eq_left
    refine ⟨ε, hε, fun x t ht => ?_⟩
    have ht' : 1 - t ≤ ε := by linarith
    simp only [Homeomorph.coe_prodCongr, Prod.map_apply,
      Homeomorph.refl_apply, id_eq, Homeomorph.subLeft_apply, hC x (1 - t) ht']
    apply Prod.ext
    · rfl
    · ring
  snd_apply_mem_Ioo' x t ht := by
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hC := C.snd_apply_mem_Ioo x (1 - t) ht'
    have hreflected : (1 - (C (x, 1 - t)).2) ∈ Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hC.1, hC.2]
    -- Unfold the assigned track map, then use the product and time-reversal application lemmas.
    change (Prod.map id (⇑(Homeomorph.subLeft (1 : ℝ)))
      (C (Prod.map id (⇑(Homeomorph.subLeft (1 : ℝ))) (x, t)))).2 ∈ Ioo 0 1
    simp only [Prod.map_snd, Prod.map_apply, id_eq, Homeomorph.subLeft_apply]
    exact hreflected

/-! ### Endpoint embeddings -/

/-- The initial map of a topological concordance is an embedding, because it is the zero-time
slice of the locally flat track. -/
theorem isEmbedding_left (C : TopologicalConcordance F F' f g) : IsEmbedding f := by
  exact C.isEmbedding_of_slice C.apply_zero

/-- The final map of a topological concordance is an embedding, because it is the time-one slice
of the locally flat track. -/
theorem isEmbedding_right (C : TopologicalConcordance F F' f g) : IsEmbedding g := by
  exact C.symm.isEmbedding_left

/-- The reversed track evaluated at `(x, t)`. -/
@[simp]
theorem symm_apply (C : TopologicalConcordance F F' f g) (x : M) (t : ℝ) :
    C.symm (x, t) = ((C (x, 1 - t)).1, 1 - (C (x, 1 - t)).2) := by
  -- Unfold the assigned track map, then use the product and time-reversal application lemmas.
  change Prod.map id (⇑(Homeomorph.subLeft (1 : ℝ)))
      (C (Prod.map id (⇑(Homeomorph.subLeft (1 : ℝ))) (x, t))) = _
  simp only [Prod.map_apply, id_eq]
  apply Prod.ext
  · rfl
  · simp only [Prod.map_snd, Homeomorph.subLeft_apply]

/-- Reversing a track twice gives it back. -/
@[simp]
theorem symm_symm (C : TopologicalConcordance F F' f g) : C.symm.symm = C := by
  apply DFunLike.coe_injective
  funext ⟨x, t⟩
  rw [symm_apply, symm_apply]
  simp only [sub_sub_cancel]

end TopologicalConcordance

/-- Two maps are topologically concordant when a locally flat collared track connects them. -/
def TopologicallyConcordant (F F' : Type*) [TopologicalSpace F] [TopologicalSpace F'] [Zero F']
    (f g : M → N) : Prop :=
  Nonempty (TopologicalConcordance F F' f g)

namespace TopologicallyConcordant

variable {f g : M → N}

/-- A topological concordance witnesses the relation. -/
theorem of_concordance (C : TopologicalConcordance F F' f g) :
    TopologicallyConcordant F F' f g :=
  ⟨C⟩

/-- Topological concordance is symmetric by reversing the time coordinate. -/
@[symm]
theorem symm (h : TopologicallyConcordant F F' f g) :
    TopologicallyConcordant F F' g f :=
  h.elim fun C => of_concordance C.symm

end TopologicallyConcordant

end TauCeti
