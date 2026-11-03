/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic
public import TauCeti.Topology.Homotopy.CollaredTrack
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Track

/-!
# Smooth concordance of smooth embeddings

This file defines a globally collared smooth concordance between two smooth embeddings
`f g : M → N`. To avoid manifolds with boundary, a concordance is a `C^n` embedding
`F : M × ℝ → N × ℝ` which is a collared track from `f` to `g` (`TauCeti.IsCollaredTrack`): the
product `f × id` and `g × id` on uniform positive-width neighborhoods of the initial and final
ends, mapping `M × (0, 1)` into `N × (0, 1)`.

Its restriction to `M × [0, 1]` is an ordinary smooth concordance which is a product near both
ends. The uniform collar widths are part of the data here, so this is stronger than merely requiring
an ordinary smooth concordance; no converse is asserted for noncompact `M`. The product ends make
globally collared concordances stack smoothly. For knots, `M` is the circle and the track is an
annulus in `N × [0, 1]`; this is the relation underlying the knot concordance group.

The relation is defined here for arbitrary smooth embeddings, in line with defining isotopy once
for general maps; smooth knot concordance is the case of `TauCeti.SmoothCircleEmbedding`, whose
source is the circle.

## Main definitions

* `TauCeti.SmoothEmbedding.Concordance f g`: a `C^n` concordance from `f` to `g`, in collared
  form.
* `TauCeti.SmoothEmbedding.conjTime`: a smooth embedding of `M × ℝ` into `N × ℝ` conjugated by an
  affine change of time, as a smooth embedding.
* `TauCeti.SmoothEmbedding.Concordance.refl`, `symm`, `trans`: the constant concordance, the
  reversed concordance, and the stacked concordance.
* `TauCeti.SmoothEmbedding.Concordance.ofDiffeotopy`: the trace of a diffeotopy, a concordance
  from an embedding to its image under the final diffeomorphism.
* `TauCeti.SmoothEmbedding.Concordance.ofSmoothIsotopy`: the collared trace of a compact-source
  smooth isotopy, as a concordance.
* `TauCeti.SmoothEmbedding.Concordance.ofSourceDiffeotopy`: the trace of a diffeotopy of the
  source, a concordance from an embedding to its reparametrization by the final diffeomorphism.
* `TauCeti.SmoothEmbedding.Concordance.ofDiffeotopies`: the trace of a diffeotopy of the target
  and one of the source run together, a concordance from `f` to `Φ.final ∘ f ∘ Ψ.final`.
* `TauCeti.SmoothEmbedding.Concordance.collaredSmoothTransitionUnit`: the time reparametrization
  of these traces, a smooth transition from `0` to `1` constant near both ends.
* `TauCeti.SmoothEmbedding.Concordant`: the concordance relation.

## Main results

* `TauCeti.SmoothEmbedding.Concordant.equivalence`: for a finite-dimensional ambient model,
  concordance is an equivalence relation.
* `TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.concordant`: smoothly ambient isotopic
  embeddings are concordant.
* `TauCeti.SmoothEmbedding.Concordant.of_smoothIsotopic`: smoothly isotopic embeddings of a
  compact boundaryless source into a finite-dimensional Hausdorff boundaryless target are
  concordant.

## Implementation notes

Everything about a concordance that does not depend on the smoothness of its track — the time-level
lemmas, the reversed track `TauCeti.reverseTime` and the stacked track `TauCeti.stack` with its
embedding property — is inherited from `TauCeti.IsCollaredTrack`; this file only supplies the
smoothness of the reversed and stacked tracks. Stacking two concordances glues two immersions along
an open cover. Mathlib's `Manifold.IsImmersion` requires a single complement for all points, so the
glued map is shown to be an immersion with `TauCeti.isImmersion_iff_forall_isImmersionAt`, which
needs the model of `N` to be finite-dimensional. The same criterion for the isotopy track
requires that assumption in `ofSmoothIsotopy` as well as `trans` and statements depending on them.

The traces of diffeotopies and smooth isotopies are reparametrized by `Real.smoothTransition`,
which is `C^∞` but not analytic; `ofDiffeotopy`, `ofSourceDiffeotopy`, `ofDiffeotopies` and
`ofSmoothIsotopy` therefore assume `n ≤ ∞`.

## References

* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448, for
  concordance of embeddings.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for knot concordance.
-/

public section

noncomputable section

namespace TauCeti

open Set Filter Manifold Topology
open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

/-- A `C^n` **concordance** from the smooth embedding `f` to the smooth embedding `g`, in collared
form: a `C^n` embedding of `M × ℝ` into `N × ℝ` which is `f × id` and `g × id` on neighborhoods
of the initial and final ends, and maps `M × (0, 1)` into `N × (0, 1)`. -/
structure Concordance (f g : SmoothEmbedding I J n M N) where
  /-- The track of the concordance, a smooth embedding of `M × ℝ` into `N × ℝ`. -/
  toSmoothEmbedding : SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ)
  /-- The track is `f × id` near the initial end and `g × id` near the final end, and maps the open
  slab `M × (0, 1)` into `N × (0, 1)`. -/
  isCollaredTrack_toSmoothEmbedding : IsCollaredTrack f g toSmoothEmbedding

/-- Two smooth embeddings are **concordant** when there is a concordance from one to the other. -/
def Concordant (f g : SmoothEmbedding I J n M N) : Prop :=
  Nonempty (Concordance f g)

/-- Two smooth embeddings are concordant exactly when their concordance type is nonempty. -/
theorem concordant_iff_nonempty {f g : SmoothEmbedding I J n M N} :
    Concordant f g ↔ Nonempty (Concordance f g) :=
  Iff.rfl

/-! ### Affine changes of time -/

section AffineTime

variable [IsManifold I n M] [IsManifold J n N]

/-- The conjugate `TauCeti.conjTime T a b` of a smooth embedding `T` of `M × ℝ` into `N × ℝ` by the
affine change of time `t ↦ a * t + b`, `a ≠ 0`, as a smooth embedding. -/
def conjTime (T : SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ))
    (a b : ℝ) (ha : a ≠ 0) : SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ) :=
  (T.compDiffeomorph ((Diffeomorph.refl I M n).prodCongr (.smulAdd n a b ha))).transDiffeomorph
    ((Diffeomorph.refl J N n).prodCongr (Diffeomorph.smulAdd n a b ha).symm)

/-- The underlying map of the conjugate smooth embedding is the conjugate map. -/
@[simp]
theorem coe_conjTime (T : SmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (M × ℝ) (N × ℝ))
    (a b : ℝ) (ha : a ≠ 0) : ⇑(T.conjTime a b ha) = TauCeti.conjTime T a b := by
  funext ⟨x, t⟩
  rw [TauCeti.conjTime_apply, ← inv_mul_eq_div]
  ext <;> simp [SmoothEmbedding.conjTime]

end AffineTime

namespace Concordance

variable {f g h : SmoothEmbedding I J n M N}

instance instFunLike : FunLike (Concordance f g) (M × ℝ) (N × ℝ) where
  coe F := F.toSmoothEmbedding
  coe_injective F G hFG := by
    cases F
    cases G
    congr
    exact DFunLike.coe_injective hFG

/-- The underlying map of a concordance is that of its track. -/
@[simp]
theorem coe_toSmoothEmbedding (F : Concordance f g) : ⇑F.toSmoothEmbedding = F :=
  (rfl)

/-- Two concordances with the same track are equal. -/
@[ext]
theorem ext {F G : Concordance f g} (hFG : ∀ p, F p = G p) : F = G :=
  DFunLike.coe_injective (funext hFG)

variable (F : Concordance f g)

/-- The track of a concordance is a collared track from `f` to `g`. -/
theorem isCollaredTrack : IsCollaredTrack f g F :=
  F.isCollaredTrack_toSmoothEmbedding

/-- At time `0` a concordance is its initial embedding. -/
@[simp]
theorem apply_zero (x : M) : F (x, 0) = (f x, 0) :=
  F.isCollaredTrack.apply_zero x

/-- At time `1` a concordance is its final embedding. -/
@[simp]
theorem apply_one (x : M) : F (x, 1) = (g x, 1) :=
  F.isCollaredTrack.apply_one x

/-! ### Diffeomorphisms -/

section Diffeomorph

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M']
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J n P]

/-- An ambient diffeomorphism carries a concordance from `f` to `g` to one between the
transported embeddings. -/
def transDiffeomorph (F : Concordance f g) (e : N ≃ₘ^n⟮J, J⟯ P) :
    Concordance (f.transDiffeomorph e) (g.transDiffeomorph e) where
  toSmoothEmbedding :=
    F.toSmoothEmbedding.transDiffeomorph (e.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ n))
  isCollaredTrack_toSmoothEmbedding := by
    simp only [coe_transDiffeomorph, Diffeomorph.coe_prodCongr, Diffeomorph.coe_refl 𝓘(ℝ) ℝ n,
      coe_toSmoothEmbedding]
    exact F.isCollaredTrack.prodMap_id_comp e

@[simp]
theorem transDiffeomorph_apply (F : Concordance f g) (e : N ≃ₘ^n⟮J, J⟯ P) (p : M × ℝ) :
    F.transDiffeomorph e p = (e (F p).1, (F p).2) := by
  ext <;> simp [← coe_toSmoothEmbedding, transDiffeomorph]

/-- A diffeomorphism of the source reparametrizes a concordance from `f` to `g` into one between
the reparametrized embeddings. -/
def compDiffeomorph (F : Concordance f g) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    Concordance (f.compDiffeomorph e) (g.compDiffeomorph e) where
  toSmoothEmbedding :=
    F.toSmoothEmbedding.compDiffeomorph (e.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ n))
  isCollaredTrack_toSmoothEmbedding := by
    simp only [coe_compDiffeomorph, Diffeomorph.coe_prodCongr, Diffeomorph.coe_refl 𝓘(ℝ) ℝ n,
      coe_toSmoothEmbedding]
    exact F.isCollaredTrack.comp_prodMap_id e

@[simp]
theorem compDiffeomorph_apply (F : Concordance f g) (e : M' ≃ₘ^n⟮I, I⟯ M) (p : M' × ℝ) :
    F.compDiffeomorph e p = F (e p.1, p.2) := by
  simp [← coe_toSmoothEmbedding, compDiffeomorph, Prod.map]

end Diffeomorph

variable [IsManifold I n M] [IsManifold J n N]

/-! ### The constant and the reversed concordance -/

/-- The constant concordance from `f` to itself, whose track is `f × id`. -/
def refl (f : SmoothEmbedding I J n M N) : Concordance f f where
  toSmoothEmbedding := f.prodMap SmoothEmbedding.id
  isCollaredTrack_toSmoothEmbedding := by
    rw [coe_prodMap, coe_id]
    exact isCollaredTrack_prodMap_id f

@[simp]
theorem refl_apply (f : SmoothEmbedding I J n M N) (p : M × ℝ) : refl f p = (f p.1, p.2) := by
  simp [← coe_toSmoothEmbedding, refl]

/-- The reversed concordance from `g` to `f`, obtained by reflecting time in `1 / 2`. -/
def symm (F : Concordance f g) : Concordance g f where
  toSmoothEmbedding := F.toSmoothEmbedding.conjTime (-1) 1 (by norm_num)
  isCollaredTrack_toSmoothEmbedding := by
    rw [coe_conjTime, coe_toSmoothEmbedding, ← reverseTime_def]
    exact F.isCollaredTrack.reverseTime

/-- The track of the reversed concordance is the reversed track. -/
theorem coe_symm (F : Concordance f g) : ⇑F.symm = reverseTime F := by
  rw [← coe_toSmoothEmbedding, symm, coe_conjTime, coe_toSmoothEmbedding, reverseTime_def]

@[simp]
theorem symm_apply (F : Concordance f g) (x : M) (t : ℝ) :
    F.symm (x, t) = ((F (x, 1 - t)).1, 1 - (F (x, 1 - t)).2) := by
  rw [coe_symm, reverseTime_apply]

/-- Reversing a concordance twice gives it back. -/
@[simp]
theorem symm_symm (F : Concordance f g) : F.symm.symm = F := by
  ext ⟨x, t⟩ <;> simp

/-! ### Stacking concordances -/

private theorem isSmoothEmbedding_stack [FiniteDimensional ℝ E'] (F : Concordance f g)
    (G : Concordance g h) :
    IsSmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (stack F G) := by
  have hF := F.isCollaredTrack
  have hG := G.isCollaredTrack
  have hlow : IsOpen {p : M × ℝ | p.2 < 2 / 3} := isOpen_lt continuous_snd continuous_const
  have hup : IsOpen {p : M × ℝ | 1 / 3 < p.2} := isOpen_lt continuous_const continuous_snd
  have hF3 : IsImmersion (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (TauCeti.conjTime F 3 0) := by
    have himm := (F.toSmoothEmbedding.conjTime 3 0 (by norm_num)).isImmersion
    rwa [coe_conjTime, coe_toSmoothEmbedding] at himm
  have hG3 : IsImmersion (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n (TauCeti.conjTime G 3 (-2)) := by
    have himm := (G.toSmoothEmbedding.conjTime 3 (-2) (by norm_num)).isImmersion
    rwa [coe_conjTime, coe_toSmoothEmbedding] at himm
  refine ⟨?_,
    hF.isEmbedding_stack hG F.toSmoothEmbedding.isEmbedding G.toSmoothEmbedding.isEmbedding⟩
  refine isImmersion_iff_forall_isImmersionAt.2 fun p => ?_
  rcases lt_or_ge p.2 (2 / 3) with hp | hp
  · exact (hF3.isImmersionAt p).congr_of_eventuallyEq
      (eventuallyEq_of_mem (hlow.mem_nhds hp) (hF.stack_eqOn_lower hG).symm)
  · exact (hG3.isImmersionAt p).congr_of_eventuallyEq
      (eventuallyEq_of_mem (hup.mem_nhds (lt_of_lt_of_le (by norm_num) hp))
        (hF.stack_eqOn_upper hG).symm)

/-- The stacked concordance from `f` to `h`: the concordance `F` from `f` to `g` at triple speed
during `[0, 1/3]`, then the constant concordance at `g`, then the concordance `G` from `g` to `h`
at triple speed during `[2/3, 1]`. -/
def trans [FiniteDimensional ℝ E'] (F : Concordance f g) (G : Concordance g h) :
    Concordance f h where
  toSmoothEmbedding := .ofIsSmoothEmbedding (stack F G) (isSmoothEmbedding_stack F G)
  isCollaredTrack_toSmoothEmbedding := by
    rw [coe_ofIsSmoothEmbedding]
    exact F.isCollaredTrack.stack G.isCollaredTrack

/-- The track of the stacked concordance is the stacked track. -/
theorem coe_trans [FiniteDimensional ℝ E'] (F : Concordance f g) (G : Concordance g h) :
    ⇑(F.trans G) = stack F G :=
  coe_ofIsSmoothEmbedding _ _

/-- Before time `1 / 2` the stacked concordance runs the first concordance at triple speed. -/
theorem trans_apply_of_le [FiniteDimensional ℝ E'] (F : Concordance f g) (G : Concordance g h)
    (x : M) {t : ℝ} (ht : t ≤ 1 / 2) :
    F.trans G (x, t) = ((F (x, 3 * t)).1, (F (x, 3 * t)).2 / 3) := by
  rw [coe_trans, stack_apply_of_le _ _ x ht]

/-- After time `1 / 2` the stacked concordance runs the second concordance at triple speed. -/
theorem trans_apply_of_lt [FiniteDimensional ℝ E'] (F : Concordance f g) (G : Concordance g h)
    (x : M) {t : ℝ} (ht : 1 / 2 < t) :
    F.trans G (x, t) = ((G (x, 3 * t - 2)).1, ((G (x, 3 * t - 2)).2 + 2) / 3) := by
  rw [coe_trans, stack_apply_of_lt _ _ x ht]

/-! ### Diffeotopies -/


/-- The time reparametrization of a diffeotopy trace: `Real.smoothTransition`, as a map into the
unit interval. -/
private def smoothTransitionUnit (t : ℝ) : unitInterval :=
  ⟨Real.smoothTransition t, Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

private theorem contMDiff_smoothTransitionUnit (hn : n ≤ ∞) :
    ContMDiff 𝓘(ℝ) (𝓡∂ 1) n smoothTransitionUnit := by
  refine contMDiff_iff_comp_subtypeVal_Icc.2 ⟨?_, ?_⟩
  · exact Real.smoothTransition.continuous.subtype_mk _
  · exact (Real.smoothTransition.contDiff.of_le hn).contMDiff

/-- The time reparametrization `t ↦ Real.smoothTransition (2 * t - 1 / 2)` of the traces of
diffeotopies, as a map into the unit interval: a smooth transition from `0` to `1` which is
constant on neighborhoods of both ends of the unit interval. -/
def collaredSmoothTransitionUnit (t : ℝ) : unitInterval :=
  smoothTransitionUnit (2 * t - 1 / 2)

/-- The collared smooth transition at `t` is `Real.smoothTransition (2 * t - 1 / 2)`. -/
@[simp]
theorem coe_collaredSmoothTransitionUnit (t : ℝ) :
    (collaredSmoothTransitionUnit t : ℝ) = Real.smoothTransition (2 * t - 1 / 2) :=
  (rfl)

/-- The collared smooth transition is `C^n` for every `n ≤ ∞`. -/
theorem contMDiff_collaredSmoothTransitionUnit (hn : n ≤ ∞) :
    ContMDiff 𝓘(ℝ) (𝓡∂ 1) n collaredSmoothTransitionUnit :=
  (contMDiff_smoothTransitionUnit hn).comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff)

/-- The collared smooth transition is continuous. -/
@[continuity, fun_prop]
theorem continuous_collaredSmoothTransitionUnit : Continuous collaredSmoothTransitionUnit :=
  (Real.smoothTransition.continuous.comp (by fun_prop)).subtype_mk _

/-- The collared smooth transition is `0` up to time `1 / 4`. -/
theorem collaredSmoothTransitionUnit_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) :
    collaredSmoothTransitionUnit t = 0 :=
  Subtype.ext (Real.smoothTransition.zero_of_nonpos (by linarith))

/-- The collared smooth transition is `1` from time `3 / 4` on. -/
theorem collaredSmoothTransitionUnit_eq_one_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) :
    collaredSmoothTransitionUnit t = 1 :=
  Subtype.ext (Real.smoothTransition.one_of_one_le (by linarith))

/-- The diffeomorphism `(y, t) ↦ (Φ (ρ t, y), t)` of `N × ℝ`, where `ρ` is the smooth transition
from `0` to `1`. -/
private def traceDiffeomorph (Φ : Diffeotopy J n N) (hn : n ≤ ∞) :
    (N × ℝ) ≃ₘ^n⟮J.prod 𝓘(ℝ), J.prod 𝓘(ℝ)⟯ (N × ℝ) where
  toFun p := (Φ (collaredSmoothTransitionUnit p.2, p.1), p.2)
  invFun p := ((Φ.toDiffeomorph.symm (collaredSmoothTransitionUnit p.2, p.1)).2, p.2)
  left_inv p := by
    set q := (collaredSmoothTransitionUnit p.2, p.1)
    have hp : (q.1, (Φ.toDiffeomorph q).2) = Φ.toDiffeomorph q := (Φ.toDiffeomorph_apply q).symm
    ext
    · simp only [Diffeotopy.coe_apply]
      rw [hp, Φ.toDiffeomorph.symm_apply_apply]
    · rfl
  right_inv p := by
    set q := (collaredSmoothTransitionUnit p.2, p.1)
    have hp : (q.1, (Φ.toDiffeomorph.symm q).2) = Φ.toDiffeomorph.symm q :=
      (Φ.toDiffeomorph_symm_apply q).symm
    ext
    · simp only [Diffeotopy.coe_apply]
      rw [hp, Φ.toDiffeomorph.apply_symm_apply]
    · rfl
  contMDiff_toFun :=
    (Φ.contMDiff.comp (((contMDiff_collaredSmoothTransitionUnit hn).comp contMDiff_snd).prodMk
      contMDiff_fst)).prodMk contMDiff_snd
  contMDiff_invFun :=
    (contMDiff_snd.comp (Φ.toDiffeomorph.symm.contMDiff.comp
      (((contMDiff_collaredSmoothTransitionUnit hn).comp contMDiff_snd).prodMk
        contMDiff_fst))).prodMk contMDiff_snd

omit [IsManifold J n N] in
@[simp]
private theorem traceDiffeomorph_apply (Φ : Diffeotopy J n N) (hn : n ≤ ∞) (p : N × ℝ) :
    traceDiffeomorph Φ hn p = (Φ (collaredSmoothTransitionUnit p.2, p.1), p.2) :=
  (rfl)

/-- The **trace of a diffeotopy** `Φ` of `N`: the concordance `(x, t) ↦ (Φ (ρ t, f x), t)` from `f`
to its image under the final diffeomorphism of `Φ`, where
`ρ(t) = Real.smoothTransition (2 * t - 1 / 2)`. -/
def ofDiffeotopy (hn : n ≤ ∞) (Φ : Diffeotopy J n N) (f : SmoothEmbedding I J n M N) :
    Concordance f (f.transDiffeomorph Φ.final) where
  toSmoothEmbedding := (f.prodMap SmoothEmbedding.id).transDiffeomorph (traceDiffeomorph Φ hn)
  isCollaredTrack_toSmoothEmbedding :=
    { exists_pos_apply_eq_left := by
        refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
        simp [collaredSmoothTransitionUnit_eq_zero_of_le ht]
      exists_pos_apply_eq_right := by
        refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
        simp [collaredSmoothTransitionUnit_eq_one_of_ge (t := t) (by linarith),
          Diffeotopy.final_apply]
      snd_apply_mem_Ioo := fun _ _ ht => by simpa using ht }

@[simp]
theorem ofDiffeotopy_apply (hn : n ≤ ∞) (Φ : Diffeotopy J n N) (f : SmoothEmbedding I J n M N)
    (p : M × ℝ) :
    ofDiffeotopy hn Φ f p =
      (Φ (collaredSmoothTransitionUnit p.2, f p.1), p.2) := by
  simp [← coe_toSmoothEmbedding, ofDiffeotopy]

private theorem isSmoothEmbedding_collaredTrace [FiniteDimensional ℝ E']
    [I.Boundaryless] [J.Boundaryless] [CompactSpace M] [T2Space N]
    (F : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap) (hn : 1 ≤ n) (hn' : n ≤ ∞) :
    IsSmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n
      (fun p : M × ℝ => (F (collaredSmoothTransitionUnit p.2, p.1), p.2)) := by
  let G : ℝ × M → N := fun p => F (collaredSmoothTransitionUnit p.1, p.2)
  have hG : ContMDiff (𝓘(ℝ).prod I) J n G :=
    F.contMDiff.comp (((contMDiff_collaredSmoothTransitionUnit hn').comp contMDiff_fst).prodMk
      contMDiff_snd)
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by simp) hn).ne'
  have hT := hG.isSmoothEmbedding_fst_prod
    (fun t => (F.isSmoothEmbedding (collaredSmoothTransitionUnit t)).isEmbedding)
    (fun t x => (F.isSmoothEmbedding (collaredSmoothTransitionUnit t)).isImmersion
      |>.isDiffImmersionAt hn0 x) hn
  let e := _root_.Diffeomorph.prodComm I 𝓘(ℝ) M ℝ n
  let e' := _root_.Diffeomorph.prodComm 𝓘(ℝ) J ℝ N n
  let S := e' ∘ (fun p : ℝ × M => (p.1, G p)) ∘ e
  have hS : ContMDiff (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n S :=
    e'.contMDiff.comp ((contMDiff_fst.prodMk hG).comp e.contMDiff)
  have hemb : IsSmoothEmbedding (I.prod 𝓘(ℝ)) (J.prod 𝓘(ℝ)) n S := by
    refine ⟨isImmersion_iff_forall_isImmersionAt.mpr fun p => ?_,
      e'.toHomeomorph.isEmbedding.comp (hT.isEmbedding.comp e.toHomeomorph.isEmbedding)⟩
    have hdiff := ((e'.isLocalDiffeomorph _).isDiffImmersionAt hn0).comp
      ((hT.isImmersion.isDiffImmersionAt hn0 (e p)).comp
        ((e.isLocalDiffeomorph _).isDiffImmersionAt hn0))
    exact (hS.contMDiffOn.isImmersionAt_iff_injective_mfderiv isOpen_univ (mem_univ p) hn).mpr
      hdiff.mfderiv_injective
  simpa only [S, G, e, e', _root_.Diffeomorph.coe_prodComm, Function.comp_def, Prod.swap]
    using hemb

/-- The collared trace of a smooth isotopy of a compact boundaryless source is a concordance.
The time coordinate is retained, so intersections between different time slices cause no problem.
The target is finite-dimensional, Hausdorff and boundaryless. -/
def ofSmoothIsotopy [FiniteDimensional ℝ E']
    [I.Boundaryless] [J.Boundaryless] [CompactSpace M] [T2Space N]
    (F : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap) (hn : 1 ≤ n) (hn' : n ≤ ∞) :
    Concordance f g where
  toSmoothEmbedding := .ofIsSmoothEmbedding
    (fun p : M × ℝ => (F (collaredSmoothTransitionUnit p.2, p.1), p.2))
    (isSmoothEmbedding_collaredTrace F hn hn')
  isCollaredTrack_toSmoothEmbedding := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
      simp [collaredSmoothTransitionUnit_eq_zero_of_le ht]
    · refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
      simp [collaredSmoothTransitionUnit_eq_one_of_ge (t := t) (by linarith)]
    · intro x t ht
      simpa only [ofIsSmoothEmbedding_apply] using ht

/-- The trace evaluates the isotopy at a smooth time transition constant near both ends. -/
@[simp]
theorem ofSmoothIsotopy_apply [FiniteDimensional ℝ E']
    [I.Boundaryless] [J.Boundaryless]
    [CompactSpace M] [T2Space N]
    (F : SmoothIsotopy f.toContMDiffMap g.toContMDiffMap) (hn : 1 ≤ n) (hn' : n ≤ ∞)
    (p : M × ℝ) :
    ofSmoothIsotopy F hn hn' p =
      (F (collaredSmoothTransitionUnit p.2, p.1), p.2) := by
  rw [← coe_toSmoothEmbedding]
  simp only [ofSmoothIsotopy, ofIsSmoothEmbedding_apply]

/-- The **trace of a source diffeotopy** `Ψ` of `M`: the concordance `(x, t) ↦ (f (Ψ (ρ t, x)), t)`
from `f` to its reparametrization by the final diffeomorphism of `Ψ`, where
`ρ(t) = Real.smoothTransition (2 * t - 1 / 2)`. -/
def ofSourceDiffeotopy (hn : n ≤ ∞) (Ψ : Diffeotopy I n M) (f : SmoothEmbedding I J n M N) :
    Concordance f (f.compDiffeomorph Ψ.final) where
  toSmoothEmbedding := (f.prodMap SmoothEmbedding.id).compDiffeomorph (traceDiffeomorph Ψ hn)
  isCollaredTrack_toSmoothEmbedding :=
    { exists_pos_apply_eq_left := by
        refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
        have : collaredSmoothTransitionUnit t = 0 :=
          Subtype.ext (Real.smoothTransition.zero_of_nonpos (by linarith))
        simp [this]
      exists_pos_apply_eq_right := by
        refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
        have : collaredSmoothTransitionUnit t = 1 :=
          Subtype.ext (Real.smoothTransition.one_of_one_le (by linarith))
        simp [this, Diffeotopy.final_apply]
      snd_apply_mem_Ioo := fun _ _ ht => by simpa using ht }

/-- The trace of a source diffeotopy at `(x, t)` is `f` applied to the motion of `x` at the
reparametrized time `Real.smoothTransition (2 * t - 1 / 2)`. -/
@[simp]
theorem ofSourceDiffeotopy_apply (hn : n ≤ ∞) (Ψ : Diffeotopy I n M)
    (f : SmoothEmbedding I J n M N) (p : M × ℝ) :
    ofSourceDiffeotopy hn Ψ f p =
      (f (Ψ (collaredSmoothTransitionUnit p.2, p.1)), p.2) := by
  simp [← coe_toSmoothEmbedding, ofSourceDiffeotopy]

/-- The **trace of an ambient and a source diffeotopy run together**: for diffeotopies `Φ` of `N`
and `Ψ` of `M`, the concordance `(x, t) ↦ (Φ (ρ t, f (Ψ (ρ t, x))), t)` from `f` to
`Φ.final ∘ f ∘ Ψ.final`, where `ρ(t) = Real.smoothTransition (2 * t - 1 / 2)`. Unlike the stacked
traces of `Φ` and of `Ψ`, every time slice is `Φₛ ∘ f ∘ Ψₛ` for a single time `s`, so a property
of `f` preserved by all such conjugations holds along the whole concordance. -/
def ofDiffeotopies (hn : n ≤ ∞) (Φ : Diffeotopy J n N) (Ψ : Diffeotopy I n M)
    (f : SmoothEmbedding I J n M N) :
    Concordance f ((f.transDiffeomorph Φ.final).compDiffeomorph Ψ.final) where
  toSmoothEmbedding := ((f.prodMap SmoothEmbedding.id).compDiffeomorph
    (traceDiffeomorph Ψ hn)).transDiffeomorph (traceDiffeomorph Φ hn)
  isCollaredTrack_toSmoothEmbedding :=
    { exists_pos_apply_eq_left := by
        refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
        simp [collaredSmoothTransitionUnit_eq_zero_of_le ht]
      exists_pos_apply_eq_right := by
        refine ⟨1 / 4, by norm_num, fun x t ht => ?_⟩
        simp [collaredSmoothTransitionUnit_eq_one_of_ge (t := t) (by linarith),
          Diffeotopy.final_apply]
      snd_apply_mem_Ioo := fun _ _ ht => by simpa using ht }

/-- The joint trace of an ambient and a source diffeotopy at `(x, t)` applies `Ψ`, then `f`, then
`Φ`, all at the reparametrized time `collaredSmoothTransitionUnit t`. -/
@[simp]
theorem ofDiffeotopies_apply (hn : n ≤ ∞) (Φ : Diffeotopy J n N) (Ψ : Diffeotopy I n M)
    (f : SmoothEmbedding I J n M N) (p : M × ℝ) :
    ofDiffeotopies hn Φ Ψ f p =
      (Φ (collaredSmoothTransitionUnit p.2, f (Ψ (collaredSmoothTransitionUnit p.2, p.1))), p.2) :=
  by simp [← coe_toSmoothEmbedding, ofDiffeotopies]

end Concordance

/-! ### The concordance relation -/

namespace Concordant

variable {f g h : SmoothEmbedding I J n M N}

/-- A concordance witnesses concordance. -/
theorem of_concordance (F : Concordance f g) : Concordant f g :=
  concordant_iff_nonempty.2 ⟨F⟩

/-- Smoothly isotopic embeddings of a compact boundaryless source into a finite-dimensional
Hausdorff boundaryless target are concordant. -/
theorem of_smoothIsotopic [FiniteDimensional ℝ E']
    [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]
    [CompactSpace M] [T2Space N]
    (hfg : SmoothIsotopic f.toContMDiffMap g.toContMDiffMap) (hn : 1 ≤ n) (hn' : n ≤ ∞) :
    Concordant f g := by
  obtain ⟨F⟩ := smoothIsotopic_def.mp hfg
  exact of_concordance (Concordance.ofSmoothIsotopy F hn hn')

section Diffeomorph

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M']
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J n P]

/-- An ambient diffeomorphism preserves concordance. -/
theorem transDiffeomorph (hfg : Concordant f g) (e : N ≃ₘ^n⟮J, J⟯ P) :
    Concordant (f.transDiffeomorph e) (g.transDiffeomorph e) :=
  concordant_iff_nonempty.2 <|
    (concordant_iff_nonempty.1 hfg).map fun F => F.transDiffeomorph e

/-- Reparametrizing the source by a diffeomorphism preserves concordance. -/
theorem compDiffeomorph (hfg : Concordant f g) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    Concordant (f.compDiffeomorph e) (g.compDiffeomorph e) :=
  concordant_iff_nonempty.2 <|
    (concordant_iff_nonempty.1 hfg).map fun F => F.compDiffeomorph e

end Diffeomorph

variable [IsManifold I n M] [IsManifold J n N]

/-- Concordance is reflexive. -/
@[refl]
theorem refl (f : SmoothEmbedding I J n M N) : Concordant f f :=
  concordant_iff_nonempty.2 ⟨Concordance.refl f⟩

/-- Concordance is symmetric. -/
@[symm]
theorem symm (hfg : Concordant f g) : Concordant g f :=
  concordant_iff_nonempty.2 <| (concordant_iff_nonempty.1 hfg).map Concordance.symm

/-- Concordance is transitive, for a finite-dimensional ambient model. -/
@[trans]
theorem trans [FiniteDimensional ℝ E'] (hfg : Concordant f g) (hgh : Concordant g h) :
    Concordant f h := by
  apply concordant_iff_nonempty.2
  exact (concordant_iff_nonempty.1 hfg).elim fun F =>
    (concordant_iff_nonempty.1 hgh).map fun G => F.trans G

/-- For a finite-dimensional ambient model, concordance is an equivalence relation on smooth
embeddings. -/
theorem equivalence [FiniteDimensional ℝ E'] :
    Equivalence (Concordant (I := I) (J := J) (n := n) (M := M) (N := N)) :=
  ⟨refl, symm, trans⟩

/-- Concordance of smooth embeddings, packaged as a setoid. -/
def setoid [FiniteDimensional ℝ E'] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (n : ℕ∞ω) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J n N] :
    Setoid (SmoothEmbedding I J n M N) where
  r := Concordant
  iseqv := equivalence

/-- The relation of the concordance setoid is concordance. -/
@[simp]
theorem setoid_r_iff [FiniteDimensional ℝ E'] : (setoid I J n M N).r f g ↔ Concordant f g :=
  Iff.rfl

end Concordant

/-- Smoothly ambient isotopic embeddings are concordant, through the trace of the diffeotopy. -/
theorem SmoothAmbientIsotopic.concordant [IsManifold I n M] [IsManifold J n N] (hn : n ≤ ∞)
    {f g : SmoothEmbedding I J n M N} (hfg : SmoothAmbientIsotopic f g) : Concordant f g := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  have hg : f.transDiffeomorph Φ.final = g := SmoothEmbedding.ext fun x => by simp [hΦ x]
  exact hg ▸ concordant_iff_nonempty.2 ⟨Concordance.ofDiffeotopy hn Φ f⟩

end SmoothEmbedding

end TauCeti
