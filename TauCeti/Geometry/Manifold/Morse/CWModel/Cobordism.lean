/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph

/-!
# Relative CW models of regular cobordisms

Let `f` be a Morse function on a boundaryless manifold `M`, and let `a ≤ b` be regular values of
`f` with compact band `W = f⁻¹[a, b]`. Then `W` is a cobordism from its incoming boundary
`f⁻¹(a)` to its outgoing boundary `f⁻¹(b)`. This file builds its CW models relative to either
boundary.

Relative to the incoming boundary, `W` is homotopy equivalent to `f⁻¹(a)` with one `λ`-cell
attached for each critical point of index `λ` in `W`, arranged as a CW complex relative to a copy
of `f⁻¹(a)`, by a homotopy equivalence which is the inclusion on `f⁻¹(a)`
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_band`). Relative to the outgoing boundary the
same holds with the cells indexed by the critical points of `-f`, so that a critical point of
index `λ` of `f` gives a cell of the complementary dimension `dim M - λ`
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_upperBand`). These are the CW forms of the
Morse inequalities for the band pairs `(f⁻¹[a, b], f⁻¹(a))` and `(f⁻¹[a, b], f⁻¹(b))` in
`TauCeti.Geometry.Manifold.Morse.Inequalities`.

The incoming model is the relative CW model of the sublevels of `f` on the open submanifold
`V = {a < f}` (`TauCeti.IsMorse.exists_relCWComplex_extension_homotopyEquiv_sublevel`), started
from `f⁻¹(a)` itself. Since `a` is a regular value, the band `f⁻¹[a, s]` is a collar without
critical points for some `s > a`, along which a flow `φ` moves `f` at unit speed
(`TauCeti.exists_flow_apply_eq_sub`). Pushing the level `f⁻¹(a)` up into `V` along `φ` identifies
it, up to homotopy, with the sublevel `{x ∈ V | f x ≤ s}`
(`Flow.exists_homotopyEquiv_level_sublevel`), and pushing the bottom of the collar back down
identifies `{x ∈ V | f x ≤ b} = f⁻¹(a, b]` with `W` (`Flow.exists_homotopyEquiv_sublevel_band`).
The two pushes are chosen to cancel on `f⁻¹(a)`, so the resulting homotopy equivalence is exactly
the inclusion there.

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_band`: **the relative CW model of a regular
  cobordism.** `f⁻¹[a, b]` is homotopy equivalent to a CW complex relative to a copy of `f⁻¹(a)`
  with one `m`-cell for each critical point of index `m` in the band, by a homotopy equivalence
  restricting to the inclusion on `f⁻¹(a)`.
* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_upperBand`: the relative CW model of
  `f⁻¹[a, b]` relative to its outgoing boundary `f⁻¹(b)`, with one `m`-cell for each critical
  point of index `dim M - m` in the band.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and its proof.
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, Theorem 3.4,
  for the collar of a regular level.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006, Theorem 5.7.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- **The relative CW model of a regular cobordism.** Let `f` be a Morse function and `a ≤ b`
regular values of `f` with compact band `f⁻¹[a, b]`. Then the band is homotopy equivalent to a CW
complex `X` relative to a copy of its incoming boundary `f⁻¹(a)`, with one `m`-cell for each
critical point of index `m` with value in `(a, b]`: there are a closed embedding
`j : f⁻¹(a) → X`, a relative CW structure on `X` with base the image of `j`, and a homotopy
equivalence `h : X ≃ₕ f⁻¹[a, b]` such that `h ∘ j` is the inclusion `f⁻¹(a) ⊆ f⁻¹[a, b]`. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_band (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ (∀ x, (h (j x) : M) = x) ∧
      Nonempty (∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) := by
  have hfc : Continuous f := hf.contMDiff.continuous
  rcases hab.eq_or_lt with rfl | hab'
  · -- A band of width zero is its level, a CW complex relative to itself with no cells.
    let := relCWComplexSelf (univ : Set (f ⁻¹' {a})) isClosed_univ
    have (m : ℕ) : IsEmpty ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a a |
        manifoldMorseIndex I f x = m} :=
      ⟨fun x ↦ (lt_irrefl a) (x.2.1.2.1.trans_le x.2.1.2.2)⟩
    refine ⟨f ⁻¹' {a}, _, inferInstance, .id _, ?_⟩
    rw [ContinuousMap.coe_id, range_id]
    exact ⟨‹_›, (Homeomorph.setCongr (by rw [Icc_self])).toHomotopyEquiv, .id,
      fun x ↦ rfl, ⟨fun m ↦ Equiv.equivOfIsEmpty _ _⟩⟩
  -- A collar `f⁻¹[a, s]` above `a` without critical points, with a flow `φ` moving `f` at unit
  -- speed through it.
  obtain ⟨s, ⟨has, hsb⟩, hcrit⟩ :=
    exists_mem_Ioc_forall_notMem_criticalPoints (hf.contMDiff.of_le (by simp)) hab' hcompact ha
  obtain ⟨φ, -, hanti, hlt, hφf⟩ := exists_flow_apply_eq_sub hf.contMDiff
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc_right hsb)))
    fun x hxa hxs h0 ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) ⟨hxa, hxs⟩
  have hφ (y : M) (t : ℝ) (hy : f y ∈ Icc a s) (ht : f y - t ∈ Icc a s) :
      f (φ t y) = f y - t :=
    φ.apply_eq_sub_of_mem_Icc hfc (fun x ↦ (hanti x).antitoneOn _) hφf
      (fun x t hx ht ↦ (hlt x t hx.ge (hx.trans_le has.le) ht).trans_eq hx) hy ht
  -- On the open submanifold `V = {a < f}` the sublevels of `f` are `f⁻¹(a, t]`.
  let V : TopologicalSpace.Opens M := ⟨{x | a < f x}, isOpen_lt continuous_const hfc⟩
  have hV (x : M) : x ∈ V ↔ a < f x := Iff.rfl
  have hfV : IsMorse I (f ∘ Subtype.val : V → ℝ) :=
    hf.comp_isLocalDiffeomorph isLocalDiffeomorph_subtype_val
  have hKV : IsCompact ((f ∘ Subtype.val : V → ℝ) ⁻¹' Icc s b) := by
    have hsub : f ⁻¹' Icc s b ⊆ range (Subtype.val : V → M) :=
      fun x hx ↦ ⟨⟨x, (hV x).2 (has.trans_le hx.1)⟩, rfl⟩
    rw [Subtype.isCompact_iff, preimage_comp, image_preimage_eq_of_subset hsub]
    exact hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc_left has.le))
  have hs : IsRegularValue I 𝓘(ℝ) f s := isRegularValue_iff_notMem_image_criticalPoints.2
    fun ⟨x, hx, hxs⟩ ↦ hcrit x hx ⟨hxs.symm ▸ has.le, hxs.le⟩
  -- The relative CW model of `f⁻¹(a, b]` over `f⁻¹(a, s]`, started from `f⁻¹(a)` itself, followed
  -- by the identification of `f⁻¹(a, b]` with the band.
  obtain ⟨h₀, hh₀⟩ := φ.exists_homotopyEquiv_level_sublevel hfc has hφ V hV
  obtain ⟨k, hk⟩ := φ.exists_homotopyEquiv_sublevel_band hfc has hsb hφ V hV
  let := relCWComplexSelf (univ : Set (f ⁻¹' {a})) isClosed_univ
  obtain ⟨X, _, _, ι, D', _, h', hD', hι, -, hh, e, -⟩ :=
    hfV.exists_relCWComplex_extension_homotopyEquiv_sublevel hsb hKV (hs.restrict V)
      (hb.restrict V) (f ⁻¹' {a}) univ h₀
  rw [image_univ] at hD'
  subst hD'
  -- The critical points of `f` on `V` with values in `(s, b]` are those of `f` in `(a, b]`.
  have hidx (y : V) (hy : (y : M) ∈ criticalPoints I f) :
      manifoldMorseIndex I (f ∘ Subtype.val) y = manifoldMorseIndex I f y :=
    (isLocalDiffeomorph_subtype_val (I := I) (n := ∞) y).manifoldMorseIndex_comp (by simp)
      (hf.contMDiff.contMDiffAt.of_le (by simp)) hy
  let c (i : ℕ) : ↥{y ∈ criticalPoints I (f ∘ Subtype.val : V → ℝ) ∩
        (f ∘ Subtype.val) ⁻¹' Ioc s b | manifoldMorseIndex I (f ∘ Subtype.val) y = i} ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i} :=
    { toFun y := ⟨y.1, ⟨mem_criticalPoints_comp_subtypeVal.1 y.2.1.1,
        has.trans y.2.1.2.1, y.2.1.2.2⟩,
        (hidx _ (mem_criticalPoints_comp_subtypeVal.1 y.2.1.1)).symm.trans y.2.2⟩
      invFun x := ⟨⟨x.1, x.2.1.2.1⟩, ⟨mem_criticalPoints_comp_subtypeVal.2 x.2.1.1,
        lt_of_not_ge fun h ↦ hcrit x x.2.1.1 ⟨x.2.1.2.1.le, h⟩, x.2.1.2.2⟩,
        (hidx ⟨x.1, x.2.1.2.1⟩ x.2.1.1).trans x.2.2⟩
      left_inv y := rfl
      right_inv x := rfl }
  refine ⟨X, _, ‹_›, ι, ‹_›, h'.trans k, hι, fun x ↦ ?_,
    ⟨fun i ↦ (e i).trans ((Equiv.emptySum _ _).trans (c i))⟩⟩
  -- On the level `f⁻¹(a)` the push up and the push down cancel.
  have hx : ((h' (ι x) : V) : M) = φ (a - (a + s) / 2) x := (congrArg Subtype.val (hh x)).trans
    (hh₀ x).1
  have hm : f ((h' (ι x) : V) : M) = (a + s) / 2 := by
    rw [hh x]
    exact (hh₀ x).2
  rw [ContinuousMap.HomotopyEquiv.trans_apply, hk _ hm, hx, ← Flow.map_add, sub_add_sub_cancel,
    sub_self, Flow.map_zero_apply]

/-- **The relative CW model of a regular cobordism relative to its outgoing boundary.** Let `f` be
a Morse function on a manifold of dimension `n`, and `a ≤ b` regular values of `f` with compact
band `f⁻¹[a, b]`. Then the band is homotopy equivalent to a CW complex `X` relative to a copy of
its outgoing boundary `f⁻¹(b)`, with one `m`-cell for each critical point of index `n - m` with
value in `[a, b)`: there are a closed embedding `j : f⁻¹(b) → X`, a relative CW structure on `X`
with base the image of `j`, and a homotopy equivalence `h : X ≃ₕ f⁻¹[a, b]` such that `h ∘ j` is
the inclusion `f⁻¹(b) ⊆ f⁻¹[a, b]`. This is the model of the same band for `-f`, relative to its
incoming boundary `(-f)⁻¹(-b) = f⁻¹(b)`. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_upperBand (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {b}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ (∀ x, (h (j x) : M) = x) ∧
      Nonempty (∀ m, cell (univ : Set X) m ≃ ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
        manifoldMorseIndex I f x + m = Module.finrank ℝ E}) := by
  obtain ⟨X, _, _, j, C, h, hj, hh, ⟨e⟩⟩ := hf.neg.exists_relCWComplex_homotopyEquiv_band
    (neg_le_neg hab) (by rwa [preimage_neg_Icc_neg]) (isRegularValue_neg_iff.2 (by rwa [neg_neg]))
    (isRegularValue_neg_iff.2 (by rwa [neg_neg]))
  -- The outgoing boundary of the band is the incoming boundary of the band of `-f`.
  have hL : f ⁻¹' {b} = (-f) ⁻¹' {-b} := by
    ext
    simp
  let j' : C(f ⁻¹' {b}, X) := j.comp ⟨_, (Homeomorph.setCongr hL).continuous⟩
  have hr : range j = range j' := ((Homeomorph.setCongr hL).surjective.range_comp j).symm
  generalize hD : range j = D at C e
  obtain rfl : D = range j' := hD.symm.trans hr
  exact ⟨X, _, ‹_›, j', C,
    h.trans (Homeomorph.setCongr (preimage_neg_Icc_neg f a b)).toHomotopyEquiv,
    hj.comp (Homeomorph.setCongr hL).isClosedEmbedding, fun x ↦ hh _,
    ⟨fun m ↦ (e m).trans (Set.equivOfEq (hf.setOf_neg_band_eq a b m))⟩⟩

end TauCeti
