/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.Morse.CWModel
import TauCeti.Geometry.Manifold.Morse.Cell.Band
import TauCeti.Geometry.Manifold.Morse.CWModel.Proper
import TauCeti.Geometry.Manifold.Morse.Generic.Strong
import TauCeti.Topology.Maps.Proper.Basic

/-!
# Finite CW models of compact regular sublevels and CW type from Morse exhaustions

Let `f` be a Morse function on a boundaryless Hausdorff smooth manifold `M`, not assumed compact,
and let `b` be a regular value of `f` whose sublevel `M_b = {f ≤ b}` is compact. Below the minimum
of `f` on `M_b` lies a regular value `a ≤ b` with empty sublevel `M_a` and compact band
`f⁻¹[a, b]`. Extending the empty CW model across this band
(`TauCeti.IsMorse.exists_finite_cwComplex_extension_homotopyEquiv_sublevel`) shows that `M_b` is
homotopy equivalent to a finite CW complex whose `m`-cells correspond to the critical points of `f`
of index `m` in `M_b`
(`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv_of_isCompact_sublevel`), so `M_b` has
finite CW type (`TauCeti.IsMorse.finiteCWType_sublevel`).

When `f` is merely smooth, a regular value `b` lying strictly below a level `c` with compact
sublevel `M_c` is isolated from the critical values of `f` on `M_c`
(`TauCeti.exists_Icc_disjoint_criticalPoints_of_isCompact_sublevel`). Any `C¹` perturbation `g` of
`f` supported outside a closed collar `f⁻¹[b - δ / 2, b + δ / 2]` and within uniform error `δ / 2`
has the same sublevel `{g ≤ b} = {f ≤ b}` and still has `b` as a regular value
(`TauCeti.sublevel_eq_and_isRegularValue_of_abs_sub_lt`). Combining this collar invariance with
relative strong-Whitney Morse approximation shows that `{f ≤ b}` still has finite CW type on any
sigma-compact manifold (`TauCeti.finiteCWType_sublevel_of_isRegularValue`), and in particular for
every regular sublevel of a smooth proper bounded-below exhaustion
(`TauCeti.finiteCWType_sublevel_of_isProperMap`).

Finally, a proper Morse function bounded below gives `CWType M` (`TauCeti.IsMorse.cwType`), so
every sigma-compact boundaryless finite-dimensional Hausdorff smooth manifold has CW type
(`TauCeti.CWType.of_isManifold`, Milnor's Corollary 3.6).

## Main results

* `TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv_of_isCompact_sublevel`: a compact regular
  sublevel `{f ≤ b}` of a Morse function is homotopy equivalent to a finite CW complex whose
  `m`-cells correspond to the critical points of index `m` in `{f ≤ b}`.
* `TauCeti.IsMorse.finiteCWType_sublevel`: a compact regular sublevel of a Morse function has
  finite CW type.
* `TauCeti.exists_Icc_disjoint_criticalPoints_of_isCompact_sublevel` and
  `TauCeti.sublevel_eq_and_isRegularValue_of_abs_sub_lt`: collar isolation of a regular level inside
  a compact higher sublevel and preservation of `{f ≤ b}` under collar-supported `C⁰`-small
  perturbations.
* `TauCeti.finiteCWType_sublevel_of_isRegularValue` and
  `TauCeti.finiteCWType_sublevel_of_isProperMap`: smooth regular sublevels have finite CW type
  without assuming `f` is Morse.
* `TauCeti.IsMorse.cwType` and `TauCeti.CWType.of_isManifold`: manifolds carrying a proper
  bounded-below Morse function, and hence all sigma-compact boundaryless smooth manifolds, have CW
  type.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and Corollary 3.6.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

section Collar

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}

/-- **Collar isolation of a regular value below a compact sublevel.** Let `f : M → ℝ` be `C¹`, let
`b < c` with `{f ≤ c}` compact, and suppose `b` is a regular value of `f`. Then some collar
`f⁻¹[b - δ, b + δ]` with `0 < δ` and `b + δ ≤ c` contains no critical points of `f`. -/
theorem exists_Icc_disjoint_criticalPoints_of_isCompact_sublevel [IsManifold I 1 M]
    (hf : ContMDiff I 𝓘(ℝ) 1 f) {b c : ℝ} (hbc : b < c) (hcompact : IsCompact {x | f x ≤ c})
    (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ δ > 0, b + δ ≤ c ∧ ∀ x ∈ f ⁻¹' Icc (b - δ) (b + δ), x ∉ criticalPoints I f := by
  have hK : IsCompact (criticalPoints I f ∩ {x | f x ≤ c}) :=
    hcompact.inter_left (isClosed_criticalPoints hf)
  have hb_notMem : b ∉ f '' (criticalPoints I f ∩ {x | f x ≤ c}) := by
    rintro ⟨x, ⟨hx, -⟩, rfl⟩
    exact isRegularValue_iff_notMem_image_criticalPoints.1 hb ⟨x, hx, rfl⟩
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1
    (hK.image hf.continuous).isClosed.isOpen_compl b hb_notMem
  refine ⟨min (δ₀ / 2) (c - b), lt_min (half_pos hδ₀) (sub_pos.2 hbc), ?_, fun x hx hcrit ↦ ?_⟩
  · linarith [min_le_right (δ₀ / 2) (c - b)]
  · have hxb : dist (f x) b < δ₀ := by
      rw [Real.dist_eq]
      have h1 : |f x - b| ≤ min (δ₀ / 2) (c - b) := abs_sub_le_iff.2 ⟨by linarith [hx.2],
        by linarith [hx.1]⟩
      exact h1.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ₀))
    have hxc : f x ≤ c := hx.2.trans (by linarith [min_le_right (δ₀ / 2) (c - b)])
    exact hball hxb ⟨x, ⟨hcrit, hxc⟩, rfl⟩

/-- **Collar-supported perturbations preserve the regular sublevel.** Suppose `f` is continuous and
`f` has no critical points in `f⁻¹[b - δ, b + δ]` (`δ > 0`), `|g - f| < δ / 2` everywhere, and
`g = f` on `f⁻¹[b - δ / 2, b + δ / 2]`. Then `{g ≤ b} = {f ≤ b}` and `b` is a regular value of
`g`. -/
theorem sublevel_eq_and_isRegularValue_of_abs_sub_lt {g : M → ℝ}
    (hf : Continuous f) {b δ : ℝ} (hδ : 0 < δ)
    (hcrit : ∀ x ∈ f ⁻¹' Icc (b - δ) (b + δ), x ∉ criticalPoints I f)
    (hgf : ∀ x, |g x - f x| < δ / 2)
    (hsupp : tsupport (fun x ↦ g x - f x) ⊆ (f ⁻¹' Icc (b - δ / 2) (b + δ / 2))ᶜ) :
    {x | g x ≤ b} = {x | f x ≤ b} ∧ IsRegularValue I 𝓘(ℝ) g b := by
  have hgf_eq {x : M} (hx : f x ∈ Icc (b - δ / 2) (b + δ / 2)) : g x = f x :=
    sub_eq_zero.1 <| image_eq_zero_of_notMem_tsupport (f := fun x ↦ g x - f x)
      fun hmem ↦ hsupp hmem hx
  refine ⟨?_, isRegularValue_iff_notMem_image_criticalPoints.2 ?_⟩
  · ext x
    by_cases hx : f x ∈ Icc (b - δ / 2) (b + δ / 2)
    · simp [hgf_eq hx]
    · simp only [mem_Icc, not_and_or, not_le] at hx
      have hdist := abs_lt.1 (hgf x)
      rcases hx with hlt | hgt <;> simp only [mem_ofPred_eq] <;> constructor <;> intro <;> linarith
  · rintro ⟨x, hx_crit, hxg⟩
    have hx_open : x ∈ f ⁻¹' Ioo (b - δ / 2) (b + δ / 2) := by
      have hdist := abs_lt.1 (hgf x)
      exact ⟨by linarith, by linarith⟩
    have hev : g =ᶠ[𝓝 x] f := Filter.eventuallyEq_of_mem
      ((isOpen_Ioo.preimage hf).mem_nhds hx_open)
      fun y hy ↦ hgf_eq (Ioo_subset_Icc_self hy)
    refine hcrit x ⟨by linarith [hx_open.1], by linarith [hx_open.2]⟩ ?_
    rw [mem_criticalPoints_iff_mfderiv_eq_zero] at hx_crit ⊢
    simp [hev.symm.mfderiv_eq, hx_crit]

end Collar

section Sublevel

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- **The finite CW model of a compact regular sublevel.** Let `f` be a Morse function on a
boundaryless Hausdorff manifold `M`, not assumed compact, and let `b` be a regular value of `f`
with compact sublevel `{f ≤ b}`. Then `{f ≤ b}` is homotopy equivalent to a finite CW complex `W`
whose `m`-cells correspond to the critical points of `f` of index `m` in `{f ≤ b}`. -/
theorem IsMorse.exists_finite_cwComplex_homotopyEquiv_of_isCompact_sublevel (hf : IsMorse I f)
    {b : ℝ} (hcompact : IsCompact {x | f x ≤ b}) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ {x | f x ≤ b}) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic b | manifoldMorseIndex I f x = m}) := by
  rcases isEmpty_or_nonempty {x | f x ≤ b} with hK | hK
  · -- When `{f ≤ b}` is empty, `PEmpty` is its finite CW model with no cells in any dimension.
    have hcell (m : ℕ) : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) :=
      ⟨fun j ↦ (map m j 0).elim⟩
    have hcrit (m : ℕ) :
        IsEmpty ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Iic b | manifoldMorseIndex I f x = m} :=
      ⟨fun x ↦ hK.false ⟨x.1, x.2.1.2⟩⟩
    exact ⟨PEmpty.{u + 1}, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨Homeomorph.empty.toHomotopyEquiv⟩, fun m ↦ ⟨Equiv.equivOfIsEmpty _ _⟩⟩
  -- A nonempty compact regular sublevel forces `E` to be finite-dimensional and bounds `f` below.
  have := finiteDimensional_of_isCompact_sublevel hf.contMDiff.continuous hcompact hb
  obtain ⟨a, hab, hempty, hband, ha⟩ :=
    exists_isEmpty_sublevelPair_of_isCompact_sublevel (I := I) hf.contMDiff.continuous hcompact
  have ha_lt (x : M) : a < f x := not_le.1 fun h ↦ hempty.false ⟨x, h⟩
  have : IsEmpty {x | f x ≤ a} := ⟨fun x ↦ (ha_lt x.1).not_ge x.2⟩
  obtain ⟨W, _, _, _, -, e, hfin, -, -, -, c, -⟩ :=
    hf.exists_finite_cwComplex_extension_homotopyEquiv_sublevel hab hband ha hb PEmpty.{u + 1}
      Homeomorph.empty.toHomotopyEquiv
  refine ⟨W, _, ‹_›, ‹_›, hfin, ⟨e⟩, fun m ↦ ⟨?_⟩⟩
  have : IsEmpty (cell (univ : Set PEmpty.{u + 1}) m) := ⟨fun j ↦ (map m j 0).elim⟩
  refine (c m).trans ((Equiv.emptySum _ _).trans (Set.equivOfEq ?_))
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioc, mem_Iic]
  exact and_congr_left fun _ ↦ and_congr_right fun _ ↦ ⟨And.right, fun hxb ↦ ⟨ha_lt x, hxb⟩⟩

/-- A compact regular sublevel of a Morse function on a boundaryless Hausdorff manifold has finite
CW type. -/
theorem IsMorse.finiteCWType_sublevel (hf : IsMorse I f) {b : ℝ}
    (hcompact : IsCompact {x | f x ≤ b}) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    FiniteCWType {x | f x ≤ b} := by
  obtain ⟨W, _, _, _, _, ⟨e⟩, -⟩ :=
    hf.exists_finite_cwComplex_homotopyEquiv_of_isCompact_sublevel hcompact hb
  exact (e.symm.trans (Homeomorph.Set.univ W).symm.toHomotopyEquiv).finiteCWType

end Sublevel

section FiniteDimensional

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- **Smooth regular sublevels inside a compact higher sublevel have finite CW type.** Let
`f : M → ℝ` be smooth (not assumed Morse) on a sigma-compact manifold `M`, and let `b < c` with
`{f ≤ c}` compact and `b` a regular value of `f`. Then `{f ≤ b}` has finite CW type. -/
theorem finiteCWType_sublevel_of_isRegularValue [SigmaCompactSpace M]
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {b c : ℝ} (hbc : b < c) (hcompact : IsCompact {x | f x ≤ c})
    (hb : IsRegularValue I 𝓘(ℝ) f b) : FiniteCWType {x | f x ≤ b} := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by norm_cast)
  obtain ⟨δ, hδ, -, hcrit⟩ :=
    exists_Icc_disjoint_criticalPoints_of_isCompact_sublevel (hf.of_le (by simp)) hbc hcompact hb
  let F : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ := ⟨f, hf⟩
  have hfV : IsMorseOn I F (f ⁻¹' Ioo (b - δ) (b + δ)) :=
    isMorseOn_iff_criticalPoints.2 ⟨hf.contMDiffOn, fun x hx_mem hx_crit ↦
      (hcrit x (Ioo_subset_Icc_self hx_mem) hx_crit).elim⟩
  obtain ⟨g, -, hgm, hgf, hgs⟩ := F.exists_isMorse_mem_ball_sub_compl
    ContMDiffMap.StrongCkControl.empty continuous_const (fun _ ↦ half_pos hδ)
    (C := f ⁻¹' Icc (b - δ / 2) (b + δ / 2)) (V := f ⁻¹' Ioo (b - δ) (b + δ))
    (isClosed_Icc.preimage hf.continuous) (isOpen_Ioo.preimage hf.continuous)
    (preimage_mono (Icc_subset_Ioo (by linarith) (by linarith))) hfV
  obtain ⟨hsub_eq, hgb⟩ := sublevel_eq_and_isRegularValue_of_abs_sub_lt hf.continuous hδ hcrit
    hgf hgs
  have hcompact_b : IsCompact {x | (g : M → ℝ) x ≤ b} := by
    rw [hsub_eq]
    exact hcompact.of_isClosed_subset (isClosed_le hf.continuous continuous_const)
      fun x hx ↦ hx.trans hbc.le
  have := hgm.finiteCWType_sublevel hcompact_b hgb
  exact (Homeomorph.setCongr hsub_eq).symm.finiteCWType

/-- **Regular sublevels of a smooth proper bounded-below exhaustion have finite CW type.** -/
theorem finiteCWType_sublevel_of_isProperMap (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) {b : ℝ} (hb : IsRegularValue I 𝓘(ℝ) f b) :
    FiniteCWType {x | f x ≤ b} := by
  have : SigmaCompactSpace M := hp.sigmaCompactSpace
  obtain ⟨m, hm⟩ := hbdd
  have hcompact : IsCompact {x | f x ≤ b + 1} := by
    have heq : {x | f x ≤ b + 1} = f ⁻¹' Icc m (b + 1) := by
      ext x
      exact ⟨fun hx ↦ ⟨hm (mem_range_self x), hx⟩, And.right⟩
    rw [heq]
    exact hp.isCompact_preimage isCompact_Icc
  exact finiteCWType_sublevel_of_isRegularValue hf (lt_add_one b) hcompact hb

/-- A boundaryless manifold carrying a proper Morse function bounded below has CW type. -/
theorem IsMorse.cwType (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) :
    CWType M := by
  obtain ⟨X, _, _, _, ⟨e⟩, -⟩ := hf.exists_cwComplex_homotopyEquiv hp hbdd
  exact (e.trans (Homeomorph.Set.univ X).symm.toHomotopyEquiv).cwType

variable (I M) in
include I in
/-- **Sigma-compact manifolds have CW type** (Milnor, *Morse Theory*, Corollary 3.6). Every
sigma-compact boundaryless Hausdorff smooth manifold with a finite-dimensional model is homotopy
equivalent to a CW complex. -/
theorem CWType.of_isManifold [SigmaCompactSpace M] : CWType M := by
  obtain ⟨g, hgm, hgp, hgbdd⟩ := exists_isMorse_isProperMap_bddBelow (I := I) (M := M)
  exact hgm.cwType hgp hgbdd

end FiniteDimensional

end TauCeti
