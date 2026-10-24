/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Topology.Order.Compact

/-!
# The Levi maximum test on complex submanifolds

At a local maximum of the restriction of a real function along a holomorphic map, its Levi form
is nonpositive on the image of the tangent map. Consequently a nonempty compact complex manifold
of positive dimension cannot immerse holomorphically into a strictly plurisubharmonic domain.
The ambient space may itself be a complex manifold, not just a complex vector space.

Real `C²` regularity and Levi positivity are stated in the preferred holomorphic charts. The
conclusions use the actual manifold derivative, with the canonical tangent-to-model maps made
explicit. Neither real criticality of the ambient function nor an embedding hypothesis is needed.
The compactness obstruction applies in particular to embedded complex submanifolds, and requires
no properness hypothesis on the immersion.

`not_isImmersion_of_isManifoldStrictlyPlurisubharmonicAt` states the obstruction using
manifold strict plurisubharmonicity and real manifold `C²` regularity.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*.
* J. Milnor, *Morse Theory*, §7.
-/

public section

open Filter Set Topology
open scoped Manifold

namespace TauCeti

variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ F K}
  [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  {f : N → ℝ} {g : M → N} {x : M}

/-- At a local maximum of a holomorphic pullback, the ambient Levi form is nonpositive on the
image of every tangent vector. The ambient real function need only be `C²` in a chart at `g x`.
In particular, `g x` need not be an ambient critical point. -/
theorem re_leviForm_mfderiv_nonpos_of_isLocalMax
    (hf : ContDiffAt ℝ 2 (f ∘ (extChartAt J (g x)).symm) (extChartAt J (g x) (g x)))
    (hg : ContMDiffAt I J 2 g x) (hmax : IsLocalMax (f ∘ g) x)
    (v : TangentSpace I x) :
    (leviForm (f ∘ (extChartAt J (g x)).symm) (extChartAt J (g x) (g x))
      (tangentSpaceCastModel J (g x) (mfderiv I J g x v))
      (tangentSpaceCastModel J (g x) (mfderiv I J g x v))).re ≤ 0 := by
  let G := writtenInExtChartAt I J x g
  let z := extChartAt I x x
  have hG : ContDiffAt ℂ 2 G z := by
    simpa only [G, z, writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
      contDiffWithinAt_univ] using (contMDiffAt_iff.mp hg).2
  have hGz : G z = extChartAt J (g x) (g x) := by
    simp [G, z, writtenInExtChartAt]
  -- The pullback agrees locally with the composition of the two coordinate expressions.
  have ht : Tendsto (g ∘ (extChartAt I x).symm) (𝓝 z) (𝓝 (g x)) := by
    have hs : Tendsto (extChartAt I x).symm (𝓝 z) (𝓝 x) := by
      simpa only [z, extChartAt_to_inv] using
        (continuousAt_extChartAt_symm (I := I) x).tendsto
    exact hg.continuousAt.tendsto.comp hs
  have heq : ((f ∘ g) ∘ (extChartAt I x).symm) =ᶠ[𝓝 z]
      (f ∘ (extChartAt J (g x)).symm) ∘ G := by
    exact ((comp_extChartAt_symm_comp_extChartAt_eventuallyEq f (g x)).comp_tendsto ht).symm
  have hmax' : IsLocalMax (((f ∘ g) ∘ (extChartAt I x).symm)) z := by
    have hm : IsLocalMax (f ∘ g) ((extChartAt I x).symm z) := by
      simpa [z] using hmax
    exact hm.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  have hf' : ContDiffAt ℝ 2 (f ∘ (extChartAt J (g x)).symm) (G z) := hGz.symm ▸ hf
  have hnonpos := re_leviForm_nonpos_of_isLocalMax
    (hf'.comp z (hG.restrict_scalars ℝ)) (hmax'.congr heq) (tangentSpaceCastModel I x v)
  rw [leviForm_comp_apply hf' hG, hGz] at hnonpos
  -- Identify the coordinate derivative with the actual tangent map, retaining the canonical casts.
  simpa only [G, z, ← tangentSpaceCastModel_mfderiv_apply
    (hg.mdifferentiableAt (by norm_num))] using hnonpos

/-- For a real function that is `C²` near the image of a complex `C²` map from a nonempty
compact complex manifold, at some point its Levi form is nonpositive on the whole tangent image.
Continuity of the restriction follows from the chartwise regularity hypotheses. -/
theorem exists_forall_re_leviForm_mfderiv_nonpos [CompactSpace M] [Nonempty M]
    (hf₂ : ∀ x, ContDiffAt ℝ 2 (f ∘ (extChartAt J (g x)).symm)
      (extChartAt J (g x) (g x)))
    (hg : ContMDiff I J 2 g) :
    ∃ x : M, ∀ v : TangentSpace I x,
      (leviForm (f ∘ (extChartAt J (g x)).symm) (extChartAt J (g x) (g x))
        (tangentSpaceCastModel J (g x) (mfderiv I J g x v))
        (tangentSpaceCastModel J (g x) (mfderiv I J g x v))).re ≤ 0 := by
  have hfc (x : M) : ContinuousAt f (g x) := by
    have hc := (hf₂ x).continuousAt.comp (continuousAt_extChartAt (I := J) (g x))
    exact hc.congr (comp_extChartAt_symm_comp_extChartAt_eventuallyEq f (g x))
  have hcont : Continuous (f ∘ g) := continuous_iff_continuousAt.mpr
    (fun x ↦ (hfc x).comp (hg x).continuousAt)
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  exact ⟨x, fun v ↦ re_leviForm_mfderiv_nonpos_of_isLocalMax (hf₂ x) (hg x)
    (hx.isLocalMax (by simp)) v⟩

/-- **The compact complex submanifold obstruction.** A nonempty compact complex manifold with a
nonzero tangent direction cannot immerse holomorphically into a domain where a continuous real
`C²` function has positive definite Levi form. This includes compact embedded complex
submanifolds of every positive complex dimension. -/
theorem not_forall_injective_mfderiv_of_re_leviForm_pos
    [CompactSpace M] [Nonempty M] [Nontrivial E]
    (hf₂ : ∀ x, ContDiffAt ℝ 2 (f ∘ (extChartAt J (g x)).symm)
      (extChartAt J (g x) (g x)))
    (hpos : ∀ x (w : F), w ≠ 0 →
      0 < (leviForm (f ∘ (extChartAt J (g x)).symm) (extChartAt J (g x) (g x)) w w).re)
    (hg : ContMDiff I J 2 g) : ¬ ∀ x, Function.Injective (mfderiv I J g x) := by
  intro hinj
  obtain ⟨x, hx⟩ := exists_forall_re_leviForm_mfderiv_nonpos hf₂ hg
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let u := (tangentSpaceCastModel I x).symm v
  have hu : u ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hv
  have hw : tangentSpaceCastModel J (g x) (mfderiv I J g x u) ≠ 0 :=
    EmbeddingLike.map_ne_zero_iff.mpr (((hinj x).ne_iff' (map_zero _)).mpr hu)
  exact (not_lt_of_ge (hx u)) (hpos x _ hw)

variable {P : Type*} [TopologicalSpace P] [ChartedSpace F P] {u : P → ℝ} {i : M → P}

/-- A nonempty compact complex manifold with a nonzero tangent direction admits no holomorphic
`C²` immersion into a complex manifold carrying a real `C²` strictly plurisubharmonic function. -/
theorem not_isImmersion_of_isManifoldStrictlyPlurisubharmonicAt
    [CompactSpace M] [Nonempty M] [Nontrivial E]
    (hpos : ∀ y, IsManifoldStrictlyPlurisubharmonicAt F u y)
    (hu : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) 2 u) :
    ¬ Manifold.IsImmersion I 𝓘(ℂ, F) 2 i := by
  intro hi
  refine not_forall_injective_mfderiv_of_re_leviForm_pos
    (I := I) (J := 𝓘(ℂ, F)) (f := u) (g := i) ?_ ?_
    hi.contMDiff (hi.mfderiv_injective (by norm_num))
  · intro x
    simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp] using
      (hu (i x)).contDiffAt_comp_chartAt_symm
  · intro x w hw
    simpa only [manifoldLeviForm_def, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
      Function.id_comp] using
      (isManifoldStrictlyPlurisubharmonicAt_iff.mp (hpos (i x)) w hw)

end TauCeti
