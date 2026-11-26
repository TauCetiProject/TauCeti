/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial.Topology
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic

/-!
# Pushforward of distributions along smooth maps of manifolds

Let `f : M → N` be a smooth map of manifolds and `χ` a compactly supported smooth function on `M`.
The tests on `M` with values in a normed space `F` are the bundle tests
`TauCeti.BundleTest I F (Bundle.Trivial M F)`, the compactly supported smooth functions `M → F`
with their test topology; for `F = ℝ` these are the scalar tests, which pair with the
distribution densities on `M`. The **composition with a cutoff**

`φ ↦ χ · (φ ∘ f)`

sends tests on `N` to tests on `M`, whether or not `f` is proper, and it is continuous for the test
topologies (`TauCeti.BundleTest.cutoffCompCLM`). Its transpose is the **pushforward with a cutoff**

`f_* (χ T) : φ ↦ T (χ · (φ ∘ f))`

of a continuous linear functional `T` on the tests on `M`
(`TauCeti.BundleTest.cutoffPushforwardCLM`), a continuous linear map for the topologies of uniform
convergence on compact sets of tests. When `χ` is equal to `1` near the support of `T`, which is
then compact, this is the pushforward `⟨f_* T, φ⟩ = ⟨T, χ (φ ∘ f)⟩` of `T` along `f`, and it does
not depend on the cutoff.

The supports of functionals enter through the sets `O` on which they vanish: `T` vanishes on `O`
when `T s = 0` for every test `s` supported in `O`; the complement of the support of `T` is the
largest open such set. This file proves:

* **independence of the cutoff**: if `T` vanishes on `O`, then cutoffs that agree off a closed
  subset of `O` give the same pushforward (`TauCeti.BundleTest.cutoffPushforwardCLM_congr`);
* **support**: if `T` vanishes on `O`, then `f_* (χ T)` vanishes on the tests supported away from
  `f (supp χ \ O)`, so the support of `f_* (χ T)` lies in `f (supp χ ∩ supp T)`
  (`TauCeti.BundleTest.cutoffPushforwardCLM_apply_eq_zero_of_disjoint`);
* **identity**: along the identity the pushforward with the cutoff `χ` is the product `χ T`
  (`TauCeti.BundleTest.cutoffPushforwardCLM_id_eq_smulLeftDualCLM`), and it is `T` when `χ` is
  equal to `1` near the support of `T` (`TauCeti.BundleTest.cutoffPushforwardCLM_id`);
* **functoriality**: `g_* (χ' f_* (χ T)) = (g ∘ f)_* ((χ · (χ' ∘ f)) T)`
  (`TauCeti.BundleTest.cutoffPushforwardCLM_cutoffPushforwardCLM`), which is `(g ∘ f)_* (χ T)`
  when `χ'` is equal to `1` near `f (supp χ ∩ supp T)`
  (`TauCeti.BundleTest.cutoffPushforwardCLM_cutoffPushforwardCLM_of_eventually_eq_one`);
* **products with smooth functions**: `f_* (χ (ψ T)) = f_* ((ψ χ) T)` and the projection formula
  `g · f_* (χ T) = f_* ((χ · (g ∘ f)) T)`
  (`TauCeti.BundleTest.cutoffPushforwardCLM_smulLeftDualCLM`,
  `TauCeti.BundleTest.smulLeftDualCLM_cutoffPushforwardCLM`);
* **point masses**: `f_* (χ δ_x ℓ) = χ(x) δ_{f x} ℓ`
  (`TauCeti.BundleTest.cutoffPushforwardCLM_delta`).

When `f` is proper, `φ ∘ f` is itself a test (`TauCeti.BundleTest.compCLM`), and every functional
has a pushforward `f_* T : φ ↦ T (φ ∘ f)` (`TauCeti.BundleTest.pushforwardCLM`), with
`(g ∘ f)_* = g_* ∘ f_*` (`TauCeti.BundleTest.pushforwardCLM_pushforwardCLM`). The pushforward with
a cutoff is the pushforward of `χ T`, so it is `f_* T` when `χ` is equal to `1` near the support
of `T` (`TauCeti.BundleTest.cutoffPushforwardCLM_eq_pushforwardCLM`).

The continuity of the composition with a cutoff rests on the continuity of the pullback of
sections of trivial bundles in the compact derivative topologies
(`ContMDiffSection.continuous_trivialPullback`): in the preferred frames of a trivial bundle the
coefficients of a section are its values, and composition with a fixed smooth map is continuous in
the weak Whitney topology (`ContMDiffMap.continuous_comp_manifoldWeakWhitney`).

These are the manifold versions of `TestFunction.cutoffCompCLM` and
`Distribution.cutoffPushforwardCLM` on open subsets of normed spaces.

## Main declarations

* `TauCeti.BundleTest.cutoffCompCLM`: the composition `φ ↦ χ · (φ ∘ f)` of tests with a cutoff.
* `TauCeti.BundleTest.cutoffPushforwardCLM`: the pushforward `f_* (χ T)` with a cutoff.
* `TauCeti.BundleTest.compCLM`, `TauCeti.BundleTest.pushforwardCLM`: composition of tests with a
  proper map and the pushforward along it.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.1 (pullback and pushforward of distributions) and §6.3 (distributions on
  manifolds).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, Studia Math. 232 (2016), arXiv:1409.7662v2, §3
  (pushforward along maps proper on the support).
-/

public noncomputable section

open Bundle Set Function Filter Topology TopologicalSpace ContMDiffSection ContinuousLinearMap
open scoped ContDiff Manifold CompactConvergenceCLM TauCeti.ManifoldWeakWhitney

namespace TauCeti.BundleTest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [LocallyCompactSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [LocallyCompactSpace E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Composition of tests with a cutoff -/

/-- The **composition with a cutoff** `φ ↦ χ · (φ ∘ f)` of tests on `N` with a smooth map
`f : M → N`, where `χ` is a compactly supported smooth function on `M`: its value at `x` is
`χ x • φ (f x)` (`TauCeti.BundleTest.cutoffCompCLM_apply`). The cutoff makes the composite
compactly supported, whether or not `f` is proper. It is a continuous linear map for the test
topologies. -/
def cutoffCompCLM (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯) :
    BundleTest J F (Bundle.Trivial N F) →L[ℝ] BundleTest I F (Bundle.Trivial M F) where
  toFun φ := ofCompactlySupported I F _
    ⟨χ • trivialPullback f ((ofCompactlySupported J F _).symm φ).val,
      smul_function_mem_compactlySupported_of_hasCompactSupport χ hχ _⟩
  map_add' φ ψ := by ext x; simp [smul_add]
  map_smul' a φ := by ext x; simp [smul_comm (χ x) a]
  cont := by
    let := frameTopology (I := J) (n := ∞)
      (fun y : N ↦ trivializationAt F (Bundle.Trivial N F) y)
      (fun y ↦ ⟨_, (trivializationAt F (Bundle.Trivial N F) y).open_baseSet⟩) fun _ ↦ subset_rfl
    let := frameTopology (I := I) (n := ∞)
      (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
      (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩) fun _ ↦ subset_rfl
    -- The composite lands in the fixed stage of the sections supported in `supp χ`.
    let L : Compacts M := ⟨_root_.tsupport χ, hχ⟩
    have hval : Continuous fun φ : BundleTest J F (Bundle.Trivial N F) ↦
        ((ofCompactlySupported J F _).symm φ).val :=
      continuous_val_compactlySupportedTopology (I := J) (n := ∞) _ _ _
    refine ((continuous_ofSupportedIn (F := F) L).comp
      ((((continuous_smul_function_frameTopology _ _ _ χ).comp
        (continuous_trivialPullback f)).comp hval).subtype_mk
        fun φ ↦ mem_supportedIn.2 <|
          (tsupport_smul_function_subset χ _).trans inter_subset_left)).congr fun φ ↦ ?_
    simp [Subtype.ext_iff]

@[simp]
theorem cutoffCompCLM_apply (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, M; J, N⟯) (φ : BundleTest J F (Bundle.Trivial N F)) (x : M) :
    cutoffCompCLM χ hχ f φ x = χ x • φ (f x) := by
  simp [cutoffCompCLM]

/-- Along the identity, the composition with a cutoff is multiplication by the cutoff. -/
@[simp]
theorem cutoffCompCLM_id (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ) :
    cutoffCompCLM (F := F) χ hχ ContMDiffMap.id = smulLeftCLM χ := by
  ext φ x
  simp

/-- Compositions with cutoffs compose: composing with `g` and the cutoff `χ'` and then with `f`
and the cutoff `χ` is composing with `g ∘ f` and the cutoff `χ · (χ' ∘ f)`. -/
theorem cutoffCompCLM_cutoffCompCLM (χ' : C^∞⟮J, N; ℝ⟯) (hχ' : HasCompactSupport χ')
    (g : C^∞⟮J, N; K, P⟯) (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯)
    (φ : BundleTest K F (Bundle.Trivial P F)) :
    cutoffCompCLM χ hχ f (cutoffCompCLM χ' hχ' g φ) =
      cutoffCompCLM (χ * χ'.comp f) hχ.mul_right (g.comp f) φ := by
  ext x
  simp [smul_smul]

/-- The composition of `φ` with a cutoff is supported in the part of the support of `χ` that `f`
maps into the support of `φ`. -/
theorem closure_cutoffCompCLM_ne_zero_subset (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, M; J, N⟯) (φ : BundleTest J F (Bundle.Trivial N F)) :
    closure {x | cutoffCompCLM χ hχ f φ x ≠ 0} ⊆
      _root_.tsupport χ ∩ f ⁻¹' closure {y | φ y ≠ 0} :=
  closure_minimal (fun x hx ↦ by
      simp only [mem_ofPred_eq, cutoffCompCLM_apply, smul_ne_zero_iff] at hx
      exact ⟨subset_tsupport _ hx.1, subset_closure hx.2⟩)
    ((_root_.isClosed_tsupport _).inter (isClosed_closure.preimage f.contMDiff.continuous))

/-- Compositions with two cutoffs differ by a test supported where the cutoffs differ. -/
theorem closure_cutoffCompCLM_sub_ne_zero_subset {χ χ' : C^∞⟮I, M; ℝ⟯}
    (hχ : HasCompactSupport χ) (hχ' : HasCompactSupport χ') (f : C^∞⟮I, M; J, N⟯)
    (φ : BundleTest J F (Bundle.Trivial N F)) :
    closure {x | (cutoffCompCLM χ hχ f φ - cutoffCompCLM χ' hχ' f φ) x ≠ 0} ⊆
      closure {x | χ x ≠ χ' x} :=
  closure_mono fun x hx ↦ by
    simp only [mem_ofPred_eq, sub_apply, cutoffCompCLM_apply, ← sub_smul,
      smul_ne_zero_iff] at hx
    exact sub_ne_zero.1 hx.1

/-! ### Composition of tests with a proper map -/

/-- The composition `φ ↦ φ ∘ f` of tests with a proper smooth map, as a linear map. -/
private def compLinearMap (f : C^∞⟮I, M; J, N⟯) (hf : IsProperMap f) :
    BundleTest J F (Bundle.Trivial N F) →ₗ[ℝ] BundleTest I F (Bundle.Trivial M F) where
  toFun φ := ofCompactlySupported I F _
    ⟨trivialPullback f ((ofCompactlySupported J F _).symm φ).val,
      mem_compactlySupported.2 <| (hf.isCompact_preimage (mem_compactlySupported.1
        ((ofCompactlySupported J F _).symm φ).property)).of_isClosed_subset
          (ContMDiffSection.isClosed_tsupport _) (tsupport_trivialPullback_subset f _)⟩
  map_add' φ ψ := by ext x; simp
  map_smul' a φ := by ext x; simp

/-- The **composition** `φ ↦ φ ∘ f` of tests on `N` with a smooth map `f : M → N` that is proper,
so that `φ ∘ f` is again compactly supported. It is a continuous linear map for the test
topologies. -/
def compCLM (f : C^∞⟮I, M; J, N⟯) (hf : IsProperMap f) :
    BundleTest J F (Bundle.Trivial N F) →L[ℝ] BundleTest I F (Bundle.Trivial M F) where
  toLinearMap := compLinearMap f hf
  cont := by
    let := frameTopology (I := J) (n := ∞)
      (fun y : N ↦ trivializationAt F (Bundle.Trivial N F) y)
      (fun y ↦ ⟨_, (trivializationAt F (Bundle.Trivial N F) y).open_baseSet⟩) fun _ ↦ subset_rfl
    let := frameTopology (I := I) (n := ∞)
      (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
      (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp (compLinearMap f hf)).2 fun L ↦ ?_
    -- The composition maps the stage of the sections supported in `L` into the stage of the
    -- sections supported in the compact set `f⁻¹ L`.
    let L' : Compacts M := ⟨f ⁻¹' L, hf.isCompact_preimage L.isCompact⟩
    refine ((continuous_ofSupportedIn (F := F) L').comp
      (((continuous_trivialPullback f).comp continuous_subtypeVal).subtype_mk
        fun s ↦ mem_supportedIn.2 <| (tsupport_trivialPullback_subset f _).trans
          (preimage_mono (mem_supportedIn.1 s.property)))).congr fun s ↦ ?_
    simp [compLinearMap, Subtype.ext_iff]

@[simp]
theorem compCLM_apply (f : C^∞⟮I, M; J, N⟯) (hf : IsProperMap f)
    (φ : BundleTest J F (Bundle.Trivial N F)) (x : M) :
    compCLM f hf φ x = φ (f x) := by
  simp [compCLM, compLinearMap]

/-- Composition with the identity is the identity. -/
@[simp]
theorem compCLM_id
    (hid : IsProperMap (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) := by exact isProperMap_id) :
    compCLM (F := F) ContMDiffMap.id hid = ContinuousLinearMap.id ℝ _ := by
  ext φ x
  simp

/-- Compositions with proper maps compose. -/
theorem compCLM_compCLM (g : C^∞⟮J, N; K, P⟯) (hg : IsProperMap g) (f : C^∞⟮I, M; J, N⟯)
    (hf : IsProperMap f) (φ : BundleTest K F (Bundle.Trivial P F))
    (hgf : IsProperMap (g.comp f) := by exact hg.comp hf) :
    compCLM f hf (compCLM g hg φ) = compCLM (g.comp f) hgf φ := by
  ext x
  simp

/-- Multiplying the composition with a proper map by a cutoff is the composition with that
cutoff. -/
theorem smulLeftCLM_compCLM (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯)
    (hf : IsProperMap f) (φ : BundleTest J F (Bundle.Trivial N F)) :
    smulLeftCLM χ (compCLM f hf φ) = cutoffCompCLM χ hχ f φ := by
  ext x
  simp

/-! ### Pushforward of functionals with a cutoff -/

section Pushforward

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousConstSMul ℝ W]

/-- The **pushforward with a cutoff** `f_* (χ T)` of a continuous linear functional `T` on the tests
on `M` with values in `F`, along a smooth map `f : M → N` with a compactly supported smooth cutoff
`χ` on `M`: the functional `φ ↦ T (χ · (φ ∘ f))` on the tests on `N`. It is the transpose of the
composition with a cutoff (`TauCeti.BundleTest.cutoffCompCLM`), a continuous linear map for the
topologies of uniform convergence on compact sets of tests. When `χ` is equal to `1` near the
support of `T`, it is the pushforward `f_* T`, independent of such `χ`
(`TauCeti.BundleTest.cutoffPushforwardCLM_congr`). -/
def cutoffPushforwardCLM (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯) :
    (BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W) →L[ℝ]
      BundleTest J F (Bundle.Trivial N F) →L_c[ℝ] W :=
  (cutoffCompCLM χ hχ f).precompCompactConvergenceCLM W

@[simp]
theorem cutoffPushforwardCLM_apply (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, M; J, N⟯) (T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W)
    (φ : BundleTest J F (Bundle.Trivial N F)) :
    cutoffPushforwardCLM χ hχ f T φ = T (cutoffCompCLM χ hχ f φ) :=
  (rfl)

/-- **Independence of the cutoff.** If `T` vanishes on the tests supported in a set `O`, then
cutoffs `χ` and `χ'` that agree off a closed subset of `O` give the same pushforward of `T`. In
particular all cutoffs equal to `1` near the support of `T` give the same pushforward. -/
theorem cutoffPushforwardCLM_congr {χ χ' : C^∞⟮I, M; ℝ⟯} (hχ : HasCompactSupport χ)
    (hχ' : HasCompactSupport χ') (f : C^∞⟮I, M; J, N⟯)
    {T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W} {O : Set M}
    (hT : ∀ s : BundleTest I F (Bundle.Trivial M F), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχχ' : closure {x | χ x ≠ χ' x} ⊆ O) :
    cutoffPushforwardCLM χ hχ f T = cutoffPushforwardCLM χ' hχ' f T := by
  ext φ
  rw [cutoffPushforwardCLM_apply, cutoffPushforwardCLM_apply, ← sub_eq_zero, ← map_sub]
  exact hT _ ((closure_cutoffCompCLM_sub_ne_zero_subset hχ hχ' f φ).trans hχχ')

/-- **The support of a pushforward.** If `T` vanishes on the tests supported in `O`, then
`f_* (χ T)` vanishes on the tests whose support avoids the image under `f` of the part of the
support of `χ` outside `O`. With `O` the complement of the support of `T`, this says that the
support of `f_* (χ T)` lies in `f (supp χ ∩ supp T)`. -/
theorem cutoffPushforwardCLM_apply_eq_zero_of_disjoint {χ : C^∞⟮I, M; ℝ⟯}
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯)
    {T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W} {O : Set M}
    (hT : ∀ s : BundleTest I F (Bundle.Trivial M F), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    {φ : BundleTest J F (Bundle.Trivial N F)}
    (hφ : Disjoint (closure {y | φ y ≠ 0}) (f '' (_root_.tsupport χ \ O))) :
    cutoffPushforwardCLM χ hχ f T φ = 0 := by
  refine hT _ fun x hx ↦ by_contra fun hxO ↦ ?_
  obtain ⟨hxχ, hxφ⟩ := closure_cutoffCompCLM_ne_zero_subset χ hχ f φ hx
  exact hφ.ne_of_mem hxφ (mem_image_of_mem f ⟨hxχ, hxO⟩) rfl

/-- Along the identity, the pushforward with a cutoff `χ` is the product `χ T`. -/
@[simp]
theorem cutoffPushforwardCLM_id_eq_smulLeftDualCLM (χ : C^∞⟮I, M; ℝ⟯)
    (hχ : HasCompactSupport χ) :
    cutoffPushforwardCLM (F := F) (W := W) χ hχ ContMDiffMap.id = smulLeftDualCLM χ := by
  ext T φ
  simp

/-- **The pushforward along the identity.** If `T` vanishes on the tests supported in `O` and the
cutoff `χ` is equal to `1` off a closed subset of `O`, for instance near the support of `T`, then
the pushforward of `T` along the identity is `T`. -/
theorem cutoffPushforwardCLM_id {χ : C^∞⟮I, M; ℝ⟯} (hχ : HasCompactSupport χ)
    {T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W} {O : Set M}
    (hT : ∀ s : BundleTest I F (Bundle.Trivial M F), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχ1 : closure {x | χ x ≠ 1} ⊆ O) :
    cutoffPushforwardCLM χ hχ ContMDiffMap.id T = T := by
  ext φ
  rw [cutoffPushforwardCLM_id_eq_smulLeftDualCLM, smulLeftDualCLM_apply, ← sub_eq_zero,
    ← map_sub]
  refine hT _ ((closure_mono fun x hx ↦ ?_).trans hχ1)
  simp only [mem_ofPred_eq, sub_apply, smulLeftCLM_apply] at hx
  rw [← one_smul ℝ (φ x), smul_smul, mul_one, ← sub_smul, smul_ne_zero_iff] at hx
  exact sub_ne_zero.1 hx.1

/-- **Functoriality of the pushforward**: pushing `T` forward with the cutoff `χ` along `f` and
then with the cutoff `χ'` along `g` is pushing `T` forward with the cutoff `χ · (χ' ∘ f)` along
`g ∘ f`. -/
theorem cutoffPushforwardCLM_cutoffPushforwardCLM (χ' : C^∞⟮J, N; ℝ⟯) (hχ' : HasCompactSupport χ')
    (g : C^∞⟮J, N; K, P⟯) (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯)
    (T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W) :
    cutoffPushforwardCLM χ' hχ' g (cutoffPushforwardCLM χ hχ f T) =
      cutoffPushforwardCLM (χ * χ'.comp f) hχ.mul_right (g.comp f) T := by
  ext φ
  simp only [cutoffPushforwardCLM_apply]
  rw [cutoffCompCLM_cutoffCompCLM]

omit [LocallyCompactSpace E] [IsManifold I ∞ M] [LocallyCompactSpace E'] [IsManifold J ∞ N] in
/-- If `χ'` is equal to `1` near the image under `f` of the part of the support of `χ` outside
`O`, then `χ · (χ' ∘ f)` agrees with `χ` off a closed subset of `O`. -/
private theorem closure_mul_comp_ne_subset {χ : C^∞⟮I, M; ℝ⟯} {χ' : C^∞⟮J, N; ℝ⟯}
    (f : C^∞⟮I, M; J, N⟯) {O : Set M}
    (hχ' : ∀ᶠ y in 𝓝ˢ (f '' (_root_.tsupport χ \ O)), χ' y = 1) :
    closure {x | χ x * χ' (f x) ≠ χ x} ⊆ O := by
  intro x hx
  by_contra hxO
  -- Near a point of `supp χ` outside `O`, the factor `χ' ∘ f` is equal to `1`.
  have hsupp : {y | χ y * χ' (f y) ≠ χ y} ⊆ support χ := fun y hy h0 ↦ hy (by simp [h0])
  have hxχ : x ∈ _root_.tsupport χ := closure_mono hsupp hx
  have h1 : ∀ᶠ y in 𝓝 x, χ' (f y) = 1 :=
    f.contMDiff.continuous.continuousAt.eventually
      ((eventually_nhdsSet_iff_forall.1 hχ') _ (mem_image_of_mem f ⟨hxχ, hxO⟩))
  obtain ⟨y, hy, hy'⟩ := (mem_closure_iff_frequently.1 hx).and_eventually h1 |>.exists
  exact hy (by simp [hy'])

/-- **Functoriality of the pushforward**: `(g ∘ f)_* (χ T) = g_* (χ' f_* (χ T))` when `T` vanishes
on `O` and `χ'` is equal to `1` near the image under `f` of the part of the support of `χ`
outside `O`, for instance near `f (supp χ ∩ supp T)`. -/
theorem cutoffPushforwardCLM_cutoffPushforwardCLM_of_eventually_eq_one {χ' : C^∞⟮J, N; ℝ⟯}
    (hχ' : HasCompactSupport χ') (g : C^∞⟮J, N; K, P⟯) {χ : C^∞⟮I, M; ℝ⟯}
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯)
    {T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W} {O : Set M}
    (hT : ∀ s : BundleTest I F (Bundle.Trivial M F), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχ'1 : ∀ᶠ y in 𝓝ˢ (f '' (_root_.tsupport χ \ O)), χ' y = 1) :
    cutoffPushforwardCLM χ' hχ' g (cutoffPushforwardCLM χ hχ f T) =
      cutoffPushforwardCLM χ hχ (g.comp f) T := by
  rw [cutoffPushforwardCLM_cutoffPushforwardCLM]
  exact cutoffPushforwardCLM_congr _ _ _ hT (closure_mul_comp_ne_subset f hχ'1)

/-- Multiplying `T` by a smooth function `ψ` before pushing it forward with the cutoff `χ` is
pushing `T` forward with the cutoff `ψ χ`. -/
theorem cutoffPushforwardCLM_smulLeftDualCLM (ψ : C^∞⟮I, M; ℝ⟯) (χ : C^∞⟮I, M; ℝ⟯)
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯)
    (T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W) :
    cutoffPushforwardCLM χ hχ f (smulLeftDualCLM ψ T) =
      cutoffPushforwardCLM (ψ * χ) hχ.mul_left f T := by
  ext φ
  simp only [cutoffPushforwardCLM_apply, smulLeftDualCLM_apply]
  congr 1
  ext x
  simp [smul_smul]

/-- **The projection formula**: multiplying the pushforward `f_* (χ T)` by a smooth function `g`
on `N` is pushing `T` forward with the cutoff `χ · (g ∘ f)`. -/
theorem smulLeftDualCLM_cutoffPushforwardCLM (g : C^∞⟮J, N; ℝ⟯) (χ : C^∞⟮I, M; ℝ⟯)
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯)
    (T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W) :
    smulLeftDualCLM g (cutoffPushforwardCLM χ hχ f T) =
      cutoffPushforwardCLM (χ * g.comp f) hχ.mul_right f T := by
  ext φ
  simp only [smulLeftDualCLM_apply, cutoffPushforwardCLM_apply]
  congr 1
  ext x
  simp [smul_smul]

/-! ### Pushforward along proper maps -/

/-- The **pushforward** `f_* T` of a continuous linear functional `T` on the tests on `M` along a
proper smooth map `f : M → N`: the functional `φ ↦ T (φ ∘ f)` on the tests on `N`, the transpose
of the composition with `f` (`TauCeti.BundleTest.compCLM`). It agrees with the pushforward with
a cutoff equal to `1` near the support of `T`
(`TauCeti.BundleTest.cutoffPushforwardCLM_eq_pushforwardCLM`). -/
def pushforwardCLM (f : C^∞⟮I, M; J, N⟯) (hf : IsProperMap f) :
    (BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W) →L[ℝ]
      BundleTest J F (Bundle.Trivial N F) →L_c[ℝ] W :=
  (compCLM f hf).precompCompactConvergenceCLM W

@[simp]
theorem pushforwardCLM_apply (f : C^∞⟮I, M; J, N⟯) (hf : IsProperMap f)
    (T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W) (φ : BundleTest J F (Bundle.Trivial N F)) :
    pushforwardCLM f hf T φ = T (compCLM f hf φ) :=
  (rfl)

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem pushforwardCLM_id
    (hid : IsProperMap (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) := by exact isProperMap_id) :
    pushforwardCLM (F := F) (W := W) ContMDiffMap.id hid = ContinuousLinearMap.id ℝ _ := by
  ext T φ
  simp

/-- **Functoriality of the pushforward along proper maps**: `(g ∘ f)_* T = g_* (f_* T)`. -/
theorem pushforwardCLM_pushforwardCLM (g : C^∞⟮J, N; K, P⟯) (hg : IsProperMap g)
    (f : C^∞⟮I, M; J, N⟯) (hf : IsProperMap f) (T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W)
    (hgf : IsProperMap (g.comp f) := by exact hg.comp hf) :
    pushforwardCLM g hg (pushforwardCLM f hf T) = pushforwardCLM (g.comp f) hgf T := by
  ext φ
  simp only [pushforwardCLM_apply]
  rw [compCLM_compCLM g hg f hf]

/-- Along a proper map, the pushforward with a cutoff `χ` is the pushforward of `χ T`. -/
theorem cutoffPushforwardCLM_eq_pushforwardCLM_smulLeftDualCLM (χ : C^∞⟮I, M; ℝ⟯)
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, M; J, N⟯) (hf : IsProperMap f)
    (T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W) :
    cutoffPushforwardCLM χ hχ f T = pushforwardCLM f hf (smulLeftDualCLM χ T) := by
  ext φ
  rw [cutoffPushforwardCLM_apply, pushforwardCLM_apply, smulLeftDualCLM_apply,
    smulLeftCLM_compCLM χ hχ]

/-- **Agreement with the pushforward along a proper map.** If `T` vanishes on the tests supported
in `O` and the cutoff `χ` is equal to `1` off a closed subset of `O`, for instance near the
support of `T`, then the pushforward of `T` with the cutoff `χ` along a proper map `f` is the
pushforward `f_* T`. -/
theorem cutoffPushforwardCLM_eq_pushforwardCLM {χ : C^∞⟮I, M; ℝ⟯} (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, M; J, N⟯) (hf : IsProperMap f)
    {T : BundleTest I F (Bundle.Trivial M F) →L_c[ℝ] W} {O : Set M}
    (hT : ∀ s : BundleTest I F (Bundle.Trivial M F), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχ1 : closure {x | χ x ≠ 1} ⊆ O) :
    cutoffPushforwardCLM χ hχ f T = pushforwardCLM f hf T := by
  rw [cutoffPushforwardCLM_eq_pushforwardCLM_smulLeftDualCLM χ hχ f hf,
    ← cutoffPushforwardCLM_id_eq_smulLeftDualCLM χ hχ, cutoffPushforwardCLM_id hχ hT hχ1]

/-- The pushforward of a point mass is a point mass at the image point:
`f_* (χ δ_x ℓ) = χ(x) δ_{f x} ℓ`. -/
@[simp]
theorem cutoffPushforwardCLM_delta (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, M; J, N⟯) (x : M) (ℓ : F →L[ℝ] W) :
    cutoffPushforwardCLM χ hχ f (delta (I := I) (V := Bundle.Trivial M F) x ℓ) =
      χ x • delta (I := J) (V := Bundle.Trivial N F) (f x) ℓ := by
  ext φ
  simp

end Pushforward

end TauCeti.BundleTest
