/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial.Topology

/-!
# Pushforward of distribution densities along smooth maps

Let `f : X → Y` be a smooth map of manifolds modelled on finite-dimensional spaces, and let `G` be a
normed space. The tests `TauCeti.BundleTest I G (Bundle.Trivial X G)` on `X` are the compactly
supported smooth maps `X → G`; for `G = ℝ` these are the scalar tests, and the continuous linear
functionals on them are the distribution densities on `X`, which a smooth density `u μ` defines by
`s ↦ ∫ s u dμ` without any choice of measure on `X`. Such functionals are pushed forward along `f`,
as for distributions on open subsets of normed spaces (`Distribution.pushforward`), which this file
follows.

A test `s` on `Y` pulls back to the smooth map `s ∘ f` on `X`, which is not compactly supported in
general. Cut off by a smooth compactly supported function `χ`, it is the test `χ (s ∘ f)`, and this
is a continuous linear map of the test spaces (`TauCeti.BundleTest.cutoffCompCLM`). Its transpose is
the pushforward `T ↦ T (χ (· ∘ f))` of functionals cut off by `χ`
(`TauCeti.BundleTest.cutoffPushforwardCLM`). The cutoff pullback needs only locally compact models.

The supports of functionals also enter through the sets `O` on which they vanish: `T` vanishes on
`O` when `T s = 0` for every test `s` supported in `O`. For the cutoff pushforward `f_* (χ T)` this
gives independence of the cutoff (`TauCeti.BundleTest.cutoffPushforwardCLM_congr`), the support
bound `supp f_* (χ T) ⊆ f (supp χ ∩ supp T)`
(`TauCeti.BundleTest.cutoffPushforwardCLM_apply_eq_zero_of_disjoint`), the identity law
(`TauCeti.BundleTest.cutoffPushforwardCLM_id`), functoriality
(`TauCeti.BundleTest.cutoffPushforwardCLM_cutoffPushforwardCLM` and
`TauCeti.BundleTest.cutoffPushforwardCLM_cutoffPushforwardCLM_of_eventually_eq_one`), the
projection formula `g · f_* (χ T) = f_* ((χ · (g ∘ f)) T)`
(`TauCeti.BundleTest.smulLeftDualCLM_cutoffPushforwardCLM`) and
`f_* (χ δ_x ℓ) = χ(x) δ_{f x} ℓ` (`TauCeti.BundleTest.cutoffPushforwardCLM_delta`). When `f` is
proper, `s ∘ f` is itself a test (`TauCeti.BundleTest.compCLM`), and every functional has a
pushforward `T ↦ T (· ∘ f)` (`TauCeti.BundleTest.pushforwardCLM`), with
`(g ∘ f)_* = g_* ∘ f_*`, support in `f (supp T)` and `f_* δ_x ℓ = δ_{f x} ℓ`; the cutoff
pushforward is this pushforward when `χ` is one near the support of `T`
(`TauCeti.BundleTest.cutoffPushforwardCLM_eq_pushforwardCLM`).

The map `f` is *proper on the support* of `T` (`TauCeti.BundleTest.IsProperOnSupport`) if the part
`supp T ∩ f⁻¹(K)` of the support of `T` (`TauCeti.BundleTest.dsupport`) over every compact
`K ⊆ Y` is compact; this holds for every continuous `f` when `T` has compact support, and for every
`T` when `f` is proper. Then `T` has a **pushforward** `f_* T` (`TauCeti.BundleTest.pushforward`),
the functional on the tests on `Y` given by

`(f_* T) s = T (χ (s ∘ f))`,

where `χ` is equal to one near `supp T ∩ f⁻¹(supp s)`. It is characterized by `(f_* T) s = T t` for
every test `t` on `X` which agrees with `s ∘ f` near each point of the support of `T`
(`TauCeti.BundleTest.pushforward_apply_of_eventuallyEq`), so it does not depend on the cutoffs. The
cutoff depends on the support of `s`, so `f_* T` is defined test by test; it is continuous because
one cutoff serves all the tests supported in a fixed compact set.

## Main declarations

* `TauCeti.BundleTest.cutoffCompCLM`: the cutoff pullback `s ↦ χ (s ∘ f)` of tests.
* `TauCeti.BundleTest.cutoffPushforwardCLM`: its transpose, the pushforward of functionals cut
  off by `χ`.
* `TauCeti.BundleTest.compCLM`, `TauCeti.BundleTest.pushforwardCLM`: the pullback of tests
  along a proper smooth map and its transpose.
* `TauCeti.BundleTest.IsProperOnSupport`: `f` is proper on the support of `T`, with
  `TauCeti.BundleTest.isProperOnSupport_of_isCompact_dsupport` and
  `TauCeti.BundleTest.isProperOnSupport_of_isCompact_preimage`.
* `TauCeti.BundleTest.pushforward`: the pushforward `f_* T`, with its values
  `TauCeti.BundleTest.pushforward_apply_of_eventuallyEq` on tests supplied by
  `TauCeti.BundleTest.IsProperOnSupport.exists_forall_eventually_eq`, and
  `TauCeti.BundleTest.pushforward_apply_eq_cutoffCompCLM`, and
  `TauCeti.BundleTest.pushforward_eq_cutoffPushforwardCLM` for compactly supported `T`.
* `TauCeti.BundleTest.dsupport_cutoffPushforwardCLM_subset`: `supp f_* (χ T) ⊆ f (supp χ ∩ supp T)`.
* `TauCeti.BundleTest.dsupport_pushforward_subset`: `supp (f_* T) ⊆ f (supp T)`, and
  `TauCeti.BundleTest.IsProperOnSupport.pushforward`.
* `TauCeti.BundleTest.pushforward_zero`, `TauCeti.BundleTest.pushforward_add`,
  `TauCeti.BundleTest.pushforward_smul`: linearity in `T`.
* `TauCeti.BundleTest.pushforward_id`, `TauCeti.BundleTest.pushforward_pushforward`:
  functoriality, `g_* (f_* T) = (g ∘ f)_* T`.
* `TauCeti.BundleTest.pushforward_delta`: `f_* δ_x ℓ = δ_{f x} ℓ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.3 (distributions and densities on manifolds) and §8.2 (the pushforward of a
  distribution along a map proper on its support, before Theorem 8.2.13).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, Studia Math. 232 (2016), arXiv:1409.7662v2, §3
  (pushforward along maps proper on the support).
-/

public noncomputable section

open Bundle Set Filter Function TopologicalSpace ContMDiffSection
open scoped ContDiff Manifold Topology CompactConvergenceCLM

namespace TauCeti.BundleTest

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  {E' H' Y : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Maps proper on the support of a functional -/

section IsProperOnSupport

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {W : Type*} [Zero W]
  {T : BundleTest I F V → W} {f : X → Y}

variable (T f) in
/-- A map `f : X → Y` is **proper on the support** of a map `T` on bundle tests if the part
`supp T ∩ f⁻¹(K)` of the support of `T` over every compact `K ⊆ Y` is compact. This is the
condition for the pushforward `f_* T` (`TauCeti.BundleTest.pushforward`). -/
def IsProperOnSupport : Prop :=
  ∀ K : Set Y, IsCompact K → IsCompact (dsupport T ∩ f ⁻¹' K)

/-- Unfolds `TauCeti.BundleTest.IsProperOnSupport`. -/
theorem isProperOnSupport_iff :
    IsProperOnSupport T f ↔ ∀ K : Set Y, IsCompact K → IsCompact (dsupport T ∩ f ⁻¹' K) :=
  Iff.rfl

/-- If `f` is proper on the support of `T`, the part of the support of `T` over a compact set is
compact. -/
theorem IsProperOnSupport.isCompact (hT : IsProperOnSupport T f) {K : Set Y} (hK : IsCompact K) :
    IsCompact (dsupport T ∩ f ⁻¹' K) :=
  hT K hK

/-- A proper map is proper on the support of every map on bundle tests. -/
theorem isProperOnSupport_of_isCompact_preimage (T : BundleTest I F V → W)
    (hf : ∀ K : Set Y, IsCompact K → IsCompact (f ⁻¹' K)) : IsProperOnSupport T f :=
  fun K hK ↦ (hf K hK).inter_left (isClosed_dsupport T)

/-- **Compactly supported maps.** Every continuous map is proper on a support which is compact. -/
theorem isProperOnSupport_of_isCompact_dsupport [T2Space Y] (hT : IsCompact (dsupport T))
    (hf : Continuous f) : IsProperOnSupport T f :=
  fun _ hK ↦ hT.inter_right (hK.isClosed.preimage hf)

/-- If `f` is proper on the support of `T`, it is proper on the support of every map whose
support lies in that of `T`. -/
theorem IsProperOnSupport.mono {W' : Type*} [Zero W'] {T' : BundleTest I F V → W'}
    (hT : IsProperOnSupport T f) (h : dsupport T' ⊆ dsupport T) : IsProperOnSupport T' f :=
  fun K hK ↦ by
    have hK' : dsupport T' ∩ f ⁻¹' K = dsupport T ∩ f ⁻¹' K ∩ dsupport T' := by
      ext x
      exact ⟨fun hx ↦ ⟨⟨h hx.1, hx.2⟩, hx.1⟩, fun hx ↦ ⟨hx.2, hx.1.2⟩⟩
    rw [hK']
    exact (hT K hK).inter_right (isClosed_dsupport T')

/-- Every map is proper on the support of the zero map. -/
theorem isProperOnSupport_zero : IsProperOnSupport (0 : BundleTest I F V → W) f :=
  fun _ _ ↦ by simp

/-- If `f` is proper on the supports of `T` and `T'`, it is proper on the support of `T + T'`. -/
theorem IsProperOnSupport.add {W : Type*} [AddZeroClass W] {T T' : BundleTest I F V → W}
    (hT : IsProperOnSupport T f) (hT' : IsProperOnSupport T' f) :
    IsProperOnSupport (T + T') f := fun K hK ↦ by
  -- Over `K`, the support of `T + T'` lies in the union of those of `T` and `T'`.
  have h : dsupport (T + T') ∩ f ⁻¹' K =
      (dsupport T ∩ f ⁻¹' K ∪ dsupport T' ∩ f ⁻¹' K) ∩ dsupport (T + T') := by
    ext x
    refine ⟨fun hx ↦ ⟨?_, hx.1⟩, fun hx ↦ ⟨hx.2, hx.1.elim (·.2) (·.2)⟩⟩
    exact (dsupport_add_subset T T' hx.1).imp (⟨·, hx.2⟩) (⟨·, hx.2⟩)
  rw [h]
  exact ((hT K hK).union (hT' K hK)).inter_right (isClosed_dsupport _)

/-- If `f` is proper on the support of `T`, it is proper on the support of `c • T`. -/
theorem IsProperOnSupport.smul {R : Type*} [SMulZeroClass R W] (hT : IsProperOnSupport T f)
    (c : R) : IsProperOnSupport (c • T) f :=
  hT.mono (dsupport_smul_subset c T)

/-- The identity is proper on the support of every map on bundle tests. -/
theorem isProperOnSupport_id (T : BundleTest I F V → W) : IsProperOnSupport T id :=
  fun _ hK ↦ hK.inter_left (isClosed_dsupport T)

end IsProperOnSupport

/-- Near a point mapped off the support of a test `s` on `Y`, the composite `s ∘ f` vanishes. -/
private theorem eventually_apply_comp_eq_zero {f : X → Y} (hf : Continuous f)
    (s : BundleTest J G (Trivial Y G)) {x : X} (hfx : f x ∉ closure {y | s y ≠ 0}) :
    ∀ᶠ z in 𝓝 x, s (f z) = 0 :=
  eventually_of_mem (hf.continuousAt.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hfx))
    fun _ hz ↦ Bundle.apply_eq_zero_of_notMem_closure hz

section Cutoff

variable [LocallyCompactSpace E] [IsManifold I ∞ X] [LocallyCompactSpace E'] [IsManifold J ∞ Y]
  {E'' H'' Z : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [LocallyCompactSpace E'']
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold K ∞ Z]

/-! ### Pulling tests back along a smooth map -/

section CutoffComp

attribute [local instance] ContMDiffMap.manifoldWeakWhitneyTopology

/-- The linear map underlying `TauCeti.BundleTest.cutoffCompCLM`. -/
private def cutoffCompLinearMap (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) : BundleTest J G (Trivial Y G) →ₗ[ℝ] BundleTest I G (Trivial X G) where
  toFun s := ofCompactlySupported I G (Trivial X G)
    ⟨χ • trivialEquiv.symm
      ((trivialEquiv ((ofCompactlySupported J G (Trivial Y G)).symm s).val).comp f),
      smul_function_mem_compactlySupported_of_hasCompactSupport χ hχ _⟩
  map_add' s t := by
    ext x
    simp [smul_add]
  map_smul' a s := by
    ext x
    simp [smul_comm (χ x) a]

/-- The **pullback of tests along a smooth map `f : X → Y`, cut off by `χ`**: a test `s` on `Y`,
a compactly supported smooth section of the trivial bundle with fibre `G`, is sent to the test
`x ↦ χ x • s (f x)` on `X`, for a smooth compactly supported function `χ` on `X`. It is a
continuous linear map for the test topologies. Its transpose is the pushforward of a functional
cut off by `χ` (`TauCeti.BundleTest.cutoffPushforwardCLM`). -/
def cutoffCompCLM (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯) :
    BundleTest J G (Trivial Y G) →L[ℝ] BundleTest I G (Trivial X G) where
  toLinearMap := cutoffCompLinearMap χ hχ f
  cont := by
    let := frameTopology (I := J) (n := ∞) (fun y : Y ↦ trivializationAt G (Trivial Y G) y)
      (fun y ↦ ⟨_, (trivializationAt G (Trivial Y G) y).open_baseSet⟩) fun _ ↦ subset_rfl
    let := frameTopology (I := I) (n := ∞) (fun x : X ↦ trivializationAt G (Trivial X G) x)
      (fun x ↦ ⟨_, (trivializationAt G (Trivial X G) x).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp _).2 fun K ↦ ?_
    -- On sections, the map is `s ↦ χ • (s ∘ f)`, continuous for the frame topologies.
    have hP : Continuous fun s : Cₛ^∞⟮J; G, Trivial Y G⟯ ↦
        χ • (trivialEquiv.symm ((trivialEquiv s).comp f) : Cₛ^∞⟮I; G, Trivial X G⟯) :=
      (continuous_smul_function_frameTopology _ _ _ χ).comp <|
        continuous_trivialEquiv_symm_frameTopology.comp <|
          ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp <|
            continuous_trivialEquiv_frameTopology.prodMk continuous_const
    -- It sends the stage of tests supported in `K` into the stage of sections supported in
    -- `tsupport χ`.
    refine ((continuous_ofSupportedIn ⟨tsupport χ, hχ⟩).comp
      ((hP.comp continuous_subtypeVal).subtype_mk fun s ↦ ?_)).congr fun s ↦ ?_
    · exact mem_supportedIn.2 ((tsupport_smul_function_subset _ _).trans inter_subset_left)
    · ext x
      simp [cutoffCompLinearMap, ofSupportedIn_apply]

@[simp]
theorem cutoffCompCLM_apply (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (s : BundleTest J G (Trivial Y G)) (x : X) : cutoffCompCLM χ hχ f s x = χ x • s (f x) := by
  simp [cutoffCompCLM, cutoffCompLinearMap, ContMDiffSection.smul_apply]

/-- The cutoff pullback of a test `s` agrees with `s ∘ f` near every point of a set `S`, when the
cutoff is one near the points of `S` mapped into the support of `s`. -/
theorem cutoffCompCLM_eventuallyEq {χ : C^∞⟮I, X; ℝ⟯} (hχc : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (s : BundleTest J G (Trivial Y G)) {S : Set X}
    (hχ : ∀ᶠ x in 𝓝ˢ (S ∩ f ⁻¹' closure {y | s y ≠ 0}), χ x = 1) {x : X} (hx : x ∈ S) :
    ∀ᶠ z in 𝓝 x, cutoffCompCLM χ hχc f s z = s (f z) := by
  by_cases hfx : f x ∈ closure {y | s y ≠ 0}
  · filter_upwards [hχ.filter_mono (nhds_le_nhdsSet
      (show x ∈ S ∩ f ⁻¹' closure {y | s y ≠ 0} from ⟨hx, hfx⟩))] with z hz
    simp [hz]
  · -- Near `x`, `f` takes values off the support of `s`, where `s` vanishes.
    filter_upwards [eventually_apply_comp_eq_zero f.contMDiff.continuous s hfx] with z hz
    simp [hz]

/-- Along the identity, the composition with a cutoff is multiplication by the cutoff. -/
@[simp]
theorem cutoffCompCLM_id (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) :
    cutoffCompCLM (G := G) χ hχ ContMDiffMap.id = smulLeftCLM χ := by
  ext φ x
  simp

/-- Compositions with cutoffs compose: composing with `g` and the cutoff `χ'` and then with `f`
and the cutoff `χ` is composing with `g ∘ f` and the cutoff `χ · (χ' ∘ f)`. -/
theorem cutoffCompCLM_cutoffCompCLM (χ' : C^∞⟮J, Y; ℝ⟯) (hχ' : HasCompactSupport χ')
    (g : C^∞⟮J, Y; K, Z⟯) (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (φ : BundleTest K G (Bundle.Trivial Z G)) :
    cutoffCompCLM χ hχ f (cutoffCompCLM χ' hχ' g φ) =
      cutoffCompCLM (χ * χ'.comp f) hχ.mul_right (g.comp f) φ := by
  ext x
  simp [smul_smul]

/-- The composition of `φ` with a cutoff is supported in the part of the support of `χ` that `f`
maps into the support of `φ`. -/
theorem closure_cutoffCompCLM_ne_zero_subset (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (φ : BundleTest J G (Bundle.Trivial Y G)) :
    closure {x | cutoffCompCLM χ hχ f φ x ≠ 0} ⊆
      _root_.tsupport χ ∩ f ⁻¹' closure {y | φ y ≠ 0} :=
  closure_minimal (fun x hx ↦ by
      simp only [mem_ofPred_eq, cutoffCompCLM_apply, smul_ne_zero_iff] at hx
      exact ⟨subset_tsupport _ hx.1, subset_closure hx.2⟩)
    ((_root_.isClosed_tsupport _).inter (isClosed_closure.preimage f.contMDiff.continuous))

/-- Compositions with two cutoffs differ by a test supported where the cutoffs differ. -/
theorem closure_cutoffCompCLM_sub_ne_zero_subset {χ χ' : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) (hχ' : HasCompactSupport χ') (f : C^∞⟮I, X; J, Y⟯)
    (φ : BundleTest J G (Bundle.Trivial Y G)) :
    closure {x | (cutoffCompCLM χ hχ f φ - cutoffCompCLM χ' hχ' f φ) x ≠ 0} ⊆
      closure {x | χ x ≠ χ' x} :=
  closure_mono fun x hx ↦ by
    simp only [mem_ofPred_eq, sub_apply, cutoffCompCLM_apply, ← sub_smul,
      smul_ne_zero_iff] at hx
    exact sub_ne_zero.1 hx.1

end CutoffComp

/-! ### Composition of tests with a proper map -/

/-- The composition `φ ↦ φ ∘ f` of tests with a proper smooth map, as a linear map. -/
private def compLinearMap (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f) :
    BundleTest J G (Bundle.Trivial Y G) →ₗ[ℝ] BundleTest I G (Bundle.Trivial X G) where
  toFun φ := ofCompactlySupported I G _
    ⟨trivialPullback f ((ofCompactlySupported J G _).symm φ).val,
      mem_compactlySupported.2 <| (hf.isCompact_preimage (mem_compactlySupported.1
        ((ofCompactlySupported J G _).symm φ).property)).of_isClosed_subset
          (ContMDiffSection.isClosed_tsupport _) (tsupport_trivialPullback_subset f _)⟩
  map_add' φ ψ := by ext x; simp
  map_smul' a φ := by ext x; simp

/-- The **composition** `φ ↦ φ ∘ f` of tests on `Y` with a smooth map `f : X → Y` that is proper,
so that `φ ∘ f` is again compactly supported. It is a continuous linear map for the test
topologies. -/
def compCLM (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f) :
    BundleTest J G (Bundle.Trivial Y G) →L[ℝ] BundleTest I G (Bundle.Trivial X G) where
  toLinearMap := compLinearMap f hf
  cont := by
    let := frameTopology (I := J) (n := ∞)
      (fun y : Y ↦ trivializationAt G (Bundle.Trivial Y G) y)
      (fun y ↦ ⟨_, (trivializationAt G (Bundle.Trivial Y G) y).open_baseSet⟩) fun _ ↦ subset_rfl
    let := frameTopology (I := I) (n := ∞)
      (fun x : X ↦ trivializationAt G (Bundle.Trivial X G) x)
      (fun x ↦ ⟨_, (trivializationAt G (Bundle.Trivial X G) x).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp (compLinearMap f hf)).2 fun L ↦ ?_
    -- The composition maps the stage of the sections supported in `L` into the stage of the
    -- sections supported in the compact set `f⁻¹ L`.
    let L' : Compacts X := ⟨f ⁻¹' L, hf.isCompact_preimage L.isCompact⟩
    refine ((continuous_ofSupportedIn (F := G) L').comp
      (((continuous_trivialPullback f).comp continuous_subtypeVal).subtype_mk
        fun s ↦ mem_supportedIn.2 <| (tsupport_trivialPullback_subset f _).trans
          (preimage_mono (mem_supportedIn.1 s.property)))).congr fun s ↦ ?_
    simp [compLinearMap, Subtype.ext_iff]

@[simp]
theorem compCLM_apply (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f)
    (φ : BundleTest J G (Bundle.Trivial Y G)) (x : X) :
    compCLM f hf φ x = φ (f x) := by
  simp [compCLM, compLinearMap]

/-- Composition with the identity is the identity. -/
@[simp]
theorem compCLM_id
    (hid : IsProperMap (ContMDiffMap.id : C^∞⟮I, X; I, X⟯) := by exact isProperMap_id) :
    compCLM (G := G) ContMDiffMap.id hid = ContinuousLinearMap.id ℝ _ := by
  ext φ x
  simp

/-- Compositions with proper maps compose. -/
theorem compCLM_compCLM (g : C^∞⟮J, Y; K, Z⟯) (hg : IsProperMap g) (f : C^∞⟮I, X; J, Y⟯)
    (hf : IsProperMap f) (φ : BundleTest K G (Bundle.Trivial Z G))
    (hgf : IsProperMap (g.comp f) := by exact hg.comp hf) :
    compCLM f hf (compCLM g hg φ) = compCLM (g.comp f) hgf φ := by
  ext x
  simp

/-- The composition of `φ` with a proper map is supported in the preimage of the support
of `φ`. -/
theorem closure_compCLM_ne_zero_subset (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f)
    (φ : BundleTest J G (Bundle.Trivial Y G)) :
    closure {x | compCLM f hf φ x ≠ 0} ⊆ f ⁻¹' closure {y | φ y ≠ 0} :=
  closure_minimal (fun x hx ↦ by
      simp only [mem_ofPred_eq, compCLM_apply] at hx
      exact subset_closure hx)
    (isClosed_closure.preimage f.contMDiff.continuous)

/-- Multiplying the composition with a proper map by a cutoff is the composition with that
cutoff. -/
theorem smulLeftCLM_compCLM (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (hf : IsProperMap f) (φ : BundleTest J G (Bundle.Trivial Y G)) :
    smulLeftCLM χ (compCLM f hf φ) = cutoffCompCLM χ hχ f φ := by
  ext x
  simp

/-! ### Pushforward of functionals with a cutoff -/

section Dual

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousConstSMul ℝ W]

/-- The **pushforward of a functional cut off by `χ`**: the transpose `T ↦ T ∘ (χ f^*)` of the
cutoff pullback of tests (`TauCeti.BundleTest.cutoffCompCLM`), a continuous linear map for the
topologies of uniform convergence on compact sets of tests. For `T` compactly supported and `χ`
equal to one near its support, it is the pushforward `f_* T`
(`TauCeti.BundleTest.pushforward_eq_cutoffPushforwardCLM`). -/
def cutoffPushforwardCLM (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯) :
    (BundleTest I G (Trivial X G) →L_c[ℝ] W) →L[ℝ] BundleTest J G (Trivial Y G) →L_c[ℝ] W :=
  (cutoffCompCLM χ hχ f).precompCompactConvergenceCLM W

@[simp]
theorem cutoffPushforwardCLM_apply (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (T : BundleTest I G (Trivial X G) →L_c[ℝ] W)
    (s : BundleTest J G (Trivial Y G)) :
    cutoffPushforwardCLM χ hχ f T s = T (cutoffCompCLM χ hχ f s) :=
  (rfl)

/-- **Independence of the cutoff.** If `T` vanishes on the tests supported in a set `O`, then
cutoffs `χ` and `χ'` that agree off a closed subset of `O` give the same pushforward of `T`. In
particular all cutoffs equal to `1` near the support of `T` give the same pushforward. -/
theorem cutoffPushforwardCLM_congr {χ χ' : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ)
    (hχ' : HasCompactSupport χ') (f : C^∞⟮I, X; J, Y⟯)
    {T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W} {O : Set X}
    (hT : ∀ s : BundleTest I G (Bundle.Trivial X G), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχχ' : closure {x | χ x ≠ χ' x} ⊆ O) :
    cutoffPushforwardCLM χ hχ f T = cutoffPushforwardCLM χ' hχ' f T := by
  ext φ
  rw [cutoffPushforwardCLM_apply, cutoffPushforwardCLM_apply, ← sub_eq_zero, ← map_sub]
  exact hT _ ((closure_cutoffCompCLM_sub_ne_zero_subset hχ hχ' f φ).trans hχχ')

/-- **The support of a pushforward.** If `T` vanishes on the tests supported in `O`, then
`f_* (χ T)` vanishes on the tests whose support avoids the image under `f` of the part of the
support of `χ` outside `O`. With `O` the complement of the support of `T`, this says that the
support of `f_* (χ T)` lies in `f (supp χ ∩ supp T)`. -/
theorem cutoffPushforwardCLM_apply_eq_zero_of_disjoint {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    {T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W} {O : Set X}
    (hT : ∀ s : BundleTest I G (Bundle.Trivial X G), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    {φ : BundleTest J G (Bundle.Trivial Y G)}
    (hφ : Disjoint (closure {y | φ y ≠ 0}) (f '' (_root_.tsupport χ \ O))) :
    cutoffPushforwardCLM χ hχ f T φ = 0 := by
  refine hT _ fun x hx ↦ by_contra fun hxO ↦ ?_
  obtain ⟨hxχ, hxφ⟩ := closure_cutoffCompCLM_ne_zero_subset χ hχ f φ hx
  exact hφ.ne_of_mem hxφ (mem_image_of_mem f ⟨hxχ, hxO⟩) rfl

/-- Along the identity, the pushforward with a cutoff `χ` is the product `χ T`. -/
@[simp]
theorem cutoffPushforwardCLM_id_eq_smulLeftDualCLM (χ : C^∞⟮I, X; ℝ⟯)
    (hχ : HasCompactSupport χ) :
    cutoffPushforwardCLM (G := G) (W := W) χ hχ ContMDiffMap.id = smulLeftDualCLM χ := by
  ext T φ
  simp

/-- **The pushforward along the identity.** If `T` vanishes on the tests supported in `O` and the
cutoff `χ` is equal to `1` off a closed subset of `O`, for instance near the support of `T`, then
the pushforward of `T` along the identity is `T`. -/
theorem cutoffPushforwardCLM_id {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ)
    {T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W} {O : Set X}
    (hT : ∀ s : BundleTest I G (Bundle.Trivial X G), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχ1 : closure {x | χ x ≠ 1} ⊆ O) :
    cutoffPushforwardCLM χ hχ ContMDiffMap.id T = T := by
  ext φ
  rw [cutoffPushforwardCLM_id_eq_smulLeftDualCLM, smulLeftDualCLM_apply, ← sub_eq_zero,
    ← map_sub]
  refine hT _ ((closure_mono fun x hx ↦ ?_).trans hχ1)
  simp only [mem_ofPred_eq, sub_apply, smulLeftCLM_apply] at hx
  have h : (χ x - 1) • φ x ≠ 0 := by rwa [sub_smul, one_smul]
  exact sub_ne_zero.1 (smul_ne_zero_iff.1 h).1

/-- **Functoriality of the pushforward**: pushing `T` forward with the cutoff `χ` along `f` and
then with the cutoff `χ'` along `g` is pushing `T` forward with the cutoff `χ · (χ' ∘ f)` along
`g ∘ f`. -/
theorem cutoffPushforwardCLM_cutoffPushforwardCLM (χ' : C^∞⟮J, Y; ℝ⟯) (hχ' : HasCompactSupport χ')
    (g : C^∞⟮J, Y; K, Z⟯) (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W) :
    cutoffPushforwardCLM χ' hχ' g (cutoffPushforwardCLM χ hχ f T) =
      cutoffPushforwardCLM (χ * χ'.comp f) hχ.mul_right (g.comp f) T := by
  ext φ
  simp only [cutoffPushforwardCLM_apply]
  rw [cutoffCompCLM_cutoffCompCLM]

omit [LocallyCompactSpace E] [IsManifold I ∞ X] [LocallyCompactSpace E'] [IsManifold J ∞ Y] in
/-- If `χ'` is equal to `1` near the image under `f` of the part of the support of `χ` outside
`O`, then `χ · (χ' ∘ f)` agrees with `χ` off a closed subset of `O`. -/
private theorem closure_mul_comp_ne_subset {χ : C^∞⟮I, X; ℝ⟯} {χ' : C^∞⟮J, Y; ℝ⟯}
    (f : C^∞⟮I, X; J, Y⟯) {O : Set X}
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
theorem cutoffPushforwardCLM_cutoffPushforwardCLM_of_eventually_eq_one {χ' : C^∞⟮J, Y; ℝ⟯}
    (hχ' : HasCompactSupport χ') (g : C^∞⟮J, Y; K, Z⟯) {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    {T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W} {O : Set X}
    (hT : ∀ s : BundleTest I G (Bundle.Trivial X G), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχ'1 : ∀ᶠ y in 𝓝ˢ (f '' (_root_.tsupport χ \ O)), χ' y = 1) :
    cutoffPushforwardCLM χ' hχ' g (cutoffPushforwardCLM χ hχ f T) =
      cutoffPushforwardCLM χ hχ (g.comp f) T := by
  rw [cutoffPushforwardCLM_cutoffPushforwardCLM]
  exact cutoffPushforwardCLM_congr _ _ _ hT (closure_mul_comp_ne_subset f hχ'1)

/-- Multiplying `T` by a smooth function `ψ` before pushing it forward with the cutoff `χ` is
pushing `T` forward with the cutoff `ψ χ`. -/
theorem cutoffPushforwardCLM_smulLeftDualCLM (ψ : C^∞⟮I, X; ℝ⟯) (χ : C^∞⟮I, X; ℝ⟯)
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W) :
    cutoffPushforwardCLM χ hχ f (smulLeftDualCLM ψ T) =
      cutoffPushforwardCLM (ψ * χ) hχ.mul_left f T := by
  ext φ
  simp only [cutoffPushforwardCLM_apply, smulLeftDualCLM_apply]
  congr 1
  ext x
  simp [smul_smul]

/-- **The projection formula**: multiplying the pushforward `f_* (χ T)` by a smooth function `g`
on `Y` is pushing `T` forward with the cutoff `χ · (g ∘ f)`. -/
theorem smulLeftDualCLM_cutoffPushforwardCLM (g : C^∞⟮J, Y; ℝ⟯) (χ : C^∞⟮I, X; ℝ⟯)
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W) :
    smulLeftDualCLM g (cutoffPushforwardCLM χ hχ f T) =
      cutoffPushforwardCLM (χ * g.comp f) hχ.mul_right f T := by
  ext φ
  simp only [smulLeftDualCLM_apply, cutoffPushforwardCLM_apply]
  congr 1
  ext x
  simp [smul_smul]

/-! ### Pushforward along proper maps -/

/-- The **pushforward** `f_* T` of a continuous linear functional `T` on the tests on `X` along a
proper smooth map `f : X → Y`: the functional `φ ↦ T (φ ∘ f)` on the tests on `Y`, the transpose
of the composition with `f` (`TauCeti.BundleTest.compCLM`). It agrees with the pushforward with
a cutoff equal to `1` near the support of `T`
(`TauCeti.BundleTest.cutoffPushforwardCLM_eq_pushforwardCLM`). -/
def pushforwardCLM (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f) :
    (BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W) →L[ℝ]
      BundleTest J G (Bundle.Trivial Y G) →L_c[ℝ] W :=
  (compCLM f hf).precompCompactConvergenceCLM W

@[simp]
theorem pushforwardCLM_apply (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f)
    (T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W) (φ : BundleTest J G (Bundle.Trivial Y G)) :
    pushforwardCLM f hf T φ = T (compCLM f hf φ) :=
  (rfl)

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem pushforwardCLM_id
    (hid : IsProperMap (ContMDiffMap.id : C^∞⟮I, X; I, X⟯) := by exact isProperMap_id) :
    pushforwardCLM (G := G) (W := W) ContMDiffMap.id hid = ContinuousLinearMap.id ℝ _ := by
  ext T φ
  simp

/-- **Functoriality of the pushforward along proper maps**: `(g ∘ f)_* T = g_* (f_* T)`. -/
theorem pushforwardCLM_pushforwardCLM (g : C^∞⟮J, Y; K, Z⟯) (hg : IsProperMap g)
    (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f) (T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W)
    (hgf : IsProperMap (g.comp f) := by exact hg.comp hf) :
    pushforwardCLM g hg (pushforwardCLM f hf T) = pushforwardCLM (g.comp f) hgf T := by
  ext φ
  simp only [pushforwardCLM_apply]
  rw [compCLM_compCLM g hg f hf]

/-- **The support of a pushforward along a proper map.** If `T` vanishes on the tests supported
in `O`, then `f_* T` vanishes on the tests whose support avoids the image under `f` of the
complement of `O`. With `O` the complement of the support of `T`, this says that the support of
`f_* T` lies in `f (supp T)`. -/
theorem pushforwardCLM_apply_eq_zero_of_disjoint (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f)
    {T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W} {O : Set X}
    (hT : ∀ s : BundleTest I G (Bundle.Trivial X G), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    {φ : BundleTest J G (Bundle.Trivial Y G)} (hφ : Disjoint (closure {y | φ y ≠ 0}) (f '' Oᶜ)) :
    pushforwardCLM f hf T φ = 0 :=
  hT _ fun _ hx ↦ by_contra fun hxO ↦
    hφ.ne_of_mem (closure_compCLM_ne_zero_subset f hf φ hx) (mem_image_of_mem f hxO) rfl

/-- Along a proper map, the pushforward with a cutoff `χ` is the pushforward of `χ T`. -/
theorem cutoffPushforwardCLM_eq_pushforwardCLM_smulLeftDualCLM (χ : C^∞⟮I, X; ℝ⟯)
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f)
    (T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W) :
    cutoffPushforwardCLM χ hχ f T = pushforwardCLM f hf (smulLeftDualCLM χ T) := by
  ext φ
  rw [cutoffPushforwardCLM_apply, pushforwardCLM_apply, smulLeftDualCLM_apply,
    smulLeftCLM_compCLM χ hχ]

/-- **Agreement with the pushforward along a proper map.** If `T` vanishes on the tests supported
in `O` and the cutoff `χ` is equal to `1` off a closed subset of `O`, for instance near the
support of `T`, then the pushforward of `T` with the cutoff `χ` along a proper map `f` is the
pushforward `f_* T`. -/
theorem cutoffPushforwardCLM_eq_pushforwardCLM {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f)
    {T : BundleTest I G (Bundle.Trivial X G) →L_c[ℝ] W} {O : Set X}
    (hT : ∀ s : BundleTest I G (Bundle.Trivial X G), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχ1 : closure {x | χ x ≠ 1} ⊆ O) :
    cutoffPushforwardCLM χ hχ f T = pushforwardCLM f hf T := by
  rw [cutoffPushforwardCLM_eq_pushforwardCLM_smulLeftDualCLM χ hχ f hf,
    ← cutoffPushforwardCLM_id_eq_smulLeftDualCLM χ hχ, cutoffPushforwardCLM_id hχ hT hχ1]

/-- The pushforward of a point mass is a point mass at the image point:
`f_* (χ δ_x ℓ) = χ(x) δ_{f x} ℓ`. -/
@[simp]
theorem cutoffPushforwardCLM_delta (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (x : X) (ℓ : G →L[ℝ] W) :
    cutoffPushforwardCLM χ hχ f (delta (I := I) (V := Bundle.Trivial X G) x ℓ) =
      χ x • delta (I := J) (V := Bundle.Trivial Y G) (f x) ℓ := by
  ext φ
  simp

/-- The pushforward of a point mass along a proper map is the point mass at the image point:
`f_* δ_x ℓ = δ_{f x} ℓ`. -/
@[simp]
theorem pushforwardCLM_delta (f : C^∞⟮I, X; J, Y⟯) (hf : IsProperMap f) (x : X)
    (ℓ : G →L[ℝ] W) :
    pushforwardCLM f hf (delta (I := I) (V := Bundle.Trivial X G) x ℓ) =
      delta (I := J) (V := Bundle.Trivial Y G) (f x) ℓ := by
  ext φ
  simp


end Dual

end Cutoff

variable [FiniteDimensional ℝ E] [IsManifold I ∞ X] [FiniteDimensional ℝ E'] [IsManifold J ∞ Y]

/-! ### The pushforward -/

section Pushforward

variable [T2Space X] {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  {T : BundleTest I G (Trivial X G) →L_c[ℝ] W} {f : C^∞⟮I, X; J, Y⟯}

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ Y] in
/-- A smooth compactly supported function equal to one near a compact set. -/
private theorem exists_contMDiffMap_eventually_eq_one {L : Set X} (hL : IsCompact L) :
    ∃ χ : C^∞⟮I, X; ℝ⟯, HasCompactSupport χ ∧ ∀ᶠ x in 𝓝ˢ L, χ x = 1 := by
  obtain ⟨χ, hχ, h1, hc, -, -⟩ :=
    hL.exists_contMDiff_one_nhds_tsupport_subset I isOpen_univ (subset_univ _)
  exact ⟨⟨χ, hχ⟩, hc, h1⟩

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ Y] in
/-- A smooth compactly supported function equal to one near the part of the support of `T` over a
compact set `K`. -/
private theorem IsProperOnSupport.exists_eventually_eq_one (hT : IsProperOnSupport ⇑T f)
    {K : Set Y} (hK : IsCompact K) :
    ∃ χ : C^∞⟮I, X; ℝ⟯, HasCompactSupport χ ∧ ∀ᶠ x in 𝓝ˢ (dsupport ⇑T ∩ f ⁻¹' K), χ x = 1 :=
  exists_contMDiffMap_eventually_eq_one (hT K hK)

/-- The pairing of `T` with a cutoff pullback of `s` is its pairing with any test agreeing with
`s ∘ f` near each point of the support of `T`. -/
private theorem map_cutoffCompCLM_eq {s : BundleTest J G (Trivial Y G)} {χ : C^∞⟮I, X; ℝ⟯}
    (hχc : HasCompactSupport χ)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport ⇑T ∩ f ⁻¹' closure {y | s y ≠ 0}), χ x = 1)
    {t : BundleTest I G (Trivial X G)} (ht : ∀ x ∈ dsupport ⇑T, ∀ᶠ z in 𝓝 x, t z = s (f z)) :
    T (cutoffCompCLM χ hχc f s) = T t :=
  map_eq_map_of_eventuallyEq T <| eventually_nhdsSet_iff_forall.2 fun x hx ↦
    ((cutoffCompCLM_eventuallyEq hχc f s hχ hx).and (ht x hx)).mono fun _ h ↦ h.1.trans h.2.symm

/-- If `f` is proper on the support of `T`, every test `s` on `Y` has a test on `X` agreeing with
`s ∘ f` near each point of the support of `T`; by
`TauCeti.BundleTest.pushforward_apply_of_eventuallyEq`, `T` pairs it with the value of `f_* T`
on `s`. -/
theorem IsProperOnSupport.exists_forall_eventually_eq (hT : IsProperOnSupport ⇑T f)
    (s : BundleTest J G (Trivial Y G)) :
    ∃ t : BundleTest I G (Trivial X G), ∀ x ∈ dsupport ⇑T, ∀ᶠ z in 𝓝 x, t z = s (f z) :=
  have h := (hT.exists_eventually_eq_one s.isCompact_tsupport).choose_spec
  ⟨cutoffCompCLM _ h.1 f s, fun _ hx ↦ cutoffCompCLM_eventuallyEq h.1 f s h.2 hx⟩

variable [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]

variable (T f) in
/-- The linear map underlying `TauCeti.BundleTest.pushforward`. -/
private def pushforwardLinearMap (hT : IsProperOnSupport ⇑T f) :
    BundleTest J G (Trivial Y G) →ₗ[ℝ] W where
  toFun s := T (cutoffCompCLM (hT.exists_eventually_eq_one s.isCompact_tsupport).choose
    (hT.exists_eventually_eq_one s.isCompact_tsupport).choose_spec.1 f s)
  map_add' s t := by
    rw [← map_add]
    refine map_cutoffCompCLM_eq _
      (hT.exists_eventually_eq_one (s + t).isCompact_tsupport).choose_spec.2 fun x hx ↦ ?_
    have hs := (hT.exists_eventually_eq_one s.isCompact_tsupport).choose_spec
    have ht := (hT.exists_eventually_eq_one t.isCompact_tsupport).choose_spec
    filter_upwards [cutoffCompCLM_eventuallyEq hs.1 f s hs.2 hx,
      cutoffCompCLM_eventuallyEq ht.1 f t ht.2 hx] with z hs ht
    simp [hs, ht]
  map_smul' a s := by
    rw [RingHom.id_apply, ← map_smul]
    refine map_cutoffCompCLM_eq _
      (hT.exists_eventually_eq_one (a • s).isCompact_tsupport).choose_spec.2 fun x hx ↦ ?_
    have hs := (hT.exists_eventually_eq_one s.isCompact_tsupport).choose_spec
    filter_upwards [cutoffCompCLM_eventuallyEq hs.1 f s hs.2 hx] with z hs
    simp [hs]

variable (T f) in
/-- The **pushforward** `f_* T` of a continuous linear functional `T` on the tests of a trivial
bundle over `X`, along a smooth map `f : X → Y` proper on the support of `T`: the functional on the
tests of the trivial bundle over `Y` pairing a test `s` with `T` through `T (χ (s ∘ f))`, where `χ`
is a smooth compactly supported function on `X` equal to one near `supp T ∩ f⁻¹(supp s)`. Its value
does not depend on `χ` (`TauCeti.BundleTest.pushforward_apply_of_eventuallyEq`). For scalar tests
these functionals are the distribution densities on `X`, and `f_* T` is the pushforward of
densities: on a density `u μ` it is `s ↦ ∫ s (f x) u x dμ`. -/
def pushforward (hT : IsProperOnSupport ⇑T f) : BundleTest J G (Trivial Y G) →L_c[ℝ] W where
  toLinearMap := pushforwardLinearMap T f hT
  cont := by
    let := frameTopology (I := J) (n := ∞) (fun y : Y ↦ trivializationAt G (Trivial Y G) y)
      (fun y ↦ ⟨_, (trivializationAt G (Trivial Y G) y).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp _).2 fun K ↦ ?_
    -- On tests supported in `K`, one cutoff serves all tests.
    obtain ⟨χ, hχc, hχ⟩ := hT.exists_eventually_eq_one K.isCompact
    refine (T.continuous.comp ((cutoffCompCLM χ hχc f).continuous.comp
      (continuous_ofSupportedIn K))).congr fun σ ↦ ?_
    have hσK : closure {y | (ofCompactlySupported J G _ (ofSupportedIn K σ)) y ≠ 0} ⊆ K := by
      simpa [ofSupportedIn_apply, ← ContMDiffSection.tsupport_def] using
        mem_supportedIn.1 σ.property
    refine (map_cutoffCompCLM_eq _ (hT.exists_eventually_eq_one
      (ofCompactlySupported J G _ (ofSupportedIn K σ)).isCompact_tsupport).choose_spec.2 fun x hx ↦
      cutoffCompCLM_eventuallyEq hχc f _ (hχ.filter_mono (nhdsSet_mono
        (inter_subset_inter_right _ (preimage_mono hσK)))) hx).symm

/-- **Values of the pushforward.** `(f_* T) s = T t` for every test `t` on `X` which agrees with
`s ∘ f` near each point of the support of `T`. -/
theorem pushforward_apply_of_eventuallyEq (hT : IsProperOnSupport ⇑T f)
    (s : BundleTest J G (Trivial Y G)) {t : BundleTest I G (Trivial X G)}
    (ht : ∀ x ∈ dsupport ⇑T, ∀ᶠ z in 𝓝 x, t z = s (f z)) : pushforward T f hT s = T t :=
  map_cutoffCompCLM_eq _ (hT.exists_eventually_eq_one s.isCompact_tsupport).choose_spec.2 ht

/-- **Values of the pushforward with a cutoff.** `(f_* T) s = T (χ (s ∘ f))` for every smooth
compactly supported `χ` equal to one near `supp T ∩ f⁻¹(supp s)`. -/
theorem pushforward_apply_eq_cutoffCompCLM (hT : IsProperOnSupport ⇑T f)
    (s : BundleTest J G (Trivial Y G)) {χ : C^∞⟮I, X; ℝ⟯} (hχc : HasCompactSupport χ)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport ⇑T ∩ f ⁻¹' closure {y | s y ≠ 0}), χ x = 1) :
    pushforward T f hT s = T (cutoffCompCLM χ hχc f s) :=
  pushforward_apply_of_eventuallyEq hT s fun _ hx ↦ cutoffCompCLM_eventuallyEq hχc f s hχ hx

/-- **The pushforward of a compactly supported functional** is its pushforward cut off by any
smooth compactly supported function equal to one near its support. -/
theorem pushforward_eq_cutoffPushforwardCLM (hT : IsProperOnSupport ⇑T f) {χ : C^∞⟮I, X; ℝ⟯}
    (hχc : HasCompactSupport χ) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport ⇑T), χ x = 1) :
    pushforward T f hT = cutoffPushforwardCLM χ hχc f T := by
  ext s
  exact pushforward_apply_eq_cutoffCompCLM hT s hχc (hχ.filter_mono (nhdsSet_mono
    inter_subset_left))

/-! ### The support of the pushforward -/

/-- The pushforward vanishes on tests supported away from the image of the support. -/
private theorem pushforward_apply_eq_zero (hT : IsProperOnSupport ⇑T f)
    {s : BundleTest J G (Trivial Y G)}
    (hs : Disjoint (closure {y | s y ≠ 0}) (f '' dsupport ⇑T)) : pushforward T f hT s = 0 := by
  rw [pushforward_apply_of_eventuallyEq hT s (t := 0) fun x hx ↦ ?_, map_zero]
  -- Near `x`, `f` takes values off the support of `s`.
  filter_upwards [eventually_apply_comp_eq_zero f.contMDiff.continuous s
    fun h ↦ disjoint_left.1 hs h ⟨x, hx, rfl⟩] with z hz
  simp [hz]

omit [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] in
/-- **The support of a pushforward with a cutoff** lies in the image of the part of the support of
`T` in the support of the cutoff: `supp f_* (χ T) ⊆ f (supp χ ∩ supp T)`. -/
theorem dsupport_cutoffPushforwardCLM_subset [T2Space Y] [ContinuousConstSMul ℝ W]
    {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ) :
    dsupport ⇑(cutoffPushforwardCLM χ hχ f T) ⊆ f '' (_root_.tsupport χ ∩ dsupport ⇑T) := by
  intro y hy
  by_contra hyT
  have hC : IsCompact (f '' (_root_.tsupport χ ∩ dsupport ⇑T)) :=
    (hχ.inter_right (isClosed_dsupport _)).image f.contMDiff.continuous
  refine (notMem_dsupport_iff.2 ⟨_, hC.isClosed.isOpen_compl, hyT, isVanishingOn_iff.2
    fun s hs ↦ ?_⟩) hy
  refine cutoffPushforwardCLM_apply_eq_zero_of_disjoint hχ f
    (isVanishingOn_iff.1 (isVanishingOn_compl_dsupport T)) ?_
  rw [sdiff_compl]
  exact disjoint_compl_left.mono_left hs

/-- **The support of the pushforward** lies in the image of the support:
`supp (f_* T) ⊆ f (supp T)`. -/
theorem dsupport_pushforward_subset [T2Space Y] (hT : IsProperOnSupport ⇑T f) :
    dsupport ⇑(pushforward T f hT) ⊆ f '' dsupport ⇑T := by
  have := J.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H' Y
  intro y hy
  by_contra hyT
  obtain ⟨K, hK, hyK⟩ := exists_compact_mem_nhds y
  -- Over `K` the image of the support is the compact, hence closed, image of `supp T ∩ f⁻¹(K)`.
  have hC := (hT K hK).image f.contMDiff.continuous
  refine (notMem_dsupport_iff.2 ⟨interior K \ f '' (dsupport ⇑T ∩ f ⁻¹' K),
    isOpen_interior.sdiff hC.isClosed, ⟨mem_interior_iff_mem_nhds.2 hyK,
      fun ⟨x, hx, hxy⟩ ↦ hyT ⟨x, hx.1, hxy⟩⟩, isVanishingOn_iff.2 fun s hs ↦ ?_⟩) hy
  refine pushforward_apply_eq_zero hT (disjoint_left.2 fun z hz ⟨x, hx, hxz⟩ ↦ (hs hz).2 ?_)
  exact ⟨x, ⟨hx, mem_preimage.2 (hxz ▸ interior_subset (hs hz).1)⟩, hxz⟩

/-- If `f` is proper on the support of `T` and `g ∘ f` is too, then `g` is proper on the support of
the pushforward `f_* T`. -/
theorem IsProperOnSupport.pushforward [T2Space Y] {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hT : IsProperOnSupport ⇑T f) (hgfT : IsProperOnSupport ⇑T (g ∘ f)) :
    IsProperOnSupport ⇑(pushforward T f hT) g := fun K hK ↦ by
  -- Over `K`, the support of `f_* T` lies in the compact image of `supp T ∩ (g ∘ f)⁻¹(K)`.
  have h : dsupport ⇑(BundleTest.pushforward T f hT) ∩ g ⁻¹' K =
      f '' (dsupport ⇑T ∩ (g ∘ f) ⁻¹' K) ∩ dsupport ⇑(BundleTest.pushforward T f hT) := by
    ext y
    refine ⟨fun hy ↦ ⟨?_, hy.1⟩, fun ⟨⟨x, hx, hxy⟩, hy⟩ ↦ ⟨hy, hxy ▸ hx.2⟩⟩
    obtain ⟨x, hx, rfl⟩ := dsupport_pushforward_subset hT hy.1
    exact ⟨x, ⟨hx, hy.2⟩, rfl⟩
  rw [h]
  exact ((hgfT K hK).image f.contMDiff.continuous).inter_right (isClosed_dsupport _)

/-! ### Linearity -/

/-- The pushforward of the zero functional is zero. -/
@[simp]
theorem pushforward_zero (h0 : IsProperOnSupport ⇑(0 : BundleTest I G (Trivial X G) →L_c[ℝ] W) f) :
    pushforward 0 f h0 = 0 := by
  ext s
  rw [pushforward_apply_of_eventuallyEq h0 s (t := 0) fun x hx ↦ by simp at hx]
  simp

/-- The pushforward is additive. -/
theorem pushforward_add {S : BundleTest I G (Trivial X G) →L_c[ℝ] W}
    (hS : IsProperOnSupport ⇑S f) (hT : IsProperOnSupport ⇑T f)
    (hST : IsProperOnSupport ⇑(S + T) f := hS.add hT) :
    pushforward (S + T) f hST = pushforward S f hS + pushforward T f hT := by
  ext s
  -- One cutoff serves `S`, `T` and `S + T`.
  obtain ⟨χ, hc, h1⟩ := exists_contMDiffMap_eventually_eq_one (I := I)
    ((hS _ s.isCompact_tsupport).union (hT _ s.isCompact_tsupport))
  have hsub {U : BundleTest I G (Trivial X G) →L_c[ℝ] W}
      (hU : dsupport ⇑U ⊆ dsupport ⇑S ∪ dsupport ⇑T) :
      ∀ᶠ x in 𝓝ˢ (dsupport ⇑U ∩ f ⁻¹' closure {y | s y ≠ 0}), χ x = 1 :=
    h1.filter_mono <| nhdsSet_mono fun x (hx : x ∈ dsupport ⇑U ∩ _) ↦
      (hU hx.1).imp (fun h ↦ ⟨h, hx.2⟩) (fun h ↦ ⟨h, hx.2⟩)
  rw [_root_.add_apply,
    pushforward_apply_eq_cutoffCompCLM hST s hc (hsub (by simpa using dsupport_add_subset ⇑S ⇑T)),
    pushforward_apply_eq_cutoffCompCLM hS s hc (hsub subset_union_left),
    pushforward_apply_eq_cutoffCompCLM hT s hc (hsub subset_union_right), _root_.add_apply]

/-- The pushforward commutes with scalar multiplication. -/
theorem pushforward_smul {R : Type*} [Monoid R] [DistribMulAction R W] [SMulCommClass ℝ R W]
    [ContinuousConstSMul R W] (hT : IsProperOnSupport ⇑T f) (c : R)
    (hcT : IsProperOnSupport ⇑(c • T) f := hT.smul c) :
    pushforward (c • T) f hcT = c • pushforward T f hT := by
  ext s
  obtain ⟨χ, hc, h1⟩ := hT.exists_eventually_eq_one s.isCompact_tsupport
  have hcT' : dsupport ⇑(c • T) ⊆ dsupport ⇑T := by simpa using dsupport_smul_subset c ⇑T
  rw [_root_.smul_apply, pushforward_apply_eq_cutoffCompCLM hT s hc h1,
    pushforward_apply_eq_cutoffCompCLM hcT s hc (h1.filter_mono <| nhdsSet_mono <|
      inter_subset_inter_left _ hcT'), _root_.smul_apply]

/-! ### Functoriality -/

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ Y] in
/-- **The pushforward along the identity** is the identity. -/
@[simp]
theorem pushforward_id (hT : IsProperOnSupport ⇑T (ContMDiffMap.id : C^∞⟮I, X; I, X⟯)) :
    pushforward T ContMDiffMap.id hT = T := by
  ext s
  exact pushforward_apply_of_eventuallyEq hT s fun _ _ ↦ Eventually.of_forall fun _ ↦ rfl

/-- **Functoriality of the pushforward**: pushing `T` forward along `f` and then along `g` is
pushing it forward along `g ∘ f`. -/
theorem pushforward_pushforward [T2Space Y] {E'' H'' Z : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [FiniteDimensional ℝ E''] [TopologicalSpace H'']
    {K : ModelWithCorners ℝ E'' H''}
    [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold K ∞ Z] {g : C^∞⟮J, Y; K, Z⟯}
    (hT : IsProperOnSupport ⇑T f) (hgfT : IsProperOnSupport ⇑T (g.comp f))
    (hgT : IsProperOnSupport ⇑(pushforward T f hT) g := hT.pushforward hgfT) :
    pushforward (pushforward T f hT) g hgT = pushforward T (g.comp f) hgfT := by
  ext s
  -- The part `L` of the support of `T` over `supp s` is compact, and so is its image in `Y`.
  set L := dsupport ⇑T ∩ (g.comp f) ⁻¹' closure {z | s z ≠ 0}
  have hL : IsCompact L := hgfT _ s.isCompact_tsupport
  obtain ⟨χ, hχc, hχ⟩ := exists_contMDiffMap_eventually_eq_one (I := I) hL
  obtain ⟨χ', hχc', hχ'⟩ := exists_contMDiffMap_eventually_eq_one (I := J)
    (hL.image f.contMDiff.continuous)
  -- `f (supp T) ∩ g⁻¹(supp s)` is the image of `L`.
  have hfL : f '' dsupport ⇑T ∩ g ⁻¹' closure {z | s z ≠ 0} = f '' L := by
    rw [← image_inter_preimage, preimage_preimage]
    simp_rw [L, ← ContMDiffMap.comp_apply g f]
  -- Pull `s` back to `Y` with the cutoff `χ'`, which is one near the image of `L`.
  have h₁ : pushforward (pushforward T f hT) g hgT s =
      pushforward T f hT (cutoffCompCLM χ' hχc' g s) :=
    pushforward_apply_of_eventuallyEq hgT s fun _ hy ↦ cutoffCompCLM_eventuallyEq hχc' g s
      (by rwa [hfL]) (dsupport_pushforward_subset hT hy)
  rw [h₁, pushforward_apply_eq_cutoffCompCLM hgfT s hχc hχ]
  refine pushforward_apply_of_eventuallyEq hT _ fun x hx ↦ ?_
  filter_upwards [cutoffCompCLM_eventuallyEq hχc (g.comp f) s hχ hx,
    (f.contMDiff.continuous.tendsto x).eventually (cutoffCompCLM_eventuallyEq hχc' g s
      (S := f '' dsupport ⇑T) (by rwa [hfL]) ⟨x, hx, rfl⟩)] with z h h'
  rw [h, h', ContMDiffMap.comp_apply]

/-! ### Point masses -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold J ∞ Y] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] in
/-- Every map is proper on the support of a point mass. -/
theorem isProperOnSupport_delta (x : X) (ℓ : G →L[ℝ] W) (f : X → Y) :
    IsProperOnSupport ⇑(delta (I := I) (F := G) (V := Trivial X G) x ℓ) f := fun _ _ ↦
  ((finite_singleton x).subset (inter_subset_left.trans
    (dsupport_delta_subset (I := I) (F := G) (V := Trivial X G) x ℓ))).isCompact

/-- **The pushforward of a point mass** is the point mass at the image point:
`f_* δ_x ℓ = δ_{f x} ℓ`. -/
@[simp]
theorem pushforward_delta (x : X) (ℓ : G →L[ℝ] W)
    (h : IsProperOnSupport ⇑(delta (I := I) (F := G) (V := Trivial X G) x ℓ) f) :
    pushforward (delta x ℓ) f h = delta (I := J) (F := G) (V := Trivial Y G) (f x) ℓ := by
  ext s
  obtain ⟨χ, hχc, hχ⟩ :=
    exists_contMDiffMap_eventually_eq_one (I := I) (isCompact_singleton (x := x))
  rw [pushforward_apply_eq_cutoffCompCLM h s hχc (hχ.filter_mono (nhdsSet_mono
    (inter_subset_left.trans (dsupport_delta_subset (I := I) (F := G) (V := Trivial X G) x ℓ))))]
  simp [hχ.self_of_nhdsSet x (mem_singleton x)]

end Pushforward


end TauCeti.BundleTest
