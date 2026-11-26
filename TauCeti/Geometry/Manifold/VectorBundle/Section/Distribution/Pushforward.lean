/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
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
(`TauCeti.BundleTest.cutoffPushforwardCLM`).

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
* `TauCeti.BundleTest.IsProperOnSupport`: `f` is proper on the support of `T`, with
  `TauCeti.BundleTest.isProperOnSupport_of_isCompact_dsupport` and
  `TauCeti.BundleTest.isProperOnSupport_of_isCompact_preimage`.
* `TauCeti.BundleTest.pushforward`: the pushforward `f_* T`, with its values
  `TauCeti.BundleTest.pushforward_apply_of_eventuallyEq` and
  `TauCeti.BundleTest.pushforward_apply_eq_cutoffCompCLM`, and
  `TauCeti.BundleTest.pushforward_eq_cutoffPushforwardCLM` for compactly supported `T`.
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

variable [FiniteDimensional ℝ E] [IsManifold I ∞ X] [FiniteDimensional ℝ E'] [IsManifold J ∞ Y]

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

section Dual

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W]

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

end Dual

end CutoffComp

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
