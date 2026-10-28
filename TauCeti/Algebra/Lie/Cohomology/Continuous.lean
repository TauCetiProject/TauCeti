/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import TauCeti.Algebra.Lie.Cochain

/-!
# Continuous low-degree Lie algebra cohomology with discrete coefficients

Let `L` be a Lie algebra carrying a topology and `M` a module of coefficients, regarded as a
discrete space. A cochain with values in `M` is continuous exactly when it is locally constant,
and since it is additive in each variable this is a condition at zero only:

* a one-cochain `f` is continuous when `f` vanishes near zero;
* an alternating two-cochain `c` is continuous when it is *separately continuous*, that is
  `y ↦ c x y` vanishes near zero for every `x`, and moreover `c` vanishes on a neighbourhood of
  `(0, 0)` in `L × L`.

These conditions define submodules `continuousOneCochain` and `continuousTwoCochain` of Mathlib's
low-degree Chevalley–Eilenberg cochains, without putting a topology on `M`. When `L` is a
topological additive group, they are precisely the cochains which are continuous for any discrete
topology on `M` (`mem_continuousOneCochain_iff_continuous`,
`mem_continuousTwoCochain_iff_continuous`). For a basis of neighbourhoods of zero, such as the
order filtration of formal currents, the condition on two-cochains becomes the familiar criterion:
separate continuity, together with one basic neighbourhood on which the cochain vanishes
identically (`mem_continuousTwoCochain_iff_of_hasBasis`).

If the bracket of `L` is continuous and every element of `M` is annihilated by a neighbourhood of
zero (for instance if `M` is a trivial module), then the differential `d₁₂` sends continuous
one-cochains to continuous two-cocycles (`d₁₂_mem_continuousTwoCocycle`). The continuous second
cohomology `continuousSecondCohomology` is the quotient of continuous two-cocycles by those
coboundaries of continuous one-cochains which are themselves continuous; under the hypotheses of
`d₁₂_mem_continuousTwoCocycle` these are all coboundaries of continuous one-cochains. With trivial
coefficients it is the receptacle for the classes of continuously split central extensions of a
topological Lie algebra, such as the formal loop algebra, by a discrete trivial module.

## Main definitions

* `TauCeti.LieModule.Cohomology.continuousOneCochain`: one-cochains vanishing near zero.
* `TauCeti.LieModule.Cohomology.continuousTwoCochain`: continuous alternating two-cochains.
* `TauCeti.LieModule.Cohomology.continuousTwoCocycle`: continuous two-cocycles.
* `TauCeti.LieModule.Cohomology.continuousTwoCoboundary`: the coboundaries of continuous
  one-cochains which are continuous two-cocycles.
* `TauCeti.LieModule.Cohomology.continuousSecondCohomology`: their quotient.

Continuous two-cochains pull back along continuous Lie algebra morphisms and push forward along
linear maps of coefficients (`twoCochainMap_mem_continuousTwoCochain`), and with trivial
coefficients so do continuous two-cocycles (`twoCochainMap_mem_continuousTwoCocycle`, and
`twoCochainMap_id_mem_continuousTwoCocycle` for coefficient maps alone). Continuous one-cochains
push forward along linear maps of coefficients (`comp_mem_continuousOneCochain`).

## Main results

* `TauCeti.LieModule.Cohomology.mem_continuousTwoCochain_iff_continuous`: the defining condition
  is joint continuity for a discrete topology on the coefficients.
* `TauCeti.LieModule.Cohomology.mem_continuousTwoCochain_iff_of_hasBasis`: the criterion in terms
  of a basis of neighbourhoods of zero.
* `TauCeti.LieModule.Cohomology.continuousTwoCochain_ext_on`: continuous two-cochains agreeing
  on a dense subset are equal.
* `TauCeti.LieModule.Cohomology.d₁₂_mem_continuousTwoCocycle`: coboundaries of continuous
  one-cochains are continuous two-cocycles.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for continuous cohomology of the
  formal loop algebra with trivial coefficients.
-/

public section

open Filter Topology

namespace TauCeti.LieModule.Cohomology

open _root_.LieModule.Cohomology

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [AddCommGroup M] [Module R M]

section Cochains

/-- Continuous one-cochains with discrete coefficients: the linear maps `L → M` vanishing on a
neighbourhood of zero. -/
def continuousOneCochain : Submodule R (oneCochain R L M) where
  carrier := {f | ∀ᶠ x in 𝓝 (0 : L), f x = 0}
  add_mem' hf hg := (hf.and hg).mono fun x hx ↦ by simp [hx.1, hx.2]
  zero_mem' := Eventually.of_forall fun _ ↦ rfl
  smul_mem' r _ hf := hf.mono fun x hx ↦ by simp [hx]

/-- Continuous alternating two-cochains with discrete coefficients: the alternating bilinear
maps `c` such that every partial map `c x` vanishes near zero, and `c` vanishes on a
neighbourhood of `(0, 0)`. -/
def continuousTwoCochain : Submodule R (twoCochain R L M) where
  carrier := {c | (∀ x, ∀ᶠ y in 𝓝 (0 : L), c x y = 0) ∧ ∀ᶠ p : L × L in 𝓝 0, c p.1 p.2 = 0}
  add_mem' hc hd := ⟨fun x ↦ ((hc.1 x).and (hd.1 x)).mono fun y hy ↦ by
      simp [add_apply_apply, hy.1, hy.2],
    (hc.2.and hd.2).mono fun p hp ↦ by simp [add_apply_apply, hp.1, hp.2]⟩
  zero_mem' := ⟨fun _ ↦ Eventually.of_forall fun _ ↦ rfl, Eventually.of_forall fun _ ↦ rfl⟩
  smul_mem' r _ hc := ⟨fun x ↦ (hc.1 x).mono fun y hy ↦ by simp [smul_apply_apply, hy],
    hc.2.mono fun p hp ↦ by simp [smul_apply_apply, hp]⟩

variable {R L M}

theorem mem_continuousOneCochain_iff {f : oneCochain R L M} :
    f ∈ continuousOneCochain R L M ↔ ∀ᶠ x in 𝓝 (0 : L), f x = 0 := Iff.rfl

theorem mem_continuousTwoCochain_iff {c : twoCochain R L M} :
    c ∈ continuousTwoCochain R L M ↔
      (∀ x, ∀ᶠ y in 𝓝 (0 : L), c x y = 0) ∧ ∀ᶠ p : L × L in 𝓝 0, c p.1 p.2 = 0 := Iff.rfl

/-- The partial maps of a continuous two-cochain are continuous one-cochains. -/
theorem apply_mem_continuousOneCochain {c : twoCochain R L M}
    (hc : c ∈ continuousTwoCochain R L M) (x : L) : c x ∈ continuousOneCochain R L M :=
  hc.1 x

/-- **The joint-continuity criterion.** Given a basis `s` of neighbourhoods of zero, a two-cochain
is continuous exactly when each partial map vanishes on some basic neighbourhood, and the
cochain vanishes on `s i × s i` for some basic neighbourhood `s i`. -/
theorem mem_continuousTwoCochain_iff_of_hasBasis {ι : Type*} {p : ι → Prop} {s : ι → Set L}
    (h : (𝓝 (0 : L)).HasBasis p s) {c : twoCochain R L M} :
    c ∈ continuousTwoCochain R L M ↔
      (∀ x, ∃ i, p i ∧ ∀ y ∈ s i, c x y = 0) ∧
        ∃ i, p i ∧ ∀ u ∈ s i, ∀ v ∈ s i, c u v = 0 := by
  rw [mem_continuousTwoCochain_iff, ← Prod.mk_zero_zero, nhds_prod_eq,
    h.prod_self.eventually_iff]
  simp only [h.eventually_iff, Set.mem_prod, and_imp, Prod.forall]
  aesop

section Topology

variable [IsTopologicalAddGroup L] [TopologicalSpace M] [DiscreteTopology M]

/-- A one-cochain vanishes near zero exactly when it is continuous for a discrete topology on the
coefficients. -/
theorem mem_continuousOneCochain_iff_continuous {f : oneCochain R L M} :
    f ∈ continuousOneCochain R L M ↔ Continuous f := by
  have : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  refine ⟨fun hf ↦ continuous_of_continuousAt_zero f ?_, fun hf ↦ ?_⟩
  · rwa [ContinuousAt, map_zero, nhds_discrete M, tendsto_pure]
  · simpa [nhds_discrete M, mem_continuousOneCochain_iff] using hf.tendsto 0

/-- **Continuity of two-cochains.** The defining condition of `continuousTwoCochain` is joint
continuity on `L × L` for a discrete topology on the coefficients. -/
theorem mem_continuousTwoCochain_iff_continuous {c : twoCochain R L M} :
    c ∈ continuousTwoCochain R L M ↔ Continuous fun p : L × L ↦ c p.1 p.2 := by
  have : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  refine ⟨fun hc ↦ ?_, fun hc ↦ ⟨fun x ↦ ?_, ?_⟩⟩
  · -- A biadditive map out of a product of topological groups is continuous once it is
    -- continuous at zero and separately continuous at zero; alternation gives the second
    -- variable from the first.
    let B : L →+ L →+ M := AddMonoidHom.mk' (fun x ↦ (c x).toAddMonoidHom) fun x y ↦ by
      ext z
      simp
    refine continuous_of_continuousAt_zero₂ B ?_ (fun x ↦ ?_) (fun y ↦ ?_)
    · rw [ContinuousAt, map_zero, nhds_discrete M, tendsto_pure, Prod.mk_zero_zero]
      exact hc.2
    · rw [ContinuousAt, map_zero, nhds_discrete M, tendsto_pure]
      exact hc.1 x
    · rw [ContinuousAt, map_zero, AddMonoidHom.zero_apply, nhds_discrete M, tendsto_pure]
      exact (hc.1 y).mono fun x hx ↦ by simp [B, ← twoCochain_skew c y x, hx]
  · simpa [nhds_discrete M, Function.comp_def] using (hc.comp (Continuous.prodMk_right x)).tendsto 0
  · simpa [nhds_discrete M] using hc.tendsto 0

end Topology

/-- **Continuous two-cochains are determined on a dense set.** Two continuous two-cochains on a
topological Lie algebra which agree on all pairs of elements of a dense subset are equal. -/
theorem continuousTwoCochain_ext_on [IsTopologicalAddGroup L] {c d : twoCochain R L M}
    (hc : c ∈ continuousTwoCochain R L M) (hd : d ∈ continuousTwoCochain R L M) {s : Set L}
    (hs : Dense s) (h : ∀ x ∈ s, ∀ y ∈ s, c x y = d x y) : c = d := by
  -- Give the coefficients the discrete topology, so that both cochains are continuous maps into a
  -- Hausdorff space.
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have hcd := (mem_continuousTwoCochain_iff_continuous.mp hc).ext_on (hs.prod hs)
    (mem_continuousTwoCochain_iff_continuous.mp hd) fun p hp ↦ h _ hp.1 _ hp.2
  exact Subtype.ext (LinearMap.ext₂ fun x y ↦ congrFun hcd (x, y))

variable {L' M' : Type*} [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L'] [AddCommGroup M']
  [Module R M']

/-- **Continuous two-cochains pull back along continuous morphisms.** Pulling a continuous
two-cochain back along a continuous Lie algebra morphism `φ` and pushing it forward along a linear
map `e` of coefficients gives a continuous two-cochain. -/
theorem twoCochainMap_mem_continuousTwoCochain (e : M →ₗ[R] M') {φ : L' →ₗ⁅R⁆ L}
    (hφ : Continuous φ) {c : twoCochain R L M} (hc : c ∈ continuousTwoCochain R L M) :
    twoCochainMap e φ c ∈ continuousTwoCochain R L' M' := by
  have h₁ : Tendsto φ (𝓝 0) (𝓝 0) := by simpa using hφ.tendsto 0
  have h₂ : Tendsto (Prod.map φ φ) (𝓝 0) (𝓝 0) := by
    simpa [Prod.map, Prod.zero_eq_mk] using (hφ.prodMap hφ).tendsto 0
  exact ⟨fun x ↦ (h₁.eventually (hc.1 (φ x))).mono fun y hy ↦ by simp [hy],
    (h₂.eventually hc.2).mono fun p (hp : c (φ p.1) (φ p.2) = 0) ↦ by simp [hp]⟩

/-- Pushing a continuous one-cochain forward along a linear map `e` of coefficients gives a
continuous one-cochain. -/
theorem comp_mem_continuousOneCochain (e : M →ₗ[R] M') {f : oneCochain R L M}
    (hf : f ∈ continuousOneCochain R L M) : e ∘ₗ f ∈ continuousOneCochain R L M' :=
  hf.mono fun x hx ↦ by simp [hx]

end Cochains

section Cohomology

variable [LieRingModule L M] [LieModule R L M]

/-- Continuous two-cocycles: continuous two-cochains annihilated by the differential `d₂₃`. -/
def continuousTwoCocycle : Submodule R (twoCochain R L M) :=
  continuousTwoCochain R L M ⊓ twoCocycle R L M

/-- The coboundaries of continuous one-cochains which are themselves continuous, as a submodule of
the continuous two-cocycles. By `d₁₂_mem_continuousTwoCocycle`, this is every coboundary of a
continuous one-cochain when the bracket of `L` is continuous and every element of `M` is
annihilated by a neighbourhood of zero. -/
def continuousTwoCoboundary : Submodule R (continuousTwoCocycle R L M) :=
  ((continuousOneCochain R L M).map (d₁₂ R L M)).comap (continuousTwoCocycle R L M).subtype

/-- Continuous second Lie algebra cohomology with discrete coefficients: continuous two-cocycles
modulo the continuous coboundaries of continuous one-cochains. -/
abbrev continuousSecondCohomology := continuousTwoCocycle R L M ⧸ continuousTwoCoboundary R L M

/-- The quotient map from continuous two-cocycles to continuous second cohomology. -/
def continuousSecondCohomologyMk :
    continuousTwoCocycle R L M →ₗ[R] continuousSecondCohomology R L M :=
  (continuousTwoCoboundary R L M).mkQ

variable {R L M}

theorem mem_continuousTwoCocycle_iff {c : twoCochain R L M} :
    c ∈ continuousTwoCocycle R L M ↔ c ∈ continuousTwoCochain R L M ∧ c ∈ twoCocycle R L M :=
  Iff.rfl

theorem mem_continuousTwoCoboundary_iff {c : continuousTwoCocycle R L M} :
    c ∈ continuousTwoCoboundary R L M ↔
      ∃ f ∈ continuousOneCochain R L M, d₁₂ R L M f = c := by
  simp [continuousTwoCoboundary]

/-- **Coboundaries of continuous cochains are continuous cocycles.** If the bracket of `L` is
continuous and every element of `M` is annihilated by a neighbourhood of zero, the differential of
a continuous one-cochain is a continuous two-cocycle. -/
theorem d₁₂_mem_continuousTwoCocycle (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, ∀ᶠ x in 𝓝 (0 : L), ⁅x, m⁆ = 0) {f : oneCochain R L M}
    (hf : f ∈ continuousOneCochain R L M) : d₁₂ R L M f ∈ continuousTwoCocycle R L M := by
  refine ⟨⟨fun x ↦ ?_, ?_⟩, range_d₁₂_le_twoCocycle ⟨f, rfl⟩⟩
  · -- Near zero, `y`, `⁅x, y⁆` lie in the kernel of `f` and `y` annihilates `f x`.
    have hx : Tendsto (fun y : L ↦ ⁅x, y⁆) (𝓝 0) (𝓝 0) := by
      simpa [Function.comp_def] using (hL.comp (Continuous.prodMk_right x)).tendsto 0
    filter_upwards [hf, hM (f x), hx.eventually hf] with y h₁ h₂ h₃
    simp [d₁₂_apply_apply, h₁, h₂, h₃]
  · -- Near `(0, 0)`, both arguments and their bracket lie in the kernel of `f`.
    have hp : Tendsto (fun p : L × L ↦ ⁅p.1, p.2⁆) (𝓝 0) (𝓝 0) := by
      simpa using hL.tendsto 0
    filter_upwards [(continuous_fst.tendsto 0).eventually hf,
      (continuous_snd.tendsto 0).eventually hf, hp.eventually hf] with p h₁ h₂ h₃
    simp [d₁₂_apply_apply, h₁, h₂, h₃]

/-- With trivial coefficients, pulling a continuous two-cocycle back along a continuous Lie
algebra morphism and pushing it forward along a linear map of coefficients gives a continuous
two-cocycle. -/
theorem twoCochainMap_mem_continuousTwoCocycle {L' M' : Type*} [LieRing L'] [LieAlgebra R L']
    [TopologicalSpace L'] [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
    [LieModule.IsTrivial L M] [LieModule.IsTrivial L' M'] (e : M →ₗ[R] M') {φ : L' →ₗ⁅R⁆ L}
    (hφ : Continuous φ) {c : twoCochain R L M} (hc : c ∈ continuousTwoCocycle R L M) :
    twoCochainMap e φ c ∈ continuousTwoCocycle R L' M' :=
  ⟨twoCochainMap_mem_continuousTwoCochain e hφ hc.1, twoCochainMap_mem_twoCocycle e φ hc.2⟩

/-- With trivial coefficients, pushing a continuous two-cocycle forward along a linear map `e` of
coefficients gives a continuous two-cocycle. -/
theorem twoCochainMap_id_mem_continuousTwoCocycle {M' : Type*} [AddCommGroup M'] [Module R M']
    [LieRingModule L M'] [LieModule R L M'] [LieModule.IsTrivial L M] [LieModule.IsTrivial L M']
    (e : M →ₗ[R] M') {c : twoCochain R L M} (hc : c ∈ continuousTwoCocycle R L M) :
    twoCochainMap e LieHom.id c ∈ continuousTwoCocycle R L M' :=
  twoCochainMap_mem_continuousTwoCocycle e (by simpa using continuous_id) hc

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Descend a linear map on continuous two-cocycles that vanishes on coboundaries of continuous
one-cochains to continuous second cohomology. -/
def continuousSecondCohomologyLift (g : continuousTwoCocycle R L M →ₗ[R] N)
    (h : ∀ c ∈ continuousTwoCoboundary R L M, g c = 0) :
    continuousSecondCohomology R L M →ₗ[R] N :=
  (continuousTwoCoboundary R L M).liftQ g h

@[simp]
theorem continuousSecondCohomologyLift_mk (g : continuousTwoCocycle R L M →ₗ[R] N)
    (h : ∀ c ∈ continuousTwoCoboundary R L M, g c = 0) (c : continuousTwoCocycle R L M) :
    continuousSecondCohomologyLift g h (continuousSecondCohomologyMk R L M c) = g c := (rfl)

/-- A linear map from continuous second cohomology is determined by its values on cocycle
representatives. -/
theorem continuousSecondCohomologyLift_unique (g : continuousTwoCocycle R L M →ₗ[R] N)
    (h : ∀ c ∈ continuousTwoCoboundary R L M, g c = 0)
    (φ : continuousSecondCohomology R L M →ₗ[R] N)
    (hφ : φ ∘ₗ continuousSecondCohomologyMk R L M = g) :
    φ = continuousSecondCohomologyLift g h :=
  Submodule.linearMap_qext _ hφ

/-- Two linear maps out of continuous second cohomology agree once they agree on cocycle
representatives. -/
@[ext]
theorem continuousSecondCohomology_hom_ext {g₁ g₂ : continuousSecondCohomology R L M →ₗ[R] N}
    (h : g₁ ∘ₗ continuousSecondCohomologyMk R L M = g₂ ∘ₗ continuousSecondCohomologyMk R L M) :
    g₁ = g₂ :=
  Submodule.linearMap_qext _ h

@[simp]
theorem continuousSecondCohomologyMk_eq_zero_iff (c : continuousTwoCocycle R L M) :
    continuousSecondCohomologyMk R L M c = 0 ↔
      ∃ f ∈ continuousOneCochain R L M, d₁₂ R L M f = c := by
  rw [continuousSecondCohomologyMk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_continuousTwoCoboundary_iff]

/-- Two continuous cocycles represent the same class exactly when their difference is the
coboundary of a continuous one-cochain. -/
theorem continuousSecondCohomologyMk_eq_iff (c d : continuousTwoCocycle R L M) :
    continuousSecondCohomologyMk R L M c = continuousSecondCohomologyMk R L M d ↔
      ∃ f ∈ continuousOneCochain R L M, d₁₂ R L M f = (c - d : continuousTwoCocycle R L M) := by
  rw [← sub_eq_zero, ← map_sub, continuousSecondCohomologyMk_eq_zero_iff]

/-- Every continuous second cohomology class has a continuous cocycle representative. -/
theorem continuousSecondCohomologyMk_surjective :
    Function.Surjective (continuousSecondCohomologyMk R L M) :=
  (continuousTwoCoboundary R L M).mkQ_surjective

end Cohomology

end TauCeti.LieModule.Cohomology
