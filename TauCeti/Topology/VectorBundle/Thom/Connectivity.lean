/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative
public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.Basic
public import TauCeti.Topology.VectorBundle.EulerClass
import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
import TauCeti.Topology.Homotopy.SerreFibration.Connected
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Connectivity of the Thom pair and its twisted homology below the rank

Let `E → B` be a real vector bundle of rank `r` over an arbitrary base, with Thom pair `(E, E₀)`,
`E₀` the complement of the zero section (`TauCeti.zeroSectionCompl`). A linear bundle chart of `E`
restricts to a chart of the projection `E₀ → B` (`TauCeti.zeroSectionComplProj`), with fibre the
nonzero vectors `F ∖ {0}` of the model fibre (`Bundle.Trivialization.zeroSectionCompl`). So
`E₀ → B` is locally trivial, hence a Serre fibration
(`TauCeti.TopCat.mem_serreFibrations_zeroSectionComplProj`), whose fibres `F ∖ {0}` are
`(r - 2)`-connected (`TauCeti.subsingleton_homotopyGroup_compl_singleton_of_lt`). Therefore
`E₀ → B` is an `(r - 1)`-connected map (`TauCeti.isNConnected_zeroSectionComplProj`). The
projection `E → B` is a weak homotopy equivalence, its fibres being vector spaces, so the inclusion
`E₀ → E` is `(r - 1)`-connected as well (`TauCeti.isNConnected_subtypeVal_zeroSectionCompl`).

Consequently the relative homology of the Thom pair vanishes below the rank with **any local
coefficient system** `L` on the total space: `Hₘ(E, E₀; L) = 0` for `m < r`
(`TauCeti.isZero_twistedHomology_thomPair`), through the long exact sequence of the pair
(`TopPair.isZero_twistedHomology_of_isNConnected`). No orientation, metric or condition on the base
is needed. For constant coefficients this vanishing is also proved by a Mayer–Vietoris argument
over trivializing open sets (`TauCeti.isZero_singularHomology_thomPair`); that argument does not
carry over directly to a local coefficient system, which need not be trivial over a trivializing
open set of the base. The twisted vanishing is the range below the rank of the Thom isomorphism
with local coefficients `Hₘ₊ᵣ(E, E₀; π^*L) ≅ Hₘ(B; o(E) ⊗ L)`, where `o(E)` is the orientation
system of the bundle, since the right side vanishes in negative degrees.

Dually, for a local system `L` with projective fibres, such as the integral orientation system
pulled back to the total space, the relative cohomology `Hᵐ(E, E₀; L, M)` vanishes for `m < r`
(`TauCeti.isZero_twistedCohomology_thomPair`), and in the rank degree the Kronecker map identifies
it with the morphisms out of homology, `Hʳ(E, E₀; L, M) ≃ Hom(Hᵣ(E, E₀; L), M)`
(`TauCeti.thomPairTwistedCohomologyFinrankEquiv`), by the universal coefficient theorem with local
coefficients (`TopPair.twistedKronecker_bijective_of_projective_homology_lt`). So a class of
`Hʳ(E, E₀; L, M)` is determined by, and can be prescribed through, its evaluations on
`Hᵣ(E, E₀; L)`. With `L` the orientation system this is the degree in which a Thom class of a bundle
that need not be orientable lives, with coefficients twisted by its orientation.

The chart, the Serre fibration property and the connectivity of `E₀ → B` follow the sphere bundle
chart `Bundle.Trivialization.sphereBundle` and `TauCeti.isNConnected_sphereBundleProj` in
`TauCeti.Topology.VectorBundle.SphereBundle.LocallyTrivial`, without the normalization to unit
vectors, so they hold over any nontrivially normed field.

## Main declarations

* `Bundle.Trivialization.zeroSectionCompl`: the chart of `E₀ → B` induced by a linear chart of `E`.
* `TauCeti.TopCat.mem_serreFibrations_zeroSectionComplProj`: `E₀ → B` is a Serre fibration.
* `TauCeti.isNConnected_zeroSectionComplProj`, `TauCeti.isNConnected_subtypeVal_zeroSectionCompl`:
  for a bundle of rank `n + 1`, the projection `E₀ → B` and the inclusion `E₀ → E` are
  `n`-connected.
* `TauCeti.isZero_twistedHomology_thomPair`: `Hₘ(E, E₀; L) = 0` for `m` below the rank and every
  local coefficient system `L`.
* `TauCeti.isZero_twistedCohomology_thomPair`: `Hᵐ(E, E₀; L, M) = 0` for `m` below the rank and
  every local coefficient system `L` with projective fibres.
* `TauCeti.twistedKronecker_bijective_thomPair`, `TauCeti.thomPairTwistedCohomologyFinrankEquiv`:
  in the rank degree, the Kronecker map `Hʳ(E, E₀; L, M) ⟶ Hom(Hᵣ(E, E₀; L), M)` is bijective.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §10 (the Thom pair of an oriented bundle vanishes below the
  rank).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H (homology with local coefficients), Proposition 4.21 (`n`-connected maps and
  homology) and Theorem 4D.10 (the Thom isomorphism).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set Topology

universe u w

namespace Bundle.Trivialization

open TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type w} [TopologicalSpace B] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] (e : Trivialization F (π F E)) [e.IsLinear 𝕜]

include 𝕜 in
/-- A nonzero vector of the bundle gives a nonzero vector of the model fibre. -/
private theorem nonempty_compl_zero (v : TauCeti.zeroSectionCompl F E) : Nonempty ({0}ᶜ : Set F) :=
  ⟨⟨(trivializationAt F E (v : TotalSpace F E).proj v).2,
    ((trivializationAt F E _).snd_apply_ne_zero_iff 𝕜
      (FiberBundle.mem_baseSet_trivializationAt' _)).2 (mem_zeroSectionCompl.1 v.property)⟩⟩

include 𝕜 in
/-- A nonzero vector of the model fibre gives a nonzero vector of the bundle over every point. -/
private theorem nonempty_zeroSectionCompl (b : B) (w : ({0}ᶜ : Set F)) :
    Nonempty (TauCeti.zeroSectionCompl F E) :=
  ⟨⟨⟨b, (trivializationAt F E b).symm b w⟩, mem_zeroSectionCompl.2
    (((trivializationAt F E b).symm_apply_ne_zero_iff 𝕜
      (FiberBundle.mem_baseSet_trivializationAt' b)).2 w.property)⟩⟩

open scoped Classical in
/-- The fibre coordinate of the chart of the nonzero vectors: `e` over its base set, and an
arbitrary nonzero vector elsewhere. -/
private def zeroSectionComplCoord (v : TauCeti.zeroSectionCompl F E) : ({0}ᶜ : Set F) :=
  if hv : (v : TotalSpace F E).proj ∈ e.baseSet then
    ⟨(e v).2, (e.snd_apply_ne_zero_iff 𝕜 hv).2 (mem_zeroSectionCompl.1 v.property)⟩
  else Classical.choice (nonempty_compl_zero 𝕜 v)

private theorem coe_zeroSectionComplCoord {v : TauCeti.zeroSectionCompl F E}
    (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    (e.zeroSectionComplCoord 𝕜 v : F) = (e v).2 := by
  simp only [zeroSectionComplCoord, hv, ↓reduceDIte]

open scoped Classical in
/-- The inverse of the chart of the nonzero vectors: the inverse of `e` over its base set, and an
arbitrary nonzero vector elsewhere. -/
private def zeroSectionComplInv (p : B × ({0}ᶜ : Set F)) : TauCeti.zeroSectionCompl F E :=
  if hp : p.1 ∈ e.baseSet then
    ⟨⟨p.1, e.symm p.1 p.2⟩, mem_zeroSectionCompl.2 ((e.symm_apply_ne_zero_iff 𝕜 hp).2 p.2.property)⟩
  else Classical.choice (nonempty_zeroSectionCompl 𝕜 p.1 p.2)

private theorem coe_zeroSectionComplInv {p : B × ({0}ᶜ : Set F)} (hp : p.1 ∈ e.baseSet) :
    (e.zeroSectionComplInv 𝕜 p : TotalSpace F E) = ⟨p.1, e.symm p.1 p.2⟩ := by
  simp only [zeroSectionComplInv, hp, ↓reduceDIte]

/-- **The chart of the nonzero vectors induced by a linear chart.** A linear bundle chart `e` of a
vector bundle restricts to a chart of the projection `E₀ → B` of the nonzero vectors, with
fibre the nonzero vectors of the model fibre and the same base set. -/
def zeroSectionCompl :
    Trivialization ({0}ᶜ : Set F) (zeroSectionComplProj F E) where
  toFun v := (zeroSectionComplProj F E v, e.zeroSectionComplCoord 𝕜 v)
  invFun := e.zeroSectionComplInv 𝕜
  source := zeroSectionComplProj F E ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, zeroSectionComplProj_apply, e.coe_zeroSectionComplInv 𝕜 hp.1]
    exact hp.1
  left_inv' v hv := by
    have hv' : (v : TotalSpace F E).proj ∈ e.baseSet := hv
    apply Subtype.ext
    rw [e.coe_zeroSectionComplInv 𝕜 hv', e.coe_zeroSectionComplCoord 𝕜 hv',
      zeroSectionComplProj_apply, e.symm_proj_apply _ hv']
  right_inv' p hp := by
    have hp' : p.1 ∈ e.baseSet := hp.1
    have hz : (e.zeroSectionComplInv 𝕜 p : TotalSpace F E).proj = p.1 := by
      rw [e.coe_zeroSectionComplInv 𝕜 hp']
    refine Prod.ext hz (Subtype.ext ?_)
    rw [e.coe_zeroSectionComplCoord 𝕜 (by rwa [hz]), e.coe_zeroSectionComplInv 𝕜 hp',
      e.apply_mk_symm hp']
  open_source := e.open_baseSet.preimage (zeroSectionComplProj F E).continuous
  open_target := e.open_baseSet.prod isOpen_univ
  continuousOn_toFun := by
    -- Read the second coordinate in the model fibre, where the map is `e`.
    rw [(IsInducing.id.prodMap IsInducing.subtypeVal).continuousOn_iff]
    have he : ContinuousOn (fun v : TauCeti.zeroSectionCompl F E ↦ e v)
        (zeroSectionComplProj F E ⁻¹' e.baseSet) :=
      e.continuousOn.comp continuous_subtypeVal.continuousOn fun v hv ↦ e.mem_source.2 hv
    refine (he.fst.prodMk he.snd).congr fun v hv ↦ ?_
    exact Prod.ext (e.coe_fst (e.mem_source.2 hv)).symm (e.coe_zeroSectionComplCoord 𝕜 hv)
  continuousOn_invFun := by
    -- Read the value in the total space of `E`, where the map is the inverse of `e`.
    rw [IsInducing.subtypeVal.continuousOn_iff]
    refine (e.continuousOn_symm.comp (continuous_id.prodMap continuous_subtypeVal).continuousOn
      fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ ⟨hp.1, mem_univ _⟩).congr
      fun p (hp : p ∈ e.baseSet ×ˢ univ) ↦ ?_
    exact e.coe_zeroSectionComplInv 𝕜 hp.1
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The chart of the nonzero vectors has the base set of `e`. -/
@[simp]
theorem zeroSectionCompl_baseSet : (e.zeroSectionCompl 𝕜).baseSet = e.baseSet :=
  (rfl)

/-- Over its base set, the chart of the nonzero vectors reads a nonzero vector in the chart `e`. -/
@[simp]
theorem coe_zeroSectionCompl_apply_snd {v : TauCeti.zeroSectionCompl F E}
    (hv : (v : TotalSpace F E).proj ∈ e.baseSet) :
    ((e.zeroSectionCompl 𝕜 v).2 : F) = (e v).2 :=
  e.coe_zeroSectionComplCoord 𝕜 hv

/-- Over its base set, the inverse chart of the nonzero vectors is the inverse of `e`. -/
@[simp]
theorem coe_zeroSectionCompl_symm_apply {b : B} (hb : b ∈ e.baseSet) (w : ({0}ᶜ : Set F)) :
    ((e.zeroSectionCompl 𝕜).toOpenPartialHomeomorph.symm (b, w) : TotalSpace F E) =
      ⟨b, e.symm b w⟩ :=
  e.coe_zeroSectionComplInv 𝕜 (p := (b, w)) hb

end Bundle.Trivialization

namespace TauCeti

section LocallyTrivial

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type w} [TopologicalSpace B] (F : Type*)
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle 𝕜 F E]

include 𝕜 in
/-- **The nonzero vectors of a vector bundle form a locally trivial bundle.** Every point of
the base lies in the base set of a chart of `E₀ → B` with fibre the nonzero vectors of the model
fibre `F`. -/
theorem exists_trivialization_zeroSectionComplProj (b : B) :
    ∃ e : Trivialization ({0}ᶜ : Set F) (zeroSectionComplProj F E), b ∈ e.baseSet :=
  ⟨(trivializationAt F E b).zeroSectionCompl 𝕜, FiberBundle.mem_baseSet_trivializationAt' b⟩

include 𝕜 in
/-- **The projection of the nonzero vectors of a vector bundle is a Serre fibration.** -/
theorem TopCat.mem_serreFibrations_zeroSectionComplProj :
    TopCat.serreFibrations (_root_.TopCat.ofHom (zeroSectionComplProj F E) :
      _root_.TopCat.of (zeroSectionCompl F E) ⟶ _root_.TopCat.of B) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (exists_trivialization_zeroSectionComplProj 𝕜 F E)

end LocallyTrivial

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

variable (E) in
/-- **The nonzero vectors of a bundle of rank `n + 1` form an `n`-connected map to the base.** If
the model fibre `F` has dimension `n + 1`, the projection `E₀ → B`, whose fibres are homeomorphic
to `F ∖ {0}`, induces bijections on `πₖ` for `k < n`, path components included, and a surjection
on `πₙ`. -/
theorem isNConnected_zeroSectionComplProj {n : ℕ} (hF : finrank ℝ F = n + 1) :
    (zeroSectionComplProj F E).IsNConnected n := by
  refine (TopCat.isNConnected_iff_of_mem_serreFibrations
    (TopCat.mem_serreFibrations_zeroSectionComplProj ℝ F E) n).2 fun b ↦ ?_
  -- Every fibre is homeomorphic to the nonzero vectors of `F`, which are `(n - 1)`-connected.
  obtain ⟨e, hb⟩ := exists_trivialization_zeroSectionComplProj ℝ F E b
  let h := e.preimageSingletonHomeomorph hb
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  obtain ⟨w, hw⟩ := exists_ne (0 : F)
  refine ⟨⟨h.symm ⟨w, hw⟩⟩, fun x k hk ↦ ?_⟩
  have := subsingleton_homotopyGroup_compl_singleton_of_lt hF 0 (N := Fin k) (by simpa using hk)
    (h x)
  exact (HomotopyGroup.homeomorphEquiv h x).subsingleton

variable (E) in
/-- **The inclusion of the nonzero vectors of a bundle of rank `n + 1` is `n`-connected.** If the
model fibre `F` has dimension `n + 1`, the inclusion `E₀ → E` of the complement of the zero section
induces bijections on `πₖ` for `k < n`, path components included, and a surjection on `πₙ`. -/
theorem isNConnected_subtypeVal_zeroSectionCompl {n : ℕ} (hF : finrank ℝ F = n + 1) :
    (ContinuousMap.subtypeVal (zeroSectionCompl F E)).IsNConnected n := by
  -- The projection of `E` is a weak homotopy equivalence, its fibres being vector spaces.
  have hπ : (⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
      C(TotalSpace F E, B)).IsWeakHomotopyEquivalence := by
    refine (TopCat.isWeakHomotopyEquivalence_iff_of_mem_serreFibrations
      (TopCat.mem_serreFibrations_proj F E)).2 fun b ↦ ?_
    let h := (trivializationAt F E b).preimageSingletonHomeomorph
      (FiberBundle.mem_baseSet_trivializationAt' b)
    exact ⟨⟨h.symm 0⟩, fun x k ↦ (HomotopyGroup.homeomorphEquiv h x).subsingleton⟩
  have hcomp : (⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).comp
      (ContinuousMap.subtypeVal (zeroSectionCompl F E)) = zeroSectionComplProj F E :=
    ContinuousMap.ext fun _ ↦ (zeroSectionComplProj_apply F E _).symm
  exact hπ.isNConnected_comp_iff.1 (hcomp ▸ isNConnected_zeroSectionComplProj E hF)

variable (F E) in
/-- **The Thom pair has no homology with local coefficients below the rank.** For a real vector
bundle `E → B` over an arbitrary base and every local coefficient system `L` on its total space,
with coefficients in any ring, the relative homology `Hₘ(E, E₀; L)` of the Thom pair vanishes for
every `m` smaller than the rank `dim F`. -/
theorem isZero_twistedHomology_thomPair {R : Type u} [Ring R]
    (L : LocalCoefficientSystem.{u, w, w} R (thomPair F E).fst) {m : ℕ} (hm : m < finrank ℝ F) :
    IsZero ((thomPair F E).twistedHomology L m) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (n := finrank ℝ F) (by lia)
  exact TopPair.isZero_twistedHomology_of_isNConnected
    (isNConnected_subtypeVal_zeroSectionCompl E hn) L (by lia)


section Cohomology

variable {R : Type u} [Ring R] (L : LocalCoefficientSystem.{u, w, w} R (thomPair F E).fst)
  [∀ x, Projective (L.obj x)] (k : Type*) [Ring k] [Linear k (ModuleCat.{w} R)]
  (M : ModuleCat.{w} R)

variable (F E) in
/-- **The Thom pair has no cohomology with local coefficients below the rank.** For a real vector
bundle `E → B` over an arbitrary base and every local coefficient system `L` with projective fibres
on its total space, the relative cohomology `Hᵐ(E, E₀; L, M)` of the Thom pair vanishes for every
`m` smaller than the rank `dim F` and every module of values `M`. -/
theorem isZero_twistedCohomology_thomPair {m : ℕ} (hm : m < finrank ℝ F) :
    IsZero ((thomPair F E).twistedCohomology L k M m) :=
  TopPair.isZero_twistedCohomology_of_isZero_twistedHomology (thomPair F E) L M m
    fun _ hj ↦ isZero_twistedHomology_thomPair F E L (hj.trans_lt hm)

variable (F E) in
/-- **The Kronecker map of the Thom pair is bijective in the rank degree.** For a real vector bundle
`E → B` of rank `r` over an arbitrary base and every local coefficient system `L` with projective
fibres on its total space, evaluation on homology `Hʳ(E, E₀; L, M) ⟶ Hom(Hᵣ(E, E₀; L), M)` is
bijective, for every module of values `M`: the relative homology vanishes below the rank. -/
theorem twistedKronecker_bijective_thomPair :
    Function.Bijective ((thomPair F E).twistedKronecker L k (M := M) (finrank ℝ F)) :=
  TopPair.twistedKronecker_bijective_of_projective_homology_lt (thomPair F E) L k M _
    fun _ hj ↦ (isZero_twistedHomology_thomPair F E L hj).projective

variable (F E) in
/-- **The cohomology of the Thom pair in the rank degree with local coefficients** is the dual of
its homology: for a local coefficient system `L` with projective fibres on the total space of a
real vector bundle of rank `r`, the Kronecker map is a `k`-linear equivalence
`Hʳ(E, E₀; L, M) ≃ₗ[k] (Hᵣ(E, E₀; L) ⟶ M)`. -/
def thomPairTwistedCohomologyFinrankEquiv :
    (thomPair F E).twistedCohomology L k M (finrank ℝ F) ≃ₗ[k]
      ((thomPair F E).twistedHomology L (finrank ℝ F) ⟶ M) :=
  LinearEquiv.ofBijective _ (twistedKronecker_bijective_thomPair F E L k M)

/-- The equivalence `TauCeti.thomPairTwistedCohomologyFinrankEquiv` is the Kronecker map. -/
@[simp]
lemma thomPairTwistedCohomologyFinrankEquiv_apply
    (α : (thomPair F E).twistedCohomology L k M (finrank ℝ F)) :
    thomPairTwistedCohomologyFinrankEquiv F E L k M α =
      (thomPair F E).twistedKronecker L k (finrank ℝ F) α :=
  (rfl)

end Cohomology

end TauCeti
