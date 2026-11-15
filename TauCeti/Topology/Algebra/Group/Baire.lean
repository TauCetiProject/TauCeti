/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Instances.Rat

/-!
# Pettis's category theorem and automatic continuity of group homomorphisms

In a topological group `G` that is a Baire space, **Pettis's theorem** asserts that for every
nonmeagre set `s` with the Baire property (`BaireMeasurableSet s`), the difference sets `s * s⁻¹`,
`s / s`, and `s⁻¹ * s` are neighbourhoods of the identity: `s` differs from a nonempty open set `U`
by a meagre set, and for every `x ∈ U * U⁻¹` the nonempty open intersection `U ∩ (x • U)` is
nonmeagre, hence meets `s ∩ (x • s)`.

From Pettis's theorem follows **automatic continuity** of Baire-measurable and Borel-measurable
homomorphisms: every group homomorphism `f : G → K` from a Baire topological group `G` to a
separable topological group `K` whose preimages of open sets have the Baire property is continuous.
Neither metrizability nor Hausdorffness of `K` is needed: for any open neighbourhood `W` of `1` in
`K`, the translates `d • W` along a countable dense subset `D ⊆ K` cover `K` (since each
`y • W⁻¹` is open and nonempty), so one preimage `f ⁻¹' (d • W)` is nonmeagre in `G`; translating
back by a single point of that preimage places it inside a translate of `f ⁻¹' (W⁻¹ * W)`, to which
Pettis's theorem applies because `W⁻¹ * W` is open.

Since every Borel set has the Baire property (`MeasurableSet.baireMeasurableSet`) and both
completely pseudometrizable (in particular Polish) spaces and locally compact Hausdorff spaces are
Baire spaces, every Borel-measurable homomorphism from a Polish or locally compact Hausdorff group
to a separable topological group with `OpensMeasurableSpace` (such as a Polish group or a separable
metrizable Borel group) is automatically continuous.

Finally, a `ℚ`-linear projection along a Hamel basis of `ℝ` over `ℚ` provides an additive
homomorphism `ℝ →+ ℝ` that is not continuous and hence not Borel-measurable, showing that the
measurability hypothesis cannot be dropped.

## Main results

* `BaireMeasurableSet.mul_inv_mem_nhds_one`, `BaireMeasurableSet.div_mem_nhds_one`,
  `BaireMeasurableSet.inv_mul_mem_nhds_one` (and additive forms): Pettis's theorem in a Baire
  topological group.
* `TauCeti.continuous_of_baireMeasurableSet_preimage_monoidHom` /
  `TauCeti.continuous_of_baireMeasurableSet_preimage_addMonoidHom`: a group homomorphism from a
  Baire topological group to a separable topological group whose preimages of open sets have the
  Baire property is continuous.
* `TauCeti.continuous_of_measurable_monoidHom` / `TauCeti.continuous_of_measurable_addMonoidHom`:
  every Borel-measurable group homomorphism from a Baire Borel topological group (in particular any
  Polish group or any locally compact Hausdorff group) to a separable topological group with
  measurable open sets is continuous.
* `TauCeti.exists_addMonoidHom_not_continuous_and_not_measurable`: there exists a discontinuous,
  non-Borel additive homomorphism `ℝ →+ ℝ`.

## References

* B. J. Pettis, *On continuity and openness of homomorphisms in topological groups*, Ann. of Math.
  (2) **52** (1950), 293–308.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Theorems 9.9 and 9.10.
* D. P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs 134, AMS,
  2007, Theorem D.11 and Lemmas D.15–D.16.
-/

public section

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped Pointwise

/-- Meagreness is invariant under eventual equality modulo the residual filter. -/
private theorem isMeagre_congr {X : Type*} [TopologicalSpace X] {s t : Set X} (hst : s =ᵇ t) :
    IsMeagre s ↔ IsMeagre t := by
  rw [IsMeagre, IsMeagre, ← eventually_mem_set, ← eventually_mem_set]
  exact eventually_congr hst.compl.mem_iff

namespace BaireMeasurableSet

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]
  {s : Set G}

/-- **Pettis's theorem**: in a Baire topological group, if `s` has the Baire property and is not
meagre, then `s * s⁻¹` is a neighbourhood of `1`. -/
@[to_additive /-- **Pettis's theorem**: in a Baire topological additive group, if `s` has the Baire
property and is not meagre, then `s + -s` is a neighbourhood of `0`. -/]
theorem mul_inv_mem_nhds_one (hs : BaireMeasurableSet s) (hnm : ¬ IsMeagre s) :
    s * s⁻¹ ∈ 𝓝 (1 : G) := by
  obtain ⟨U, hUo, hsU⟩ := hs.residualEq_isOpen
  have hUnm : ¬ IsMeagre U := fun hU => hnm ((isMeagre_congr hsU).2 hU)
  obtain ⟨u₀, hu₀⟩ := nonempty_of_not_isMeagre hUnm
  have hUU : U * U⁻¹ ∈ 𝓝 (1 : G) := by
    rw [← mul_inv_cancel u₀]
    exact (hUo.mul_right (s := U) (t := U⁻¹)).mem_nhds
      (mul_mem_mul hu₀ (Set.inv_mem_inv.2 hu₀))
  refine mem_of_superset hUU fun x hx => ?_
  rcases mem_mul.1 hx with ⟨a, ha, b, hb, rfl⟩
  rw [Set.mem_inv] at hb
  let φ : G ≃ₜ G := Homeomorph.mulLeft (a * b)
  have htrans : (φ '' s : Set G) =ᵇ (φ '' U : Set G) := by
    have hpre : φ.symm ⁻¹' s =ᵇ φ.symm ⁻¹' U :=
      hsU.filter_mono (tendsto_residual_of_isOpenMap φ.symm.continuous φ.symm.isOpenMap)
    simpa only [Homeomorph.preimage_symm] using hpre
  have hinter_eq : (s ∩ φ '' s : Set G) =ᵇ (U ∩ φ '' U : Set G) := hsU.inter htrans
  have hinter_open : IsOpen (U ∩ φ '' U) := hUo.inter (φ.isOpenMap U hUo)
  have hinter_ne : (U ∩ φ '' U).Nonempty :=
    ⟨a, ha, b⁻¹, hb, by simp [φ, mul_assoc]⟩
  have hinter_nm : ¬ IsMeagre (s ∩ φ '' s) := fun hm =>
    not_isMeagre_of_isOpen hinter_open hinter_ne ((isMeagre_congr hinter_eq).1 hm)
  obtain ⟨y, hys, z, hzs, hyz⟩ := nonempty_of_not_isMeagre hinter_nm
  have hzy : a * b * z = y := hyz
  refine mem_mul.2 ⟨y, hys, z⁻¹, Set.inv_mem_inv.2 hzs, ?_⟩
  simp [← hzy, mul_assoc]

/-- **Pettis's theorem** (division form): if `s` has the Baire property and is not meagre in a
Baire topological group, then `s / s` is a neighbourhood of `1`. -/
@[to_additive /-- **Pettis's theorem** (subtraction form): if `s` has the Baire property and is not
meagre in a Baire topological additive group, then `s - s` is a neighbourhood of `0`. -/]
theorem div_mem_nhds_one (hs : BaireMeasurableSet s) (hnm : ¬ IsMeagre s) :
    s / s ∈ 𝓝 (1 : G) := by
  simpa only [div_eq_mul_inv] using hs.mul_inv_mem_nhds_one hnm

/-- **Pettis's theorem** (`s⁻¹ * s` form): if `s` has the Baire property and is not meagre in a
Baire topological group, then `s⁻¹ * s` is a neighbourhood of `1`. -/
@[to_additive /-- **Pettis's theorem** (`-s + s` form): if `s` has the Baire property and is not
meagre in a Baire topological additive group, then `-s + s` is a neighbourhood of `0`. -/]
theorem inv_mul_mem_nhds_one (hs : BaireMeasurableSet s) (hnm : ¬ IsMeagre s) :
    s⁻¹ * s ∈ 𝓝 (1 : G) := by
  have hpre_inv : ∀ t : Set G, (Homeomorph.inv G) ⁻¹' t = t⁻¹ := fun t => by
    ext x
    simp [Set.mem_inv]
  have hinv_bm : BaireMeasurableSet s⁻¹ := by
    rw [← hpre_inv s]
    exact hs.preimage (Homeomorph.inv G).continuous (Homeomorph.inv G).isOpenMap
  have hinv_nm : ¬ IsMeagre s⁻¹ := fun hm => hnm <| by
    have hpre := hm.preimage_of_isOpenMap (Homeomorph.inv G).continuous (Homeomorph.inv G).isOpenMap
    rwa [hpre_inv, inv_inv] at hpre
  simpa only [inv_inv] using hinv_bm.mul_inv_mem_nhds_one hinv_nm

end BaireMeasurableSet

namespace TauCeti

section AutomaticContinuity

variable {G K F : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BaireSpace G]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [SeparableSpace K]
  [FunLike F G K] [MonoidHomClass F G K]

/-- **Automatic continuity of Baire-measurable homomorphisms.** Every group homomorphism from a
Baire topological group `G` to a separable topological group `K` whose preimages of open sets have
the Baire property is continuous. Neither metrizability nor Hausdorffness of `K` is needed. -/
@[to_additive /-- **Automatic continuity of Baire-measurable additive homomorphisms.** Every
additive group homomorphism from a Baire topological additive group `G` to a separable topological
additive group `K` whose preimages of open sets have the Baire property is continuous. Neither
metrizability nor Hausdorffness of `K` is needed. -/]
theorem continuous_of_baireMeasurableSet_preimage_monoidHom (f : F)
    (hf : ∀ U : Set K, IsOpen U → BaireMeasurableSet (f ⁻¹' U)) :
    Continuous f := by
  refine continuous_of_continuousAt_one f (continuousAt_def.2 ?_)
  rw [map_one]
  intro V hV
  -- Choose an open identity neighbourhood `U` with `U * U⁻¹ ⊆ V`, then an open `W ∋ 1` with
  -- `W⁻¹ * W ⊆ U`.
  have hmul_inv : Continuous fun p : K × K => p.1 * p.2⁻¹ := continuous_fst.mul continuous_snd.inv
  have hV11 : (fun p : K × K => p.1 * p.2⁻¹) ⁻¹' V ∈ 𝓝 ((1 : K), (1 : K)) :=
    hmul_inv.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨U₁, hU₁, U₂, hU₂, hUsub⟩ := mem_nhds_prod_iff.1 hV11
  obtain ⟨U, hUU₁, hUo, h1U⟩ := mem_nhds_iff.1 (inter_mem hU₁ hU₂)
  have hUU_sub : U * U⁻¹ ⊆ V := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_inv] at hb
    simpa using hUsub (mk_mem_prod (hUU₁ ha).1 (hUU₁ hb).2)
  have hinv_mul : Continuous fun p : K × K => p.1⁻¹ * p.2 := continuous_fst.inv.mul continuous_snd
  have hU11 : (fun p : K × K => p.1⁻¹ * p.2) ⁻¹' U ∈ 𝓝 ((1 : K), (1 : K)) :=
    hinv_mul.continuousAt.preimage_mem_nhds (by simpa using hUo.mem_nhds h1U)
  obtain ⟨W₁, hW₁, W₂, hW₂, hWsub⟩ := mem_nhds_prod_iff.1 hU11
  obtain ⟨W, hWW, hWo, h1W⟩ := mem_nhds_iff.1 (inter_mem hW₁ hW₂)
  have hWW_sub : W⁻¹ * W ⊆ U := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_inv] at ha
    simpa using hWsub (mk_mem_prod (hWW ha).1 (hWW hb).2)
  -- Cover `K` by countably many translates of `W` along a countable dense subset `D`.
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense K
  have hcover : (⋃ d ∈ D, f ⁻¹' ((d * ·) '' W)) = univ := by
    refine eq_univ_iff_forall.2 fun g => mem_iUnion₂.2 ?_
    have hop : IsOpen ((f g * ·) '' W⁻¹) := (Homeomorph.mulLeft (f g)).isOpenMap W⁻¹ hWo.inv
    have hne : ((f g * ·) '' W⁻¹).Nonempty := ⟨f g, 1, Set.mem_inv.2 (by simpa using h1W), by simp⟩
    obtain ⟨d, hdW, hdD⟩ := hDd.inter_open_nonempty _ hop hne
    rcases hdW with ⟨w, hw, rfl⟩
    rw [Set.mem_inv] at hw
    exact ⟨f g * w, hdD, w⁻¹, hw, by simp [mul_assoc]⟩
  -- In the nonempty Baire space `G`, one of the countably many pieces must be nonmeagre.
  have hnot_all : ¬ ∀ d ∈ D, IsMeagre (f ⁻¹' ((d * ·) '' W)) := fun hall => by
    have huniv : IsMeagre (univ : Set G) := hcover ▸ isMeagre_biUnion hDc hall
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty huniv
  push Not at hnot_all
  obtain ⟨d, _, hd_nm⟩ := hnot_all
  obtain ⟨g₀, w₀, hw₀, hfg₀⟩ := nonempty_of_not_isMeagre hd_nm
  -- Translate that piece back to `1`: `f ⁻¹' (d • W) ⊆ g₀ • f ⁻¹' U`, so `f ⁻¹' U` is nonmeagre.
  have hsub_tr : f ⁻¹' ((d * ·) '' W) ⊆ (Homeomorph.mulLeft g₀) '' (f ⁻¹' U) := by
    rintro g ⟨w, hw, hfg⟩
    have hfg₀' : d * w₀ = f g₀ := hfg₀
    have hfg' : d * w = f g := hfg
    refine ⟨g₀⁻¹ * g, ?_, by simp⟩
    rw [mem_preimage, map_mul, map_inv, ← hfg₀', ← hfg']
    have heq : (d * w₀)⁻¹ * (d * w) = w₀⁻¹ * w := by
      simp [mul_inv_rev, mul_assoc]
    rw [heq]
    exact hWW_sub (mul_mem_mul (Set.inv_mem_inv.2 hw₀) hw)
  have hUnm : ¬ IsMeagre (f ⁻¹' U) := fun hm => hd_nm <| by
    let ψ : G ≃ₜ G := Homeomorph.mulLeft g₀
    have hpre : f ⁻¹' ((d * ·) '' W) ⊆ ψ.symm ⁻¹' (f ⁻¹' U) := by
      simpa only [Homeomorph.preimage_symm] using hsub_tr
    exact IsMeagre.mono hpre (hm.preimage_of_isOpenMap ψ.symm.continuous ψ.symm.isOpenMap)
  refine mem_of_superset ((hf U hUo).mul_inv_mem_nhds_one hUnm) ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [Set.mem_inv] at hb
  have hfb : f b = (f b⁻¹)⁻¹ := by simp
  rw [mem_preimage, map_mul, hfb]
  exact hUU_sub (mul_mem_mul ha (Set.inv_mem_inv.2 hb))

/-- **Automatic continuity of Borel-measurable group homomorphisms.** Every Borel-measurable group
homomorphism from a Baire Borel topological group (in particular any Polish group or any locally
compact Hausdorff group) to a separable topological group with `OpensMeasurableSpace` (such as a
Polish group or a separable metrizable Borel group) is continuous. -/
@[to_additive /-- **Automatic continuity of Borel-measurable additive group homomorphisms.** Every
Borel-measurable additive group homomorphism from a Baire Borel topological additive group (in
particular any Polish additive group or any locally compact Hausdorff additive group) to a
separable topological additive group with `OpensMeasurableSpace` is continuous. -/]
theorem continuous_of_measurable_monoidHom [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace K] [OpensMeasurableSpace K] (f : F) (hf : Measurable f) :
    Continuous f :=
  continuous_of_baireMeasurableSet_preimage_monoidHom f fun _ hU =>
    (hf hU.measurableSet).baireMeasurableSet

end AutomaticContinuity

/-- **Measurability cannot be dropped in automatic continuity.** A `ℚ`-linear coordinate projection
along a Hamel basis of `ℝ` over `ℚ` is an additive homomorphism `ℝ →+ ℝ` that is not `ℝ`-linear,
hence neither continuous nor Borel-measurable. -/
theorem exists_addMonoidHom_not_continuous_and_not_measurable :
    ∃ f : ℝ →+ ℝ, ¬ Continuous f ∧ ¬ Measurable f := by
  let b := Module.Basis.ofVectorSpace ℚ ℝ
  -- Since `ℝ` is uncountable and `ℚ` is countable, the Hamel basis index type has at least two
  -- distinct elements.
  have hnt : Nontrivial (Module.Basis.ofVectorSpaceIndex ℚ ℝ) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Countable (Module.Basis.ofVectorSpaceIndex ℚ ℝ →₀ ℚ) :=
      Finsupp.equivFunOnFinite.countable_iff.2 inferInstance
    have hcnt : Countable ℝ := b.repr.toEquiv.countable_iff.2 this
    exact not_countable hcnt
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Module.Basis.ofVectorSpaceIndex ℚ ℝ)
  let L : ℝ →ₗ[ℚ] ℝ := (Algebra.linearMap ℚ ℝ).comp (b.coord i)
  let f : ℝ →+ ℝ := L.toAddMonoidHom
  have hfi : f (b i) = 1 := by
    simp [f, L, Module.Basis.coord_apply, b.repr_self]
  have hfj : f (b j) = 0 := by
    simp [f, L, Module.Basis.coord_apply, b.repr_self, hij.symm]
  have hnc : ¬ Continuous f := fun hc => by
    have hmul : ∀ r y : ℝ, f (r * y) = r * f y := fun r y => by
      have heq : (fun x : ℝ => f (x * y)) = fun x : ℝ => x * f y := by
        refine Rat.denseRange_cast.equalizer (hc.comp (continuous_mul_const y))
          (continuous_mul_const (f y)) ?_
        ext q
        simpa only [f, Function.comp_apply, LinearMap.toAddMonoidHom_coe, Rat.smul_def] using
          L.map_smul q y
      exact congr_fun heq r
    have hbj : b j = 0 := by
      calc
        b j = b j * f (b i) := by rw [hfi, mul_one]
        _ = f (b j * b i) := (hmul (b j) (b i)).symm
        _ = f (b i * b j) := by rw [mul_comm]
        _ = b i * f (b j) := hmul (b i) (b j)
        _ = 0 := by rw [hfj, mul_zero]
    exact b.ne_zero j hbj
  exact ⟨f, hnc, fun hm => hnc (continuous_of_measurable_addMonoidHom f hm)⟩

end TauCeti
