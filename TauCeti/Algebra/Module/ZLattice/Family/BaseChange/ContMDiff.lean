/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.Manifold

/-!
# Smooth base change of period quotients

For a `C^n` family of full period lattices `P` over `Y` and a `C^n` map `f : Z → Y`,
the canonical map from the period quotient for `P ∘ f` to that for `P` is `C^n`.
Moreover, a map into the pulled-back family is `C^n` exactly when its projection to `Z`
and its composite with this canonical map are `C^n`. Thus the topological pullback
comparison has the smooth universal property, with the existing quotient atlases.
For `𝕜 = ℂ` and `1 ≤ n`, with compatible complex manifold structures, these statements
give holomorphic base change for varying period lattices; they do not assert holomorphic
local triviality with a fixed fibre.

The universal property requires no continuity hypothesis on the map being tested.
Local inverses of the period covering in the original family recover smooth vector
representatives from its second component. These, paired with its first component,
give local smooth representatives in the pulled-back family.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Chapter 8 (families of complex tori given by period matrices).
-/

public section

open Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EY EZ : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
  {HY HZ : Type*} [TopologicalSpace HY] [TopologicalSpace HZ]
  {I : ModelWithCorners 𝕜 EY HY} {J : ModelWithCorners 𝕜 EZ HZ}
  {Y Z : Type*} [TopologicalSpace Y] [ChartedSpace HY Y] [T2Space Y] [LocallyCompactSpace Y]
  [TopologicalSpace Z] [ChartedSpace HZ Z] [T2Space Z] [LocallyCompactSpace Z]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace 𝕜 E] (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y] [IsManifold J n Z]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l) (f : Z → Y) (hf : ContMDiff J I n f)

include hf

/-- A `C^n` map of bases induces a `C^n` map of period quotients. For `𝕜 = ℂ` and
`1 ≤ n`, with complex manifold structures on `Y` and `Z` modeled by `I` and `J`,
this is the holomorphic map `[z, v] ↦ [f z, v]` for the pulled-back period family. -/
theorem contMDiff_torusFamilyBaseChangeMap :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf).continuous) (fun z ↦ hinj (f z))
    ContMDiff (J.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) n (torusFamilyBaseChangeMap P f) := by
  let : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (DiscreteTopology (LinearMap.range (P (f z))))
  let : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (IsZLattice ℝ (LinearMap.range (P (f z))))
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyChartedSpace (H := HZ) (P ∘ f)
    (fun l ↦ ((hP l).comp hf).continuous) (fun z ↦ hinj (f z))
  refine ((isLocalDiffeomorph_torusFamily_mk (P ∘ f) (fun z ↦ hinj (f z))
    (fun l ↦ (hP l).comp hf)).contMDiff_comp_iff Quotient.mk_surjective le_rfl).1 ?_
  have hcomm : torusFamilyBaseChangeMap P f ∘ Quotient.mk _ =
      Quotient.mk _ ∘ Prod.map f id := by
    funext ⟨z, v⟩
    exact torusFamilyBaseChangeMap_mk P f z v
  rw [hcomm]
  exact (isLocalDiffeomorph_torusFamily_mk P hinj hP).contMDiff.comp
    (hf.prodMap (contMDiff_id (I := 𝓘(𝕜, E))))

variable {EW : Type*} [NormedAddCommGroup EW] [NormedSpace 𝕜 EW]
  {HW : Type*} [TopologicalSpace HW] {K : ModelWithCorners 𝕜 EW HW}
  {W : Type*} [TopologicalSpace W] [ChartedSpace HW W]

/-- The pointwise smooth universal property of base change: a map into the pulled-back
period quotient is `C^n` at a point exactly when both its base component and its map to
the original family are `C^n` there. Continuity of the tested map is not assumed. -/
theorem contMDiffAt_torusFamilyBaseChange_iff
    (u : letI := periodAddAction (P ∘ f); W → AddAction.orbitRel.Quotient Λ (Z × E)) (x : W) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf).continuous) (fun z ↦ hinj (f z))
    ContMDiffAt K (J.prod 𝓘(𝕜, E)) n u x ↔
      ContMDiffAt K J n (torusFamilyProjection (P ∘ f) ∘ u) x ∧
      ContMDiffAt K (I.prod 𝓘(𝕜, E)) n (torusFamilyBaseChangeMap P f ∘ u) x := by
  let : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (DiscreteTopology (LinearMap.range (P (f z))))
  let : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (IsZLattice ℝ (LinearMap.range (P (f z))))
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyChartedSpace (H := HZ) (P ∘ f)
    (fun l ↦ ((hP l).comp hf).continuous) (fun z ↦ hinj (f z))
  constructor
  · intro hu
    exact ⟨(contMDiff_torusFamilyProjection (P ∘ f) (fun z ↦ hinj (f z))
      (fun l ↦ (hP l).comp hf)).contMDiffAt.comp x hu,
      (contMDiff_torusFamilyBaseChangeMap P hinj hP f hf).contMDiffAt.comp x hu⟩
  · rintro ⟨ha, hb⟩
    -- Lift the second component locally through the original period covering.
    obtain ⟨v, hv⟩ := Quotient.mk_surjective (torusFamilyBaseChangeMap P f (u x))
    have hq := isLocalDiffeomorph_torusFamily_mk P hinj hP v
    have hs : ContMDiffAt K (I.prod 𝓘(𝕜, E)) n
        (hq.localInverse ∘ (torusFamilyBaseChangeMap P f ∘ u)) x := by
      apply ContMDiffAt.comp x _ hb
      rw [comp_apply, ← hv]
      exact hq.contMDiffAt_localInverse
    have hlocal := (hq.localInverse_open_source.mem_nhds hq.localInverse_mem_source)
    rw [hv] at hlocal
    have heq : u =ᶠ[𝓝 x] fun w ↦ Quotient.mk (AddAction.orbitRel Λ (Z × E))
        (torusFamilyProjection (P ∘ f) (u w),
          (hq.localInverse (torusFamilyBaseChangeMap P f (u w))).2) := by
      filter_upwards [hb.continuousAt.preimage_mem_nhds hlocal] with w hw
      have hright := hq.localInverse_right_inv hw
      simp only [comp_apply] at hright
      have hbase := congrArg (torusFamilyProjection P) hright
      simp only [torusFamilyProjection_mk, torusFamilyProjection_baseChangeMap] at hbase
      -- The existing topological comparison proves uniqueness from the two projections.
      apply (torusFamilyBaseChangeHomeomorph P f (fun l ↦ (hP l).continuous)
        hf.continuous).injective
      apply Subtype.ext
      simp only [coe_torusFamilyBaseChangeHomeomorph, torusFamilyProjection_mk,
        torusFamilyBaseChangeMap_mk]
      refine Prod.ext rfl (hright.symm.trans ?_)
      exact congrArg (Quotient.mk _) (Prod.ext hbase rfl)
    exact ((isLocalDiffeomorph_torusFamily_mk (P ∘ f) (fun z ↦ hinj (f z))
      (fun l ↦ (hP l).comp hf)).contMDiff.contMDiffAt.comp x
        (ha.prodMk hs.snd)).congr_of_eventuallyEq heq

/-- The smooth universal property of base change for period quotients. For `𝕜 = ℂ` and
`1 ≤ n`, with compatible complex manifold structures on `W`, `Y`, and `Z`, this
characterizes holomorphic maps into the pulled-back family by their two components. -/
theorem contMDiff_torusFamilyBaseChange_iff
    (u : letI := periodAddAction (P ∘ f); W → AddAction.orbitRel.Quotient Λ (Z × E)) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf).continuous) (fun z ↦ hinj (f z))
    ContMDiff K (J.prod 𝓘(𝕜, E)) n u ↔
      ContMDiff K J n (torusFamilyProjection (P ∘ f) ∘ u) ∧
      ContMDiff K (I.prod 𝓘(𝕜, E)) n (torusFamilyBaseChangeMap P f ∘ u) := by
  exact ⟨fun hu ↦ ⟨fun x ↦ ((contMDiffAt_torusFamilyBaseChange_iff P hinj hP f hf u x).1
    (hu x)).1, fun x ↦ ((contMDiffAt_torusFamilyBaseChange_iff P hinj hP f hf u x).1 (hu x)).2⟩,
    fun ⟨ha, hb⟩ x ↦ (contMDiffAt_torusFamilyBaseChange_iff P hinj hP f hf u x).2 ⟨ha x, hb x⟩⟩

/-- A compatible pair of `C^n` maps to the new base and the original family lifts to a
`C^n` map into the pulled-back family through the canonical pullback homeomorphism.
The literal pullback needs no independently supplied manifold structure. -/
theorem contMDiff_torusFamilyBaseChangeHomeomorph_symm
    (a : W → Z)
    (b : letI := periodAddAction P; W → AddAction.orbitRel.Quotient Λ (Y × E))
    (hab : ∀ w, torusFamilyProjection P (b w) = f (a w)) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf).continuous) (fun z ↦ hinj (f z))
    ContMDiff K J n a → ContMDiff K (I.prod 𝓘(𝕜, E)) n b →
      ContMDiff K (J.prod 𝓘(𝕜, E)) n
        (fun w ↦ (torusFamilyBaseChangeHomeomorph P f (fun l ↦ (hP l).continuous)
          hf.continuous).symm ⟨(a w, b w), hab w⟩) := by
  let : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (DiscreteTopology (LinearMap.range (P (f z))))
  let : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
    (IsZLattice ℝ (LinearMap.range (P (f z))))
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyChartedSpace (H := HZ) (P ∘ f)
    (fun l ↦ ((hP l).comp hf).continuous) (fun z ↦ hinj (f z))
  intro ha hb
  apply (contMDiff_torusFamilyBaseChange_iff P hinj hP f hf _).2
  have hcomp : ∀ w,
      (torusFamilyProjection (P ∘ f)
          ((torusFamilyBaseChangeHomeomorph P f (fun l ↦ (hP l).continuous)
            hf.continuous).symm ⟨(a w, b w), hab w⟩),
        torusFamilyBaseChangeMap P f
          ((torusFamilyBaseChangeHomeomorph P f (fun l ↦ (hP l).continuous)
            hf.continuous).symm ⟨(a w, b w), hab w⟩)) = (a w, b w) := by
    intro w
    have h := congrArg Subtype.val ((torusFamilyBaseChangeHomeomorph P f
      (fun l ↦ (hP l).continuous) hf.continuous).apply_symm_apply ⟨(a w, b w), hab w⟩)
    simpa only [coe_torusFamilyBaseChangeHomeomorph] using h
  exact ⟨ha.congr (fun w ↦ congrArg Prod.fst (hcomp w)),
    hb.congr (fun w ↦ congrArg Prod.snd (hcomp w))⟩

/-- A compatible pair of `C^n` maps to the new base and the original family lifts to a
`C^n` map into the pulled-back family through the algebraic pullback equivalence
`TauCeti.torusFamilyBaseChangeEquiv`. -/
theorem contMDiff_torusFamilyBaseChangeEquiv_symm
    (a : W → Z)
    (b : letI := periodAddAction P; W → AddAction.orbitRel.Quotient Λ (Y × E))
    (hab : ∀ w, torusFamilyProjection P (b w) = f (a w)) :
    letI : ∀ z, DiscreteTopology (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (DiscreteTopology (LinearMap.range (P (f z))))
    letI : ∀ z, IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) := fun z ↦ inferInstanceAs
      (IsZLattice ℝ (LinearMap.range (P (f z))))
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyChartedSpace (H := HY) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyChartedSpace (H := HZ) (P ∘ f)
      (fun l ↦ ((hP l).comp hf).continuous) (fun z ↦ hinj (f z))
    ContMDiff K J n a → ContMDiff K (I.prod 𝓘(𝕜, E)) n b →
      ContMDiff K (J.prod 𝓘(𝕜, E)) n
        (fun w ↦ (torusFamilyBaseChangeEquiv P f).symm ⟨(a w, b w), hab w⟩) := by
  simpa only [← coe_torusFamilyBaseChangeHomeomorph_symm P f (fun l ↦ (hP l).continuous)
    hf.continuous] using contMDiff_torusFamilyBaseChangeHomeomorph_symm P hinj hP f hf a b hab

end TauCeti
