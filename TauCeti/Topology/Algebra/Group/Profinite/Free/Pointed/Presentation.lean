/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank

/-!
# Presentations of pro-`p` groups by free pro-`p` groups on pointed profinite spaces

A subset `s` of a profinite group `G` converging to `1` becomes, once `1` is added, a pointed
profinite space `(insert 1 s, 1)`. The **presentation of `G` on `s`** is the continuous
homomorphism from the free pro-`p` group on this pointed space, `TauCeti.freeProPInsertOne p s`,
to `G` that extends the inclusion of `insert 1 s`. It is surjective exactly when `s` generates `G`
topologically, so every pro-`p` group is presented by the free pro-`p` group on a pointed
profinite space, since every profinite group has a generating set converging to `1`.

The presentation on `s` is **minimal** when its kernel lies in the Frattini subgroup of the free
pro-`p` group. This is the condition under which a continuous homomorphic section makes the
presentation an isomorphism (`TauCeti.IsProP.continuousMulEquivOfLeftInverse`); for presentations
on a finite type it is the condition that the number of generators be the topological generator
rank (`TauCeti.presentedProP.subset_proPFrattini_iff_card_eq`). Every pro-`p` group has a minimal
presentation, on a dual family of a basis of its continuous `𝔽_p`-dual, and the free pro-`p` group
of a minimal presentation has the same topological generator rank as `G`.

## Main definitions

* `TauCeti.freeProPInsertOne`: the free pro-`p` group on the pointed space `(insert 1 s, 1)`.
* `TauCeti.IsProP.presentation`: the continuous homomorphism from it to `G` extending the inclusion.

## Main results

* `TauCeti.topologicalGeneratorRank_freeProPInsertOne_le`: the free pro-`p` group on
  `(insert 1 s, 1)` has topological generator rank at most the cardinality of `s`.
* `TauCeti.IsProP.presentation_surjective_iff`: the presentation on `s` is surjective exactly when
  `s` generates `G` topologically.
* `TauCeti.IsProP.exists_convergesToOne_presentation_surjective`: **every pro-`p` group is a
  quotient of the free pro-`p` group on a pointed profinite space.**
* `TauCeti.IsProP.exists_convergesToOne_presentation_surjective_ker_le_proPFrattini`: **every
  pro-`p` group has a minimal presentation**, whose kernel lies in the Frattini subgroup of the
  free pro-`p` group and whose free pro-`p` group has the topological generator rank of `G`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.8 and 3.3.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Section III.9.
-/

public section

namespace TauCeti

open Filter Topology

open scoped Cardinal

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-- The free pro-`p` group on the pointed space `(insert 1 s, 1)` cut out of a topological group
`G` by a subset `s`. When `s` converges to `1` in a profinite group `G`, the subspace `insert 1 s`
is a profinite space (`TauCeti.ConvergesToOne.isClosed_insert_one`), and this is the free pro-`p`
group `F_p(insert 1 s, 1)` on a pointed profinite space. -/
abbrev freeProPInsertOne (p : ℕ) (s : Set G) : Type u :=
  freeProCPointed (finiteGroupClassP.{u} p) (⟨1, Set.mem_insert 1 s⟩ : ↥(insert (1 : G) s))

/-- The free pro-`p` group on `(insert 1 s, 1)`, for a set `s` converging to `1`, has topological
generator rank at most the cardinality of `s`: the generators attached to the points of `s`
converge to `1` and generate it topologically. -/
theorem topologicalGeneratorRank_freeProPInsertOne_le {s : Set G} (hs : ConvergesToOne s) :
    topologicalGeneratorRank (freeProPInsertOne p s) ≤ #s := by
  set x₀ : ↥(insert (1 : G) s) := ⟨1, Set.mem_insert 1 _⟩
  set e : s → ↥(insert (1 : G) s) := fun x ↦ ⟨x, Set.mem_insert_of_mem 1 x.2⟩
  have he : Tendsto e cofinite (𝓝 x₀) := tendsto_subtype_rng.mpr hs.tendsto_coe
  have hconv : Tendsto (fun x ↦ freeProCPointed.of (finiteGroupClassP.{u} p) x₀ (e x))
      cofinite (𝓝 1) := by
    rw [← freeProCPointed.of_basePoint (finiteGroupClassP.{u} p) x₀]
    exact ((freeProCPointed.continuous_of _ x₀).tendsto x₀).comp he
  have hgen : (Subgroup.closure
      (Set.range fun x ↦ freeProCPointed.of (finiteGroupClassP.{u} p) x₀ (e x))).topologicalClosure
        = ⊤ := by
    refine top_unique ?_
    rw [← freeProCPointed.topologicalClosure_closure_range_of_eq_top (finiteGroupClassP.{u} p) x₀]
    refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).mpr ?_)
      (Subgroup.isClosed_topologicalClosure _)
    rintro _ ⟨x, rfl⟩
    rcases x.2 with hx1 | hx
    · have hx₀ : x = x₀ := Subtype.ext hx1
      rw [hx₀, freeProCPointed.of_basePoint]
      exact one_mem _
    · exact Subgroup.le_topologicalClosure _ (Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩)
  exact (topologicalGeneratorRank_le hconv.convergesToOne_range hgen).trans Cardinal.mk_range_le

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

namespace IsProP

variable (hG : IsProP p G) (s : Set G)

/-- **The presentation of a pro-`p` group `G` on a subset `s`**: the continuous homomorphism from
the free pro-`p` group on the pointed space `(insert 1 s, 1)` to `G` that extends the inclusion
of `insert 1 s` into `G`. -/
noncomputable def presentation : freeProPInsertOne p s →ₜ* G :=
  freeProCPointed.lift (isProC_finiteGroupClassP_iff.mpr hG) Subtype.val continuous_subtype_val rfl

/-- The presentation sends the generator attached to a point of `insert 1 s` to that point. -/
@[simp]
theorem presentation_of (x : ↥(insert (1 : G) s)) :
    hG.presentation s (freeProCPointed.of _ _ x) = x :=
  freeProCPointed.lift_of _ _ _ _ x

/-- The presentation composed with the generator map is the inclusion of `insert 1 s`. -/
theorem presentation_comp_of :
    ⇑(hG.presentation s) ∘ freeProCPointed.of (finiteGroupClassP.{u} p) _ =
      (Subtype.val : ↥(insert (1 : G) s) → G) :=
  funext (hG.presentation_of s)

/-- **The presentation on `s` is surjective exactly when `s` generates `G` topologically.** -/
theorem presentation_surjective_iff :
    Function.Surjective (hG.presentation s) ↔ (Subgroup.closure s).topologicalClosure = ⊤ := by
  constructor
  · intro hsurj
    have h := topologicalClosure_closure_image_eq_top
      (freeProCPointed.topologicalClosure_closure_range_of_eq_top (finiteGroupClassP.{u} p) _)
      (f := (hG.presentation s : freeProPInsertOne p s →* G)) (hG.presentation s).continuous
      hsurj.denseRange
    rwa [← Set.range_comp, MonoidHom.coe_ofClass, presentation_comp_of, Subtype.range_coe,
      Subgroup.closure_insert_one] at h
  · intro hgen
    refine freeProCPointed.lift_surjective _ _ _ ?_
    rw [Subtype.range_coe, Subgroup.closure_insert_one]
    exact Subgroup.dense_iff_topologicalClosure_eq_top.mpr hgen

/-- **Every pro-`p` group is a quotient of the free pro-`p` group on a pointed profinite space**:
some subset `s` of `G` converging to `1` has surjective presentation. -/
theorem exists_convergesToOne_presentation_surjective :
    ∃ s : Set G, ConvergesToOne s ∧ Function.Surjective (hG.presentation s) :=
  let ⟨s, hs, hgen⟩ := exists_convergesToOne_topologicallyGenerates (G := G)
  ⟨s, hs, (hG.presentation_surjective_iff s).mpr hgen⟩

variable [Fact p.Prime]

section DualFamily

variable {ι : Type u} {g : ι → G} (hg : Tendsto g cofinite (𝓝 1))
  (b : Module.Basis ι (ZMod p) (continuousZModDual p G))
  (hb : ∀ i (x : continuousZModDual p G),
    b.coord i x = Multiplicative.toAdd (Additive.toMul x (g i)))

include hg hb in
/-- **Characters factor through the presentation on a dual family.** Let `g` tend to `1` and be a
dual family of a basis `b` of the continuous `𝔽_p`-dual of `G`. Every continuous `𝔽_p`-character
of the free pro-`p` group on `(insert 1 (range g), 1)` is a continuous `𝔽_p`-character of `G`
composed with the presentation on `range g`. This is what makes that presentation minimal. -/
theorem exists_comp_presentation_eq
    (ψ : freeProPInsertOne p (Set.range g) →ₜ* Multiplicative (ZMod p)) :
    ∃ χ : G →ₜ* Multiplicative (ZMod p), χ.comp (hG.presentation (Set.range g)) = ψ := by
  classical
  -- `ψ` vanishes on the generators attached to all but finitely many `g i`, so its values on them
  -- are the coordinates of a vector `χ` of the dual of `G`, and `χ` composed with the presentation
  -- agrees with `ψ` on every generator.
  set x₀ : ↥(insert (1 : G) (Set.range g)) := ⟨1, Set.mem_insert 1 _⟩
  set e : ι → ↥(insert (1 : G) (Set.range g)) := fun i ↦ ⟨g i, Set.mem_insert_of_mem 1 ⟨i, rfl⟩⟩
  have he : Tendsto e cofinite (𝓝 x₀) := tendsto_subtype_rng.mpr hg
  -- `ψ` is trivial on the generators attached to all but finitely many `g i`.
  have hψ : Tendsto (fun i ↦ ψ (freeProCPointed.of _ x₀ (e i))) cofinite (𝓝 1) := by
    have h1 : ψ (freeProCPointed.of (finiteGroupClassP.{u} p) x₀ x₀) = 1 := by
      rw [freeProCPointed.of_basePoint, map_one]
    rw [← h1]
    exact ((ψ.continuous.comp (freeProCPointed.continuous_of _ x₀)).tendsto x₀).comp he
  rw [nhds_discrete, tendsto_pure, eventually_cofinite] at hψ
  let c : ι →₀ ZMod p := Finsupp.ofSupportFinite
    (fun i ↦ Multiplicative.toAdd (ψ (freeProCPointed.of _ x₀ (e i))))
    (by simpa only [Function.support, ne_eq, toAdd_eq_zero] using hψ)
  refine ⟨Additive.toMul (b.repr.symm c), freeProCPointed.hom_ext fun x ↦ ?_⟩
  rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, presentation_of]
  rcases x.2 with hx1 | ⟨i, hi⟩
  · have hx₀ : x = x₀ := Subtype.ext hx1
    rw [hx1, map_one, hx₀, freeProCPointed.of_basePoint, map_one]
  · have hx : x = e i := Subtype.ext hi.symm
    rw [← hi, hx]
    apply Multiplicative.toAdd.injective
    rw [← hb i, Module.Basis.coord_apply, LinearEquiv.apply_symm_apply]
    simp only [c, x₀, Finsupp.ofSupportFinite_coe]

end DualFamily

/-- **Every pro-`p` group has a minimal presentation by the free pro-`p` group on a pointed
profinite space.** Some subset `s` of `G` converging to `1` has surjective presentation whose
kernel lies in the Frattini subgroup of the free pro-`p` group on `(insert 1 s, 1)`, and that free
pro-`p` group has the same topological generator rank as `G`. The subset is a dual family of a
basis of the continuous `𝔽_p`-dual of `G`. -/
theorem exists_convergesToOne_presentation_surjective_ker_le_proPFrattini :
    ∃ s : Set G, ConvergesToOne s ∧ Function.Surjective (hG.presentation s) ∧
      (hG.presentation s).ker ≤ proPFrattini p (freeProPInsertOne p s) ∧
      topologicalGeneratorRank (freeProPInsertOne p s) = topologicalGeneratorRank G := by
  classical
  let b := Module.Basis.ofVectorSpace (ZMod p) (continuousZModDual p G)
  obtain ⟨g, hg, hgen, hb⟩ := hG.exists_tendsto_cofinite_topologicallyGenerates_coord_eq b
  have hsurj : Function.Surjective (hG.presentation (Set.range g)) :=
    (hG.presentation_surjective_iff _).mpr hgen
  refine ⟨Set.range g, hg.convergesToOne_range, hsurj,
    (hG.presentation _).ker_le_proPFrattini_of_forall_exists_comp_eq
      (hG.exists_comp_presentation_eq hg b hb),
    le_antisymm ((topologicalGeneratorRank_freeProPInsertOne_le hg.convergesToOne_range).trans
      (Cardinal.mk_range_le.trans_eq ?_))
      (topologicalGeneratorRank_le_of_surjective
        (hG.presentation (Set.range g) : freeProPInsertOne p (Set.range g) →* G)
        (hG.presentation _).continuous hsurj)⟩
  rw [b.mk_eq_rank'', hG.topologicalGeneratorRank_eq_rank_continuousZModDual]

end IsProP

end TauCeti
