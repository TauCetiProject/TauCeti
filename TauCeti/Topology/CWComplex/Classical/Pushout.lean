/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.RelativeCellComplex.Pushout
public import TauCeti.Topology.CWComplex.Abstract.Classical
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex

/-!
# Gluing a relative CW complex to a space

Let `C` be a classical relative CW complex with base `D` in a Hausdorff space, and let
`a : D → Z` be a continuous map to a space `Z`. The adjunction space `Z ∪_a C`
(`TauCeti.adjunctionSpace`) is the pushout in `TopCat` of `a` and the inclusion of `D` into `C`,
with its quotient topology. This file shows
that it is a relative CW complex over `Z`, whose cells are those of `C`:

* the inclusion `Z → Z ∪_a C` is a closed embedding (`TauCeti.isClosedEmbedding_pushout_inl`);
* `Z ∪_a C` is Hausdorff when `Z` is (`TauCeti.t2Space_adjunctionSpace`);
* `Z ∪_a C` is a classical relative CW complex relative to the image of `Z`
  (`TauCeti.relativeCWPushout`), whose `n`-cells are the `n`-cells of `C`
  (`TauCeti.relativeCWPushoutCellEquiv`), with the characteristic maps of `C` composed with
  `C → Z ∪_a C` (`TauCeti.map_relativeCWPushout_apply`).

No CW structure on `Z` is needed. The construction goes through categorical relative CW
complexes: `C` gives one on the inclusion `D → C` (`TauCeti.toRelativeCWComplex`), its cobase
change along `a` is a categorical relative CW complex on `Z → Z ∪_a C`
(`HomotopicalAlgebra.RelativeCellComplex.ofIsPushout`), and that is read back as a classical one
(`TopCat.RelativeCWComplex.toRelCWComplex`). This is the form in which cells are attached along
maps into spaces that are not themselves CW complexes, such as the sublevel sets of a function
on a manifold.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and Appendix, Propositions A.2 and A.3.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

public section

open CategoryTheory Limits HomotopicalAlgebra Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D]
  {Z : TopCat.{u}} (a : C(D, Z))

/-- The inclusion of the base `D` of a relative CW complex `C` into `C`, as a morphism of
`TopCat`. -/
abbrev baseInclusion : TopCat.of D ⟶ TopCat.of C :=
  TopCat.ofHom (ContinuousMap.inclusion (base_subset_complex (C := C)))

/-- The adjunction space `Z ∪_a C` obtained by gluing `C` to `Z` along `a : D → Z`: the pushout in
`TopCat` of `a` and the inclusion of `D` into `C`. -/
noncomputable abbrev adjunctionSpace : TopCat.{u} :=
  pushout (TopCat.ofHom a) (baseInclusion C)

/-- The adjunction space `Z ∪_a C` is a categorical relative CW complex over `Z`, with the cells
of `C`. -/
noncomputable def pushoutRelativeCWComplex :
    TopCat.RelativeCWComplex.{u} (pushout.inl (TopCat.ofHom a) (baseInclusion C)) :=
  (toRelativeCWComplex C).ofIsPushout (IsPushout.of_hasPushout _ _)

/-- **The inclusion of `Z` into the adjunction space `Z ∪_a C` is a closed embedding.** -/
theorem isClosedEmbedding_pushout_inl :
    IsClosedEmbedding (pushout.inl (TopCat.ofHom a) (baseInclusion C)) :=
  (pushoutRelativeCWComplex C a).isClosedEmbedding

/-- **The adjunction space `Z ∪_a C` is Hausdorff when `Z` is.** -/
instance t2Space_adjunctionSpace [T2Space Z] : T2Space (adjunctionSpace C a) :=
  (pushoutRelativeCWComplex C a).t2Space

/-- **Gluing a relative CW complex to a space.** The adjunction space `Z ∪_a C` obtained by gluing
the relative CW complex `C` with base `D` to `Z` along `a : D → Z` is a classical relative CW
complex relative to the image of `Z`. Its `n`-cells are the `n`-cells of `C`
(`TauCeti.relativeCWPushoutCellEquiv`), with the characteristic maps of `C` composed with
`C → Z ∪_a C` (`TauCeti.map_relativeCWPushout_apply`). -/
@[instance_reducible] noncomputable def relativeCWPushout :
    RelCWComplex (univ : Set (adjunctionSpace C a))
      (range (pushout.inl (TopCat.ofHom a) (baseInclusion C))) :=
  (pushoutRelativeCWComplex C a).toRelCWComplex

/-- The `n`-cells of `TauCeti.relativeCWPushout C a` are the `n`-cells of `C`. -/
noncomputable def relativeCWPushoutCellEquiv (n : ℕ) :
    (relativeCWPushout C a).cell n ≃ cell C n :=
  (pushoutRelativeCWComplex C a).toRelCWComplexCellEquiv n

/-- The characteristic maps of `TauCeti.relativeCWPushout C a` are those of `C`, composed with the
map `C → Z ∪_a C`. -/
theorem map_relativeCWPushout_apply (n : ℕ) (i : (relativeCWPushout C a).cell n)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    (relativeCWPushout C a).map n i x =
      pushout.inr (TopCat.ofHom a) (baseInclusion C)
        ⟨map n (relativeCWPushoutCellEquiv C a n i) x,
          closedCell_subset_complex n _ (mem_image_of_mem _ hx)⟩ := by
  let c := toRelativeCWComplex C
  let γ : c.Cells := ⟨n, not_isMax n, relativeCWPushoutCellEquiv C a n i⟩
  -- The cell of the cobase change indexed by `i` is the cell `γ` of `c`, transported along
  -- `ofIsPushoutCellsEquiv`; both are indexed by `i` itself.
  have hγ : (⟨n, not_isMax n, (pushoutRelativeCWComplex C a).toRelCWComplexCellEquiv n i⟩ :
      (pushoutRelativeCWComplex C a).Cells).ι =
        γ.ι ≫ pushout.inr (TopCat.ofHom a) (baseInclusion C) :=
    c.ofIsPushout_cells_ι (IsPushout.of_hasPushout _ _) γ
  rw [(pushoutRelativeCWComplex C a).toRelCWComplex_map_apply n i ⟨x, hx⟩,
    ConcreteCategory.congr_hom hγ, ConcreteCategory.comp_apply]
  congr 1
  ext
  rw [coe_toRelativeCWComplex_cells_ι_apply, Homeomorph.apply_symm_apply]

end TauCeti
