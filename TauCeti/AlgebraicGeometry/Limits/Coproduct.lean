/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The summands of a coproduct of schemes

For a family of schemes `X : σ → Scheme` indexed by a type that is small relative to the universe
of the schemes, Mathlib constructs the coproduct `∐ X`, whose coprojections
`Sigma.ι X i : X i ⟶ ∐ X` are open immersions that cover `∐ X` (`AlgebraicGeometry.sigmaOpenCover`)
and are disjoint (`AlgebraicGeometry.sigmaι_eq_iff`). This file records the point-set consequences
used to work one summand at a time:

* `TauCeti.AlgebraicGeometry.sigmaι_jointly_surjective`: every point of `∐ X` lies in some summand;
* `TauCeti.AlgebraicGeometry.sigmaι_apply_mem_range_sigmaι_iff`: the point `Sigma.ι X i x` lies in
  the summand `X j` only for `j = i`;
* `TauCeti.AlgebraicGeometry.isClopen_range_sigmaι`: each summand is open and closed, so each
  coprojection is a closed immersion (`TauCeti.AlgebraicGeometry.isClosedImmersion_sigmaι`);
* `TauCeti.AlgebraicGeometry.exists_range_subset_range_sigmaι`: a morphism from a connected scheme
  to `∐ X` lands in a single summand;
* `TauCeti.AlgebraicGeometry.locallyFinite_range_sigmaι`: the summands form a locally finite
  family;
* `TauCeti.AlgebraicGeometry.isLocallyNoetherian_sigma`: a coproduct of locally Noetherian schemes
  is locally Noetherian.
-/

public section

open CategoryTheory Limits Topology _root_.AlgebraicGeometry

universe u v

namespace TauCeti.AlgebraicGeometry

variable {σ : Type v} (X : σ → Scheme.{u}) [Small.{u} σ]

/-- Every point of a coproduct of schemes lies in some summand: the coprojections are jointly
surjective, since they form the open cover `AlgebraicGeometry.sigmaOpenCover X`. -/
theorem sigmaι_jointly_surjective (x : ↑(∐ X)) : ∃ i y, Sigma.ι X i y = x :=
  -- `(sigmaOpenCover X).X i` and `(sigmaOpenCover X).f i` are `X i` and `Sigma.ι X i` by
  -- definition (`sigmaOpenCover_X`, `sigmaOpenCover_f`), so the statement of `Cover.exists_eq`
  -- is this one up to unfolding `Cover.copy`.
  (sigmaOpenCover X).exists_eq x

variable {X} in
/-- The image of a point of the summand `X i` lies in the summand `X j` exactly when `j = i`: the
summands of a coproduct are pairwise disjoint. -/
theorem sigmaι_apply_mem_range_sigmaι_iff {i j : σ} (x : X i) :
    Sigma.ι X i x ∈ Set.range (Sigma.ι X j) ↔ i = j := by
  refine ⟨fun ⟨y, hy⟩ ↦ (Sigma.mk.inj_iff.mp ((sigmaι_eq_iff X j i y x).mp hy)).left.symm, ?_⟩
  rintro rfl
  exact ⟨x, rfl⟩

/-- Each summand of a coproduct of schemes is open and closed: its complement is the union of the
other summands. -/
theorem isClopen_range_sigmaι (i : σ) : IsClopen (Set.range (Sigma.ι X i)) := by
  have h : (Set.range (Sigma.ι X i))ᶜ = ⋃ (j : σ) (_ : j ≠ i), Set.range (Sigma.ι X j) := by
    ext x
    obtain ⟨j, y, rfl⟩ := sigmaι_jointly_surjective X x
    simp only [Set.mem_compl_iff, sigmaι_apply_mem_range_sigmaι_iff, Set.mem_iUnion,
      exists_prop, exists_eq_right']
  refine ⟨isOpen_compl_iff.mp ?_, (Sigma.ι X i).isOpenEmbedding.isOpen_range⟩
  rw [h]
  exact isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ (Sigma.ι X j).isOpenEmbedding.isOpen_range

/-- The coprojections of a coproduct of schemes are closed immersions: they are open immersions
with closed range. -/
instance isClosedImmersion_sigmaι (i : σ) : IsClosedImmersion (Sigma.ι X i) :=
  .of_isPreimmersion _ (isClopen_range_sigmaι X i).isClosed

/-- The summands of a coproduct of schemes form a locally finite family: the summand containing a
point is a neighbourhood of it meeting no other summand. -/
theorem locallyFinite_range_sigmaι : LocallyFinite fun i ↦ Set.range (Sigma.ι X i) := by
  intro x
  obtain ⟨i, y, rfl⟩ := sigmaι_jointly_surjective X x
  refine ⟨_, (isClopen_range_sigmaι X i).isOpen.mem_nhds ⟨y, rfl⟩,
    (Set.finite_singleton i).subset fun j ⟨_, ⟨z, rfl⟩, hz⟩ ↦ ?_⟩
  exact Set.mem_singleton_iff.mpr ((sigmaι_apply_mem_range_sigmaι_iff z).mp hz)

/-- A morphism from a connected scheme to a coproduct of schemes lands in a single summand: the
preimages of the summands are open and closed. -/
theorem exists_range_subset_range_sigmaι {W : Scheme.{u}} [ConnectedSpace W] (f : W ⟶ ∐ X) :
    ∃ i, Set.range f ⊆ Set.range (Sigma.ι X i) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty W)
  obtain ⟨i, y, hy⟩ := sigmaι_jointly_surjective X (f w)
  have huniv := ((isClopen_range_sigmaι X i).preimage f.continuous).eq_univ ⟨w, y, hy⟩
  exact ⟨i, Set.range_subset_iff.mpr (Set.eq_univ_iff_forall.mp huniv)⟩

/-- A coproduct of locally Noetherian schemes is locally Noetherian: the summands form an open
cover of it. -/
instance isLocallyNoetherian_sigma [hX : ∀ i, IsLocallyNoetherian (X i)] :
    IsLocallyNoetherian (∐ X) :=
  (isLocallyNoetherian_iff_openCover (sigmaOpenCover X)).mpr hX

end TauCeti.AlgebraicGeometry
