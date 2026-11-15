/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import TauCeti.Topology.VectorBundle.Orientation.EulerClass

/-!
# Local indices of a section and the Euler number

Let `M` be a topological manifold of dimension `n + 1` without boundary, with a homological
orientation `oM`, and let `E → M` be a real vector bundle of rank `n + 1` with an orientation `o`.
Let `s` be a continuous section of `E`, and let `z` be a point with an open neighbourhood `U`
containing no zero of `s` other than `z`. Then `s` restricts to a map of pairs
`(U, U ∖ {z}) ⟶ (E, E₀)` into the Thom pair, along which the Thom class
`U_E ∈ Hⁿ⁺¹(E, E₀; ℤ)` pulls back to a class of `Hⁿ⁺¹(U, U ∖ {z}; ℤ)`. The *local index* of `s`
at `z` (`TauCeti.VectorBundleOrientation.sectionIndex`) is the Kronecker pairing of this class with
the local orientation `oM z ∈ Hₙ₊₁(M, M ∖ {z}; ℤ)`, read in `Hₙ₊₁(U, U ∖ {z}; ℤ)` through excision.
It does not depend on `U` (`TauCeti.VectorBundleOrientation.sectionIndex_eq`), and reversing either
orientation negates it.

For `M` compact and `s` with finitely many zeros, the Euler class of `E` evaluated on the
fundamental class of `M` is the sum of the local indices of `s` at its zeros
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`):
`⟨e(E), [M]⟩ = ∑_{s z = 0} ind_z(s)`. The proof has three steps.

* The zero section is homotopic to `s` through `t • s`, so the Euler class is the image in
  `Hⁿ⁺¹(M; ℤ)` of the relative class `s^* U_E ∈ Hⁿ⁺¹(M, M ∖ Z; ℤ)`, where `Z` is the zero set
  (`TauCeti.eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero`); its pairing with `[M]` is
  the pairing of `s^* U_E` with the image of `[M]` in `Hₙ₊₁(M, M ∖ Z; ℤ)`, which is the
  fundamental class of `M` along `Z`.
* The fundamental class along the finite set `Z` is the sum over `z ∈ Z` of the local orientations
  `oM z`, each read in an isolating neighbourhood of `z` through excision and pushed into
  `Hₙ₊₁(M, M ∖ Z; ℤ)`
  (`TauCeti.HomologicalOrientation.fundamentalClassOn_eq_sum_localOrientationAlong`).
* By naturality of the Kronecker pairing, pairing `s^* U_E` with the term at `z` is the local index
  at `z`.

## Main definitions

* `TauCeti.VectorBundleOrientation.sectionIndex`: the local index of a section at a point.

## Main results

* `TauCeti.VectorBundleOrientation.sectionIndex_eq`: the local index is the pairing along any open
  neighbourhood containing no other zero; at a point without such a neighbourhood it is `0`
  (`TauCeti.VectorBundleOrientation.sectionIndex_of_not_isolated`), and so it is at a point where
  the section is nonzero (`TauCeti.VectorBundleOrientation.sectionIndex_of_ne_zero`).
* `TauCeti.VectorBundleOrientation.sectionIndex_neg` and
  `TauCeti.VectorBundleOrientation.sectionIndex_neg_manifold`: reversing the orientation of the
  bundle or of the manifold negates the local index.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`: the
  Euler number is the sum of the local indices.

## Implementation notes

The manifold and the bundle live in `Type`, as for the fundamental class
(`TauCeti.HomologicalOrientation.fundamentalClass`), and integral coefficients are `ULift ℤ`, as
for the Thom class; the local index is the underlying integer. At a point that is an accumulation
point of zeros of `s`, the local index is `0` by convention.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class as the obstruction class of a section, evaluated through
  its zeros).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (fundamental classes along compact sets, Lemma 3.27).
* G. E. Bredon, *Topology and Geometry*, Graduate Texts in Mathematics 139, Springer (1993),
  Chapter VI, §12 (the Euler class and indices of sections).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

namespace TauCeti

namespace VectorBundleOrientation

variable {M E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] {n : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : M → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
  (oM : HomologicalOrientation M E' (n + 1)) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))

/-- The pairing defining the local index of `s` at `z` along an open neighbourhood `U` of `z`
containing no other zero of `s`. -/
private def indexOn {z : M} {U : Set M} (hU : IsOpen U) (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) : ℤ :=
  (((TopPair.ofSubset ({⟨z, hz⟩}ᶜ : Set (TopCat.of U))).singularKronecker ℤ (n + 1)
    (TopPair.singularCohomologyMap
      (thomPairMapOfNeZero ⟨fun x : U ↦ TotalSpace.mk' F x.1 (s x.1),
        hs.comp continuous_subtype_val⟩ (S := {⟨z, hz⟩})
        fun x hx h0 ↦ hx (Subtype.ext (hUz x.1 x.2 h0)))
      (n + 1) (o.thomClass hF))).hom
    ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
      hU.isOpenEmbedding_subtypeVal ⟨z, hz⟩ (n + 1)).inv (oM z).val)).down

/-- The pairing along a neighbourhood does not change when the neighbourhood shrinks. -/
private theorem indexOn_of_subset {z : M} {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hz : z ∈ V) (hVU : V ⊆ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) :
    indexOn o hF oM hs hV hz (fun x hx ↦ hUz x (hVU hx)) = indexOn o hF oM hs hU (hVU hz) hUz := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let i : C(V, U) := ⟨inclusion hVU, continuous_inclusion hVU⟩
  have hi : i ⁻¹' {⟨z, hVU hz⟩} ⊆ {⟨z, hz⟩} := fun y hy ↦ Subtype.ext (congrArg Subtype.val hy :)
  have hj : Topology.IsOpenEmbedding (inclusion hVU) :=
    (hU.isOpenEmbedding_subtypeVal.of_comp_iff _).1 hV.isOpenEmbedding_subtypeVal
  -- The excision isomorphisms of `V` and `U` are compatible with the inclusion `V ⊆ U`.
  have hexc : localHomologyMap R i hi (n + 1)
      ((localHomologyIsoOfIsOpenEmbedding R hV.isOpenEmbedding_subtypeVal ⟨z, hz⟩ (n + 1)).inv
        (oM z).val) =
      (localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal ⟨z, hVU hz⟩
        (n + 1)).inv (oM z).val := by
    rw [← localHomologyIsoOfIsOpenEmbedding_trans R hj hU.isOpenEmbedding_subtypeVal ⟨z, hz⟩,
      Iso.trans_inv, ConcreteCategory.comp_apply]
    exact localHomologyIsoOfIsOpenEmbedding_inv_comp_localHomologyMap_apply R hj ⟨z, hz⟩ hi
      (n + 1) _
  simp only [indexOn]
  rw [← hexc, localHomologyMap_def]
  conv_rhs => rw [← ModuleCat.comp_apply, ← TopPair.singularKronecker_naturality,
    ← TopPair.singularCohomologyMap_comp_apply]
  rw [ofSubsetMap_comp_thomPairMapOfNeZero_of_comp_eq (hf := rfl)]
  -- `s` restricted to `U`, composed with the inclusion `V ⊆ U`, is `s` restricted to `V`.
  rfl

/-- The local orientation at a zero `z` of `s`, read through excision in an open neighbourhood `U`
of `z` and pushed into `Hₙ₊₁(M, M ∖ Z)`, paired with the pull-back of the Thom class along
`s : (M, M ∖ Z) ⟶ (E, E₀)`, where `Z` is the zero set, is the pairing defining the local index at
`z`. -/
private theorem singularKronecker_localOrientationAlong {z : M} {U : Set M} (hU : IsOpen U)
    (hz : z ∈ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) :
    (((TopPair.ofSubset ({x | s x = 0}ᶜ : Set (TopCat.of M))).singularKronecker ℤ (n + 1)
      (TopPair.singularCohomologyMap
        (thomPairMapOfNeZero ⟨_, hs⟩ (S := {x | s x = 0}) fun _ hx ↦ hx) (n + 1)
        (o.thomClass hF))).hom (oM.localOrientationAlong hU hz hUz)).down =
      indexOn o hF oM hs hU hz hUz := by
  rw [HomologicalOrientation.localOrientationAlong_def, localHomologyMap_def
    (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨Subtype.val, continuous_subtype_val⟩ (S := {(⟨z, hz⟩ : U)})
    (T := {x | s x = 0}) (fun x (hx : x.1 ∈ {x | s x = 0}) ↦ Subtype.ext (hUz x.1 x.2 hx)),
    ← ModuleCat.comp_apply,
    ← TopPair.singularKronecker_naturality, ← TopPair.singularCohomologyMap_comp_apply,
    ofSubsetMap_comp_thomPairMapOfNeZero_of_comp_eq (hf := rfl), indexOn]
  -- `s` composed with the inclusion of `U` is `s` restricted to `U`.
  rfl

open Classical in
/-- **The local index of a section at a point.** Let `s` be a continuous section of an oriented
vector bundle `E` of rank `n + 1` over a manifold `M` with orientation `oM`, of dimension `n + 1`.
If `z` has an open neighbourhood `U` containing no zero of `s` other than `z`, then `s` restricts
to a map of pairs `(U, U ∖ {z}) ⟶ (E, E₀)`, and the local index of `s` at `z` is the Kronecker
pairing of the pull-back along it of the Thom class `U_E ∈ Hⁿ⁺¹(E, E₀; ℤ)` with the local
orientation `oM z ∈ Hₙ₊₁(M, M ∖ {z}; ℤ)`, read in `Hₙ₊₁(U, U ∖ {z}; ℤ)` through excision. It does
not depend on `U` (`TauCeti.VectorBundleOrientation.sectionIndex_eq`). At a point which is an
accumulation point of zeros of `s` it is `0` by convention. -/
def sectionIndex (z : M) : ℤ :=
  if h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z then
    indexOn o hF oM hs h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2
  else 0

/-- At a point which is not an isolated zero of `s`, that is, without an open neighbourhood
containing no zero of `s` other than itself, the local index is `0`. At a point where `s` is
nonzero, see `TauCeti.VectorBundleOrientation.sectionIndex_of_ne_zero`. -/
theorem sectionIndex_of_not_isolated {z : M}
    (h : ¬ ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z) : o.sectionIndex hF oM hs z = 0 :=
  dite_eq_right h

/-- **The local index along any isolating neighbourhood.** For an open neighbourhood `U` of `z`
containing no zero of `s` other than `z`, the local index of `s` at `z` is the Kronecker pairing
of the pull-back of the Thom class along `s : (U, U ∖ {z}) ⟶ (E, E₀)` with the local orientation
`oM z`, read in `Hₙ₊₁(U, U ∖ {z}; ℤ)` through excision. -/
theorem sectionIndex_eq {z : M} {U : Set M} (hU : IsOpen U) (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) :
    o.sectionIndex hF oM hs z =
      (((TopPair.ofSubset ({⟨z, hz⟩}ᶜ : Set (TopCat.of U))).singularKronecker ℤ (n + 1)
        (TopPair.singularCohomologyMap
          (thomPairMapOfNeZero ⟨fun x : U ↦ TotalSpace.mk' F x.1 (s x.1),
            hs.comp continuous_subtype_val⟩ (S := {⟨z, hz⟩})
            fun x hx h0 ↦ hx (Subtype.ext (hUz x.1 x.2 h0)))
          (n + 1) (o.thomClass hF))).hom
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          hU.isOpenEmbedding_subtypeVal ⟨z, hz⟩ (n + 1)).inv (oM z).val)).down := by
  have h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z := ⟨U, hU, hz, hUz⟩
  obtain ⟨hU₀, hz₀, hU₀z⟩ := h.choose_spec
  rw [sectionIndex, dite_eq_left h, ← indexOn_of_subset o hF oM hs hU₀ (hU₀.inter hU) ⟨hz₀, hz⟩
    inter_subset_left hU₀z, indexOn_of_subset o hF oM hs hU (hU₀.inter hU) ⟨hz₀, hz⟩
    inter_subset_right hUz, indexOn]

/-- At a point where `s` is nonzero, the local index of `s` is `0`. -/
theorem sectionIndex_of_ne_zero {z : M} (h : s z ≠ 0) : o.sectionIndex hF oM hs z = 0 := by
  by_cases hU : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z
  · obtain ⟨U, hU, hz, hUz⟩ := hU
    -- No point of `U` is a zero of `s`, so `s` is a map of pairs `(U, U) ⟶ (E, E₀)`, and the
    -- local orientation is paired through `Hₙ₊₁(U, U) = 0`.
    have h₀ : ∀ x : U, x ∉ (∅ : Set U) → s x.1 ≠ 0 := fun x _ h0 ↦ h (hUz x.1 x.2 h0 ▸ h0)
    rw [sectionIndex_eq o hF oM hs hU hz hUz, ← ofSubsetMap_comp_thomPairMapOfNeZero_of_comp_eq
      _ h₀ (ContinuousMap.id U) (T := {⟨z, hz⟩}) (fun _ _ h ↦ h) (ContinuousMap.comp_id _),
      TopPair.singularCohomologyMap_comp_apply, TopPair.singularKronecker_naturality,
      (isZero_localHomology_empty _ (n + 1)).eq_zero_of_tgt (TopPair.singularHomologyMap _ _ _),
      Limits.zero_comp]
    simp
  · exact sectionIndex_of_not_isolated o hF oM hs hU

/-- **Reversing the orientation of the bundle negates the local index.** -/
@[simp]
theorem sectionIndex_neg (z : M) : (-o).sectionIndex hF oM hs z = -o.sectionIndex hF oM hs z := by
  by_cases h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z
  · obtain ⟨U, hU, hz, hUz⟩ := h
    rw [sectionIndex_eq (-o) hF oM hs hU hz hUz, sectionIndex_eq o hF oM hs hU hz hUz,
      thomClass_neg, map_neg, map_neg]
    simp only [ModuleCat.hom_neg, LinearMap.neg_apply, ULift.neg_down]
  · rw [sectionIndex_of_not_isolated _ _ _ _ h, sectionIndex_of_not_isolated _ _ _ _ h, neg_zero]

/-- **Reversing the orientation of the manifold negates the local index.** -/
@[simp]
theorem sectionIndex_neg_manifold (z : M) :
    o.sectionIndex hF (-oM) hs z = -o.sectionIndex hF oM hs z := by
  by_cases h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z
  · obtain ⟨U, hU, hz, hUz⟩ := h
    rw [sectionIndex_eq o hF (-oM) hs hU hz hUz, sectionIndex_eq o hF oM hs hU hz hUz,
      HomologicalOrientation.neg_apply, LocalOrientation.coe_neg, map_neg, map_neg]
    simp only [ULift.neg_down]
  · rw [sectionIndex_of_not_isolated _ _ _ _ h, sectionIndex_of_not_isolated _ _ _ _ h, neg_zero]

/-- **The Euler number is the sum of the local indices.** Let `M` be a compact manifold of
dimension `n + 1` with orientation `oM`, and let `s` be a continuous section with finitely many
zeros of a real vector bundle `E → M` of rank `n + 1` with orientation `o`. Then the Euler class of
`E`, evaluated on the fundamental class of `M`, is the sum of the local indices of `s` at its
zeros: `⟨e(E), [M]⟩ = ∑_{s z = 0} ind_z s`. -/
theorem evalFundamentalClass_eulerClass_eq_sum_sectionIndex [CompactSpace M]
    (hE : finrank ℝ E' = n + 1) (hZ : {x | s x = 0}.Finite) :
    (oM.evalFundamentalClass hE (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (o.eulerClass hF)).down = ∑ z ∈ hZ.toFinset, o.sectionIndex hF oM hs z := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let P := TopPair.ofSubset ({x | s x = 0}ᶜ : Set (TopCat.of M))
  let α := TopPair.singularCohomologyMap (thomPairMapOfNeZero ⟨_, hs⟩ (S := {x | s x = 0})
    fun _ hx ↦ hx) (n + 1) (o.thomClass hF)
  -- The zero section is homotopic to `s` through `t • s`, so the Euler class is the image of the
  -- relative class `s^* U_E ∈ Hⁿ⁺¹(M, M ∖ Z)`.
  have h₁ : o.eulerClass hF = P.singularCohomologyπ R ℤ R (n + 1) α :=
    (eulerClass_def o hF).trans <| (ConcreteCategory.congr_hom
      (eulerClass_eq_singularCohomologyMap_thomPairMapOfNeZero F E hs (S := {x | s x = 0})
        (fun _ hx ↦ hx) (n + 1)) (o.thomClass hF)).trans (ConcreteCategory.comp_apply _ _ _)
  -- The Kronecker pairing with `[M]` is the relative pairing with the image of `[M]` in
  -- `Hₙ₊₁(M, M ∖ Z)`, which is the fundamental class along `Z`.
  have h₂ : ((TopCat.of M).singularKronecker ℤ (n + 1)
        (P.singularCohomologyπ R ℤ R (n + 1) α)).hom (oM.fundamentalClass hE) =
      (P.singularKronecker ℤ (n + 1) α).hom (oM.fundamentalClassOn hE hZ.isCompact) :=
    (ConcreteCategory.congr_hom (TopPair.singularKronecker_singularCohomologyπ P ℤ (n + 1) α)
      _).trans ((ConcreteCategory.comp_apply _ _ _).trans (congrArg _
        (oM.singularHomologyπ_fundamentalClass hE hZ.isCompact)))
  rw [HomologicalOrientation.evalFundamentalClass_apply,
    HomologicalOrientation.mapFundamentalClass_id, h₁, h₂]
  -- Each zero `z` is the only zero in its open neighbourhood `(Z ∖ {z})ᶜ`, and the fundamental
  -- class along `Z` is the sum of the local orientations at the zeros, read in these
  -- neighbourhoods.
  have hU : ∀ z, IsOpen ({x | s x = 0} \ {z})ᶜ := fun _ ↦ hZ.sdiff.isClosed.isOpen_compl
  have hzU : ∀ z, z ∈ ({x | s x = 0} \ {z})ᶜ := fun _ h ↦ h.2 rfl
  have hUz : ∀ z, ∀ x ∈ ({x | s x = 0} \ {z})ᶜ, s x = 0 → x = z :=
    fun _ _ hx h0 ↦ by_contra fun hxz ↦ hx ⟨h0, hxz⟩
  have h₄ := oM.fundamentalClassOn_eq_sum_localOrientationAlong hE hZ hU hzU hUz
  rw [h₄, map_sum]
  refine (map_sum (ULift.moduleEquiv (R := ℤ)) _ _).trans (Finset.sum_congr rfl fun z _ ↦ ?_)
  rw [sectionIndex_eq o hF oM hs (hU z) (hzU z) (hUz z)]
  exact singularKronecker_localOrientationAlong o hF oM hs _ _ _

end VectorBundleOrientation

end TauCeti
