/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import TauCeti.Topology.VectorBundle.Orientation.EulerClass
import TauCeti.Topology.VectorBundle.Smul

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
  `Hⁿ⁺¹(M; ℤ)` of the relative class `s^* U_E ∈ Hⁿ⁺¹(M, M ∖ Z; ℤ)`, where `Z` is the zero set; its
  pairing with `[M]` is the pairing of `s^* U_E` with the image of `[M]` in `Hₙ₊₁(M, M ∖ Z; ℤ)`,
  which is the fundamental class of `M` along `Z`.
* The fundamental class along the finite set `Z` is the sum over `z ∈ Z` of the local orientations
  `oM z`, each read in an isolating neighbourhood of `z` through excision and pushed into
  `Hₙ₊₁(M, M ∖ Z; ℤ)`: both restrict to `oM x` at every `x ∈ Z`.
* By naturality of the Kronecker pairing, pairing `s^* U_E` with the term at `z` is the local index
  at `z`.

## Main definitions

* `TauCeti.thomPairMapOfNeZero`: a continuous map `f : X → E` taking nonzero values off a set `S`,
  as a map of pairs `(X, X ∖ S) ⟶ (E, E₀)`.
* `TauCeti.VectorBundleOrientation.sectionIndex`: the local index of a section at a point.

## Main results

* `TauCeti.VectorBundleOrientation.sectionIndex_eq`: the local index is the pairing along any open
  neighbourhood containing no other zero.
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

universe w

namespace TauCeti

/-- The map of pairs `(X, X ∖ S) ⟶ (E, E₀)` into the Thom pair of a bundle given by a continuous
map `f : X → E` which takes nonzero values off `S`. For a section `s` and `S` its zero set, this is
`s` as a map of pairs. -/
def thomPairMapOfNeZero {B : Type w} {F : Type*} {E : B → Type w}
    [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)] {X : Type w} [TopologicalSpace X]
    (f : C(X, TotalSpace F E)) {S : Set X} (h : ∀ x ∉ S, (f x).2 ≠ 0) :
    TopPair.ofSubset (Sᶜ : Set (TopCat.of X)) ⟶ thomPair F E :=
  TopPair.ofSubsetMap (TopCat.ofHom f) fun x hx ↦ mem_zeroSectionCompl.2 (h x hx)

@[simp]
theorem thomPairMapOfNeZero_fst_apply {B : Type w} {F : Type*} {E : B → Type w}
    [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)] {X : Type w} [TopologicalSpace X]
    (f : C(X, TotalSpace F E)) {S : Set X} (h : ∀ x ∉ S, (f x).2 ≠ 0) (x : X) :
    TopPair.Hom.fst (thomPairMapOfNeZero f h) x = f x :=
  TopPair.ofSubsetMap_fst_apply (X := TopCat.of X) _ _ x

namespace VectorBundleOrientation

variable {M E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] {n : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : M → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
  (oM : HomologicalOrientation M E' (n + 1)) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))

/-- The section `s`, as a continuous map into the total space. -/
private def sectionMap : C(M, TotalSpace F E) :=
  ⟨fun x ↦ TotalSpace.mk' F x (s x), hs⟩

/-- The pairing defining the local index of `s` at `z` along an open neighbourhood `U` of `z`
containing no other zero of `s`. -/
private def indexOn {z : M} {U : Set M} (hU : IsOpen U) (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) : ℤ :=
  (((TopPair.ofSubset ({⟨z, hz⟩}ᶜ : Set (TopCat.of U))).singularKronecker ℤ (n + 1)
    (TopPair.singularCohomologyMap
      (thomPairMapOfNeZero ((sectionMap hs).comp ⟨Subtype.val, continuous_subtype_val⟩)
        (S := {⟨z, hz⟩}) fun x hx h0 ↦ hx (Subtype.ext (hUz x.1 x.2 h0)))
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
  -- The excision isomorphisms of `V` and `U` are compatible with the inclusion `V ⊆ U`.
  have hexc : localHomologyMap R i hi (n + 1)
      ((localHomologyIsoOfIsOpenEmbedding R hV.isOpenEmbedding_subtypeVal ⟨z, hz⟩ (n + 1)).inv
        (oM z).val) =
      (localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal ⟨z, hVU hz⟩
        (n + 1)).inv (oM z).val := by
    have hV' := (localHomologyIsoOfIsOpenEmbedding R hV.isOpenEmbedding_subtypeVal ⟨z, hz⟩
      (n + 1)).inv_hom_id_apply (oM z).val
    have hU' := (localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal ⟨z, hVU hz⟩
      (n + 1)).hom_inv_id_apply
      (localHomologyMap R i hi (n + 1) ((localHomologyIsoOfIsOpenEmbedding R
        hV.isOpenEmbedding_subtypeVal ⟨z, hz⟩ (n + 1)).inv (oM z).val))
    rw [localHomologyIsoOfIsOpenEmbedding_hom] at hV'
    rw [localHomologyIsoOfIsOpenEmbedding_hom,
      ← ConcreteCategory.comp_apply (localHomologyMap R i hi (n + 1)), localHomologyMap_comp] at hU'
    rw [← hU']
    exact congrArg _ hV'
  simp only [indexOn]
  rw [← hexc, localHomologyMap_def]
  conv_rhs => rw [← ModuleCat.comp_apply, ← TopPair.singularKronecker_naturality,
    ← TopPair.singularCohomologyMap_comp_apply]
  congr 7
  unfold thomPairMapOfNeZero
  symm
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (TopCat.ext fun _ ↦ rfl)

/-- The local orientation at `z`, read through excision in an open neighbourhood `U` of `z`
containing no other zero of `s` and pushed into `Hₙ₊₁(M, M ∖ Z)`, where `Z` is the zero set. -/
private def zeroClass {z : M} {U : Set M} (hU : IsOpen U) (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) {x | s x = 0} (n + 1) :=
  localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨Subtype.val, continuous_subtype_val⟩
    (S := {(⟨z, hz⟩ : U)}) (T := {x | s x = 0}) (fun x hx ↦ Subtype.ext (hUz x.1 x.2 hx)) (n + 1)
    ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
      hU.isOpenEmbedding_subtypeVal ⟨z, hz⟩ (n + 1)).inv (oM z).val)

omit [∀ x, Module ℝ (E x)] [∀ x, TopologicalSpace (E x)] in
/-- The class `zeroClass` restricts to the local orientation at `z`. -/
private theorem localHomologyRestriction_zeroClass_self {z : M} {U : Set M} (hU : IsOpen U)
    (hz : z ∈ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) (hz₀ : z ∈ {x | s x = 0}) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hz₀) (n + 1)
        (zeroClass oM hU hz hUz) = (oM z).val := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  have h := localHomologyMap_comp_localHomologyRestriction R ⟨Subtype.val, continuous_subtype_val⟩
    (S := {(⟨z, hz⟩ : U)}) (singleton_subset_iff.2 hz₀)
    (fun x (hx : x.1 ∈ {x | s x = 0}) ↦ Subtype.ext (hUz x.1 x.2 hx)) (n + 1)
  have h' := (localHomologyIsoOfIsOpenEmbedding R hU.isOpenEmbedding_subtypeVal ⟨z, hz⟩
    (n + 1)).inv_hom_id_apply (oM z).val
  rw [localHomologyIsoOfIsOpenEmbedding_hom] at h'
  rw [zeroClass, ← ConcreteCategory.comp_apply, h]
  exact h'

omit [∀ x, Module ℝ (E x)] [∀ x, TopologicalSpace (E x)] in
/-- The class `zeroClass` restricts to `0` at every zero of `s` other than `z`. -/
private theorem localHomologyRestriction_zeroClass_of_ne {z : M} {U : Set M} (hU : IsOpen U)
    (hz : z ∈ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) {x : M} (hx : x ∈ {x | s x = 0})
    (hxz : x ≠ z) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hx) (n + 1)
        (zeroClass oM hU hz hUz) = 0 := by
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  -- No point of `U` lies over the zero `x ≠ z`, so the map factors through `Hₙ₊₁(U, U) = 0`.
  have h : (Subtype.val : U → M) ⁻¹' {x} ⊆ ∅ := fun y (hy : y.1 = x) ↦
    hxz (hy.symm.trans (hUz y.1 y.2 (hy ▸ hx)))
  have h₁ := localHomologyMap_comp_localHomologyRestriction R ⟨Subtype.val, continuous_subtype_val⟩
    (S := {(⟨z, hz⟩ : U)}) (singleton_subset_iff.2 hx)
    (fun x (hx : x.1 ∈ {x | s x = 0}) ↦ Subtype.ext (hUz x.1 x.2 hx)) (n + 1)
  have h₂ := localHomologyRestriction_comp_localHomologyMap R ⟨Subtype.val, continuous_subtype_val⟩
    (empty_subset {(⟨z, hz⟩ : U)}) h (n + 1)
  rw [zeroClass, ← ConcreteCategory.comp_apply, h₁, ← h₂, ConcreteCategory.comp_apply,
    (isZero_localHomology_empty R (n + 1)).eq_zero_of_tgt (localHomologyRestriction R _ _)]
  simp

/-- The local orientation `zeroClass` at a zero `z`, paired with the pull-back of the Thom class
along `s : (M, M ∖ Z) ⟶ (E, E₀)`, is the pairing defining the local index at `z`. -/
private theorem singularKronecker_zeroClass {z : M} {U : Set M} (hU : IsOpen U) (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) :
    (((TopPair.ofSubset ({x | s x = 0}ᶜ : Set (TopCat.of M))).singularKronecker ℤ (n + 1)
      (TopPair.singularCohomologyMap
        (thomPairMapOfNeZero (sectionMap hs) (S := {x | s x = 0}) fun _ hx ↦ hx) (n + 1)
        (o.thomClass hF))).hom (zeroClass oM hU hz hUz)).down =
      indexOn o hF oM hs hU hz hUz := by
  rw [zeroClass, localHomologyMap_def (ModuleCat.of ℤ (ULift.{0} ℤ))
    ⟨Subtype.val, continuous_subtype_val⟩ (S := {(⟨z, hz⟩ : U)}) (T := {x | s x = 0})
    (fun x (hx : x.1 ∈ {x | s x = 0}) ↦ Subtype.ext (hUz x.1 x.2 hx)), ← ModuleCat.comp_apply,
    ← TopPair.singularKronecker_naturality, ← TopPair.singularCohomologyMap_comp_apply]
  unfold indexOn
  congr 7
  unfold thomPairMapOfNeZero
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (TopCat.ext fun _ ↦ rfl)

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
    inter_subset_right hUz]
  rfl

/-- **Reversing the orientation of the bundle negates the local index.** -/
@[simp]
theorem sectionIndex_neg (z : M) : (-o).sectionIndex hF oM hs z = -o.sectionIndex hF oM hs z := by
  by_cases h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z
  · obtain ⟨U, hU, hz, hUz⟩ := h
    rw [sectionIndex_eq (-o) hF oM hs hU hz hUz, sectionIndex_eq o hF oM hs hU hz hUz,
      thomClass_neg, map_neg, map_neg]
    rfl
  · simp [sectionIndex, h]

/-- **Reversing the orientation of the manifold negates the local index.** -/
@[simp]
theorem sectionIndex_neg_manifold (z : M) :
    o.sectionIndex hF (-oM) hs z = -o.sectionIndex hF oM hs z := by
  by_cases h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z
  · obtain ⟨U, hU, hz, hUz⟩ := h
    rw [sectionIndex_eq o hF (-oM) hs hU hz hUz, sectionIndex_eq o hF oM hs hU hz hUz,
      HomologicalOrientation.neg_apply, LocalOrientation.coe_neg, map_neg, map_neg]
    rfl
  · simp [sectionIndex, h]

/-- **The Euler number is the sum of the local indices.** Let `M` be a compact manifold of
dimension `n + 1` with orientation `oM`, and let `s` be a continuous section with finitely many
zeros of a real vector bundle `E → M` of rank `n + 1` with orientation `o`. Then the Euler class of
`E`, evaluated on the fundamental class of `M`, is the sum of the local indices of `s` at its
zeros: `⟨e(E), [M]⟩ = ∑_{s z = 0} ind_z s`. -/
theorem evalFundamentalClass_eulerClass_eq_sum_sectionIndex [CompactSpace M]
    (hE : finrank ℝ E' = n + 1) (hZ : {x | s x = 0}.Finite) :
    (oM.evalFundamentalClass hE (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (o.eulerClass hF)).down = ∑ z ∈ hZ.toFinset, o.sectionIndex hF oM hs z := by
  classical
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let P := TopPair.ofSubset ({x | s x = 0}ᶜ : Set (TopCat.of M))
  let sP : P ⟶ thomPair F E := thomPairMapOfNeZero (sectionMap hs) (S := {x | s x = 0})
    fun _ hx ↦ hx
  let α := TopPair.singularCohomologyMap sP (n + 1) (o.thomClass hF)
  -- The zero section is homotopic to `s` through `t • s`, so the Euler class is the image of the
  -- relative class `s^* U_E ∈ Hⁿ⁺¹(M, M ∖ Z)`.
  have h₁ : o.eulerClass hF = P.singularCohomologyπ R ℤ R (n + 1) α := by
    let H : TopCat.Homotopy (zeroSectionHom F E) (TopCat.ofHom (sectionMap hs)) :=
      { toFun := fun p ↦ TotalSpace.mk' F p.2 ((p.1 : ℝ) • s p.2)
        continuous_toFun :=
          (continuous_subtype_val.comp continuous_fst).smul_totalSpace (hs.comp continuous_snd)
        map_zero_left := fun b ↦ by
          simp only [Icc.coe_zero, zero_smul]; exact (zeroSectionHom_apply F E b).symm
        map_one_left := fun b ↦ by simp; rfl }
    have hfst : TopPair.Hom.fst sP = TopCat.ofHom (sectionMap hs) := TopPair.ofSubsetMap_fst _ _
    have h := ConcreteCategory.congr_hom
      (TopPair.singularCohomologyπ_naturality (R := R) (k := ℤ) (M := R) sP (n + 1))
      (o.thomClass hF)
    rw [hfst] at h
    rw [eulerClass_def, TauCeti.eulerClass_def, H.congr_singularCohomologyMap]
    exact h
  -- The Kronecker pairing with `[M]` is the relative pairing with the image of `[M]` in
  -- `Hₙ₊₁(M, M ∖ Z)`.
  have h₂ : (TopCat.of M).singularKronecker ℤ (n + 1) (P.singularCohomologyπ R ℤ R (n + 1) α) =
      P.singularHomologyπ R (n + 1) ≫ P.singularKronecker ℤ (n + 1) α := by
    rw [TopCat.singularKronecker_def, TopPair.singularKronecker_def]
    exact TauCeti.ChainComplex.kronecker_naturality (P.singularChainComplexπ R) (n + 1) α
  rw [HomologicalOrientation.evalFundamentalClass_apply,
    HomologicalOrientation.mapFundamentalClass_id, h₁, h₂]
  -- The image of `[M]` in `Hₙ₊₁(M, M ∖ Z)` is the fundamental class along `Z`.
  have h₃ : P.singularHomologyπ R (n + 1) (oM.fundamentalClass hE) =
      oM.fundamentalClassOn hE hZ.isCompact := by
    have h := TopPair.singularHomologyπ_naturality (R := R)
      (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (compl_subset_compl.2 (subset_univ {x | s x = 0})))
      (n + 1)
    -- The ambient space of `TopPair.ofSubset` is `TopCat.of M` only up to unfolding, so the
    -- identity is matched by `erw`.
    erw [TopPair.ofSubsetMap_fst, CategoryTheory.Functor.map_id, SSet.homologyMap_id,
      Category.id_comp] at h
    rw [← oM.localHomologyRestriction_fundamentalClassOn_of_subset hE isCompact_univ hZ.isCompact
      (subset_univ _), ← oM.singularHomologyπ_fundamentalClass hE, localHomologyRestriction_def]
    exact ConcreteCategory.congr_hom h _
  -- Every zero is isolated, and the local orientations at the zeros, pushed into
  -- `Hₙ₊₁(M, M ∖ Z)`, sum to the fundamental class along `Z`.
  have hiso : ∀ z ∈ {x | s x = 0}, ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z :=
    fun z _ ↦ ⟨({x | s x = 0} \ {z})ᶜ, (hZ.sdiff.isClosed).isOpen_compl,
      fun h ↦ h.2 rfl, fun x hx h0 ↦ by_contra fun hxz ↦ hx ⟨h0, hxz⟩⟩
  let c : M → localHomology (A := ModuleCat.{0} ℤ) R {x | s x = 0} (n + 1) := fun z ↦
    if h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s x = 0 → x = z then
      zeroClass oM h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2
    else 0
  have h₄ : oM.fundamentalClassOn hE hZ.isCompact = ∑ z ∈ hZ.toFinset, c z := by
    refine (oM.eq_fundamentalClassOn hE hZ.isCompact fun x hx ↦ ?_).symm
    rw [map_sum, Finset.sum_eq_single_of_mem x (hZ.mem_toFinset.2 hx)]
    · simp only [c, dite_eq_left (hiso x hx)]
      exact localHomologyRestriction_zeroClass_self oM _ _ _ hx
    · intro z hz hzx
      have h := hiso z (hZ.mem_toFinset.1 hz)
      simp only [c, dite_eq_left h]
      exact localHomologyRestriction_zeroClass_of_ne oM _ _ _ hx (Ne.symm hzx)
  erw [ModuleCat.comp_apply, h₃]
  rw [h₄, map_sum]
  refine (map_sum (ULift.moduleEquiv (R := ℤ)) _ _).trans (Finset.sum_congr rfl fun z hz ↦ ?_)
  have h := hiso z (hZ.mem_toFinset.1 hz)
  simp only [c, dite_eq_left h, sectionIndex]
  exact singularKronecker_zeroClass o hF oM hs _ _ _

end VectorBundleOrientation

end TauCeti
