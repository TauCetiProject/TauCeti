/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The Thom pair over finite unions of trivializing open sets

Let `E → B` be a real vector bundle with model fibre `F` of finite dimension `r`, and `E₀` the
complement of its zero section. For a subset `W` of the base, the Thom pair of the restriction of
`E` to `W` is the pair `(E|_W, E₀|_W)` of subspaces of the total space
(`TauCeti.thomPairOver`). Over the whole base it is the Thom pair `(E, E₀)`
(`TauCeti.thomPairOverUnivIso`).

Over a subset of the base set of a linear trivialization `e`, the trivialization identifies this
pair with the Thom pair `(W × F, W × (F ∖ {0}))` of the product bundle
(`Bundle.Trivialization.thomPairOverIso`), whose relative homology vanishes below the rank. The
Mayer–Vietoris sequence of the two pairs over open sets `U` and `V`
(`TopCat.isZero_singularHomology_ofInclusion_union`) propagates this vanishing from `U`, `V` and
`U ∩ V` to `U ∪ V`. Since the intersection of an open set with a finite union of open sets is again
a finite union of open sets, induction on the number of sets shows that
`Hₙ(E|_W, E₀|_W) = 0` for `n < r` whenever `W` is a finite union of open sets each lying in the base
set of a linear trivialization (`TauCeti.isZero_singularHomology_thomPairOver_biUnion`). In
particular the relative homology of the Thom pair `(E, E₀)` vanishes below the rank over a compact
base (`TauCeti.isZero_singularHomology_thomPair_of_compactSpace`).

By the universal coefficient theorem, the same holds for the relative cohomology with projective
coefficients (`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`,
`TauCeti.isZero_singularCohomology_thomPair_of_compactSpace`). This is the vanishing that the
construction of a Thom class by Mayer–Vietoris over a finite trivializing cover uses: since
`Hʳ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V}) = 0`, a class over `U ∪ V` is determined by its restrictions to
`U` and `V`.

## Main definitions

* `Bundle.Trivialization.thomPairOverIso`: over a subset of the base set of a linear
  trivialization it is the Thom pair of a product bundle.

## Main results

* `TauCeti.isZero_singularHomology_thomPairOver_union`: the Mayer–Vietoris step from open sets
  `U` and `V` to `U ∪ V`.
* `TauCeti.isZero_singularHomology_thomPairOver_biUnion`: `Hₙ(E|_W, E₀|_W) = 0` for `n < r` over a
  finite union `W` of trivializing open sets.
* `TauCeti.isZero_singularHomology_thomPair_of_compactSpace`: `Hₙ(E, E₀) = 0` for `n < r` over a
  compact base.
* `TauCeti.isZero_singularCohomology_thomPairOver_biUnion`,
  `TauCeti.isZero_singularCohomology_thomPair_of_compactSpace`: the same for relative cohomology
  with projective coefficients.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, the proof of Theorem 4D.10.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w v u

namespace Bundle.Trivialization

open TauCeti

section Linear

variable (R : Type*) [Semiring R] {B : Type w} [TopologicalSpace B] {F : Type w}
  [TopologicalSpace F] [AddCommMonoid F] [Module R F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]
  (e : Trivialization F (π F E)) [e.IsLinear R] {W : Set B} (hW : W ⊆ e.baseSet)

/-- The map of pairs `(E|_W, E₀|_W) ⟶ (W × F, W × (F ∖ {0}))` given by a linear trivialization
whose base set contains `W`. -/
private def thomPairOverHom : thomPairOver F E W ⟶ prodThomPair W F :=
  TopPair.ofHom (TopCat.isoOfHomeo (e.preimageHomeomorph hW)).hom
    (TopCat.ofHom ⟨fun v ↦ ⟨e.preimageHomeomorph hW ⟨v.1, v.2.1⟩, by
      simpa [preimageHomeomorph_apply] using
        (e.snd_apply_ne_zero_iff R (hW v.2.1)).2 (mem_zeroSectionCompl.1 v.2.2)⟩,
      by fun_prop⟩) (by ext; rfl)

/-- Over a subset `W` of the base set of a linear trivialization `e`, the trivialization identifies
the Thom pair `(E|_W, E₀|_W)` of the restriction with the Thom pair `(W × F, W × (F ∖ {0}))` of the
product bundle. -/
def thomPairOverIso : thomPairOver F E W ≅ prodThomPair W F :=
  have : IsIso (TopPair.Hom.fst (e.thomPairOverHom R hW)) := (TopCat.isoOfHomeo _).isIso_hom
  have := TopPair.isIso_of_isIso_fst_of_surjective_snd (e.thomPairOverHom R hW) fun p ↦ by
    let v := (e.preimageHomeomorph hW).symm p.1
    have hv : e.preimageHomeomorph hW v = p.1 := Homeomorph.apply_symm_apply _ _
    refine ⟨⟨v.1, v.2, mem_zeroSectionCompl.2 ((e.snd_apply_ne_zero_iff R (hW v.2)).1 ?_)⟩,
      Subtype.ext hv⟩
    simpa [preimageHomeomorph_apply, ← hv] using p.2
  asIso (e.thomPairOverHom R hW)

@[simp]
theorem thomPairOverIso_hom_fst_apply (v : π F E ⁻¹' W) :
    TopPair.Hom.fst (e.thomPairOverIso R hW).hom v = (⟨v.1.proj, v.2⟩, (e v).2) :=
  e.preimageHomeomorph_apply hW v

@[simp]
theorem thomPairOverIso_hom_snd_apply (v : (thomPairOver F E W).snd) :
    (TopPair.Hom.snd (e.thomPairOverIso R hW).hom v).1 = (⟨v.1.proj, v.2.1⟩, (e v.1).2) :=
  e.preimageHomeomorph_apply hW ⟨v.1, v.2.1⟩

@[simp]
theorem thomPairOverIso_inv_fst_apply (p : W × F) :
    TopPair.Hom.fst (e.thomPairOverIso R hW).inv p = (e.preimageHomeomorph hW).symm p :=
  (e.preimageHomeomorph hW).eq_symm_apply.2
    ((TopPair.proj₁.mapIso (e.thomPairOverIso R hW)).inv_hom_id_apply p)

@[simp]
theorem thomPairOverIso_inv_snd_apply (p : (prodThomPair W F).snd) :
    (TopPair.Hom.snd (e.thomPairOverIso R hW).inv p).1 = (e.preimageHomeomorph hW).symm p.1 :=
  (congrArg Subtype.val ((TopPair.Hom.w_apply (e.thomPairOverIso R hW).inv p).trans
    (e.thomPairOverIso_inv_fst_apply R hW p.1)) :)

end Linear

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {W : Set B} (hW : W ⊆ e.baseSet)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

include hW in
/-- **The relative homology of the Thom pair over a trivializing set vanishes below the rank**:
for `W` contained in the base set of a linear trivialization, `Hₙ(E|_W, E₀|_W) = 0` for
`n < dim F`. -/
theorem isZero_singularHomology_thomPairOver {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPairOver F E W).singularHomology R n) :=
  (isZero_singularHomology_prodThomPair R W F hn).of_iso
    (asIso (TopPair.singularHomologyMap (e.thomPairOverIso ℝ hW).hom R n))

end Bundle.Trivialization

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

section Empty

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, Zero (E b)]
  [TopologicalSpace (TotalSpace F E)]

/-- The relative homology of the Thom pair over the empty set vanishes. -/
private theorem isZero_singularHomology_thomPairOver_empty (n : ℕ) :
    IsZero ((thomPairOver F E ∅).singularHomology R n) := by
  rw [IsZero.iff_id_eq_zero, ← TopPair.singularHomologyMap_id]
  exact TopPair.singularHomologyMap_eq_zero_of_fac _ R
    (TopCat.ofHom (X := π F E ⁻¹' (∅ : Set B))
      (Y := ↥(π F E ⁻¹' (∅ : Set B) ∩ zeroSectionCompl F E))
      ⟨fun v ↦ v.2.elim, continuous_of_const fun v ↦ v.2.elim⟩) (by ext v; exact v.2.elim) n

end Empty

section Union

variable {B : Type w} [TopologicalSpace B] {F : Type*} [TopologicalSpace F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] {U V : Set B}

/-- **The Mayer–Vietoris step for the Thom pair**: for open sets `U` and `V` of the base, if
`Hₙ(E|_U, E₀|_U)` and `Hₙ(E|_V, E₀|_V)` vanish, and so does `Hₙ₋₁(E|_{U ∩ V}, E₀|_{U ∩ V})` when
`n` is positive, then `Hₙ(E|_{U ∪ V}, E₀|_{U ∪ V})` vanishes. -/
theorem isZero_singularHomology_thomPairOver_union (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (hUn : IsZero ((thomPairOver F E U).singularHomology R n))
    (hVn : IsZero ((thomPairOver F E V).singularHomology R n))
    (hUVn : ∀ m, m + 1 = n → IsZero ((thomPairOver F E (U ∩ V)).singularHomology R m)) :
    IsZero ((thomPairOver F E (U ∪ V)).singularHomology R n) := by
  -- The preimages of `U` and `V` are open in the total space, hence in any subspace, and their
  -- traces on a subspace of nonzero vectors are the traces of the preimages themselves.
  have hopen {W : Set B} (hW : IsOpen W) (T : Set (TotalSpace F E)) :
      IsOpen (((↑) : T → TotalSpace F E) ⁻¹' (π F E ⁻¹' W)) :=
    (hW.preimage (FiberBundle.continuous_proj F E)).preimage continuous_subtype_val
  have hopen₀ {W : Set B} (hW : IsOpen W) {T : Set (TotalSpace F E)}
      (hT : T ⊆ zeroSectionCompl F E) :
      IsOpen (((↑) : T → TotalSpace F E) ⁻¹' (π F E ⁻¹' W ∩ zeroSectionCompl F E)) := by
    convert hopen hW T using 1
    ext x
    simp [hT x.2]
  have hT : π F E ⁻¹' U ∩ zeroSectionCompl F E ∪ π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆
      zeroSectionCompl F E := union_subset inter_subset_right inter_subset_right
  have h := TopCat.isZero_singularHomology_ofInclusion_union R (X := TopCat.of (TotalSpace F E))
    (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
    (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
    (hopen hU _) (hopen hV _) (hopen₀ hU hT) (hopen₀ hV hT) (n := n) hUn hVn fun m hm ↦
      (TopPair.isZero_singularHomology_ofInclusion_congr R
        (inter_subset_left : π F E ⁻¹' (U ∩ V) ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' (U ∩ V))
        (inter_subset_inter inter_subset_left inter_subset_left) preimage_inter
        (inter_inter_distrib_right _ _ _) m).1 (hUVn m hm)
  exact (TopPair.isZero_singularHomology_ofInclusion_congr R
    (union_subset_union inter_subset_left inter_subset_left)
    (inter_subset_left : π F E ⁻¹' (U ∪ V) ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' (U ∪ V))
    preimage_union.symm (union_inter_distrib_right _ _ _).symm n).1 h

end Union

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- **The relative homology of the Thom pair over a finite union of trivializing open sets
vanishes below the rank**: if each of the finitely many open sets `W i`, `i ∈ s`, lies in the base
set of a linear trivialization, then `Hₙ(E|_W, E₀|_W) = 0` for `n < dim F`, where `W` is their
union. -/
theorem isZero_singularHomology_thomPairOver_biUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPairOver F E (⋃ i ∈ s, W i)).singularHomology R n) := by
  classical
  induction s using Finset.induction_on generalizing W n with
  | empty => simpa using isZero_singularHomology_thomPairOver_empty R n
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    refine isZero_singularHomology_thomPairOver_union R (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi))
      (e.isZero_singularHomology_thomPairOver he R hn)
      (ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)) hn) fun m hm ↦ ?_
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the trivializing open sets `W a ∩ W i`, `i ∈ s`.
    rw [inter_iUnion₂]
    refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter
      (hWo i (Finset.mem_insert_of_mem hi))) (fun i hi ↦ ?_) (by omega)
    obtain ⟨e', he', hi'⟩ := hWe i (Finset.mem_insert_of_mem hi)
    exact ⟨e', he', inter_subset_right.trans hi'⟩

/-- **The relative homology of the Thom pair of a vector bundle over a compact base vanishes below
the rank**: `Hₙ(E, E₀) = 0` for `n < dim F`. -/
theorem isZero_singularHomology_thomPair_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {n : ℕ} (hn : n < finrank ℝ F) : IsZero ((thomPair F E).singularHomology R n) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  have h := isZero_singularHomology_thomPairOver_biUnion R t
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hn
  rw [univ_subset_iff.1 ht] at h
  exact h.of_iso (asIso (TopPair.singularHomologyMap (thomPairOverUnivIso F E).inv R n))

section Cohomology

variable {k : Type*} [CommRing k] (R' M' : ModuleCat.{w} k) [Module.Projective k R']

/-- **The relative cohomology of the Thom pair over a finite union of trivializing open sets
vanishes below the rank**: if each of the finitely many open sets `W i`, `i ∈ s`, lies in the base
set of a linear trivialization, then `Hⁿ(E|_W, E₀|_W; R, M) = 0` for `n < dim F`, where `W` is
their union and `R` is projective. -/
theorem isZero_singularCohomology_thomPairOver_biUnion {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology R' k M' n) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R' M' n fun _ hj ↦
    isZero_singularHomology_thomPairOver_biUnion R' s hWo hWe (hj.trans_lt hn)

/-- **The relative cohomology of the Thom pair of a vector bundle over a compact base vanishes
below the rank**: `Hⁿ(E, E₀; R, M) = 0` for `n < dim F`, for `R` projective. -/
theorem isZero_singularCohomology_thomPair_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {n : ℕ} (hn : n < finrank ℝ F) : IsZero ((thomPair F E).singularCohomology R' k M' n) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R' M' n fun _ hj ↦
    isZero_singularHomology_thomPair_of_compactSpace R' (hj.trans_lt hn)

end Cohomology

end TauCeti
