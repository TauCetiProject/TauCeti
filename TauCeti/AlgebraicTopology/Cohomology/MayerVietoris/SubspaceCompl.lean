/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Compl
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.SubspaceCompl

/-!
# Relative cohomology modulo the preimage of the complement of a subspace

Let `q : X → F` be a continuous map to a real normed space of finite dimension `r`, and for a
subspace `W` of `F` let `(X, q⁻¹(F ∖ W))` be the pair `TauCeti.subspaceComplPair q ∅ W`. Assume
that `X` has vanishing relative singular cohomology modulo the preimage of the complement of every
closed half-subspace: for every subspace `W'` of `F` and every functional `φ` on `F` with `φ v = 1`
for some `v ∈ W'`, the pair `(X, q⁻¹(F ∖ {y ∈ W' | φ y ≤ 0}))` has vanishing cohomology. Then

`Hⁿ(X, ∅) ≅ Hᵐ(X, q⁻¹(F ∖ W))`

for `W` of codimension `c` and `m = n + c` (`TauCeti.subspaceComplPairSingularCohomologyIso`),
naturally in maps over `F` (`TauCeti.subspaceComplPairSingularCohomologyIso_hom_naturality`).

This is the cohomological form of `TauCeti.subspaceComplPairSingularHomologyIso`, with the same
proof. The computation removes one dimension at a time, along the extensions `W ⊆ W'` of
`Submodule.LineExtension`. For the extension `ψ = Submodule.LineExtension.extension` to `F` of the
functional of the step, the closed sets `S± = q⁻¹{y ∈ W' | ±ψ y ≤ 0}` have union `q⁻¹(W')` and
intersection `q⁻¹(W)`. The pairs `(X, X ∖ S±)` have vanishing cohomology by assumption, so the
Mayer–Vietoris sequence of the complements of two closed sets
(`TopCat.singularCohomologyComplMayerVietorisδ`) gives `Hⁿ(X, q⁻¹(F ∖ W')) ≅ Hⁿ⁺¹(X, q⁻¹(F ∖ W))`.

For a Serre fibration over a disk, this computes the cohomology of the total space modulo the part
over the boundary sphere (`TauCeti.TopCat.singularCohomologyPreimageSphereIso`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D, the proof of Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits Module

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {X X' : TopCat.{w}} (q : C(X, F))
  {q' : C(X', F)}

namespace SubspaceComplPairCohomology

/-- The preimage of the closed half-subspace `{y ∈ W | φ y ≤ 0}`. -/
private abbrev closedHalf (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) : Set X :=
  q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}

private lemma isClosed_closedHalf [FiniteDimensional ℝ F] (W : Submodule ℝ F)
    (φ : F →ₗ[ℝ] ℝ) : IsClosed (closedHalf q W φ) :=
  (W.isClosed_of_finiteDimensional.inter (isClosed_le φ.continuous_of_finiteDimensional
    continuous_const)).preimage q.continuous

variable {W : Submodule ℝ F}

/-- The identification of the pair modulo the complement of the union of the two closed
half-subspaces of a step with `(X, q⁻¹(F ∖ W'))`. -/
private def unionIso (s : W.LineExtension) :
    TopPair.ofSubset (closedHalf q s.W' s.extension ∪ closedHalf q s.W' (-s.extension))ᶜ ≅
      subspaceComplPair q ∅ s.W' :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun x ↦ by
    rw [Set.empty_union, Set.compl_union, ← Set.preimage_compl, ← Set.preimage_compl,
      ← Set.preimage_inter, s.compl_inter_compl]
    rfl

/-- The identification of `(X, q⁻¹(F ∖ W))` with the pair modulo the complement of the
intersection of the two closed half-subspaces of a step. -/
private def interIso (s : W.LineExtension) :
    subspaceComplPair q ∅ W ≅
      TopPair.ofSubset (closedHalf q s.W' s.extension ∩ closedHalf q s.W' (-s.extension))ᶜ :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun x ↦ by
    rw [Set.empty_union, Set.compl_inter, ← Set.preimage_compl, ← Set.preimage_compl,
      ← Set.preimage_union, s.compl_union_compl s.extension_comp]
    rfl

variable (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
  IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularCohomology R k M n))

include hq

variable [FiniteDimensional ℝ F]

private lemma isIso_singularCohomologyComplMayerVietorisδ (s : W.LineExtension) (n : ℕ) :
    IsIso (TopCat.singularCohomologyComplMayerVietorisδ R k M
      (isClosed_closedHalf q s.W' s.extension) (isClosed_closedHalf q s.W' (-s.extension))
      n (n + 1) rfl) := by
  have hpos (m : ℕ) :=
    ModuleCat.isZero_iff_subsingleton.1 (hq _ s.extension _ s.v.property s.extension_apply_v m)
  have hneg (m : ℕ) :=
    ModuleCat.isZero_iff_subsingleton.1 (hq _ (-s.extension) _ (neg_mem s.v.property) (by simp) m)
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, fun z ↦ ?_⟩
  · -- A class killed by the connecting morphism comes from the two vanishing groups.
    refine (injective_iff_map_eq_zero (TopCat.singularCohomologyComplMayerVietorisδ R k M
      (isClosed_closedHalf q s.W' s.extension) (isClosed_closedHalf q s.W' (-s.extension))
      n (n + 1) rfl).hom).2 fun a ha ↦ ?_
    obtain ⟨b, c, rfl⟩ := TopCat.exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero
      (isClosed_closedHalf q s.W' s.extension) (isClosed_closedHalf q s.W' (-s.extension)) rfl a ha
    rw [(hpos n).elim b 0, (hneg n).elim c 0, map_zero, map_zero, sub_zero]
  · -- Every class restricts to zero in the two vanishing groups, so is a connecting image.
    exact TopCat.exists_singularCohomologyComplMayerVietorisδ_eq
      (isClosed_closedHalf q s.W' s.extension) (isClosed_closedHalf q s.W' (-s.extension)) rfl z
      ((hpos (n + 1)).elim _ _) ((hneg (n + 1)).elim _ _)

/-- One step of the computation: `Hⁿ(X, q⁻¹(F ∖ W')) ≅ Hⁿ⁺¹(X, q⁻¹(F ∖ W))`. -/
private def stepIso (s : W.LineExtension) (n : ℕ) :
    (subspaceComplPair q ∅ s.W').singularCohomology R k M n ≅
      (subspaceComplPair q ∅ W).singularCohomology R k M (n + 1) :=
  TopPair.singularCohomologyMapIso R k M (unionIso q s) n ≪≫
    @asIso _ _ _ _ _ (isIso_singularCohomologyComplMayerVietorisδ R k M q hq s n) ≪≫
    TopPair.singularCohomologyMapIso R k M (interIso q s) (n + 1)

private lemma stepIso_hom (s : W.LineExtension) (n : ℕ) :
    (stepIso R k M q hq s n).hom =
      TopPair.singularCohomologyMap (unionIso q s).hom n ≫
        TopCat.singularCohomologyComplMayerVietorisδ R k M
          (isClosed_closedHalf q s.W' s.extension) (isClosed_closedHalf q s.W' (-s.extension))
          n (n + 1) rfl ≫
        TopPair.singularCohomologyMap (interIso q s).hom (n + 1) := by
  simp only [stepIso, Iso.trans_hom, TopPair.singularCohomologyMapIso_hom, asIso_hom]

variable {q} (hq' : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
  IsZero ((TopPair.ofSubset (q' ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularCohomology R k M n))
  (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)

private lemma stepIso_hom_naturality (s : W.LineExtension) (n : ℕ) :
    (stepIso R k M q' hq' s n).hom ≫
        TopPair.singularCohomologyMap (subspaceComplPairMap f hf (Set.mapsTo_empty _ _) W) (n + 1) =
      TopPair.singularCohomologyMap (subspaceComplPairMap f hf (Set.mapsTo_empty _ _) s.W') n ≫
        (stepIso R k M q hq s n).hom := by
  have hS := Set.mapsTo_preimage_of_apply_eq f hf {y | y ∈ s.W' ∧ s.extension y ≤ 0}ᶜ
  have hT := Set.mapsTo_preimage_of_apply_eq f hf {y | y ∈ s.W' ∧ (-s.extension) y ≤ 0}ᶜ
  have hU : Set.MapsTo f (closedHalf q s.W' s.extension ∪ closedHalf q s.W' (-s.extension))ᶜ
      (closedHalf q' s.W' s.extension ∪ closedHalf q' s.W' (-s.extension))ᶜ :=
    fun x hx h ↦ hx (by simpa only [Set.mem_union, Set.mem_preimage, hf] using h)
  have hI : Set.MapsTo f (closedHalf q s.W' s.extension ∩ closedHalf q s.W' (-s.extension))ᶜ
      (closedHalf q' s.W' s.extension ∩ closedHalf q' s.W' (-s.extension))ᶜ :=
    fun x hx h ↦ hx (by simpa only [Set.mem_inter_iff, Set.mem_preimage, hf] using h)
  have hunion : (unionIso q s).hom ≫ subspaceComplPairMap f hf (Set.mapsTo_empty _ _) s.W' =
      TopPair.ofSubsetMap f hU ≫ (unionIso q' s).hom := by
    simp only [unionIso, subspaceComplPairMap_eq_ofSubsetMap f hf (Set.mapsTo_empty _ _) _
      ((Set.mapsTo_empty _ _).union_union (Set.mapsTo_preimage_of_apply_eq f hf _)),
      TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  have hinter : (interIso q s).hom ≫ TopPair.ofSubsetMap f hI =
      subspaceComplPairMap f hf (Set.mapsTo_empty _ _) W ≫ (interIso q' s).hom := by
    simp only [interIso, subspaceComplPairMap_eq_ofSubsetMap f hf (Set.mapsTo_empty _ _) _
      ((Set.mapsTo_empty _ _).union_union (Set.mapsTo_preimage_of_apply_eq f hf _)),
      TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ rfl
  rw [stepIso_hom, stepIso_hom, Category.assoc, Category.assoc]
  rw [← TopPair.singularCohomologyMap_comp, ← hinter, TopPair.singularCohomologyMap_comp,
    TopCat.singularCohomologyComplMayerVietorisδ_naturality_assoc R k M
      (isClosed_closedHalf q s.W' s.extension) (isClosed_closedHalf q s.W' (-s.extension))
      (isClosed_closedHalf q' s.W' s.extension) (isClosed_closedHalf q' s.W' (-s.extension)) f
      hS hT n (n + 1) rfl,
    ← TopPair.singularCohomologyMap_comp_assoc, ← hunion, TopPair.singularCohomologyMap_comp_assoc]

end SubspaceComplPairCohomology

open SubspaceComplPairCohomology

variable [FiniteDimensional ℝ F]
  (hq : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (q ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularCohomology R k M n))

/-- **The cohomology modulo the preimage of the complement of a subspace.** If `X` has vanishing
cohomology modulo the preimage under `q` of the complement of every closed half-subspace of `F`,
then `Hⁿ(X, ∅) ≅ Hᵐ(X, q⁻¹(F ∖ W))` for `W` of codimension `c` and `m = n + c`.

The isomorphism is the composite of `c` Mayer–Vietoris connecting morphisms, for a fixed choice of
a flag of subspaces of `F` (`Submodule.lineExtension`) that does not depend on `X`. -/
def subspaceComplPairSingularCohomologyIso :
    ∀ (c : ℕ) (W : Submodule ℝ F), finrank ℝ W + c = finrank ℝ F → ∀ (n m : ℕ), n + c = m →
      ((subspaceComplPair q ∅ (⊤ : Submodule ℝ F)).singularCohomology R k M n ≅
        (subspaceComplPair q ∅ W).singularCohomology R k M m)
  | 0, _, hW, n, _, rfl =>
    TopPair.singularCohomologyMapIso R k M
      (subspaceComplPairTopIso q ∅ (Submodule.eq_top_of_finrank_eq hW)) n
  | c + 1, W, hW, n, _, rfl =>
    let s := W.lineExtension (Submodule.lt_top_of_finrank_lt_finrank (by omega)).ne
    subspaceComplPairSingularCohomologyIso c s.W' (by rw [s.finrank_eq]; omega) n (n + c) rfl ≪≫
      stepIso R k M q hq s (n + c)

variable {q} (hq' : ∀ (W : Submodule ℝ F) (φ : F →ₗ[ℝ] ℝ) (v : F), v ∈ W → φ v = 1 → ∀ n,
    IsZero ((TopPair.ofSubset (q' ⁻¹' {y | y ∈ W ∧ φ y ≤ 0}ᶜ)).singularCohomology R k M n))
  (f : X ⟶ X') (hf : ∀ x, q' (f x) = q x)

/-- The isomorphism `Hⁿ(X, ∅) ≅ Hᵐ(X, q⁻¹(F ∖ W))`, for `m = n + c` with `c` the codimension of
`W`, is natural in maps over `F`. -/
@[reassoc]
theorem subspaceComplPairSingularCohomologyIso_hom_naturality :
    ∀ (c : ℕ) (W : Submodule ℝ F) (hW : finrank ℝ W + c = finrank ℝ F) (n m : ℕ)
      (h : n + c = m),
      (subspaceComplPairSingularCohomologyIso R k M q' hq' c W hW n m h).hom ≫
          TopPair.singularCohomologyMap (subspaceComplPairMap f hf (Set.mapsTo_empty _ _) W) m =
        TopPair.singularCohomologyMap (subspaceComplPairMap f hf (Set.mapsTo_empty _ _) ⊤) n ≫
          (subspaceComplPairSingularCohomologyIso R k M q hq c W hW n m h).hom
  | 0, W, hW, n, _, rfl => by
    rw [subspaceComplPairSingularCohomologyIso, subspaceComplPairSingularCohomologyIso,
      TopPair.singularCohomologyMapIso_hom, TopPair.singularCohomologyMapIso_hom,
      ← TopPair.singularCohomologyMap_comp, subspaceComplPairTopIso_hom_naturality,
      TopPair.singularCohomologyMap_comp]
    -- The degree `n + 0` of the left side is `n`.
    rfl
  | c + 1, W, hW, n, _, rfl => by
    rw [subspaceComplPairSingularCohomologyIso, subspaceComplPairSingularCohomologyIso,
      Iso.trans_hom, Iso.trans_hom, Category.assoc]
    -- The degree `n + (c + 1)` is `n + c + 1` by definition, so the step is applied by `trans`.
    refine (congrArg (_ ≫ ·) (stepIso_hom_naturality R k M hq hq' f hf _ (n + c))).trans ?_
    rw [← Category.assoc, subspaceComplPairSingularCohomologyIso_hom_naturality c, Category.assoc]

end TauCeti
