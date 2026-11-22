/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.FramedTube
public import TauCeti.Topology.Compactification.OnePoint.Collapse
public import TauCeti.Topology.Compactification.OnePoint.ZeroSection

/-!
# The shriek map of a framed submanifold through its Thom space

Let `τ : S × V → B` be a framed tube around a compact submanifold `f : S → B` of codimension
`k = dim V`, in a Hausdorff space `B`. The one-point compactification `OnePoint (S × V)` of the
trivial bundle is its Thom space `S₊ ∧ Sᵏ`, and the **Thom collapse**
`c_S : B → OnePoint (S × V)` (`TauCeti.thomCollapse`) sends `τ (x, v)` to `(x, v)` and every point
outside the tube to `∞`. Following it by the projection `OnePoint (S × V) → OnePoint V` gives the
Pontryagin–Thom collapse onto the sphere (`TauCeti.map_snd_thomCollapse`).

The Thom space carries the framed tube `S × V → OnePoint (S × V)` around its zero section
(`TauCeti.isFramedTube_onePoint_coe`), whose complement is contractible
(`TauCeti.contractibleSpace_compl_range_onePoint_zeroSection`). So the homology of the Thom space
in a positive degree `n + k` is its homology relative to that complement, which is the shifted
homology of the zero section:

`H_{n+k}(OnePoint (S × V)) ≅ H_{n+k}(OnePoint (S × V), OnePoint (S × V) ∖ S) ≅ Hₙ(S)`

(`TauCeti.TopCat.onePointProdHomologyIso`). This is the Thom isomorphism of the trivial bundle, read
on its Thom space.

The **shriek map** `i_! : H_{n+k}(B) → Hₙ(f(S))` of the framed submanifold is the map to the
homology of `B` relative to the complement of the core, followed by the local homology along the
core (`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`). It is the map induced by the Thom
collapse, followed by the Thom isomorphism of the Thom space and the map induced by the core
`f : S → f(S)` (`TauCeti.IsFramedTube.coreHom`)
(`TauCeti.TopCat.singularHomologyπ_comp_singularHomologyComplPreimageCoreIso_hom`):

`i_! = f_* ∘ (Thom isomorphism) ∘ (c_S)_*`.

This is how the shriek map of a closed submanifold is computed from its Pontryagin–Thom collapse.
The local homology along the core needs no orientation and no fundamental class: Poincaré duality
enters only when `i_!` is compared with `[S] ⌢ i^* D_B⁻¹`.

## Main definitions

* `TauCeti.thomCollapse τ`: the collapse of `B` onto the Thom space `OnePoint (S × V)`, and
  `TauCeti.IsFramedTube.thomCollapseHom`, the same as a morphism of topological spaces.
* `TauCeti.IsFramedTube.coreHom`: the core `S → f(S)` as a morphism of topological spaces.
* `TauCeti.TopCat.onePointProdHomologyIso`: `H_{n+k}(OnePoint (S × V)) ≅ Hₙ(S)` in positive degrees.

## Main results

* `TauCeti.continuous_thomCollapse`: the Thom collapse is continuous.
* `TauCeti.map_snd_thomCollapse`: the Thom collapse followed by the projection is the
  Pontryagin–Thom collapse onto the sphere.
* `TauCeti.TopCat.onePointProdHomologyIso_hom_comp_map_coreHom`: the Thom isomorphism of the Thom
  space, read in its zero section, is the local homology along the zero section.
* `TauCeti.TopCat.singularHomologyπ_comp_singularHomologyComplPreimageCoreIso_hom`: the shriek map
  of the core is the Thom collapse followed by the Thom isomorphism of the Thom space and the map
  induced by the core.

## Implementation notes

For compact `S` the one-point compactification `OnePoint (S × V)` is homeomorphic to the disc
bundle modulo the sphere bundle, the model `TauCeti.thomSpace` of the Thom space of a general
vector bundle. The one-point model is used here because the Thom collapse is then a
`TauCeti.onePointCollapse`, like the Pontryagin–Thom collapse `TauCeti.pontryaginThomCollapse`
onto `OnePoint V`, and the two are related by the projection `OnePoint (S × V) → OnePoint V`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Remark 9.2.5 (the shriek map of
  a closed submanifold is the Thom isomorphism of its tube).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.D (Thom spaces and the
  Thom isomorphism).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18.
-/

public section

noncomputable section

open CategoryTheory Function Module Set Topology OnePoint

universe u

namespace TauCeti

/-! ### The Thom collapse -/

section Collapse

variable {S V M : Type*}

/-- The **Thom collapse** of a tube `τ : S × V → M` onto the Thom space `OnePoint (S × V)`: the
point `τ (x, v)` goes to `(x, v)`, and every point outside the tube goes to `∞`. It is continuous
when `τ` is an open embedding into a Hausdorff space (`TauCeti.continuous_thomCollapse`). -/
def thomCollapse (τ : S × V → M) : M → OnePoint (S × V) :=
  onePointCollapse τ id

variable {τ : S × V → M}

/-- The Thom collapse is the collapse `TauCeti.onePointCollapse τ id`. -/
theorem thomCollapse_eq_onePointCollapse : thomCollapse τ = onePointCollapse τ id :=
  (rfl)

@[simp]
theorem thomCollapse_apply (hτ : Injective τ) (z : S × V) : thomCollapse τ (τ z) = z :=
  onePointCollapse_apply hτ id z

@[simp]
theorem thomCollapse_of_notMem_range {m : M} (hm : m ∉ range τ) : thomCollapse τ m = ∞ :=
  onePointCollapse_of_notMem_range hm

/-- The Thom collapse sends exactly the points outside the tube to `∞`. -/
theorem thomCollapse_eq_infty_iff (hτ : Injective τ) {m : M} :
    thomCollapse τ m = ∞ ↔ m ∉ range τ :=
  onePointCollapse_eq_infty_iff hτ

/-- The Thom collapse sends `m` to the point `z` of `S × V` exactly when `m = τ z`. -/
theorem thomCollapse_eq_coe_iff (hτ : Injective τ) {m : M} {z : S × V} :
    thomCollapse τ m = z ↔ τ z = m := by
  rw [thomCollapse, onePointCollapse_eq_coe_iff hτ]
  exact ⟨fun ⟨_, hz, hm⟩ ↦ hz ▸ hm, fun hm ↦ ⟨z, rfl, hm⟩⟩

/-- The Thom collapse followed by the projection `OnePoint (S × V) → OnePoint V` is the
Pontryagin–Thom collapse onto `OnePoint V`. -/
theorem map_snd_thomCollapse (hτ : Injective τ) (m : M) :
    OnePoint.map Prod.snd (thomCollapse τ m) = pontryaginThomCollapse τ m := by
  by_cases hm : m ∈ range τ
  · obtain ⟨z, rfl⟩ := hm
    rw [thomCollapse_apply hτ, OnePoint.map_some, pontryaginThomCollapse_apply hτ]
  · rw [thomCollapse_of_notMem_range hm, pontryaginThomCollapse_of_notMem_range hm,
      OnePoint.map_infty]

variable [TopologicalSpace S] [TopologicalSpace V] [TopologicalSpace M]

/-- The Thom collapse of an open embedding `τ : S × V → M` into a Hausdorff space is
continuous. -/
theorem continuous_thomCollapse [T2Space M] (hτ : IsOpenEmbedding τ) :
    Continuous (thomCollapse τ) :=
  continuous_onePointCollapse hτ isProperMap_id

variable [Zero V]

/-- The Thom space `OnePoint (S × V)` is a framed tube around its zero section `x ↦ (x, 0)`, through
the inclusion of `S × V`. -/
theorem isFramedTube_onePoint_coe :
    IsFramedTube (fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V))) ((↑) : S × V → OnePoint (S × V)) :=
  ⟨isOpenEmbedding_coe, fun _ ↦ rfl⟩

/-- The Thom collapse sends the core of a framed tube to the zero section. -/
@[simp]
theorem IsFramedTube.thomCollapse_apply_self {f : S → M} (h : IsFramedTube f τ) (x : S) :
    thomCollapse τ (f x) = ((x, (0 : V)) : S × V) := by
  rw [← h.apply_zero, thomCollapse_apply h.isOpenEmbedding.injective]

/-- The Thom collapse of a framed tube sends exactly the points of the core to the zero section. -/
theorem IsFramedTube.thomCollapse_mem_range_iff {f : S → M} (hτ : IsFramedTube f τ) {m : M} :
    thomCollapse τ m ∈ range (fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V))) ↔ m ∈ range f := by
  refine exists_congr fun x ↦ ?_
  rw [eq_comm, thomCollapse, onePointCollapse_eq_coe_iff hτ.isOpenEmbedding.injective]
  simp [hτ.apply_zero]

end Collapse

/-! ### The core and the collapse as morphisms -/

namespace IsFramedTube

variable {S V : Type u} [TopologicalSpace S] {B : _root_.TopCat.{u}} {f : S → B}

/-- The core `f : S → f(S)` of a framed tube, as a morphism to the preimage of `f(S)` under the
identity of `B`, the form in which the local homology along the core is stated. -/
def coreHom [TopologicalSpace V] [Zero V] {τ : S × V → B} (hτ : IsFramedTube f τ) :
    _root_.TopCat.of S ⟶ _root_.TopCat.of ↥((𝟙 B) ⁻¹' range f) :=
  _root_.TopCat.ofHom ⟨fun x ↦ ⟨f x, mem_range_self x⟩, hτ.continuous.subtype_mk _⟩

-- Not `@[simp]`: `simp` rewrites the preimage under the identity in the type of the codomain, so
-- the left-hand side is not in simp normal form.
lemma coe_coreHom_apply [TopologicalSpace V] [Zero V] {τ : S × V → B} (hτ : IsFramedTube f τ)
    (x : S) : (hτ.coreHom x : B) = f x :=
  (rfl)

/-- The Thom collapse of a framed tube, as a morphism of topological spaces. -/
def thomCollapseHom [NormedAddCommGroup V] [T2Space B] {τ : S × V → B} (hτ : IsFramedTube f τ) :
    B ⟶ _root_.TopCat.of (OnePoint (S × V)) :=
  _root_.TopCat.ofHom ⟨thomCollapse τ, continuous_thomCollapse hτ.isOpenEmbedding⟩

@[simp]
lemma thomCollapseHom_apply [NormedAddCommGroup V] [T2Space B] {τ : S × V → B}
    (hτ : IsFramedTube f τ) (b : B) : hτ.thomCollapseHom b = thomCollapse τ b :=
  (rfl)

end IsFramedTube

/-! ### The shriek map through the Thom space -/

namespace TopCat

section ThomSpace

variable {S V : Type u} [TopologicalSpace S] [CompactSpace S] [T2Space S] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] {R : Type*} [Ring R] (M : ModuleCat.{u} R)

omit [CompactSpace S] [FiniteDimensional ℝ V] in
/-- The quotient map from the homology of the Thom space to its homology relative to the complement
of the zero section is an isomorphism in positive degrees, since that complement is contractible. -/
theorem isIso_singularHomologyπ_onePointProd (m : ℕ) :
    IsIso ((TopPair.ofSubset ((𝟙 (_root_.TopCat.of (OnePoint (S × V)))) ⁻¹'
      range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)))ᶜ).singularHomologyπ M (m + 1)) :=
  -- Instance search does not see through the subspace of `TopPair.ofSubset`, so the
  -- contractibility of the complement of the zero section is supplied explicitly.
  @TopPair.isIso_singularHomologyπ_of_contractibleSpace _ _ _ _ _ M
    contractibleSpace_compl_range_onePoint_zeroSection m

omit [CompactSpace S] [T2Space S] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The zero section `S → OnePoint (S × V)` is a homeomorphism onto its image. -/
private def zeroSectionHomeomorph :
    S ≃ₜ ↥((𝟙 (_root_.TopCat.of (OnePoint (S × V)))) ⁻¹'
      range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V))) :=
  (isOpenEmbedding_coe.isEmbedding.comp (isEmbedding_prodMkLeft (0 : V))).toHomeomorph

omit [CompactSpace S] [T2Space S] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The zero section is the core of the framed tube of the Thom space. -/
private lemma isoOfHomeo_zeroSectionHomeomorph_hom :
    (_root_.TopCat.isoOfHomeo (zeroSectionHomeomorph (S := S) (V := V))).hom =
      isFramedTube_onePoint_coe.coreHom := by
  ext x
  rfl

/-- **The Thom isomorphism of a trivial bundle, on its Thom space.** For a compact Hausdorff space
`S` and a real normed space `V` of finite dimension `k`, the homology of the Thom space
`OnePoint (S × V)` in a positive degree `n + k` is the homology of `S` in degree `n`. It is the
quotient map onto the homology relative to the complement of the zero section, an isomorphism
because that complement is contractible, followed by the local homology along the zero section
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`) and the identification of the zero section
with `S` (`TauCeti.TopCat.onePointProdHomologyIso_hom_comp_map_coreHom`). -/
def onePointProdHomologyIso (n m : ℕ) (h : n + finrank ℝ V = m + 1) :
    (_root_.TopCat.toSSet.obj (_root_.TopCat.of (OnePoint (S × V)))).homology M (m + 1) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj
        (_root_.TopCat.of S) :=
  @asIso _ _ _ _ _ (isIso_singularHomologyπ_onePointProd M m) ≪≫
    singularHomologyComplPreimageCoreIso isFramedTube_onePoint_coe M
      isFramedTube_onePoint_coe.isClosed_range one_pos (serreFibrations.of_isIso _) n (m + 1) h ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).mapIso
      (_root_.TopCat.isoOfHomeo zeroSectionHomeomorph).symm

private lemma onePointProdHomologyIso_hom_eq (n m : ℕ) (h : n + finrank ℝ V = m + 1) :
    (onePointProdHomologyIso M n m h).hom =
      (TopPair.ofSubset ((𝟙 (_root_.TopCat.of (OnePoint (S × V)))) ⁻¹'
          range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)))ᶜ).singularHomologyπ M (m + 1) ≫
        (singularHomologyComplPreimageCoreIso isFramedTube_onePoint_coe M
          isFramedTube_onePoint_coe.isClosed_range one_pos (serreFibrations.of_isIso _) n (m + 1)
          h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.isoOfHomeo zeroSectionHomeomorph).inv :=
  (rfl)

/-- `TauCeti.TopCat.onePointProdHomologyIso`, read in the zero section of the Thom space, is the
quotient map onto the homology relative to the complement of the zero section followed by the
local homology along the zero section. -/
@[reassoc]
lemma onePointProdHomologyIso_hom_comp_map_coreHom (n m : ℕ) (h : n + finrank ℝ V = m + 1) :
    (onePointProdHomologyIso M n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (isFramedTube_onePoint_coe.coreHom) =
      (TopPair.ofSubset ((𝟙 (_root_.TopCat.of (OnePoint (S × V)))) ⁻¹'
          range fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V)))ᶜ).singularHomologyπ M (m + 1) ≫
        (singularHomologyComplPreimageCoreIso isFramedTube_onePoint_coe M
          isFramedTube_onePoint_coe.isClosed_range one_pos (serreFibrations.of_isIso _) n (m + 1)
          h).hom := by
  rw [onePointProdHomologyIso_hom_eq]
  -- The source of the quotient map is the homology of the Thom space only up to unfolding, which
  -- `rw` does not see through, so the first reassociation is applied as a term.
  refine (Category.assoc _ _ _).trans ?_
  rw [Category.assoc, ← Functor.map_comp, ← isoOfHomeo_zeroSectionHomeomorph_hom, Iso.inv_hom_id]
  exact congrArg _ (by rw [CategoryTheory.Functor.map_id, Category.comp_id])

end ThomSpace

section Collapse

variable {S V : Type u} [TopologicalSpace S] [NormedAddCommGroup V] {B : _root_.TopCat.{u}}
  [T2Space B] {f : S → B} {τ : S × V → B} (hτ : IsFramedTube f τ)

variable [CompactSpace S] [T2Space S] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {R : Type*}
  [Ring R] (M : ModuleCat.{u} R)

/-- **The shriek map of a framed submanifold is the Thom collapse followed by the Thom
isomorphism.** Let `τ : S × V → B` be a framed tube around `f : S → B`, with `S` compact
Hausdorff and `B` Hausdorff, and let `m + 1 = n + dim V`. The shriek map
`H_{m+1}(B) → Hₙ(f(S))`, the map to the homology of `B` relative to the complement of the core
followed by the local homology along the core
(`TauCeti.TopCat.singularHomologyComplPreimageCoreIso`), is the map induced by the Thom collapse
`B → OnePoint (S × V)`, followed by the Thom isomorphism `H_{m+1}(OnePoint (S × V)) ≅ Hₙ(S)` of
the Thom space (`TauCeti.TopCat.onePointProdHomologyIso`) and the map induced by `f : S → f(S)`. -/
theorem singularHomologyπ_comp_singularHomologyComplPreimageCoreIso_hom (n m : ℕ)
    (h : n + finrank ℝ V = m + 1) :
    (TopPair.ofSubset ((𝟙 B) ⁻¹' range f)ᶜ).singularHomologyπ M (m + 1) ≫
        (singularHomologyComplPreimageCoreIso hτ M hτ.isClosed_range one_pos
          (serreFibrations.of_isIso _) n (m + 1) h).hom =
      SSet.homologyMap (_root_.TopCat.toSSet.map (hτ.thomCollapseHom)) M (m + 1) ≫
        (onePointProdHomologyIso M n m h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (hτ.coreHom) := by
  have hg : hτ.thomCollapseHom ≫ 𝟙 _ = 𝟙 B ≫ hτ.thomCollapseHom := by simp
  have hs : ∀ x v, hτ.thomCollapseHom (τ (x, v)) = ((x, v) : OnePoint (S × V)) := fun x v ↦
    thomCollapse_apply hτ.isOpenEmbedding.injective (x, v)
  have hsf : ∀ b, hτ.thomCollapseHom b ∈ range (fun x : S ↦ ((x, (0 : V)) : OnePoint (S × V))) →
      b ∈ range f := fun _ hx ↦ hτ.thomCollapse_mem_range_iff.1 hx
  have hπ := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap (hτ.thomCollapseHom) (mapsTo_compl_preimage_range_compl_preimage_range hg
      hsf)) M (m + 1)
  rw [TopPair.ofSubsetMap_fst] at hπ
  -- The collapse sends the point `f x` of the core to the point `(x, 0)` of the zero section, so
  -- the composite of the three maps of cores is the identity.
  have hid : (hτ.thomCollapseHom).preimageMapOver hg
      (mapsTo_range_of_apply_eq isFramedTube_onePoint_coe hτ (φ := id) hs) ≫
        (_root_.TopCat.isoOfHomeo (zeroSectionHomeomorph (S := S) (V := V))).inv ≫ hτ.coreHom =
        𝟙 _ := by
    ext ⟨b, x, hx⟩
    obtain rfl : f x = b := hx
    have hx' : zeroSectionHomeomorph.symm
        ((hτ.thomCollapseHom).preimageMapOver hg
          (mapsTo_range_of_apply_eq isFramedTube_onePoint_coe hτ (φ := id) hs) ⟨f x, x, rfl⟩) =
        x := by
      rw [Homeomorph.symm_apply_eq]
      apply Subtype.ext
      rw [TopCat.Hom.coe_preimageMapOver_apply, IsFramedTube.thomCollapseHom_apply]
      exact hτ.thomCollapse_apply_self x
    simp only [ConcreteCategory.comp_apply, _root_.TopCat.isoOfHomeo_inv, _root_.TopCat.hom_ofHom,
      ContinuousMap.coe_ofClass, hx']
    rfl
  have key : TopPair.singularHomologyMap (TopPair.ofSubsetMap (hτ.thomCollapseHom)
      (mapsTo_compl_preimage_range_compl_preimage_range hg hsf)) M (m + 1) ≫
        (singularHomologyComplPreimageCoreIso isFramedTube_onePoint_coe M
          isFramedTube_onePoint_coe.isClosed_range one_pos (serreFibrations.of_isIso _) n (m + 1)
          h).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (_root_.TopCat.isoOfHomeo (zeroSectionHomeomorph (S := S) (V := V))).inv ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (hτ.coreHom) =
      (singularHomologyComplPreimageCoreIso hτ M hτ.isClosed_range one_pos
          (serreFibrations.of_isIso _) n (m + 1) h).hom := by
    rw [singularHomologyComplPreimageCoreIso_hom_naturality_of_apply_eq_assoc
      isFramedTube_onePoint_coe hτ hg hs hsf, ← Functor.map_comp, ← Functor.map_comp, hid,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← key, ← Category.assoc, ← hπ, onePointProdHomologyIso_hom_eq]
  -- The two sides differ by associativity, across the identification of the source of the
  -- quotient map with the homology of the Thom space, which `rw` does not see through.
  exact (Category.assoc _ _ _).trans
    (congrArg _ ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).symm)

end Collapse

end TopCat

end TauCeti
