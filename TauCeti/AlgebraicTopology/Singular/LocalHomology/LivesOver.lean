/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Kunneth.Relative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Classes living over the fundamental class

Let `p : E → M` be a map to an `n`-manifold, for instance the projection of a fibration
`F ↪ E → M`, and let `b ∈ M`. Barraud, Damian, Humilière and Oancea say that a class
`α ∈ Hₖ(E)` **lives over the fundamental class** of `M` if its image under the shriek map
`j_! : Hₖ(E) → Hₖ₋ₙ(F_b)` of the inclusion `j` of the point `b` is nonzero (their Definition 2.3
and Example 2.4). By their Lemma 2.9 this shriek map is the map to the homology of `E` relative
to the part of `E` lying over the complement of a small disc around `b`, followed by an
identification of that relative group with `Hₖ₋ₙ(F_b)`.

This file works with the topological form of that criterion. The **localization at the fibre**
over `b` is the map

`Hₖ(E) → Hₖ(E, E ∖ p⁻¹(b))`

(`TauCeti.fiberLocalization`), and a class lives over the fundamental class at `b` if its
localization is nonzero (`TauCeti.LivesOverFundamentalClass`). Being nonzero does not depend on
the identification of the relative group with the homology of the fibre, which is therefore not
needed for the statements below.

* **Naturality** (the topological form of the source's Proposition 2.12). A map `σ : E → E'` over
  `M`, that is with `p' ∘ σ = p`, is a map of pairs `(E, E ∖ p⁻¹(b)) → (E', E' ∖ p'⁻¹(b))`, and
  localization commutes with it (`TauCeti.homologyMap_comp_fiberLocalization`). Hence if `σ_* α`
  lives over the fundamental class, so does `α`
  (`TauCeti.LivesOverFundamentalClass.of_homologyMap`). With `σ = p` and `p' = id`, a class lives
  over the fundamental class as soon as its image in `Hₖ(M)` does
  (`TauCeti.LivesOverFundamentalClass.of_homologyMap_proj`).
* **Products with a second factor.** For a space `Y`, the map `p ∘ fst : E × Y → M` has fibre
  `p⁻¹(b) × Y`, and localizing a cross product `α × β` at it is the relative cross product of the
  localization of `α` with `β` (`TauCeti.fiberLocalization_singularHomologyCross_tmul`). So if
  `α × β` lives over the fundamental class, so does `α`
  (`TauCeti.LivesOverFundamentalClass.of_singularHomologyCross`), and `β ≠ 0`
  (`TauCeti.LivesOverFundamentalClass.right_ne_zero_of_singularHomologyCross`). When the relative
  cross product is injective, for instance over a field by the relative Künneth theorem, and the
  homology is projective over a ring without zero divisors, the converse holds
  (`TauCeti.livesOverFundamentalClass_singularHomologyCross_iff`,
  `TauCeti.livesOverFundamentalClass_singularHomologyCross_iff_of_field`).
* **Products of two maps.** For `p : E → M` and `q : Y → N`, the fibre of
  `p × q : E × Y → M × N` over `(b, c)` is `p⁻¹(b) × q⁻¹(c)`. If `α × β` lives over the fundamental
  class at `(b, c)`, then `α` lives over it at `b` and `β` at `c`
  (`TauCeti.LivesOverFundamentalClass.left_of_singularHomologyCross_prodMap`,
  `TauCeti.LivesOverFundamentalClass.right_of_singularHomologyCross_prodMap`). Over a field, and
  with closed fibres, the converse holds
  (`TauCeti.LivesOverFundamentalClass.singularHomologyCross_prodMap`,
  `TauCeti.livesOverFundamentalClass_prodMap_singularHomologyCross_iff_of_field`). Write
  `A = E ∖ p⁻¹(b)` and `B = Y ∖ q⁻¹(c)`. By excision, a class of `Hₙ(E × Y, A × Y)` dies in
  `Hₙ(E × Y, A × Y ∪ E × B)` only if it comes from `Hₙ(E × B, A × B)`
  (`TopCat.exists_singularHomologyMap_ofSubsetMap_tensorHom_eq`); by the relative Künneth
  theorem the class `(loc α) × β` does not when `β` does not come from `B`
  (`TopCat.singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel_of_field`). This
  is the
  localization statement behind the source's Proposition 6.13 (products of manifolds abundant
  with 2-spheres), with coefficients in a field.
* **The trivial fibration.** For the identity of a compact oriented `n`-manifold `M` and integer
  coefficients, the localization of `Hₙ(M)` at a point is the map to the local homology
  `Hₙ(M, M ∖ {b})`, and the multiple `d • [M]` of the fundamental class lives over the
  fundamental class exactly when `d ≠ 0`
  (`TauCeti.HomologicalOrientation.livesOverFundamentalClass_id_zsmul_fundamentalClass_iff`). When
  `M` is moreover connected, the classes of `Hₙ(M)` that live over the fundamental class are
  exactly the nonzero ones (`TauCeti.HomologicalOrientation.livesOverFundamentalClass_id_iff`).
  This is the remark following the source's Definition 2.3: for trivial coefficients these are
  the nonzero multiples of the fundamental class.
* **Classes of nonzero degree.** If `α ∈ Hₙ(E; ℤ)` satisfies `p_* α = d • [M]` with `d ≠ 0`, then
  `α` lives over the fundamental class at every point
  (`TauCeti.HomologicalOrientation.livesOverFundamentalClass_of_homologyMap_eq_zsmul`). In
  particular, for a compact oriented `n`-manifold `S` and a map `φ : S → E` such that
  `(p ∘ φ)_*[S] = d • [M]` with `d ≠ 0`, the class `φ_*[S]` lives over the fundamental class
  (`TauCeti.HomologicalOrientation.livesOverFundamentalClass_mapFundamentalClass`); this is the
  degree hypothesis of the source's Theorems 5.10 and 5.14, stated homologically. For a section
  `s` of `p` the class `s_*[M]` lives over the fundamental class
  (`TauCeti.HomologicalOrientation.livesOverFundamentalClass_mapFundamentalClass_of_section`), as
  for the constant spheres in the evaluation fibration `Map(S², Q) → Q` of the source's §6.3.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4 (Definition 2.3, Example 2.4,
  Lemma 2.9, Proposition 2.12) and §§5–6 (Proposition 6.13).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, local homology and fundamental classes, and Section 3.B, the relative Künneth
  formula.
-/

public section

noncomputable section

open CategoryTheory Limits Set MonoidalCategory

universe w v u

namespace TauCeti

section Localization

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {E E' M : Type w} [TopologicalSpace E] [TopologicalSpace E']

/-- The **localization at the fibre** of a map `p : E → M` over a point `b`: the map
`Hₖ(E) → Hₖ(E, E ∖ p⁻¹(b))` from the singular homology of `E` to its homology relative to the
complement of the fibre. A class lives over the fundamental class of `M` at `b` when its
localization is nonzero (`TauCeti.LivesOverFundamentalClass`). -/
abbrev fiberLocalization (p : E → M) (b : M) (k : ℕ) :
    (TopCat.toSSet.obj (TopCat.of E)).homology R k ⟶ localHomology R (p ⁻¹' {b}) k :=
  (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E))).singularHomologyπ R k

/-- **Naturality of the localization at the fibre**: for a map `σ : E → E'` over `M`, that is with
`p' ∘ σ = p`, localizing `σ_* α` at the fibre of `p'` over `b` is the image under `σ` of the
localization of `α` at the fibre of `p`. This is the topological form of the naturality of the
shriek map of a point under maps of fibrations (Barraud–Damian–Humilière–Oancea,
Proposition 2.12). -/
@[reassoc]
theorem homologyMap_comp_fiberLocalization (σ : C(E, E')) {p : E → M} {p' : E' → M}
    (h : p' ∘ σ = p) (b : M) (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) R k ≫ fiberLocalization R p' b k =
      fiberLocalization R p b k ≫
        localHomologyMap R σ (by rw [← preimage_comp, h]) k := by
  have hσ : σ ⁻¹' (p' ⁻¹' {b}) ⊆ p ⁻¹' {b} := by rw [← preimage_comp, h]
  have h' := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap (X := TopCat.of E) (Y := TopCat.of E') (B := (p ⁻¹' {b})ᶜ)
      (B' := (p' ⁻¹' {b})ᶜ) (TopCat.ofHom σ) ((mapsTo_preimage _ _).mono_left
        (compl_subset_compl.2 hσ))) R k
  simp only [TopPair.ofSubsetMap_fst] at h'
  rw [localHomologyMap_def]
  exact h'

/-- For the identity of `M`, the localization at the fibre over `b` is the quotient map to
`Hₖ(M, M ∖ M)` followed by restriction to the local homology `Hₖ(M, M ∖ {b})` at `b`. -/
theorem fiberLocalization_id [TopologicalSpace M] (b : M) (k : ℕ) :
    fiberLocalization R (id : M → M) b k =
      (TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ R k ≫
        localHomologyRestriction R (subset_univ {b}) k := by
  have hB : MapsTo (𝟙 (TopCat.of M)) ((univ : Set (TopCat.of M))ᶜ) ({b}ᶜ : Set (TopCat.of M)) :=
    fun x hx ↦ compl_subset_compl.2 (subset_univ {b}) hx
  have h := TopPair.singularHomologyπ_naturality (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hB) R k
  rw [TopPair.ofSubsetMap_fst] at h
  rw [localHomologyRestriction_def, ← h]
  erw [TopCat.toSSet.map_id, SSet.homologyMap_id, Category.id_comp]

end Localization

section LivesOver

variable {Λ : Type*} [Ring Λ] (R : ModuleCat.{w} Λ)
  {E E' M : Type w} [TopologicalSpace E] [TopologicalSpace E']

/-- A class `α ∈ Hₖ(E)` **lives over the fundamental class** of `M` at `b`, for a map
`p : E → M`, if its localization `Hₖ(E) → Hₖ(E, E ∖ p⁻¹(b))` at the fibre over `b` is nonzero.

For a fibration over an `n`-manifold the target is identified with `Hₖ₋ₙ(p⁻¹(b))`, and the
localization with the shriek map of the inclusion of `b`
(Barraud–Damian–Humilière–Oancea, Lemma 2.9), so this is their Definition 2.3 for the local
system of chains on the fibre (their Example 2.4). For the identity of a compact connected
oriented `n`-manifold and integer coefficients, the classes of `Hₙ(M; ℤ)` living over the
fundamental class are the nonzero multiples of the fundamental class
(`TauCeti.HomologicalOrientation.livesOverFundamentalClass_id_iff`). -/
def LivesOverFundamentalClass (p : E → M) (b : M) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)) : Prop :=
  (fiberLocalization R p b k).hom α ≠ 0

theorem livesOverFundamentalClass_iff (p : E → M) (b : M) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)) :
    LivesOverFundamentalClass R p b α ↔ (fiberLocalization R p b k).hom α ≠ 0 :=
  Iff.rfl

/-- The zero class does not live over the fundamental class. -/
@[simp]
theorem not_livesOverFundamentalClass_zero (p : E → M) (b : M) (k : ℕ) :
    ¬LivesOverFundamentalClass R p b
      (0 : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)) :=
  fun h ↦ h (map_zero _)

/-- A class lives over the fundamental class at `b` if one of its scalar multiples does. -/
theorem LivesOverFundamentalClass.of_smul {p : E → M} {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)} (c : Λ)
    (h : LivesOverFundamentalClass R p b (c • α)) : LivesOverFundamentalClass R p b α :=
  fun h' ↦ h (by rw [map_smul, h', smul_zero])

/-- **Classes living over the fundamental class pull back along maps over the base.** If
`σ : E → E'` satisfies `p' ∘ σ = p` and `σ_* α` lives over the fundamental class at `b` for `p'`,
then `α` lives over the fundamental class at `b` for `p`. -/
theorem LivesOverFundamentalClass.of_homologyMap (σ : C(E, E')) {p : E → M} {p' : E' → M}
    (h : p' ∘ σ = p) {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (hα : LivesOverFundamentalClass R p' b
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) R k).hom α)) :
    LivesOverFundamentalClass R p b α := by
  intro h'
  apply hα
  rw [← ModuleCat.comp_apply, homologyMap_comp_fiberLocalization R σ h b k,
    ModuleCat.comp_apply, h', map_zero]

/-- If the image `p_* α` of a class of `E` in the homology of `M` lives over the fundamental class
at `b`, then `α` lives over the fundamental class at `b` for `p`. -/
theorem LivesOverFundamentalClass.of_homologyMap_proj [TopologicalSpace M] (p : C(E, M))
    {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (hα : LivesOverFundamentalClass R id b
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α)) :
    LivesOverFundamentalClass R p b α :=
  hα.of_homologyMap R p (Function.id_comp _)

end LivesOver

section Cross

section General

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
  [HasCoproducts.{w} A]
  [∀ (T : A) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : A) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  (R S : A) {E Y M : Type w} [TopologicalSpace E] [TopologicalSpace Y]

/-- **Localization of a cross product at the fibre.** For `p : E → M` and a space `Y`, the fibre
of `p ∘ fst : E × Y → M` over `b` is `p⁻¹(b) × Y`. Localizing the cross product of
`α ∈ Hᵢ(E; R)` and `β ∈ Hⱼ(Y; S)` at this fibre gives the relative cross product of the
localization of `α` at `p⁻¹(b)` with `β`. -/
@[reassoc]
theorem singularHomologyCross_comp_fiberLocalization (p : E → M) (b : M) (i j n : ℕ)
    (h : i + j = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).homology i))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      (((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E))).singularChainComplex R).homology i))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopCat.toSSet.obj (TopCat.of Y)).chainComplex S).cycles j))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight
      (((TopCat.toSSet.obj (TopCat.of Y)).chainComplex S).X ((ComplexShape.down ℕ).prev j)))] :
    TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h ≫
        fiberLocalization (R ⊗ S) (p ∘ Prod.fst) b n =
      (fiberLocalization R p b i ▷ (TopCat.toSSet.obj (TopCat.of Y)).homology S j) ≫
        TopCat.singularHomologyCrossRel (TopCat.of E) (TopCat.of Y) (p ⁻¹' {b})ᶜ R S i j n h :=
  TopCat.singularHomologyCross_comp_singularHomologyπ (TopCat.of E) (TopCat.of Y) (p ⁻¹' {b})ᶜ R S
    i j n h

end General

variable {k : Type w} [CommRing k] (R S : ModuleCat.{w} k) {E Y M : Type w} [TopologicalSpace E]
  [TopologicalSpace Y]

/-- The localization of `α × β` at the fibre of `p ∘ fst : E × Y → M` over `b` is the relative
cross product of the localization of `α` at the fibre of `p` with `β`. -/
theorem fiberLocalization_singularHomologyCross_tmul (p : E → M) (b : M) {i j n : ℕ}
    (h : i + j = n) (α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} k))
    (β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)) :
    (fiberLocalization (R ⊗ S) (p ∘ Prod.fst) b n).hom
        ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β)) =
      (TopCat.singularHomologyCrossRel (TopCat.of E) (TopCat.of Y) (p ⁻¹' {b})ᶜ R S i j n h).hom
        ((fiberLocalization R p b i).hom α ⊗ₜ β) :=
  ConcreteCategory.congr_hom (singularHomologyCross_comp_fiberLocalization R S p b i j n h) (α ⊗ₜ β)

/-- If the cross product `α × β ∈ Hₙ(E × Y; R ⊗ S)` lives over the fundamental class at `b` for
`p ∘ fst : E × Y → M`, then `α` lives over the fundamental class at `b` for `p`. -/
theorem LivesOverFundamentalClass.of_singularHomologyCross {p : E → M} {b : M} {i j n : ℕ}
    (h : i + j = n) {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} k)}
    {β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)}
    (hαβ : LivesOverFundamentalClass (R ⊗ S) (p ∘ Prod.fst) b
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β))) :
    LivesOverFundamentalClass R p b α := by
  intro hα
  refine hαβ ((fiberLocalization_singularHomologyCross_tmul R S p b h α β).trans ?_)
  rw [hα]
  -- The tensor product of `ModuleCat` is not syntactically `TensorProduct`, so `simp` does not
  -- apply `TensorProduct.zero_tmul` here.
  exact (congrArg _ (TensorProduct.zero_tmul _ _)).trans (map_zero _)

/-- If the cross product `α × β ∈ Hₙ(E × Y; R ⊗ S)` lives over the fundamental class at `b` for
`p ∘ fst : E × Y → M`, then `β ≠ 0`. -/
theorem LivesOverFundamentalClass.right_ne_zero_of_singularHomologyCross {p : E → M} {b : M}
    {i j n : ℕ} (h : i + j = n)
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} k)}
    {β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)}
    (hαβ : LivesOverFundamentalClass (R ⊗ S) (p ∘ Prod.fst) b
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β))) :
    β ≠ 0 := by
  rintro rfl
  exact hαβ ((fiberLocalization_singularHomologyCross_tmul R S p b h α 0).trans <|
    (congrArg _ (TensorProduct.tmul_zero _ _)).trans (map_zero _))

/-- **Cross products living over the fundamental class.** The cross product
`α × β ∈ Hₙ(E × Y; R ⊗ S)` lives over the fundamental class at `b` for `p ∘ fst : E × Y → M` if
and only if `α` lives over the fundamental class at `b` for `p` and `β ≠ 0`, provided the relative
cross product is injective and the two homology modules are projective over a ring without zero
divisors. This holds for all coefficient modules over a field, by the relative Künneth theorem
(`TopCat.mono_singularHomologyCrossRel`). -/
@[simp]
theorem livesOverFundamentalClass_singularHomologyCross_iff [NoZeroDivisors k] {p : E → M} {b : M}
    {i j n : ℕ} (h : i + j = n)
    [Module.Projective k (localHomology R (p ⁻¹' {b}) i : ModuleCat.{w} k)]
    [Module.Projective k
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} k) j).obj S).obj (TopCat.of Y) :
        ModuleCat.{w} k)]
    [Mono (TopCat.singularHomologyCrossRel (TopCat.of E) (TopCat.of Y) (p ⁻¹' {b})ᶜ R S i j n h)]
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} k)}
    {β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)} :
    LivesOverFundamentalClass (R ⊗ S) (p ∘ Prod.fst) b
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β)) ↔
      LivesOverFundamentalClass R p b α ∧ β ≠ 0 := by
  refine ⟨fun hαβ ↦ ⟨hαβ.of_singularHomologyCross R S h,
    hαβ.right_ne_zero_of_singularHomologyCross R S h⟩, fun ⟨hα, hβ⟩ ↦ ?_⟩
  have hinj := (ModuleCat.mono_iff_injective
    (TopCat.singularHomologyCrossRel (TopCat.of E) (TopCat.of Y) (p ⁻¹' {b})ᶜ R S i j n h)).1
      inferInstance
  exact fun h₀ ↦ (map_ne_zero_iff _ hinj).2 (tmul_ne_zero hα hβ)
    ((fiberLocalization_singularHomologyCross_tmul R S p b h α β).symm.trans h₀)

/-- Over a field, the cross product `α × β ∈ Hₙ(E × Y; R ⊗ S)` lives over the fundamental class
at `b` for `p ∘ fst : E × Y → M` if and only if `α` lives over the fundamental class at `b` for
`p` and `β ≠ 0`. -/
theorem livesOverFundamentalClass_singularHomologyCross_iff_of_field {K : Type w} [Field K]
    (R S : ModuleCat.{w} K) {p : E → M} {b : M} {i j n : ℕ} (h : i + j = n)
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} K)}
    {β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} K)} :
    LivesOverFundamentalClass (R ⊗ S) (p ∘ Prod.fst) b
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β)) ↔
      LivesOverFundamentalClass R p b α ∧ β ≠ 0 :=
  -- Over a field all chain modules are semisimple, so their cycles split off; the instance is
  -- passed explicitly since synthesizing it through the singular chain complexes times out.
  have := @TopCat.mono_singularHomologyCrossRel K _ (TopCat.of E) (TopCat.of Y) (p ⁻¹' {b})ᶜ R S
    (fun _ ↦ HomologicalComplex.isSplitMono_iCycles_of_isSemisimpleModule _ _)
    (fun _ ↦ HomologicalComplex.isSplitMono_iCycles_of_isSemisimpleModule _ _) i j n h
  livesOverFundamentalClass_singularHomologyCross_iff R S h

end Cross

section ProdMap

/-! ### Products of two maps -/

section Restriction

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {E E' M M' : Type w} [TopologicalSpace E] [TopologicalSpace E']

/-- **Localizing at a smaller fibre.** If the fibre of `p'` over `b'` lies in the fibre of `p`
over `b`, the localization at the fibre of `p'` is the localization at the fibre of `p` followed by
the restriction of local homology. -/
@[reassoc]
theorem fiberLocalization_comp_localHomologyRestriction {p : E → M} {p' : E → M'} {b : M}
    {b' : M'} (h : p' ⁻¹' {b'} ⊆ p ⁻¹' {b}) (k : ℕ) :
    fiberLocalization R p b k ≫ localHomologyRestriction R h k = fiberLocalization R p' b' k := by
  rw [localHomologyRestriction_def]
  exact TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id R _ k

/-- A map `σ : E' → E` missing the fibre of `p` over `b` is killed by the localization at that
fibre: `σ_*` followed by `Hₖ(E) → Hₖ(E, E ∖ p⁻¹(b))` is zero. -/
@[reassoc]
theorem homologyMap_comp_fiberLocalization_eq_zero (σ : C(E', E)) {p : E → M} {b : M}
    (hσ : ∀ x, p (σ x) ≠ b) (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) R k ≫ fiberLocalization R p b k = 0 := by
  -- By naturality the composite is the localization of `E'` at the empty fibre of `p ∘ σ`,
  -- whose target `Hₖ(E', E')` vanishes.
  rw [homologyMap_comp_fiberLocalization R σ rfl b k]
  have hz : IsZero (localHomology R ((p ∘ σ) ⁻¹' {b}) k) :=
    TopPair.isZero_singularHomology_of_surjective_map _ R
      (fun x ↦ ⟨(⟨x, fun h' ↦ hσ x (Set.mem_singleton_iff.1 (Set.mem_preimage.1 h'))⟩ :
        ↥(((p ∘ σ) ⁻¹' {b})ᶜ : Set E')), rfl⟩) k
  rw [hz.eq_of_tgt (fiberLocalization R (p ∘ σ) b k) 0, zero_comp]

end Restriction

variable {E Y M N : Type w} [TopologicalSpace E] [TopologicalSpace Y]

section CommRing

variable {k : Type w} [CommRing k] (R S : ModuleCat.{w} k)

/-- If the cross product `α × β ∈ Hₙ(E × Y; R ⊗ S)` lives over the fundamental class at `(b, c)`
for `p × q : E × Y → M × N`, then `α` lives over the fundamental class at `b` for `p`. -/
theorem LivesOverFundamentalClass.left_of_singularHomologyCross_prodMap {p : E → M} {q : Y → N}
    {b : M} {c : N} {i j n : ℕ} (h : i + j = n)
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} k)}
    {β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)}
    (hαβ : LivesOverFundamentalClass (R ⊗ S) (Prod.map p q) (b, c)
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β))) :
    LivesOverFundamentalClass R p b α := by
  -- The fibre `p⁻¹(b) × q⁻¹(c)` lies in the fibre `p⁻¹(b) × Y` of `p ∘ fst`.
  have hsub : Prod.map p q ⁻¹' {(b, c)} ⊆ (p ∘ Prod.fst) ⁻¹' {b} := fun x hx ↦ by
    simp_all [Prod.ext_iff]
  refine LivesOverFundamentalClass.of_singularHomologyCross (p := p) (b := b) (β := β) R S h
    fun h₀ ↦ hαβ ?_
  rw [← fiberLocalization_comp_localHomologyRestriction (R ⊗ S) hsub]
  exact (congrArg (localHomologyRestriction (R ⊗ S) hsub n).hom h₀).trans (map_zero _)

/-- If the cross product `α × β ∈ Hₙ(E × Y; R ⊗ S)` lives over the fundamental class at `(b, c)`
for `p × q : E × Y → M × N`, then `β` lives over the fundamental class at `c` for `q`. -/
theorem LivesOverFundamentalClass.right_of_singularHomologyCross_prodMap {p : E → M}
    {q : Y → N} {b : M} {c : N} {i j n : ℕ} (h : i + j = n)
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} k)}
    {β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)}
    (hαβ : LivesOverFundamentalClass (R ⊗ S) (Prod.map p q) (b, c)
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β))) :
    LivesOverFundamentalClass S q c β := by
  intro hβ
  -- By the exact sequence of the pair `(Y, Y ∖ q⁻¹(c))`, `β` comes from `Y ∖ q⁻¹(c)`, so `α × β`
  -- comes from `E × (Y ∖ q⁻¹(c))`, which misses the fibre over `(b, c)`.
  let P := TopPair.ofSubset ((q ⁻¹' {c})ᶜ : Set (TopCat.of Y))
  obtain ⟨β', rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (P.singularHomology_exact_space S j) β hβ
  apply hαβ
  have key : (𝟙 _ ⊗ₘ ((AlgebraicTopology.singularHomologyFunctor _ j).obj S).map P.map) ≫
      TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h ≫
        fiberLocalization (R ⊗ S) (Prod.map p q) (b, c) n = 0 := by
    have hnat := TopCat.singularHomologyCross_naturality_assoc (𝟙 (TopCat.of E)) P.map R S i j n
      h (fiberLocalization (R ⊗ S) (Prod.map p q) (b, c) n)
    rw [CategoryTheory.Functor.map_id] at hnat
    refine hnat.trans ?_
    exact (_ ≫= homologyMap_comp_fiberLocalization_eq_zero (R ⊗ S)
      (ContinuousMap.prodMap (ContinuousMap.id E)
        (⟨Subtype.val, continuous_subtype_val⟩ : C(((q ⁻¹' {c})ᶜ : Set Y), Y)))
      (p := Prod.map p q) (b := (b, c)) (fun x hx ↦ x.2.2 (congrArg Prod.snd hx :)) n).trans
      comp_zero
  have h₁ := congrArg (fun φ ↦ φ.hom (α ⊗ₜ β')) key
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at h₁
  exact h₁

end CommRing

section Field

variable {K : Type w} [Field K] (R S : ModuleCat.{w} K)

/-- **Cross products living over the fundamental class of a product.** With coefficients in a
field, if `α ∈ Hᵢ(E; R)` lives over the fundamental class at `b` for `p` and `β ∈ Hⱼ(Y; S)` lives
over the fundamental class at `c` for `q`, and the two fibres are closed, then the cross product
`α × β` lives over the fundamental class at `(b, c)` for `p × q : E × Y → M × N`. -/
theorem LivesOverFundamentalClass.singularHomologyCross_prodMap {p : E → M} {q : Y → N} {b : M}
    {c : N} (hp : IsClosed (p ⁻¹' {b})) (hq : IsClosed (q ⁻¹' {c})) {i j n : ℕ} (h : i + j = n)
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} K)}
    {β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} K)}
    (hα : LivesOverFundamentalClass R p b α) (hβ : LivesOverFundamentalClass S q c β) :
    LivesOverFundamentalClass (R ⊗ S) (Prod.map p q) (b, c)
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β)) := by
  intro h₀
  -- Write `A = E ∖ p⁻¹(b)` and `B = Y ∖ q⁻¹(c)`. In `E × Y` the complement `A × Y` of the fibre
  -- of `p ∘ fst` lies in the complement `Z = A × Y ∪ E × B` of the fibre of `p × q`.
  let A : Set (TopCat.of E) := (p ⁻¹' {b})ᶜ
  let B : Set (TopCat.of Y) := (q ⁻¹' {c})ᶜ
  let Z : Set (TopCat.of E ⊗ TopCat.of Y) := (Prod.map p q ⁻¹' {(b, c)})ᶜ
  have hAZ : CartesianMonoidalCategory.fst (TopCat.of E) (TopCat.of Y) ⁻¹' A ⊆ Z :=
    fun x hx hx' ↦ hx (congrArg Prod.fst hx' :)
  have hBZ : CartesianMonoidalCategory.snd (TopCat.of E) (TopCat.of Y) ⁻¹' B ⊆ Z :=
    fun x hx hx' ↦ hx (congrArg Prod.snd hx' :)
  have hZ : Z ⊆ CartesianMonoidalCategory.fst (TopCat.of E) (TopCat.of Y) ⁻¹' A ∪
      CartesianMonoidalCategory.snd (TopCat.of E) (TopCat.of Y) ⁻¹' B := fun x hx ↦ by
    by_cases hb : p x.1 = b
    · exact Or.inr fun hc ↦ hx (Prod.ext hb hc)
    · exact Or.inl hb
  -- `h₀` says that `α × β` vanishes in `Hₙ(E × Y, Z)`, so its image `(loc α) × β` in
  -- `Hₙ(E × Y, A × Y)` comes from `Hₙ(E × B, A × B)`; the relative Künneth theorem rules this out.
  obtain ⟨y, hy⟩ := TopCat.exists_singularHomologyMap_ofSubsetMap_tensorHom_eq (R ⊗ S)
    hp.isOpen_compl hq.isOpen_compl hAZ hBZ hZ
    ((congrArg (fun φ ↦ φ.hom
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β)))
      (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id (R ⊗ S)
        (X := TopCat.of E ⊗ TopCat.of Y) (S := Z) (fun _ hx ↦ hAZ hx) n)).trans h₀)
  exact TopCat.singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel_of_field _ _
    A B R S h hα hβ y (hy.trans (congrArg (fun φ ↦ φ.hom (α ⊗ₜ β))
      (TopCat.singularHomologyCross_comp_singularHomologyπ (TopCat.of E) (TopCat.of Y) A R S i j n
        h)))

/-- **Classes living over the fundamental class of a product.** With coefficients in a field and
closed fibres, the cross product `α × β` lives over the fundamental class at `(b, c)` for
`p × q : E × Y → M × N` if and only if `α` lives over the fundamental class at `b` for `p` and `β`
lives over the fundamental class at `c` for `q`. -/
theorem livesOverFundamentalClass_prodMap_singularHomologyCross_iff_of_field {p : E → M}
    {q : Y → N} {b : M} {c : N} (hp : IsClosed (p ⁻¹' {b})) (hq : IsClosed (q ⁻¹' {c}))
    {i j n : ℕ} (h : i + j = n)
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R i : ModuleCat.{w} K)}
    {β : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} K)} :
    LivesOverFundamentalClass (R ⊗ S) (Prod.map p q) (b, c)
      ((TopCat.singularHomologyCross (TopCat.of E) (TopCat.of Y) R S i j n h).hom (α ⊗ₜ β)) ↔
      LivesOverFundamentalClass R p b α ∧ LivesOverFundamentalClass S q c β :=
  ⟨fun hαβ ↦ ⟨hαβ.left_of_singularHomologyCross_prodMap R S h,
    hαβ.right_of_singularHomologyCross_prodMap R S h⟩,
    fun ⟨hα, hβ⟩ ↦ hα.singularHomologyCross_prodMap R S hp hq h hβ⟩

end Field

end ProdMap

namespace HomologicalOrientation

open AlgebraicTopology

variable {M E V : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [ChartedSpace V M]
  [TopologicalSpace E] {n : ℕ} (o : HomologicalOrientation M V n) (hn : Module.finrank ℝ V = n)

include hn in
/-- **Multiples of the fundamental class.** For the identity of a compact oriented manifold, the
multiple `d • [M]` of the fundamental class lives over the fundamental class at any point exactly
when `d ≠ 0`: its localization at `b` is `d` times the local orientation at `b`, which has
infinite order. -/
@[simp]
theorem livesOverFundamentalClass_id_zsmul_fundamentalClass_iff (b : M) (d : ℤ) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) id b (d • o.fundamentalClass hn) ↔
      d ≠ 0 := by
  rw [livesOverFundamentalClass_iff, fiberLocalization_id, map_zsmul]
  erw [ModuleCat.comp_apply]
  erw [← singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_fundamentalClass]
  rw [not_iff_not]
  exact ⟨fun h ↦ o.zsmul_left_injective hn b (h.trans (zero_smul ℤ _).symm),
    fun h ↦ h ▸ zero_smul ℤ _⟩

include hn in
/-- The fundamental class of a compact oriented manifold lives over itself at every point. -/
@[simp]
theorem livesOverFundamentalClass_id_fundamentalClass (b : M) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) id b (o.fundamentalClass hn) := by
  simpa using (o.livesOverFundamentalClass_id_zsmul_fundamentalClass_iff hn b 1).2 one_ne_zero

include o hn in
/-- **The trivial fibration** (the remark after Barraud–Damian–Humilière–Oancea, Definition 2.3).
On a compact connected oriented manifold, a class of `Hₙ(M; ℤ)` lives over the fundamental class
at a point exactly when it is nonzero, that is, when it is a nonzero multiple of the fundamental
class. -/
theorem livesOverFundamentalClass_id_iff [ConnectedSpace M] (b : M)
    (γ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) id b γ ↔ γ ≠ 0 := by
  obtain ⟨d, rfl⟩ := o.exists_eq_zsmul_fundamentalClass hn γ
  rw [o.livesOverFundamentalClass_id_zsmul_fundamentalClass_iff hn b d, not_iff_not]
  constructor
  · rintro rfl
    exact zero_smul ℤ _
  · intro h
    exact (o.fundamentalClassEquiv hn).injective ((o.fundamentalClassEquiv_apply hn d).trans
      (h.trans (by rw [fundamentalClassEquiv_apply, zero_smul])))

include hn in
/-- **Classes of nonzero degree live over the fundamental class.** Let `p : E → M` be a map to a
compact oriented `n`-manifold and let `α ∈ Hₙ(E; ℤ)` satisfy `p_* α = d • [M]` with `d ≠ 0`.
Then `α` lives over the fundamental class of `M` at every point. -/
theorem livesOverFundamentalClass_of_homologyMap_eq_zsmul (p : C(E, M))
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)} {d : ℤ}
    (hα : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom α = d • o.fundamentalClass hn) (hd : d ≠ 0)
    (b : M) : LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) p b α :=
  LivesOverFundamentalClass.of_homologyMap_proj _ p <| by
    rw [hα]
    exact (o.livesOverFundamentalClass_id_zsmul_fundamentalClass_iff hn b d).2 hd

variable {S W : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [ChartedSpace W S]
  (o' : HomologicalOrientation S W n) (hn' : Module.finrank ℝ W = n)

include hn hn' in
/-- **The image of a manifold of nonzero degree over the base.** Let `p : E → M` be a map to a
compact oriented `n`-manifold and `φ : S → E` a map from a compact oriented `n`-manifold with
`(p ∘ φ)_*[S] = d • [M]` and `d ≠ 0`. Then `φ_*[S]` lives over the fundamental class of `M` at
every point. This is the degree hypothesis of Barraud–Damian–Humilière–Oancea, Theorems 5.10 and
5.14, stated homologically. -/
theorem livesOverFundamentalClass_mapFundamentalClass (p : C(E, M)) (φ : C(S, E)) {d : ℤ}
    (hφ : o'.mapFundamentalClass hn' (p.comp φ) = d • o.fundamentalClass hn) (hd : d ≠ 0)
    (b : M) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) p b
      (o'.mapFundamentalClass hn' φ) := by
  refine o.livesOverFundamentalClass_of_homologyMap_eq_zsmul hn p ?_ hd b
  rw [← hφ, mapFundamentalClass_comp]
  -- Both sides are the image of `φ_*[S]` under `p`; the source is read as `SSet.homology`.
  rfl

include hn in
/-- **Sections live over the fundamental class.** If `s : M → E` is a section of `p : E → M`
over a compact oriented manifold `M`, then the class `s_*[M]` lives over the
fundamental class of `M` at every point. -/
theorem livesOverFundamentalClass_mapFundamentalClass_of_section (p : C(E, M)) (s : C(M, E))
    (hs : p.comp s = ContinuousMap.id M) (b : M) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) p b
      (o.mapFundamentalClass hn s) :=
  o.livesOverFundamentalClass_mapFundamentalClass hn o hn p s
    (by rw [hs, mapFundamentalClass_id, one_smul]) one_ne_zero b

end HomologicalOrientation

end TauCeti
