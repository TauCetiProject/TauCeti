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
  (`TauCeti.LivesOverFundamentalClass.of_homologyMap_proj`). Conversely, if `σ` has a left inverse
  `τ` over `M`, for instance if `σ` is a homeomorphism over `M`, then `σ_* α` lives over the
  fundamental class exactly when `α` does
  (`TauCeti.livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id`). Localization also commutes
  with morphisms of coefficients (`TauCeti.fiberLocalization_coefficient_naturality`), so living
  over the fundamental class is unchanged by an isomorphism of coefficients
  (`TauCeti.livesOverFundamentalClass_homologyMap_coefficient_iff`).
* **Products with a second factor.** For a space `Y`, the map `p ∘ fst : E × Y → M` has fibre
  `p⁻¹(b) × Y`, and localizing a cross product `α × β` at it is the relative cross product of the
  localization of `α` with `β` (`TauCeti.fiberLocalization_singularHomologyCross_tmul`); the
  relative cross product is natural for maps of local homology in the first factor
  (`TauCeti.singularHomologyCrossRel_localHomologyMap_tmul`). So if `α × β` lives over the
  fundamental class, so does `α`
  (`TauCeti.LivesOverFundamentalClass.of_singularHomologyCross`), and `β ≠ 0`
  (`TauCeti.LivesOverFundamentalClass.right_ne_zero_of_singularHomologyCross`). When the relative
  cross product is injective, for instance over a field by the relative Künneth theorem, and the
  homology is projective over a ring without zero divisors, the converse holds
  (`TauCeti.livesOverFundamentalClass_singularHomologyCross_iff`,
  `TauCeti.livesOverFundamentalClass_singularHomologyCross_iff_of_field`). Over the integers,
  without projectivity, the cross product `[M] × α` of the fundamental class of a compact
  oriented `n`-manifold `M` with a class `α` of a space `Y` lives over the fundamental class for
  the projection `M × Y → M` exactly when `α ≠ 0`, since the local orientation generates
  `Hₙ(M, M ∖ {b}; ℤ)` and the integral relative cross product is injective
  (`HomologicalOrientation.livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff`
  in namespace `TauCeti`).
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
  Lemma 2.9, Proposition 2.12) and §§5–6.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, local homology and fundamental classes.
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
        localHomologyMap R σ (by rw [← preimage_comp, h]) k :=
  homologyMap_comp_singularHomologyπ_ofSubset R σ _ k

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

/-- **Naturality of the localization at the fibre in the coefficients**: a morphism `φ : R ⟶ R'`
of coefficients commutes with the localization at the fibre of `p` over `b`. -/
@[reassoc]
theorem fiberLocalization_coefficient_naturality {R R' : A} (φ : R ⟶ R') (p : E → M) (b : M)
    (k : ℕ) :
    HomologicalComplex.homologyMap (((SSet.chainComplexFunctor A).map φ).app
        (TopCat.toSSet.obj (TopCat.of E))) k ≫ fiberLocalization R' p b k =
      fiberLocalization R p b k ≫ HomologicalComplex.homologyMap
        (((SSetPair.chainComplexFunctor A).map φ).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E))))) k :=
  SSetPair.homologyπ_coefficient_naturality
    (TopPair.toSSetPair.obj (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E)))) φ k

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

/-- Living over the fundamental class only depends on the fibre: for maps `p : E → M` and
`p' : E → M'` with `p⁻¹(b) = p'⁻¹(b')`, a class lives over the fundamental class at `b` for `p`
exactly when it does at `b'` for `p'`. -/
theorem livesOverFundamentalClass_congr {M' : Type w} {p : E → M} {p' : E → M'} {b : M} {b' : M'}
    (h : p ⁻¹' {b} = p' ⁻¹' {b'}) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)) :
    LivesOverFundamentalClass R p b α ↔ LivesOverFundamentalClass R p' b' α := by
  rw [livesOverFundamentalClass_iff, livesOverFundamentalClass_iff, fiberLocalization,
    fiberLocalization, h]

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

/-- **Classes living over the fundamental class push forward along maps over the base with a
left inverse over the base.** If `σ : E → E'` and `τ : E' → E` satisfy `τ ∘ σ = id`,
`p' ∘ σ = p` and `p ∘ τ = p'`, for instance a homeomorphism over `M` and its inverse, then
`σ_* α` lives over the fundamental class at `b` for `p'` exactly when `α` does for `p`. -/
theorem livesOverFundamentalClass_homologyMap_iff_of_comp_eq_id (σ : C(E, E')) (τ : C(E', E))
    (hτ : τ.comp σ = ContinuousMap.id E) {p : E → M} {p' : E' → M} (h : p' ∘ σ = p)
    (h' : p ∘ τ = p') {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)} :
    LivesOverFundamentalClass R p' b
        ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) R k).hom α) ↔
      LivesOverFundamentalClass R p b α := by
  refine ⟨fun hα ↦ hα.of_homologyMap R σ h, fun hα ↦ ?_⟩
  -- `τ_* σ_* α = α`, so `α` is the image of `σ_* α` under a map over `M`.
  have key : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom τ)) R k).hom
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) R k).hom α) = α := by
    simp [← ModuleCat.comp_apply, ← SSet.homologyMap_comp, ← Functor.map_comp,
      ← TopCat.ofHom_comp, hτ]
  exact LivesOverFundamentalClass.of_homologyMap R τ h' (by rwa [key])

/-- **Living over the fundamental class does not depend on the coefficients up to
isomorphism.** For an isomorphism `φ : R ≅ R'` of coefficient modules, the image of
`α ∈ Hₖ(E; R)` in `Hₖ(E; R')` lives over the fundamental class at `b` exactly when `α` does. -/
theorem livesOverFundamentalClass_homologyMap_coefficient_iff {R' : ModuleCat.{w} Λ}
    (φ : R ≅ R') {p : E → M} {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)} :
    LivesOverFundamentalClass R' p b ((HomologicalComplex.homologyMap
        (((SSet.chainComplexFunctor (ModuleCat.{w} Λ)).map φ.hom).app
          (TopCat.toSSet.obj (TopCat.of E))) k).hom α) ↔
      LivesOverFundamentalClass R p b α := by
  -- The coefficient map on relative homology is an isomorphism, hence injective.
  have hinj := (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap
    (((SSetPair.chainComplexFunctor (ModuleCat.{w} Λ)).map φ.hom).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E))))) k)).1
    inferInstance
  have hc := ConcreteCategory.congr_hom (fiberLocalization_coefficient_naturality φ.hom p b k) α
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hc
  rw [livesOverFundamentalClass_iff, livesOverFundamentalClass_iff, hc]
  exact (map_ne_zero_iff _ hinj)

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

/-- Naturality of the relative cross product in the pair, read in local homology: for a map
`f : X → X'` with `f⁻¹(T) ⊆ S'`, the relative cross product of `f_* a` with `b` is the image under
`f × id` of the relative cross product of `a` with `b`. -/
theorem singularHomologyCrossRel_localHomologyMap_tmul {X X' : Type w} [TopologicalSpace X]
    [TopologicalSpace X'] (f : C(X, X')) {S' : Set X} {T : Set X'} (h : f ⁻¹' T ⊆ S') {i j n : ℕ}
    (hn : i + j = n) (a : localHomology (A := ModuleCat.{w} k) R S' i)
    (b : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)) :
    (TopCat.singularHomologyCrossRel (TopCat.of X') (TopCat.of Y) Tᶜ R S i j n hn).hom
        ((localHomologyMap R f h i).hom a ⊗ₜ b) =
      (localHomologyMap (R ⊗ S) (f.prodMap (ContinuousMap.id Y)) (S := Prod.fst ⁻¹' S')
        (T := Prod.fst ⁻¹' T) (fun _ hz ↦ h hz) n).hom
        ((TopCat.singularHomologyCrossRel (TopCat.of X) (TopCat.of Y) S'ᶜ R S i j n hn).hom
          (a ⊗ₜ b)) := by
  have h' : f.prodMap (ContinuousMap.id Y) ⁻¹' (Prod.fst ⁻¹' T) ⊆ Prod.fst ⁻¹' S' :=
    fun _ hz ↦ h hz
  have hf : Set.MapsTo (TopCat.ofHom f) S'ᶜ Tᶜ := fun _ hx hfx ↦ hx (h hfx)
  -- Naturality for `f` and the identity of `Y`, with the product map read as `f × id`.
  have hnat := TopCat.singularHomologyCrossRel_naturality (TopCat.of X) (TopCat.of Y) S'ᶜ R S i j
    n hn (B' := Tᶜ) (TopCat.ofHom f) hf (𝟙 (TopCat.of Y))
  rw [CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id] at hnat
  have hfg : TopPair.singularHomologyMap (TopPair.ofSubsetMap (TopCat.ofHom f ⊗ₘ 𝟙 (TopCat.of Y))
      (TopCat.mapsTo_tensorHom_preimage_fst _ _ hf)) (R ⊗ S) n =
      localHomologyMap (R ⊗ S) (f.prodMap (ContinuousMap.id Y)) h' n := by
    -- The map underlying `f ⊗ₘ 𝟙` is the product map (`TopCat.tensor_apply`).
    have hfY : TopCat.ofHom f ⊗ₘ 𝟙 (TopCat.of Y) = TopCat.ofHom (f.prodMap (ContinuousMap.id Y)) :=
      TopCat.hom_ext (ContinuousMap.ext fun z ↦ TopCat.tensor_apply _ _ z)
    have h₁ : TopPair.ofSubsetMap (TopCat.ofHom f ⊗ₘ 𝟙 (TopCat.of Y))
        (TopCat.mapsTo_tensorHom_preimage_fst _ _ hf) =
        TopPair.ofSubsetMap (X := TopCat.of (X × Y)) (Y := TopCat.of (X' × Y))
          (B := (Prod.fst ⁻¹' S')ᶜ) (B' := (Prod.fst ⁻¹' T)ᶜ)
          (TopCat.ofHom (f.prodMap (ContinuousMap.id Y)))
          ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h')) :=
      TopPair.hom_ext_of_fst _
        (Eq.trans (TopPair.ofSubsetMap_fst _ _) (hfY.trans (TopPair.ofSubsetMap_fst _ _).symm))
    exact (congrArg (fun φ ↦ TopPair.singularHomologyMap φ _ n) h₁).trans
      (localHomologyMap_def _ (f.prodMap (ContinuousMap.id Y)) h' n).symm
  rw [hfg] at hnat
  exact (congrArg (fun x ↦ (TopCat.singularHomologyCrossRel (TopCat.of X') (TopCat.of Y) Tᶜ
    R S i j n hn).hom (x ⊗ₜ b)) (ConcreteCategory.congr_hom (localHomologyMap_def R f h i) a)).trans
    (ConcreteCategory.congr_hom hnat (a ⊗ₜ b))

/-- Naturality of the relative cross product in the second factor, read in local homology: for a
map `g : Y → Y'`, the relative cross product of `a` with `g_* b` is the image under `id × g` of the
relative cross product of `a` with `b`. -/
theorem singularHomologyCrossRel_tmul_homologyMap {X Y Y' : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Y'] (g : C(Y, Y')) {T : Set X} {i j n : ℕ}
    (hn : i + j = n) (a : localHomology (A := ModuleCat.{w} k) R T i)
    (b : ((TopCat.toSSet.obj (TopCat.of Y)).homology S j : ModuleCat.{w} k)) :
    (TopCat.singularHomologyCrossRel (TopCat.of X) (TopCat.of Y') Tᶜ R S i j n hn).hom
        (a ⊗ₜ (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom g)) S j).hom b) =
      (localHomologyMap (R ⊗ S) ((ContinuousMap.id X).prodMap g) (S := Prod.fst ⁻¹' T)
        (T := Prod.fst ⁻¹' T) (fun _ hz ↦ hz) n).hom
        ((TopCat.singularHomologyCrossRel (TopCat.of X) (TopCat.of Y) Tᶜ R S i j n hn).hom
          (a ⊗ₜ b)) := by
  have h' : (ContinuousMap.id X).prodMap g ⁻¹' (Prod.fst ⁻¹' T) ⊆ Prod.fst ⁻¹' T :=
    fun _ hz ↦ hz
  have hT : Set.MapsTo (𝟙 (TopCat.of X)) Tᶜ Tᶜ := fun _ hx ↦ hx
  have hnat := TopCat.singularHomologyCrossRel_naturality (TopCat.of X) (TopCat.of Y) Tᶜ R S i j
    n hn (B' := Tᶜ) (𝟙 (TopCat.of X)) hT (TopCat.ofHom g)
  rw [← localHomologyRestriction_def R (subset_refl T) i, localHomologyRestriction_refl,
    MonoidalCategory.id_tensorHom] at hnat
  have hfg : TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of X) ⊗ₘ TopCat.ofHom g)
      (TopCat.mapsTo_tensorHom_preimage_fst _ _ hT)) (R ⊗ S) n =
      localHomologyMap (R ⊗ S) ((ContinuousMap.id X).prodMap g) h' n := by
    have hXg : 𝟙 (TopCat.of X) ⊗ₘ TopCat.ofHom g =
        TopCat.ofHom ((ContinuousMap.id X).prodMap g) :=
      TopCat.hom_ext (ContinuousMap.ext fun z ↦ TopCat.tensor_apply _ _ z)
    have h₁ : TopPair.ofSubsetMap (𝟙 (TopCat.of X) ⊗ₘ TopCat.ofHom g)
        (TopCat.mapsTo_tensorHom_preimage_fst _ _ hT) =
        TopPair.ofSubsetMap (X := TopCat.of (X × Y)) (Y := TopCat.of (X × Y'))
          (B := (Prod.fst ⁻¹' T)ᶜ) (B' := (Prod.fst ⁻¹' T)ᶜ)
          (TopCat.ofHom ((ContinuousMap.id X).prodMap g))
          ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h')) :=
      TopPair.hom_ext_of_fst _
        (Eq.trans (TopPair.ofSubsetMap_fst _ _) (hXg.trans (TopPair.ofSubsetMap_fst _ _).symm))
    exact (congrArg (fun φ ↦ TopPair.singularHomologyMap φ _ n) h₁).trans
      (localHomologyMap_def _ ((ContinuousMap.id X).prodMap g) h' n).symm
  rw [hfg] at hnat
  exact ConcreteCategory.congr_hom hnat (a ⊗ₜ b)

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

namespace HomologicalOrientation

open AlgebraicTopology

variable {M E V : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [ChartedSpace V M]
  [TopologicalSpace E] {n : ℕ} (o : HomologicalOrientation M V n) (hn : Module.finrank ℝ V = n)

/-- The localization of the fundamental class at a point `b`, for the identity of `M`, is the
local orientation `o b`. -/
theorem fiberLocalization_id_fundamentalClass (b : M) :
    (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) id b n).hom (o.fundamentalClass hn) =
      (o b).val := by
  rw [fiberLocalization_id]
  -- After this rewrite the composite lands in `localHomology R {b} n` while the goal expects
  -- `localHomology R (id ⁻¹' {b}) n`. The two agree only after unfolding `id ⁻¹' {b}`, so the
  -- goal is not type-correct at reducible transparency and `rw` cannot match `comp_apply` or
  -- `singularHomologyToLocalHomology_apply`; `erw` matches up to this unfolding.
  erw [ModuleCat.comp_apply]
  erw [← singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_fundamentalClass]

include hn in
/-- **Multiples of the fundamental class.** For the identity of a compact oriented manifold, the
multiple `d • [M]` of the fundamental class lives over the fundamental class at any point exactly
when `d ≠ 0`: its localization at `b` is `d` times the local orientation at `b`, which has
infinite order. -/
@[simp]
theorem livesOverFundamentalClass_id_zsmul_fundamentalClass_iff (b : M) (d : ℤ) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) id b (d • o.fundamentalClass hn) ↔
      d ≠ 0 := by
  rw [livesOverFundamentalClass_iff, map_zsmul, o.fiberLocalization_id_fundamentalClass hn,
    not_iff_not]
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

variable {Y : Type} [TopologicalSpace Y]

include hn in
/-- **Cross products with the fundamental class.** For a compact oriented `n`-manifold `M`, a
space `Y` and an integral class `α ∈ Hₖ(Y; ℤ)`, the cross product `[M] × α` lives over the
fundamental class of `M`, at any point, for the projection `M × Y → M`, exactly when `α ≠ 0`. -/
theorem livesOverFundamentalClass_singularHomologyCross_fundamentalClass_iff (b : M) {k m : ℕ}
    (h : n + k = m)
    {α : ((TopCat.toSSet.obj (TopCat.of Y)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) k :
      ModuleCat.{0} ℤ)} :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
        (id ∘ Prod.fst) b ((TopCat.singularHomologyCross (TopCat.of M) (TopCat.of Y)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) n k m h).hom
            (o.fundamentalClass hn ⊗ₜ α)) ↔
      α ≠ 0 := by
  refine ⟨fun hα ↦ hα.right_ne_zero_of_singularHomologyCross _ _ h, fun hα ↦ ?_⟩
  -- Over the integers the relative cross product is injective, and tensoring with the local
  -- orientation `o b` is injective.
  have hx := fiberLocalization_singularHomologyCross_tmul (ModuleCat.of ℤ (ULift.{0} ℤ))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (id : M → M) b h (o.fundamentalClass hn) α
  rw [o.fiberLocalization_id_fundamentalClass hn] at hx
  exact fun h₀ ↦ (map_ne_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance)).2
    (o.apply_tmul_ne_zero hn b hα) (hx.symm.trans h₀)

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
