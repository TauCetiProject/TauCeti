/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

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

* **Naturality** (the topological form of the source's Proposition 2.12). A map `σ : E → E'` with
  `σ⁻¹(p'⁻¹(b')) ⊆ p⁻¹(b)`, for instance a map over `M` with `p' ∘ σ = p` and `b' = b`, is a map of
  pairs `(E, E ∖ p⁻¹(b)) → (E', E' ∖ p'⁻¹(b'))`, and localization commutes with it
  (`TauCeti.homologyMap_comp_fiberLocalization`). Hence if `σ_* α` lives over the fundamental
  class, so does `α` (`TauCeti.LivesOverFundamentalClass.of_homologyMap`). With `σ = p` and
  `p' = id`, a class lives over the fundamental class as soon as its image in `Hₖ(M)` does
  (`TauCeti.LivesOverFundamentalClass.of_homologyMap_proj`). Localization also commutes with
  changing coefficients (`TauCeti.singularHomologyFunctor_map_app_comp_fiberLocalization`), so a
  class lives over the fundamental class if its image under a change of coefficients does
  (`TauCeti.LivesOverFundamentalClass.of_singularHomologyFunctor_map_app`), and living over the
  fundamental class is invariant under coefficient isomorphisms
  (`TauCeti.livesOverFundamentalClass_singularHomologyFunctor_map_app_iff`).
* **Products.** If `B ∖ {b}` is contractible, the localization
  `Hₖ(B × F) → Hₖ(B × F, (B ∖ {b}) × F)` at the fibre of the projection over `b` is an
  epimorphism (`TauCeti.epi_fiberLocalization_fst`).
* **Sections.** For a section `s` of `p`, the composite `p_* ∘ s_*` is the identity on homology
  (`TauCeti.homologyMap_comp_homologyMap_of_comp_eq_id`), and the localization of `s_* β` is the
  image under `s` of the localization of `β`. So a class `α` with `p_* α = 0` that lives over the
  fundamental class keeps doing so after subtracting any class `s_* β`
  (`TauCeti.LivesOverFundamentalClass.sub_homologyMap_section`), and some class lives over the
  fundamental class modulo the classes `s_* β` exactly when some class with `p_* α = 0` lives over
  it (`TauCeti.exists_forall_livesOverFundamentalClass_sub_iff`). For the evaluation fibration
  `Map(S², Q) → Q` and its section by constant spheres, this is the step from Definition 6.11 to
  the class used in the proof of Theorem 6.12 of the source.
* **The trivial fibration.** For the identity of a compact oriented `n`-manifold `M` and integer
  coefficients, the localization of `Hₙ(M)` at a point is the map to the local homology
  `Hₙ(M, M ∖ {b})`, sending `[M]` to the local orientation at `b`
  (`TauCeti.HomologicalOrientation.fiberLocalization_id_fundamentalClass`), and the multiple
  `d • [M]` of the fundamental class lives over the fundamental class exactly when `d ≠ 0`
  (`TauCeti.HomologicalOrientation.livesOverFundamentalClass_id_zsmul_fundamentalClass_iff`). So
  for a section `s` of a map `p` to `M`, a class of `Hₙ(E; ℤ)` lives over the fundamental class
  modulo all classes `s_* β` exactly when it does so modulo the multiples of `s_*[M]`
  (`TauCeti.HomologicalOrientation.forall_livesOverFundamentalClass_sub_iff`). When
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

open CategoryTheory Limits Set

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

/-- **Naturality of the localization at the fibre**: for a map `σ : E → E'` with
`σ⁻¹(p'⁻¹(b')) ⊆ p⁻¹(b)`, for instance a map over `M` with `p' ∘ σ = p` and `b' = b`, localizing
`σ_* α` at the fibre of `p'` over `b'` is the image under `σ` of the localization of `α` at the
fibre of `p` over `b`. This is the topological form of the naturality of the shriek map of a point
under maps of fibrations (Barraud–Damian–Humilière–Oancea, Proposition 2.12). -/
@[reassoc, elementwise]
theorem homologyMap_comp_fiberLocalization (σ : C(E, E')) {M' : Type w} {p : E → M} {p' : E' → M'}
    {b : M} {b' : M'} (h : σ ⁻¹' (p' ⁻¹' {b'}) ⊆ p ⁻¹' {b}) (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) R k ≫ fiberLocalization R p' b' k =
      fiberLocalization R p b k ≫ localHomologyMap R σ h k := by
  have h' := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap (X := TopCat.of E) (Y := TopCat.of E') (B := (p ⁻¹' {b})ᶜ)
      (B' := (p' ⁻¹' {b'})ᶜ) (TopCat.ofHom σ) ((mapsTo_preimage _ _).mono_left
        (compl_subset_compl.2 h))) R k
  simp only [TopPair.ofSubsetMap_fst] at h'
  rw [localHomologyMap_def]
  exact h'

/-- **Naturality of the localization at the fibre in the coefficients**: changing coefficients
along `φ : R ⟶ R'` commutes with localizing at the fibre of `p` over `b`. This is
`TauCeti.TopPair.singularHomologyπ_coefficient_naturality` for the pair `(E, E ∖ p⁻¹(b))`. -/
@[reassoc]
theorem singularHomologyFunctor_map_app_comp_fiberLocalization {R' : A} (φ : R ⟶ R')
    (p : E → M) (b : M) (k : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor A k).map φ).app (TopCat.of E) ≫
        fiberLocalization R' p b k =
      fiberLocalization R p b k ≫ HomologicalComplex.homologyMap
        (((SSetPair.chainComplexFunctor A).map φ).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E))))) k :=
  TopPair.singularHomologyπ_coefficient_naturality
    (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E))) φ k

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

/-- **Localization at a fibre of a product is an epimorphism** when the base minus the point is
contractible: for `b ∈ B` with `B ∖ {b}` contractible, `Hₖ(B × F) → Hₖ(B × F, (B ∖ {b}) × F)` is
an epimorphism. -/
theorem epi_fiberLocalization_fst {B F : Type w} [TopologicalSpace B] [TopologicalSpace F] (b : B)
    [ContractibleSpace ({b}ᶜ : Set B)] (k : ℕ) :
    Epi (fiberLocalization R (Prod.fst : B × F → B) b k) := by
  cases k with
  | zero => exact inferInstanceAs (Epi (TopPair.singularHomologyπ _ R 0))
  | succ k =>
  -- The next map `Hₖ((B ∖ {b}) × F) → Hₖ(B × F)` of the pair sequence is a monomorphism, since
  -- its composite with the projection to `F` is induced by a homotopy equivalence.
  let P : TopPair := TopPair.ofSubset ((Prod.fst ⁻¹' {b})ᶜ : Set (TopCat.of (B × F)))
  let snd : P.fst ⟶ TopCat.of F := TopCat.ofHom ContinuousMap.snd
  -- The complement `(B ∖ {b}) × F` of the fibre, projected onto `F`.
  let h : ((Prod.fst ⁻¹' {b})ᶜ : Set (B × F)) ≃ₜ F × ({b}ᶜ : Set B) :=
    { toFun := fun x ↦ (x.1.2, ⟨x.1.1, x.2⟩)
      invFun := fun y ↦ ⟨(y.2.1, y.1), y.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e := h.toHomotopyEquiv.trans
    (ContinuousMap.HomotopyEquiv.prodContractible F ({b}ᶜ : Set B))
  have he : TopCat.ofHom e.toFun = P.map ≫ snd := by
    ext x
    simp [e, ContinuousMap.HomotopyEquiv.trans_apply, h, P, snd]
    rfl
  have hiso : IsIso (SSet.homologyMap (TopCat.toSSet.map P.map) R k ≫
      SSet.homologyMap (TopCat.toSSet.map snd) R k) := by
    have := (e.singularHomologyIso R k).isIso_hom
    rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom, singularHomologyFunctor_obj_map]
      at this
    rwa [← SSet.homologyMap_comp, ← Functor.map_comp, ← he]
  have hmono : Mono (SSet.homologyMap (TopCat.toSSet.map P.map) R k) :=
    mono_of_mono _ (SSet.homologyMap (TopCat.toSSet.map snd) R k)
  exact (P.singularHomology_exact_relative R (k + 1) k).epi_f_iff.2
    ((P.singularHomology_exact_subspace R (k + 1) k).mono_g_iff.1 hmono)

end Localization

section LivesOver

variable {Λ : Type w} [Ring Λ] (R : ModuleCat.{w} Λ)
  {E E' M : Type w} [TopologicalSpace E] [TopologicalSpace E']

/-- Pointwise form of `TauCeti.fiberLocalization_id`: for the identity of `M`, the localization of
`α` at the fibre over `b` is its image in the local homology `Hₖ(M, M ∖ {b})`. The fibre
`id ⁻¹' {b}` is `{b}` by definition. -/
theorem fiberLocalization_id_apply [TopologicalSpace M] (b : M) {k : ℕ}
    (α : ((TopCat.toSSet.obj (TopCat.of M)).homology R k : ModuleCat.{w} Λ)) :
    (fiberLocalization R (id : M → M) b k).hom α = singularHomologyToLocalHomology R b k α :=
  -- Both sides restrict the image of `α` in `Hₖ(M, M ∖ M)` to `{b}`, on the left through
  -- `ModuleCat.Hom.hom` of a composite and on the right through the concrete-category coercion.
  (congrArg (fun f ↦ f.hom α) (fiberLocalization_id R b k)).trans
    (singularHomologyToLocalHomology_apply R b α).symm

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

/-- **Classes living over the fundamental class pull back along maps.** If `σ : E → E'` satisfies
`σ⁻¹(p'⁻¹(b')) ⊆ p⁻¹(b)`, for instance `p' ∘ σ = p` and `b' = b`, and `σ_* α` lives over the
fundamental class at `b'` for `p'`, then `α` lives over the fundamental class at `b` for `p`. -/
theorem LivesOverFundamentalClass.of_homologyMap (σ : C(E, E')) {M' : Type w} {p : E → M}
    {p' : E' → M'} {b : M} {b' : M'} (h : σ ⁻¹' (p' ⁻¹' {b'}) ⊆ p ⁻¹' {b}) {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (hα : LivesOverFundamentalClass R p' b'
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) R k).hom α)) :
    LivesOverFundamentalClass R p b α := by
  intro h'
  apply hα
  rw [homologyMap_comp_fiberLocalization_apply R σ h _, h', map_zero]

/-- If the image `p_* α` of a class of `E` in the homology of `M` lives over the fundamental class
at `b`, then `α` lives over the fundamental class at `b` for `p`. -/
theorem LivesOverFundamentalClass.of_homologyMap_proj [TopologicalSpace M] (p : C(E, M))
    {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (hα : LivesOverFundamentalClass R id b
      ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α)) :
    LivesOverFundamentalClass R p b α :=
  hα.of_homologyMap R p subset_rfl

/-- **Classes over a section.** Let `s` be a section of `p : E → M`. If `α ∈ Hₖ(E)` lives over
the fundamental class at `b` and `p_* α = 0`, then `α - s_* β` lives over the fundamental class
at `b` for every `β ∈ Hₖ(M)`. -/
theorem LivesOverFundamentalClass.sub_homologyMap_section [TopologicalSpace M] (p : C(E, M))
    (s : C(M, E)) (hs : p.comp s = ContinuousMap.id M) {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (hα₀ : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α = 0)
    (hα : LivesOverFundamentalClass R p b α)
    (β : ((TopCat.toSSet.obj (TopCat.of M)).homology R k : ModuleCat.{w} Λ)) :
    LivesOverFundamentalClass R p b
      (α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom s)) R k).hom β) := by
  have hsb : s ⁻¹' (p ⁻¹' {b}) ⊆ id ⁻¹' {b} := by
    rw [← preimage_comp, ← ContinuousMap.coe_comp, hs, ContinuousMap.coe_id]
  intro h
  rw [map_sub, sub_eq_zero] at h
  -- The localization of `β = p_* s_* β` at `b` is the image under `p` of the localization of
  -- `s_* β`, which is that of `α`; so it is the localization of `p_* α = 0`.
  have hβ : (fiberLocalization R id b k).hom β = 0 := calc
    (fiberLocalization R id b k).hom β
        = (localHomologyMap R p subset_rfl k).hom ((fiberLocalization R p b k).hom
            ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom s)) R k).hom β)) := by
      rw [← homologyMap_comp_fiberLocalization_apply R p (b' := b) subset_rfl,
        homologyMap_comp_homologyMap_of_comp_eq_id_apply R p s hs k]
    _ = (localHomologyMap R p subset_rfl k).hom ((fiberLocalization R p b k).hom α) := by rw [h]
    _ = 0 := by
      rw [← homologyMap_comp_fiberLocalization_apply R p (b' := b) subset_rfl, hα₀, map_zero]
  apply hα
  rw [h, homologyMap_comp_fiberLocalization_apply R s hsb, hβ, map_zero]

/-- **Classes over a section, up to the section.** Let `s` be a section of `p : E → M`. Some
`α ∈ Hₖ(E)` keeps living over the fundamental class at `b` after subtracting any class `s_* β`,
`β ∈ Hₖ(M)`, exactly when some `α' ∈ Hₖ(E)` with `p_* α' = 0` lives over the fundamental class at
`b`. Given `α`, the class `α' = α - s_* p_* α` works; conversely `α'` itself keeps living over the
fundamental class (`TauCeti.LivesOverFundamentalClass.sub_homologyMap_section`). -/
theorem exists_forall_livesOverFundamentalClass_sub_iff [TopologicalSpace M] (p : C(E, M))
    (s : C(M, E)) (hs : p.comp s = ContinuousMap.id M) (b : M) (k : ℕ) :
    (∃ α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ),
      ∀ β : ((TopCat.toSSet.obj (TopCat.of M)).homology R k : ModuleCat.{w} Λ),
        LivesOverFundamentalClass R p b
          (α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom s)) R k).hom β)) ↔
      ∃ α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ),
        (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α = 0 ∧
          LivesOverFundamentalClass R p b α := by
  refine ⟨fun ⟨α, hα⟩ ↦
    ⟨_, ?_, hα ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α)⟩,
    fun ⟨α, hα₀, hα⟩ ↦ ⟨α, hα.sub_homologyMap_section R p s hs hα₀⟩⟩
  rw [map_sub, homologyMap_comp_homologyMap_of_comp_eq_id_apply R p s hs k, sub_self]

/-- **Changing coefficients.** For a morphism `φ : R ⟶ R'` of coefficients, if the image in
`Hₖ(E; R')` of a class `α ∈ Hₖ(E; R)` lives over the fundamental class at `b`, then so does
`α`. -/
theorem LivesOverFundamentalClass.of_singularHomologyFunctor_map_app {R' : ModuleCat.{w} Λ}
    (φ : R ⟶ R') {p : E → M} {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (hα : LivesOverFundamentalClass R' p b
      ((((AlgebraicTopology.singularHomologyFunctor _ k).map φ).app (TopCat.of E)).hom α)) :
    LivesOverFundamentalClass R p b α := fun h ↦ hα <|
  -- Evaluate both composites of the naturality square at `α`; the lower one vanishes by `h`.
  (congrArg (fun f ↦ f.hom α)
    (singularHomologyFunctor_map_app_comp_fiberLocalization R φ p b k)).trans <|
      (congrArg (HomologicalComplex.homologyMap
        (((SSetPair.chainComplexFunctor (ModuleCat.{w} Λ)).map φ).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E))))) k).hom
        h).trans (map_zero _)

/-- **Changing coefficients along an isomorphism.** For an isomorphism `φ : R ⟶ R'` of
coefficients, the image in `Hₖ(E; R')` of a class `α ∈ Hₖ(E; R)` lives over the fundamental class
at `b` exactly when `α` does. -/
@[simp]
theorem livesOverFundamentalClass_singularHomologyFunctor_map_app_iff {R' : ModuleCat.{w} Λ}
    (φ : R ⟶ R') [IsIso φ] {p : E → M} {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)} :
    LivesOverFundamentalClass R' p b
        ((((AlgebraicTopology.singularHomologyFunctor _ k).map φ).app (TopCat.of E)).hom α) ↔
      LivesOverFundamentalClass R p b α := by
  refine ⟨LivesOverFundamentalClass.of_singularHomologyFunctor_map_app R φ, fun hα ↦ ?_⟩
  -- Changing coefficients on the relative group is an isomorphism, hence injective.
  have hinj : Function.Injective (HomologicalComplex.homologyMap
      (((SSetPair.chainComplexFunctor (ModuleCat.{w} Λ)).map φ).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set (TopCat.of E))))) k).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h := congrArg (fun f ↦ f.hom α)
    (singularHomologyFunctor_map_app_comp_fiberLocalization R φ p b k)
  -- `h` evaluates both composites at `α`; they are the two sides below by `ModuleCat.hom_comp`.
  exact (Iff.of_eq (congrArg (· ≠ 0) h)).2 ((hinj.ne_iff' (map_zero _)).2 hα)

end LivesOver

namespace HomologicalOrientation

open AlgebraicTopology

variable {M E V : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [ChartedSpace V M]
  [TopologicalSpace E] {n : ℕ} (o : HomologicalOrientation M V n) (hn : Module.finrank ℝ V = n)

/-- For the identity of a compact oriented manifold, the localization of the fundamental class at
`b` is the local orientation at `b`. -/
theorem fiberLocalization_id_fundamentalClass (b : M) :
    (fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) id b n).hom (o.fundamentalClass hn) =
      (o b).val :=
  (fiberLocalization_id_apply _ b _).trans (o.singularHomologyToLocalHomology_fundamentalClass hn b)

include hn in
/-- **Multiples of the fundamental class.** For the identity of a compact oriented manifold, the
multiple `d • [M]` of the fundamental class lives over the fundamental class at any point exactly
when `d ≠ 0`: its localization at `b` is `d` times the local orientation at `b`, which has
infinite order. -/
@[simp]
theorem livesOverFundamentalClass_id_zsmul_fundamentalClass_iff (b : M) (d : ℤ) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) id b (d • o.fundamentalClass hn) ↔
      d ≠ 0 := by
  rw [livesOverFundamentalClass_iff, map_zsmul, fiberLocalization_id_fundamentalClass, not_iff_not]
  exact ⟨fun h ↦ o.zsmul_left_injective hn b (h.trans (zero_smul ℤ _).symm),
    fun h ↦ h ▸ zero_smul ℤ _⟩

include hn in
/-- The fundamental class of a compact oriented manifold lives over itself at every point. -/
@[simp]
theorem livesOverFundamentalClass_id_fundamentalClass (b : M) :
    LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) id b (o.fundamentalClass hn) := by
  simpa using (o.livesOverFundamentalClass_id_zsmul_fundamentalClass_iff hn b 1).2 one_ne_zero

/-- **Classes over a section, modulo the fundamental class.** Let `s` be a section of a map
`p : E → M` to a compact oriented `n`-manifold. A class `α ∈ Hₙ(E; ℤ)` keeps living over the
fundamental class at `b` after subtracting any class `s_* β`, `β ∈ Hₙ(M; ℤ)`, exactly when it does
so after subtracting every multiple `d • s_*[M]`. -/
theorem forall_livesOverFundamentalClass_sub_iff (p : E → M) (s : C(M, E)) (hs : p ∘ s = id)
    (b : M)
    (α : ((TopCat.toSSet.obj (TopCat.of E)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)) :
    (∀ β : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
        ModuleCat.{0} ℤ),
      LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) p b
        (α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom s))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom β)) ↔
      ∀ d : ℤ, LivesOverFundamentalClass (ModuleCat.of ℤ (ULift.{0} ℤ)) p b
        (α - d • (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom s))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom (o.fundamentalClass hn)) := by
  refine ⟨fun h d ↦ by simpa using h (d • o.fundamentalClass hn), fun h β ↦ ?_⟩
  have hsb : s ⁻¹' (p ⁻¹' {b}) ⊆ id ⁻¹' {b} := by rw [← preimage_comp, hs]
  -- The localization of `β` at `b` is a multiple of the local orientation at `b`, which is the
  -- localization of `[M]`.
  obtain ⟨d, hd⟩ := (isLocalOrientation_iff _ _ _).1 (o b).property
    ((fiberLocalization (ModuleCat.of ℤ (ULift.{0} ℤ)) id b n).hom β)
  rw [← o.fiberLocalization_id_fundamentalClass hn b, ← map_zsmul] at hd
  intro h0
  apply h d
  rw [← map_zsmul, map_sub, homologyMap_comp_fiberLocalization_apply _ s hsb, hd,
    ← homologyMap_comp_fiberLocalization_apply _ s hsb, ← map_sub]
  exact h0

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
