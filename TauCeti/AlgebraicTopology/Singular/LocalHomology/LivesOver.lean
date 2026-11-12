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

* **Naturality** (the topological form of the source's Proposition 2.12). A map `σ : E → E'` over
  `M`, that is with `p' ∘ σ = p`, is a map of pairs `(E, E ∖ p⁻¹(b)) → (E', E' ∖ p'⁻¹(b))`, and
  localization commutes with it (`TauCeti.homologyMap_comp_fiberLocalization`). Hence if `σ_* α`
  lives over the fundamental class, so does `α`
  (`TauCeti.LivesOverFundamentalClass.of_homologyMap`). With `σ = p` and `p' = id`, a class lives
  over the fundamental class as soon as its image in `Hₖ(M)` does
  (`TauCeti.LivesOverFundamentalClass.of_homologyMap_proj`).
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
* **Fibrations with a section.** For a section `σ` of `p`, the class `α - σ_* p_* α` is killed
  by `p`, and lives over the fundamental class at `b` when the localization of `α` is not the
  image under `σ` of a local homology class of `M` at `b`
  (`TauCeti.livesOverFundamentalClass_sub_homologyMap_of_leftInverse`); such a class itself lives
  over the fundamental class
  (`TauCeti.livesOverFundamentalClass_of_notMem_range_localHomologyMap`). Conversely the
  localization of a class living over the fundamental class and killed by `p` is not such an
  image (`TauCeti.LivesOverFundamentalClass.notMem_range_localHomologyMap`). This is the
  reduction in the proof of the source's Theorem 6.12.

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

variable {Λ : Type w} [Ring Λ] (R : ModuleCat.{w} Λ)
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

section Section

/-! ### Fibrations with a section

For a map `p : E → M` with a continuous section `σ`, the classes of `E` coming from `M` through
`σ` localize at the fibre over `b` into the image of the local homology of `M` at `b`. Removing
this part of a class gives a class killed by `p` with the same localization modulo that image.
This is the reduction in the proof of Theorem 6.12 of Barraud–Damian–Humilière–Oancea, for the
evaluation fibration `Map(S², Q) → Q` and its section by constant spheres. -/

variable {Λ : Type w} [Ring Λ] (R : ModuleCat.{w} Λ)
  {E M : Type w} [TopologicalSpace E] [TopologicalSpace M] {p : C(E, M)} {σ : C(M, E)}

/-- A class whose localization at the fibre over `b` is not the image of a local homology class
of `M` at `b` under a map `σ : M → E` lives over the fundamental class at `b`, since the zero
class is such an image. -/
theorem livesOverFundamentalClass_of_notMem_range_localHomologyMap {b : M} {k : ℕ}
    (hs : σ ⁻¹' (p ⁻¹' {b}) ⊆ {b})
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (hα : (fiberLocalization R p b k).hom α ∉ LinearMap.range (localHomologyMap R σ hs k).hom) :
    LivesOverFundamentalClass R p b α :=
  fun h ↦ hα ⟨0, by rw [map_zero, h]⟩

/-- **Removing the part of a class coming from a section.** Let `σ` be a section of `p` and
`α ∈ Hₖ(E)`. Then `α - σ_* p_* α` is killed by `p`, and lives over the fundamental class at `b` as
soon as the localization of `α` at the fibre over `b` is not the image under `σ` of a local
homology class of `M` at `b`. -/
theorem livesOverFundamentalClass_sub_homologyMap_of_leftInverse
    (hσ : Function.LeftInverse p σ) {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (hα : (fiberLocalization R p b k).hom α ∉ LinearMap.range
      (localHomologyMap R σ (hσ.preimage_preimage {b}).subset k).hom) :
    LivesOverFundamentalClass R p b (α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ))
      R k).hom ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α)) := by
  intro h
  rw [map_sub, sub_eq_zero] at h
  refine hα ⟨(fiberLocalization R id b k).hom
    ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α), (h.trans ?_).symm⟩
  exact ConcreteCategory.congr_hom (homologyMap_comp_fiberLocalization R σ hσ.comp_eq_id b k) _

/-- The class `α - σ_* p_* α` is killed by `p`, for a section `σ` of `p`. -/
theorem homologyMap_sub_homologyMap_eq_zero_of_leftInverse (hσ : Function.LeftInverse p σ)
    {k : ℕ} (α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)) :
    (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom
        (α - (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) R k).hom
          ((SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α)) = 0 := by
  rw [map_sub, sub_eq_zero, ← ModuleCat.comp_apply, ← SSet.homologyMap_comp, ← Functor.map_comp,
    ← TopCat.ofHom_comp, show p.comp σ = ContinuousMap.id M from ContinuousMap.ext hσ,
    TopCat.ofHom_id, CategoryTheory.Functor.map_id, SSet.homologyMap_id, CategoryTheory.id_apply]

/-- **Classes killed by the projection.** If `α ∈ Hₖ(E)` lives over the fundamental class at `b`
and `p_* α = 0`, then the localization of `α` at the fibre over `b` is not the image under a
section `σ` of a local homology class of `M` at `b`: applying `p` to such an image recovers the
local homology class, while it kills the localization of `α`. -/
theorem LivesOverFundamentalClass.notMem_range_localHomologyMap
    (hσ : Function.LeftInverse p σ) {b : M} {k : ℕ}
    {α : ((TopCat.toSSet.obj (TopCat.of E)).homology R k : ModuleCat.{w} Λ)}
    (h : LivesOverFundamentalClass R p b α)
    (hα : (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom p)) R k).hom α = 0) :
    (fiberLocalization R p b k).hom α ∉ LinearMap.range
      (localHomologyMap R σ (hσ.preimage_preimage {b}).subset k).hom := by
  rintro ⟨y, hy⟩
  have hp : p ⁻¹' (id ⁻¹' {b}) ⊆ p ⁻¹' {b} := subset_rfl
  have hid : localHomologyMap R σ (hσ.preimage_preimage {b}).subset k ≫
      localHomologyMap R p hp k = 𝟙 _ := by
    rw [localHomologyMap_comp,
      localHomologyMap_congr R (ContinuousMap.ext hσ : p.comp σ = ContinuousMap.id M),
      localHomologyMap_id]
    exact localHomologyRestriction_refl R _ k
  have hpα := ConcreteCategory.congr_hom
    (homologyMap_comp_fiberLocalization R p (Function.id_comp _) b k) α
  have hy' := ConcreteCategory.congr_hom hid y
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hpα hy'
  rw [hα, map_zero, ← hy, hy'] at hpα
  exact h (by rw [← hy, ← hpα, map_zero])

end Section

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
  erw [localHomologyRestriction_singularHomologyπ_fundamentalClass]
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
