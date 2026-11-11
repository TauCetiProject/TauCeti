/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.Product
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.AbsoluteCup

/-!
# The Leray–Hirsch map and its Mayer–Vietoris gluing step

Let `k` be a commutative ring, `p : E ⟶ B` a continuous map, and for every degree `d` let
`e d : ι d → Hᵈ(E; k)` be a family of global classes on `E`. The **Leray–Hirsch map** in degree `n`
is

`⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ Hⁿ(E; k)`, `(a_{d,i}) ↦ ∑ p^* a_{d,i} ⌣ e_{d,i}`

(`TopCat.lerayHirsch`), with the source of the Leray–Hirsch map of a product
`TopCat.lerayHirschProd`: for the projection `X × F ⟶ X` and the pullbacks of a family of classes
on `F` the two agree (`TopCat.lerayHirsch_fst`). The Leray–Hirsch theorem asserts that it is
bijective for a locally trivial bundle whose classes `e` restrict to a basis of the cohomology of
every fibre. The map is natural in maps of spaces over a map of bases
(`TopCat.lerayHirsch_lof_naturality`), so its bijectivity is invariant under homeomorphisms over
homeomorphisms (`TopCat.bijective_lerayHirsch_iff_of_isIso`).

The main result is the **Mayer–Vietoris gluing step** (`TopCat.bijective_lerayHirsch_union`): for
open subsets `U` and `V` of `B`, if the Leray–Hirsch maps of the restrictions of `p` over `U`, `V`
and `U ∩ V`, with the restricted classes (`TopCat.lerayHirschRestrict`), are bijective in degrees
`m ≤ n`, then so is the Leray–Hirsch map of the restriction of `p` over `U ∪ V`. Together with the
product case `TopCat.lerayHirschProd_bijective`, induction over a finite cover of `B` by open sets
over which `p` is trivial, with trivializations carrying the classes `e` to pullbacks of classes of
the fibre, then gives the Leray–Hirsch theorem over a base with such a finite cover. This finite
open cover route is the classical one; for arbitrary bases one instead inducts over cells and
skeleta of a CW approximation.

The proof of the gluing step is the five lemma. The Mayer–Vietoris sequences of the cover
`{U, V}` of `U ∪ V` (one for each summand of the source) and of the cover `{p⁻¹ U, p⁻¹ V}` of
`p⁻¹ (U ∪ V)` are long exact sequences, and the Leray–Hirsch maps form a map between them: on the
restriction maps by naturality, and on the connecting morphisms because
`δ (p^* a ⌣ e|) = δ (p^* a) ⌣ e = p^* (δ a) ⌣ e`
(`TopCat.singularCohomologyMayerVietorisδ_singularCup` and the naturality of `δ`). We first prove
it when `U ∪ V = B` (`TopCat.bijective_lerayHirsch_of_union_eq_univ`), and deduce the general case
by applying this to the restriction of `p` over `U ∪ V`.

## Main definitions and results

* `TopCat.lerayHirsch`: the Leray–Hirsch map, characterized on summands by
  `TopCat.lerayHirsch_lof`; `TopCat.lerayHirsch_fst`: for a product it is
  `TopCat.lerayHirschProd`.
* `TopCat.lerayHirsch_lof_naturality`: naturality in maps over a map of bases.
* `TopCat.lerayHirschRestrict`: the Leray–Hirsch map of the restriction of `p` over a subset of
  `B`, with the restricted classes.
* `TopCat.bijective_lerayHirsch_of_union_eq_univ` and `TopCat.bijective_lerayHirsch_union`: the
  Mayer–Vietoris gluing step.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch) and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped DirectSum

universe w

namespace TopCat

variable {k : Type w} [CommRing k]

section Definition

variable {E B : TopCat.{w}} (p : E ⟶ B) (n : ℕ) {ι : ℕ → Type w} [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- **The Leray–Hirsch map** of `p : E ⟶ B` and a family of classes `e d : ι d → Hᵈ(E; k)` in degree
`n`, `⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ Hⁿ(E; k)`, sending `a` in the summand indexed by
`d + q = n` and `i : ι d` to `p^* a ⌣ e d i`. -/
def lerayHirsch :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) →ₗ[k]
      E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  DirectSum.toModule k _ _ fun j ↦
    (E.singularCup k (λ_ _).inv (λ_ _).hom j.1.1.2 j.1.1.1 n
        (by rw [add_comm]; exact j.1.2)).flip (e j.1.1.1 j.2) ∘ₗ
      (TopCat.singularCohomologyMap p j.1.1.2).hom

/-- The Leray–Hirsch map sends `a` in the summand indexed by `d + q = n` and `i : ι d` to
`p^* a ⌣ e d i`. -/
@[simp]
lemma lerayHirsch_lof (d q : ℕ) (h : d + q = n) (i : ι d)
    (a : B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirsch p n e (DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(d, q), h⟩, i⟩ a) =
      E.singularCup k (λ_ _).inv (λ_ _).hom q d n (by omega)
        (TopCat.singularCohomologyMap p q a) (e d i) := by
  simp [lerayHirsch]

/-- For the projection `X × F ⟶ X` and the pullbacks of a family `b` of classes on `F`, the
Leray–Hirsch map is the Leray–Hirsch map of the product `TopCat.lerayHirschProd`. -/
lemma lerayHirsch_fst (X F : TopCat.{w})
    (b : ∀ d, Module.Basis (ι d) k
      (F.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)) :
    lerayHirsch (CartesianMonoidalCategory.fst X F) n
        (fun d i ↦ TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X F) d (b d i)) =
      lerayHirschProd X F n b :=
  DirectSum.linearMap_ext k fun ⟨⟨⟨d, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, lerayHirsch_lof, lerayHirschProd_lof]

end Definition

section Naturality

variable {E B E' B' : TopCat.{w}} {p : E ⟶ B} {p' : E' ⟶ B'} {n : ℕ} {ι : ℕ → Type w}
  [∀ d, DecidableEq (ι d)]
  {e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d}
  {e' : ∀ d, ι d → E'.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d}

/-- **Naturality of the Leray–Hirsch map.** For maps `f : E' ⟶ E` and `g : B' ⟶ B` with
`f ≫ p = p' ≫ g`, carrying the classes `e` to the classes `e'`, the Leray–Hirsch map of `p'` sends
`g^* a` in a summand to the pullback along `f` of the image of `a` under the Leray–Hirsch map of
`p`. -/
lemma lerayHirsch_lof_naturality (f : E' ⟶ E) (g : B' ⟶ B) (hfg : f ≫ p = p' ≫ g)
    (he : ∀ d i, TopCat.singularCohomologyMap f d (e d i) = e' d i)
    (d q : ℕ) (h : d + q = n) (i : ι d)
    (a : B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirsch p' n e' (DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦
        B'.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(d, q), h⟩, i⟩ (TopCat.singularCohomologyMap g q a)) =
      TopCat.singularCohomologyMap f n (lerayHirsch p n e (DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
          B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(d, q), h⟩, i⟩ a)) := by
  rw [lerayHirsch_lof, lerayHirsch_lof, ← singularCup_naturality, ← he,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_comp, hfg]

/-- The map `⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ ⨁_{d + q = n} ⨁_{i : ι d} H^q(B'; k)` induced by
`g : B' ⟶ B` on the sources of Leray–Hirsch maps. -/
private abbrev sourceMap (g : B' ⟶ B) (n : ℕ) (ι : ℕ → Type w) :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) →ₗ[k]
      ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        B'.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2 :=
  DirectSum.lmap fun j ↦ (TopCat.singularCohomologyMap g j.1.1.2).hom

private lemma lerayHirsch_comp_sourceMap (f : E' ⟶ E) (g : B' ⟶ B) (hfg : f ≫ p = p' ≫ g)
    (he : ∀ d i, TopCat.singularCohomologyMap f d (e d i) = e' d i) :
    lerayHirsch p' n e' ∘ₗ sourceMap g n ι =
      (TopCat.singularCohomologyMap f n).hom ∘ₗ lerayHirsch p n e := by
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨d, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof]
  exact lerayHirsch_lof_naturality f g hfg he d q h i a

/-- Bijectivity of the Leray–Hirsch map is invariant under isomorphisms `f : E' ⟶ E` and
`g : B' ⟶ B` with `f ≫ p = p' ≫ g` carrying the classes `e` to the classes `e'`. -/
lemma bijective_lerayHirsch_iff_of_isIso (f : E' ⟶ E) (g : B' ⟶ B) [IsIso f] [IsIso g]
    (hfg : f ≫ p = p' ≫ g)
    (he : ∀ d i, TopCat.singularCohomologyMap f d (e d i) = e' d i) :
    Function.Bijective (lerayHirsch p' n e') ↔ Function.Bijective (lerayHirsch p n e) := by
  have hbij {X Y : TopCat.{w}} (φ : X ⟶ Y) [IsIso φ] (m : ℕ) :
      Function.Bijective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
        (M := 𝟙_ (ModuleCat.{w} k)) φ m) :=
    ((TauCeti.singularCohomologyFunctor _ k _ m).mapIso (asIso φ).op).toLinearEquiv.bijective
  have hsrc : Function.Bijective (sourceMap g n ι) :=
    ⟨(DirectSum.lmap_injective _).2 fun j ↦ (hbij g _).1,
      (DirectSum.lmap_surjective _).2 fun j ↦ (hbij g _).2⟩
  have h := lerayHirsch_comp_sourceMap (n := n) f g hfg he
  constructor
  · intro h'
    have : Function.Bijective ((TopCat.singularCohomologyMap f n).hom ∘ₗ lerayHirsch p n e) := by
      rw [← h]
      exact h'.comp hsrc
    exact (Function.Bijective.of_comp_iff' (hbij f n) _).1 this
  · intro h'
    have : Function.Bijective (lerayHirsch p' n e' ∘ₗ sourceMap g n ι) := by
      rw [h]
      exact (hbij f n).comp h'
    exact (Function.Bijective.of_comp_iff _ hsrc).1 this

end Naturality

section Restrict

variable {E B : TopCat.{w}} (p : E ⟶ B) {ι : ℕ → Type w} [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- The Leray–Hirsch map in degree `n` of the restriction `p⁻¹ S ⟶ S` of `p` over a subset `S` of
`B`, with the restrictions of the classes `e` to `p⁻¹ S`. -/
abbrev lerayHirschRestrict (S : Set B) (n : ℕ) :=
  lerayHirsch (ofHom (p.hom.restrictPreimage S)) n
    (fun d i ↦ TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (p ⁻¹' S))) d (e d i))

end Restrict

/-! ### Linear algebra for the five lemma -/

section LinearAlgebra

/-- An exact short complex of modules gives exact linear maps between modules identified with its
terms. -/
private lemma function_exact_of_linearEquiv {S : ShortComplex (ModuleCat.{w} k)} (hS : S.Exact)
    {X₁ X₂ X₃ : Type w} [AddCommGroup X₁] [Module k X₁] [AddCommGroup X₂] [Module k X₂]
    [AddCommGroup X₃] [Module k X₃] (F : X₁ →ₗ[k] X₂) (G : X₂ →ₗ[k] X₃) (e₁ : S.X₁ ≃ₗ[k] X₁)
    (e₂ : S.X₂ ≃ₗ[k] X₂) (e₃ : S.X₃ ≃ₗ[k] X₃) (h₁ : ∀ x, e₂ (S.f x) = F (e₁ x))
    (h₂ : ∀ x, e₃ (S.g x) = G (e₂ x)) : Function.Exact F G := by
  intro y
  constructor
  · intro hy
    have : S.g (e₂.symm y) = 0 := e₃.injective (by rw [h₂, e₂.apply_symm_apply, hy, map_zero])
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff S).1 hS _ this
    exact ⟨e₁ x, by rw [← h₁, hx, e₂.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := e₁.surjective x
    rw [← h₁, ← h₂, S.moduleCat_zero_apply, map_zero]

/-- An element of a biproduct of modules is the sum of the images of its two components. -/
private lemma biprod_apply_eq {B₁ B₂ : ModuleCat.{w} k} (x : ↑(B₁ ⊞ B₂)) :
    x = (biprod.inl : B₁ ⟶ B₁ ⊞ B₂) ((biprod.fst : B₁ ⊞ B₂ ⟶ B₁) x) +
      (biprod.inr : B₂ ⟶ B₁ ⊞ B₂) ((biprod.snd : B₁ ⊞ B₂ ⟶ B₂) x) := by
  exact (congrArg (fun φ : B₁ ⊞ B₂ ⟶ B₁ ⊞ B₂ ↦ φ x) (biprod.total (X := B₁) (Y := B₂))).symm

variable {J : Type w} {A B C : J → Type w} [∀ j, AddCommGroup (A j)]
  [∀ j, Module k (A j)] [∀ j, AddCommGroup (B j)] [∀ j, Module k (B j)]
  [∀ j, AddCommGroup (C j)] [∀ j, Module k (C j)]

/-- A direct sum of exact sequences is exact. -/
private lemma exact_lmap (f : ∀ j, A j →ₗ[k] B j) (g : ∀ j, B j →ₗ[k] C j)
    (h : ∀ j, Function.Exact (f j) (g j)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  rw [LinearMap.exact_iff, DirectSum.ker_lmap, DirectSum.range_lmap]
  simp only [fun j ↦ (LinearMap.exact_iff.1 (h j))]

/-- The map `⨁ⱼ (Aⱼ × Bⱼ) ⟶ (⨁ⱼ Aⱼ) × (⨁ⱼ Bⱼ)`. -/
private def splitSum :
    (⨁ j, A j × B j) →ₗ[k] (⨁ j, A j) × (⨁ j, B j) :=
  (DirectSum.lmap fun j ↦ LinearMap.fst k (A j) (B j)).prod
    (DirectSum.lmap fun j ↦ LinearMap.snd k (A j) (B j))

private lemma bijective_splitSum : Function.Bijective (splitSum (k := k) (A := A) (B := B)) := by
  constructor
  · intro x y hxy
    have h₁ : DirectSum.lmap (fun j ↦ LinearMap.fst k (A j) (B j)) x =
        DirectSum.lmap (fun j ↦ LinearMap.fst k (A j) (B j)) y := congrArg Prod.fst hxy
    have h₂ : DirectSum.lmap (fun j ↦ LinearMap.snd k (A j) (B j)) x =
        DirectSum.lmap (fun j ↦ LinearMap.snd k (A j) (B j)) y := congrArg Prod.snd hxy
    ext j : 1
    have h₁j := DFunLike.congr_fun h₁ j
    have h₂j := DFunLike.congr_fun h₂ j
    rw [DirectSum.lmap_apply, DirectSum.lmap_apply] at h₁j h₂j
    exact Prod.ext h₁j h₂j
  · rintro ⟨y, z⟩
    refine ⟨DirectSum.lmap (fun j ↦ LinearMap.inl k (A j) (B j)) y +
      DirectSum.lmap (fun j ↦ LinearMap.inr k (A j) (B j)) z, ?_⟩
    refine Prod.ext ?_ ?_ <;> ext j : 1 <;> simp [splitSum]

/-- The pair of maps `⨁ⱼ (Aⱼ × Bⱼ) ⟶ P × Q` given by maps `⨁ⱼ Aⱼ ⟶ P` and `⨁ⱼ Bⱼ ⟶ Q`. -/
private def pairMap {P Q : Type w} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    (φ : (⨁ j, A j) →ₗ[k] P) (ψ : (⨁ j, B j) →ₗ[k] Q) : (⨁ j, A j × B j) →ₗ[k] P × Q :=
  φ.prodMap ψ ∘ₗ splitSum

private lemma surjective_pairMap {P Q : Type w} [AddCommGroup P] [Module k P] [AddCommGroup Q]
    [Module k Q] {φ : (⨁ j, A j) →ₗ[k] P} {ψ : (⨁ j, B j) →ₗ[k] Q} (hφ : Function.Surjective φ)
    (hψ : Function.Surjective ψ) : Function.Surjective (pairMap φ ψ) := by
  rw [pairMap, LinearMap.coe_comp]
  exact (Function.Surjective.prodMap hφ hψ).comp bijective_splitSum.2

private lemma bijective_pairMap {P Q : Type w} [AddCommGroup P] [Module k P] [AddCommGroup Q]
    [Module k Q] {φ : (⨁ j, A j) →ₗ[k] P} {ψ : (⨁ j, B j) →ₗ[k] Q} (hφ : Function.Bijective φ)
    (hψ : Function.Bijective ψ) : Function.Bijective (pairMap φ ψ) := by
  rw [pairMap, LinearMap.coe_comp]
  exact (Function.Bijective.prodMap hφ hψ).comp bijective_splitSum

private lemma pairMap_lof [DecidableEq J] {P Q : Type w} [AddCommGroup P] [Module k P]
    [AddCommGroup Q] [Module k Q] (φ : (⨁ j, A j) →ₗ[k] P) (ψ : (⨁ j, B j) →ₗ[k] Q) (j : J)
    (y : A j) (z : B j) :
    pairMap φ ψ (DirectSum.lof k J (fun j ↦ A j × B j) j (y, z)) =
      (φ (DirectSum.lof k J A j y), ψ (DirectSum.lof k J B j z)) := by
  simp [pairMap, splitSum]

end LinearAlgebra

/-! ### The Mayer–Vietoris sequence as exact sequences of modules -/

section MayerVietoris

variable (k) {X : TopCat.{w}} (U V : Set X)

/-- The restrictions `Hᵠ(X) ⟶ Hᵠ(U) × Hᵠ(V)`. -/
private abbrev mvRes (q : ℕ) :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q →ₗ[k]
      (of U).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q ×
        (of V).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q :=
  (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) q).hom.prod
    (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) q).hom

/-- The difference of the restrictions `Hᵠ(U) × Hᵠ(V) ⟶ Hᵠ(U ∩ V)`. -/
private abbrev mvDiff (q : ℕ) :
    (of U).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q ×
        (of V).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q →ₗ[k]
      (of ↥(U ∩ V)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q :=
  (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_left))
      q).hom.coprod
    (-(TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion Set.inter_subset_right))
      q).hom)

/-- Under the identification of the biproduct with the product, the first map of the
Mayer–Vietoris sequence is `mvRes`. -/
private lemma biprodIsoProd_toBiprod (q : ℕ)
    (x : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    (ModuleCat.biprodIsoProd _ _).toLinearEquiv
      (singularCohomologyMayerVietorisToBiprod _ k _ U V q x) = mvRes k U V q x := by
  change (ModuleCat.biprodIsoProd _ _).hom _ = _
  rw [ModuleCat.biprodIsoProd_hom_apply]
  refine Prod.ext ?_ ?_
  · exact (ConcreteCategory.comp_apply _ _ x).symm.trans
      (by rw [singularCohomologyMayerVietorisToBiprod_fst]; rfl)
  · exact (ConcreteCategory.comp_apply _ _ x).symm.trans
      (by rw [singularCohomologyMayerVietorisToBiprod_snd]; rfl)

/-- Under the identification of the biproduct with the product, the second map of the
Mayer–Vietoris sequence is `mvDiff`. -/
private lemma fromBiprod_apply (q : ℕ)
    (x : ↑((of U).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q ⊞
      (of V).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)) :
    singularCohomologyMayerVietorisFromBiprod _ k _ U V q x =
      mvDiff k U V q ((ModuleCat.biprodIsoProd _ _).toLinearEquiv x) := by
  conv_lhs => rw [biprod_apply_eq x]
  change _ = mvDiff k U V q ((ModuleCat.biprodIsoProd _ _).hom x)
  rw [map_add, ← ConcreteCategory.comp_apply biprod.inl,
    ← ConcreteCategory.comp_apply biprod.inr, inl_singularCohomologyMayerVietorisFromBiprod,
    inr_singularCohomologyMayerVietorisFromBiprod, ModuleCat.biprodIsoProd_hom_apply]
  rfl

variable {U V} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- The Mayer–Vietoris connecting morphism `Hᵠ(U ∩ V) ⟶ Hᵠ⁺¹(X)`. -/
private abbrev mvδ (q : ℕ) :
    (of ↥(U ∩ V)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q →ₗ[k]
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (q + 1) :=
  (singularCohomologyMayerVietorisδ _ k _ hU hV hUV q (q + 1)).hom

include hU hV hUV in
private lemma exact_mvRes_mvDiff (q : ℕ) : Function.Exact (mvRes k U V q) (mvDiff k U V q) :=
  function_exact_of_linearEquiv (singularCohomologyMayerVietoris_exact₂ _ k _ hU hV hUV q) _ _
    (LinearEquiv.refl k _) (ModuleCat.biprodIsoProd _ _).toLinearEquiv (LinearEquiv.refl k _)
    (biprodIsoProd_toBiprod k U V q) (fromBiprod_apply k U V q)

private lemma exact_mvDiff_mvδ (q : ℕ) :
    Function.Exact (mvDiff k U V q) (mvδ k hU hV hUV q) :=
  function_exact_of_linearEquiv (singularCohomologyMayerVietoris_exact₃ _ k _ hU hV hUV q (q + 1))
    _ _ (ModuleCat.biprodIsoProd _ _).toLinearEquiv (LinearEquiv.refl k _) (LinearEquiv.refl k _)
    (fromBiprod_apply k U V q) (fun x ↦ rfl)

private lemma exact_mvδ_mvRes (q : ℕ) :
    Function.Exact (mvδ k hU hV hUV q) (mvRes k U V (q + 1)) :=
  function_exact_of_linearEquiv (singularCohomologyMayerVietoris_exact₁ _ k _ hU hV hUV q (q + 1))
    _ _ (LinearEquiv.refl k _) (LinearEquiv.refl k _) (ModuleCat.biprodIsoProd _ _).toLinearEquiv
    (fun x ↦ rfl) (biprodIsoProd_toBiprod k U V (q + 1))

include hU hV hUV in
private lemma injective_mvRes_zero : Function.Injective (mvRes k U V 0) := by
  have := mono_singularCohomologyMayerVietorisToBiprod_zero (𝟙_ (ModuleCat.{w} k)) k
    (𝟙_ (ModuleCat.{w} k)) hU hV hUV
  have hinj := (ModuleCat.mono_iff_injective _).1 this
  intro x y hxy
  apply hinj
  apply (ModuleCat.biprodIsoProd _ _).toLinearEquiv.injective
  rw [biprodIsoProd_toBiprod, biprodIsoProd_toBiprod]
  exact hxy

end MayerVietoris

/-! ### The gluing step -/

section Gluing

variable {E B : TopCat.{w}} (p : E ⟶ B) {ι : ℕ → Type w} [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- The indices `(d, q)` with `d + q = n` and `i : ι d` of the summands of the source of a
Leray–Hirsch map in degree `n`. -/
private abbrev Idx (ι : ℕ → Type w) (n : ℕ) : Type w :=
  Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1

/-- The index `(d, q + 1)` in degree `l + 1` of the index `(d, q)` in degree `l`. -/
private abbrev Idx.succ {l : ℕ} (j : Idx ι l) : Idx ι (l + 1) :=
  ⟨⟨(j.1.1.1, j.1.1.2 + 1), by have := j.1.2; omega⟩, j.2⟩

omit [∀ d, DecidableEq (ι d)] in
private lemma Idx.succ_injective (l : ℕ) : Function.Injective (Idx.succ (ι := ι) (l := l)) := by
  rintro ⟨⟨⟨d, q⟩, h⟩, i⟩ ⟨⟨⟨d', q'⟩, h'⟩, i'⟩ hj
  simp only [Sigma.mk.inj_iff, Subtype.mk.injEq, Prod.mk.injEq, add_left_inj] at hj
  obtain ⟨⟨rfl, rfl⟩, hi⟩ := hj
  simp only [heq_eq_eq] at hi
  subst hi
  rfl

variable (B) in
/-- The reindexing `⨁_{(d, q)} H^{q+1}(B) ⟶ ⨁_{(d, q')} H^{q'}(B)` from degree `l` to degree
`l + 1` along `Idx.succ`, which misses exactly the summands with `q' = 0`. -/
private abbrev reindex (ι : ℕ → Type w) [∀ d, DecidableEq (ι d)] (l : ℕ) :
    (⨁ j : Idx ι l,
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (j.1.1.2 + 1)) →ₗ[k]
      ⨁ j : Idx ι (l + 1),
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2 :=
  DirectSum.toModule k _ _ fun j ↦ DirectSum.lof k (Idx ι (l + 1))
    (fun j ↦ B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
    (Idx.succ j)

private lemma reindex_apply_succ (l : ℕ) (x : ⨁ j : Idx ι l,
    B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (j.1.1.2 + 1))
    (j : Idx ι l) : reindex B ι l x (Idx.succ j) = x j := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j' y =>
    rw [← DirectSum.lof_eq_of k, reindex, DirectSum.toModule_lof]
    by_cases hj : j' = j
    · subst hj
      simp only [DirectSum.lof_apply]
    · rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj),
        DirectSum.of_eq_of_ne _ _ _ ((Idx.succ_injective l).ne hj).symm]
  | add x y hx hy => simp [hx, hy]

private lemma reindex_apply_of_eq_zero (l : ℕ) (x : ⨁ j : Idx ι l,
    B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (j.1.1.2 + 1))
    (j : Idx ι (l + 1)) (hj : j.1.1.2 = 0) : reindex B ι l x j = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j' y =>
    rw [← DirectSum.lof_eq_of k, reindex, DirectSum.toModule_lof, DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne]
    rintro rfl
    simp at hj
  | add x y hx hy => simp [hx, hy]

private lemma reindex_injective (l : ℕ) : Function.Injective (reindex (k := k) B ι l) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  ext j : 1
  rw [← reindex_apply_succ, hx, DirectSum.zero_apply, DirectSum.zero_apply]

/-- An element of the source in degree `l + 1` whose summands with `q = 0` vanish is reindexed from
degree `l`. -/
private lemma reindex_comapDomain (l : ℕ) (x : ⨁ j : Idx ι (l + 1),
    B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
    (hx : ∀ j : Idx ι (l + 1), j.1.1.2 = 0 → x j = 0) :
    reindex B ι l (DFinsupp.comapDomain Idx.succ (Idx.succ_injective l) x) = x := by
  ext ⟨⟨⟨d, q⟩, h⟩, i⟩ : 1
  cases q with
  | zero => rw [reindex_apply_of_eq_zero _ _ _ rfl, hx _ rfl]
  | succ q =>
    exact (reindex_apply_succ l _ ⟨⟨(d, q), by omega⟩, i⟩).trans
      (DFinsupp.comapDomain_apply _ _ _ _)

/-- The Leray–Hirsch map over a smaller subset `S ⊆ T` of `B` sends the restriction of a class to
the restriction of its image under the Leray–Hirsch map over `T`. -/
private lemma lerayHirschRestrict_lof_inclusion {S T : Set B} (hST : S ⊆ T) (m d q : ℕ)
    (h : d + q = m) (i : ι d)
    (a : (of T).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirschRestrict p e S m (DirectSum.lof k (Idx ι m)
        (fun j ↦ (of S).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
          j.1.1.2) ⟨⟨(d, q), h⟩, i⟩
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion hST)) q a)) =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion (Set.preimage_mono hST))) m
        (lerayHirschRestrict p e T m (DirectSum.lof k (Idx ι m)
          (fun j ↦ (of T).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
            j.1.1.2) ⟨⟨(d, q), h⟩, i⟩ a)) :=
  lerayHirsch_lof_naturality _ _ (by ext; rfl) (fun d i ↦ by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp]
    rfl) d q h i a

/-- The Leray–Hirsch map over a subset `S` of `B` sends the restriction of a class of `B` to the
restriction of its image under the Leray–Hirsch map of `p`. -/
private lemma lerayHirschRestrict_lof_subtypeVal (S : Set B) (m d q : ℕ) (h : d + q = m)
    (i : ι d) (a : B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirschRestrict p e S m (DirectSum.lof k (Idx ι m)
        (fun j ↦ (of S).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
          j.1.1.2) ⟨⟨(d, q), h⟩, i⟩
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal S)) q a)) =
      TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (p ⁻¹' S))) m
        (lerayHirsch p m e (DirectSum.lof k (Idx ι m)
          (fun j ↦ B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
            j.1.1.2) ⟨⟨(d, q), h⟩, i⟩ a)) :=
  lerayHirsch_lof_naturality _ _ (by ext; rfl) (fun _ _ ↦ rfl) d q h i a

variable {U V : Set B}

/-- The difference of the restrictions `Hᵐ(p⁻¹ U) × Hᵐ(p⁻¹ V) ⟶ Hᵐ(p⁻¹ (U ∩ V))`. -/
private abbrev mvDiffPre (m : ℕ) :
    (of ↥(p ⁻¹' U)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) m ×
        (of ↥(p ⁻¹' V)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) m →ₗ[k]
      (of ↥(p ⁻¹' (U ∩ V))).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
        m :=
  (TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion
      (Set.preimage_mono (f := p) (Set.inter_subset_left (s := U) (t := V))))) m).hom.coprod
    (-(TopCat.singularCohomologyMap (ofHom (ContinuousMap.inclusion
      (Set.preimage_mono (f := p) (Set.inter_subset_right (s := U) (t := V))))) m).hom)

/-- The Leray–Hirsch maps commute with the differences of restrictions to `U ∩ V`. -/
private lemma mvDiffPre_comp_pairMap (m : ℕ) :
    mvDiffPre p m ∘ₗ pairMap (lerayHirschRestrict p e U m) (lerayHirschRestrict p e V m) =
      lerayHirschRestrict p e (U ∩ V) m ∘ₗ
        DirectSum.lmap fun j : Idx ι m ↦ mvDiff k U V j.1.1.2 := by
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨d, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun ⟨y, z⟩ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    pairMap_lof, DirectSum.lmap_lof, LinearMap.coprod_apply, LinearMap.coprod_apply,
    LinearMap.neg_apply, LinearMap.neg_apply]
  dsimp only
  rw [map_add, map_neg, map_add, map_neg, lerayHirschRestrict_lof_inclusion,
    lerayHirschRestrict_lof_inclusion]

/-- The Leray–Hirsch maps commute with the restrictions to `U` and `V`. -/
private lemma mvRes_comp_lerayHirsch (m : ℕ) :
    mvRes k (p ⁻¹' U) (p ⁻¹' V) m ∘ₗ lerayHirsch p m e =
      pairMap (lerayHirschRestrict p e U m) (lerayHirschRestrict p e V m) ∘ₗ
        DirectSum.lmap fun j : Idx ι m ↦ mvRes k U V j.1.1.2 := by
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨d, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    DirectSum.lmap_lof, LinearMap.prod_apply, LinearMap.prod_apply, Function.prod, Function.prod,
    pairMap_lof, lerayHirschRestrict_lof_subtypeVal, lerayHirschRestrict_lof_subtypeVal]

variable (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

include hUV in
private lemma preimage_union_preimage_eq_univ : p ⁻¹' U ∪ p ⁻¹' V = Set.univ := by
  rw [← Set.preimage_union, hUV, Set.preimage_univ]

/-- The Mayer–Vietoris connecting morphism `Hˡ(p⁻¹ (U ∩ V)) ⟶ Hˡ⁺¹(E)` of the cover
`{p⁻¹ U, p⁻¹ V}` of `E`. -/
private abbrev mvδPre (l : ℕ) :
    (of ↥(p ⁻¹' (U ∩ V))).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
        l →ₗ[k]
      E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (l + 1) :=
  mvδ k (hU.preimage p.hom.continuous) (hV.preimage p.hom.continuous)
    (preimage_union_preimage_eq_univ p hUV) l

/-- The Leray–Hirsch maps commute with the Mayer–Vietoris connecting morphisms:
`δ (p^* a ⌣ e|) = δ (p^* a) ⌣ e = p^* (δ a) ⌣ e`. -/
private lemma mvδPre_comp_lerayHirschRestrict (l : ℕ) :
    mvδPre p hU hV hUV l ∘ₗ lerayHirschRestrict p e (U ∩ V) l =
      lerayHirsch p (l + 1) e ∘ₗ reindex B ι l ∘ₗ
        DirectSum.lmap fun j : Idx ι l ↦ mvδ k hU hV hUV j.1.1.2 := by
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨d, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, DirectSum.lmap_lof, reindex, DirectSum.toModule_lof, lerayHirsch_lof,
    lerayHirsch_lof]
  have hδ := ConcreteCategory.congr_hom (singularCohomologyMayerVietorisδ_naturality
    (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) (hU.preimage p.hom.continuous)
    (hV.preimage p.hom.continuous) (preimage_union_preimage_eq_univ p hUV) hU hV hUV p
    (Set.mapsTo_preimage p U) (Set.mapsTo_preimage p V) q (q + 1)) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hδ
  refine Eq.trans ?_ (congrArg (fun x ↦ E.singularCup k (λ_ _).inv (λ_ _).hom (q + 1) d (l + 1)
    (show q + 1 + d = l + 1 by omega) x (e d i)) hδ).symm
  exact singularCohomologyMayerVietorisδ_singularCup (p := q) (q := d) (n := l) (p' := q + 1)
    (m := l + 1) k _ _ _ _ _ (by omega) rfl rfl (by omega) _ _

include hU hV hUV in
/-- The source rows: exactness at `⨁ Hᵠ(B)` of the reindexed connecting morphisms followed by the
restrictions. A class all of whose restrictions vanish has vanishing summands with `q = 0`, and its
other summands come from `U ∩ V`. -/
private lemma exact_reindex_lmap_mvRes (l : ℕ) :
    Function.Exact (reindex B ι l ∘ₗ DirectSum.lmap fun j : Idx ι l ↦ mvδ k hU hV hUV j.1.1.2)
      (DirectSum.lmap fun j : Idx ι (l + 1) ↦ mvRes k U V j.1.1.2) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ fun x hx ↦ ?_
  · refine DirectSum.linearMap_ext k fun j ↦ LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.lmap_lof,
      reindex, DirectSum.toModule_lof, DirectSum.lmap_lof,
      (exact_mvδ_mvRes k hU hV hUV j.1.1.2).apply_apply_eq_zero, map_zero]
    rfl
  · have hx' (j : Idx ι (l + 1)) : mvRes k U V j.1.1.2 (x j) = 0 := by
      have := DFunLike.congr_fun (LinearMap.mem_ker.1 hx) j
      rwa [DirectSum.lmap_apply, DirectSum.zero_apply] at this
    have hzero (j : Idx ι (l + 1)) (hj : j.1.1.2 = 0) : x j = 0 := by
      obtain ⟨⟨⟨d, q⟩, h⟩, i⟩ := j
      obtain rfl : q = 0 := hj
      exact injective_mvRes_zero k hU hV hUV
        ((hx' ⟨⟨(d, 0), h⟩, i⟩).trans (map_zero (mvRes k U V 0)).symm)
    have hy : DFinsupp.comapDomain Idx.succ (Idx.succ_injective l) x ∈
        LinearMap.range (DirectSum.lmap fun j : Idx ι l ↦ mvδ k hU hV hUV j.1.1.2) := by
      rw [DirectSum.range_lmap, Submodule.mem_comap, Submodule.mem_pi]
      intro j _
      rw [DirectSum.coeFnLinearMap_apply, DFinsupp.comapDomain_apply]
      exact (exact_mvδ_mvRes k hU hV hUV j.1.1.2 (x (Idx.succ j))).1 (hx' (Idx.succ j))
    obtain ⟨w, hw⟩ := hy
    exact ⟨w, by rw [LinearMap.comp_apply, hw, reindex_comapDomain _ _ hzero]⟩

include hU hV hUV in
/-- The gluing step in a positive degree `l + 1`, by the five lemma. -/
private lemma bijective_lerayHirsch_succ (l : ℕ)
    (hU₁ : Function.Surjective (lerayHirschRestrict p e U l))
    (hV₁ : Function.Surjective (lerayHirschRestrict p e V l))
    (hUV₁ : Function.Bijective (lerayHirschRestrict p e (U ∩ V) l))
    (hU₂ : Function.Bijective (lerayHirschRestrict p e U (l + 1)))
    (hV₂ : Function.Bijective (lerayHirschRestrict p e V (l + 1)))
    (hUV₂ : Function.Injective (lerayHirschRestrict p e (U ∩ V) (l + 1))) :
    Function.Bijective (lerayHirsch p (l + 1) e) := by
  have hU' := hU.preimage p.hom.continuous
  have hV' := hV.preimage p.hom.continuous
  have hUV' := preimage_union_preimage_eq_univ p hUV
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (DirectSum.lmap fun j : Idx ι l ↦ mvDiff k U V j.1.1.2)
    (reindex B ι l ∘ₗ DirectSum.lmap fun j : Idx ι l ↦ mvδ k hU hV hUV j.1.1.2)
    (DirectSum.lmap fun j : Idx ι (l + 1) ↦ mvRes k U V j.1.1.2)
    (DirectSum.lmap fun j : Idx ι (l + 1) ↦ mvDiff k U V j.1.1.2)
    (mvDiffPre p l) (mvδPre p hU hV hUV l) (mvRes k (p ⁻¹' U) (p ⁻¹' V) (l + 1))
    (mvDiffPre p (l + 1))
    (pairMap (lerayHirschRestrict p e U l) (lerayHirschRestrict p e V l))
    (lerayHirschRestrict p e (U ∩ V) l) (lerayHirsch p (l + 1) e)
    (pairMap (lerayHirschRestrict p e U (l + 1)) (lerayHirschRestrict p e V (l + 1)))
    (lerayHirschRestrict p e (U ∩ V) (l + 1))
    (mvDiffPre_comp_pairMap p e l) (mvδPre_comp_lerayHirschRestrict p e hU hV hUV l)
    (mvRes_comp_lerayHirsch p e (l + 1)) (mvDiffPre_comp_pairMap p e (l + 1))
    ((reindex_injective l).comp_exact_iff_exact.2
      (exact_lmap _ _ fun j ↦ exact_mvDiff_mvδ k hU hV hUV _))
    (exact_reindex_lmap_mvRes hU hV hUV l)
    (exact_lmap _ _ fun j ↦ exact_mvRes_mvDiff k hU hV hUV _)
    (exact_mvDiff_mvδ k hU' hV' hUV' l) (exact_mvδ_mvRes k hU' hV' hUV' l)
    (exact_mvRes_mvDiff k hU' hV' hUV' (l + 1))
    (surjective_pairMap hU₁ hV₁) hUV₁ (bijective_pairMap hU₂ hV₂) hUV₂

include hU hV hUV in
/-- The gluing step in degree `0`, by the four lemmas. -/
private lemma bijective_lerayHirsch_zero
    (hU₀ : Function.Bijective (lerayHirschRestrict p e U 0))
    (hV₀ : Function.Bijective (lerayHirschRestrict p e V 0))
    (hUV₀ : Function.Injective (lerayHirschRestrict p e (U ∩ V) 0)) :
    Function.Bijective (lerayHirsch p 0 e) := by
  have hU' := hU.preimage p.hom.continuous
  have hV' := hV.preimage p.hom.continuous
  have hUV' := preimage_union_preimage_eq_univ p hUV
  have hres : Function.Injective (DirectSum.lmap fun j : Idx ι 0 ↦ mvRes k U V j.1.1.2) :=
    (DirectSum.lmap_injective _).2 fun ⟨⟨⟨d, q⟩, h⟩, i⟩ ↦ by
      obtain rfl : q = 0 := by omega
      exact injective_mvRes_zero k hU hV hUV
  have hc := mvRes_comp_lerayHirsch (ι := ι) p e (U := U) (V := V) 0
  refine ⟨fun x y hxy ↦ hres ((bijective_pairMap hU₀ hV₀).1 ?_), ?_⟩
  · rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← hc, LinearMap.comp_apply,
      LinearMap.comp_apply, hxy]
  · exact LinearMap.surjective_of_surjective_of_surjective_of_injective
      (0 : PUnit.{w + 1} →ₗ[k] _) (DirectSum.lmap fun j : Idx ι 0 ↦ mvRes k U V j.1.1.2)
      (DirectSum.lmap fun j : Idx ι 0 ↦ mvDiff k U V j.1.1.2)
      (0 : PUnit.{w + 1} →ₗ[k] _) (mvRes k (p ⁻¹' U) (p ⁻¹' V) 0) (mvDiffPre p 0)
      0 (lerayHirsch p 0 e)
      (pairMap (lerayHirschRestrict p e U 0) (lerayHirschRestrict p e V 0))
      (lerayHirschRestrict p e (U ∩ V) 0) (by ext; simp) hc (mvDiffPre_comp_pairMap p e 0)
      (exact_lmap _ _ fun j ↦ exact_mvRes_mvDiff k hU hV hUV _)
      ((LinearMap.exact_zero_iff_injective _ _).2 (injective_mvRes_zero k hU' hV' hUV'))
      (exact_mvRes_mvDiff k hU' hV' hUV' 0) (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩)
      (bijective_pairMap hU₀ hV₀).2 hUV₀

end Gluing

/-! ### The gluing step over a union -/

section Union

variable {E B : TopCat.{w}} (p : E ⟶ B) {ι : ℕ → Type w} [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- **The Mayer–Vietoris gluing step for the Leray–Hirsch map, for an open cover of the base.**
Let `U` and `V` be open subsets of `B` with `U ∪ V = B`. If the Leray–Hirsch maps of the
restrictions of `p` over `U`, `V` and `U ∩ V`, with the restricted classes, are bijective in
degrees `m ≤ n`, then so is the Leray–Hirsch map of `p`. -/
theorem bijective_lerayHirsch_of_union_eq_univ {U V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e U m))
    (hV' : ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e V m))
    (hUV' : ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e (U ∩ V) m)) :
    ∀ m ≤ n, Function.Bijective (lerayHirsch p m e) := by
  rintro (_ | l) hm
  · exact bijective_lerayHirsch_zero p e hU hV hUV (hU' 0 hm) (hV' 0 hm) (hUV' 0 hm).1
  · exact bijective_lerayHirsch_succ p e hU hV hUV l (hU' l (by omega)).2 (hV' l (by omega)).2
      (hUV' l (by omega)) (hU' _ hm) (hV' _ hm) (hUV' _ hm).1

/-- Restricting first over `W` and then over the preimage of `S ⊆ W` in `W` is restricting over
`S`, up to homeomorphisms over homeomorphisms; so the two Leray–Hirsch maps are bijective
together. -/
private lemma bijective_lerayHirschRestrict_restrict_iff {W S : Set B} (hSW : S ⊆ W) (m : ℕ) :
    Function.Bijective (lerayHirschRestrict (ofHom (p.hom.restrictPreimage W))
      (fun d i ↦ TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (p ⁻¹' W))) d
        (e d i)) ((↑) ⁻¹' S : Set ↥W) m) ↔
      Function.Bijective (lerayHirschRestrict p e S m) := by
  let f : of ↥((ofHom (p.hom.restrictPreimage W)) ⁻¹' ((↑) ⁻¹' S : Set ↥W)) ⟶ of ↥(p ⁻¹' S) :=
    ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let f' : of ↥(p ⁻¹' S) ⟶ of ↥((ofHom (p.hom.restrictPreimage W)) ⁻¹' ((↑) ⁻¹' S : Set ↥W)) :=
    ofHom ⟨fun y ↦ ⟨⟨y.1, hSW y.2⟩, y.2⟩, (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  let g : of ↥((↑) ⁻¹' S : Set ↥W) ⟶ of ↥S :=
    ofHom ⟨fun x ↦ ⟨x.1, x.2⟩, (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let g' : of ↥S ⟶ of ↥((↑) ⁻¹' S : Set ↥W) :=
    ofHom ⟨fun y ↦ ⟨⟨y.1, hSW y.2⟩, y.2⟩, (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  have : IsIso f := ⟨f', by ext; rfl, by ext; rfl⟩
  have : IsIso g := ⟨g', by ext; rfl, by ext; rfl⟩
  exact bijective_lerayHirsch_iff_of_isIso f g (by ext; rfl) fun d i ↦ by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_comp]
    rfl

/-- **The Mayer–Vietoris gluing step for the Leray–Hirsch map.** Let `U` and `V` be open subsets of
`B`. If the Leray–Hirsch maps of the restrictions of `p` over `U`, `V` and `U ∩ V`, with the
restricted classes, are bijective in degrees `m ≤ n`, then so is the Leray–Hirsch map of the
restriction of `p` over `U ∪ V`. -/
theorem bijective_lerayHirsch_union {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (hU' : ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e U m))
    (hV' : ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e V m))
    (hUV' : ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e (U ∩ V) m)) :
    ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p e (U ∪ V) m) :=
  bijective_lerayHirsch_of_union_eq_univ (ofHom (p.hom.restrictPreimage (U ∪ V)))
    (fun d i ↦ TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (p ⁻¹' (U ∪ V)))) d
      (e d i))
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    (by rw [← Set.preimage_union, Subtype.coe_preimage_self]) n
    (fun m hm ↦ (bijective_lerayHirschRestrict_restrict_iff p e Set.subset_union_left m).2
      (hU' m hm))
    (fun m hm ↦ (bijective_lerayHirschRestrict_restrict_iff p e Set.subset_union_right m).2
      (hV' m hm))
    (fun m hm ↦ (bijective_lerayHirschRestrict_restrict_iff p e
      (Set.inter_subset_left.trans Set.subset_union_left) m).2 (hUV' m hm))

end Union

end TopCat
