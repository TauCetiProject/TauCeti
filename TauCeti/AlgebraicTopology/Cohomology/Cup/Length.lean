/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.Category

/-!
# Cup length and the Lusternik–Schnirelmann category

Let `k` be a commutative ring and write `Hⁿ(X; k)` for the singular cohomology of a space `X` with
coefficients in `k`. The **cup length** `TauCeti.lsCupLength X k : ℕ∞` is the supremum of the
lengths `r` of the nonzero cup products `a₁ ⌣ ⋯ ⌣ a_r` of classes `aᵢ` of positive degree, and `0`
when there is no such product. A cup product of this shape is recorded by the predicate
`TauCeti.IsCupProduct X k r n a`, for `a ∈ Hⁿ(X; k)`.

The cup length bounds the Lusternik–Schnirelmann category from below: if `X` is nonempty, then

`lsCupLength X k + 1 ≤ lsCategoryCount X univ`,

that is, `lsCupLength X k ≤ normalizedLSCategory X`
(`TauCeti.lsCupLength_add_one_le_lsCategoryCount`). The proof is the classical one. If `U` is
open in `X` and its inclusion is nullhomotopic, then every class of positive degree restricts to
zero on `U`, since nullhomotopic maps vanish on positive-degree cohomology, so by the long exact
sequence of the pair `(X, U)` it lifts to `Hᵖ(X, U; k)`
(`TauCeti.exists_singularCohomologyπ_eq_of_nullhomotopic`). The relative cup product
`Hᵖ(X, U; k) × H^q(X, V; k) ⟶ Hᵖ⁺ᑫ(X, U ∪ V; k)` of open sets then shows that a product of `r`
positive-degree classes lifts to `H*(X, U₁ ∪ ⋯ ∪ U_r; k)` for any `r` such open sets
(`TauCeti.IsCupProduct.exists_singularCohomologyπ_iUnion_eq`). If the `Uᵢ` cover `X`, this
relative cohomology vanishes, so the product does: no product of `r` positive-degree classes is
nonzero when `X` has a categorical cover by `r` open sets.

## Main definitions

* `TauCeti.IsCupProduct X k r n a`: `a ∈ Hⁿ(X; k)` is a cup product of `r ≥ 1` classes of positive
  degree, nested to the right.
* `TauCeti.lsCupLength X k`: the cup length of `X` with coefficients in `k`.

## Main results

* `TauCeti.le_lsCupLength` and `TauCeti.lsCupLength_le_iff`: the cup length is the least upper
  bound of the lengths of nonzero cup products.
* `TauCeti.IsCupProduct.singularCohomologyMap`: pulling back a cup product along a continuous map
  gives a cup product of the same length, and so `TauCeti.lsCupLength_le_of_injective`: the cup
  length does not drop along a map inducing injections on cohomology.
* `TauCeti.IsCupProduct.exists_singularCohomologyπ_iUnion_eq`: a product of `r` classes of positive
  degree comes from the cohomology of `X` relative to the union of any `r` open sets with
  nullhomotopic inclusions.
* `TauCeti.lsCupLength_add_one_le_lsCategoryCount` and
  `TauCeti.lsCupLength_le_normalizedLSCategory`: **the cup-length lower bound for the
  Lusternik–Schnirelmann category.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Exercise 2, for the vanishing of `n`-fold products of positive-degree classes on a
  union of `n` contractible open sets.
* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1, for the cup-length
  lower bound.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Set

universe w v u

namespace TauCeti

section Relative

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  {R : C} {k : Type*} [Ring k] [Linear k C] {M : C} {X : TopCat.{w}}

/-- If the inclusion of `U ⊆ X` is nullhomotopic, then every class of positive degree of `X` comes
from the cohomology of `X` relative to `U`: it restricts to zero on `U`. -/
theorem exists_singularCohomologyπ_eq_of_nullhomotopic {U : Set X}
    (hU : (ContinuousMap.subtypeVal U).Nullhomotopic) {n : ℕ} (hn : n ≠ 0)
    (a : X.singularCohomology R k M n) :
    ∃ b, (TopPair.ofSubset U).singularCohomologyπ R k M n b = a := by
  have hex := (TopPair.ofSubset U).singularCohomology_exact_space R k M n
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at hex
  -- The restriction to `U` is induced by the inclusion `U ⟶ X`, which is nullhomotopic.
  have h0 : TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (TopPair.ofSubset U).map n = 0 :=
    TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic hU hn
  -- `h0` is stated on the ambient space `(TopPair.ofSubset U).fst`, which is `X` only up to
  -- unfolding, so the zero map is evaluated at `a` by `LinearMap.zero_apply` rather than by `rw`.
  exact hex (LinearMap.mem_ker.2 ((congrArg (fun g ↦ g.hom a) h0).trans (LinearMap.zero_apply a)))

/-- For `B ⊆ A`, a class of `X` coming from the cohomology of `X` relative to `A` also comes from
the cohomology of `X` relative to `B`. -/
theorem exists_singularCohomologyπ_eq_of_subset {A B : Set X} (h : B ⊆ A) {n : ℕ}
    {a : X.singularCohomology R k M n}
    (ha : ∃ b, (TopPair.ofSubset A).singularCohomologyπ R k M n b = a) :
    ∃ b, (TopPair.ofSubset B).singularCohomologyπ R k M n b = a := by
  obtain ⟨b, rfl⟩ := ha
  have hf := TopPair.singularCohomologyπ_naturality (R := R) (k := k) (M := M)
    (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ h hx) n
  -- The ambient map of the map of pairs is the identity of `X`.
  have hid := (congrArg
    (fun g : X ⟶ X ↦ TopCat.singularCohomologyMap (R := R) (k := k) (M := M) g n)
    (TopPair.ofSubsetMap_fst (𝟙 X) fun _ hx ↦ h hx)).trans (TopCat.singularCohomologyMap_id X n)
  exact ⟨_, (ConcreteCategory.congr_hom hf b).symm.trans (ConcreteCategory.congr_hom hid _)⟩

/-- The map from the cohomology of `X` relative to all of `X` to the cohomology of `X` is zero. -/
@[simp]
theorem singularCohomologyπ_ofSubset_univ (n : ℕ) :
    (TopPair.ofSubset (univ : Set X)).singularCohomologyπ R k M n = 0 := by
  -- The inclusion `i` of `univ` has the left inverse `r` on `X`, so it induces an injection on
  -- cohomology, which kills the image of the relative cohomology by exactness.
  let i : (TopPair.ofSubset (univ : Set X)).snd ⟶ X := (TopPair.ofSubset (univ : Set X)).map
  let r : X ⟶ (TopPair.ofSubset (univ : Set X)).snd :=
    TopCat.ofHom ⟨fun x ↦ ⟨x, mem_univ x⟩, by fun_prop⟩
  have hri : r ≫ i = 𝟙 X := by
    ext
    rfl
  have hinj (x : X.singularCohomology R k M n) :
      TopCat.singularCohomologyMap r n (TopCat.singularCohomologyMap i n x) = x := by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hri,
      TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  ext y
  have h0 : TopCat.singularCohomologyMap (R := R) (k := k) (M := M) i n
      ((TopPair.ofSubset (univ : Set X)).singularCohomologyπ R k M n y) = 0 :=
    ConcreteCategory.congr_hom
      ((TopPair.ofSubset (univ : Set X)).singularCohomologyπ_comp_singularCohomologyMap R k M n) y
  rw [← hinj ((TopPair.ofSubset (univ : Set X)).singularCohomologyπ R k M n y), h0, map_zero,
    ModuleCat.hom_zero, LinearMap.zero_apply]
  -- The two zeros live in the cohomology of `X` and of `(TopPair.ofSubset univ).fst`, which is `X`
  -- up to unfolding.
  rfl

end Relative

variable (X : TopCat.{w}) (k : Type w) [CommRing k]

/-- `IsCupProduct X k r n a` says that the class `a ∈ Hⁿ(X; k)` is a cup product
`a₁ ⌣ (a₂ ⌣ ⋯ ⌣ a_r)` of `r ≥ 1` classes `aᵢ` of positive degree, for the cup product of
singular cohomology with coefficients in the commutative ring `k`. -/
inductive IsCupProduct :
    (r n : ℕ) → X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n → Prop
  /-- A single class of positive degree is a cup product of length one. -/
  | single {p : ℕ} (hp : p ≠ 0)
      (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
      IsCupProduct 1 p a
  /-- The cup product of a class of positive degree with a cup product of length `r` is a cup
  product of length `r + 1`. -/
  | cup {p q r : ℕ} (hp : p ≠ 0)
      (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
      {b : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q}
      (hb : IsCupProduct r q b) :
      IsCupProduct (r + 1) (p + q)
        (X.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (ρ_ (𝟙_ (ModuleCat.{w} k))).hom
          p q (p + q) rfl a b)

/-- The **cup length** of `X` with coefficients in the commutative ring `k`: the supremum of the
lengths `r` of the nonzero cup products `a₁ ⌣ ⋯ ⌣ a_r` of classes of positive degree in the
singular cohomology `H*(X; k)`, and `0` if there is no such product. -/
def lsCupLength : ℕ∞ :=
  ⨆ (r : ℕ) (n : ℕ) (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n)
    (_ : IsCupProduct X k r n a) (_ : a ≠ 0), (r : ℕ∞)

variable {X k}

/-- A nonzero cup product of `r` classes of positive degree bounds the cup length below by `r`. -/
theorem le_lsCupLength {r n : ℕ}
    {a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n}
    (h : IsCupProduct X k r n a) (ha : a ≠ 0) : (r : ℕ∞) ≤ lsCupLength X k :=
  le_iSup_of_le r <| le_iSup_of_le n <| le_iSup_of_le a <| le_iSup_of_le h <| le_iSup_of_le ha
    le_rfl

/-- The cup length is at most `m` exactly when every nonzero cup product of classes of positive
degree has length at most `m`. -/
theorem lsCupLength_le_iff {m : ℕ∞} :
    lsCupLength X k ≤ m ↔ ∀ (r n : ℕ)
      (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n),
      IsCupProduct X k r n a → a ≠ 0 → (r : ℕ∞) ≤ m := by
  simp only [lsCupLength, iSup_le_iff]

/-- **Naturality of cup products**: pulling back a cup product of `r` classes of positive degree
along a continuous map gives a cup product of `r` classes of positive degree. -/
theorem IsCupProduct.singularCohomologyMap {Y : TopCat.{w}} (f : X ⟶ Y) {r n : ℕ}
    {a : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n}
    (h : IsCupProduct Y k r n a) :
    IsCupProduct X k r n (TopCat.singularCohomologyMap f n a) := by
  induction h with
  | single hp a => exact .single hp _
  | cup hp a _ ih =>
    rw [← TopCat.singularCup_naturality]
    exact .cup hp _ ih

/-- The cup length does not drop along a continuous map `f : X ⟶ Y` inducing injections on
cohomology in every degree: `lsCupLength Y k ≤ lsCupLength X k`. -/
theorem lsCupLength_le_of_injective {Y : TopCat.{w}} (f : X ⟶ Y)
    (hf : ∀ n, Function.Injective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k))
      (k := k) (M := 𝟙_ (ModuleCat.{w} k)) f n)) :
    lsCupLength Y k ≤ lsCupLength X k :=
  lsCupLength_le_iff.2 fun _ n _ h ha ↦
    le_lsCupLength (h.singularCohomologyMap f) fun h0 ↦ ha (hf n (h0.trans (map_zero _).symm))

/-- **Products of classes vanishing on open sets.** Let `U₁, …, U_r` be open subsets of `X` whose
inclusions are nullhomotopic. Then every cup product of `r` classes of positive degree comes from
the cohomology of `X` relative to `U₁ ∪ ⋯ ∪ U_r`. -/
theorem IsCupProduct.exists_singularCohomologyπ_iUnion_eq {r n : ℕ}
    {a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n}
    (h : IsCupProduct X k r n a) (U : Fin r → Set X) (hUo : ∀ i, IsOpen (U i))
    (hU : ∀ i, (ContinuousMap.subtypeVal (U i)).Nullhomotopic) :
    ∃ b, (TopPair.ofSubset (⋃ i, U i)).singularCohomologyπ
      (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n b = a := by
  induction h with
  | single hp a =>
    exact exists_singularCohomologyπ_eq_of_subset
      (iUnion_subset fun i ↦ by rw [Subsingleton.elim i 0])
      (exists_singularCohomologyπ_eq_of_nullhomotopic (hU 0) hp a)
  | @cup p q r hp a b _ ih =>
    -- Lift `a` to `(X, U₀)` and `b` to `(X, U₁ ∪ ⋯ ∪ U_r)`, and take their relative cup product.
    obtain ⟨a', rfl⟩ := exists_singularCohomologyπ_eq_of_nullhomotopic (hU 0) hp a
    obtain ⟨b', rfl⟩ := ih (fun i ↦ U i.succ) (fun i ↦ hUo i.succ) fun i ↦ hU i.succ
    have hV : IsOpen (⋃ i : Fin r, U i.succ) := isOpen_iUnion fun i ↦ hUo i.succ
    have hsub : ⋃ i, U i ⊆ U 0 ∪ ⋃ i : Fin r, U i.succ := by
      refine iUnion_subset fun i ↦ ?_
      cases i using Fin.cases with
      | zero => exact subset_union_left
      | succ i => exact (subset_iUnion (fun i : Fin r ↦ U i.succ) i).trans subset_union_right
    exact exists_singularCohomologyπ_eq_of_subset hsub
      ⟨TopCat.singularRelativeCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
        (ρ_ (𝟙_ (ModuleCat.{w} k))).hom _ _ ((hUo 0).preimage continuous_subtype_val)
        (hV.preimage continuous_subtype_val) p q (p + q) rfl a' b',
        TopCat.singularCohomologyπ_singularRelativeCup k _ _ _ _ _ _ p q (p + q) rfl a' b'⟩

/-- A cup product of `r` classes of positive degree vanishes if `X` has a categorical cover by `r`
open sets. -/
theorem IsCupProduct.eq_zero_of_lsCategoricalCover {r n : ℕ}
    {a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n}
    (h : IsCupProduct X k r n a) (c : LSCategoricalCover X univ r) : a = 0 := by
  obtain ⟨a', rfl⟩ := exists_singularCohomologyπ_eq_of_subset c.subset_iUnion
    (h.exists_singularCohomologyπ_iUnion_eq (fun i ↦ c.opens i) (fun i ↦ (c.opens i).isOpen)
      c.nullhomotopic)
  rw [singularCohomologyπ_ofSubset_univ]
  -- The zero morphism sends `a'` to the zero of the cohomology of `(TopPair.ofSubset univ).fst`,
  -- which is the cohomology of `X` up to unfolding.
  rfl

/-- **The cup-length lower bound for the Lusternik–Schnirelmann category.** On a nonempty space
`X`, the cup length of `X` with coefficients in any commutative ring is less than the least number
of open sets with nullhomotopic inclusions covering `X`. -/
theorem lsCupLength_add_one_le_lsCategoryCount [Nonempty X] :
    lsCupLength X k + 1 ≤ lsCategoryCount X univ := by
  induction hm : lsCategoryCount X univ using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    obtain ⟨c⟩ := nonempty_lsCategoricalCover_of_lsCategoryCount_eq hm
    have hm1 : 0 < m := by
      have := (lsCategoryCount_pos (X := X)).2 univ_nonempty
      rw [hm] at this
      exact_mod_cast this
    -- Every nonzero product has fewer than `m` factors: a product of `r ≥ m` factors vanishes,
    -- since padding the categorical cover gives a cover by `r` open sets.
    have hle : lsCupLength X k ≤ (m - 1 : ℕ) := lsCupLength_le_iff.2 fun r n a h ha ↦ by
      by_contra hr
      have hmr : m ≤ r := by
        have : m - 1 < r := by exact_mod_cast not_le.1 hr
        omega
      exact ha (h.eq_zero_of_lsCategoricalCover (c.pad hmr))
    calc lsCupLength X k + 1 ≤ ((m - 1 : ℕ) : ℕ∞) + 1 := by gcongr
      _ = m := by norm_cast; omega

/-- **The cup-length lower bound for the normalized Lusternik–Schnirelmann category**: on a
nonempty space `X`, `lsCupLength X k ≤ normalizedLSCategory X` for every commutative ring `k`. -/
theorem lsCupLength_le_normalizedLSCategory [Nonempty X] :
    lsCupLength X k ≤ normalizedLSCategory X := by
  have h := lsCupLength_add_one_le_lsCategoryCount (X := X) (k := k)
  rw [lsCategoryCount_univ_eq_normalizedLSCategory_add_one] at h
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h

/-- On a nonempty contractible space every cup product of classes of positive degree vanishes:
the cup length is `0`. -/
theorem lsCupLength_of_contractibleSpace [Nonempty X] [ContractibleSpace X] :
    lsCupLength X k = 0 := by
  have h := lsCupLength_le_normalizedLSCategory (X := X) (k := k)
  rwa [normalizedLSCategory_of_contractibleSpace, nonpos_iff_eq_zero] at h

end TauCeti
