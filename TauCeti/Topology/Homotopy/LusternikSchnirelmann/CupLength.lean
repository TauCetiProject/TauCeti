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

For a commutative ring `R`, the cup length `TauCeti.lsCupLength X R : ℕ∞` of a space `X` is the
supremum of the lengths `n` of the nonzero cup products `a₁ ⌣ ⋯ ⌣ aₙ` of classes `aᵢ` of positive
degree in the singular cohomology `H*(X; R)`, the supremum of the empty collection being `0`.
The cohomology and the cup product are the singular ones of
`TauCeti.AlgebraicTopology.Cohomology.Cup.Basic`, for the coefficient category `ModuleCat R`, the
chain and cochain coefficients `R = 𝟙_ (ModuleCat R)`, and the unitors of `ModuleCat R` as the
diagonal of the chain coefficients and the multiplication of the cochain values.

The main result is the classical lower bound for the Lusternik–Schnirelmann category: on a nonempty
space, `lsCupLength X R + 1 ≤ lsCategoryCount X univ`, equivalently
`lsCupLength X R ≤ normalizedLSCategory X`. If `U₁, …, Uₙ` are open sets whose inclusions into `X`
are nullhomotopic, a class `aᵢ` of positive degree restricts to zero on `Uᵢ`, because the
positive-degree cohomology of a point vanishes, so the long exact sequence of the pair lifts it to
`H*(X, Uᵢ)`. The relative cup product of open sets lifts `a₁ ⌣ ⋯ ⌣ aₙ` to `H*(X, U₁ ∪ ⋯ ∪ Uₙ)`,
which vanishes when the `Uᵢ` cover `X`.

## Main definitions

* `TauCeti.IsPositiveDegreeCupProduct X R n x`: the class `x` of `H*(X; R)` is a cup product
  `a₁ ⌣ (a₂ ⌣ ⋯ ⌣ aₙ)` of `n ≥ 1` classes of positive degree.
* `TauCeti.lsCupLength X R`: the cup length of `X` with coefficients in `R`.

## Main results

* `TauCeti.natCast_le_lsCupLength_iff`: for `n ≥ 1`, `n ≤ lsCupLength X R` exactly when some
  product of `n` positive-degree classes is nonzero.
* `TauCeti.lsCupLength_eq_zero_iff`: the cup length vanishes exactly when every class of positive
  degree vanishes.
* `TauCeti.IsPositiveDegreeCupProduct.exists_singularCohomologyπ_eq`: a product of `n` classes of
  positive degree comes from the cohomology of `X` relative to the union of any `n` open sets with
  nullhomotopic inclusions.
* `TauCeti.lsCupLength_add_one_le_lsCategoryCount` and
  `TauCeti.lsCupLength_le_normalizedLSCategory`: the cup-length lower bound for the
  Lusternik–Schnirelmann category.
* `TauCeti.lsCupLength_le_of_injective` and `ContinuousMap.HomotopyEquiv.lsCupLength_eq`:
  monotonicity along maps injective on cohomology, and homotopy invariance.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*,
  Mathematical Surveys and Monographs 103, AMS, 2003, Chapter 1, the cup-length lower bound.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the relative cup product `Hᵏ(X, A) × Hˡ(X, B) ⟶ Hᵏ⁺ˡ(X, A ∪ B)` for open `A` and `B`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Set TopologicalSpace

universe u

namespace TauCeti

variable (X : Type u) [TopologicalSpace X] (R : Type u) [CommRing R]

/-- `IsPositiveDegreeCupProduct X R n x`: the class `x ∈ Hᵈ(X; R)` is a cup product
`a₁ ⌣ (a₂ ⌣ ⋯ ⌣ aₙ)` of `n` classes `aᵢ ∈ H^{pᵢ}(X; R)` of positive degree `pᵢ ≠ 0`, nested to the
right, so that `n ≥ 1` and `d = p₁ + ⋯ + pₙ`. Here `H*(X; R)` is singular cohomology with chain and
cochain coefficients `R = 𝟙_ (ModuleCat R)`, and the cup product uses the unitors of `ModuleCat R`
as diagonal and multiplication. -/
inductive IsPositiveDegreeCupProduct :
    (n : ℕ) → {d : ℕ} →
      (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d → Prop
  /-- A single class of positive degree is a product of length one. -/
  | single {p : ℕ} (hp : p ≠ 0)
      (a : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) p) :
      IsPositiveDegreeCupProduct 1 a
  /-- A class of positive degree cupped with a product of length `n` is a product of length
  `n + 1`. -/
  | cup {n p q d : ℕ} (hp : p ≠ 0) (h : p + q = d)
      (a : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) p)
      {y : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) q}
      (hy : IsPositiveDegreeCupProduct n y) :
      IsPositiveDegreeCupProduct (n + 1)
        ((TopCat.of X).singularCup R (λ_ _).inv (λ_ _).hom p q d h a y)

/-- The **cup length** of a space `X` with coefficients in a commutative ring `R`: the supremum of
the lengths `n` of the nonzero cup products `a₁ ⌣ ⋯ ⌣ aₙ` of classes of positive degree in
`H*(X; R)` (`TauCeti.IsPositiveDegreeCupProduct`). It is `0` when every class of positive degree
vanishes, and `⊤` when there are nonzero such products of every length. -/
def lsCupLength : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ (d : ℕ) (x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R
    (𝟙_ (ModuleCat.{u} R)) d), IsPositiveDegreeCupProduct X R n x ∧ x ≠ 0), (n : ℕ∞)

variable {X R}

namespace IsPositiveDegreeCupProduct

/-- A product of positive-degree classes has at least one factor. -/
theorem pos {n d : ℕ}
    {x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d}
    (hx : IsPositiveDegreeCupProduct X R n x) : 0 < n := by
  cases hx <;> omega

/-- A product of positive-degree classes has positive degree. -/
theorem degree_ne_zero {n d : ℕ}
    {x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d}
    (hx : IsPositiveDegreeCupProduct X R n x) : d ≠ 0 := by
  cases hx <;> omega

/-- The products of length one are exactly the classes of positive degree. -/
@[simp]
theorem one_iff {d : ℕ}
    {x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d} :
    IsPositiveDegreeCupProduct X R 1 x ↔ d ≠ 0 :=
  ⟨degree_ne_zero, (single · x)⟩

/-- If a nonzero class is a product of `n` positive-degree classes, then for every `1 ≤ m ≤ n` some
nonzero class is a product of `m` positive-degree classes: drop leading factors, since a cup product
with a zero factor vanishes. -/
theorem exists_ne_zero_of_le {n d : ℕ}
    {x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d}
    (hx : IsPositiveDegreeCupProduct X R n x) (hx0 : x ≠ 0) {m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ∃ (e : ℕ) (z : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R
      (𝟙_ (ModuleCat.{u} R)) e), IsPositiveDegreeCupProduct X R m z ∧ z ≠ 0 := by
  induction hx with
  | single hp a =>
    obtain rfl : m = 1 := by omega
    exact ⟨_, a, single hp a, hx0⟩
  | @cup n p q d hp h a y hy ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact ih (fun hy0 ↦ hx0 (by rw [hy0, map_zero])) (by omega)
    · obtain rfl : m = n + 1 := by omega
      exact ⟨_, _, cup hp h a hy, hx0⟩

/-- **Naturality**: pulling back a product of positive-degree classes along a continuous map gives
a product of positive-degree classes of the same length. -/
theorem map {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) {n d : ℕ}
    {x : (TopCat.of Y).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d}
    (hx : IsPositiveDegreeCupProduct Y R n x) :
    IsPositiveDegreeCupProduct X R n (TopCat.singularCohomologyMap (TopCat.ofHom f) d x) := by
  induction hx with
  | single hp a => exact single hp _
  | cup hp h a hy ih =>
    rw [← TopCat.singularCup_naturality]
    exact cup hp h _ ih

end IsPositiveDegreeCupProduct

/-- The defining property of the cup length: it bounds the length of every nonzero product of
positive-degree classes. -/
theorem le_lsCupLength {n d : ℕ}
    {x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d}
    (hx : IsPositiveDegreeCupProduct X R n x) (hx0 : x ≠ 0) : (n : ℕ∞) ≤ lsCupLength X R :=
  le_iSup₂_of_le (f := fun (n : ℕ) _ ↦ (n : ℕ∞)) n ⟨d, x, hx, hx0⟩ le_rfl

/-- The cup length is at most `m` exactly when every nonzero product of positive-degree classes
has length at most `m`. -/
theorem lsCupLength_le_iff {m : ℕ∞} :
    lsCupLength X R ≤ m ↔ ∀ (n d : ℕ)
      (x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d),
      IsPositiveDegreeCupProduct X R n x → x ≠ 0 → (n : ℕ∞) ≤ m := by
  refine ⟨fun h n d x hx hx0 ↦ (le_lsCupLength hx hx0).trans h, fun h ↦ iSup₂_le ?_⟩
  rintro n ⟨d, x, hx, hx0⟩
  exact h n d x hx hx0

/-- **Finite-product witnesses**: for `n ≥ 1`, the cup length is at least `n` exactly when some
product of `n` classes of positive degree is nonzero. -/
theorem natCast_le_lsCupLength_iff {n : ℕ} (hn : n ≠ 0) :
    (n : ℕ∞) ≤ lsCupLength X R ↔ ∃ (d : ℕ)
      (x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d),
      IsPositiveDegreeCupProduct X R n x ∧ x ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨d, x, hx, hx0⟩ ↦ le_lsCupLength hx hx0⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  have hlt : (k : ℕ∞) < lsCupLength X R := by
    rw [← ENat.add_one_le_iff (ENat.natCast_ne_top k)]
    exact_mod_cast h
  obtain ⟨m, hm⟩ := lt_iSup_iff.mp hlt
  obtain ⟨⟨d, x, hx, hx0⟩, hkm⟩ := lt_iSup_iff.mp hm |>.imp fun _ h ↦ h
  exact hx.exists_ne_zero_of_le hx0 (by omega) (by exact_mod_cast hkm)

/-- The cup length vanishes exactly when every class of positive degree in `H*(X; R)` vanishes. -/
theorem lsCupLength_eq_zero_iff :
    lsCupLength X R = 0 ↔ ∀ (p : ℕ), p ≠ 0 → ∀
      (a : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) p),
      a = 0 := by
  rw [← not_iff_not, ← ne_eq, ← Order.one_le_iff_ne_zero, ← Nat.cast_one,
    natCast_le_lsCupLength_iff one_ne_zero]
  simp

/-- **Monotonicity**: if a continuous map `f : X → Y` induces injective maps on cohomology in every
positive degree, then the cup length of `Y` is at most that of `X`. -/
theorem lsCupLength_le_of_injective {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    (hf : ∀ d, d ≠ 0 → Function.Injective
      (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{u} R)) (k := R)
        (M := 𝟙_ (ModuleCat.{u} R)) (TopCat.ofHom f) d)) :
    lsCupLength Y R ≤ lsCupLength X R := by
  refine lsCupLength_le_iff.mpr fun n d x hx hx0 ↦ le_lsCupLength (hx.map f) fun h ↦ hx0 ?_
  exact hf d hx.degree_ne_zero (h.trans (map_zero _).symm)

/-- **Homotopy invariance** of the cup length. -/
theorem _root_.ContinuousMap.HomotopyEquiv.lsCupLength_eq {Y : Type u} [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : lsCupLength X R = lsCupLength Y R := by
  -- A homotopy equivalence induces isomorphisms, in particular injections, on cohomology.
  have key {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      (e : ContinuousMap.HomotopyEquiv X Y) (d : ℕ) :
      Function.Injective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{u} R)) (k := R)
        (M := 𝟙_ (ModuleCat.{u} R)) (TopCat.ofHom e.toFun) d) := by
    have := TopCat.isIso_singularCohomologyMap (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
      e.left_inv.some e.right_inv.some (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  exact le_antisymm (lsCupLength_le_of_injective e.invFun fun d _ ↦ key e.symm d)
    (lsCupLength_le_of_injective e.toFun fun d _ ↦ key e d)

/-! ### The lower bound for the Lusternik–Schnirelmann category -/

section LowerBound

/-- A positive-degree class restricts to zero on an open set whose inclusion is nullhomotopic, so
it comes from the cohomology of `X` relative to that set. -/
private theorem exists_singularCohomologyπ_eq_of_nullhomotopic {U : Set X}
    (hU : (ContinuousMap.subtypeVal U).Nullhomotopic) {p : ℕ} (hp : p ≠ 0)
    (a : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) p) :
    ∃ z, (TopPair.ofSubset (X := TopCat.of X) U).singularCohomologyπ (𝟙_ (ModuleCat.{u} R)) R
      (𝟙_ (ModuleCat.{u} R)) p z = a := by
  have hexact := (TopPair.ofSubset (X := TopCat.of X) U).singularCohomology_exact_space
    (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) p
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  refine hexact a ?_
  exact ConcreteCategory.congr_hom
    (TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic
      (f := (TopPair.ofSubset (X := TopCat.of X) U).map) hU hp) a

/-- A class which comes from the cohomology of `X` relative to `S` also comes from the cohomology
of `X` relative to any smaller `S' ⊆ S`. -/
private theorem exists_singularCohomologyπ_eq_of_subset {S S' : Set X} (hS : S' ⊆ S) {d : ℕ}
    {x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d}
    (hx : ∃ z, (TopPair.ofSubset (X := TopCat.of X) S).singularCohomologyπ (𝟙_ (ModuleCat.{u} R))
      R (𝟙_ (ModuleCat.{u} R)) d z = x) :
    ∃ z, (TopPair.ofSubset (X := TopCat.of X) S').singularCohomologyπ (𝟙_ (ModuleCat.{u} R)) R
      (𝟙_ (ModuleCat.{u} R)) d z = x := by
  obtain ⟨z, rfl⟩ := hx
  have hS' : MapsTo (𝟙 (TopCat.of X)) S' S := fun _ hx ↦ hS hx
  refine ⟨TopPair.singularCohomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) hS') d z, ?_⟩
  have := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality
    (R := 𝟙_ (ModuleCat.{u} R)) (k := R) (M := 𝟙_ (ModuleCat.{u} R))
    (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) hS') d) z
  have hid : TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{u} R)) (k := R)
      (M := 𝟙_ (ModuleCat.{u} R))
        (TopPair.Hom.fst (TopPair.ofSubsetMap (𝟙 (TopCat.of X)) hS')) d = 𝟙 _ := by
    rw [TopPair.ofSubsetMap_fst]
    exact TopCat.singularCohomologyMap_id _ d
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hid] at this
  exact this.symm

/-- A class which comes from the cohomology of `X` relative to the whole space vanishes. -/
private theorem eq_zero_of_exists_singularCohomologyπ_eq_univ {d : ℕ}
    {x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d}
    (hx : ∃ z, (TopPair.ofSubset (X := TopCat.of X) univ).singularCohomologyπ
      (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d z = x) : x = 0 := by
  obtain ⟨z, rfl⟩ := hx
  -- The inclusion `univ → X` has a left inverse `r`, so it is injective on cohomology, and it
  -- kills every relative class.
  let P := TopPair.ofSubset (X := TopCat.of X) univ
  let r : P.fst ⟶ P.snd := TopCat.ofHom ⟨fun x ↦ ⟨x, mem_univ x⟩, by fun_prop⟩
  have hr : r ≫ P.map = 𝟙 P.fst := rfl
  have h0 := ConcreteCategory.congr_hom
    (P.singularCohomologyπ_comp_singularCohomologyMap (𝟙_ (ModuleCat.{u} R)) R
      (𝟙_ (ModuleCat.{u} R)) d) z
  have hid := ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp
    (R := 𝟙_ (ModuleCat.{u} R)) (k := R) (M := 𝟙_ (ModuleCat.{u} R)) r P.map d)
    (P.singularCohomologyπ _ R _ d z)
  rw [hr, TopCat.singularCohomologyMap_id] at hid
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hid h0
  refine hid.trans ?_
  rw [h0, map_zero]
  -- The ambient space `P.fst` of the pair is `TopCat.of X` by definition, so the two zeros agree.
  rfl

/-- **Products of positive-degree classes vanish on categorical opens.** A product of `n` classes
of positive degree comes from the cohomology of `X` relative to the union `U₁ ∪ ⋯ ∪ Uₙ` of any `n`
open sets whose inclusions into `X` are nullhomotopic. -/
theorem IsPositiveDegreeCupProduct.exists_singularCohomologyπ_eq {n d : ℕ}
    {x : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d}
    (hx : IsPositiveDegreeCupProduct X R n x) (U : Fin n → Opens X)
    (hU : ∀ i, (ContinuousMap.subtypeVal (U i : Set X)).Nullhomotopic) :
    ∃ z, (TopPair.ofSubset (X := TopCat.of X) (⋃ i, (U i : Set X))).singularCohomologyπ
      (𝟙_ (ModuleCat.{u} R)) R (𝟙_ (ModuleCat.{u} R)) d z = x := by
  induction hx with
  | single hp a =>
    exact exists_singularCohomologyπ_eq_of_subset
      (iUnion_subset fun i ↦ by rw [Fin.fin_one_eq_zero i])
      (exists_singularCohomologyπ_eq_of_nullhomotopic (hU 0) hp a)
  | @cup n p q d hp h a y hy ih =>
    -- Lift `a` relative to `U 0` and `y` relative to the union of the other open sets, and take
    -- their relative cup product.
    obtain ⟨za, rfl⟩ := exists_singularCohomologyπ_eq_of_nullhomotopic (hU 0) hp a
    obtain ⟨zy, rfl⟩ := ih (fun i ↦ U (Fin.succ i)) fun i ↦ hU (Fin.succ i)
    let V : Set (TopCat.of X) := ⋃ i, (U (Fin.succ i) : Set X)
    have hU0 : IsOpen ((↑) ⁻¹' (U 0 : Set X) : Set ↥((U 0 : Set X) ∪ V)) :=
      (U 0).isOpen.preimage continuous_subtype_val
    have hV : IsOpen ((↑) ⁻¹' V : Set ↥((U 0 : Set X) ∪ V)) :=
      (isOpen_iUnion fun i ↦ (U (Fin.succ i)).isOpen).preimage continuous_subtype_val
    refine exists_singularCohomologyπ_eq_of_subset (S := (U 0 : Set X) ∪ V)
      (iUnion_subset fun i ↦ ?_) ⟨_, TopCat.singularCohomologyπ_singularRelativeCup
        (X := TopCat.of X) R (λ_ _).inv (λ_ _).hom (U 0 : Set X) V hU0 hV p q d h za zy⟩
    induction i using Fin.cases with
    | zero => exact subset_union_left
    | succ i =>
      exact (subset_iUnion (fun j ↦ (U (Fin.succ j) : Set X)) i).trans subset_union_right

/-- **The cup-length lower bound for the Lusternik–Schnirelmann category**: on a nonempty space
`X`, a cover by `r` open sets with nullhomotopic inclusions forces every product of `r` classes of
positive degree to vanish, so `lsCupLength X R + 1 ≤ lsCategoryCount X univ`. -/
theorem lsCupLength_add_one_le_lsCategoryCount [Nonempty X] :
    lsCupLength X R + 1 ≤ lsCategoryCount X univ := by
  cases hcat : lsCategoryCount X univ with
  | top => exact le_top
  | coe r =>
    obtain ⟨c⟩ := nonempty_lsCategoricalCover_of_lsCategoryCount_eq hcat
    have hr : r ≠ 0 := by
      rintro rfl
      exact univ_nonempty.ne_empty (LSCategoricalCover.nonempty_zero_iff.mp ⟨c⟩)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr
    push_cast
    gcongr
    refine lsCupLength_le_iff.mpr fun n d x hx hx0 ↦ ?_
    by_contra! hlt
    have hkn : k + 1 ≤ n := by exact_mod_cast Order.add_one_le_of_lt hlt
    let c' := c.pad hkn
    exact hx0 (eq_zero_of_exists_singularCohomologyπ_eq_univ <|
      exists_singularCohomologyπ_eq_of_subset (fun x _ ↦ c'.subset_iUnion (mem_univ x))
        (hx.exists_singularCohomologyπ_eq c'.opens c'.nullhomotopic))

/-- **The cup-length lower bound for the normalized Lusternik–Schnirelmann category**: on a
nonempty space, `lsCupLength X R ≤ normalizedLSCategory X`. -/
theorem lsCupLength_le_normalizedLSCategory [Nonempty X] :
    lsCupLength X R ≤ normalizedLSCategory X := by
  rw [normalizedLSCategory_def]
  exact ENat.le_sub_of_add_le_right ENat.one_ne_top lsCupLength_add_one_le_lsCategoryCount

end LowerBound

/-- A contractible space has cup length zero. -/
theorem lsCupLength_of_contractibleSpace [ContractibleSpace X] : lsCupLength X R = 0 := by
  have := lsCupLength_le_normalizedLSCategory (X := X) (R := R)
  rwa [normalizedLSCategory_of_contractibleSpace, nonpos_iff_eq_zero] at this

/-- The empty space has cup length zero. -/
theorem lsCupLength_of_isEmpty [IsEmpty X] : lsCupLength X R = 0 := by
  refine lsCupLength_eq_zero_iff.mpr fun p _ a ↦ ?_
  -- The empty space has no singular simplices, so its singular cochain complex is zero.
  have : (TopCat.toSSet.obj (TopCat.of X)).HasDimensionLT 0 :=
    (SSet.notNonempty_iff_hasDimensionLT_zero _).mp fun ⟨σ⟩ ↦
      isEmptyElim (TopCat.toSSetObj₀Equiv σ)
  have hC : IsZero ((TopCat.of X).singularCochainComplex (𝟙_ (ModuleCat.{u} R)) R
      (𝟙_ (ModuleCat.{u} R))) :=
    (TauCeti.ChainComplex.linearYonedaFunctor R (𝟙_ (ModuleCat.{u} R))).map_isZero
      ((TopCat.toSSet.obj (TopCat.of X)).isZero_chainComplex _).op
  exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.homologyFunctor _ _ p).map_isZero hC)) _ _

end TauCeti
