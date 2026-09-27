/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.MinimalPresentation

/-!
# The relator words of the Demushkin normal forms

Labute's classification of Demushkin groups puts every finite-rank Demushkin group in one of
three normal forms, each a pro-`p` group presented on `n` generators `x₁, …, xₙ` by a single
relator word. This file covers the forms with finite `f`, presented by the words

* `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, for `q ≠ 2` and `n` even;
* `x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)`, for `q = 2` and `n` odd;
* `x₁^{2+α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, for `q = 2` and `n` even,

where `(x, y) = x⁻¹y⁻¹xy` is Labute's commutator. In the two `q = 2` forms Labute also allows
`f = ∞`, meaning that the factor `x₂^{2^f}`, resp. `x₃^{2^f}`, is absent. The words below take a
natural number `f` and do not define those forms; only the rank-two even form is reached, since
on its two generators `x₃ = 1` and the even word reads as the `f = ∞` relator `x₁^{2+α} (x₁, x₂)`.
This file defines the commutator and the three words on an arbitrary tuple `x : ℕ → H` of group
elements, so that the same word can be read in a free pro-`p` group and in any group that
receives it. Read on the `ℕ`-indexed generators `TauCeti.freeProPGen` and
`TauCeti.presentedProPGen`, which are `1` out of range, the words carry no index-bound side
conditions.

Under the conditions `p ∣ q` for the first word, `0 < f` for the second, and `2 ∣ a` together with
`0 < f` for the third, each word is a product of `p`-th powers and commutators, so it lies in the
pro-`p` Frattini subgroup of every topological group, in particular of the free pro-`p` group.
Hence, under the same conditions, the presentation of a normal form on `n` generators is minimal:
the presented group has topological generator rank exactly `n`.

## Main definitions

* `TauCeti.labuteComm`: Labute's commutator `(x, y) = x⁻¹y⁻¹xy`.
* `TauCeti.demushkinWordNeTwo`, `TauCeti.demushkinWordTwoOdd`, `TauCeti.demushkinWordTwoEven`:
  the three normal-form relator words, on an arbitrary tuple.

## Main results

* `TauCeti.demushkinWordNeTwo_presentedProPGen_eq_one` and its two companions: the generators of the
  normal-form presentation satisfy its defining relation.
* `TauCeti.demushkinWordNeTwo_mem_proPFrattini`, `TauCeti.demushkinWordTwoOdd_mem_proPFrattini`,
  `TauCeti.demushkinWordTwoEven_mem_proPFrattini`: each word lies in the pro-`p` Frattini
  subgroup, for `p ∣ q`, resp. `0 < f`, resp. `2 ∣ a` and `0 < f`.
* `TauCeti.topologicalGeneratorRankNat_presentedProP_demushkinWordNeTwo` and its two companions:
  under the same conditions, the normal-form presentation on `n` generators is minimal.
* `TauCeti.map_demushkinWordNeTwo_eq_one` and its two companions: a character into a commutative
  group kills the word as soon as its values on the generators carrying a power have trivial
  power: `χ(x₁)^q = 1`, resp. `χ(x₁)² = 1` and `χ(x₂)^{2^f} = 1`, resp. `χ(x₁)^{2+a} = 1` and
  `χ(x₃)^{2^f} = 1`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Theorems 1–4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Theorem 3.9.19.
-/

public section

namespace TauCeti

open scoped commutatorElement

/-! ### Labute's commutator -/

section LabuteComm

variable {H : Type*} [Group H]

/-- **Labute's commutator** `(x, y) = x⁻¹y⁻¹xy`, the convention in which the Demushkin
normal-form relators are written. Mathlib's `⁅x, y⁆ = xyx⁻¹y⁻¹` is the other convention; the two
are related by `TauCeti.labuteComm_eq_commutatorElement_inv_inv`, and generate the same
subgroups. -/
def labuteComm (x y : H) : H := x⁻¹ * y⁻¹ * x * y

/-- The defining equation of `TauCeti.labuteComm`. -/
theorem labuteComm_def (x y : H) : labuteComm x y = x⁻¹ * y⁻¹ * x * y := (rfl)

/-- Labute's commutator is Mathlib's commutator of the inverses: `(x, y) = ⁅x⁻¹, y⁻¹⁆`. -/
theorem labuteComm_eq_commutatorElement_inv_inv (x y : H) : labuteComm x y = ⁅x⁻¹, y⁻¹⁆ := by
  rw [labuteComm_def, commutatorElement_def, inv_inv, inv_inv]

/-- A monoid homomorphism carries Labute's commutator to Labute's commutator. -/
@[simp]
theorem map_labuteComm {K F : Type*} [Group K] [FunLike F H K] [MonoidHomClass F H K] (f : F)
    (x y : H) : f (labuteComm x y) = labuteComm (f x) (f y) := by
  simp only [labuteComm_def, map_mul, map_inv]

/-- Labute's commutator is trivial exactly when the two elements commute. -/
theorem labuteComm_eq_one_iff_commute (x y : H) : labuteComm x y = 1 ↔ Commute x y := by
  rw [labuteComm_eq_commutatorElement_inv_inv, commutatorElement_eq_one_iff_commute,
    Commute.inv_inv_iff]

/-- Labute's commutator of two commuting elements is trivial. -/
theorem _root_.Commute.labuteComm_eq_one {x y : H} (h : Commute x y) : labuteComm x y = 1 :=
  (labuteComm_eq_one_iff_commute x y).mpr h

/-- Labute's commutator is trivial in a commutative group. -/
@[simp]
theorem labuteComm_eq_one {A : Type*} [CommGroup A] (x y : A) : labuteComm x y = 1 :=
  (Commute.all x y).labuteComm_eq_one

/-- Labute's commutator lies in the commutator subgroup. -/
theorem labuteComm_mem_commutator (x y : H) : labuteComm x y ∈ commutator H := by
  rw [labuteComm_eq_commutatorElement_inv_inv]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Labute's commutator lies in the pro-`p` Frattini subgroup of a topological group. -/
theorem labuteComm_mem_proPFrattini [TopologicalSpace H] {p : ℕ} (hp : p.Prime) (x y : H) :
    labuteComm x y ∈ proPFrattini p H :=
  commutator_le_proPFrattini hp (labuteComm_mem_commutator x y)

end LabuteComm

/-! ### The three normal-form words -/

section Words

variable {H : Type*} [Group H]

/-- The `q ≠ 2` normal-form word `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, on an arbitrary tuple
`x : ℕ → H`, with `x 0` playing the role of `x₁`. The classification uses it for `n` even; the
word has `n / 2` commutator factors. -/
def demushkinWordNeTwo (q n : ℕ) (x : ℕ → H) : H :=
  x 0 ^ q * ((List.range (n / 2)).map fun i ↦ labuteComm (x (2 * i)) (x (2 * i + 1))).prod

/-- The defining equation of `TauCeti.demushkinWordNeTwo`. -/
theorem demushkinWordNeTwo_def (q n : ℕ) (x : ℕ → H) :
    demushkinWordNeTwo q n x =
      x 0 ^ q * ((List.range (n / 2)).map fun i ↦ labuteComm (x (2 * i)) (x (2 * i + 1))).prod :=
  (rfl)

/-- The `q = 2`, `n` odd normal-form word `x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)`, on an
arbitrary tuple `x : ℕ → H`, with `x 0` playing the role of `x₁`. The parameter `f` is finite;
the word has `n / 2` commutator factors. -/
def demushkinWordTwoOdd (f n : ℕ) (x : ℕ → H) : H :=
  x 0 ^ 2 * x 1 ^ 2 ^ f *
    ((List.range (n / 2)).map fun i ↦ labuteComm (x (2 * i + 1)) (x (2 * i + 2))).prod

/-- The defining equation of `TauCeti.demushkinWordTwoOdd`. -/
theorem demushkinWordTwoOdd_def (f n : ℕ) (x : ℕ → H) :
    demushkinWordTwoOdd f n x =
      x 0 ^ 2 * x 1 ^ 2 ^ f *
        ((List.range (n / 2)).map fun i ↦ labuteComm (x (2 * i + 1)) (x (2 * i + 2))).prod :=
  (rfl)

/-- The `q = 2`, `n` even normal-form word `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`,
on an arbitrary tuple `x : ℕ → H`, with `x 0` playing the role of `x₁`. The exponent `2 + a` is
a natural number standing for Labute's `2 + α`, `α ∈ 4ℤ₂`: on an arbitrary group only natural
powers make sense, and no normal form is lost, because the presented pro-`2` group is determined
up to isomorphism by `n` and the image of its orientation (Labute, Theorem 2), which depends on
`α` only through `v₂(α)`: it is `{±1} × U^(f)` for `v₂(α) ≥ f` and `U^[v₂(α)]` otherwise
(corollary to Labute's Theorem 4), so `a = 0` and `a = 2^g` with `2 ≤ g < f` already realize
every class. The word has `n / 2 - 1` commutator factors after `(x₁, x₂)`. -/
def demushkinWordTwoEven (a f n : ℕ) (x : ℕ → H) : H :=
  x 0 ^ (2 + a) * labuteComm (x 0) (x 1) * x 2 ^ 2 ^ f *
    ((List.range (n / 2 - 1)).map fun i ↦ labuteComm (x (2 * i + 2)) (x (2 * i + 3))).prod

/-- The defining equation of `TauCeti.demushkinWordTwoEven`. -/
theorem demushkinWordTwoEven_def (a f n : ℕ) (x : ℕ → H) :
    demushkinWordTwoEven a f n x =
      x 0 ^ (2 + a) * labuteComm (x 0) (x 1) * x 2 ^ 2 ^ f *
        ((List.range (n / 2 - 1)).map fun i ↦
          labuteComm (x (2 * i + 2)) (x (2 * i + 3))).prod :=
  (rfl)

variable {K F : Type*} [Group K] [FunLike F H K] [MonoidHomClass F H K] (φ : F)

/-- A homomorphism reads the `q ≠ 2` word on the image tuple. -/
@[simp]
theorem map_demushkinWordNeTwo (q n : ℕ) (x : ℕ → H) :
    φ (demushkinWordNeTwo q n x) = demushkinWordNeTwo q n (φ ∘ x) := by
  simp only [demushkinWordNeTwo_def, map_mul, map_pow, map_list_prod, List.map_map,
    Function.comp_def, map_labuteComm]

/-- A homomorphism reads the `q = 2`, `n` odd word on the image tuple. -/
@[simp]
theorem map_demushkinWordTwoOdd (f n : ℕ) (x : ℕ → H) :
    φ (demushkinWordTwoOdd f n x) = demushkinWordTwoOdd f n (φ ∘ x) := by
  simp only [demushkinWordTwoOdd_def, map_mul, map_pow, map_list_prod, List.map_map,
    Function.comp_def, map_labuteComm]

/-- A homomorphism reads the `q = 2`, `n` even word on the image tuple. -/
@[simp]
theorem map_demushkinWordTwoEven (a f n : ℕ) (x : ℕ → H) :
    φ (demushkinWordTwoEven a f n x) = demushkinWordTwoEven a f n (φ ∘ x) := by
  simp only [demushkinWordTwoEven_def, map_mul, map_pow, map_list_prod, List.map_map,
    Function.comp_def, map_labuteComm]

variable {A : Type*} [CommGroup A]

/-- In a commutative group the `q ≠ 2` word is `x₁^q`. -/
@[simp]
theorem demushkinWordNeTwo_eq_of_commGroup (q n : ℕ) (x : ℕ → A) :
    demushkinWordNeTwo q n x = x 0 ^ q := by
  simp [demushkinWordNeTwo_def]

/-- In a commutative group the `q = 2`, `n` odd word is `x₁² x₂^{2^f}`. -/
@[simp]
theorem demushkinWordTwoOdd_eq_of_commGroup (f n : ℕ) (x : ℕ → A) :
    demushkinWordTwoOdd f n x = x 0 ^ 2 * x 1 ^ 2 ^ f := by
  simp [demushkinWordTwoOdd_def]

/-- In a commutative group the `q = 2`, `n` even word is `x₁^{2+a} x₃^{2^f}`. -/
@[simp]
theorem demushkinWordTwoEven_eq_of_commGroup (a f n : ℕ) (x : ℕ → A) :
    demushkinWordTwoEven a f n x = x 0 ^ (2 + a) * x 2 ^ 2 ^ f := by
  simp [demushkinWordTwoEven_def]

variable {G : Type*} [Group G] {F' : Type*} [FunLike F' G A] [MonoidHomClass F' G A] (χ : F')

/-- A character into a commutative group whose value on `x₁` has trivial `q`-th power kills the
`q ≠ 2` word. -/
theorem map_demushkinWordNeTwo_eq_one (q n : ℕ) {x : ℕ → G} (h₀ : χ (x 0) ^ q = 1) :
    χ (demushkinWordNeTwo q n x) = 1 := by
  rw [map_demushkinWordNeTwo, demushkinWordNeTwo_eq_of_commGroup, Function.comp_apply, h₀]

/-- A character into a commutative group whose value on `x₁` squares to `1` and whose value on
`x₂` has trivial `2^f`-th power kills the `q = 2`, `n` odd word. -/
theorem map_demushkinWordTwoOdd_eq_one (f n : ℕ) {x : ℕ → G} (h₀ : χ (x 0) ^ 2 = 1)
    (h₁ : χ (x 1) ^ 2 ^ f = 1) : χ (demushkinWordTwoOdd f n x) = 1 := by
  rw [map_demushkinWordTwoOdd, demushkinWordTwoOdd_eq_of_commGroup, Function.comp_apply,
    Function.comp_apply, h₀, h₁, one_mul]

/-- A character into a commutative group whose value on `x₁` has trivial `(2 + a)`-th power and
whose value on `x₃` has trivial `2^f`-th power kills the `q = 2`, `n` even word. -/
theorem map_demushkinWordTwoEven_eq_one (a f n : ℕ) {x : ℕ → G} (h₀ : χ (x 0) ^ (2 + a) = 1)
    (h₂ : χ (x 2) ^ 2 ^ f = 1) : χ (demushkinWordTwoEven a f n x) = 1 := by
  rw [map_demushkinWordTwoEven, demushkinWordTwoEven_eq_of_commGroup, Function.comp_apply,
    Function.comp_apply, h₀, h₂, one_mul]

end Words

/-! ### The generators of a normal-form presentation satisfy the relation -/

section Relation

variable (p : ℕ)

/-- The `ℕ`-indexed generators of the `q ≠ 2` normal-form presentation satisfy its defining
relation `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n) = 1`. -/
@[simp]
theorem demushkinWordNeTwo_presentedProPGen_eq_one (q n : ℕ) :
    demushkinWordNeTwo q n (presentedProPGen p n {demushkinWordNeTwo q n (freeProPGen p n)}) =
      1 := by
  rw [← presentedProP.mk_comp_freeProPGen, ← map_demushkinWordNeTwo]
  exact presentedProP.mk_relator _ (Set.mem_singleton _)

/-- The `ℕ`-indexed generators of the `q = 2`, `n` odd normal-form presentation satisfy its
defining relation `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n) = 1`. -/
@[simp]
theorem demushkinWordTwoOdd_presentedProPGen_eq_one (f n : ℕ) :
    demushkinWordTwoOdd f n (presentedProPGen p n {demushkinWordTwoOdd f n (freeProPGen p n)}) =
      1 := by
  rw [← presentedProP.mk_comp_freeProPGen, ← map_demushkinWordTwoOdd]
  exact presentedProP.mk_relator _ (Set.mem_singleton _)

/-- The `ℕ`-indexed generators of the `q = 2`, `n` even normal-form presentation satisfy its
defining relation `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n) = 1`. -/
@[simp]
theorem demushkinWordTwoEven_presentedProPGen_eq_one (a f n : ℕ) :
    demushkinWordTwoEven a f n
      (presentedProPGen p n {demushkinWordTwoEven a f n (freeProPGen p n)}) = 1 := by
  rw [← presentedProP.mk_comp_freeProPGen, ← map_demushkinWordTwoEven]
  exact presentedProP.mk_relator _ (Set.mem_singleton _)

end Relation

/-! ### The words lie in the Frattini subgroup -/

section Frattini

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- For `p ∣ q`, the `q ≠ 2` word lies in the pro-`p` Frattini subgroup: `x₁^q` is a `p`-th power
and the remaining factors are commutators. This covers `q = 0`. -/
theorem demushkinWordNeTwo_mem_proPFrattini {p q : ℕ} (hp : p.Prime) (hq : p ∣ q) (n : ℕ)
    (x : ℕ → H) : demushkinWordNeTwo q n x ∈ proPFrattini p H := by
  refine mul_mem (pow_mem_proPFrattini_of_dvd hq _) (Subgroup.list_prod_mem _ ?_)
  simpa only [List.forall_mem_map] using fun i _ ↦ labuteComm_mem_proPFrattini hp _ _

/-- For `f ≥ 1`, the `q = 2`, `n` odd word lies in the pro-`2` Frattini subgroup: `x₁²` and
`x₂^{2^f}` are squares and the remaining factors are commutators. -/
theorem demushkinWordTwoOdd_mem_proPFrattini {f : ℕ} (hf : 0 < f) (n : ℕ) (x : ℕ → H) :
    demushkinWordTwoOdd f n x ∈ proPFrattini 2 H := by
  refine mul_mem (mul_mem (pow_mem_proPFrattini _)
    (pow_mem_proPFrattini_of_dvd (dvd_pow_self 2 hf.ne') _)) (Subgroup.list_prod_mem _ ?_)
  simpa only [List.forall_mem_map] using fun i _ ↦ labuteComm_mem_proPFrattini Nat.prime_two _ _

/-- For `a` even and `f ≥ 1`, the `q = 2`, `n` even word lies in the pro-`2` Frattini subgroup:
`x₁^{2+a}` and `x₃^{2^f}` are squares and the remaining factors are commutators. -/
theorem demushkinWordTwoEven_mem_proPFrattini {a f : ℕ} (ha : 2 ∣ a) (hf : 0 < f) (n : ℕ)
    (x : ℕ → H) : demushkinWordTwoEven a f n x ∈ proPFrattini 2 H := by
  refine mul_mem (mul_mem (mul_mem (pow_mem_proPFrattini_of_dvd (dvd_add (dvd_refl 2) ha) _)
    (labuteComm_mem_proPFrattini Nat.prime_two _ _))
    (pow_mem_proPFrattini_of_dvd (dvd_pow_self 2 hf.ne') _)) (Subgroup.list_prod_mem _ ?_)
  simpa only [List.forall_mem_map] using fun i _ ↦ labuteComm_mem_proPFrattini Nat.prime_two _ _

end Frattini

/-! ### The normal-form presentations are minimal -/

section Minimal

variable {p : ℕ} [Fact p.Prime]

/-- **The `q ≠ 2` normal-form presentation is minimal**: for `p ∣ q`, the pro-`p` group presented
on `n` generators by `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` has topological generator rank `n`. -/
theorem topologicalGeneratorRankNat_presentedProP_demushkinWordNeTwo {q : ℕ} (hq : p ∣ q)
    (n : ℕ) :
    topologicalGeneratorRankNat
      (presentedProP p (Fin n) {demushkinWordNeTwo q n (freeProPGen p n)})
      presentedProP.isTopologicallyFinitelyGenerated = n := by
  simpa using (presentedProP.topologicalGeneratorRankNat_eq_card_iff
    {demushkinWordNeTwo q n (freeProPGen p n)}).mpr
    (Set.singleton_subset_iff.mpr (demushkinWordNeTwo_mem_proPFrattini Fact.out hq n _))

/-- **The `q = 2`, `n` odd normal-form presentation is minimal**: for `f ≥ 1`, the pro-`2` group
presented on `n` generators by `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` has topological generator
rank `n`. -/
theorem topologicalGeneratorRankNat_presentedProP_demushkinWordTwoOdd {f : ℕ} (hf : 0 < f)
    (n : ℕ) :
    topologicalGeneratorRankNat
      (presentedProP 2 (Fin n) {demushkinWordTwoOdd f n (freeProPGen 2 n)})
      presentedProP.isTopologicallyFinitelyGenerated = n := by
  simpa using (presentedProP.topologicalGeneratorRankNat_eq_card_iff
    {demushkinWordTwoOdd f n (freeProPGen 2 n)}).mpr
    (Set.singleton_subset_iff.mpr (demushkinWordTwoOdd_mem_proPFrattini hf n _))

/-- **The `q = 2`, `n` even normal-form presentation is minimal**: for `a` even and `f ≥ 1`, the
pro-`2` group presented on `n` generators by `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`
has topological generator rank `n`. -/
theorem topologicalGeneratorRankNat_presentedProP_demushkinWordTwoEven {a f : ℕ} (ha : 2 ∣ a)
    (hf : 0 < f) (n : ℕ) :
    topologicalGeneratorRankNat
      (presentedProP 2 (Fin n) {demushkinWordTwoEven a f n (freeProPGen 2 n)})
      presentedProP.isTopologicallyFinitelyGenerated = n := by
  simpa using (presentedProP.topologicalGeneratorRankNat_eq_card_iff
    {demushkinWordTwoEven a f n (freeProPGen 2 n)}).mpr
    (Set.singleton_subset_iff.mpr (demushkinWordTwoEven_mem_proPFrattini ha hf n _))

end Minimal

end TauCeti
