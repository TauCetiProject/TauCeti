/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Order.Directed
import Mathlib.Tactic.Abel

/-!
# Riesz interpolation, unperforation and dimension groups

A *dimension group* is a directed, unperforated, partially ordered abelian group with the Riesz
interpolation property. By the Effros–Handelman–Shen theorem the countable dimension groups
are exactly the sequential positive inductive limits of the simplicial groups `ℤʳ`; they are
also exactly the ordered `K₀`-groups of AF C⋆-algebras.
This file sets up the three defining properties and the equivalent forms of interpolation used
to manipulate positive elements.

## Main definitions

* `TauCeti.HasRieszInterpolation G`: whenever `a₁, a₂ ≤ b₁, b₂` there is `c` with
  `aᵢ ≤ c ≤ bⱼ` for all `i, j`.
* `TauCeti.IsUnperforated G`: `0 ≤ n • g` with `n ≠ 0` forces `0 ≤ g`.
* `TauCeti.IsDimensionGroup G`: directed, unperforated, with Riesz interpolation.

## Main results

* `TauCeti.hasRieszInterpolation_iff_decomposition`: in a preordered abelian group,
  interpolation is equivalent to the Riesz decomposition property: `0 ≤ g ≤ a + b` with
  `0 ≤ a, b` splits as `g = g₁ + g₂` with `0 ≤ g₁ ≤ a` and `0 ≤ g₂ ≤ b`.
* `TauCeti.hasRieszInterpolation_iff_refinement`: both are equivalent to Riesz refinement of
  equal sums of two positive elements.
* `TauCeti.HasRieszInterpolation.exists_decomposition_sum`: decomposition below a finite sum.
* `TauCeti.IsUnperforated.hasUniqueDiv`: an unperforated group is torsion-free.
* `TauCeti.IsDimensionGroup.of_linearOrder`, `TauCeti.IsDimensionGroup.pi`: linearly ordered
  groups and their products, in particular the simplicial groups `ℤʳ`, are dimension groups.

The equivalences of interpolation with decomposition and with refinement hold in every
preordered abelian group; neither antisymmetry nor directedness is needed.

## References

* K. R. Goodearl, *Partially ordered abelian groups with interpolation*, Mathematical Surveys
  and Monographs 20, AMS, 1986, Chapter 2, Proposition 2.1.
* E. G. Effros, D. E. Handelman and C.-L. Shen, *Dimension groups and their affine
  representations*, American Journal of Mathematics 102 (1980), 385–407.
* M. Rørdam, *Classification of nuclear C⋆-algebras*, Encyclopaedia of Mathematical Sciences
  126, Springer, 2002, §1.4.
-/

public section

namespace TauCeti

section Defs

/-- The Riesz interpolation property of a relation `≤`: whenever `a₁ ≤ b₁`, `a₁ ≤ b₂`,
`a₂ ≤ b₁` and `a₂ ≤ b₂`, some `c` satisfies `aᵢ ≤ c ≤ bⱼ` for all `i, j`. Every
join-semilattice has it, but it is strictly weaker than a lattice order. -/
def HasRieszInterpolation (G : Type*) [LE G] : Prop :=
  ∀ a₁ a₂ b₁ b₂ : G, a₁ ≤ b₁ → a₁ ≤ b₂ → a₂ ≤ b₁ → a₂ ≤ b₂ →
    ∃ c, a₁ ≤ c ∧ a₂ ≤ c ∧ c ≤ b₁ ∧ c ≤ b₂

/-- A partially ordered abelian group is unperforated when `0 ≤ n • g` for some `n ≠ 0`
forces `0 ≤ g`. -/
def IsUnperforated (G : Type*) [AddCommGroup G] [PartialOrder G] : Prop :=
  ∀ ⦃n : ℕ⦄, n ≠ 0 → ∀ ⦃g : G⦄, 0 ≤ n • g → 0 ≤ g

/-- A dimension group: a directed, unperforated partially ordered abelian group with Riesz
interpolation. Countability and a scale are separate data. -/
structure IsDimensionGroup (G : Type*) [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] :
    Prop where
  /-- A dimension group is directed. -/
  isDirectedOrder : IsDirectedOrder G
  /-- A dimension group is unperforated. -/
  isUnperforated : IsUnperforated G
  /-- A dimension group has Riesz interpolation. -/
  hasRieszInterpolation : HasRieszInterpolation G

/-- Unfolding lemma for `HasRieszInterpolation`. -/
theorem hasRieszInterpolation_iff (G : Type*) [LE G] :
    HasRieszInterpolation G ↔
      ∀ a₁ a₂ b₁ b₂ : G, a₁ ≤ b₁ → a₁ ≤ b₂ → a₂ ≤ b₁ → a₂ ≤ b₂ →
        ∃ c, a₁ ≤ c ∧ a₂ ≤ c ∧ c ≤ b₁ ∧ c ≤ b₂ :=
  Iff.rfl

/-- Unfolding lemma for `IsUnperforated`. -/
theorem isUnperforated_iff (G : Type*) [AddCommGroup G] [PartialOrder G] :
    IsUnperforated G ↔ ∀ ⦃n : ℕ⦄, n ≠ 0 → ∀ ⦃g : G⦄, 0 ≤ n • g → 0 ≤ g :=
  Iff.rfl

end Defs

namespace HasRieszInterpolation

section LE

variable {G : Type*} [LE G]

/-- An interpolant between two lower and two upper bounds. -/
theorem exists_ge_ge_le_le (h : HasRieszInterpolation G) {a₁ a₂ b₁ b₂ : G}
    (h₁₁ : a₁ ≤ b₁) (h₁₂ : a₁ ≤ b₂) (h₂₁ : a₂ ≤ b₁) (h₂₂ : a₂ ≤ b₂) :
    ∃ c, a₁ ≤ c ∧ a₂ ≤ c ∧ c ≤ b₁ ∧ c ≤ b₂ :=
  h a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂

/-- A join-semilattice has Riesz interpolation, with interpolant `a₁ ⊔ a₂`. -/
theorem of_semilatticeSup {G : Type*} [SemilatticeSup G] : HasRieszInterpolation G :=
  fun a₁ a₂ _ _ h₁₁ h₁₂ h₂₁ h₂₂ ↦
    ⟨a₁ ⊔ a₂, le_sup_left, le_sup_right, sup_le h₁₁ h₂₁, sup_le h₁₂ h₂₂⟩

/-- Riesz interpolation passes to products, ordered componentwise. -/
theorem pi {ι : Type*} {G : ι → Type*} [∀ i, LE (G i)]
    (h : ∀ i, HasRieszInterpolation (G i)) : HasRieszInterpolation (∀ i, G i) := by
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  choose c hc using fun i ↦ (h i).exists_ge_ge_le_le (h₁₁ i) (h₁₂ i) (h₂₁ i) (h₂₂ i)
  exact ⟨c, fun i ↦ (hc i).1, fun i ↦ (hc i).2.1, fun i ↦ (hc i).2.2.1, fun i ↦ (hc i).2.2.2⟩

end LE

section OrderedGroup

variable {G : Type*} [AddCommGroup G]

/-- **Riesz decomposition**: under interpolation, `0 ≤ g ≤ a + b` with `0 ≤ a` and `0 ≤ b`
splits as `g = g₁ + g₂` with `0 ≤ g₁ ≤ a` and `0 ≤ g₂ ≤ b`. -/
theorem exists_decomposition [Preorder G] [IsOrderedAddMonoid G] (h : HasRieszInterpolation G)
    {a b g : G} (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g) (hgab : g ≤ a + b) :
    ∃ g₁ g₂, 0 ≤ g₁ ∧ g₁ ≤ a ∧ 0 ≤ g₂ ∧ g₂ ≤ b ∧ g₁ + g₂ = g := by
  obtain ⟨c, h0c, hc, hca, hcg⟩ :=
    h.exists_ge_ge_le_le ha hg (sub_le_iff_le_add.2 hgab) (sub_le_self g hb)
  exact ⟨c, g - c, h0c, hca, sub_nonneg.2 hcg, sub_le_comm.1 hc, add_sub_cancel c g⟩

/-- Riesz decomposition below a finite sum: under interpolation, `0 ≤ g ≤ ∑ i ∈ s, a i` with
every `a i` positive splits as `g = ∑ i ∈ s, f i` with `0 ≤ f i ≤ a i`. -/
theorem exists_decomposition_sum [PartialOrder G] [IsOrderedAddMonoid G]
    (h : HasRieszInterpolation G) {ι : Type*} (s : Finset ι)
    {a : ι → G} (ha : ∀ i ∈ s, 0 ≤ a i) {g : G} (hg : 0 ≤ g) (hgs : g ≤ ∑ i ∈ s, a i) :
    ∃ f : ι → G, (∀ i ∈ s, 0 ≤ f i ∧ f i ≤ a i) ∧ ∑ i ∈ s, f i = g := by
  classical
  induction s using Finset.cons_induction generalizing g with
  | empty =>
    obtain rfl : g = 0 := le_antisymm (by simpa using hgs) hg
    exact ⟨0, by simp, by simp⟩
  | cons j s hj ih =>
    rw [Finset.sum_cons] at hgs
    have has : ∀ i ∈ s, 0 ≤ a i := fun i hi ↦ ha i (Finset.mem_cons_of_mem hi)
    obtain ⟨g₁, g₂, hg₁, hg₁a, hg₂, hg₂s, rfl⟩ :=
      h.exists_decomposition (ha j (Finset.mem_cons_self j s)) (Finset.sum_nonneg has) hg hgs
    obtain ⟨f, hf, hfs⟩ := ih has hg₂ hg₂s
    refine ⟨Function.update f j g₁, fun i hi ↦ ?_, ?_⟩
    · rcases Finset.mem_cons.1 hi with rfl | hi
      · simpa using ⟨hg₁, hg₁a⟩
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
        exact hf i hi
    · rw [Finset.sum_cons, Finset.sum_update_of_notMem hj, Function.update_self, hfs]

end OrderedGroup

end HasRieszInterpolation

section RieszEquivalences

variable {G : Type*} [AddCommGroup G] [Preorder G] [IsOrderedAddMonoid G]

/-- Riesz decomposition gives Riesz refinement: decompose `x₁ ≤ y₁ + y₂` and take the
complements in `y₁` and `y₂` as the second row. -/
private theorem exists_refinement_of_decomposition
    (hdec : ∀ a b g : G, 0 ≤ a → 0 ≤ b → 0 ≤ g → g ≤ a + b →
      ∃ g₁ g₂, 0 ≤ g₁ ∧ g₁ ≤ a ∧ 0 ≤ g₂ ∧ g₂ ≤ b ∧ g₁ + g₂ = g)
    {x₁ x₂ y₁ y₂ : G} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (hxy : x₁ + x₂ = y₁ + y₂) :
    ∃ z₁₁ z₁₂ z₂₁ z₂₂ : G, 0 ≤ z₁₁ ∧ 0 ≤ z₁₂ ∧ 0 ≤ z₂₁ ∧ 0 ≤ z₂₂ ∧
      z₁₁ + z₁₂ = x₁ ∧ z₂₁ + z₂₂ = x₂ ∧ z₁₁ + z₂₁ = y₁ ∧ z₁₂ + z₂₂ = y₂ := by
  obtain ⟨z₁₁, z₁₂, h₁₁, h₁₁y, h₁₂, h₁₂y, rfl⟩ :=
    hdec y₁ y₂ x₁ hy₁ hy₂ hx₁ (hxy ▸ le_add_of_nonneg_right hx₂)
  refine ⟨z₁₁, z₁₂, y₁ - z₁₁, y₂ - z₁₂, h₁₁, h₁₂, sub_nonneg.2 h₁₁y, sub_nonneg.2 h₁₂y, rfl,
    ?_, add_sub_cancel z₁₁ y₁, add_sub_cancel z₁₂ y₂⟩
  rw [eq_sub_of_add_eq' hxy]
  abel

/-- Riesz refinement gives interpolation: refine `(b₁ - a₁) + (b₂ - a₂) = (b₁ - a₂) + (b₂ - a₁)`
and take the interpolant `a₁ + z₁₂ = a₂ + z₂₁ = b₁ - z₁₁ = b₂ - z₂₂`. -/
private theorem hasRieszInterpolation_of_refinement
    (h : ∀ x₁ x₂ y₁ y₂ : G, 0 ≤ x₁ → 0 ≤ x₂ → 0 ≤ y₁ → 0 ≤ y₂ → x₁ + x₂ = y₁ + y₂ →
      ∃ z₁₁ z₁₂ z₂₁ z₂₂ : G, 0 ≤ z₁₁ ∧ 0 ≤ z₁₂ ∧ 0 ≤ z₂₁ ∧ 0 ≤ z₂₂ ∧
        z₁₁ + z₁₂ = x₁ ∧ z₂₁ + z₂₂ = x₂ ∧ z₁₁ + z₂₁ = y₁ ∧ z₁₂ + z₂₂ = y₂) :
    HasRieszInterpolation G := by
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  obtain ⟨z₁₁, z₁₂, z₂₁, z₂₂, hz₁₁, hz₁₂, hz₂₁, hz₂₂, e₁, -, e₃, e₄⟩ :=
    h (b₁ - a₁) (b₂ - a₂) (b₁ - a₂) (b₂ - a₁) (sub_nonneg.2 h₁₁) (sub_nonneg.2 h₂₂)
      (sub_nonneg.2 h₂₁) (sub_nonneg.2 h₁₂) (by abel)
  have c₂ : a₁ + z₁₂ = a₂ + z₂₁ := by
    rw [eq_sub_of_add_eq' e₁, eq_sub_of_add_eq e₃]; abel
  have c₃ : a₁ + z₁₂ = b₁ - z₁₁ := by
    rw [eq_sub_of_add_eq' e₁]; abel
  have c₄ : a₁ + z₁₂ = b₂ - z₂₂ := by
    rw [eq_sub_of_add_eq e₄]; abel
  exact ⟨a₁ + z₁₂, le_add_of_nonneg_right hz₁₂, c₂ ▸ le_add_of_nonneg_right hz₂₁,
    c₃ ▸ sub_le_self b₁ hz₁₁, c₄ ▸ sub_le_self b₂ hz₂₂⟩

/-- **Riesz refinement**: under interpolation, two equal sums `x₁ + x₂ = y₁ + y₂` of positive
elements have a common positive refinement `xᵢ = zᵢ₁ + zᵢ₂`, `yⱼ = z₁ⱼ + z₂ⱼ`. -/
theorem HasRieszInterpolation.exists_refinement (h : HasRieszInterpolation G)
    {x₁ x₂ y₁ y₂ : G} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (hxy : x₁ + x₂ = y₁ + y₂) :
    ∃ z₁₁ z₁₂ z₂₁ z₂₂ : G, 0 ≤ z₁₁ ∧ 0 ≤ z₁₂ ∧ 0 ≤ z₂₁ ∧ 0 ≤ z₂₂ ∧
      z₁₁ + z₁₂ = x₁ ∧ z₂₁ + z₂₂ = x₂ ∧ z₁₁ + z₂₁ = y₁ ∧ z₁₂ + z₂₂ = y₂ :=
  exists_refinement_of_decomposition
    (fun _ _ _ ha hb hg hgab ↦ h.exists_decomposition ha hb hg hgab) hx₁ hx₂ hy₁ hy₂ hxy

/-- In a preordered abelian group, Riesz interpolation is equivalent to the Riesz
decomposition property. Neither antisymmetry nor directedness is needed. -/
theorem hasRieszInterpolation_iff_decomposition :
    HasRieszInterpolation G ↔
      ∀ a b g : G, 0 ≤ a → 0 ≤ b → 0 ≤ g → g ≤ a + b →
        ∃ g₁ g₂, 0 ≤ g₁ ∧ g₁ ≤ a ∧ 0 ≤ g₂ ∧ g₂ ≤ b ∧ g₁ + g₂ = g :=
  ⟨fun h _ _ _ ha hb hg hgab ↦ h.exists_decomposition ha hb hg hgab, fun hdec ↦
    hasRieszInterpolation_of_refinement fun _ _ _ _ hx₁ hx₂ hy₁ hy₂ hxy ↦
      exists_refinement_of_decomposition hdec hx₁ hx₂ hy₁ hy₂ hxy⟩

/-- In a preordered abelian group, Riesz interpolation is equivalent to the Riesz
refinement property for equal sums of two positive elements. Neither antisymmetry nor
directedness is needed. -/
theorem hasRieszInterpolation_iff_refinement :
    HasRieszInterpolation G ↔
      ∀ x₁ x₂ y₁ y₂ : G, 0 ≤ x₁ → 0 ≤ x₂ → 0 ≤ y₁ → 0 ≤ y₂ → x₁ + x₂ = y₁ + y₂ →
        ∃ z₁₁ z₁₂ z₂₁ z₂₂ : G, 0 ≤ z₁₁ ∧ 0 ≤ z₁₂ ∧ 0 ≤ z₂₁ ∧ 0 ≤ z₂₂ ∧
          z₁₁ + z₁₂ = x₁ ∧ z₂₁ + z₂₂ = x₂ ∧ z₁₁ + z₂₁ = y₁ ∧ z₁₂ + z₂₂ = y₂ :=
  ⟨fun h _ _ _ _ hx₁ hx₂ hy₁ hy₂ hxy ↦ h.exists_refinement hx₁ hx₂ hy₁ hy₂ hxy,
    hasRieszInterpolation_of_refinement⟩

end RieszEquivalences

namespace IsUnperforated

variable {G : Type*} [AddCommGroup G]

/-- In an unperforated group, `0 ≤ g` follows from `0 ≤ n • g` for any `n ≠ 0`. -/
theorem nonneg_of_nsmul_nonneg [PartialOrder G] (h : IsUnperforated G)
    {n : ℕ} (hn : n ≠ 0) {g : G} (hg : 0 ≤ n • g) : 0 ≤ g :=
  h hn hg

/-- In an unperforated group, `0 ≤ n • g ↔ 0 ≤ g` for `n ≠ 0`. -/
theorem nsmul_nonneg_iff [PartialOrder G] [IsOrderedAddMonoid G]
    (h : IsUnperforated G) {n : ℕ} (hn : n ≠ 0) {g : G} : 0 ≤ n • g ↔ 0 ≤ g :=
  ⟨h.nonneg_of_nsmul_nonneg hn, fun hg ↦ nsmul_nonneg hg n⟩

/-- A linearly ordered abelian group is unperforated. -/
theorem of_linearOrder [LinearOrder G] [IsOrderedAddMonoid G] : IsUnperforated G :=
  fun _ hn _ ↦ (_root_.nsmul_nonneg_iff hn).1

/-- Unperforation passes to products, ordered componentwise. -/
theorem pi {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, PartialOrder (G i)]
    (h : ∀ i, IsUnperforated (G i)) : IsUnperforated (∀ i, G i) :=
  fun _ hn _ hg i ↦ (h i).nonneg_of_nsmul_nonneg hn (hg i)

/-- An unperforated partially ordered abelian group is torsion-free: `n • g = n • h` with
`n ≠ 0` forces `g = h`, since then `0 ≤ g - h` and `0 ≤ h - g`. -/
theorem hasUniqueDiv [PartialOrder G] [IsOrderedAddMonoid G]
    (h : IsUnperforated G) : HasUniqueDiv G where
  nsmul_right_injective n hn a b hab := by
    have hab' : n • a = n • b := hab
    refine le_antisymm (sub_nonneg.1 (h.nonneg_of_nsmul_nonneg hn ?_))
      (sub_nonneg.1 (h.nonneg_of_nsmul_nonneg hn ?_)) <;> simp [nsmul_sub, hab']

end IsUnperforated

namespace IsDimensionGroup

/-- A linearly ordered abelian group, for instance `ℤ`, `ℚ` or `ℝ`, is a dimension group. -/
theorem of_linearOrder {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] :
    IsDimensionGroup G where
  isDirectedOrder := inferInstance
  isUnperforated := .of_linearOrder
  hasRieszInterpolation := .of_semilatticeSup

/-- A product of dimension groups, ordered componentwise, is a dimension group. In particular
the simplicial groups `Fin r → ℤ` are dimension groups. -/
theorem pi {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, PartialOrder (G i)]
    [∀ i, IsOrderedAddMonoid (G i)] (h : ∀ i, IsDimensionGroup (G i)) :
    IsDimensionGroup (∀ i, G i) where
  isDirectedOrder := ⟨fun a b ↦ by
    choose c hc using fun i ↦ (h i).isDirectedOrder.directed (a i) (b i)
    exact ⟨c, fun i ↦ (hc i).1, fun i ↦ (hc i).2⟩⟩
  isUnperforated := .pi fun i ↦ (h i).isUnperforated
  hasRieszInterpolation := .pi fun i ↦ (h i).hasRieszInterpolation

end IsDimensionGroup

end TauCeti
