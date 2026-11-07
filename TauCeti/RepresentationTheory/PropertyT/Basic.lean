/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Invariants
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Relative property (T) for discrete groups

A representation `ρ` of a group `Γ` on a normed space has *almost invariant vectors* when for every
finite set `F ⊆ Γ` and every `ε > 0` some unit vector is moved by less than `ε` by each element of
`F`. A subgroup `Λ ≤ Γ` has *relative property (T)* in `Γ` when every unitary representation of `Γ`
on a complex Hilbert space with almost invariant vectors has a nonzero `Λ`-invariant vector;
property (T) of `Γ` is the case `Λ = ⊤`. The group is discrete: no topology on `Γ` is used, and
unitary representations are Tau Ceti's `ContRepresentation.IsUnitary` on `ContRepresentation ℂ Γ H`.

A pair `(F, δ)` of a finite set and a real number is a *Kazhdan pair* for `Λ ≤ Γ` when every
unitary representation with a unit vector moved by less than `δ` by each element of `F` has a
nonzero `Λ`-invariant vector. A Kazhdan pair with `δ > 0` yields relative property (T).

## Main definitions

* `ContRepresentation.HasAlmostInvariantVectors`: almost invariant vectors.
* `Subgroup.RelativePropertyT`: relative property (T) of a subgroup.
* `Subgroup.IsKazhdanPair`: Kazhdan pairs for a subgroup.

## Main statements

* `Subgroup.relativePropertyT_bot`: the trivial subgroup has relative property (T) in every group.
* `Subgroup.RelativePropertyT.anti` and `Subgroup.RelativePropertyT.map`: relative property (T)
  passes to smaller subgroups and to images under group homomorphisms; in particular from a
  subgroup of `Γ₀` to the same subgroup of any group containing `Γ₀`, and to quotients.
* `Subgroup.IsKazhdanPair.relativePropertyT`: a Kazhdan pair gives relative property (T).
* `Subgroup.isKazhdanPair_top_univ_one` and `Subgroup.relativePropertyT_top_of_finite`: for a
  finite group, `(Γ, 1)` is a Kazhdan pair for `⊤`, so finite groups have property (T).

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Definition 14.1.1 and
  Proposition 14.1.2.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Chapter 1.
-/

public section

universe u v w

namespace ContRepresentation

section Normed

variable {R G V : Type*} [Ring R] [Monoid G] [SeminormedAddCommGroup V] [Module R V]

/-- A representation `ρ` has almost invariant vectors when for every finite set `F` and every
`ε > 0` some unit vector is moved by less than `ε` by each element of `F`. -/
def HasAlmostInvariantVectors (ρ : ContRepresentation R G V) : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → ∃ ξ : V, ‖ξ‖ = 1 ∧ ∀ g ∈ F, ‖ρ g ξ - ξ‖ < ε

variable {ρ : ContRepresentation R G V}

/-- Unfolding lemma for `ContRepresentation.HasAlmostInvariantVectors`. -/
theorem hasAlmostInvariantVectors_iff :
    ρ.HasAlmostInvariantVectors ↔
      ∀ (F : Finset G) (ε : ℝ), 0 < ε → ∃ ξ : V, ‖ξ‖ = 1 ∧ ∀ g ∈ F, ‖ρ g ξ - ξ‖ < ε :=
  Iff.rfl

/-- A representation with almost invariant vectors has a unit vector. -/
theorem HasAlmostInvariantVectors.exists_norm_eq_one (hρ : ρ.HasAlmostInvariantVectors) :
    ∃ ξ : V, ‖ξ‖ = 1 :=
  (hρ ∅ 1 one_pos).imp fun _ hξ ↦ hξ.1

/-- Almost invariant vectors are preserved by restriction along a monoid homomorphism. -/
theorem HasAlmostInvariantVectors.restrict (hρ : ρ.HasAlmostInvariantVectors) {S : Type*}
    [Monoid S] (φ : S →* G) : (ρ.restrict φ).HasAlmostInvariantVectors := by
  classical
  intro F ε hε
  obtain ⟨ξ, hξ, hF⟩ := hρ (F.image φ) ε hε
  exact ⟨ξ, hξ, fun s hs ↦ hF (φ s) (Finset.mem_image_of_mem φ hs)⟩

end Normed

/-- A representation on a normed space with a nonzero invariant vector has almost invariant
vectors: the normalized invariant vector is moved by nothing. -/
theorem hasAlmostInvariantVectors_of_invariants_ne_bot {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] {ρ : ContRepresentation 𝕜 G V}
    (hρ : ρ.invariants ≠ ⊥) : ρ.HasAlmostInvariantVectors := by
  obtain ⟨ξ, hξ, hξ0⟩ := (Submodule.ne_bot_iff _).mp hρ
  refine fun F ε hε ↦ ⟨(‖ξ‖⁻¹ : 𝕜) • ξ, norm_smul_inv_norm hξ0, fun g _ ↦ ?_⟩
  rw [map_smul, (mem_invariants ξ).mp hξ g, sub_self, norm_zero]
  exact hε

end ContRepresentation

namespace Subgroup

/-- A subgroup `Λ` of a discrete group `Γ` has relative property (T) in `Γ` when every unitary
representation of `Γ` on a complex Hilbert space (in a fixed universe) with almost invariant
vectors has a nonzero `Λ`-invariant vector. Property (T) of `Γ` is the case `Λ = ⊤`. -/
def RelativePropertyT.{u', v'} {Γ : Type v'} [Group Γ] (Λ : Subgroup Γ) : Prop :=
  ∀ (H : Type u') [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary → ρ.HasAlmostInvariantVectors →
      (ρ.restrict Λ.subtype).invariants ≠ ⊥

/-- A pair `(F, δ)` of a finite set `F ⊆ Γ` and a real number `δ` is a Kazhdan pair for the
subgroup `Λ` when every unitary representation of `Γ` on a complex Hilbert space (in a fixed
universe) with a unit vector moved by less than `δ` by each element of `F` has a nonzero
`Λ`-invariant vector. -/
def IsKazhdanPair.{u', v'} {Γ : Type v'} [Group Γ] (Λ : Subgroup Γ) (F : Finset Γ) (δ : ℝ) :
    Prop :=
  ∀ (H : Type u') [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
      (∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) → (ρ.restrict Λ.subtype).invariants ≠ ⊥

open ContRepresentation

variable {Γ : Type v} [Group Γ]

/-- Unfolding lemma for `Subgroup.RelativePropertyT`. -/
theorem relativePropertyT_iff {Λ : Subgroup Γ} :
    Λ.RelativePropertyT.{u} ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary → ρ.HasAlmostInvariantVectors →
          (ρ.restrict Λ.subtype).invariants ≠ ⊥ :=
  Iff.rfl

/-- Unfolding lemma for `Subgroup.IsKazhdanPair`. -/
theorem isKazhdanPair_iff {Λ : Subgroup Γ} {F : Finset Γ} {δ : ℝ} :
    Λ.IsKazhdanPair.{u} F δ ↔
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (ρ : ContRepresentation ℂ Γ H), ρ.IsUnitary →
          (∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ F, ‖ρ g ξ - ξ‖ < δ) →
            (ρ.restrict Λ.subtype).invariants ≠ ⊥ :=
  Iff.rfl

/-- The trivial subgroup has relative property (T) in every group: a representation with almost
invariant vectors is nonzero, and every vector is invariant under the trivial subgroup. -/
theorem relativePropertyT_bot : (⊥ : Subgroup Γ).RelativePropertyT.{u} := by
  intro H _ _ _ ρ _ hρ
  obtain ⟨ξ, hξ⟩ := hρ.exists_norm_eq_one
  have : Nontrivial H := ⟨ξ, 0, fun h ↦ by simp [h] at hξ⟩
  simp

/-- Relative property (T) passes to smaller subgroups. -/
theorem RelativePropertyT.anti {Λ Λ' : Subgroup Γ} (hΛ : Λ.RelativePropertyT.{u})
    (hle : Λ' ≤ Λ) : Λ'.RelativePropertyT.{u} := by
  intro H _ _ _ ρ hu hρ
  obtain ⟨ξ, hξ, hξ0⟩ := (Submodule.ne_bot_iff _).mp (hΛ H ρ hu hρ)
  rw [mem_invariants_restrict] at hξ
  exact (Submodule.ne_bot_iff _).mpr
    ⟨ξ, mem_invariants_restrict.mpr fun s hs ↦ hξ s (hle hs), hξ0⟩

/-- Relative property (T) passes to images under group homomorphisms. For the inclusion of a
subgroup `Γ₀ ≤ Γ`, this says that relative property (T) of `Λ` in `Γ₀` gives relative property (T)
of `Λ` in `Γ`; for a quotient map, it gives relative property (T) of the image of `Λ` in the
quotient. -/
theorem RelativePropertyT.map {Λ : Subgroup Γ} (hΛ : Λ.RelativePropertyT.{u}) {Γ' : Type w}
    [Group Γ'] (φ : Γ →* Γ') : (Λ.map φ).RelativePropertyT.{u} := by
  intro H _ _ _ ρ hu hρ
  obtain ⟨ξ, hξ, hξ0⟩ :=
    (Submodule.ne_bot_iff _).mp (hΛ H (ρ.restrict φ) (hu.restrict φ) (hρ.restrict φ))
  rw [mem_invariants_restrict] at hξ
  refine (Submodule.ne_bot_iff _).mpr ⟨ξ, mem_invariants_restrict.mpr ?_, hξ0⟩
  rintro _ ⟨s, hs, rfl⟩
  exact hξ s hs

/-- A Kazhdan pair `(F, δ)` with `δ > 0` for `Λ` gives relative property (T) of `Λ`. -/
theorem IsKazhdanPair.relativePropertyT {Λ : Subgroup Γ} {F : Finset Γ} {δ : ℝ}
    (hΛ : Λ.IsKazhdanPair.{u} F δ) (hδ : 0 < δ) : Λ.RelativePropertyT.{u} :=
  fun H _ _ _ ρ hu hρ ↦ hΛ H ρ hu (hρ F δ hδ)

/-- In a finite group `Γ`, the pair `(Γ, 1)` is a Kazhdan pair for `⊤`: the sum over `Γ` of the
translates of a unit vector moved by less than `1` by every element is invariant and nonzero. -/
theorem isKazhdanPair_top_univ_one [Fintype Γ] :
    (⊤ : Subgroup Γ).IsKazhdanPair.{u} Finset.univ 1 := by
  rintro H _ _ _ ρ - ⟨ξ, hξ, hF⟩
  set η := ∑ g, ρ g ξ
  have hη : η ∈ (ρ.restrict (⊤ : Subgroup Γ).subtype).invariants := by
    refine mem_invariants_restrict.mpr fun h _ ↦ ?_
    calc ρ h η = ∑ g, ρ (h * g) ξ := by simp [η, map_mul, mul_apply_eq_comp]
      _ = η := Equiv.sum_comp (Equiv.mulLeft h) fun g ↦ ρ g ξ
  refine (Submodule.ne_bot_iff _).mpr ⟨η, hη, fun hη0 ↦ ?_⟩
  -- Comparing `η` with `|Γ| • ξ` shows that `η` is within less than `|Γ|` of a vector of norm
  -- `|Γ|`, so it cannot vanish.
  have hlt : ‖η - Fintype.card Γ • ξ‖ < Fintype.card Γ := by
    calc ‖η - Fintype.card Γ • ξ‖ = ‖∑ g, (ρ g ξ - ξ)‖ := by
          simp [η, Finset.sum_sub_distrib, Finset.card_univ]
      _ ≤ ∑ g, ‖ρ g ξ - ξ‖ := norm_sum_le _ _
      _ < ∑ _g : Γ, (1 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun g _ ↦ hF g (Finset.mem_univ g)
      _ = Fintype.card Γ := by simp
  simp [hη0, RCLike.norm_nsmul ℂ, hξ] at hlt

/-- Finite groups have property (T). -/
theorem relativePropertyT_top_of_finite [Finite Γ] : (⊤ : Subgroup Γ).RelativePropertyT.{u} := by
  have := Fintype.ofFinite Γ
  exact isKazhdanPair_top_univ_one.relativePropertyT one_pos

end Subgroup
