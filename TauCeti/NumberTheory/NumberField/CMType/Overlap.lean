/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Rat.Defs
public import TauCeti.NumberTheory.NumberField.CMType.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.Ring

/-!
# Overlap characters of CM types

For a CM type `Φ` on `E` and an automorphism `σ` of `ℂ`, the **overlap**
`a_Φ(σ) = #(Φ ∩ σΦ)` counts the embeddings that `Φ` shares with its translate
`σΦ = {σ ∘ φ : φ ∈ Φ}`. Its conjugacy average `a⁰_Φ` is a rational class function on `Aut(ℂ)`,
the class function through which Colmez expresses the Faltings height of an abelian variety with
complex multiplication of type `Φ`: the conjectural height `h_Col(E, Φ)` is obtained from `a⁰_Φ`
by expanding it in Artin characters and replacing each character by the logarithmic derivative of
its Artin L-function at `0`.

The action of `Aut(ℂ)` on the CM types of `E` has finite orbits when `E` has finitely many
complex embeddings, and we define `a⁰_Φ(σ)` as the mean of `a_Ψ(σ)` over the `Aut(ℂ)`-orbit of
`Φ`. Since `a_Φ(τστ⁻¹) = a_{τ⁻¹Φ}(σ)` (`TauCeti.CMType.overlap_conj`), this is the normalised
sum `|G|⁻¹ ∑_{τ ∈ G} a_Φ(τστ⁻¹)` over any finite Galois quotient `G` through which the action on
the embeddings factors (`TauCeti.CMType.averageOverlap_eq_inv_card_mul_sum`), without choosing
such a quotient in the definition.

## Main definitions

* `TauCeti.CMType.overlap Φ σ`: the overlap `a_Φ(σ) = #(Φ ∩ σΦ)`.
* `TauCeti.CMType.averageOverlap Φ σ`: its conjugacy average `a⁰_Φ(σ)`, the mean of `a_Ψ(σ)`
  over the `Aut(ℂ)`-orbit of `Φ`.

## Main results

* `TauCeti.CMType.overlap_eq_ncard`: `a_Φ(σ)` counts the `φ ∈ Φ` with `σ ∘ φ ∈ Φ`.
* `TauCeti.CMType.overlap_add_overlap_starRingAut_mul` and
  `TauCeti.CMType.averageOverlap_add_averageOverlap_starRingAut_mul`: the complement identity
  `a(σ) + a(cσ) = d` for complex conjugation `c` and `d = #Φ`.
* `TauCeti.CMType.overlap_inv`, `TauCeti.CMType.averageOverlap_inv`: invariance under
  `σ ↦ σ⁻¹`; `TauCeti.CMType.overlap_starRingAut`, `TauCeti.CMType.averageOverlap_starRingAut`:
  vanishing at `c`; `TauCeti.CMType.averageOverlap_one`: the value `d` at `1`.
* `TauCeti.CMType.averageOverlap_eq_inv_card_mul_sum`: `a⁰_Φ(σ)` is the normalised conjugacy
  sum `|G|⁻¹ ∑_{τ ∈ G} a_Φ(τστ⁻¹)` over any finite quotient `G` of `Aut(ℂ)` through which the
  action on the embeddings factors.
* `TauCeti.CMType.averageOverlap_conj`: `a⁰_Φ` is a class function, and
  `TauCeti.CMType.averageOverlap_smul`: it depends only on the orbit of `Φ`.
* `TauCeti.CMType.finsum_averageOverlap`: **the average CM character.** If `E` has `2d`
  complex embeddings and a CM type, then
  `∑_Φ a⁰_Φ(σ) = 2^(d-2) (2d + fix(σ) - swap(σ))`, the sum running over all `2^d` CM types,
  where `fix(σ)` counts the embeddings `φ` with `σ ∘ φ = φ` and `swap(σ)` those with
  `σ ∘ φ = conj ∘ φ`. For a CM field `E` with maximal real subfield `F`,
  `(fix(σ) - swap(σ)) / 2` is the value at `σ` of the character `Ind_F^ℚ χ_{E/F}` induced from the
  quadratic character of `E / F`, so this is the identity
  `(2d)⁻¹ ∑_Φ a⁰_Φ = 2^(d-2) (1 + d⁻¹ Ind χ_{E/F})`.

## References

* F. Andreatta, E. Z. Goren, B. Howard, K. Madapusi Pera, *Faltings heights of abelian varieties
  with complex multiplication*, Ann. of Math. 187 (2018), Definition 9.1.1 and Proposition 9.3.1.
* P. Colmez, *Périodes des variétés abéliennes à multiplication complexe*, Ann. of Math. 138
  (1993), §0.
-/

public section

namespace TauCeti

namespace CMType

open MulAction

variable {E : Type*} [CommRing E] [StarCompCommute E]

/-- Translating two CM types by the same automorphism of `ℂ` preserves the size of their
intersection. -/
private theorem ncard_smul_inter_smul (τ : RingAut ℂ) (Ψ₁ Ψ₂ : CMType E) :
    (((τ • Ψ₁ : CMType E) : Set (E →+* ℂ)) ∩ (τ • Ψ₂ : CMType E)).ncard =
      ((Ψ₁ : Set (E →+* ℂ)) ∩ Ψ₂).ncard := by
  have hinj : Function.Injective (RingHom.comp (τ : ℂ →+* ℂ) : (E →+* ℂ) → E →+* ℂ) :=
    fun φ ψ h ↦ RingHom.ext fun x ↦ τ.injective (RingHom.congr_fun h x)
  rw [coe_smul, coe_smul, ← Set.image_inter hinj, Set.ncard_image_of_injective _ hinj]

/-! ### The overlap -/

/-- The **overlap** `a_Φ(σ) = #(Φ ∩ σΦ)` of a CM type `Φ` with its translate
`σΦ = {σ ∘ φ : φ ∈ Φ}` by an automorphism `σ` of `ℂ`. -/
noncomputable def overlap (Φ : CMType E) (σ : RingAut ℂ) : ℕ :=
  ((Φ : Set (E →+* ℂ)) ∩ (σ • Φ : CMType E)).ncard

theorem overlap_def (Φ : CMType E) (σ : RingAut ℂ) :
    overlap Φ σ = ((Φ : Set (E →+* ℂ)) ∩ (σ • Φ : CMType E)).ncard :=
  (rfl)

/-- Translating the type conjugates the argument of its overlap:
`a_{τΦ}(σ) = a_Φ(τ⁻¹στ)`. -/
theorem overlap_smul (τ σ : RingAut ℂ) (Φ : CMType E) :
    overlap (τ • Φ) σ = overlap Φ (τ⁻¹ * σ * τ) := by
  have h : σ • τ • Φ = τ • (τ⁻¹ * σ * τ) • Φ := by simp [smul_smul, mul_assoc]
  rw [overlap_def, h, ncard_smul_inter_smul, overlap_def]

/-- The overlap at a conjugate is the overlap of a translated type:
`a_Φ(τστ⁻¹) = a_{τ⁻¹Φ}(σ)`. -/
theorem overlap_conj (τ σ : RingAut ℂ) (Φ : CMType E) :
    overlap Φ (τ * σ * τ⁻¹) = overlap (τ⁻¹ • Φ) σ := by
  rw [overlap_smul, inv_inv]

/-- The overlap is invariant under inversion: `a_Φ(σ⁻¹) = a_Φ(σ)`. -/
@[simp]
theorem overlap_inv (Φ : CMType E) (σ : RingAut ℂ) : overlap Φ σ⁻¹ = overlap Φ σ := by
  have h : ((Φ : Set (E →+* ℂ)) ∩ (σ⁻¹ • Φ : CMType E)) =
      ((σ⁻¹ • σ • Φ : CMType E) : Set (E →+* ℂ)) ∩ (σ⁻¹ • Φ : CMType E) := by
    rw [inv_smul_smul]
  rw [overlap_def, h, ncard_smul_inter_smul, Set.inter_comm, overlap_def]

/-- The overlap `a_Φ(σ)` counts the embeddings `φ ∈ Φ` with `σ ∘ φ ∈ Φ`. -/
theorem overlap_eq_ncard (Φ : CMType E) (σ : RingAut ℂ) :
    overlap Φ σ = {φ : E →+* ℂ | φ ∈ Φ ∧ (σ : ℂ →+* ℂ).comp φ ∈ Φ}.ncard := by
  -- `φ ∈ σ⁻¹ • Φ` unfolds to `σ ∘ φ ∈ Φ` (`TauCeti.CMType.mem_smul`).
  rw [← overlap_inv, overlap_def]
  congr 1

/-- The overlap at the identity is the number `d = #Φ` of embeddings in the type. -/
@[simp]
theorem overlap_one (Φ : CMType E) : overlap Φ 1 = Nat.card Φ := by
  rw [overlap_def, one_smul, Set.inter_self]
  exact (Nat.card_coe_set_eq _).symm

/-- The overlap vanishes at complex conjugation, which sends `Φ` to its complement. -/
@[simp]
theorem overlap_starRingAut (Φ : CMType E) : overlap Φ starRingAut = 0 := by
  simp [overlap_def]

/-- **The complement identity.** For complex conjugation `c`,
`a_Φ(σ) + a_Φ(cσ) = #Φ`: the type `cσΦ` is the complement of `σΦ`. -/
theorem overlap_add_overlap_starRingAut_mul [Finite (E →+* ℂ)] (Φ : CMType E)
    (σ : RingAut ℂ) : overlap Φ σ + overlap Φ (starRingAut * σ) = Nat.card Φ := by
  rw [overlap_def, overlap_def, mul_smul, starRingAut_smul, coe_star, ← Set.sdiff_eq,
    Set.ncard_inter_add_ncard_sdiff_eq_ncard]
  exact (Nat.card_coe_set_eq _).symm

/-- Complex conjugation commutes with every `σ` in the overlap: `a_Φ(σc) = a_Φ(cσ)`. -/
theorem overlap_mul_starRingAut (Φ : CMType E) (σ : RingAut ℂ) :
    overlap Φ (σ * starRingAut) = overlap Φ (starRingAut * σ) := by
  rw [overlap_def, overlap_def, mul_smul, mul_smul, starRingAut_smul, starRingAut_smul,
    star_smul]

/-! ### The conjugacy average -/

/-- The **conjugacy-averaged overlap** `a⁰_Φ(σ)`: the mean of `a_Ψ(σ)` over the CM types `Ψ` in
the `Aut(ℂ)`-orbit of `Φ`. This is the normalised conjugacy sum `|G|⁻¹ ∑_{τ ∈ G} a_Φ(τστ⁻¹)`
over any finite Galois quotient `G` of `Aut(ℂ)` through which the action on the embeddings of `E`
factors (`TauCeti.CMType.averageOverlap_eq_inv_card_mul_sum`). -/
noncomputable def averageOverlap (Φ : CMType E) (σ : RingAut ℂ) : ℚ :=
  (∑ᶠ Ψ ∈ orbit (RingAut ℂ) Φ, (overlap Ψ σ : ℚ)) / (orbit (RingAut ℂ) Φ).ncard

/-- The `Aut(ℂ)`-orbit of a CM type is a nonempty finite set. -/
private theorem ncard_orbit_ne_zero [Finite (E →+* ℂ)] (Φ : CMType E) :
    ((orbit (RingAut ℂ) Φ).ncard : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Set.ncard_ne_zero_of_mem (mem_orbit_self Φ))

theorem averageOverlap_def (Φ : CMType E) (σ : RingAut ℂ) :
    averageOverlap Φ σ =
      (∑ᶠ Ψ ∈ orbit (RingAut ℂ) Φ, (overlap Ψ σ : ℚ)) / (orbit (RingAut ℂ) Φ).ncard :=
  (rfl)

/-- The averaged overlap depends only on the orbit of the type: `a⁰_{τΦ} = a⁰_Φ`. -/
@[simp]
theorem averageOverlap_smul (τ : RingAut ℂ) (Φ : CMType E) (σ : RingAut ℂ) :
    averageOverlap (τ • Φ) σ = averageOverlap Φ σ := by
  rw [averageOverlap_def, orbit_smul, averageOverlap_def]

/-- The averaged overlap is a class function: `a⁰_Φ(τστ⁻¹) = a⁰_Φ(σ)`. -/
@[simp]
theorem averageOverlap_conj (τ σ : RingAut ℂ) (Φ : CMType E) :
    averageOverlap Φ (τ * σ * τ⁻¹) = averageOverlap Φ σ := by
  rw [averageOverlap_def, averageOverlap_def]
  congr 1
  -- Translation by `τ⁻¹` permutes the orbit, and `a_Ψ(τστ⁻¹) = a_{τ⁻¹Ψ}(σ)`.
  have h := (MulAction.injective τ⁻¹).injOn.bijOn_image (s := orbit (RingAut ℂ) Φ)
  rw [Set.image_smul, smul_orbit] at h
  exact finsum_mem_eq_of_bijOn _ h fun Ψ _ ↦ by rw [overlap_conj]

/-- **The conjugacy average over a finite Galois quotient.** Let `π` map `Aut(ℂ)` to a finite
group `G` such that every automorphism in the kernel of `π` fixes each embedding of `E`, and let
`s g` be a lift of each `g ∈ G`. Then `a⁰_Φ(σ) = |G|⁻¹ ∑_{g ∈ G} a_Φ(s(g) σ s(g)⁻¹)`. In
particular the right side does not depend on the choice of the quotient `G` or of the lifts. -/
theorem averageOverlap_eq_inv_card_mul_sum {G : Type*} [Group G] [Fintype G]
    (π : RingAut ℂ →* G) (hπ : ∀ τ, π τ = 1 → ∀ φ : E →+* ℂ, (τ : ℂ →+* ℂ).comp φ = φ)
    {s : G → RingAut ℂ} (hs : ∀ g, π (s g) = g) (Φ : CMType E) (σ : RingAut ℂ) :
    averageOverlap Φ σ =
      (Nat.card G : ℚ)⁻¹ * ∑ g, (overlap Φ (s g * σ * (s g)⁻¹) : ℚ) := by
  classical
  -- The action of `τ` on CM types depends only on `π τ`.
  have hact {τ τ' : RingAut ℂ} (h : π τ = π τ') (Ψ : CMType E) : τ • Ψ = τ' • Ψ := by
    have hκ : π (τ⁻¹ * τ')⁻¹ = 1 := by simp [h]
    rw [smul_eq_iff_eq_inv_smul, smul_smul]
    ext ψ
    rw [mem_smul, show ((τ⁻¹ * τ').symm : ℂ →+* ℂ).comp ψ = ψ from hπ _ hκ ψ]
  -- Hence the orbit of `Φ` is the finite set of the `s(g)⁻¹ Φ`.
  have hfin : (orbit (RingAut ℂ) Φ).Finite := (Set.finite_range fun g ↦ (s g)⁻¹ • Φ).subset <| by
    rintro _ ⟨τ, rfl⟩
    exact ⟨π τ⁻¹, hact (by simp [hs]) Φ⟩
  -- The sum over `G` is the same for every type `Ψ` in the orbit.
  have hinv : ∀ Ψ ∈ hfin.toFinset, ∑ g, (overlap ((s g)⁻¹ • Ψ) σ : ℚ) =
      ∑ g, (overlap ((s g)⁻¹ • Φ) σ : ℚ) := by
    rintro _ hΨ
    obtain ⟨τ, rfl⟩ := hfin.mem_toFinset.mp hΨ
    exact Fintype.sum_equiv (Equiv.mulLeft (π τ)⁻¹) _ _ fun g ↦ by
      rw [Equiv.coe_mulLeft, smul_smul, hact (τ' := (s ((π τ)⁻¹ * g))⁻¹) (by simp [hs])]
  -- Each `s(g)⁻¹` permutes the orbit.
  have hperm (g : G) : ∑ Ψ ∈ hfin.toFinset, (overlap ((s g)⁻¹ • Ψ) σ : ℚ) =
      ∑ Ψ ∈ hfin.toFinset, (overlap Ψ σ : ℚ) := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hfin, ← finsum_mem_eq_finite_toFinset_sum _ hfin]
    have h := (MulAction.injective (s g)⁻¹).injOn.bijOn_image (s := orbit (RingAut ℂ) Φ)
    rw [Set.image_smul, smul_orbit] at h
    exact finsum_mem_eq_of_bijOn _ h fun _ _ ↦ rfl
  -- Summing `∑_g a_{s(g)⁻¹Ψ}(σ)` over the orbit in both orders.
  have key : (hfin.toFinset.card : ℚ) * ∑ g, (overlap ((s g)⁻¹ • Φ) σ : ℚ) =
      Nat.card G * ∑ Ψ ∈ hfin.toFinset, (overlap Ψ σ : ℚ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_congr rfl hinv, Finset.sum_comm,
      Finset.sum_congr rfl fun g _ ↦ hperm g, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hO : (hfin.toFinset.card : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem (hfin.mem_toFinset.mpr (mem_orbit_self Φ)))
  have hG : (Nat.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp_rw [overlap_conj]
  rw [averageOverlap_def, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Set.ncard_eq_toFinset_card _ hfin, eq_inv_mul_iff_mul_eq₀ hG, mul_div_assoc', div_eq_iff hO,
    ← key, mul_comm]

/-- The averaged overlap is invariant under inversion: `a⁰_Φ(σ⁻¹) = a⁰_Φ(σ)`. -/
@[simp]
theorem averageOverlap_inv (Φ : CMType E) (σ : RingAut ℂ) :
    averageOverlap Φ σ⁻¹ = averageOverlap Φ σ := by
  simp only [averageOverlap_def, overlap_inv]

/-- The averaged overlap vanishes at complex conjugation. -/
@[simp]
theorem averageOverlap_starRingAut (Φ : CMType E) : averageOverlap Φ starRingAut = 0 := by
  simp [averageOverlap_def]

/-- **The complement identity** for the averaged overlap: `a⁰_Φ(σ) + a⁰_Φ(cσ) = #Φ`. -/
theorem averageOverlap_add_averageOverlap_starRingAut_mul [Finite (E →+* ℂ)] (Φ : CMType E)
    (σ : RingAut ℂ) :
    averageOverlap Φ σ + averageOverlap Φ (starRingAut * σ) = Nat.card Φ := by
  rw [averageOverlap_def, averageOverlap_def, ← add_div, ← finsum_mem_add_distrib (Set.toFinite _),
    div_eq_iff (ncard_orbit_ne_zero Φ)]
  calc ∑ᶠ Ψ ∈ orbit (RingAut ℂ) Φ, ((overlap Ψ σ : ℚ) + overlap Ψ (starRingAut * σ))
      = ∑ᶠ Ψ ∈ orbit (RingAut ℂ) Φ, (Nat.card Φ : ℚ) := finsum_mem_congr rfl fun Ψ _ ↦ by
        rw [← card_eq_card Ψ Φ, ← overlap_add_overlap_starRingAut_mul Ψ σ, Nat.cast_add]
    _ = Nat.card Φ * (orbit (RingAut ℂ) Φ).ncard := by
        rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_const,
          ← Set.ncard_eq_toFinset_card _, nsmul_eq_mul, mul_comm]

/-- The averaged overlap at the identity is `d = #Φ`. -/
@[simp]
theorem averageOverlap_one [Finite (E →+* ℂ)] (Φ : CMType E) :
    averageOverlap Φ 1 = Nat.card Φ := by
  simpa using averageOverlap_add_averageOverlap_starRingAut_mul Φ 1

/-! ### The average over all CM types -/

/-- Averaging over orbits does not change the total over all CM types:
`∑_Φ a⁰_Φ(σ) = ∑_Φ a_Φ(σ)`. -/
theorem finsum_averageOverlap_eq_finsum_overlap [Finite (E →+* ℂ)] (σ : RingAut ℂ) :
    ∑ᶠ Φ : CMType E, averageOverlap Φ σ = ∑ᶠ Φ : CMType E, (overlap Φ σ : ℚ) := by
  classical
  have := Fintype.ofFinite (CMType E)
  -- Write `a⁰_Φ(σ)` as a sum over all types `Ψ`, weighted by `[Ψ ∈ OΦ] / |OΨ|`, and exchange
  -- the two sums: each `Ψ` lies in the `|OΨ|` orbits `OΦ` with `Φ ∈ OΨ`.
  have key (Φ : CMType E) : averageOverlap Φ σ = ∑ Ψ : CMType E,
      if Φ ∈ orbit (RingAut ℂ) Ψ then (overlap Ψ σ : ℚ) / (orbit (RingAut ℂ) Ψ).ncard
      else 0 := by
    rw [averageOverlap_def, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      Finset.sum_div, ← Finset.sum_filter]
    refine Finset.sum_congr (by ext; simp [mem_orbit_symm]) fun Ψ hΨ ↦ ?_
    rw [orbit_eq_iff.mpr (by simpa using hΨ)]
  have hcount (Ψ : CMType E) :
      (Finset.univ.filter (· ∈ orbit (RingAut ℂ) Ψ)).card = (orbit (RingAut ℂ) Ψ).ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext
    simp
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Ψ _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount,
    mul_div_cancel₀ _ (ncard_orbit_ne_zero Ψ)]

omit [StarCompCommute E] in
open scoped Classical in
/-- The number of CM types containing two embeddings `φ` and `ψ`, uniformly in the relative
position of `ψ`: a quarter of all types when `ψ ∉ {φ, star φ}`, half when `ψ = φ`, none when
`ψ = star φ`. -/
private theorem four_mul_ncard_mem_and_mem_eq [Finite (E →+* ℂ)] (Φ : CMType E)
    (φ ψ : E →+* ℂ) :
    (4 * {Ψ : CMType E | φ ∈ Ψ ∧ ψ ∈ Ψ}.ncard : ℚ) =
      2 ^ Nat.card Φ * (1 + (if ψ = φ then 1 else 0) - (if ψ = star φ then 1 else 0)) := by
  have hN : (2 : ℚ) ^ Nat.card Φ = Nat.card (CMType E) := by
    rw [Φ.card_eq_two_pow]
    norm_cast
  rw [hN]
  by_cases h₁ : ψ = φ
  · subst h₁
    have h := two_mul_ncard_mem (E := E) ψ
    simp only [and_self, (Φ.ringHom_star_ne_self ψ).symm, ↓reduceIte]
    rw [← h]
    push_cast
    ring
  · by_cases h₂ : ψ = star φ
    · subst h₂
      simp [h₁]
    · simp only [h₁, h₂, ↓reduceIte]
      rw [← four_mul_ncard_mem_and_mem h₁ h₂]
      push_cast
      ring

/-- The total overlap `∑_Φ a_Φ(σ)` over all `2^d` CM types of a ring with `2d` complex
embeddings, in terms of the number `fix(σ)` of embeddings fixed by `σ` and the number
`swap(σ)` of embeddings that `σ` sends to their conjugate. -/
theorem finsum_overlap [Finite (E →+* ℂ)] [Nonempty (CMType E)] {d : ℕ}
    (hd : Nat.card (E →+* ℂ) = 2 * d) (σ : RingAut ℂ) :
    ∑ᶠ Φ : CMType E, (overlap Φ σ : ℚ) =
      2 ^ d / 4 * (2 * d + Nat.card {φ : E →+* ℂ // (σ : ℂ →+* ℂ).comp φ = φ} -
        Nat.card {φ : E →+* ℂ // (σ : ℂ →+* ℂ).comp φ = star φ}) := by
  classical
  obtain ⟨Φ⟩ := ‹Nonempty (CMType E)›
  have hΦ : Nat.card Φ = d := by
    have := Φ.card_ringHom_eq_two_mul
    omega
  have := Fintype.ofFinite (CMType E)
  have := Fintype.ofFinite (E →+* ℂ)
  -- Count the pairs `(Ψ, φ)` with `φ ∈ Ψ` and `σ ∘ φ ∈ Ψ` embedding by embedding.
  have hcount (Ψ : CMType E) : (overlap Ψ σ : ℚ) =
      ∑ φ : E →+* ℂ, if φ ∈ Ψ ∧ (σ : ℂ →+* ℂ).comp φ ∈ Ψ then 1 else 0 := by
    rw [overlap_eq_ncard, Set.ncard_eq_toFinset_card', Finset.sum_boole]
    simp
  have hcount' (φ : E →+* ℂ) :
      (∑ Ψ : CMType E, if φ ∈ Ψ ∧ (σ : ℂ →+* ℂ).comp φ ∈ Ψ then (1 : ℚ) else 0) =
        2 ^ d / 4 * (1 + (if (σ : ℂ →+* ℂ).comp φ = φ then 1 else 0) -
          (if (σ : ℂ →+* ℂ).comp φ = star φ then 1 else 0)) := by
    rw [Finset.sum_boole, ← hΦ, div_mul_eq_mul_div, ← four_mul_ncard_mem_and_mem_eq Φ,
      Set.ncard_eq_toFinset_card']
    simp
  rw [finsum_eq_sum_of_fintype]
  simp_rw [hcount]
  rw [Finset.sum_comm]
  simp_rw [hcount']
  rw [← Finset.mul_sum]
  rw [Nat.card_eq_fintype_card] at hd
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_boole, Nat.card_eq_fintype_card,
    Fintype.card_subtype, hd]

/-- **The average CM character.** For a ring `E` with `2d` complex embeddings and a CM type,
such as a CM field of degree `2d`, the averaged overlaps of all `2^d` CM types sum to
`2^(d-2) (2d + fix(σ) - swap(σ))`, where `fix(σ)` counts the embeddings `φ` with `σ ∘ φ = φ` and
`swap(σ)` those with `σ ∘ φ = conj ∘ φ`. For a CM field `E` with maximal real subfield `F`,
`(fix(σ) - swap(σ)) / 2` is the induced character `Ind_F^ℚ χ_{E/F}` at `σ`, so this reads
`(2d)⁻¹ ∑_Φ a⁰_Φ = 2^(d-2) (1 + d⁻¹ Ind χ_{E/F})`. -/
theorem finsum_averageOverlap [Finite (E →+* ℂ)] [Nonempty (CMType E)] {d : ℕ}
    (hd : Nat.card (E →+* ℂ) = 2 * d) (σ : RingAut ℂ) :
    ∑ᶠ Φ : CMType E, averageOverlap Φ σ =
      2 ^ d / 4 * (2 * d + Nat.card {φ : E →+* ℂ // (σ : ℂ →+* ℂ).comp φ = φ} -
        Nat.card {φ : E →+* ℂ // (σ : ℂ →+* ℂ).comp φ = star φ}) := by
  rw [finsum_averageOverlap_eq_finsum_overlap, finsum_overlap hd]

end CMType

end TauCeti
