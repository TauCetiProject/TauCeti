/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants

/-!
# The descending filtration cut out by the powers of a linear character

Let `ρ` be a representation of a group `G` on a module `U` over a commutative ring `R`, and let
`ψ : G →* Rˣ` be a linear character. For a submodule `N ≤ U`, the **character step**
`ρ.charStep ψ N` is the submodule of those `u` with `ρ g u - ψ g • u ∈ N` for every `g`. When
`N` is `G`-stable it contains `N`, is again `G`-stable, and is the preimage of the
`ψ`-eigenspace of the quotient representation on `U ⧸ N`; for `N = ⊥` and the trivial character
it is `ρ.invariants`.

Iterating the step with the powers of a character `χ` from a top index `n` downwards gives the
**character filtration**: `ρ.charFiltration χ n i` is `⊥` for `n ≤ i`, and for `i < n` it is the
`χ ^ i`-step of the next term. It is a descending chain of subrepresentations
`0 = U_n ≤ U_(n-1) ≤ ... ≤ U_0 ≤ U`, and `G` acts on each graded piece `U_i ⧸ U_(i+1)` through
`χ ^ i`. The order matters: the term `U_i` is the largest submodule containing `U_(i+1)` on whose
quotient by `U_(i+1)` the group acts by `χ ^ i`, so the higher powers of `χ` are split off first.
Applied to the cyclotomic character of a Galois representation this is the filtration used by
Fontaine to show that a seven-adic crystalline representation of the absolute Galois group of `ℚ`
with Hodge–Tate weights in `[0, 3]`, unramified away from seven, is an iterated extension of
powers of the cyclotomic character; that exhaustiveness statement (`U_0 = U`) is arithmetic and
is not proved here. This file supplies the purely representation-theoretic construction, valid
for every coefficient ring, in particular for finite `ℤ ⧸ p ^ k`-modules and for vector spaces.

## Main definitions

* `Representation.charStep`: the preimage of the `ψ`-eigenspace modulo a submodule.
* `Representation.charFiltration`: the descending filtration by the steps of `χ ^ i`.

## Main results

* `Representation.mem_charStep`: membership is the family of congruences
  `ρ g u - ψ g • u ∈ N`.
* `Representation.le_charStep`, `Representation.charStep_le_comap`: for stable `N`, the step
  contains `N` and is stable.
* `Representation.charStep_eq_comap_mkQ`: the step is the preimage of the `ψ`-eigenspace of
  `U ⧸ N`.
* `Representation.charStep_one_bot`: the step of the trivial character over `⊥` is the invariant
  submodule.
* `Representation.comap_charStep`: steps pull back along intertwining maps.
* `Representation.charFiltration_of_lt`, `Representation.charFiltration_of_le`: the recursive
  description of the filtration.
* `Representation.charFiltration_antitone`, `Representation.charFiltration_le_comap`: the
  filtration is descending and consists of subrepresentations.
* `Representation.sub_mem_charFiltration_succ`: `G` acts on `U_i ⧸ U_(i+1)` through `χ ^ i`.
* `Representation.map_charFiltration_le`, `Representation.comap_charFiltration_of_injective`,
  `Representation.Equiv.map_charFiltration`: functoriality, restriction to subrepresentations
  and invariance under isomorphism.
* `Representation.charFiltration_eq_top_iff`: on a representation where `G` acts through the
  scalar character `χ ^ j`, the term `U_i` is everything exactly when `i ≤ j`, provided the
  differences `χ ^ k - χ ^ j` take a unit value for `j < k < n`.

## References

* J.-M. Fontaine, *Schémas propres et lisses sur Z*, Proceedings of the Indo-French Conference on
  Geometry (Bombay, 1989), Hindustan Book Agency (1993), 43–56; §§2.1–2.2.
-/

public section

namespace Representation

variable {R G U W : Type*} [CommRing R] [AddCommGroup U] [Module R U]
  [AddCommGroup W] [Module R W]

section Monoid

variable [Monoid G] (ρ : Representation R G U) (σ : Representation R G W)

/-- **The character step.** For a linear character `ψ` and a submodule `N`, the submodule of
those `u` with `ρ g u - ψ g • u ∈ N` for every `g : G`, the intersection over `g` of the
preimages of `N` under `ρ g - ψ g • id`. When `N` is `G`-stable it is the preimage of the
`ψ`-eigenspace of the quotient representation on `U ⧸ N` (`charStep_eq_comap_mkQ`). -/
def charStep (ψ : G →* Rˣ) (N : Submodule R U) : Submodule R U :=
  ⨅ g : G, N.comap (ρ g - (ψ g : R) • LinearMap.id)

variable {ρ} {ψ : G →* Rˣ} {N N' : Submodule R U} {u : U}

@[simp]
theorem mem_charStep : u ∈ ρ.charStep ψ N ↔ ∀ g : G, ρ g u - (ψ g : R) • u ∈ N := by
  simp [charStep, Submodule.mem_iInf]

variable (ρ ψ) in
theorem charStep_mono : Monotone (ρ.charStep ψ) :=
  fun _ _ h _ hu ↦ mem_charStep.2 fun g ↦ h (mem_charStep.1 hu g)

@[gcongr]
theorem charStep_le_charStep (h : N ≤ N') : ρ.charStep ψ N ≤ ρ.charStep ψ N' :=
  charStep_mono ρ ψ h

variable (ρ ψ) in
@[simp]
theorem charStep_top : ρ.charStep ψ ⊤ = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_charStep.2 fun _ ↦ Submodule.mem_top

/-- The step over `⊥` is the `ψ`-eigenspace: the vectors on which each `g` acts by `ψ g`. -/
theorem mem_charStep_bot : u ∈ ρ.charStep ψ ⊥ ↔ ∀ g : G, ρ g u = (ψ g : R) • u := by
  simp [sub_eq_zero]

/-- A `G`-stable submodule is contained in each of its character steps. -/
theorem le_charStep (hN : ∀ g, N ≤ N.comap (ρ g)) : N ≤ ρ.charStep ψ N :=
  fun _ hu ↦ mem_charStep.2 fun g ↦ N.sub_mem (hN g hu) (N.smul_mem _ hu)

/-- For a `G`-stable submodule `N`, the character step is the preimage in `U` of the
`ψ`-eigenspace of the quotient representation on `U ⧸ N`. -/
theorem charStep_eq_comap_mkQ (hN : ∀ g, N ≤ N.comap (ρ g)) :
    ρ.charStep ψ N = ((ρ.quotient N hN).charStep ψ ⊥).comap N.mkQ := by
  ext u
  simp [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub,
    Submodule.Quotient.mk_eq_zero]

/-- Character steps pull back along intertwining maps. -/
theorem comap_charStep (f : IntertwiningMap ρ σ) (N : Submodule R W) :
    (σ.charStep ψ N).comap f.toLinearMap = ρ.charStep ψ (N.comap f.toLinearMap) := by
  ext u
  simp [f.isIntertwining]

/-- An intertwining map carries a character step into the step of the image. -/
theorem map_charStep_le (f : IntertwiningMap ρ σ) (N : Submodule R U) :
    (ρ.charStep ψ N).map f.toLinearMap ≤ σ.charStep ψ (N.map f.toLinearMap) := by
  rw [Submodule.map_le_iff_le_comap, comap_charStep]
  exact charStep_mono ρ ψ (Submodule.le_comap_map _ _)

end Monoid

section Group

variable [Group G] {ρ : Representation R G U} {ψ : G →* Rˣ} {N : Submodule R U}

variable (ρ) in
/-- For the trivial character, the step over `⊥` is the invariant submodule. -/
@[simp]
theorem charStep_one_bot : ρ.charStep 1 ⊥ = ρ.invariants := by
  ext u
  simp [mem_invariants, sub_eq_zero]

/-- The character step of a `G`-stable submodule is `G`-stable. -/
theorem charStep_le_comap (hN : ∀ g, N ≤ N.comap (ρ g)) (h : G) :
    ρ.charStep ψ N ≤ (ρ.charStep ψ N).comap (ρ h) := by
  intro u hu
  refine mem_charStep.2 fun g ↦ ?_
  have hψ : ψ (h⁻¹ * g * h) = ψ g := by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have hρ : ρ h * ρ (h⁻¹ * g * h) = ρ g * ρ h := by
    rw [← map_mul, ← map_mul]
    group
  have key : ρ g (ρ h u) - (ψ g : R) • ρ h u =
      ρ h (ρ (h⁻¹ * g * h) u - (ψ (h⁻¹ * g * h) : R) • u) := by
    rw [map_sub, map_smul, hψ, ← mul_apply_eq_comp, ← mul_apply_eq_comp, hρ]
  rw [key]
  exact hN h (mem_charStep.1 hu _)

end Group

/-! ### The character filtration -/

section Filtration

variable [Monoid G] (ρ : Representation R G U) (σ : Representation R G W) (χ : G →* Rˣ)

/-- **The character filtration.** For a linear character `χ` and a top index `n`, the term of
index `i` is `⊥` for `n ≤ i`, and for `i < n` it is the `χ ^ i`-character step of the term of
index `i + 1`. Thus it is built downwards from `U_n = ⊥`, splitting off `χ ^ (n - 1)` first and
`χ ^ 0` last. -/
def charFiltration (n i : ℕ) : Submodule R U :=
  if i < n then ρ.charStep (χ ^ i) (charFiltration n (i + 1)) else ⊥
termination_by n - i

variable {n i : ℕ}

/-- Below the top index, `U_i` is the `χ ^ i`-character step of `U_(i+1)`. -/
theorem charFiltration_of_lt (h : i < n) :
    ρ.charFiltration χ n i = ρ.charStep (χ ^ i) (ρ.charFiltration χ n (i + 1)) := by
  rw [charFiltration]
  simp [h]

/-- From the top index on, every term of the character filtration is `⊥`. -/
theorem charFiltration_of_le (h : n ≤ i) : ρ.charFiltration χ n i = ⊥ := by
  rw [charFiltration]
  simp [not_lt.2 h]

@[simp]
theorem charFiltration_self : ρ.charFiltration χ n n = ⊥ :=
  ρ.charFiltration_of_le χ le_rfl

variable {ρ χ} in
/-- Membership in a term of the character filtration below the top index: `u ∈ U_i` exactly when
`ρ g u - χ g ^ i • u ∈ U_(i+1)` for every `g`. -/
theorem mem_charFiltration_of_lt (h : i < n) {u : U} :
    u ∈ ρ.charFiltration χ n i ↔
      ∀ g : G, ρ g u - (χ g : R) ^ i • u ∈ ρ.charFiltration χ n (i + 1) := by
  rw [charFiltration_of_lt ρ χ h, mem_charStep]
  simp

variable {ρ σ χ}

/-- An intertwining map carries each term of the character filtration into the corresponding
term. -/
theorem map_charFiltration_le (f : IntertwiningMap ρ σ) (n i : ℕ) :
    (ρ.charFiltration χ n i).map f.toLinearMap ≤ σ.charFiltration χ n i := by
  induction h : n - i generalizing i with
  | zero => simp [charFiltration_of_le _ _ (Nat.sub_eq_zero_iff_le.1 h)]
  | succ k ih =>
    have hi : i < n := by omega
    rw [charFiltration_of_lt _ _ hi, charFiltration_of_lt _ _ hi]
    exact (map_charStep_le σ f _).trans (charStep_mono σ _ (ih (i + 1) (by omega)))

/-- For an injective intertwining map, each term of the character filtration of the source is
the preimage of the corresponding term of the target. In particular the filtration of a
subrepresentation is the restriction of the filtration of the ambient representation. -/
theorem comap_charFiltration_of_injective (f : IntertwiningMap ρ σ)
    (hf : Function.Injective f) (n i : ℕ) :
    (σ.charFiltration χ n i).comap f.toLinearMap = ρ.charFiltration χ n i := by
  induction h : n - i generalizing i with
  | zero =>
    have hi : n ≤ i := Nat.sub_eq_zero_iff_le.1 h
    simp only [charFiltration_of_le _ _ hi, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.2 hf
  | succ k ih =>
    have hi : i < n := by omega
    rw [charFiltration_of_lt _ _ hi, charFiltration_of_lt _ _ hi, comap_charStep,
      ih (i + 1) (by omega)]

/-- An isomorphism of representations identifies the character filtrations term by term. -/
theorem Equiv.map_charFiltration (e : ρ.Equiv σ) (n i : ℕ) :
    (ρ.charFiltration χ n i).map e.toLinearEquiv.toLinearMap = σ.charFiltration χ n i := by
  rw [Submodule.map_equiv_eq_comap_symm, ← e.toLinearMap_symm]
  exact comap_charFiltration_of_injective e.symm.toIntertwiningMap e.symm.toLinearEquiv.injective
    n i

/-! ### Representations acting through a single power of the character -/

variable {j : ℕ}

/-- If `G` acts on `U` through the scalar character `χ ^ j`, and `χ ^ k - χ ^ j` takes a unit
value for each `i ≤ k < n`, then the term of index `i` of the character filtration vanishes. -/
theorem charFiltration_eq_bot_of_isUnit_sub (hρ : ∀ g u, ρ g u = (χ g : R) ^ j • u)
    (hχ : ∀ k, i ≤ k → k < n → ∃ g, IsUnit ((χ g : R) ^ k - (χ g : R) ^ j)) :
    ρ.charFiltration χ n i = ⊥ := by
  induction h : n - i generalizing i with
  | zero => exact charFiltration_of_le _ _ (Nat.sub_eq_zero_iff_le.1 h)
  | succ k ih =>
    have hi : i < n := by omega
    rw [charFiltration_of_lt _ _ hi, ih (fun k hk hkn ↦ hχ k (by omega) hkn) (by omega),
      eq_bot_iff]
    intro u hu
    obtain ⟨g, hg⟩ := hχ i le_rfl hi
    have hu' := mem_charStep_bot.1 hu g
    rw [hρ, MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at hu'
    rw [Submodule.mem_bot, ← hg.smul_left_cancel, smul_zero, sub_smul, ← hu', sub_self]

/-- If `G` acts on `U` through the scalar character `χ ^ j` with `j < n`, and `χ ^ k - χ ^ j`
takes a unit value for each `j < k < n`, then every term of the character filtration of index at
most `j` is all of `U`. -/
theorem charFiltration_eq_top_of_le (hρ : ∀ g u, ρ g u = (χ g : R) ^ j • u)
    (hχ : ∀ k, j < k → k < n → ∃ g, IsUnit ((χ g : R) ^ k - (χ g : R) ^ j)) (hjn : j < n)
    (hij : i ≤ j) : ρ.charFiltration χ n i = ⊤ := by
  induction h : j - i generalizing i with
  | zero =>
    obtain rfl : i = j := by omega
    rw [charFiltration_of_lt _ _ hjn, charFiltration_eq_bot_of_isUnit_sub hρ hχ, eq_top_iff]
    exact fun u _ ↦ mem_charStep_bot.2 fun g ↦ by simp [hρ]
  | succ k ih =>
    rw [charFiltration_of_lt _ _ (by omega), ih (by omega) (by omega), charStep_top]

/-- On a nonzero representation where `G` acts through the scalar character `χ ^ j` with
`j < n`, and `χ ^ k - χ ^ j` takes a unit value for each `j < k < n`, the term `U_i` of the
character filtration is all of `U` exactly when `i ≤ j`. Over a field the unit condition says
that `χ ^ k ≠ χ ^ j` for `j < k < n`. Over `ZMod 25` distinctness does not suffice: for the
character with value `6`, the powers `1, 6, 11, 16` are distinct but `6 ^ 3 - 6 = 210` is not a
unit. -/
theorem charFiltration_eq_top_iff [Nontrivial U] (hρ : ∀ g u, ρ g u = (χ g : R) ^ j • u)
    (hχ : ∀ k, j < k → k < n → ∃ g, IsUnit ((χ g : R) ^ k - (χ g : R) ^ j)) (hjn : j < n) :
    ρ.charFiltration χ n i = ⊤ ↔ i ≤ j := by
  refine ⟨fun h ↦ not_lt.1 fun hji ↦ ?_, charFiltration_eq_top_of_le hρ hχ hjn⟩
  rw [charFiltration_eq_bot_of_isUnit_sub hρ fun k hk hkn ↦ hχ k (hji.trans_le hk) hkn] at h
  exact bot_ne_top h

end Filtration

section GroupFiltration

variable [Group G] (ρ : Representation R G U) (χ : G →* Rˣ) {n i : ℕ}

/-- Each term of the character filtration is `G`-stable. -/
theorem charFiltration_le_comap (n i : ℕ) (g : G) :
    ρ.charFiltration χ n i ≤ (ρ.charFiltration χ n i).comap (ρ g) := by
  induction h : n - i generalizing i g with
  | zero => simp [charFiltration_of_le _ _ (Nat.sub_eq_zero_iff_le.1 h)]
  | succ k ih =>
    have hi : i < n := by omega
    rw [charFiltration_of_lt _ _ hi]
    exact charStep_le_comap (fun g ↦ ih (i + 1) g (by omega)) g

/-- Each term of the character filtration contains the next one. -/
theorem charFiltration_succ_le (n i : ℕ) :
    ρ.charFiltration χ n (i + 1) ≤ ρ.charFiltration χ n i := by
  rcases lt_or_ge i n with hi | hi
  · rw [charFiltration_of_lt _ _ hi]
    exact le_charStep (charFiltration_le_comap ρ χ n (i + 1))
  · simp [charFiltration_of_le _ _ (hi.trans (Nat.le_succ i))]

/-- The character filtration is descending. -/
theorem charFiltration_antitone (n : ℕ) : Antitone (ρ.charFiltration χ n) :=
  antitone_nat_of_succ_le (charFiltration_succ_le ρ χ n)

variable {ρ χ} in
/-- `G` acts on the graded piece `U_i ⧸ U_(i+1)` through `χ ^ i`. -/
theorem sub_mem_charFiltration_succ {u : U} (hu : u ∈ ρ.charFiltration χ n i) (g : G) :
    ρ g u - (χ g : R) ^ i • u ∈ ρ.charFiltration χ n (i + 1) := by
  rcases lt_or_ge i n with hi | hi
  · exact (mem_charFiltration_of_lt hi).1 hu g
  · rw [charFiltration_of_le _ _ hi] at hu
    rw [(Submodule.mem_bot R).1 hu]
    simp

/-- Below the top index, `U_i` is the preimage in `U` of the `χ ^ i`-eigenspace of the quotient
representation on `U ⧸ U_(i+1)`. -/
theorem charFiltration_eq_comap_mkQ (h : i < n) :
    ρ.charFiltration χ n i =
      ((ρ.quotient _ (charFiltration_le_comap ρ χ n (i + 1))).charStep (χ ^ i) ⊥).comap
        (ρ.charFiltration χ n (i + 1)).mkQ := by
  rw [charFiltration_of_lt _ _ h, charStep_eq_comap_mkQ]

end GroupFiltration

end Representation
