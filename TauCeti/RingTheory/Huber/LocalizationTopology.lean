/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import TauCeti.RingTheory.Huber.Basic

/-!
# Localization Topology for Huber Rings

We construct the non-archimedean ring topology on `Localization.Away s` following §8.1 of
Wedhorn's *Adic Spaces*.

## Main definitions

* `divByS t s` : The element `t/s` in `Localization.Away s`.
* `locSubring P T s` : The ring of definition `D = A₀[t₁/s, …, tₙ/s]`.
* `locIdeal P T s` : The ideal of definition `J = I · D` in `D`.
* `locNhd P T s n` : The `n`-th neighborhood `image(Jⁿ)` in `Aₛ`.

## Main results

* `locNhd_antitone`: Neighborhoods are antitone.
* `locNhd_preimage_eq_locIdeal_pow`: Connects localization topology to adic topology.
* `locNhd_mul_subset` and `locNhd_leftMul`: The two multiplicative compatibilities the subgroup
  basis needs.
* `locBasis`: The neighborhoods form a `RingSubgroupsBasis`, so they are the zero-neighbourhood
  basis of a ring topology on `Aₛ`.

## Provenance

This is a port of AINTLIB's `LocalizationTopology.lean` (branch `dev/adic-spaces`). The main
changes are:
- Adapted `PairOfDefinition` field names to TauCeti conventions
  (`A₀`→`ringOfDefinition`, `I`→`ideal`, etc.)
- Uses TauCeti's module system and namespace structure
- Uses characteristic lemmas instead of destructuring definitions
- Removed unused hypotheses to satisfy `#lint` checks

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.51, §8.1
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`
-/

open Pointwise

namespace TauCeti.Huber

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### The ring of definition `D` -/

/-- The element `t/s` in `Localization.Away s`. -/
noncomputable def divByS (t s : A) : Localization.Away s :=
  IsLocalization.mk' (Localization.Away s) t
    (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s)

omit [TopologicalSpace A] in
/-- When `s = 1`, the fraction `t/1` equals `algebraMap t`. -/
theorem divByS_eq_algebraMap (t : A) :
    divByS t (1 : A) = algebraMap A (Localization.Away (1 : A)) t := by
  unfold divByS
  exact IsLocalization.mk'_one (M := Submonoid.powers (1 : A))
    (S := Localization.Away (1 : A)) t

/-- **Clearing the denominator**: `s · (t/s) = t` in `Localization.Away s`. -/
theorem algebraMap_mul_divByS {R : Type*} [CommRing R] (t s : R) :
    algebraMap R (Localization.Away s) s * divByS t s =
      algebraMap R (Localization.Away s) t := by
  unfold divByS
  exact IsLocalization.mk'_spec' (Localization.Away s) t
    (⟨s, ⟨1, pow_one s⟩⟩ : Submonoid.powers s)

/-- The ring of definition `D = A₀[t₁/s, …, tₙ/s]` of `Localization.Away s`. -/
noncomputable def locSubring (P : PairOfDefinition A) (T : Finset A)
    (s : A) : Subring (Localization.Away s) :=
  Subring.closure
    ((algebraMap A (Localization.Away s)) '' (P.ringOfDefinition : Set A) ∪
     Set.range (fun t : T ↦ divByS (t : A) s))

/-- The image of `A₀` under `algebraMap` is contained in `D`. -/
theorem algebraMap_ringOfDefinition_subset_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) :
    (algebraMap A (Localization.Away s)) '' (P.ringOfDefinition : Set A) ⊆
      (locSubring P T s : Set (Localization.Away s)) :=
  Set.subset_union_left.trans Subring.subset_closure

/-- Each element `t/s` (for `t ∈ T`) belongs to `D`. -/
theorem divByS_mem_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) {t : A} (ht : t ∈ T) :
    divByS t s ∈ locSubring P T s :=
  Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)

/-- An element of `A₀` maps into `D` under `algebraMap`. -/
theorem algebraMap_mem_locSubring (P : PairOfDefinition A)
    (T : Finset A) (s : A) {a : A} (ha : a ∈ P.ringOfDefinition) :
    algebraMap A (Localization.Away s) a ∈ locSubring P T s :=
  algebraMap_ringOfDefinition_subset_locSubring P T s ⟨a, ha, rfl⟩

/-! ### The ideal of definition `J` -/

/-- The ring homomorphism `A₀ →+* D` induced by `algebraMap`. -/
noncomputable def algebraMapD (P : PairOfDefinition A) (T : Finset A)
    (s : A) : P.ringOfDefinition →+* (locSubring P T s) :=
  ((algebraMap A (Localization.Away s)).comp P.ringOfDefinition.subtype).codRestrict
    (locSubring P T s)
    (fun a ↦ algebraMap_ringOfDefinition_subset_locSubring P T s ⟨a, a.property, rfl⟩)

/-- The ideal of definition `J = I · D` in `D`. -/
noncomputable def locIdeal (P : PairOfDefinition A) (T : Finset A)
    (s : A) : Ideal (locSubring P T s) :=
  Ideal.map (algebraMapD P T s) P.ideal

/-! ### The neighborhood basis -/

/-- The `n`-th neighborhood of `0` in `Localization.Away s`. -/
noncomputable def locNhd (P : PairOfDefinition A) (T : Finset A) (s : A)
    (n : ℕ) : AddSubgroup (Localization.Away s) :=
  ((locIdeal P T s) ^ n).toAddSubgroup.map
    (locSubring P T s).subtype.toAddMonoidHom

/-- The neighborhoods are antitone. -/
theorem locNhd_antitone (P : PairOfDefinition A) (T : Finset A) (s : A) :
    Antitone (locNhd P T s) :=
  fun _ _ h ↦ AddSubgroup.map_mono (Submodule.toAddSubgroup_mono (Ideal.pow_le_pow_right h))

/-- `0 ∈ locNhd n` for all `n`. -/
theorem zero_mem_locNhd (P : PairOfDefinition A) (T : Finset A) (s : A)
    (n : ℕ) : (0 : Localization.Away s) ∈ locNhd P T s n :=
  ⟨0, (locIdeal P T s ^ n).zero_mem, map_zero _⟩

/-- The preimage of `locNhd n` under the subtype embedding equals `locIdeal^n`. -/
theorem locNhd_preimage_eq_locIdeal_pow (P : PairOfDefinition A) (T : Finset A)
    (s : A) (n : ℕ) :
    (locSubring P T s).subtype ⁻¹' (locNhd P T s n : Set (Localization.Away s)) =
      ((locIdeal P T s) ^ n : Ideal (locSubring P T s)) := by
  ext d
  constructor
  · rintro ⟨d', hd', heq⟩
    exact (Subtype.val_injective heq) ▸ hd'
  · intro hd
    exact ⟨d, hd, rfl⟩

/-- The ideal of definition `J` is finitely generated. -/
theorem locIdeal_fg (P : PairOfDefinition A) (T : Finset A) (s : A) :
    (locIdeal P T s).FG :=
  P.fg_ideal.map _

/-- Products of the `n`-th neighbourhood land in the `n`-th neighbourhood: this is the
multiplicative half of the subgroup basis. -/
theorem locNhd_mul_subset (P : PairOfDefinition A) (T : Finset A) (s : A) (i : ℕ) :
    (locNhd P T s i : Set (Localization.Away s)) * (locNhd P T s i : Set (Localization.Away s))
      ⊆ (locNhd P T s i : Set (Localization.Away s)) := by
  rintro _ ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨d₂, hd₂, rfl⟩, rfl⟩
  exact ⟨d₁ * d₂, Ideal.pow_le_pow_right (Nat.le_add_left i i)
    (pow_add (locIdeal P T s) i i ▸ Ideal.mul_mem_mul hd₁ hd₂), MulMemClass.coe_mul ..⟩

/-- Multiplying `1/s` by an element of `Jᴺ` lands back in `D`, once `N` is large enough that
`b/s ∈ D` for every `b ∈ Iᴺ`. -/
private theorem locNhd_invS_mem (P : PairOfDefinition A) (T : Finset A) (s : A) (N : ℕ)
    (hN : ∀ b : P.ringOfDefinition, b ∈ P.ideal ^ N → divByS (↑b : A) s ∈ locSubring P T s)
    {d : locSubring P T s} (hd : d ∈ locIdeal P T s ^ N) :
    divByS 1 s * ↑d ∈ locSubring P T s := by
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.ideal ^ N), Ideal.map_span] at hd
  refine Submodule.span_induction (p := fun d _ ↦ divByS 1 s * ↑d ∈ locSubring P T s)
    ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    -- `algebraMapD` is a codomain restriction of `algebraMap`, so its value coerces to that map
    change divByS 1 s * algebraMap A _ ↑b ∈ _
    rw [show divByS 1 s * algebraMap A (Localization.Away s) ↑b = divByS (↑b) s by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers s) (S := Localization.Away s)
        (↑b : A), ← IsLocalization.mk'_mul, one_mul, mul_one]]
    exact hN b hb
  · simp [(locSubring P T s).zero_mem]
  · intro d₁ d₂ _ _ h₁ h₂
    simp only [AddMemClass.coe_add, mul_add]
    exact (locSubring P T s).add_mem h₁ h₂
  · intro r d₁ _ h₁
    rw [show (↑(r • d₁) : Localization.Away s) = ↑r * ↑d₁ from MulMemClass.coe_mul ..,
      mul_left_comm]
    exact (locSubring P T s).mul_mem r.property h₁

/-- Multiplying `1/s` by an element of `locNhd (n + N)` lands in `locNhd n`, once `N` is large
enough that `b/s ∈ D` for every `b ∈ Iᴺ`. -/
private theorem locNhd_invS_step (P : PairOfDefinition A) (T : Finset A) (s : A) (N : ℕ)
    (hN : ∀ b : P.ringOfDefinition, b ∈ P.ideal ^ N → divByS (↑b : A) s ∈ locSubring P T s)
    (n : ℕ) (y : Localization.Away s) (hy : y ∈ locNhd P T s (n + N)) :
    divByS 1 s * y ∈ locNhd P T s n := by
  obtain ⟨d, hd, rfl⟩ := hy
  -- `locNhd` is an image, so `y` is literally the coercion of the witness `d`
  change divByS 1 s * ↑d ∈ locNhd P T s n
  rw [Nat.add_comm, pow_add] at hd
  refine Submodule.mul_induction_on hd ?_ ?_
  · intro a ha b hb
    -- expose the product `(1/s * a) * b`, whose left factor lands in `D` by `locNhd_invS_mem`
    change divByS 1 s * (↑a * ↑b) ∈ locNhd P T s n
    rw [← mul_assoc]
    exact ⟨⟨divByS 1 s * ↑a, locNhd_invS_mem P T s N hN ha⟩ * b, Ideal.mul_mem_left _ _ hb,
      MulMemClass.coe_mul ..⟩
  · intro y₁ y₂ h₁ h₂
    simp only [AddMemClass.coe_add, mul_add]
    exact (locNhd P T s n).add_mem h₁ h₂

/-- Multiplying `algebraMap a` by an element of a suitable `locNhd j` lands in `locNhd i`. -/
private theorem locNhd_algMap_step [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A)
    (s : A) (i : ℕ) (a : A) :
    ∃ j, ∀ y ∈ locNhd P T s j, algebraMap A (Localization.Away s) a * y ∈ locNhd P T s i := by
  obtain ⟨m₀, -, hm₀⟩ := P.hasBasis_nhds_zero.mem_iff.mp
    (continuous_const_mul a |>.continuousAt.preimage_mem_nhds
      (by rw [mul_zero]; exact P.hasBasis_nhds_zero.mem_of_mem trivial (i := i)))
  refine ⟨m₀, ?_⟩
  rintro y ⟨d, hd, rfl⟩
  -- `locNhd` is an image, so `y` is literally the coercion of the witness `d`
  change algebraMap A (Localization.Away s) a * ↑d ∈ locNhd P T s i
  rw [locIdeal, ← Ideal.map_pow, ← Ideal.span_eq (P.ideal ^ m₀), Ideal.map_span] at hd
  refine Submodule.span_induction (p := fun d _ ↦
    algebraMap A (Localization.Away s) a * ↑d ∈ locNhd P T s i) ?_ ?_ ?_ ?_ hd
  · rintro d ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hval⟩ := (P.mem_idealImage i).mp (hm₀ ((P.mem_idealImage m₀).mpr ⟨b, hb, rfl⟩))
    -- `algebraMapD` is a codomain restriction of `algebraMap`, so its value coerces to that map
    change algebraMap A _ a * algebraMap A _ ↑b ∈ _
    rw [← map_mul, show a * (↑b : A) = ↑c from hval.symm]
    exact ⟨algebraMapD P T s c,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hc, rfl⟩
  · simp [(locNhd P T s i).zero_mem]
  · intro d₁ d₂ _ _ h₁ h₂
    simp only [AddMemClass.coe_add, mul_add]
    exact (locNhd P T s i).add_mem h₁ h₂
  · intro r d₁ _ h₁
    rw [show (↑(r • d₁) : Localization.Away s) = ↑r * ↑d₁ from MulMemClass.coe_mul ..,
      mul_left_comm]
    obtain ⟨e, he, he_eq⟩ := h₁
    exact ⟨r * e, Ideal.mul_mem_left _ r he,
      congrArg ((↑r : Localization.Away s) * ·) he_eq⟩

/-- **Left multiplication is continuous** for the localization topology: multiplication by a
fixed `x` pulls some neighbourhood `locNhd j` back inside `locNhd i`. -/
theorem locNhd_leftMul [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.ringOfDefinition, b ∈ P.ideal ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (x : Localization.Away s) (i : ℕ) :
    ∃ j, (locNhd P T s j : Set (Localization.Away s)) ⊆
      (x * ·) ⁻¹' (locNhd P T s i : Set (Localization.Away s)) := by
  obtain ⟨N, hN⟩ := hopen
  induction x using Localization.induction_on with
  | H p =>
    obtain ⟨a, ⟨_, k, rfl⟩⟩ := p
    induction k generalizing a with
    | zero =>
      simp only [pow_zero]
      obtain ⟨j, hj⟩ := locNhd_algMap_step P T s i a
      exact ⟨j, fun _ hy ↦ hj _ hy⟩
    | succ k ih =>
      have hk₁ : s ^ (k + 1) ∈ Submonoid.powers s := ⟨k + 1, rfl⟩
      have hk : s ^ k ∈ Submonoid.powers s := ⟨k, rfl⟩
      have hdecomp : Localization.mk a ⟨s ^ (k + 1), hk₁⟩ =
          Localization.mk a ⟨s ^ k, hk⟩ * divByS 1 s := by
        rw [divByS, ← Localization.mk_eq_mk', Localization.mk_mul, mul_one]
        congr 1
        exact Subtype.ext (pow_succ s k)
      obtain ⟨j₁, hj₁⟩ := ih a
      refine ⟨j₁ + N, fun y hy ↦ ?_⟩
      simp only [Set.mem_preimage]
      rw [hdecomp, mul_assoc]
      exact hj₁ (locNhd_invS_step P T s N hN j₁ _ hy)

/-- The `RingSubgroupsBasis` underlying the localization topology on `Aₛ`: the images of the
powers `Jⁿ` are a basis of neighbourhoods of zero compatible with the ring structure. -/
theorem locBasis [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.ringOfDefinition, b ∈ P.ideal ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    RingSubgroupsBasis (locNhd P T s) :=
  .of_comm _
    (fun i j ↦ ⟨max i j,
      le_inf (locNhd_antitone P T s (le_max_left i j))
        (locNhd_antitone P T s (le_max_right i j))⟩)
    (fun i ↦ ⟨i, locNhd_mul_subset P T s i⟩)
    (locNhd_leftMul P T s hopen)

/-- Wedhorn's topological localisation: the topology on `Aₛ` whose neighbourhoods of zero are the
images of the powers of the ideal of definition of `D = A₀[t₁/s, …, tₙ/s]`. -/
@[reducible] noncomputable def locTopology [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b ∈ P.ideal ^ N, divByS ((b : A)) s ∈ locSubring P T s) :
    TopologicalSpace (Localization.Away s) :=
  (locBasis P T s hopen).topology

end

end TauCeti.Huber
