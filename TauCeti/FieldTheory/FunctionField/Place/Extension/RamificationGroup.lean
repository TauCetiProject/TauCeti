/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia
public import TauCeti.FieldTheory.FunctionField.Place.Filtration

/-!
# The higher ramification groups of a place

Let `F' / F` be an extension of fields, `k` a subfield of `F`, and `P` a place of `F' / k`.  An
automorphism of `F'` over `F` fixing `P` acts on the valuation ring `𝒪_P`, and the **`i`-th
ramification group** of `P` collects those automorphisms whose action on `𝒪_P` is the identity to
order `i + 1`:

`G_i(P) = {σ ∈ G_Z(P) | ord_P (σ z - z) ≥ i + 1 for every z ∈ 𝒪_P}`.

At `i = 0` this is the condition that `σ` act trivially on the residue field, so `G_0(P)` is the
inertia group; the groups then decrease, are normal in the decomposition group, and meet in the
trivial group.  This is the lower numbering, and no completion is taken: the condition is read off
the order filtration of `F'` at `P` built in
`TauCeti/FieldTheory/FunctionField/Place/Filtration.lean`.

The structure of the successive quotients comes from a single map.  Fix a uniformizer `t` at `P`.
For `σ ∈ G_{i+1}(P)` the function `z ↦ (σ z - z) / t^{i+2}` takes values in `𝒪_P`, and reducing it
at `P` gives a function `𝒪_P → F'_P`; the resulting
`TauCeti.Place.ramificationResidueHom` is a group homomorphism from `G_{i+1}(P)` to the *additive*
group of such functions, and its kernel is exactly `G_{i+2}(P)`.  Its being a homomorphism is
where the hypothesis `i + 1 ≥ 1` enters: an automorphism in `G_1(P)` moves `t` by a unit
congruent to `1` at `P`, and one in `G_0(P)` does not move residues at all, so the two error terms
produced by expanding `(στ) z - z` disappear on reduction.

Consequently every quotient `G_{i+1}(P) / G_{i+2}(P)` embeds in the additive group of functions
from `𝒪_P` to the residue field: it is abelian, and in characteristic `p` it is killed by `p`, while
in characteristic zero it is trivial and hence — the groups meeting in `1` — `G_1(P)` is trivial.

This is Stichtenoth, Definition 3.8.4 and Proposition 3.8.5.  Nothing here consumes perfectness of
the residue fields; the complementary statement that `G_0(P) / G_1(P)` is cyclic of order prime to
the characteristic does, and is not proved here.

## Main definitions

* `TauCeti.Place.ramificationGroup`: the `i`-th ramification group of a place, a subgroup of the
  decomposition group, with `TauCeti.Place.mem_ramificationGroup_iff` for its membership.
* `TauCeti.Place.ramificationResidueHom`: for a uniformizer `t` at `P`, the homomorphism
  `σ ↦ (z ↦ ((σ z - z) / t^{i+2})(P))` from `G_{i+1}(P)` to the additive group of functions
  `𝒪_P → F'_P`.

## Main results

* `TauCeti.Place.ramificationGroup_zero`: the `0`-th ramification group is the inertia group.
* `TauCeti.Place.ramificationGroup_antitone`, `TauCeti.Place.normal_ramificationGroup`: the
  ramification groups decrease and are normal in the decomposition group.
* `TauCeti.Place.iInf_ramificationGroup_eq_bot` and
  `TauCeti.Place.exists_forall_ramificationGroup_eq_bot`: the ramification groups meet in the
  trivial group, and are trivial from some index on.
* `TauCeti.Place.ker_ramificationResidueHom`: **the kernel of the ramification residue is the next
  ramification group**, so `G_{i+1}(P) / G_{i+2}(P)` embeds in an additive group of functions to
  the residue field.
* `TauCeti.Place.commutator_ramificationGroup_le` and
  `TauCeti.Place.pow_mem_ramificationGroup_of_charP`: the quotient `G_{i+1}(P) / G_{i+2}(P)` is
  abelian, and elementary abelian of exponent `p` in characteristic `p`.
* `TauCeti.Place.ramificationGroup_one_eq_bot`: **in characteristic zero the first ramification
  group is trivial**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.8.4 and Proposition 3.8.5.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

section Transport

variable (F) (P : Place k F') (g : P.integers.decompositionSubgroup F)

/-- An automorphism fixing `P` leaves the valuation at `P` unchanged. -/
theorem valuation_decompositionSubgroup_apply (x : F') :
    P.valuation ((g : F' ≃ₐ[F] F') x) = P.valuation x := by
  have h : (g : F' ≃ₐ[F] F') • P = P := by
    have hg : (g : F' ≃ₐ[F] F') ∈ MulAction.stabilizer (F' ≃ₐ[F] F') P := by
      rw [stabilizer_eq_decompositionSubgroup]
      exact g.2
    exact hg
  calc P.valuation ((g : F' ≃ₐ[F] F') x)
      = ((g : F' ≃ₐ[F] F') • P).valuation ((g : F' ≃ₐ[F] F') x) := by rw [h]
    _ = P.valuation x := valuation_smul_apply _ _ _

/-- An automorphism fixing `P` preserves every step of the order filtration at `P`. -/
theorem mem_filtration_decompositionSubgroup_apply {a : ℤ} {x : F'} :
    (g : F' ≃ₐ[F] F') x ∈ P.filtration a ↔ x ∈ P.filtration a := by
  simp only [mem_filtration_iff, valuation_decompositionSubgroup_apply]

/-- An automorphism fixing `P` preserves the valuation ring of `P`. -/
theorem mem_integers_decompositionSubgroup_apply {x : F'} :
    (g : F' ≃ₐ[F] F') x ∈ P.integers ↔ x ∈ P.integers := by
  simp only [← mem_filtration_zero_iff, mem_filtration_decompositionSubgroup_apply]

end Transport

section Defs

variable (F) (P : Place k F')

/-- **The `i`-th ramification group of a place** (Stichtenoth, Definition 3.8.4): the
automorphisms in the decomposition group of `P` that move every function integral at `P` by
something of order at least `i + 1`.  This is the lower numbering. -/
def ramificationGroup (i : ℕ) : Subgroup (P.integers.decompositionSubgroup F) where
  carrier := {g | ∀ x ∈ P.integers, (g : F' ≃ₐ[F] F') x - x ∈ P.filtration (i + 1)}
  mul_mem' {a b} ha hb x hx := by
    have h₁ : (a : F' ≃ₐ[F] F') ((b : F' ≃ₐ[F] F') x) - (a : F' ≃ₐ[F] F') x ∈
        P.filtration (i + 1) := by
      rw [← map_sub]
      exact (mem_filtration_decompositionSubgroup_apply F P a).mpr (hb x hx)
    have h₂ := Submodule.add_mem _ h₁ (ha x hx)
    have hcoe : ((a * b : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') x =
        (a : F' ≃ₐ[F] F') ((b : F' ≃ₐ[F] F') x) := rfl
    rw [hcoe]
    convert h₂ using 1
    ring
  one_mem' x _ := by simp
  inv_mem' {a} ha x hx := by
    have hy : (a : F' ≃ₐ[F] F').symm x ∈ P.integers :=
      (mem_integers_decompositionSubgroup_apply F P a⁻¹).mpr hx
    have h := ha _ hy
    rw [AlgEquiv.apply_symm_apply] at h
    have hcoe : ((a⁻¹ : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') x =
        (a : F' ≃ₐ[F] F').symm x := rfl
    rw [hcoe, ← neg_sub x]
    exact neg_mem h

/-- **Membership in the `i`-th ramification group** (Stichtenoth, Definition 3.8.4). -/
@[simp]
theorem mem_ramificationGroup_iff {i : ℕ} {g : P.integers.decompositionSubgroup F} :
    g ∈ ramificationGroup F P i ↔
      ∀ x ∈ P.integers, (g : F' ≃ₐ[F] F') x - x ∈ P.filtration (i + 1) :=
  (Iff.rfl)

/-- **The `0`-th ramification group is the inertia group** (Stichtenoth, Definition 3.8.4): acting
trivially on the residue field is acting trivially to order `1` on the valuation ring. -/
@[simp]
theorem ramificationGroup_zero : ramificationGroup F P 0 = P.integers.inertiaSubgroup F := by
  ext g
  rw [mem_ramificationGroup_iff, mem_inertiaSubgroup_iff]
  have key : ∀ x : P.integers, (IsLocalRing.residue P.integers (g • x) =
      IsLocalRing.residue P.integers x ↔
      (g : F' ≃ₐ[F] F') (x : F') - (x : F') ∈ P.filtration ((0 : ℕ) + 1)) := by
    intro x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      mem_maximalIdeal_iff_valuation_lt_one, ← mem_filtration_one_iff]
    have hsub : ((g • x - x : P.integers) : F') =
        ((g • x : P.integers) : F') - ((x : P.integers) : F') := rfl
    rw [hsub, coe_decompositionSubgroup_smul]
    norm_num
  exact ⟨fun h x ↦ (key x).mpr (h (x : F') x.2), fun h x hx ↦ (key ⟨x, hx⟩).mp (h ⟨x, hx⟩)⟩

/-- The ramification groups decrease: vanishing to higher order is a stronger condition. -/
theorem ramificationGroup_antitone : Antitone (ramificationGroup F P) := by
  intro i j hij g hg x hx
  refine P.filtration_antitone ?_ (hg x hx)
  exact_mod_cast Int.add_le_add_right (Int.ofNat_le.mpr hij) 1

/-- Every ramification group sits inside the inertia group. -/
theorem ramificationGroup_le_inertiaSubgroup (i : ℕ) :
    ramificationGroup F P i ≤ P.integers.inertiaSubgroup F := by
  rw [← ramificationGroup_zero]
  exact ramificationGroup_antitone F P (Nat.zero_le i)

/-- **The ramification groups are normal in the decomposition group**
(Stichtenoth, Proposition 3.8.5). -/
instance normal_ramificationGroup (i : ℕ) : (ramificationGroup F P i).Normal where
  conj_mem a ha b x hx := by
    have hy : (b : F' ≃ₐ[F] F').symm x ∈ P.integers :=
      (mem_integers_decompositionSubgroup_apply F P b⁻¹).mpr hx
    have h := ha _ hy
    have hb := (mem_filtration_decompositionSubgroup_apply (a := ((i : ℤ) + 1))
      (x := (a : F' ≃ₐ[F] F') ((b : F' ≃ₐ[F] F').symm x) - (b : F' ≃ₐ[F] F').symm x) F P b).mpr h
    rw [map_sub, AlgEquiv.apply_symm_apply] at hb
    have hcoe : ((b * a * b⁻¹ : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') x =
        (b : F' ≃ₐ[F] F') ((a : F' ≃ₐ[F] F') ((b : F' ≃ₐ[F] F').symm x)) := rfl
    rw [hcoe]
    exact hb

/-- **The ramification groups meet in the trivial group** (Stichtenoth, Proposition 3.8.5): an
automorphism fixing every function integral at `P` to every order is the identity, because the
valuation ring of `P` has `F'` for its field of fractions. -/
theorem iInf_ramificationGroup_eq_bot : ⨅ i, ramificationGroup F P i = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_iInf] at hg
  have hfix : ∀ x ∈ P.integers, (g : F' ≃ₐ[F] F') x = x := by
    intro x hx
    by_contra hne
    have h0 : (g : F' ≃ₐ[F] F') x - x ≠ 0 := sub_ne_zero.mpr hne
    have hmem := hg (P.ord ((g : F' ≃ₐ[F] F') x - x)).toNat x hx
    have := (P.mem_filtration_iff_le_ord h0).mp hmem
    omega
  rw [Subgroup.mem_bot]
  refine Subtype.ext (AlgEquiv.ext fun y ↦ ?_)
  -- Unfold the nested subgroup and equivalence coercions to state pointwise equality in `F'`.
  change (g : F' ≃ₐ[F] F') y = y
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · rcases ValuationSubring.mem_or_inv_mem P.integers y with hy | hy
    · exact hfix y hy
    · have h := hfix _ hy
      rw [map_inv₀] at h
      exact inv_injective h

/-- **The ramification groups are trivial from some index on**
(Stichtenoth, Proposition 3.8.5). -/
theorem exists_forall_ramificationGroup_eq_bot [Finite (P.integers.decompositionSubgroup F)] :
    ∃ N : ℕ, ∀ i, N ≤ i → ramificationGroup F P i = ⊥ := by
  classical
  have := Fintype.ofFinite (P.integers.decompositionSubgroup F)
  have key : ∀ g : P.integers.decompositionSubgroup F,
      ∃ n : ℕ, ∀ i, n ≤ i → g ∈ ramificationGroup F P i → g = 1 := by
    intro g
    by_cases hg : ∀ i : ℕ, g ∈ ramificationGroup F P i
    · exact ⟨0, fun i _ _ ↦ by
        have : g ∈ (⊥ : Subgroup (P.integers.decompositionSubgroup F)) := by
          rw [← iInf_ramificationGroup_eq_bot F P]
          exact Subgroup.mem_iInf.mpr hg
        rwa [Subgroup.mem_bot] at this⟩
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, g ∉ ramificationGroup F P n := by
        by_contra h
        exact hg fun i ↦ not_not.mp fun hi ↦ h ⟨i, hi⟩
      exact ⟨n, fun i hi hmem ↦ absurd (ramificationGroup_antitone F P hi hmem) hn⟩
  choose n hn using key
  refine ⟨Finset.univ.sup n, fun i hi ↦ le_bot_iff.mp fun g hg ↦ ?_⟩
  rw [Subgroup.mem_bot]
  exact hn g i (le_trans (Finset.le_sup (Finset.mem_univ g)) hi) hg

end Defs

section Residue

variable (F) (P : Place k F') {t : F'}

private theorem ord_inv_pow_add_two (ht : P.ord t = 1) (i : ℕ) :
    P.ord ((t ^ (i + 2))⁻¹) = -((i : ℤ) + 2) := by
  rw [ord_inv, ord_pow, ht, mul_one]
  push_cast
  ring

private theorem sub_mem_filtration_add_two {i : ℕ} (g : ramificationGroup F P (i + 1)) {x : F'}
    (hx : x ∈ P.integers) :
    ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') x - x ∈
      P.filtration ((i : ℤ) + 2) := by
  have h := g.2 x hx
  -- Normalize the coerced natural-number index to the integer index used by `filtration`.
  rwa [show (((i + 1 : ℕ) : ℤ) + 1) = (i : ℤ) + 2 by push_cast; ring] at h

private theorem residue_eq_of_sub_mem_filtration_one {y z : P.integers}
    (h : (y : F') - (z : F') ∈ P.filtration 1) :
    IsLocalRing.residue P.integers y = IsLocalRing.residue P.integers z := by
  -- Expose subtraction in the valuation subring as subtraction in its fraction field.
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    mem_maximalIdeal_iff_valuation_lt_one, ← mem_filtration_one_iff,
    show ((y - z : P.integers) : F') = (y : F') - (z : F') from rfl]
  exact h

private theorem pow_sub_one_mem_filtration_one {u : F'} (hu : u ∈ P.integers)
    (h : u - 1 ∈ P.filtration 1) (n : ℕ) : u ^ n - 1 ∈ P.filtration 1 := by
  induction n with
  | zero =>
    rw [pow_zero, sub_self]
    exact Submodule.zero_mem (P.filtration 1)
  | succ n ih =>
    -- Split the successor power difference into the induction term and `u - 1`.
    rw [show u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) by ring]
    refine Submodule.add_mem _ ?_ h
    simpa using P.mul_mem_filtration (P.mem_filtration_zero_iff.mpr hu) ih

/-- **The ramification residue** (Stichtenoth, Proposition 3.8.5): for a uniformizer `t` at `P`,
the map sending an automorphism `σ` of `G_{i+1}(P)` to the function `z ↦ ((σ z - z)/t^{i+2})(P)`
on `𝒪_P`.  It is a homomorphism into the *additive* group of functions `𝒪_P → F'_P`, which is
therefore written multiplicatively here.  The map depends on the choice of `t`; its kernel,
`TauCeti.Place.ker_ramificationResidueHom`, does not. -/
noncomputable def ramificationResidueHom (ht : P.ord t = 1) (i : ℕ) :
    ramificationGroup F P (i + 1) →* Multiplicative (P.integers → P.ResidueField) :=
  MonoidHom.mk'
    (fun g ↦ Multiplicative.ofAdd fun x ↦
      filtrationResidue (P := P) (a := (i : ℤ) + 2) (s := (t ^ (i + 2))⁻¹)
        (ord_inv_pow_add_two P ht i) ⟨_, sub_mem_filtration_add_two F P g x.2⟩)
    (by
      intro g h
      rw [← ofAdd_add]
      refine congrArg Multiplicative.ofAdd (funext fun x ↦ ?_)
      have ht0 : t ≠ 0 := fun h0 ↦ by simp [h0, ord_zero] at ht
      set s : F' := (t ^ (i + 2))⁻¹ with hs
      set σ : F' ≃ₐ[F] F' := ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') with hσ
      set τ : F' ≃ₐ[F] F' := ((h : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') with hτ
      -- Normalize the error of `τ` by the chosen power of the uniformizer.
      have hw : τ (x : F') - (x : F') ∈ P.filtration ((i : ℤ) + 2) :=
        sub_mem_filtration_add_two F P h x.2
      have hc : s * (τ (x : F') - (x : F')) ∈ P.integers :=
        mul_mem_integers_of_mem_filtration (ord_inv_pow_add_two P ht i) hw
      set c : F' := s * (τ (x : F') - (x : F')) with hcdef
      have hwc : τ (x : F') - (x : F') = t ^ (i + 2) * c := by
        rw [hcdef, hs, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0), one_mul]
      have htmem : t ∈ P.integers := by
        rw [mem_integers_iff_ord_nonneg, ht]
        norm_num
      have hσt : σ t - t ∈ P.filtration ((i : ℤ) + 2) := sub_mem_filtration_add_two F P g htmem
      set u : F' := σ t * t⁻¹ with hu
      have hu1 : u - 1 ∈ P.filtration 1 := by
        -- Rewrite the uniformizer ratio so its filtration follows from `σ t - t`.
        rw [show u - 1 = (σ t - t) * t⁻¹ by rw [hu]; field_simp]
        have hord : P.ord t⁻¹ = -1 := by rw [ord_inv, ht]
        have h2 : (2 : ℤ) ≤ (i : ℤ) + 2 := by omega
        have h3 := P.mul_mem_filtration (P.filtration_antitone h2 hσt)
          (P.mem_filtration_ord t⁻¹)
        -- The filtration indices add to `2 + (-1) = 1`.
        rwa [hord, show (2 : ℤ) + -1 = 1 by ring] at h3
      have humem : u ∈ P.integers := by
        -- Recover integrality of `u` from the integral summands `u - 1` and `1`.
        rw [show u = (u - 1) + 1 by ring]
        have h0 : (0 : ℤ) ≤ 1 := by norm_num
        exact add_mem (P.mem_filtration_zero_iff.mp (P.filtration_antitone h0 hu1)) (one_mem _)
      have hσc : σ c - c ∈ P.filtration 1 := by
        have h1 := g.2 c hc
        have h2 : (1 : ℤ) ≤ ((i + 1 : ℕ) : ℤ) + 1 := by push_cast; omega
        exact P.filtration_antitone h2 h1
      have hσcmem : σ c ∈ P.integers := (mem_integers_decompositionSubgroup_apply F P _).mpr hc
      -- Expand the composite-action error using `σ t = u * t`.
      have hexp : s * (σ (τ (x : F')) - σ (x : F')) = u ^ (i + 2) * σ c := by
        rw [← map_sub, hwc, map_mul, map_pow, hu, mul_pow, inv_pow, hs]
        ring
      have hkey : s * (σ (τ (x : F')) - σ (x : F')) - c ∈ P.filtration 1 := by
        -- Separate the two error terms: `u^(i+2) - 1` and `σ c - c`.
        rw [hexp, show u ^ (i + 2) * σ c - c = (u ^ (i + 2) - 1) * σ c + (σ c - c) by ring]
        refine Submodule.add_mem _ ?_ hσc
        simpa using P.mul_mem_filtration (pow_sub_one_mem_filtration_one P humem hu1 (i + 2))
          (P.mem_filtration_zero_iff.mpr hσcmem)
      simp only [Pi.add_apply, filtrationResidue_apply, ← map_add]
      refine residue_eq_of_sub_mem_filtration_one P ?_
      convert hkey using 1
      -- Unfold the three residue numerators to the field identity supplied by `hkey`.
      change s * (σ (τ (x : F')) - (x : F')) -
          (s * (σ (x : F') - (x : F')) + s * (τ (x : F') - (x : F'))) =
        s * (σ (τ (x : F')) - σ (x : F')) - c
      rw [hcdef]
      ring)

/-- The value of the ramification residue at a function `x` integral at `P`, computed on any
representative `y` of `(σ x - x)/t^{i+2}` in `𝒪_P`. -/
theorem toAdd_ramificationResidueHom_apply (ht : P.ord t = 1) (i : ℕ)
    (g : ramificationGroup F P (i + 1)) (x y : P.integers)
    (hy : (y : F') = (t ^ (i + 2))⁻¹ *
      (((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') (x : F') - (x : F'))) :
    Multiplicative.toAdd (ramificationResidueHom F P ht i g) x =
      IsLocalRing.residue P.integers y := by
  have hrfl : Multiplicative.toAdd (ramificationResidueHom F P ht i g) x =
      filtrationResidue (P := P) (a := (i : ℤ) + 2) (s := (t ^ (i + 2))⁻¹)
        (ord_inv_pow_add_two P ht i) ⟨_, sub_mem_filtration_add_two F P g x.2⟩ := rfl
  rw [hrfl, filtrationResidue_apply]
  exact congrArg _ (Subtype.ext hy.symm)

/-- **The kernel of the ramification residue is the next ramification group** (Stichtenoth,
Proposition 3.8.5): so `G_{i+1}(P) / G_{i+2}(P)` embeds into the additive group of functions from
`𝒪_P` to the residue field at `P`. -/
theorem ker_ramificationResidueHom (ht : P.ord t = 1) (i : ℕ) :
    (ramificationResidueHom F P ht i).ker =
      (ramificationGroup F P (i + 2)).subgroupOf (ramificationGroup F P (i + 1)) := by
  have ht0 : t ≠ 0 := fun h0 ↦ by simp [h0, ord_zero] at ht
  have hinv : (t ^ (i + 2))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ ht0)
  have hidx : (((i + 2 : ℕ) : ℤ) + 1) = (i : ℤ) + 2 + 1 := by push_cast; ring
  ext g
  have hval : ∀ x : P.integers, Multiplicative.toAdd (ramificationResidueHom F P ht i g) x =
      filtrationResidue (P := P) (a := (i : ℤ) + 2) (s := (t ^ (i + 2))⁻¹)
        (ord_inv_pow_add_two P ht i) ⟨_, sub_mem_filtration_add_two F P g x.2⟩ := fun _ ↦ rfl
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_ramificationGroup_iff, ← toAdd_eq_zero]
  constructor
  · intro hg x hx
    have h1 : Multiplicative.toAdd (ramificationResidueHom F P ht i g) ⟨x, hx⟩ = 0 := by
      rw [hg, Pi.zero_apply]
    rw [hval] at h1
    have h2 := (filtrationResidue_eq_zero_iff (ord_inv_pow_add_two P ht i) hinv _).mp h1
    rwa [hidx]
  · intro hg
    funext x
    rw [hval, Pi.zero_apply]
    refine (filtrationResidue_eq_zero_iff (ord_inv_pow_add_two P ht i) hinv _).mpr ?_
    have := hg (x : F') x.2
    rwa [hidx] at this

end Residue

section Structure

variable (F) (P : Place k F')

/-- **The successive quotients of the ramification filtration are abelian**
(Stichtenoth, Proposition 3.8.5): a commutator of `G_{i+1}(P)` lies in `G_{i+2}(P)`. -/
theorem commutator_ramificationGroup_le (i : ℕ) :
    ⁅ramificationGroup F P (i + 1), ramificationGroup F P (i + 1)⁆ ≤
      ramificationGroup F P (i + 2) := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [isUniformizer_iff_ord_eq_one] at ht
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have hmem : (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ :
      ramificationGroup F P (i + 1)) ∈ (ramificationResidueHom F P ht i).ker := by
    rw [MonoidHom.mem_ker, ← toAdd_eq_zero]
    funext x
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
    ring
  rw [ker_ramificationResidueHom, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

/-- **In characteristic `p` the successive quotients of the ramification filtration are killed by
`p`** (Stichtenoth, Proposition 3.8.5): the `p`-th power of an element of `G_{i+1}(P)` lies in
`G_{i+2}(P)`, so `G_{i+1}(P) / G_{i+2}(P)` is elementary abelian. -/
theorem pow_mem_ramificationGroup_of_charP (p : ℕ) [CharP P.ResidueField p] (i : ℕ)
    {g : P.integers.decompositionSubgroup F} (hg : g ∈ ramificationGroup F P (i + 1)) :
    g ^ p ∈ ramificationGroup F P (i + 2) := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [isUniformizer_iff_ord_eq_one] at ht
  have hp : (p : P.ResidueField) = 0 := CharP.cast_eq_zero P.ResidueField p
  have hmem : (⟨g, hg⟩ : ramificationGroup F P (i + 1)) ^ p ∈
      (ramificationResidueHom F P ht i).ker := by
    rw [MonoidHom.mem_ker, map_pow, ← toAdd_eq_zero]
    funext x
    rw [toAdd_pow, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, hp, zero_mul]
  rw [ker_ramificationResidueHom, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

/-- **In characteristic zero the first ramification group is trivial**
(Stichtenoth, Proposition 3.8.5). -/
theorem ramificationGroup_one_eq_bot [Finite (P.integers.decompositionSubgroup F)]
    [CharZero P.ResidueField] :
    ramificationGroup F P 1 = ⊥ := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [isUniformizer_iff_ord_eq_one] at ht
  have hstep : ∀ i : ℕ, ramificationGroup F P (i + 1) ≤ ramificationGroup F P (i + 2) := by
    intro i g hg
    have hfin : (0 : ℕ) < orderOf (⟨g, hg⟩ : ramificationGroup F P (i + 1)) := orderOf_pos _
    have hmem : (⟨g, hg⟩ : ramificationGroup F P (i + 1)) ∈
        (ramificationResidueHom F P ht i).ker := by
      rw [MonoidHom.mem_ker, ← toAdd_eq_zero]
      funext x
      set n := orderOf (⟨g, hg⟩ : ramificationGroup F P (i + 1))
      have hpow : (ramificationResidueHom F P ht i ⟨g, hg⟩) ^ n = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      have hval := congrFun (congrArg Multiplicative.toAdd hpow) x
      rw [toAdd_pow, toAdd_one, Pi.zero_apply, Pi.smul_apply, nsmul_eq_mul] at hval
      have hncast : (n : P.ResidueField) ≠ 0 := Nat.cast_ne_zero.mpr hfin.ne'
      rw [Pi.zero_apply]
      exact (mul_eq_zero.mp hval).resolve_left hncast
    rw [ker_ramificationResidueHom, Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  have hle : ∀ i : ℕ, ramificationGroup F P 1 ≤ ramificationGroup F P i := by
    intro i
    induction i with
    | zero => exact ramificationGroup_antitone F P (Nat.zero_le 1)
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact le_rfl
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact le_trans ih (hstep j)
  refine le_antisymm ?_ bot_le
  rw [← iInf_ramificationGroup_eq_bot F P]
  exact le_iInf hle

end Structure

end Place

end TauCeti
