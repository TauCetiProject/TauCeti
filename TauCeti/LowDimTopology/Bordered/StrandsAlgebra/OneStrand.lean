/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Occupancy

/-!
# Coordinates on the one-strand summand of a matched algebra

Let `M` be a matching on a finite linearly ordered set `α`. The summand
`TauCeti.StrandsAlgebra.matchedSummand R M 1` of the matched subalgebra with one strand has the
basis consisting of the idempotents `I({p})` of the matched pairs `p` and the single strands of
the chords `u < v` (`TauCeti.StrandsAlgebra.oneStrandSummandBasis`), the basis
`TauCeti.StrandsAlgebra.oneStrandBasis` of the one-strand part of the matched subalgebra read on
the summand. For the genus-one pointed matched circle this is the basis `ι₀, ι₁, ρ₁, ρ₂, ρ₃, ρ₁₂,
ρ₂₃, ρ₁₂₃` of the torus algebra.

The coordinate of the idempotent of `p` (`TauCeti.StrandsAlgebra.oneStrandIdemCoord`) and the
coordinate of a chord (`TauCeti.StrandsAlgebra.oneStrandChordCoord`) of a product are computed from
the coordinates of the factors. A chord from `a` to `b` times a chord from `c` to `d` is the chord
from `a` to `d` when `b = c` and zero otherwise, an idempotent fixes the chords starting or ending
at its pair, and the idempotents are orthogonal. Hence the idempotent coordinates are
multiplicative (`TauCeti.StrandsAlgebra.oneStrandIdemCoord_mul`), and the coordinate of the chord
from `u` to `v` of a product `x y` is

`c_{I(u)}(x) c_{uv}(y) + c_{uv}(x) c_{I(v)}(y) + ∑_{u < m < v} c_{um}(x) c_{mv}(y)`

(`TauCeti.StrandsAlgebra.oneStrandChordCoord_mul`), where `I(u)` is the idempotent of the pair of
`u`: the chord is either kept by an idempotent on one side or broken at an intermediate point `m`.

## Main definitions

* `TauCeti.StrandsAlgebra.oneStrandSummandBasis`: the basis of the matched summand with one strand.
* `TauCeti.StrandsAlgebra.oneStrandIdemCoord`: the coordinate of an idempotent.

## Main results

* `TauCeti.StrandsAlgebra.oneStrandChordCoord_eq_coord`: the chord coordinates are the
  coordinates of the basis.
* `TauCeti.StrandsAlgebra.oneStrandIdemCoord_mul`: idempotent coordinates are multiplicative.
* `TauCeti.StrandsAlgebra.oneStrandChordCoord_mul`: the chord coordinates of a product.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1 and
  §3.2 (the strands algebra and the algebra of a pointed matched circle).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] [DecidableEq β]
  (M : α → β)

omit [DecidableEq β] in
/-- The matched summand with one strand is the one-strand part of the matched subalgebra. -/
theorem toSubmodule_matchedSummand_one :
    (matchedSummand R M 1).toSubmodule =
      (matchedSubalgebra R M).toSubmodule ⊓ strandCountPart R 1 := by
  ext x
  rw [NonUnitalSubalgebra.mem_toSubmodule, mem_matchedSummand, mem_strandSummand,
    Submodule.mem_inf, NonUnitalSubalgebra.mem_toSubmodule, mem_strandCountPart]
  exact and_congr Iff.rfl ⟨fun h φ hφ ↦ h φ (Finsupp.mem_support_iff.1 hφ),
    fun h φ hφ ↦ h φ (Finsupp.mem_support_iff.2 hφ)⟩

variable (R) in
/-- **The basis of the matched summand with one strand**: the idempotent `I({p})` of each matched
pair `p` and the single strand of each chord `u < v`. -/
def oneStrandSummandBasis :
    Module.Basis (Set.range M ⊕ {p : α × α // p.1 < p.2}) R (matchedSummand R M 1) :=
  (oneStrandBasis R M).map (LinearEquiv.ofEq _ _ (toSubmodule_matchedSummand_one M)).symm

@[simp]
theorem oneStrandSummandBasis_inl (p : Set.range M) :
    oneStrandSummandBasis R M (.inl p) = oneStrandIdem R M p :=
  Subtype.ext <| by
    rw [oneStrandSummandBasis, Module.Basis.map_apply, LinearEquiv.ofEq_symm,
      LinearEquiv.coe_ofEq_apply, coe_oneStrandBasis]
    simp

@[simp]
theorem oneStrandSummandBasis_inr (c : {p : α × α // p.1 < p.2}) :
    oneStrandSummandBasis R M (.inr c) = oneStrandChord R M c.property :=
  Subtype.ext <| by
    rw [oneStrandSummandBasis, Module.Basis.map_apply, LinearEquiv.ofEq_symm,
      LinearEquiv.coe_ofEq_apply, coe_oneStrandBasis]
    simp

variable (R) in
/-- The coordinate of the idempotent `I({p})` of a matched pair `p` on the matched summand with one
strand. -/
def oneStrandIdemCoord (p : Set.range M) : Module.Dual R (matchedSummand R M 1) :=
  (oneStrandSummandBasis R M).coord (.inl p)

/-- The idempotent coordinates are the coordinates of the basis of the matched summand with one
strand. -/
theorem oneStrandIdemCoord_eq_coord (p : Set.range M) :
    oneStrandIdemCoord R M p = (oneStrandSummandBasis R M).coord (.inl p) :=
  (rfl)

/-- The coordinate of an idempotent on an idempotent is `1` if they agree and `0` otherwise. -/
@[simp]
theorem oneStrandIdemCoord_oneStrandIdem (p q : Set.range M) :
    oneStrandIdemCoord R M p (oneStrandIdem R M q) = if q = p then 1 else 0 := by
  rw [oneStrandIdemCoord, ← oneStrandSummandBasis_inl, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  exact if_congr Sum.inl_injective.eq_iff rfl rfl

/-- The coordinate of an idempotent on a chord is `0`. -/
@[simp]
theorem oneStrandIdemCoord_oneStrandChord (p : Set.range M) {u v : α} (h : u < v) :
    oneStrandIdemCoord R M p (oneStrandChord R M h) = 0 := by
  rw [oneStrandIdemCoord, ← oneStrandSummandBasis_inr M ⟨(u, v), h⟩, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp

/-- The coordinate of the idempotent of `p` on the unit is `1`. -/
@[simp]
theorem oneStrandIdemCoord_one (p : Set.range M) : oneStrandIdemCoord R M p 1 = 1 := by
  rw [← sum_oneStrandIdem, map_sum, Fintype.sum_eq_single p fun q hq ↦ by simp [hq]]
  simp

/-- **The chord coordinates are the coordinates of the basis** of the matched summand with one
strand. -/
theorem oneStrandChordCoord_eq_coord {u v : α} (h : u < v) :
    oneStrandChordCoord R M h = (oneStrandSummandBasis R M).coord (.inr ⟨(u, v), h⟩) := by
  refine (oneStrandSummandBasis R M).ext fun b ↦ ?_
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rcases b with p | ⟨⟨a, b⟩, hab⟩
  · simp
  · rw [oneStrandSummandBasis_inr, oneStrandChordCoord_oneStrandChord]
    refine if_congr ?_ rfl rfl
    simp [Subtype.ext_iff, Prod.ext_iff, eq_comm]

/-! ### Coordinates of products -/

section Mul

/-- The idempotent coordinate of a product of two basis elements. -/
private theorem oneStrandIdemCoord_basis_mul_basis (p : Set.range M)
    (b b' : Set.range M ⊕ {p : α × α // p.1 < p.2}) :
    oneStrandIdemCoord R M p (oneStrandSummandBasis R M b * oneStrandSummandBasis R M b') =
      oneStrandIdemCoord R M p (oneStrandSummandBasis R M b) *
        oneStrandIdemCoord R M p (oneStrandSummandBasis R M b') := by
  rcases b with q | ⟨⟨a, c⟩, hac⟩ <;> rcases b' with q' | ⟨⟨a', c'⟩, hac'⟩
  · simp only [oneStrandSummandBasis_inl, oneStrandIdem_mul_oneStrandIdem]
    rcases eq_or_ne q q' with rfl | hq
    · simp only [ite_true, oneStrandIdemCoord_oneStrandIdem]
      split_ifs <;> simp
    · simp only [hq, ite_false, map_zero, oneStrandIdemCoord_oneStrandIdem]
      split_ifs with h₁ h₂ <;> simp_all
  · simp only [oneStrandSummandBasis_inl, oneStrandSummandBasis_inr,
      oneStrandIdem_mul_oneStrandChord]
    split_ifs <;> simp
  · simp only [oneStrandSummandBasis_inl, oneStrandSummandBasis_inr,
      oneStrandChord_mul_oneStrandIdem]
    split_ifs <;> simp
  · simp only [oneStrandSummandBasis_inr]
    by_cases hc : c = a'
    · subst hc
      simp
    · simp [oneStrandChord_mul_oneStrandChord_of_ne M hac hac' hc]

/-- **The idempotent coordinates are multiplicative**: the coefficient of `I({p})` in a product is
the product of the coefficients of `I({p})` in the factors. -/
theorem oneStrandIdemCoord_mul (p : Set.range M) (x y : matchedSummand R M 1) :
    oneStrandIdemCoord R M p (x * y) = oneStrandIdemCoord R M p x * oneStrandIdemCoord R M p y := by
  have := LinearMap.ext_basis (oneStrandSummandBasis R M) (oneStrandSummandBasis R M)
    (B := (LinearMap.mul R (matchedSummand R M 1)).compr₂ (oneStrandIdemCoord R M p))
    (B' := (LinearMap.mul R R).compl₁₂ (oneStrandIdemCoord R M p) (oneStrandIdemCoord R M p))
    fun b b' ↦ by simpa using oneStrandIdemCoord_basis_mul_basis M p b b'
  simpa using LinearMap.congr_fun₂ this x y

omit [DecidableEq β] in
/-- The sum over the intermediate points `u < m < v` of `c_{um}(ρ_{ac}) c_{mv}(ρ_{a'c'})` vanishes
unless `a = u`, `c = a'` and `c' = v`. -/
private theorem sum_oneStrandChordCoord_mul_eq_zero {u v a c a' c' : α} (hac : a < c)
    (hac' : a' < c') (h : ¬(a = u ∧ c = a' ∧ c' = v)) :
    ∑ m : {m : α // u < m ∧ m < v}, oneStrandChordCoord R M m.property.1 (oneStrandChord R M hac) *
      oneStrandChordCoord R M m.property.2 (oneStrandChord R M hac') = 0 := by
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  simp only [oneStrandChordCoord_oneStrandChord]
  split_ifs with h₁ h₂ <;> simp_all

/-- The chord coordinate of a product of two basis elements. -/
private theorem oneStrandChordCoord_basis_mul_basis {u v : α} (h : u < v)
    (b b' : Set.range M ⊕ {p : α × α // p.1 < p.2}) :
    oneStrandChordCoord R M h (oneStrandSummandBasis R M b * oneStrandSummandBasis R M b') =
      oneStrandIdemCoord R M ⟨M u, u, rfl⟩ (oneStrandSummandBasis R M b) *
          oneStrandChordCoord R M h (oneStrandSummandBasis R M b') +
        oneStrandChordCoord R M h (oneStrandSummandBasis R M b) *
          oneStrandIdemCoord R M ⟨M v, v, rfl⟩ (oneStrandSummandBasis R M b') +
        ∑ m : {m : α // u < m ∧ m < v}, oneStrandChordCoord R M m.property.1
            (oneStrandSummandBasis R M b) *
          oneStrandChordCoord R M m.property.2 (oneStrandSummandBasis R M b') := by
  rcases b with q | ⟨⟨a, c⟩, hac⟩ <;> rcases b' with q' | ⟨⟨a', c'⟩, hac'⟩
  · simp only [oneStrandSummandBasis_inl, oneStrandIdem_mul_oneStrandIdem]
    split_ifs <;> simp
  · simp only [oneStrandSummandBasis_inl, oneStrandSummandBasis_inr,
      oneStrandIdem_mul_oneStrandChord, oneStrandChordCoord_oneStrandIdem, zero_mul,
      add_zero, Finset.sum_const_zero, oneStrandIdemCoord_oneStrandIdem,
      oneStrandChordCoord_oneStrandChord, apply_ite (oneStrandChordCoord R M h), map_zero]
    by_cases hc : a' = u ∧ c' = v
    · obtain ⟨rfl, rfl⟩ := hc
      simp [Subtype.ext_iff]
    · simp [hc]
  · simp only [oneStrandSummandBasis_inl, oneStrandSummandBasis_inr,
      oneStrandChord_mul_oneStrandIdem, oneStrandChordCoord_oneStrandIdem, mul_zero,
      zero_add, Finset.sum_const_zero, oneStrandIdemCoord_oneStrandIdem, add_zero,
      oneStrandChordCoord_oneStrandChord, apply_ite (oneStrandChordCoord R M h), map_zero]
    by_cases hc : a = u ∧ c = v
    · obtain ⟨rfl, rfl⟩ := hc
      simp [Subtype.ext_iff]
    · simp [hc]
  · simp only [oneStrandSummandBasis_inr, oneStrandIdemCoord_oneStrandChord, zero_mul, mul_zero,
      zero_add]
    by_cases hca : c = a'
    · subst hca
      rw [oneStrandChord_mul_oneStrandChord, oneStrandChordCoord_oneStrandChord]
      by_cases hcase : a = u ∧ c' = v
      · obtain ⟨rfl, rfl⟩ := hcase
        -- Only the intermediate point `m = c` contributes to the sum.
        simp only [and_self, ↓reduceIte]
        rw [Fintype.sum_eq_single ⟨c, hac, hac'⟩]
        · simp
        · intro m hm
          have hm' : c ≠ m := fun h ↦ hm (Subtype.ext h.symm)
          simp [oneStrandChordCoord_oneStrandChord, hm']
      · simp only [hcase, ↓reduceIte]
        exact (sum_oneStrandChordCoord_mul_eq_zero M hac hac' fun ⟨h₁, _, h₃⟩ ↦
          hcase ⟨h₁, h₃⟩).symm
    · rw [oneStrandChord_mul_oneStrandChord_of_ne M hac hac' hca, map_zero]
      exact (sum_oneStrandChordCoord_mul_eq_zero M hac hac' fun ⟨_, h₂, _⟩ ↦ hca h₂).symm

/-- **The chord coordinates of a product.** The coefficient of the chord from `u` to `v` in `x y`
is `c_{I(u)}(x) c_{uv}(y) + c_{uv}(x) c_{I(v)}(y) + ∑_{u < m < v} c_{um}(x) c_{mv}(y)`, where `I(u)`
and `I(v)` are the idempotents of the pairs of `u` and `v`: the chord is kept by an idempotent on
one side, or broken at an intermediate point `m`. -/
theorem oneStrandChordCoord_mul {u v : α} (h : u < v) (x y : matchedSummand R M 1) :
    oneStrandChordCoord R M h (x * y) =
      oneStrandIdemCoord R M ⟨M u, u, rfl⟩ x * oneStrandChordCoord R M h y +
        oneStrandChordCoord R M h x * oneStrandIdemCoord R M ⟨M v, v, rfl⟩ y +
        ∑ m : {m : α // u < m ∧ m < v},
          oneStrandChordCoord R M m.property.1 x * oneStrandChordCoord R M m.property.2 y := by
  have := LinearMap.ext_basis (oneStrandSummandBasis R M) (oneStrandSummandBasis R M)
    (B := (LinearMap.mul R (matchedSummand R M 1)).compr₂ (oneStrandChordCoord R M h))
    (B' := (LinearMap.mul R R).compl₁₂ (oneStrandIdemCoord R M ⟨M u, u, rfl⟩)
        (oneStrandChordCoord R M h) +
      (LinearMap.mul R R).compl₁₂ (oneStrandChordCoord R M h)
        (oneStrandIdemCoord R M ⟨M v, v, rfl⟩) +
      ∑ m : {m : α // u < m ∧ m < v}, (LinearMap.mul R R).compl₁₂
        (oneStrandChordCoord R M m.property.1) (oneStrandChordCoord R M m.property.2))
    fun b b' ↦ by
      simpa [LinearMap.sum_apply] using oneStrandChordCoord_basis_mul_basis M h b b'
  simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ this x y

end Mul

end StrandsAlgebra

end TauCeti
