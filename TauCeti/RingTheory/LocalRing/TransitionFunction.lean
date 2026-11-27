/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableDegree
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.LocalRing.Herbrand
public import TauCeti.RingTheory.LocalRing.RingHom
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import TauCeti.RingTheory.LocalRing.Pointwise

/-!
# The integral formula for the transition function of a subgroup

Let a finite group `G` act on a local ring `S` by ring automorphisms, and let `H` be a subgroup,
acting on `S` by restriction. Write `φ_G`, `ψ_G` and `G^t` for the Herbrand function, its inverse
and the upper ramification groups of `G` (`TauCeti.IsLocalRing.herbrandFun`), and `φ_H` for the
Herbrand function of `H`. The composite `φ_H ∘ ψ_G` is the **transition function** of `H ≤ G`:
for a finite Galois extension `M/K` of complete discretely valued fields, `G = Gal(M/K)` acting on
the integer ring of `M` and `H = Gal(M/L)` for an intermediate field `L`, Galois or not, it is the
function `ψ_{L/K}` of Serre, which reindexes the upper filtration along `H ∩ G^u = H^{ψ_{L/K}(u)}`
(`TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup`).

This file proves the **integral formula**

`φ_H(ψ_G(u)) = ∫_0^u [G : G^t H] / [G : G_0 H] dt`

for every real `u` and every finite group action on a local ring. Its integrand is the number of
orbits of `G^t` on the cosets `G / H`, that is on the `K`-embeddings of `L` into `M`, normalized by
its value on `(-1, 0]`. Over a separable residue extension the normalizing constant is the residue
degree `f(L/K)`, which gives Serre's form

`ψ_{L/K}(u) = (1 / f(L/K)) ∫_0^u [G : G^t H] dt`.

The identification of the constant holds in general with the separable residue degree: if `G`
acts faithfully on the local ring `B` by `A`-algebra automorphisms with invariants `A`, then
`[G : G_0 H]` is the separable degree of the residue extension of the fixed ring `B^H` over `A`.
Without separability it can differ from the residue degree: for the purely inseparable residue
extension of degree `p` of `y^p - y = s t^{-p}` over `𝔽_p(s)((t))`, with `H = 1`, the index is
`[G : G_0] = 1`.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun_eq_integral`: the integral formula
  `φ_H(ψ_G(u)) = ∫_0^u [G : G^t H] / [G : G_0 H] dt`.
* `TauCeti.IsLocalRing.index_ramificationGroup_zero_sup_eq_finSepDegree`: `[G : G_0 H]` is the
  separable residue degree of `B^H` over `A`.
* `TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun_eq_integral_div_finrank`: over a separable
  residue extension, `φ_H(ψ_G(u)) = (1 / f) ∫_0^u [G : G^t H] dt`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 2, and §3.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, Proposition 4 and the remark after it, for totally ramified
  extensions.
-/

public section
noncomputable section

open IsLocalRing MeasureTheory Set intervalIntegral Filter

open scoped Pointwise

namespace TauCeti.IsLocalRing

/-! ### The integral formula for a finite group acting on a local ring -/

section Integral

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The product formula `#(G_i H) · #(H ∩ G_i) = #G_i · #H`, in the form
`[G : G_i H] · #G_i · #H = #G · #H_i`, with `H_i = H ∩ G_i` the ramification group of `H`. -/
private theorem index_sup_mul_natCard_mul_natCard (H : Subgroup G) (i : ℤ) :
    (ramificationGroup G S i ⊔ H).index * Nat.card (ramificationGroup G S i) * Nat.card H =
      Nat.card G * Nat.card (ramificationGroup H S i) := by
  set N := ramificationGroup G S i
  -- `[G_i H : G_i] = [H : H ∩ G_i]`, since `G_i` is normal.
  have h₁ := Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ H)
  rw [Subgroup.relIndex_sup_left] at h₁
  have h₂ := (N.subgroupOf H).card_mul_index
  have h₃ := N.card_mul_index
  rw [← subgroupOf_ramificationGroup, ← h₃, ← h₁, ← h₂, Subgroup.relIndex]
  ring

variable [Finite G]

/-- The integrand `[G : G^t H]` of the transition function is increasing in `t`. -/
private theorem monotone_index_upperRamificationGroup_sup (H : Subgroup G) :
    Monotone fun t ↦ (upperRamificationGroup G S t ⊔ H).index := fun _ _ h ↦
  Subgroup.index_antitone (sup_le_sup_right (upperRamificationGroup_antitone G S h) H)

/-- On `[i - 1, i]` with `i : ℤ` the increments of `φ_H` and of `v ↦ ∫_0^{φ_G(v)} k` agree, for the
integrand `k(t) = [G : G^t H] / [G : G_0 H]`: both are affine there, with slopes `#H_i / #H_0`
and `(#G_i / #G_0) · [G : G_i H] / [G : G_0 H]`, which agree by the product formula. -/
private theorem herbrandFun_sub_herbrandFun_eq_integral (H : Subgroup G) {i : ℤ} {x : ℝ}
    (h₁ : (i : ℝ) - 1 ≤ x) (h₂ : x ≤ i) :
    herbrandFun H S x - herbrandFun H S ((i : ℝ) - 1) =
      ∫ t in herbrandFun G S ((i : ℝ) - 1)..herbrandFun G S x,
        ((upperRamificationGroup G S t ⊔ H).index : ℝ) / (ramificationGroup G S 0 ⊔ H).index := by
  set c : ℝ := ((ramificationGroup G S 0 ⊔ H).index : ℝ)
  have hc : 0 < c := Nat.cast_pos.2 Subgroup.index_pos
  have hmono := (herbrandFun_strictMono G S).monotone
  -- On `(φ_G(i - 1), φ_G(x)]` the upper group `G^t` is the lower group `G_i`.
  have hI : (∫ t in herbrandFun G S ((i : ℝ) - 1)..herbrandFun G S x,
        ((upperRamificationGroup G S t ⊔ H).index : ℝ) / c) =
      (herbrandFun G S x - herbrandFun G S ((i : ℝ) - 1)) *
        ((ramificationGroup G S i ⊔ H).index / c) := by
    rw [← smul_eq_mul, ← intervalIntegral.integral_const]
    refine integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
    rw [uIoc_of_le (hmono h₁)] at ht
    rw [upperRamificationGroup_eq_of_herbrandFun_lt_of_le G S ht.1 (ht.2.trans (hmono h₂))]
  -- The product formula at `i` and at `0` identifies the slopes.
  have hPi : ((ramificationGroup G S i ⊔ H).index : ℝ) * Nat.card (ramificationGroup G S i) *
      Nat.card H = Nat.card G * Nat.card (ramificationGroup H S i) := by
    exact_mod_cast index_sup_mul_natCard_mul_natCard G S H i
  have hP0 : c * Nat.card (ramificationGroup G S 0) * Nat.card H =
      Nat.card G * Nat.card (ramificationGroup H S 0) := by
    simp only [c]
    exact_mod_cast index_sup_mul_natCard_mul_natCard G S H 0
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hG0 : (0 : ℝ) < Nat.card (ramificationGroup G S 0) := by exact_mod_cast Nat.card_pos
  have hH0 : (0 : ℝ) < Nat.card (ramificationGroup H S 0) := by exact_mod_cast Nat.card_pos
  have hslope : (Nat.card (ramificationGroup H S i) : ℝ) / Nat.card (ramificationGroup H S 0) =
      Nat.card (ramificationGroup G S i) / Nat.card (ramificationGroup G S 0) *
        ((ramificationGroup G S i ⊔ H).index / c) := by
    rw [div_mul_div_comm, div_eq_div_iff hH0.ne' (mul_pos hG0 hc).ne']
    refine mul_left_cancel₀ hG.ne' ?_
    linear_combination (-(Nat.card (ramificationGroup G S 0) * c)) * hPi +
      (Nat.card (ramificationGroup G S i) * ((ramificationGroup G S i ⊔ H).index : ℝ)) * hP0
  rw [hI, herbrandFun_sub_herbrandFun_of_le G S le_rfl h₁ h₂,
    herbrandFun_sub_herbrandFun_of_le H S le_rfl h₁ h₂, hslope]
  ring

/-- **The integral formula for the transition function.** For a subgroup `H` of a finite group
`G` acting on a local ring `S`,

`φ_H(ψ_G(u)) = ∫_0^u [G : G^t H] / [G : G_0 H] dt`

for every real `u`. For `G = Gal(M/K)` and `H = Gal(M/L)` the left side is `ψ_{L/K}(u)`, and the
normalizing index `[G : G_0 H]` is the residue degree of `L/K` over a separable residue extension
(`herbrandFun_inverseHerbrandFun_eq_integral_div_finrank`). -/
theorem herbrandFun_inverseHerbrandFun_eq_integral (H : Subgroup G) (u : ℝ) :
    herbrandFun H S (inverseHerbrandFun G S u) =
      ∫ t in (0 : ℝ)..u,
        ((upperRamificationGroup G S t ⊔ H).index : ℝ) / (ramificationGroup G S 0 ⊔ H).index := by
  set k : ℝ → ℝ := fun t ↦
    ((upperRamificationGroup G S t ⊔ H).index : ℝ) / (ramificationGroup G S 0 ⊔ H).index
  have hk (a b : ℝ) : IntervalIntegrable k volume a b :=
    ((Nat.mono_cast.comp (monotone_index_upperRamificationGroup_sup G S H)).div_const
      (Nat.cast_nonneg _)).intervalIntegrable
  -- `F(x) = φ_H(x) - ∫_0^{φ_G(x)} k` is constant on every interval `[i - 1, i]` with `i : ℤ`.
  set F : ℝ → ℝ := fun x ↦ herbrandFun H S x - ∫ t in (0 : ℝ)..herbrandFun G S x, k t
  have hstep {i : ℤ} {x : ℝ} (h₁ : (i : ℝ) - 1 ≤ x) (h₂ : x ≤ i) : F x = F ((i : ℝ) - 1) := by
    have h := herbrandFun_sub_herbrandFun_eq_integral G S H h₁ h₂
    rw [← integral_interval_sub_left (hk 0 _) (hk 0 _)] at h
    simp only [F]
    linarith
  -- Hence `F` vanishes at every integer, since it vanishes at `0`.
  have hint (i : ℤ) : F i = 0 := by
    induction i using Int.induction_on with
    | zero => simp [F]
    | succ i ih =>
      have h := hstep (i := i + 1) (x := ((i + 1 : ℤ) : ℝ)) (by push_cast; linarith) le_rfl
      push_cast at h ih ⊢
      rw [h, add_sub_cancel_right, ih]
    | pred i ih =>
      have h := hstep (i := -i) (x := ((-i : ℤ) : ℝ)) (by push_cast; linarith) le_rfl
      push_cast at h ih ⊢
      rw [← h, ih]
  -- So `F` vanishes everywhere; evaluate at `ψ_G(u)`.
  have h := hstep (by linarith [Int.ceil_lt_add_one (inverseHerbrandFun G S u)])
    (Int.le_ceil (inverseHerbrandFun G S u))
  rw [← Int.cast_one, ← Int.cast_sub, hint] at h
  simp only [F, herbrandFun_inverseHerbrandFun] at h
  linarith

end Integral

/-! ### The normalizing index as a residue degree -/

section ResidueDegree

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]

attribute [local instance] Ideal.Quotient.field in
/-- `#G = #G_0 · f_s`, with `f_s` the separable degree of the residue extension: every element of
`G` stabilizes the maximal ideal of `B`. -/
private theorem natCard_eq_natCard_ramificationGroup_zero_mul_finSepDegree :
    Nat.card G = Nat.card (ramificationGroup G B 0) *
      Field.finSepDegree (ResidueField A) (ResidueField B) := by
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have h := Ideal.card_stabilizer_eq_card_inertia_mul_finSepDegree (G := G) (maximalIdeal A)
    (maximalIdeal B)
  have htop : MulAction.stabilizer G (maximalIdeal B) = ⊤ :=
    eq_top_iff.2 fun σ _ ↦ smul_maximalIdeal σ
  rw [htop, Subgroup.card_top] at h
  rw [h, ramificationGroup_zero_eq_inertia]
  -- The residue field of a local ring is its quotient by the maximal ideal.
  rfl

variable (A) in
/-- **The normalizing index is the separable residue degree.** Let a finite group `G` act
faithfully on the local ring `B` by `A`-algebra automorphisms, with invariants the local ring
`A`, and let `H` be a subgroup. Then `[G : G_0 H]` is the separable degree of the residue
extension of the fixed ring `B^H` over `A`. For `G = Gal(M/K)` and `H = Gal(M/L)` this is the
separable residue degree of `L/K`. -/
theorem index_ramificationGroup_zero_sup_eq_finSepDegree (H : Subgroup G) :
    (ramificationGroup G B 0 ⊔ H).index =
      Field.finSepDegree (ResidueField A) (ResidueField (FixedPoints.subalgebra A B H)) := by
  -- `#G = #G_0 · f_s(B/A)` and `#H = #H_0 · f_s(B/B^H)`.
  have hG := natCard_eq_natCard_ramificationGroup_zero_mul_finSepDegree (A := A) (B := B) (G := G)
  have hH := natCard_eq_natCard_ramificationGroup_zero_mul_finSepDegree
    (A := FixedPoints.subalgebra A B H) (B := B) (G := H)
  -- The separable degree is multiplicative in the residue tower of `A ⊆ B^H ⊆ B`.
  have := Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra A B H) B H
  have : Algebra.IsIntegral B (ResidueField B) :=
    .of_surjective (Algebra.ofId B (ResidueField B)) residue_surjective
  have : Algebra.IsIntegral (FixedPoints.subalgebra A B H) (ResidueField B) := .trans B
  have : IsScalarTower (FixedPoints.subalgebra A B H) (ResidueField (FixedPoints.subalgebra A B H))
      (ResidueField B) :=
    -- Both maps into `ResidueField B` are the residue map of `B` after `B^H → B`, by definition.
    .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B) :=
    .tower_top (FixedPoints.subalgebra A B H)
  have hmul := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic (ResidueField A)
    (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B)
  -- Compare with the product formula `[G : G_0 H] · #G_0 · #H = #G · #H_0`.
  have hP := index_sup_mul_natCard_mul_natCard G B H 0
  have hf : Field.finSepDegree (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B) ≠ 0 :=
    fun h ↦ (Nat.card_pos (α := H)).ne' (by rw [hH, h, mul_zero])
  rw [hG, hH, ← hmul] at hP
  have hG0 : Nat.card (ramificationGroup G B 0) ≠ 0 := Nat.card_pos.ne'
  have hH0 : Nat.card (ramificationGroup H B 0) ≠ 0 := Nat.card_pos.ne'
  refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hG0 hH0) hf) ?_
  linear_combination hP

variable (A) in
/-- **Serre's integral formula for `ψ_{L/K}`.** Let a finite group `G` act faithfully on the local
ring `B` by `A`-algebra automorphisms, with invariants the local ring `A`, and let `H` be a
subgroup whose fixed ring `B^H` has separable residue extension over `A`, of degree `f`. Then

`φ_H(ψ_G(u)) = (1 / f) ∫_0^u [G : G^t H] dt`

for every real `u`. For `G = Gal(M/K)` and `H = Gal(M/L)` this is
`ψ_{L/K}(u) = (1 / f(L/K)) ∫_0^u [G : G^t H] dt`. Without separability `f` must be replaced by the
separable residue degree (`index_ramificationGroup_zero_sup_eq_finSepDegree`). -/
theorem herbrandFun_inverseHerbrandFun_eq_integral_div_finrank (H : Subgroup G)
    [Algebra.IsSeparable (ResidueField A) (ResidueField (FixedPoints.subalgebra A B H))] (u : ℝ) :
    herbrandFun H B (inverseHerbrandFun G B u) =
      ∫ t in (0 : ℝ)..u, ((upperRamificationGroup G B t ⊔ H).index : ℝ) /
        Module.finrank (ResidueField A) (ResidueField (FixedPoints.subalgebra A B H)) := by
  rw [herbrandFun_inverseHerbrandFun_eq_integral,
    index_ramificationGroup_zero_sup_eq_finSepDegree A,
    Field.finSepDegree_eq_finrank_of_isSeparable]

end ResidueDegree

end TauCeti.IsLocalRing
