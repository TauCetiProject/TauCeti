/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.Herbrand.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup.ResidueDegree
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.GroupTheory.Index.Basic

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
`[G : G_0 H]` is the separable degree of the residue extension of the fixed ring `B^H` over
`A` (`TauCeti.IsLocalRing.index_ramificationGroup_zero_sup_eq_finSepDegree`). Without
separability it can differ from the residue degree: for the purely inseparable residue extension
of degree `p` of `y^p - y = s t^{-p}` over `𝔽_p(s)((t))`, with `H = 1`, the index is
`[G : G_0] = 1`.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun_eq_integral`: the integral formula
  `φ_H(ψ_G(u)) = ∫_0^u [G : G^t H] / [G : G_0 H] dt`.
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

namespace TauCeti.IsLocalRing

/-! ### The integral formula for a finite group acting on a local ring -/

section Integral

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  [Finite G]

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
    rw [← subgroupOf_ramificationGroup]
    exact_mod_cast Subgroup.index_sup_mul_card_mul_card (N := ramificationGroup G S i) (H := H)
      Subgroup.le_normalizer_of_normal
  have hP0 : c * Nat.card (ramificationGroup G S 0) * Nat.card H =
      Nat.card G * Nat.card (ramificationGroup H S 0) := by
    simp only [c]
    rw [← subgroupOf_ramificationGroup]
    exact_mod_cast Subgroup.index_sup_mul_card_mul_card (N := ramificationGroup G S 0) (H := H)
      Subgroup.le_normalizer_of_normal
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
  -- Hence `F` is constant, and it vanishes at `0`; evaluate at `ψ_G(u)`.
  have h := apply_eq_apply_zero_of_forall_mem_Icc_intCast_sub_one
    (fun i x hx ↦ hstep (i := i) (x := x) hx.1 hx.2) (inverseHerbrandFun G S u)
  simp only [F, herbrandFun_inverseHerbrandFun, herbrandFun_zero, integral_same, sub_zero] at h
  linarith

end Integral

/-! ### Serre's form over a separable residue extension -/

section ResidueDegree

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]

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
