/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Star
-- Private: tactics and `ZMod 3` field helpers are proof-only.
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# Spectral projections and the Temperley–Lieb comparison map on `cubicFixed`

At loop value `δ = √3 = 2 cos (π / 6)`, the spectral projections
`cubicProjection N j = 3⁻¹ • (1 + U_j + U_j²)` in `CubicTorus N` lie in `cubicFixed N`, are
self-adjoint under `cubicAdjoint N`, satisfy `p_j * p_{j±1} * p_j = 3⁻¹ • p_j`, and commute at
distance `≥ 2`. Rescaling by `√3` gives the surjective star-compatible homomorphism
`cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`.

## Main definitions and results

* `cubicProjection`, `cubicFixedHom`.
* `cubicProjection_mul_self`, `cubicProjection_mul_cubicProjection_mul_cubicProjection`,
  `commute_cubicProjection`, `cubicFixedHom_star`.
* `adjoin_range_cubicProjection`, `cubicFixedHom_surjective`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* F. M. Goodman, P. de la Harpe, and V. F. R. Jones, *Coxeter Graphs and Towers of Algebras*,
  MSRI Publications 14, Springer (1989).
-/

public section

namespace TauCeti.TemperleyLieb

open Multiplicative

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact` for the analytic `StarRing` structure
on `TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) := ⟨Complex.conj_ofReal _⟩

/-! ### Spectral projections and the Temperley–Lieb comparison map -/

/-- **The spectral projection** `p_j = 3⁻¹ • (1 + U_j + U_j²)` at site `j : Fin N`. -/
noncomputable def cubicProjection (N : ℕ) (j : Fin N) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2)

theorem cubicProjection_def (N : ℕ) (j : Fin N) :
    cubicProjection N j = (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2) := (rfl)

private theorem one_add_cubicSite_mul_cubicSite (N : ℕ) (j : Fin N) :
    (1 + cubicSite N j + cubicSite N j ^ 2) * cubicSite N j =
      1 + cubicSite N j + cubicSite N j ^ 2 := by
  linear_combination (norm := noncomm_ring) cubicSite_pow_three N j

private theorem cubicSite_mul_one_add_cubicSite (N : ℕ) (j : Fin N) :
    cubicSite N j * (1 + cubicSite N j + cubicSite N j ^ 2) =
      1 + cubicSite N j + cubicSite N j ^ 2 := by
  linear_combination (norm := noncomm_ring) cubicSite_pow_three N j

@[simp] theorem cubicInversion_cubicProjection (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicProjection N j) = cubicProjection N j := by
  have h4 : (cubicSite N j ^ 2) ^ 2 = cubicSite N j := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, cubicSite_pow_three, one_mul]
  rw [cubicProjection_def, map_smul, map_add, map_add, map_one, map_pow, cubicInversion_cubicSite,
    h4, add_right_comm]

theorem cubicProjection_mem_cubicFixed (N : ℕ) (j : Fin N) :
    cubicProjection N j ∈ cubicFixed N :=
  mem_cubicFixed_iff.mpr (cubicInversion_cubicProjection N j)

@[simp] theorem cubicAdjoint_cubicProjection (N : ℕ) (j : Fin N) :
    cubicAdjoint N (cubicProjection N j) = cubicProjection N j := by
  have hsq : cubicAdjoint N (cubicSite N j ^ 2) = cubicSite N j := by
    rw [sq, cubicAdjoint_mul, cubicAdjoint_cubicSite, ← pow_add, show 2 + 2 = 3 + 1 from rfl,
      pow_succ, cubicSite_pow_three, one_mul]
  rw [cubicProjection_def, map_smulₛₗ, starRingEnd_apply, star_inv₀, star_ofNat, map_add, map_add,
    TwistedMonoidAlgebra.conjReverse_one, cubicAdjoint_cubicSite, hsq, add_right_comm]

/-- `cubicProjection N j` is idempotent: `p_j * p_j = p_j`. -/
@[simp] theorem cubicProjection_mul_self (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicProjection N j = cubicProjection N j := by
  set s := 1 + cubicSite N j + cubicSite N j ^ 2 with hs
  have hsu : s * cubicSite N j = s := one_add_cubicSite_mul_cubicSite N j
  have hsu2 : s * cubicSite N j ^ 2 = s := by rw [sq, ← mul_assoc, hsu, hsu]
  have hsum : s * s = (3 : ℂ) • s := by
    nth_rw 2 [hs]
    rw [mul_add, mul_add, mul_one, hsu, hsu2, show (3 : ℂ) = 1 + 1 + 1 by norm_num,
      add_smul, add_smul, one_smul]
  rw [cubicProjection_def, ← hs, smul_mul_smul_comm, hsum, smul_smul]
  congr 1; norm_num

/-- Sandwiching `W(a)` with `B(e_j, a) ≠ 0` between `cubicProjection N j` gives `0`. -/
theorem cubicProjection_mul_weyl_mul_cubicProjection_eq_zero {N : ℕ} (j : Fin N)
    {a : Multiplicative (Fin N → ZMod 3)} (hc : chainForm N (Pi.single j 1) a.toAdd ≠ 0) :
    cubicProjection N j * weyl N a * cubicProjection N j = 0 := by
  set u := cubicSite N j with hu_def
  set s := 1 + u + u ^ 2 with hs_def
  set c := chainForm N (Pi.single j 1) a.toAdd
  have hu : u * weyl N a = (cubeRootPow c : ℂ) • (weyl N a * u) := by
    simpa [u, c, cubicSite_def] using weyl_mul_comm N (ofAdd (Pi.single j 1)) a
  have hu2 : u ^ 2 * weyl N a = (cubeRootPow (2 * c) : ℂ) • (weyl N a * u ^ 2) := by
    rw [sq, mul_assoc, hu, mul_smul_comm, ← mul_assoc, hu, smul_mul_assoc, smul_smul,
      ← Units.val_mul, ← cubeRootPow_add, two_mul, mul_assoc (weyl N a) u u]
  have hus : u * s = s := cubicSite_mul_one_add_cubicSite N j
  have hu2s : u ^ 2 * s = s := by rw [sq, mul_assoc, hus, hus]
  have hs : s * weyl N a * s = 0 := by
    calc
      s * weyl N a * s
          = weyl N a * s + (cubeRootPow c : ℂ) • (weyl N a * (u * s)) +
              (cubeRootPow (2 * c) : ℂ) • (weyl N a * (u ^ 2 * s)) := by
            simp only [s, add_mul, one_mul, hu, hu2, smul_mul_assoc, mul_assoc]
      _ = (1 + (cubeRootPow c : ℂ) + (cubeRootPow (2 * c) : ℂ)) • (weyl N a * s) := by
            rw [hus, hu2s, add_smul, add_smul, one_smul]
      _ = 0 := by rw [one_add_cubeRootPow_add_two_mul hc, zero_smul]
  rw [cubicProjection_def, ← hu_def, ← hs_def]
  simp only [smul_mul_assoc, mul_smul_comm, hs, smul_zero]

/-- Adjacent projections satisfy `p_j * p_k * p_j = 3⁻¹ • p_j` when `|j - k| = 1`. -/
theorem cubicProjection_mul_cubicProjection_mul_cubicProjection {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j) :
    cubicProjection N j * cubicProjection N k * cubicProjection N j =
      (3 : ℂ)⁻¹ • cubicProjection N j := by
  have hc : ∀ {r : ZMod 3}, r ≠ 0 → chainForm N (Pi.single j 1) (Pi.single k r) ≠ 0 := by
    intro r hr; rw [chainForm_single_single]
    rcases h with hjk | hkj
    · simpa [hjk, show ¬ (k : ℕ) + 1 = j by omega] using hr
    · simpa [hkj, show ¬ (j : ℕ) + 1 = k by omega] using hr
  have h1 := cubicProjection_mul_weyl_mul_cubicProjection_eq_zero j (a := ofAdd (Pi.single k 1))
    (hc (by decide))
  have h2 := cubicProjection_mul_weyl_mul_cubicProjection_eq_zero j (a := ofAdd (Pi.single k 2))
    (hc (by decide))
  rw [cubicProjection_def N k, cubicSite_sq, cubicSite_def]
  simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, h1, h2, add_zero,
    cubicProjection_mul_self]

/-- Projections at distance at least two commute. -/
theorem commute_cubicProjection {N : ℕ} {j k : Fin N}
    (h : (j : ℕ) + 2 ≤ k ∨ (k : ℕ) + 2 ≤ j) :
    Commute (cubicProjection N j) (cubicProjection N k) := by
  have hsite := commute_cubicSite (N := N) h
  have hleft : Commute (cubicProjection N j) (cubicSite N k) := by
    rw [cubicProjection_def]
    exact (((Commute.one_left _).add_left hsite).add_left (hsite.pow_left 2)).smul_left _
  rw [cubicProjection_def N k]
  exact (((Commute.one_right _).add_right hleft).add_right (hleft.pow_right 2)).smul_right _

/-- **The comparison homomorphism** `F_m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`
sending each generator `e j` to `√3 • cubicProjection (m - 1) j`. -/
noncomputable def cubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
  have hsq : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by positivity)
  lift (fun j ↦ ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
      (cubicFixed (m - 1)).smul_mem (cubicProjection_mem_cubicFixed (m - 1) j) _⟩)
    (fun j ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, Subalgebra.coe_smul, smul_mul_smul_comm,
        cubicProjection_mul_self, smul_smul, hsq])
    (fun h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul]
      rw [smul_mul_smul_comm, smul_mul_smul_comm,
        cubicProjection_mul_cubicProjection_mul_cubicProjection h, smul_smul, hsq]
      congr 1; ring)
    (fun h ↦ Subtype.ext <| by
      simpa [Subalgebra.coe_mul, smul_mul_smul_comm] using
        ((commute_cubicProjection (N := m - 1) h).smul_left (Real.sqrt 3 : ℂ)
          |>.smul_right (Real.sqrt 3 : ℂ)).eq)

theorem coe_cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by simp [cubicFixedHom]

@[simp] theorem cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) =
      ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
        (cubicFixed (m - 1)).smul_mem (cubicProjection_mem_cubicFixed (m - 1) j) _⟩ :=
  Subtype.ext (coe_cubicFixedHom_e m j)

/-- `cubicFixedHom m` intertwines `star` with `cubicAdjoint (m - 1)` in `CubicTorus (m - 1)`. -/
theorem coe_cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (cubicFixedHom m (star x) : CubicTorus (m - 1)) =
      cubicAdjoint (m - 1) (cubicFixedHom m x) := by
  induction x using TemperleyLieb.induction with
  | e j =>
    rw [star_e, coe_cubicFixedHom_e, map_smulₛₗ, starRingEnd_apply, Complex.star_def,
      Complex.conj_ofReal, cubicAdjoint_cubicProjection]
  | algebraMap c =>
    have hstar : star (algebraMap ℂ (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) c) =
        algebraMap ℂ _ (star c) := by
      rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, Algebra.algebraMap_eq_smul_one]
    rw [hstar, AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul, Subalgebra.coe_one,
      Subalgebra.coe_smul, Subalgebra.coe_one, map_smulₛₗ, starRingEnd_apply,
      TwistedMonoidAlgebra.conjReverse_one]
  | add x y hx hy =>
    have hadd (a b) : cubicFixedHom m (a + b) = cubicFixedHom m a + cubicFixedHom m b :=
      (cubicFixedHom m).map_add' a b
    rw [star_add, hadd, hadd, Subalgebra.coe_add, Subalgebra.coe_add,
      map_add (cubicAdjoint (m - 1)), hx, hy]
  | mul x y hx hy =>
    rw [star_mul, map_mul, map_mul, Subalgebra.coe_mul, Subalgebra.coe_mul, cubicAdjoint_mul,
      hx, hy]

/-- `cubicFixedHom m` intertwines `star` with `cubicFixedAdjoint (m - 1)`. -/
@[simp] theorem cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedHom m (star x) = cubicFixedAdjoint (m - 1) (cubicFixedHom m x) :=
  Subtype.ext (by rw [coe_cubicFixedHom_star, coe_cubicFixedAdjoint])

/-! ### Generation of `cubicFixed N` by `cubicProjection N` and surjectivity of `cubicFixedHom` -/

/-- Symmetrized Weyl element `S(a) = W(a) + W(a⁻¹)` in `CubicTorus N`. -/
private noncomputable def symmWeyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) : CubicTorus N :=
  weyl N a + weyl N a⁻¹

private theorem symmWeyl_inv (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    symmWeyl N a⁻¹ = symmWeyl N a := by simp [symmWeyl, add_comm]

private theorem symmWeyl_one (N : ℕ) : symmWeyl N 1 = (2 : ℂ) • 1 := by simp [symmWeyl, two_smul]

private theorem symmWeyl_mul_symmWeyl (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    symmWeyl N a * symmWeyl N b =
      (cubicFactor N a b : ℂ) • symmWeyl N (a * b) +
        (((cubicFactor N a b)⁻¹ : ℂˣ) : ℂ) • symmWeyl N (a * b⁻¹) := by
  have hab : a⁻¹ * b⁻¹ = (a * b)⁻¹ := toAdd.injective (by ext; simp [add_comm])
  have hab' : a⁻¹ * b = (a * b⁻¹)⁻¹ := toAdd.injective (by ext; simp [add_comm])
  simp only [symmWeyl, add_mul, mul_add, weyl_mul_weyl, cubicFactor_inv_right,
    cubicFactor_inv_left, hab, hab', inv_inv, smul_add]
  abel

private theorem symmWeyl_mul_mem_of_chainForm_ne_zero {N : ℕ} {S : Subalgebra ℂ (CubicTorus N)}
    {a b : Multiplicative (Fin N → ZMod 3)}
    (ha : symmWeyl N a ∈ S) (hb : symmWeyl N b ∈ S)
    (hc : chainForm N a.toAdd b.toAdd ≠ 0) :
    symmWeyl N (a * b) ∈ S := by
  set α : ℂ := (cubicFactor N a b : ℂ)
  set β : ℂ := (((cubicFactor N a b)⁻¹ : ℂˣ) : ℂ)
  have hαβ : α * β = 1 := by simp [α, β]
  have hβα : β * α = 1 := mul_comm α β ▸ hαβ
  have hα3 : α ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, cubicFactor_def, cubeRootPow_pow_three, Units.val_one]
  have hα1 : α ≠ 1 := fun h1 ↦ by
    have hu : cubicFactor N a b = 1 := Units.ext h1
    rw [cubicFactor_def, cubeRootPow_eq_one_iff] at hu
    exact hc ((mul_eq_zero.mp hu).resolve_left (by decide))
  have hba : symmWeyl N b * symmWeyl N a = β • symmWeyl N (a * b) + α • symmWeyl N (a * b⁻¹) := by
    rw [symmWeyl_mul_symmWeyl, cubicFactor_swap, inv_inv, mul_comm b a,
      show b * a⁻¹ = (a * b⁻¹)⁻¹ from toAdd.injective (by ext; simp), symmWeyl_inv]
  have hcomb : α • (symmWeyl N a * symmWeyl N b) + (-β) • (symmWeyl N b * symmWeyl N a) =
      (α ^ 2 - β ^ 2) • symmWeyl N (a * b) := by
    rw [symmWeyl_mul_symmWeyl N a b, hba, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      smul_smul, hαβ, show -β * β = -(β ^ 2) by ring, show -β * α = -1 by linear_combination -hβα,
      ← sq α, add_add_add_comm, ← add_smul, ← add_smul, add_neg_cancel, zero_smul, add_zero,
      ← sub_eq_add_neg]
  have hne : α ^ 2 - β ^ 2 ≠ 0 := fun h0 ↦ hα1 <| sub_eq_zero.mp <| by
    linear_combination (α ^ 2) * h0 - α * hα3 + (β * α + 1) * hβα
  have hmem := S.smul_mem
    (hcomb ▸ S.add_mem (S.smul_mem (S.mul_mem ha hb) α) (S.smul_mem (S.mul_mem hb ha) (-β)))
    (α ^ 2 - β ^ 2)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hmem

private theorem symmWeyl_single_mem_adjoin (N : ℕ) (j : Fin N) (r : ZMod 3) :
    symmWeyl N (ofAdd (Pi.single j r)) ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  have hp : symmWeyl N (ofAdd (Pi.single j 1)) ∈ S := by
    have h1 : (1 : CubicTorus N) + (-1 : ℂ) • (1 : CubicTorus N) = 0 := by
      nth_rw 1 [← one_smul ℂ (1 : CubicTorus N)]
      rw [← add_smul, add_neg_cancel, zero_smul]
    have heq : symmWeyl N (ofAdd (Pi.single j 1)) =
        (3 : ℂ) • cubicProjection N j + (-1 : ℂ) • (1 : CubicTorus N) := by
      rw [symmWeyl, ← ofAdd_neg, ← Pi.single_neg, show (-1 : ZMod 3) = 2 by decide, ← cubicSite_sq,
        ← cubicSite_def, cubicProjection_def, smul_smul, mul_inv_cancel₀ (by norm_num), one_smul,
        add_right_comm (1 + cubicSite N j), add_right_comm 1 (cubicSite N j), h1, zero_add]
    exact heq ▸ S.add_mem (S.smul_mem (Algebra.subset_adjoin (Set.mem_range_self j)) (3 : ℂ))
      (S.smul_mem S.one_mem (-1 : ℂ))
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by revert r; decide
  rcases hcases with rfl | rfl | rfl
  · rw [Pi.single_zero, ofAdd_zero, symmWeyl_one]; exact S.smul_mem S.one_mem (2 : ℂ)
  · exact hp
  · simpa [← show (-1 : ZMod 3) = 2 by decide, Pi.single_neg, ofAdd_neg, symmWeyl_inv] using hp

private theorem chainForm_prefix_single {N m : ℕ} (hm : m + 1 < N)
    {y : Multiplicative (Fin N → ZMod 3)} (hy : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → y.toAdd i = 0)
    (r : ZMod 3) :
    chainForm N y.toAdd (Pi.single ⟨m + 1, hm⟩ r) = y.toAdd ⟨m, by omega⟩ * r := by
  rw [chainForm_def, Fintype.sum_eq_single (⟨m, by omega⟩ : Fin N)]
  · rw [Fintype.sum_eq_single (⟨m + 1, hm⟩ : Fin N)]
    · simp
    · intro j hj; simp [show ¬ (m : ℕ) + 1 = (j : ℕ) from fun h ↦ hj (Fin.ext h.symm)]
  · intro i hi
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    split_ifs with hij
    · have hj : j ≠ ⟨m + 1, hm⟩ := fun h ↦
        hi (Fin.ext (by have := congrArg Fin.val h; simp at this ⊢; omega))
      by_cases him : i = ⟨m + 1, hm⟩
      · subst him; simp [Pi.single_eq_of_ne hj, hy j (by simp at hij; omega)]
      · simp [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne him]
    · rfl

/-- Inductive elimination step for `symmWeyl_mem_adjoin_of_support`. -/
private theorem symmWeyl_mul_single_mem_adjoin_of_prefix {N m : ℕ} (hm : m + 1 < N)
    (ih : ∀ z : Multiplicative (Fin N → ZMod 3),
      (∀ i : Fin N, m + 1 ≤ (i : ℕ) → z.toAdd i = 0) →
      symmWeyl N z ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)))
    {y : Multiplicative (Fin N → ZMod 3)}
    (hy : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → y.toAdd i = 0)
    {r : ZMod 3} (hr : r ≠ 0) :
    symmWeyl N (y * ofAdd (Pi.single ⟨m + 1, hm⟩ r)) ∈
      Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  let jk : Fin N := ⟨m + 1, hm⟩
  let jm : Fin N := ⟨m, by omega⟩
  have hstep : ∀ (z : Multiplicative (Fin N → ZMod 3)) (s : ZMod 3),
      (∀ i : Fin N, m + 1 ≤ (i : ℕ) → z.toAdd i = 0) → z.toAdd jm ≠ 0 → s ≠ 0 →
      symmWeyl N (z * ofAdd (Pi.single jk s)) ∈ S := fun z s hz hzm hs ↦
    symmWeyl_mul_mem_of_chainForm_ne_zero (ih z hz) (symmWeyl_single_mem_adjoin N jk s)
      (by rw [toAdd_ofAdd, chainForm_prefix_single hm hz]; exact mul_ne_zero hzm hs)
  by_cases hym : y.toAdd jm = 0
  · let em : Multiplicative (Fin N → ZMod 3) := ofAdd (Pi.single jm 1)
    let b := y * em
    let c := em⁻¹ * ofAdd (Pi.single jk r)
    let y' := y * ofAdd (Pi.single jm 2)
    have hbc : b * c = y * ofAdd (Pi.single jk r) := toAdd.injective (by ext; simp [b, c])
    have hbcinv : b * c⁻¹ = y' * ofAdd (Pi.single jk (-r)) :=
      toAdd.injective (by ext i; simp [b, c, y', em, Pi.single_apply]; split_ifs <;> ring)
    have hne_jm : ∀ i : Fin N, m + 1 ≤ (i : ℕ) → i ≠ jm := fun i hi h ↦ by subst h; simp [jm] at hi
    have hb_mem : symmWeyl N b ∈ S := ih b fun i hi ↦ by
      simp [b, em, Pi.single_eq_of_ne (hne_jm i hi), hy i hi]
    have hc_mem : symmWeyl N c ∈ S :=
      hstep em⁻¹ r (fun i hi ↦ by simp [em, Pi.single_eq_of_ne (hne_jm i hi)]) (by simp [em]) hr
    have hy'_mem : symmWeyl N (b * c⁻¹) ∈ S :=
      hbcinv ▸ hstep y' (-r) (fun i hi ↦ by simp [y', Pi.single_eq_of_ne (hne_jm i hi), hy i hi])
        (by simp only [y', toAdd_mul, toAdd_ofAdd, Pi.add_apply, hym, zero_add, Pi.single_eq_same,
          ne_eq]; decide) (neg_ne_zero.mpr hr)
    set γ : ℂ := (((cubicFactor N b c)⁻¹ : ℂˣ) : ℂ)
    have hcomb : symmWeyl N b * symmWeyl N c + (-γ) • symmWeyl N (b * c⁻¹) =
        (cubicFactor N b c : ℂ) • symmWeyl N (y * ofAdd (Pi.single jk r)) := by
      rw [symmWeyl_mul_symmWeyl N b c, hbc, add_assoc, ← add_smul, add_neg_cancel, zero_smul,
        add_zero]
    have hres := S.smul_mem
      (hcomb ▸ S.add_mem (S.mul_mem hb_mem hc_mem) (S.smul_mem hy'_mem (-γ))) γ
    rwa [smul_smul, show γ * (cubicFactor N b c : ℂ) = 1 by simp [γ],
      one_smul] at hres
  · exact hstep y r hy hym hr

private theorem symmWeyl_mem_adjoin_of_support (N k : ℕ) :
    ∀ (a : Multiplicative (Fin N → ZMod 3)),
      (∀ i : Fin N, k ≤ (i : ℕ) → a.toAdd i = 0) →
      symmWeyl N a ∈ Algebra.adjoin ℂ (Set.range (cubicProjection N)) := by
  induction k with
  | zero =>
    intro a ha
    have ha1 : a = 1 := toAdd.injective (funext fun i ↦ ha i (Nat.zero_le _))
    rw [ha1, symmWeyl_one]
    exact (Algebra.adjoin ℂ (Set.range (cubicProjection N))).smul_mem (Subalgebra.one_mem _) (2 : ℂ)
  | succ k ih =>
    intro a ha
    by_cases hkN : k < N
    · let jk : Fin N := ⟨k, hkN⟩
      set r := a.toAdd jk
      by_cases hr : r = 0
      · refine ih a fun i hi ↦ ?_
        rcases eq_or_lt_of_le hi with hval | hlt
        · exact (Fin.ext hval.symm : i = jk) ▸ hr
        · exact ha i hlt
      · let d : Multiplicative (Fin N → ZMod 3) := ofAdd (Pi.single jk r)
        let y : Multiplicative (Fin N → ZMod 3) := a * d⁻¹
        have hy : ∀ i : Fin N, k ≤ (i : ℕ) → y.toAdd i = 0 := fun i hi ↦ by
          rcases eq_or_lt_of_le hi with hval | hlt
          · have hij : i = jk := Fin.ext hval.symm; subst hij; simp [y, d, r]
          · have hne : i ≠ jk := fun h ↦ by subst h; exact Nat.lt_irrefl _ hlt
            simp [y, d, Pi.single_eq_of_ne hne, ha i hlt]
        rw [show a = y * d by simp [y]]
        rcases k with _ | m
        · rw [show y = 1 from toAdd.injective (funext fun i ↦ hy i (Nat.zero_le _)), one_mul]
          exact symmWeyl_single_mem_adjoin N jk r
        · exact symmWeyl_mul_single_mem_adjoin_of_prefix hkN ih hy hr
    · exact ih a fun i _ ↦ absurd i.isLt (by omega)

/-- **The projections `cubicProjection N` generate `cubicFixed N`** as a `ℂ`-algebra. -/
theorem adjoin_range_cubicProjection (N : ℕ) :
    Algebra.adjoin ℂ (Set.range (cubicProjection N)) = cubicFixed N := by
  let S : Subalgebra ℂ (CubicTorus N) := Algebra.adjoin ℂ (Set.range (cubicProjection N))
  refine le_antisymm (Algebra.adjoin_le_iff.mpr <| by
    rintro _ ⟨j, rfl⟩; exact cubicProjection_mem_cubicFixed N j) fun x hx ↦ ?_
  have hsymm : ∀ z : CubicTorus N, z + cubicInversion N z ∈ S := fun z ↦ by
    induction (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3))
        (cubicFactor N)).mem_span z using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨a, rfl⟩ := hw
      rw [TwistedMonoidAlgebra.basis_apply, ← weyl_def, cubicInversion_weyl]
      exact symmWeyl_mem_adjoin_of_support N N a fun i hi ↦ absurd i.isLt (not_lt.mpr hi)
    | zero => simp [S.zero_mem]
    | add _ _ _ _ hy hw => rw [map_add, add_add_add_comm]; exact S.add_mem hy hw
    | smul c _ _ hy => rw [map_smul, ← smul_add]; exact S.smul_mem hy c
  have hx2 := hsymm x
  rw [mem_cubicFixed_iff.mp hx, ← two_smul ℂ x] at hx2
  have hres := S.smul_mem hx2 (2 : ℂ)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul] at hres

/-- **Surjectivity of `cubicFixedHom`.** For every `m : ℕ`, the comparison homomorphism
`TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` is surjective. -/
theorem cubicFixedHom_surjective (m : ℕ) : Function.Surjective (cubicFixedHom m) := by
  have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  let Φ : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] CubicTorus (m - 1) :=
    (cubicFixed (m - 1)).val.comp (cubicFixedHom m)
  have hrange : Φ.range = cubicFixed (m - 1) := by
    rw [← Algebra.map_top, ← adjoin_range_e, AlgHom.map_adjoin, ← Set.range_comp]
    let S₁ := Algebra.adjoin ℂ (Set.range (Φ ∘ e (Real.sqrt 3 : ℂ)))
    let S₂ := Algebra.adjoin ℂ (Set.range (cubicProjection (m - 1)))
    have hadj : S₁ = S₂ := le_antisymm
      (Algebra.adjoin_le_iff.mpr <| by
        rintro _ ⟨j, rfl⟩
        simpa [Φ, coe_cubicFixedHom_e] using
          S₂.smul_mem (Algebra.subset_adjoin (Set.mem_range_self j)) (Real.sqrt 3 : ℂ))
      (Algebra.adjoin_le_iff.mpr <| by
        rintro _ ⟨j, rfl⟩
        have hj0 : (Φ ∘ e (Real.sqrt 3 : ℂ)) j ∈ S₁ :=
          Algebra.subset_adjoin (Set.mem_range_self j)
        simp only [Function.comp_apply, Φ, AlgHom.comp_apply, Subalgebra.coe_val,
          coe_cubicFixedHom_e] at hj0
        have hres := S₁.smul_mem hj0 (Real.sqrt 3 : ℂ)⁻¹
        rwa [smul_smul, inv_mul_cancel₀ hsqrt, one_smul] at hres)
    exact hadj.trans (adjoin_range_cubicProjection (m - 1))
  intro y
  obtain ⟨x, hx⟩ : (y : CubicTorus (m - 1)) ∈ Φ.range := hrange.symm ▸ y.2
  exact ⟨x, Subtype.ext hx⟩

end TauCeti.TemperleyLieb
