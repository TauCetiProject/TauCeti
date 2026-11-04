/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import TauCeti.RingTheory.CyclicCohomology.RowExactness
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Connes' periodicity operator on cyclic cochains and cyclic cohomology

Connes' periodicity operator `S : HCⁿ(A; M) → HCⁿ⁺²(A; M)` is defined at the cochain level from the
double-face operator `S₀ : Cⁿ → Cⁿ⁺²`,

`(S₀ φ)(a₀, …, aₙ₊₂) = ∑_{j = 0}^n ∑_{r ≤ j} (-1)^(j - r) φ(dᵣ(d_{j+1}(a₀, …, aₙ₊₂)))`,

which evaluates the character of the exterior product with the scalar `2`-cocycle
`(a₀, a₁, a₂) ↦ a₀ a₁ a₂` on a cyclic cocycle `φ`
(`TauCeti.exteriorProductCocycle_scalarCocycle_one_apply_tmul_one`).

This file develops `S₀`, Connes' averaged operator `S = (n + 3)⁻¹ N S₀` on cyclic cochains, and the
induced periodicity map on cyclic cohomology:

* **Simplicial and row-homotopy decomposition.** Write
  `H' = ∑_{j ≤ n+1} ∑_{k < j} λᵏ` for the unscaled numerator of `TauCeti.cyclicRowHomotopy` in
  degree `n + 1`, satisfying `(1 - λ) H' = H' (1 - λ) = (n + 2) - N`. On a cyclic `n`-cochain `φ`,
  `b (H' (b' φ))` differs from `S₀ φ` by `-∑_{r ≤ n} (n + 1 - r) (-1)ʳ dᵣ*(b φ)`. In particular,
  for every cyclic cocycle `φ`, `S₀ φ = b (H' (b' φ))` identically over any commutative ring.
* **Cocycle preservation and Connes' Proposition 12.** From `S₀ φ = b (H' (b' φ))` and the cyclic
  bicomplex relations `(1 - λ) b = b' (1 - λ)` and `b N = N b'`, `S₀` maps cyclic `n`-cocycles into
  cyclic `(n + 2)`-cocycles over every commutative ring, and on every cyclic `n`-cochain `ψ`,
  `b (N (S₀ ψ)) = (n + 1) • S₀ (b ψ)`. When `n + 3` is invertible in `R`, Connes' operator
  `S = (n + 3)⁻¹ N S₀` restricts to `S₀` on cyclic cocycles and satisfies
  `(n + 3) • b (S ψ) = (n + 1) • S (b ψ)`.
* **Descent to cyclic cohomology.** When every `q + 1` with `q < n` is invertible in `R` (in
  particular in degree zero over any commutative ring, and in all degrees when `R` is a
  `ℚ`-algebra), `S₀` maps cyclic coboundaries into cyclic coboundaries. For a `ℚ`-algebra this
  yields `TauCeti.cyclicCohomology.periodicity : HCⁿ(A; M) ⟶ HCⁿ⁺²(A; M)`.

## Main definitions

* `TauCeti.cochainPeriodicity`: the double-face operator `S₀ : Cⁿ → Cⁿ⁺²`.
* `TauCeti.cyclicRowHomotopySum`: the unscaled row homotopy `∑_{j ≤ n} ∑_{k < j} λᵏ`.
* `TauCeti.cyclicCocyclesPeriodicity`: `S₀` restricted to cyclic cocycles, over any commutative
  ring.
* `TauCeti.connesS`: Connes' averaged operator `(n + 3)⁻¹ N S₀` on cyclic cochains when `n + 3` is
  invertible.
* `TauCeti.cyclicCohomology.periodicity`: Connes' periodicity map `S : HCⁿ(A; M) ⟶ HCⁿ⁺²(A; M)`
  over a `ℚ`-algebra.

## Main results

* `TauCeti.cochainPeriodicity_apply_const_of_isIdempotentElem`: `(S₀ φ)(e, …, e) = (n / 2 + 1) •
  φ(e, …, e)` for an idempotent `e`.
* `TauCeti.hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCocycles`:
  `b (H' (b' φ)) = S₀ φ` for every cyclic cocycle `φ`.
* `TauCeti.hochschildCoboundary_cyclicNorm_cochainPeriodicity`: `b (N (S₀ ψ)) = (n + 1) • S₀ (b ψ)`
  for every cyclic `n`-cochain `ψ`.
* `TauCeti.smul_cyclicHochschildCoboundary_connesS`: `(n + 3) • b (S ψ) = (n + 1) • S (b ψ)`.
* `TauCeti.cyclicCohomology.map_comp_periodicity`: naturality of `S` with respect to algebra
  homomorphisms.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, Proposition 12 and Corollary 13.
* J.-L. Loday, *Cyclic Homology*, §2.2.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

/-! ### The double-face operator `S₀` on multilinear cochains -/

section CochainPeriodicity

variable (R : Type*) (A : Type u) (M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- Connes' unaveraged cochain periodicity operator `S₀ : Cⁿ → Cⁿ⁺²`, sending an `n`-cochain `φ` to
`(a₀, …, aₙ₊₂) ↦ ∑_{j = 0}^n ∑_{r ≤ j} (-1)^(j - r) φ(dᵣ(d_{j+1}(a₀, …, aₙ₊₂)))`. -/
def cochainPeriodicity (n : ℕ) :
    MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      MultilinearMap R (fun _ : Fin (n + 3) ↦ A) M :=
  ∑ j : Fin (n + 1), ∑ r ∈ Finset.Iic j,
    (-1 : ℤ) ^ ((j : ℕ) - r) •
      (hochschildCoface R A M j.succ.castSucc ∘ₗ hochschildCoface R A M r.castSucc)

variable {R A M} {n : ℕ}

/-- Pointwise formula for `cochainPeriodicity`. -/
@[simp]
theorem cochainPeriodicity_apply (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 3) → A) :
    cochainPeriodicity R A M n φ a =
      ∑ j : Fin (n + 1), ∑ r ∈ Finset.Iic j,
        (-1 : ℤ) ^ ((j : ℕ) - r) •
          φ (hochschildFace r.castSucc (hochschildFace j.succ.castSucc a)) := by
  simp [cochainPeriodicity, LinearMap.sum_apply]

/-- Pulling cochains back along a homomorphism of nonunital algebras commutes with
`cochainPeriodicity`. -/
theorem cochainPeriodicity_compLinearMap {B : Type u} [NonUnitalNonAssocSemiring B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B] (f : A →ₙₐ[R] B)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ B) M) :
    cochainPeriodicity R A M n (φ.compLinearMap fun _ ↦ (f : A →ₗ[R] B)) =
      (cochainPeriodicity R B M n φ).compLinearMap fun _ ↦ (f : A →ₗ[R] B) := by
  ext a
  simp only [cochainPeriodicity_apply, MultilinearMap.compLinearMap_apply]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun r _ ↦ ?_
  congr 2
  exact (comp_hochschildFace f r.castSucc _).trans
    (congrArg (hochschildFace r.castSucc) (comp_hochschildFace f j.succ.castSucc a))

/-- Applying a linear map to the values of a cochain commutes with `cochainPeriodicity`. -/
theorem compMultilinearMap_cochainPeriodicity {N : Type*} [AddCommGroup N] [Module R N]
    [SMulCommClass R R N] (n : ℕ) (g : M →ₗ[R] N)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    g.compMultilinearMap (cochainPeriodicity R A M n φ) =
      cochainPeriodicity R A N n (g.compMultilinearMap φ) := by
  ext a
  simp [LinearMap.compMultilinearMap_apply, map_sum, map_zsmul]

/-- The alternating double sum `∑_{j = 0}^n ∑_{r ≤ j} (-1)^(j - r)` equals `n / 2 + 1`. -/
private theorem sum_Iic_neg_one_pow_sub (n : ℕ) :
    (∑ j : Fin (n + 1), ∑ r ∈ Finset.Iic j, (-1 : ℤ) ^ ((j : ℕ) - r)) = (n / 2 + 1 : ℕ) := by
  have hinner (m : ℕ) :
      (∑ r ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - r)) = if Even m then 1 else 0 := by
    have hcongr : (∑ r ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - r)) =
        ∑ r ∈ Finset.range (m + 1), (-1 : ℤ) ^ r := by
      rw [← Finset.sum_range_reflect (fun k ↦ (-1 : ℤ) ^ k) (m + 1)]
      simp
    rw [hcongr, neg_one_geom_sum]
    split_ifs <;> simp_all [Nat.even_add_one]
  have hfin (j : Fin (n + 1)) :
      (∑ r ∈ Finset.Iic j, (-1 : ℤ) ^ ((j : ℕ) - r)) = if Even (j : ℕ) then 1 else 0 := by
    rw [← hinner j]
    refine Finset.sum_bij (fun r _ ↦ (r : ℕ)) ?_ ?_ ?_ ?_
    · intro r hr
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Fin.le_def.1 (Finset.mem_Iic.1 hr)))
    · intro r₁ _ r₂ _ h
      exact Fin.ext h
    · intro k hk
      have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
      exact ⟨⟨k, lt_of_le_of_lt hkj j.2⟩, Finset.mem_Iic.2 hkj, rfl⟩
    · intro _ _
      rfl
  simp_rw [hfin]
  clear hfin hinner
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ if Even k then (1 : ℤ) else 0) (n + 1)]
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hodd : ¬Even (k + k + 1) := fun ⟨m, hm⟩ ↦ by omega
      rw [ite_eq_right hodd]
      push_cast
      omega
    · have heven : Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩
      rw [ite_eq_left heven]
      push_cast
      omega

/-- Evaluating `cochainPeriodicity` on a constant tuple with idempotent entry multiplies the value
by `n / 2 + 1`. -/
theorem cochainPeriodicity_apply_const_of_isIdempotentElem
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) {e : A} (he : IsIdempotentElem e) :
    cochainPeriodicity R A M n φ (fun _ ↦ e) = (n / 2 + 1 : ℕ) • φ (fun _ ↦ e) := by
  rw [cochainPeriodicity_apply]
  simp only [hochschildFace_const_of_isIdempotentElem he, ← Finset.sum_smul,
    sum_Iic_neg_one_pow_sub, natCast_zsmul]

end CochainPeriodicity

/-- On a commutative semiring, `cochainPeriodicity` multiplies a product cochain by `n / 2 + 1`. -/
theorem cochainPeriodicity_mkPiRing {S : Type u} {M : Type*} [CommSemiring S] [AddCommGroup M]
    [Module S M] (n : ℕ) (m : M) :
    cochainPeriodicity S S M n (MultilinearMap.mkPiRing S (Fin (n + 1)) m) =
      MultilinearMap.mkPiRing S (Fin (n + 3)) ((n / 2 + 1 : ℕ) • m) := by
  rw [← (cochainPeriodicity S S M n
    (MultilinearMap.mkPiRing S (Fin (n + 1)) m)).mkPiRing_apply_one_eq_self,
    cochainPeriodicity_apply_const_of_isIdempotentElem _ IsIdempotentElem.one]
  simp

/-! ### Simplicial decomposition and the unscaled row homotopy -/

section Simplicial

section Semigroup

variable {R : Type*} {A : Type u} {M : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M] {n : ℕ}

/-- Auxiliary cochain operator `-∑_{s = 0}^{n+1} s (-1)ˢ δₛ` whose Hochschild coboundary gives
`cochainPeriodicity` on Hochschild cocycles. -/
private def cupOneSelf (n : ℕ) :
    MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M →ₗ[R]
      MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M :=
  -∑ s : Fin (n + 2), (s : ℤ) • (-1 : ℤ) ^ (s : ℕ) • hochschildCoface R A M s

/-- Auxiliary cochain operator `∑_{r = 0}^n (n + 1 - r) (-1)ʳ δᵣ` measuring the coboundary defect
in `hochschildCoboundary_cupOneSelf_add`. -/
private def cupOneLeft (n : ℕ) :
    MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M →ₗ[R]
      MultilinearMap R (fun _ : Fin (n + 3) ↦ A) M :=
  ∑ r : Fin (n + 1), ((n + 1 : ℤ) - r) • (-1 : ℤ) ^ (r : ℕ) •
    hochschildCoface R A M r.castSucc.castSucc

/-- Pure simplicial decomposition of `cochainPeriodicity`: for any cochain `φ`,
`b (cupOneSelf φ) + cupOneLeft (b φ) = S₀ φ`. -/
private theorem hochschildCoboundary_cupOneSelf_add
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    hochschildCoboundary R A M (n + 1) (cupOneSelf n φ) +
        cupOneLeft n (hochschildCoboundary R A M n φ) =
      cochainPeriodicity R A M n φ := by
  ext a
  set F : Fin (n + 3) → Fin (n + 2) → M := fun i s ↦ φ (hochschildFace s (hochschildFace i a))
  have hF (i s : Fin (n + 2)) (his : i ≤ s) : F s.succ i = F i.castSucc s := by
    simp only [F, hochschildFace_hochschildFace his]
  set w : Fin (n + 3) → ℤ := fun i ↦ if (i : ℕ) ≤ n + 1 then (n + 1 : ℤ) - i else 0
  have hleft : cupOneLeft n (hochschildCoboundary R A M n φ) a =
      ∑ i : Fin (n + 3), ∑ s : Fin (n + 2), (w i * (-1 : ℤ) ^ ((i : ℕ) + s)) • F i s := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hlast₁ : w (Fin.last (n + 2)) = 0 := by simp [w]
    have hlast₂ : w (Fin.last (n + 1)).castSucc = 0 := by simp [w]
    simp only [hlast₁, hlast₂, zero_mul, zero_smul, Finset.sum_const_zero, add_zero]
    rw [cupOneLeft, LinearMap.sum_apply, sum_apply]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hr : (r : ℕ) ≤ n + 1 := by omega
    simp only [LinearMap.smul_apply, smul_apply, hochschildCoface_apply,
      hochschildCoboundary_apply, Finset.smul_sum, w, Fin.val_castSucc, hr, ↓reduceIte, F]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [smul_smul, smul_smul, pow_add]
    congr 1
    ring
  have hself : hochschildCoboundary R A M (n + 1) (cupOneSelf n φ) a =
      ∑ i : Fin (n + 3), ∑ s : Fin (n + 2), (-(s : ℤ) * (-1 : ℤ) ^ ((i : ℕ) + s)) • F i s := by
    rw [hochschildCoboundary_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [cupOneSelf, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      neg_apply, sum_apply, smul_apply, hochschildCoface_apply, smul_neg, Finset.smul_sum,
      ← Finset.sum_neg_distrib, F]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [smul_smul, smul_smul, ← neg_smul, pow_add]
    congr 1
    ring
  rw [add_apply, hself, hleft, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← add_smul]
  simp only [← Finset.sum_product']
  let S : Finset (Fin (n + 3) × Fin (n + 2)) := {is | (is.1 : ℕ) ≤ is.2}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S]
  have hcompl :
      (∑ x ∈ Sᶜ, ((-(x.2 : ℤ) * (-1 : ℤ) ^ ((x.1 : ℕ) + x.2) +
          w x.1 * (-1 : ℤ) ^ ((x.1 : ℕ) + x.2))) • F x.1 x.2) =
        ∑ x ∈ S, (((x.1 : ℤ) - w x.2.succ) * (-1 : ℤ) ^ ((x.1 : ℕ) + x.2)) • F x.1 x.2 := by
    refine (Finset.sum_bij (fun x hx ↦ (x.2.succ, x.1.castLT
        (lt_of_le_of_lt (Finset.mem_filter.1 hx).2 x.2.2))) ?_ ?_ ?_ ?_).symm
    · intro x hx
      simp only [S, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
        Fin.val_castLT] at hx ⊢
      omega
    · rintro ⟨i, s⟩ _ ⟨i', s'⟩ _ h
      simp only [Prod.mk.injEq, Fin.succ_inj] at h
      ext
      · simpa using congrArg Fin.val h.2
      · exact congrArg Fin.val h.1
    · rintro ⟨i', s'⟩ h
      simp only [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at h
      refine ⟨(s'.castSucc, i'.pred fun hi ↦ by simp [hi] at h), ?_, ?_⟩
      · simp only [S, Finset.mem_filter_univ, Fin.val_castSucc, Fin.val_pred]
        omega
      · simp
    · rintro ⟨i, s⟩ hx
      have his : (i : ℕ) ≤ s := (Finset.mem_filter.1 hx).2
      dsimp only
      have hi' : (i.castLT (lt_of_le_of_lt his s.2)).castSucc = i := by ext; rfl
      rw [hF _ _ (by simpa [Fin.le_def] using his), hi', Fin.val_succ, Fin.val_castLT]
      congr 1
      have hpow : (-1 : ℤ) ^ ((s : ℕ) + 1 + i) = -((-1 : ℤ) ^ ((i : ℕ) + s)) := by
        rw [show (s : ℕ) + 1 + i = ((i : ℕ) + s) + 1 by omega, pow_succ]
        ring
      rw [hpow]
      ring
  rw [hcompl, ← Finset.sum_add_distrib]
  -- Evaluate the combined weight on `S`, splitting off `s = Fin.last (n + 1)` where it vanishes.
  rw [cochainPeriodicity_apply]
  trans ∑ s : Fin (n + 2), ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 3) ↦ (i : ℕ) ≤ s),
      (((n + 1 : ℤ) - s - w s.succ) * (-1 : ℤ) ^ ((i : ℕ) + s)) • F i s
  · rw [show S = (Finset.univ ×ˢ Finset.univ).filter (fun x : Fin (n + 3) × Fin (n + 2) ↦
      (x.1 : ℕ) ≤ x.2) from rfl, Finset.sum_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with his
    · have hi : (i : ℕ) ≤ n + 1 := le_trans his (Nat.le_of_lt_succ s.2)
      rw [← add_smul]
      congr 1
      simp only [w, hi, ↓reduceIte]
      ring
    · rfl
  · rw [Fin.sum_univ_castSucc]
    have hlast : (((n + 1 : ℤ) - (Fin.last (n + 1) : ℕ) - w (Fin.last (n + 1)).succ)) = 0 := by
      simp [w]
    simp only [hlast, zero_mul, zero_smul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hwj : ((n + 1 : ℤ) - (j.castSucc : ℕ) - w j.castSucc.succ) = 1 := by
      have hj : (j : ℕ) + 1 ≤ n + 1 := Nat.succ_le_of_lt j.2
      simp only [w, Fin.val_succ, Fin.val_castSucc, hj, ↓reduceIte]
      omega
    rw [hwj]
    refine Finset.sum_bij (fun i hi ↦ ⟨i, lt_of_le_of_lt (Finset.mem_filter.1 hi).2 j.2⟩)
      ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_Iic.2 (Fin.le_def.2 (Finset.mem_filter.1 hi).2)
    · intro i₁ _ i₂ _ h
      exact Fin.ext (congrArg (Fin.val (n := n + 1)) h)
    · intro r hr
      exact ⟨r.castSucc.castSucc, Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.le_def.1
        (Finset.mem_Iic.1 hr)⟩, Fin.ext rfl⟩
    · intro i hi
      have hij : (i : ℕ) ≤ j := (Finset.mem_filter.1 hi).2
      dsimp only
      have hjs : j.castSucc.succ = j.succ.castSucc := Fin.ext (by simp)
      have hface := hF ⟨i, lt_of_le_of_lt hij (Nat.lt_succ_of_lt j.2)⟩ j.castSucc hij
      have hi_eq' : (⟨(i : ℕ), lt_of_le_of_lt hij (Nat.lt_succ_of_lt j.2)⟩ : Fin (n + 2)).castSucc =
          i := Fin.ext rfl
      rw [hi_eq'] at hface
      rw [one_mul, ← hface, hjs]
      congr 1
      rw [Fin.val_castSucc, show (i : ℕ) + j = 2 * i + ((j : ℕ) - i) by omega, pow_add, pow_mul,
        neg_one_sq, one_pow, one_mul]

end Semigroup

/-! ### Row homotopy and cyclic cocycles -/

section RowHomotopy

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R]

section Additive

variable [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M]

/-- The unscaled cyclic row homotopy `H' = ∑_{j ≤ n} ∑_{k < j} λᵏ` on `n`-cochains. When `n + 1` is
invertible in `R`, `TauCeti.cyclicRowHomotopy` is `⅟(n + 1 : R) • cyclicRowHomotopySum`. -/
def cyclicRowHomotopySum (n : ℕ) :
    Module.End R (MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :=
  ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range j, cyclicOperator R A M n ^ k

variable {R A M} {n : ℕ}

/-- `(1 - λ) H' = (n + 1) - N` on `n`-cochains, without any invertibility hypothesis on `R`. -/
theorem one_sub_cyclicOperator_mul_cyclicRowHomotopySum :
    (1 - cyclicOperator R A M n) * cyclicRowHomotopySum R A M n =
      (n + 1 : R) • 1 - cyclicNorm R A M n := by
  rw [cyclicRowHomotopySum, Finset.mul_sum]
  simp only [mul_neg_geom_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, ← cyclicNorm_def]
  simp [← Nat.cast_smul_eq_nsmul R]

/-- `H' (1 - λ) = (n + 1) - N` on `n`-cochains, without any invertibility hypothesis on `R`. -/
theorem cyclicRowHomotopySum_mul_one_sub_cyclicOperator :
    cyclicRowHomotopySum R A M n * (1 - cyclicOperator R A M n) =
      (n + 1 : R) • 1 - cyclicNorm R A M n := by
  rw [cyclicRowHomotopySum, Finset.sum_mul]
  simp only [geom_sum_mul_neg, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, ← cyclicNorm_def]
  simp [← Nat.cast_smul_eq_nsmul R]

/-- Pointwise form of `one_sub_cyclicOperator_mul_cyclicRowHomotopySum`. -/
theorem one_sub_cyclicOperator_apply_cyclicRowHomotopySum
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    (1 - cyclicOperator R A M n) (cyclicRowHomotopySum R A M n φ) =
      (n + 1 : R) • φ - cyclicNorm R A M n φ := by
  simpa only [mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self] using
    LinearMap.congr_fun one_sub_cyclicOperator_mul_cyclicRowHomotopySum φ

/-- Pointwise form of `cyclicRowHomotopySum_mul_one_sub_cyclicOperator`. -/
theorem cyclicRowHomotopySum_apply_one_sub_cyclicOperator
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) :
    cyclicRowHomotopySum R A M n ((1 - cyclicOperator R A M n) φ) =
      (n + 1 : R) • φ - cyclicNorm R A M n φ := by
  simpa only [mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self] using
    LinearMap.congr_fun cyclicRowHomotopySum_mul_one_sub_cyclicOperator φ

end Additive

section Algebra

variable {R A M} [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [AddCommGroup M] [Module R M] {n : ℕ}

/-- Iterating `λ` on the bar coboundary of a cyclic cochain `φ` shifts the missing coface down:
`λᵏ (b' φ) = b φ - (-1)^(n + 1 - k) δ_{n + 1 - k} φ` for `k ≤ n + 1`. -/
private theorem cyclicOperator_pow_barCoboundary_of_mem_cyclicCochains
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n)
    {k : ℕ} (hk : k ≤ n + 1) :
    (cyclicOperator R A M (n + 1) ^ k) (barCoboundary R A M n φ) =
      hochschildCoboundary R A M n φ -
        (-1 : ℤ) ^ (n + 1 - k) • hochschildCoface R A M ⟨n + 1 - k, by omega⟩ φ := by
  induction k with
  | zero =>
    simp only [pow_zero, one_apply_eq_self, Nat.sub_zero]
    have hlast : (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) := rfl
    rw [hlast, hochschildCoboundary_eq_barCoboundary_add, add_sub_cancel_right]
  | succ k ih =>
    have hcyc_b : cyclicOperator R A M (n + 1) (hochschildCoboundary R A M n φ) =
        hochschildCoboundary R A M n φ :=
      mem_cyclicCochains_iff_cyclicOperator_apply_eq_self.1
        (hochschildCoboundary_mem_cyclicCochains R A M hφ)
    have hcyc_φ : cyclicOperator R A M n φ = φ :=
      mem_cyclicCochains_iff_cyclicOperator_apply_eq_self.1 hφ
    have hsucc : (⟨n + 1 - k, by omega⟩ : Fin (n + 2)) = (⟨n - k, by omega⟩ : Fin (n + 1)).succ :=
      Fin.ext (by simp; omega)
    have hcast : (⟨n - k, by omega⟩ : Fin (n + 1)).castSucc = ⟨n + 1 - (k + 1), by omega⟩ :=
      Fin.ext (by simp)
    rw [pow_succ', mul_apply_eq_comp, ih (Nat.le_of_succ_le hk), map_sub, hcyc_b, map_zsmul,
      hsucc, cyclicOperator_hochschildCoface_succ, hcyc_φ, hcast, smul_neg, sub_neg_eq_add]
    have hpow : (-1 : ℤ) ^ (n + 1 - k) = -((-1 : ℤ) ^ (n + 1 - (k + 1))) := by
      rw [show n + 1 - k = (n + 1 - (k + 1)) + 1 by omega, pow_succ]
      ring
    rw [hpow, neg_smul, ← sub_eq_add_neg]

/-- On a cyclic `n`-cochain `φ`, `H' (b' φ) = ((n + 1)(n + 2) / 2) • b φ + cupOneSelf φ`. -/
private theorem cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCochains
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n) :
    cyclicRowHomotopySum R A M (n + 1) (barCoboundary R A M n φ) =
      ((n + 1) * (n + 2) / 2 : ℕ) • hochschildCoboundary R A M n φ + cupOneSelf n φ := by
  rw [cyclicRowHomotopySum, LinearMap.sum_apply]
  set T : ℕ → MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M := fun k ↦
    if hk : k < n + 2 then (-1 : ℤ) ^ (n + 1 - k) • hochschildCoface R A M ⟨n + 1 - k, by omega⟩ φ
    else 0
  have hj (j : ℕ) (hj : j ∈ Finset.range (n + 2)) :
      (∑ k ∈ Finset.range j, cyclicOperator R A M (n + 1) ^ k) (barCoboundary R A M n φ) =
        j • hochschildCoboundary R A M n φ - ∑ k ∈ Finset.range j, T k := by
    rw [LinearMap.sum_apply]
    have hk_eq (k : ℕ) (hk : k ∈ Finset.range j) :
        (cyclicOperator R A M (n + 1) ^ k) (barCoboundary R A M n φ) =
          hochschildCoboundary R A M n φ - T k := by
      have hkn : k < n + 2 := lt_trans (Finset.mem_range.1 hk) (Finset.mem_range.1 hj)
      simp only [T, hkn, ↓reduceDIte]
      exact cyclicOperator_pow_barCoboundary_of_mem_cyclicCochains hφ (Nat.le_of_lt_succ hkn)
    rw [Finset.sum_congr rfl hk_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  rw [Finset.sum_congr rfl hj, Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_range_id,
    show n + 2 - 1 = n + 1 by omega, mul_comm (n + 2) (n + 1), sub_eq_add_neg]
  congr 1
  -- Exchange the triangular double sum `k < j ≤ n + 1` and reverse `s = n + 1 - k`.
  have hswap : (∑ j ∈ Finset.range (n + 2), ∑ k ∈ Finset.range j, T k) =
      ∑ k ∈ Finset.range (n + 2), (n + 1 - k) • T k := by
    have haux (m : ℕ) : (∑ j ∈ Finset.range (m + 1), ∑ k ∈ Finset.range j, T k) =
        ∑ k ∈ Finset.range (m + 1), (m - k) • T k := by
      induction m with
      | zero => simp
      | succ r ih =>
        rw [Finset.sum_range_succ (fun j ↦ ∑ k ∈ Finset.range j, T k) (r + 1), ih,
          ← Finset.sum_add_distrib, Finset.sum_range_succ _ (r + 1), tsub_self, zero_smul, add_zero]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hkr : k ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [show r + 1 - k = (r - k) + 1 by omega, succ_nsmul]
    exact haux (n + 1)
  rw [hswap]
  simp only [cupOneSelf, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  congr 1
  rw [← Finset.sum_range_reflect (fun k ↦ (n + 1 - k) • T k) (n + 2), ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hs : n + 2 - 1 - (s : ℕ) < n + 2 := by omega
  simp only [T, hs, ↓reduceDIte, show n + 1 - (n + 2 - 1 - (s : ℕ)) = s by omega, Fin.eta,
    natCast_zsmul]

/-- On any cyclic `n`-cochain `φ`, `b (H' (b' φ)) + cupOneLeft (b φ) = S₀ φ`. -/
private theorem hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_add
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n) :
    hochschildCoboundary R A M (n + 1)
        (cyclicRowHomotopySum R A M (n + 1) (barCoboundary R A M n φ)) +
      cupOneLeft n (hochschildCoboundary R A M n φ) =
      cochainPeriodicity R A M n φ := by
  rw [cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCochains hφ, map_add, map_nsmul,
    hochschildCoboundary_hochschildCoboundary, smul_zero, zero_add,
    hochschildCoboundary_cupOneSelf_add]

/-- **Bicomplex homotopy formula for `S₀`.** For a cyclic cocycle `φ`, `b (H' (b' φ)) = S₀ φ` over
every commutative ring `R`. -/
theorem hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCocycles
    {φ : cyclicCochains R A M n} (hφ : φ ∈ cyclicCocycles R A M n) :
    hochschildCoboundary R A M (n + 1)
        (cyclicRowHomotopySum R A M (n + 1) (barCoboundary R A M n φ)) =
      cochainPeriodicity R A M n φ := by
  have hb : hochschildCoboundary R A M n φ = 0 := (mem_cyclicCocycles_iff R A M).1 hφ
  simpa [hb] using hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_add φ.2

/-- For every cyclic cocycle `φ`, `S₀ φ` is a cyclic cochain. -/
theorem cochainPeriodicity_mem_cyclicCochains_of_mem_cyclicCocycles
    {φ : cyclicCochains R A M n} (hφ : φ ∈ cyclicCocycles R A M n) :
    cochainPeriodicity R A M n φ ∈ cyclicCochains R A M (n + 2) := by
  rw [← ker_one_sub_cyclicOperator, LinearMap.mem_ker,
    ← hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCocycles hφ,
    ← LinearMap.comp_apply, one_sub_cyclicOperator_comp_hochschildCoboundary,
    LinearMap.comp_apply, one_sub_cyclicOperator_apply_cyclicRowHomotopySum, map_sub, map_smul,
    barCoboundary_barCoboundary, smul_zero, zero_sub,
    ← LinearMap.comp_apply (cyclicNorm R A M (n + 1)),
    ← hochschildCoboundary_comp_cyclicNorm, LinearMap.comp_apply,
    cyclicNorm_apply_of_mem_cyclicCochains φ.2, map_smul,
    (mem_cyclicCocycles_iff R A M).1 hφ, smul_zero, map_zero, neg_zero]

/-- For every cyclic cocycle `φ`, `S₀ φ` is a Hochschild cocycle. -/
theorem hochschildCoboundary_cochainPeriodicity_of_mem_cyclicCocycles
    {φ : cyclicCochains R A M n} (hφ : φ ∈ cyclicCocycles R A M n) :
    hochschildCoboundary R A M (n + 2) (cochainPeriodicity R A M n φ) = 0 := by
  rw [← hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCocycles hφ,
    hochschildCoboundary_hochschildCoboundary]

variable (R A M) in
/-- Connes' periodicity operator on cyclic cocycles, sending a cyclic `n`-cocycle `φ` to the cyclic
`(n + 2)`-cocycle `S₀ φ`. -/
def cyclicCocyclesPeriodicity (n : ℕ) :
    cyclicCocycles R A M n →ₗ[R] cyclicCocycles R A M (n + 2) where
  toFun φ := ⟨⟨cochainPeriodicity R A M n φ.1.1,
      cochainPeriodicity_mem_cyclicCochains_of_mem_cyclicCocycles φ.2⟩,
    (mem_cyclicCocycles_iff R A M).2
      (hochschildCoboundary_cochainPeriodicity_of_mem_cyclicCocycles φ.2)⟩
  map_add' φ ψ := by ext a; simp [map_add]
  map_smul' c φ := by ext a; simp [map_smul]

/-- The underlying cochain of `cyclicCocyclesPeriodicity φ` is `cochainPeriodicity φ`. -/
@[simp]
theorem coe_cyclicCocyclesPeriodicity_apply (φ : cyclicCocycles R A M n) :
    ((cyclicCocyclesPeriodicity R A M n φ : cyclicCochains R A M (n + 2)) :
      MultilinearMap R (fun _ : Fin (n + 3) ↦ A) M) =
      cochainPeriodicity R A M n φ.1.1 :=
  (rfl)

/-! ### Connes' Proposition 12 and coboundary preservation -/

/-- For a cyclic `m`-cochain `φ`, the cyclic norm of every signed coface `(-1)ⁱ δᵢ φ` equals the
Hochschild coboundary `b φ`. -/
private theorem cyclicNorm_hochschildCoface_of_mem_cyclicCochains {m : ℕ}
    {φ : MultilinearMap R (fun _ : Fin (m + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M m)
    (i : Fin (m + 2)) :
    (-1 : ℤ) ^ (i : ℕ) • cyclicNorm R A M (m + 1) (hochschildCoface R A M i φ) =
      hochschildCoboundary R A M m φ := by
  have hcyc : cyclicOperator R A M m φ = φ :=
    mem_cyclicCochains_iff_cyclicOperator_apply_eq_self.1 hφ
  have hface (j : Fin (m + 2)) :
      (-1 : ℤ) ^ (j : ℕ) • hochschildCoface R A M j φ =
        (cyclicOperator R A M (m + 1) ^ (m + 1 - j + 1)) (hochschildCoface R A M 0 φ) := by
    rcases j with ⟨j, hj⟩
    have hpow : cyclicOperator R A M (m + 1) ^ (m + 1 - j + 1) *
        cyclicOperator R A M (m + 1) ^ j = 1 := by
      rw [← pow_add, show m + 1 - j + 1 + j = m + 1 + 1 by omega, cyclicOperator_pow_eq_one]
    have hcyc_pow : (cyclicOperator R A M m ^ j) φ = φ := by
      rw [pow_apply_eq_iterate, Function.iterate_fixed hcyc]
    conv_lhs =>
      rw [← one_apply_eq_self (F := Module.End R _) (hochschildCoface R A M ⟨j, hj⟩ φ), ← hpow]
    rw [mul_apply_eq_comp, cyclicOperator_pow_hochschildCoface, hcyc_pow, map_zsmul, smul_smul,
      ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  have hsum : ∑ j ∈ Finset.range (m + 2), cyclicOperator R A M (m + 1) ^ (m + 1 - j + 1) =
      cyclicNorm R A M (m + 1) := by
    rw [← Finset.sum_range_reflect, ← cyclicOperator_mul_cyclicNorm, cyclicNorm_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← pow_succ', show m + 1 - (m + 2 - 1 - j) = j by
      have := Finset.mem_range.1 hj; omega]
  have hb : hochschildCoboundary R A M m φ =
      cyclicNorm R A M (m + 1) (hochschildCoface R A M 0 φ) := by
    have heq : hochschildCoboundary R A M m φ =
        ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) • hochschildCoface R A M j φ := by
      ext a; simp
    rw [heq, Finset.sum_congr rfl fun j _ ↦ hface j,
      Fin.sum_univ_eq_sum_range (fun j ↦ (cyclicOperator R A M (m + 1) ^ (m + 1 - j + 1))
        (hochschildCoface R A M 0 φ)), ← LinearMap.sum_apply, hsum]
  rw [hb, ← map_zsmul, hface i, ← mul_apply_eq_comp, cyclicNorm_mul_cyclicOperator_pow]

/-- **Connes' Proposition 12 (unscaled form).** For every cyclic `n`-cochain `ψ`,
`b (N (S₀ ψ)) = (n + 1) • S₀ (b ψ)`. -/
theorem hochschildCoboundary_cyclicNorm_cochainPeriodicity (ψ : cyclicCochains R A M n) :
    hochschildCoboundary R A M (n + 2)
        (cyclicNorm R A M (n + 2) (cochainPeriodicity R A M n ψ)) =
      (n + 1 : R) • cochainPeriodicity R A M (n + 1) (hochschildCoboundary R A M n ψ) := by
  have hbψ_cyc : hochschildCoboundary R A M n ψ ∈ cyclicCochains R A M (n + 1) :=
    hochschildCoboundary_mem_cyclicCochains R A M ψ.2
  have hbψ_coc : (⟨hochschildCoboundary R A M n ψ, hbψ_cyc⟩ : cyclicCochains R A M (n + 1)) ∈
      cyclicCocycles R A M (n + 1) :=
    (mem_cyclicCocycles_iff R A M).2 (hochschildCoboundary_hochschildCoboundary R A M ψ.1)
  -- `N` kills `cupOneLeft (b ψ)` because `N (δ_r (b ψ)) = ± b (b ψ) = 0`.
  have hN_cup : cyclicNorm R A M (n + 2) (cupOneLeft n (hochschildCoboundary R A M n ψ)) = 0 := by
    simp only [cupOneLeft, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
    refine Finset.sum_eq_zero fun r _ ↦ ?_
    have hr := cyclicNorm_hochschildCoface_of_mem_cyclicCochains hbψ_cyc r.castSucc.castSucc
    simp only [Fin.val_castSucc] at hr
    rw [hr, hochschildCoboundary_hochschildCoboundary, smul_zero]
  -- Decompose `N (S₀ ψ)` via `H' (1 - λ) = (n + 3) - N`.
  have h1op : (1 - cyclicOperator R A M (n + 2))
      (hochschildCoboundary R A M (n + 1)
        (cyclicRowHomotopySum R A M (n + 1) (barCoboundary R A M n ψ))) =
      -((n + 1 : R) • barCoboundary R A M (n + 1) (hochschildCoboundary R A M n ψ)) := by
    rw [← LinearMap.comp_apply, one_sub_cyclicOperator_comp_hochschildCoboundary,
      LinearMap.comp_apply, one_sub_cyclicOperator_apply_cyclicRowHomotopySum, map_sub, map_smul,
      barCoboundary_barCoboundary, smul_zero, zero_sub,
      ← LinearMap.comp_apply (cyclicNorm R A M (n + 1)), ← hochschildCoboundary_comp_cyclicNorm,
      LinearMap.comp_apply, cyclicNorm_apply_of_mem_cyclicCochains ψ.2, map_smul, map_smul]
  have hH := congrArg (cyclicRowHomotopySum R A M (n + 2)) h1op
  rw [cyclicRowHomotopySum_apply_one_sub_cyclicOperator, map_neg, map_smul] at hH
  have hNS₀ : cyclicNorm R A M (n + 2) (cochainPeriodicity R A M n ψ) =
      ((n + 2 : ℕ) + 1 : R) • hochschildCoboundary R A M (n + 1)
        (cyclicRowHomotopySum R A M (n + 1) (barCoboundary R A M n ψ)) +
      (n + 1 : R) • cyclicRowHomotopySum R A M (n + 2)
        (barCoboundary R A M (n + 1) (hochschildCoboundary R A M n ψ)) := by
    rw [← hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_add ψ.2, map_add, hN_cup,
      add_zero]
    exact (eq_sub_of_add_eq' (sub_eq_iff_eq_add.1 hH).symm).trans (sub_neg_eq_add _ _)
  rw [hNS₀, map_add, map_smul, hochschildCoboundary_hochschildCoboundary, smul_zero, zero_add,
    map_smul, hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCocycles hbψ_coc]

section ConnesS

variable (R A M n) in
/-- **Connes' periodicity operator `S = (n + 3)⁻¹ N S₀` on cyclic `n`-cochains**, defined whenever
`n + 3` is invertible in `R`. -/
def connesS [Invertible (n + 3 : R)] :
    cyclicCochains R A M n →ₗ[R] cyclicCochains R A M (n + 2) where
  toFun ψ := ⟨⅟(n + 3 : R) • cyclicNorm R A M (n + 2) (cochainPeriodicity R A M n ψ),
    (cyclicCochains R A M (n + 2)).smul_mem _ (cyclicNorm_mem_cyclicCochains _)⟩
  map_add' ψ₁ ψ₂ := by ext a; simp [map_add, smul_add]
  map_smul' c ψ := by ext a; simp [map_smul, smul_comm c]

/-- Underlying cochain of `connesS`. -/
@[simp]
theorem coe_connesS_apply [Invertible (n + 3 : R)] (ψ : cyclicCochains R A M n) :
    (connesS R A M n ψ : MultilinearMap R (fun _ : Fin (n + 3) ↦ A) M) =
      ⅟(n + 3 : R) • cyclicNorm R A M (n + 2) (cochainPeriodicity R A M n ψ) :=
  (rfl)

/-- On a cyclic cocycle `φ`, `connesS` agrees with the unaveraged operator `cochainPeriodicity`. -/
theorem connesS_eq_cyclicCocyclesPeriodicity [Invertible (n + 3 : R)]
    (φ : cyclicCocycles R A M n) :
    connesS R A M n φ.1 = (cyclicCocyclesPeriodicity R A M n φ).1 := by
  ext1
  rw [coe_connesS_apply, cyclicNorm_apply_of_mem_cyclicCochains
    (cochainPeriodicity_mem_cyclicCochains_of_mem_cyclicCocycles φ.2),
    show ((n + 2 : ℕ) + 1 : R) = (n + 3 : R) by push_cast; ring, invOf_smul_smul]
  rfl

/-- **Connes' Proposition 12**: `(n + 3) • b (S ψ) = (n + 1) • S (b ψ)` on cyclic `n`-cochains. -/
theorem smul_cyclicHochschildCoboundary_connesS [Invertible (n + 3 : R)]
    [Invertible (↑(n + 1) + 3 : R)] (ψ : cyclicCochains R A M n) :
    (n + 3 : R) • cyclicHochschildCoboundary R A M (n + 2) (connesS R A M n ψ) =
      (n + 1 : R) • connesS R A M (n + 1) (cyclicHochschildCoboundary R A M n ψ) := by
  have hbψ : cyclicHochschildCoboundary R A M n ψ ∈ cyclicCocycles R A M (n + 1) := by
    rw [mem_cyclicCocycles_iff, coe_cyclicHochschildCoboundary_apply]
    exact hochschildCoboundary_hochschildCoboundary R A M ψ.1
  ext1
  rw [Submodule.coe_smul_of_tower, coe_cyclicHochschildCoboundary_apply, coe_connesS_apply,
    map_smul, smul_invOf_smul, hochschildCoboundary_cyclicNorm_cochainPeriodicity,
    Submodule.coe_smul_of_tower,
    connesS_eq_cyclicCocyclesPeriodicity ⟨cyclicHochschildCoboundary R A M n ψ, hbψ⟩,
    coe_cyclicCocyclesPeriodicity_apply, Subtype.coe_mk, coe_cyclicHochschildCoboundary_apply]

end ConnesS

/-- When every `q + 1` with `q < n` is invertible in `R` (vacuously for `n = 0`, and using
`IsUnit (n : R)` for `n = m + 1`), `cyclicCocyclesPeriodicity` preserves cyclic coboundaries. -/
theorem cyclicCocyclesPeriodicity_mem_cyclicCoboundaries
    (hR : ∀ q < n, IsUnit ((q : R) + 1)) (φ : cyclicCocycles R A M n)
    (hφ : (φ : cyclicCochains R A M n) ∈ cyclicCoboundaries R A M n) :
    (cyclicCocyclesPeriodicity R A M n φ : cyclicCochains R A M (n + 2)) ∈
      cyclicCoboundaries R A M (n + 2) := by
  cases n with
  | zero =>
    rw [cyclicCoboundaries_zero, Submodule.mem_bot] at hφ
    have hφ0 : φ = 0 := Subtype.ext hφ
    rw [hφ0, map_zero, ZeroMemClass.coe_zero]
    exact zero_mem _
  | succ m =>
    obtain ⟨ψ, hψ⟩ := (mem_cyclicCoboundaries_succ_iff R A M).1 hφ
    obtain ⟨u, hu⟩ := hR m (Nat.lt_succ_self m)
    rw [mem_cyclicCoboundaries_succ_iff]
    refine ⟨(↑u⁻¹ : R) • ⟨cyclicNorm R A M (m + 2) (cochainPeriodicity R A M m ψ),
      cyclicNorm_mem_cyclicCochains _⟩, ?_⟩
    ext1
    rw [map_smul, Submodule.coe_smul_of_tower, coe_cyclicHochschildCoboundary_apply,
      Subtype.coe_mk, hochschildCoboundary_cyclicNorm_cochainPeriodicity, ← hu,
      smul_smul, Units.inv_mul, one_smul, coe_cyclicCocyclesPeriodicity_apply, ← hψ,
      coe_cyclicHochschildCoboundary_apply]

end Algebra

end RowHomotopy

end Simplicial

/-! ### Periodicity on cyclic cohomology -/

namespace cyclicCohomology

section Cohomology

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- **Connes' periodicity operator `S : HCⁿ(A; M) ⟶ HCⁿ⁺²(A; M)`** on cyclic cohomology over a
`ℚ`-algebra, sending the class of a cyclic cocycle `φ` to `[S₀ φ]`. -/
def periodicity (n : ℕ) :
    cyclicCohomology R A M n ⟶ cyclicCohomology R A M (n + 2) :=
  ModuleCat.ofHom (X := cyclicCohomology R A M n) (Y := cyclicCohomology R A M (n + 2)) <|
    desc n (mk R A M (n + 2) ∘ₗ cyclicCocyclesPeriodicity R A M n) fun φ hφ ↦
      (mk_eq_zero_iff R A M (n + 2) _).2 <|
        cyclicCocyclesPeriodicity_mem_cyclicCoboundaries
          (fun q _ ↦ by
            simpa using (Nat.cast_add_one_ne_zero (R := ℚ) q).isUnit.map (algebraMap ℚ R))
          φ hφ

variable {R A M} {n : ℕ}

/-- On the class of a cyclic cocycle `φ`, `periodicity` is the class of
`cyclicCocyclesPeriodicity φ`. -/
@[simp]
theorem periodicity_mk (φ : cyclicCocycles R A M n) :
    periodicity R A M n (mk R A M n φ) =
      mk R A M (n + 2) (cyclicCocyclesPeriodicity R A M n φ) :=
  desc_mk _ _ _ φ

/-- Connes' periodicity map on cyclic cohomology is natural with respect to homomorphisms of
nonunital algebras between unital algebras. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem map_comp_periodicity {B : Type u} [Ring B] [Algebra R B] (f : A →ₙₐ[R] B) (n : ℕ) :
    map M f n ≫ periodicity R A M n = periodicity R B M n ≫ map M f (n + 2) := by
  refine ModuleCat.hom_ext <| linearMap_ext <| LinearMap.ext fun φ ↦ ?_
  simp only [LinearMap.comp_apply, ModuleCat.hom_comp, map_mk, periodicity_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_cyclicCocyclesPeriodicity_apply, Subtype.coe_mk, coe_cyclicCochainsMap_apply,
    Subtype.coe_mk, coe_cyclicCochainsMap_apply, coe_cyclicCocyclesPeriodicity_apply]
  exact cochainPeriodicity_compLinearMap f φ.1.1

end Cohomology

end cyclicCohomology

end TauCeti
