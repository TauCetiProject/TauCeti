/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TraceSplitting
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The three cup placements on three strands

Insert the inverse-form cup into slots `01`, `02`, or `12` of a tensor cube, keeping the
remaining vector in its original order (`symplecticThreeStrandCup`). In every symplectic rank each
placement is injective, its image is the image of the corresponding arc `symplecticCupCapAt`, and
the three images together span the existing trace-tensor space.

In symplectic rank one the three placements satisfy `D₀₁ - D₀₂ + D₁₂ = 0`. This is their entire
relation: the map from three copies of the standard module to the tensor cube has kernel exactly
the vectors `(v, -v, v)`. Consequently the cup images together are free of rank four, rather
than six, and the first two placements parametrize them.

The harmonic tensors of the rank-one tensor cube have dimension four over every field: they are
the orthogonal complement of the trace tensors for the dot product of the monomial basis.
The cups use the bivector of `-Matrix.J`, consistently with `symplecticCup`.

## References

* R. Dipper, S. Doty, J. Hu, *Brauer algebras, symplectic Schur algebras and
  Schur–Weyl duality*, Trans. Amer. Math. Soc. 360 (2008), 189–213, §1.
* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, §10.1.
-/

public section

open scoped TensorProduct Matrix

namespace TauCeti

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- Insert the inverse symplectic cup into a tensor cube. The index `0`, `1`, or `2`
selects the pair `01`, `02`, or `12`, respectively; the free slot keeps the input vector. -/
noncomputable def symplecticThreeStrandCup (p : Fin 3) :
    ((Fin n ⊕ Fin n) → R) →ₗ[R] ⨂[R]^3 ((Fin n ⊕ Fin n) → R) :=
  ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, (-(Matrix.J (Fin n) R a b)) •
    match p with
    | 0 => (PiTensorProduct.tprod R).toLinearMap ![Pi.single a 1, Pi.single b 1, 0] 2
    | 1 => (PiTensorProduct.tprod R).toLinearMap ![Pi.single a 1, 0, Pi.single b 1] 1
    | 2 => (PiTensorProduct.tprod R).toLinearMap ![0, Pi.single a 1, Pi.single b 1] 0

/-- The cup in the first two slots, with the free vector last. -/
theorem symplecticThreeStrandCup_zero_apply (v : (Fin n ⊕ Fin n) → R) :
    symplecticThreeStrandCup R n 0 v =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, (-(Matrix.J (Fin n) R a b)) •
        PiTensorProduct.tprod R ![Pi.single a 1, Pi.single b 1, v] := by
  simp only [symplecticThreeStrandCup, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.toLinearMap_apply]
  congr 1
  funext a
  congr 1
  funext b
  congr 2
  ext i
  fin_cases i <;> simp

/-- The cup in the outside slots, with the free vector in the middle. -/
theorem symplecticThreeStrandCup_one_apply (v : (Fin n ⊕ Fin n) → R) :
    symplecticThreeStrandCup R n 1 v =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, (-(Matrix.J (Fin n) R a b)) •
        PiTensorProduct.tprod R ![Pi.single a 1, v, Pi.single b 1] := by
  simp only [symplecticThreeStrandCup, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.toLinearMap_apply]
  congr 1
  funext a
  congr 1
  funext b
  congr 2
  ext i
  fin_cases i <;> simp

/-- The cup in the last two slots, with the free vector first. -/
theorem symplecticThreeStrandCup_two_apply (v : (Fin n ⊕ Fin n) → R) :
    symplecticThreeStrandCup R n 2 v =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, (-(Matrix.J (Fin n) R a b)) •
        PiTensorProduct.tprod R ![v, Pi.single a 1, Pi.single b 1] := by
  simp only [symplecticThreeStrandCup, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.toLinearMap_apply]
  congr 1
  funext a
  congr 1
  funext b
  congr 2
  ext i
  fin_cases i <;> simp

/-- Sum the three cup placements. Its domain records the free vector at each placement. -/
noncomputable def symplecticThreeStrandCupSum :
    (Fin 3 → ((Fin n ⊕ Fin n) → R)) →ₗ[R] ⨂[R]^3 ((Fin n ⊕ Fin n) → R) :=
  LinearMap.lsum R (fun _ : Fin 3 => (Fin n ⊕ Fin n) → R) R (symplecticThreeStrandCup R n)

@[simp]
theorem symplecticThreeStrandCupSum_apply (v : Fin 3 → ((Fin n ⊕ Fin n) → R)) :
    symplecticThreeStrandCupSum R n v = symplecticThreeStrandCup R n 0 (v 0) +
      symplecticThreeStrandCup R n 1 (v 1) + symplecticThreeStrandCup R n 2 (v 2) := by
  simp [symplecticThreeStrandCupSum, Fin.sum_univ_three, add_assoc]

variable {R n}

/-- On a vector supported at one placement, the sum is that single cup placement. -/
theorem symplecticThreeStrandCupSum_single (p : Fin 3) (v : (Fin n ⊕ Fin n) → R) :
    symplecticThreeStrandCupSum R n (Pi.single p v) = symplecticThreeStrandCup R n p v :=
  LinearMap.lsum_piSingle R (fun _ : Fin 3 => (Fin n ⊕ Fin n) → R) R _ p v

/-- Coordinates of the three cup placements in the standard monomial tensor basis. -/
theorem piTensorProduct_repr_symplecticThreeStrandCup (p : Fin 3) (v : (Fin n ⊕ Fin n) → R)
    (w : Fin 3 → Fin n ⊕ Fin n) :
    (Basis.piTensorProduct (fun _ : Fin 3 => Pi.basisFun R (Fin n ⊕ Fin n))).repr
        (symplecticThreeStrandCup R n p v) w =
      match p with
      | 0 => -(Matrix.J (Fin n) R (w 0) (w 1)) * v (w 2)
      | 1 => -(Matrix.J (Fin n) R (w 0) (w 2)) * v (w 1)
      | 2 => -(Matrix.J (Fin n) R (w 1) (w 2)) * v (w 0) := by
  fin_cases p <;>
    simp [symplecticThreeStrandCup, -Fintype.sum_sum_type, Fin.prod_univ_three,
      Pi.single_apply, eq_comm, mul_ite, ite_mul, Function.update]

private theorem cupCapAt_tprod (p : Fin 3) (v : Fin 3 → ((Fin n ⊕ Fin n) → R)) :
    symplecticCupCapAt R n 3 (![0, 0, 1] p) (![1, 2, 2] p) (PiTensorProduct.tprod R v) =
      stdSymplecticBilinForm R n (v (![0, 0, 1] p)) (v (![1, 2, 2] p)) •
        symplecticThreeStrandCup R n p (v (![2, 1, 0] p)) := by
  have hij : (![0, 0, 1] p : Fin 3) ≠ ![1, 2, 2] p := by fin_cases p <;> decide
  calc
    _ = stdSymplecticBilinForm R n (v (![0, 0, 1] p)) (v (![1, 2, 2] p)) •
        -∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, Matrix.J (Fin n) R x y •
          PiTensorProduct.tprod R (Function.update
            (Function.update v (![0, 0, 1] p) (Pi.single x 1))
            (![1, 2, 2] p) (Pi.single y 1)) := symplecticCupCapAt_tprod hij v
    _ = _ := ?_
  have hup (a b : Fin n ⊕ Fin n) :
      Function.update (Function.update v (![0, 0, 1] p) (Pi.single a 1))
        (![1, 2, 2] p) (Pi.single b 1) =
      match p with
      | 0 => ![Pi.single a 1, Pi.single b 1, v 2]
      | 1 => ![Pi.single a 1, v 1, Pi.single b 1]
      | 2 => ![v 0, Pi.single a 1, Pi.single b 1] := by
    fin_cases p <;> ext i <;> fin_cases i <;> simp
  simp_rw [hup]
  fin_cases p
  · simp [symplecticThreeStrandCup_zero_apply, -Fintype.sum_sum_type, Finset.smul_sum,
      neg_smul (M := ⨂[R]^3 ((Fin n ⊕ Fin n) → R)), Finset.sum_neg_distrib]
  · simp [symplecticThreeStrandCup_one_apply, -Fintype.sum_sum_type, Finset.smul_sum,
      neg_smul (M := ⨂[R]^3 ((Fin n ⊕ Fin n) → R)), Finset.sum_neg_distrib]
  · simp [symplecticThreeStrandCup_two_apply, -Fintype.sum_sum_type, Finset.smul_sum,
      neg_smul (M := ⨂[R]^3 ((Fin n ⊕ Fin n) → R)), Finset.sum_neg_distrib]

/-- The arc on slots `0, 1` of a pure tensor cube is the cup placement
`symplecticThreeStrandCup R n 0` on the last vector, scaled by the pairing of the first two. -/
theorem symplecticCupCapAt_zero_one_tprod (v : Fin 3 → ((Fin n ⊕ Fin n) → R)) :
    symplecticCupCapAt R n 3 0 1 (PiTensorProduct.tprod R v) =
      stdSymplecticBilinForm R n (v 0) (v 1) • symplecticThreeStrandCup R n 0 (v 2) :=
  cupCapAt_tprod 0 v

/-- The arc on slots `0, 2` of a pure tensor cube is the cup placement
`symplecticThreeStrandCup R n 1` on the middle vector, scaled by the pairing of the outer two. -/
theorem symplecticCupCapAt_zero_two_tprod (v : Fin 3 → ((Fin n ⊕ Fin n) → R)) :
    symplecticCupCapAt R n 3 0 2 (PiTensorProduct.tprod R v) =
      stdSymplecticBilinForm R n (v 0) (v 2) • symplecticThreeStrandCup R n 1 (v 1) :=
  cupCapAt_tprod 1 v

/-- The arc on slots `1, 2` of a pure tensor cube is the cup placement
`symplecticThreeStrandCup R n 2` on the first vector, scaled by the pairing of the last two. -/
theorem symplecticCupCapAt_one_two_tprod (v : Fin 3 → ((Fin n ⊕ Fin n) → R)) :
    symplecticCupCapAt R n 3 1 2 (PiTensorProduct.tprod R v) =
      stdSymplecticBilinForm R n (v 1) (v 2) • symplecticThreeStrandCup R n 2 (v 0) :=
  cupCapAt_tprod 2 v

private theorem range_cupCapAt (p : Fin 3) :
    LinearMap.range (symplecticCupCapAt R n 3 (![0, 0, 1] p) (![1, 2, 2] p)) =
      LinearMap.range (symplecticThreeStrandCup R n p) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, cupCapAt_tprod]
      exact Submodule.smul_mem _ r (Submodule.smul_mem _ _ ⟨_, rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · rintro _ ⟨v, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Subsingleton.elim v 0, map_zero]
      exact zero_mem _
    let x₀ : Fin n ⊕ Fin n := Sum.inl ⟨0, hn⟩
    let y₀ : Fin n ⊕ Fin n := Sum.inr ⟨0, hn⟩
    let w : Fin 3 → ((Fin n ⊕ Fin n) → R) := match p with
      | 0 => ![Pi.single x₀ 1, Pi.single y₀ 1, v]
      | 1 => ![Pi.single x₀ 1, v, Pi.single y₀ 1]
      | 2 => ![v, Pi.single x₀ 1, Pi.single y₀ 1]
    refine ⟨-PiTensorProduct.tprod R w, ?_⟩
    rw [map_neg, cupCapAt_tprod]
    fin_cases p <;> simp [w, x₀, y₀, Matrix.J, neg_smul (M := ⨂[R]^3 ((Fin n ⊕ Fin n) → R))]

/-- The image of the arc on slots `0, 1` is the image of `symplecticThreeStrandCup R n 0`. -/
theorem range_symplecticCupCapAt_zero_one :
    LinearMap.range (symplecticCupCapAt R n 3 0 1) =
      LinearMap.range (symplecticThreeStrandCup R n 0) :=
  range_cupCapAt 0

/-- The image of the arc on slots `0, 2` is the image of `symplecticThreeStrandCup R n 1`. -/
theorem range_symplecticCupCapAt_zero_two :
    LinearMap.range (symplecticCupCapAt R n 3 0 2) =
      LinearMap.range (symplecticThreeStrandCup R n 1) :=
  range_cupCapAt 1

/-- The image of the arc on slots `1, 2` is the image of `symplecticThreeStrandCup R n 2`. -/
theorem range_symplecticCupCapAt_one_two :
    LinearMap.range (symplecticCupCapAt R n 3 1 2) =
      LinearMap.range (symplecticThreeStrandCup R n 2) :=
  range_cupCapAt 2

/-- The image of `symplecticThreeStrandCupSum R n`, that is, the sum of the three cup images, is
exactly the trace-tensor space in degree three. -/
theorem range_symplecticThreeStrandCupSum :
    LinearMap.range (symplecticThreeStrandCupSum R n) =
      (symplecticTraceTensors R n 3).toSubmodule := by
  have hcup (p : Fin 3) : LinearMap.range (symplecticThreeStrandCup R n p) ≤
      LinearMap.range (symplecticThreeStrandCupSum R n) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨Pi.single p v, symplecticThreeStrandCupSum_single p v⟩
  have htrace (p : Fin 3) : LinearMap.range (symplecticThreeStrandCup R n p) ≤
      (symplecticTraceTensors R n 3).toSubmodule := by
    rw [← range_cupCapAt p]
    apply range_symplecticCupCapAt_le_symplecticTraceTensors
    fin_cases p <;> decide
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [symplecticThreeStrandCupSum_apply]
    exact add_mem (add_mem (htrace 0 ⟨_, rfl⟩) (htrace 1 ⟨_, rfl⟩)) (htrace 2 ⟨_, rfl⟩)
  · rw [symplecticTraceTensors_toSubmodule_le_iff]
    intro i j hij
    have h (p : Fin 3) := (range_cupCapAt (R := R) (n := n) p).le.trans (hcup p)
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact h 0
    · exact h 1
    · exact (congrArg LinearMap.range
        (symplecticCupCapAt_comm (k := R) (n := n) (d := 3) 1 0)).le.trans (h 0)
    · exact False.elim (hij rfl)
    · exact h 2
    · exact (congrArg LinearMap.range
        (symplecticCupCapAt_comm (k := R) (n := n) (d := 3) 2 0)).le.trans (h 1)
    · exact (congrArg LinearMap.range
        (symplecticCupCapAt_comm (k := R) (n := n) (d := 3) 2 1)).le.trans (h 2)
    · exact False.elim (hij rfl)

/-- Each cup placement is injective, in every symplectic rank and over every commutative ring,
including rings of characteristic two. -/
theorem symplecticThreeStrandCup_injective (p : Fin 3) :
    Function.Injective (symplecticThreeStrandCup R n p) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => funext fun x => ?_
  let i : Fin n := Sum.elim id id x
  have coord (w : Fin 3 → Fin n ⊕ Fin n) := congrArg
    (fun t => (Basis.piTensorProduct (fun _ : Fin 3 =>
      Pi.basisFun R (Fin n ⊕ Fin n))).repr t w) hv
  simp only [piTensorProduct_repr_symplecticThreeStrandCup, map_zero, Finsupp.zero_apply]
    at coord
  fin_cases p
  · simpa [Matrix.J] using coord ![Sum.inr i, Sum.inl i, x]
  · simpa [Matrix.J] using coord ![Sum.inr i, x, Sum.inl i]
  · simpa [Matrix.J] using coord ![x, Sum.inr i, Sum.inl i]

/-- Each individual cup image is free of rank `2 * n`. -/
theorem finrank_range_symplecticThreeStrandCup [StrongRankCondition R] (p : Fin 3) :
    Module.finrank R (LinearMap.range (symplecticThreeStrandCup R n p)) = 2 * n := by
  rw [LinearMap.finrank_range_of_inj (symplecticThreeStrandCup_injective p)]
  simp [two_mul]

/-- In rank one, the alternating sum of the three cup placements vanishes. -/
theorem symplecticThreeStrandCup_rankOne_zero_sub_one_add_two_eq_zero :
    symplecticThreeStrandCup R 1 0 - symplecticThreeStrandCup R 1 1 +
      symplecticThreeStrandCup R 1 2 = 0 := by
  apply LinearMap.ext
  intro v
  apply (Basis.piTensorProduct (fun _ : Fin 3 => Pi.basisFun R (Fin 1 ⊕ Fin 1))).repr.injective
  ext w
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply, map_add, map_sub,
    Finsupp.add_apply, Finsupp.sub_apply, piTensorProduct_repr_symplecticThreeStrandCup, map_zero,
    Finsupp.zero_apply]
  rcases w 0 with a | a <;> rcases w 1 with b | b <;> rcases w 2 with c | c <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [Matrix.J]

/-- The full kernel of the sum of the rank-one cup placements. This holds over every
commutative ring, including characteristic two, where the signs coincide. -/
theorem symplecticThreeStrandCupSum_rankOne_eq_zero_iff (v : Fin 3 → ((Fin 1 ⊕ Fin 1) → R)) :
    symplecticThreeStrandCupSum R 1 v = 0 ↔ v 1 = -v 0 ∧ v 2 = v 0 := by
  constructor
  · intro h
    have coord (w : Fin 3 → Fin 1 ⊕ Fin 1) := congrArg
      (fun t => (Basis.piTensorProduct (fun _ : Fin 3 =>
        Pi.basisFun R (Fin 1 ⊕ Fin 1))).repr t w) h
    simp only [symplecticThreeStrandCupSum_apply, map_add, Finsupp.add_apply,
      piTensorProduct_repr_symplecticThreeStrandCup, map_zero, Finsupp.zero_apply] at coord
    have h₁ := coord ![Sum.inl 0, Sum.inl 0, Sum.inr 0]
    have h₂ := coord ![Sum.inl 0, Sum.inr 0, Sum.inl 0]
    have h₃ := coord ![Sum.inl 0, Sum.inr 0, Sum.inr 0]
    have h₄ := coord ![Sum.inr 0, Sum.inl 0, Sum.inr 0]
    simp [Matrix.J] at h₁ h₂ h₃ h₄
    constructor
    · funext a
      rcases a with a | a <;> simp only [Fin.eq_zero a, Pi.neg_apply]
      · linear_combination h₁ + h₂
      · linear_combination h₃
    · funext a
      rcases a with a | a <;> simp only [Fin.eq_zero a]
      · linear_combination -h₂
      · linear_combination h₄
  · rintro ⟨h₁, h₂⟩
    have h := LinearMap.congr_fun
      (symplecticThreeStrandCup_rankOne_zero_sub_one_add_two_eq_zero (R := R)) (v 0)
    rw [symplecticThreeStrandCupSum_apply, h₁, h₂, map_neg]
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      sub_eq_add_neg] using h

variable (R) in
/-- The `R`-linear map
`(x, y) ↦ symplecticThreeStrandCup R 1 0 x + symplecticThreeStrandCup R 1 1 y`, as an equivalence
from two copies of the rank-one coordinate module onto the image of
`symplecticThreeStrandCupSum R 1`. -/
noncomputable def symplecticThreeStrandCupRangeEquivRankOne :
    (((Fin 1 ⊕ Fin 1) → R) × ((Fin 1 ⊕ Fin 1) → R)) ≃ₗ[R]
      LinearMap.range (symplecticThreeStrandCupSum R 1) := by
  refine LinearEquiv.ofBijective
    (((symplecticThreeStrandCup R 1 0).coprod (symplecticThreeStrandCup R 1 1)).codRestrict
      (LinearMap.range (symplecticThreeStrandCupSum R 1)) fun v => ⟨![v.1, v.2, 0], by simp⟩)
    ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have hzero : symplecticThreeStrandCupSum R 1 ![v.1, v.2, 0] = 0 := by
      have h : symplecticThreeStrandCup R 1 0 v.1 + symplecticThreeStrandCup R 1 1 v.2 = 0 :=
        congrArg Subtype.val hv
      simpa using h
    have h := (symplecticThreeStrandCupSum_rankOne_eq_zero_iff _).mp hzero
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
    exact Prod.ext h.2.symm (by simpa [← h.2] using h.1)
  · rintro ⟨t, v, rfl⟩
    have h := LinearMap.congr_fun
      (symplecticThreeStrandCup_rankOne_zero_sub_one_add_two_eq_zero (R := R)) (v 2)
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply] at h
    have hv : symplecticThreeStrandCup R 1 0 (v 0 - v 2) +
        symplecticThreeStrandCup R 1 1 (v 1 + v 2) = symplecticThreeStrandCupSum R 1 v := by
      simp only [map_sub, map_add, symplecticThreeStrandCupSum_apply]
      linear_combination -h
    exact ⟨(v 0 - v 2, v 1 + v 2), Subtype.ext hv⟩

@[simp]
theorem symplecticThreeStrandCupRangeEquivRankOne_apply
    (v : ((Fin 1 ⊕ Fin 1) → R) × ((Fin 1 ⊕ Fin 1) → R)) :
    (symplecticThreeStrandCupRangeEquivRankOne R v : ⨂[R]^3 ((Fin 1 ⊕ Fin 1) → R)) =
      symplecticThreeStrandCup R 1 0 v.1 + symplecticThreeStrandCup R 1 1 v.2 := (rfl)

/-- The inverse of `symplecticThreeStrandCupRangeEquivRankOne R` sends the image of `v` under
`symplecticThreeStrandCupSum R 1` to `(v 0 - v 2, v 1 + v 2)`. -/
theorem symplecticThreeStrandCupRangeEquivRankOne_symm_mk
    (v : Fin 3 → ((Fin 1 ⊕ Fin 1) → R))
    (hv : symplecticThreeStrandCupSum R 1 v ∈ LinearMap.range (symplecticThreeStrandCupSum R 1)) :
    (symplecticThreeStrandCupRangeEquivRankOne R).symm ⟨symplecticThreeStrandCupSum R 1 v, hv⟩ =
      (v 0 - v 2, v 1 + v 2) := by
  rw [LinearEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  simp only [symplecticThreeStrandCupRangeEquivRankOne_apply, map_sub, map_add,
    symplecticThreeStrandCupSum_apply]
  have h := LinearMap.congr_fun
    (symplecticThreeStrandCup_rankOne_zero_sub_one_add_two_eq_zero (R := R)) (v 2)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply] at h
  linear_combination h

/-- `symplecticThreeStrandCupRangeEquivRankOne_symm_mk` stated with `LinearMap.rangeRestrict`. -/
@[simp]
theorem symplecticThreeStrandCupRangeEquivRankOne_symm_rangeRestrict
    (v : Fin 3 → ((Fin 1 ⊕ Fin 1) → R)) :
    (symplecticThreeStrandCupRangeEquivRankOne R).symm
        ((symplecticThreeStrandCupSum R 1).rangeRestrict v) = (v 0 - v 2, v 1 + v 2) :=
  symplecticThreeStrandCupRangeEquivRankOne_symm_mk v _

/-- The sum of the three rank-one cup images is free of rank four. -/
theorem finrank_range_symplecticThreeStrandCupSum_rankOne [StrongRankCondition R] :
    Module.finrank R (LinearMap.range (symplecticThreeStrandCupSum R 1)) = 4 := by
  rw [← (symplecticThreeStrandCupRangeEquivRankOne R).finrank_eq]
  simp

/-- In symplectic rank one, the trace tensors in degree three are free of rank four. -/
theorem finrank_symplecticTraceTensors_one_three [StrongRankCondition R] :
    Module.finrank R (symplecticTraceTensors R 1 3).toSubmodule = 4 := by
  rw [← range_symplecticThreeStrandCupSum, finrank_range_symplecticThreeStrandCupSum_rankOne]

/-- The harmonic tensors in the rank-one tensor cube have dimension four over every field,
including fields of characteristic two. They are the orthogonal complement of the trace tensors
for the dot product of the monomial basis, for which every arc is self-adjoint. -/
theorem finrank_symplecticHarmonicTensors_one_three {K : Type*} [Field K] :
    Module.finrank K (symplecticHarmonicTensors K 1 3) = 4 := by
  let b := Basis.piTensorProduct (fun _ : Fin 3 => Pi.basisFun K (Fin 1 ⊕ Fin 1))
  let I : Matrix (Fin 3 → Fin 1 ⊕ Fin 1) (Fin 3 → Fin 1 ⊕ Fin 1) K := 1
  let B := Matrix.toBilin b I
  have hB : B.Nondegenerate :=
    (Matrix.nondegenerate_of_det_ne_zero (M := I) (by simp [I])).toBilin b
  have hBapply (x y) : B x y = ⇑(b.repr x) ⬝ᵥ ⇑(b.repr y) := by
    simp [B, I, Matrix.toBilin_apply, dotProduct, Matrix.one_apply]
  have hadj (i j : Fin 3) (x y) :
      B (symplecticCupCapAt K 1 3 i j x) y = B (symplecticCupCapAt K 1 3 i j y) x := by
    let : StarRing K := starRingOfComm
    have hT : (LinearMap.toMatrix b b (symplecticCupCapAt K 1 3 i j))ᵀ =
        LinearMap.toMatrix b b (symplecticCupCapAt K 1 3 i j) :=
      isHermitian_toMatrix_symplecticCupCapAt
    rw [hBapply, hBapply, ← LinearMap.toMatrix_mulVec_repr b b _ x,
      ← LinearMap.toMatrix_mulVec_repr b b _ y, dotProduct_comm, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hT]
  have horth : B.orthogonal (symplecticTraceTensors K 1 3).toSubmodule =
      symplecticHarmonicTensors K 1 3 := by
    rw [symplecticHarmonicTensors_eq_iInf_ker_symplecticCupCapAt]
    ext x
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro h i j hij
      refine hB.1 _ fun y => ?_
      rw [hadj]
      exact h _ (range_symplecticCupCapAt_le_symplecticTraceTensors hij ⟨y, rfl⟩)
    · intro h t ht
      refine (symplecticTraceTensors_toSubmodule_le_iff (p := LinearMap.ker (B.flip x))).2
        (fun i j hij => ?_) ht
      rintro _ ⟨y, rfl⟩
      simp [hadj, h i j hij]
  have ht : Module.finrank K (⨂[K]^3 ((Fin 1 ⊕ Fin 1) → K)) = 8 := by
    rw [Module.finrank_eq_card_basis b]
    simp
  rw [← horth, LinearMap.BilinForm.finrank_orthogonal hB, finrank_symplecticTraceTensors_one_three,
    ht]

end TauCeti
