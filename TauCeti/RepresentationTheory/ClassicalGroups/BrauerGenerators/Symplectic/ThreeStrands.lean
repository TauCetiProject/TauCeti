/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TraceSplitting

/-!
# The three cup placements in symplectic rank one

Insert the inverse-form cup into slots `01`, `02`, or `12` of a tensor cube, keeping the
remaining vector in its original order. In symplectic rank one these three maps satisfy
`D₀₁ - D₀₂ + D₁₂ = 0`. This is their entire relation: the map from three copies of the
standard module to the tensor cube has kernel exactly the vectors `(v, -v, v)`.
Consequently the cup images together have dimension four, rather than six, over a field.
This is the first dependent cup expansion in symplectic tensor duality.

The cup image is identified with the existing trace-tensor space. Over a star-ordered field,
the trace splitting then gives a four-dimensional harmonic complement in the tensor cube.
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
noncomputable def symplecticTripleCup (p : Fin 3) :
    ((Fin n ⊕ Fin n) → R) →ₗ[R] ⨂[R]^3 ((Fin n ⊕ Fin n) → R) :=
  ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, (-(Matrix.J (Fin n) R a b)) •
    match p with
    | 0 => (PiTensorProduct.tprod R).toLinearMap ![Pi.single a 1, Pi.single b 1, 0] 2
    | 1 => (PiTensorProduct.tprod R).toLinearMap ![Pi.single a 1, 0, Pi.single b 1] 1
    | 2 => (PiTensorProduct.tprod R).toLinearMap ![0, Pi.single a 1, Pi.single b 1] 0

/-- The cup in the first two slots, with the free vector last. -/
theorem symplecticTripleCup_zero_apply (v : (Fin n ⊕ Fin n) → R) :
    symplecticTripleCup R n 0 v =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, (-(Matrix.J (Fin n) R a b)) •
        PiTensorProduct.tprod R ![Pi.single a 1, Pi.single b 1, v] := by
  simp only [symplecticTripleCup, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.toLinearMap_apply]
  congr 1
  funext a
  congr 1
  funext b
  congr 2
  ext i
  fin_cases i <;> simp

/-- The cup in the outside slots, with the free vector in the middle. -/
theorem symplecticTripleCup_one_apply (v : (Fin n ⊕ Fin n) → R) :
    symplecticTripleCup R n 1 v =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, (-(Matrix.J (Fin n) R a b)) •
        PiTensorProduct.tprod R ![Pi.single a 1, v, Pi.single b 1] := by
  simp only [symplecticTripleCup, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.toLinearMap_apply]
  congr 1
  funext a
  congr 1
  funext b
  congr 2
  ext i
  fin_cases i <;> simp

/-- The cup in the last two slots, with the free vector first. -/
theorem symplecticTripleCup_two_apply (v : (Fin n ⊕ Fin n) → R) :
    symplecticTripleCup R n 2 v =
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, (-(Matrix.J (Fin n) R a b)) •
        PiTensorProduct.tprod R ![v, Pi.single a 1, Pi.single b 1] := by
  simp only [symplecticTripleCup, LinearMap.sum_apply, LinearMap.smul_apply,
    MultilinearMap.toLinearMap_apply]
  congr 1
  funext a
  congr 1
  funext b
  congr 2
  ext i
  fin_cases i <;> simp

/-- Sum the three cup placements. Its domain records the free vector at each placement. -/
noncomputable def symplecticTripleCupSum :
    (Fin 3 → ((Fin n ⊕ Fin n) → R)) →ₗ[R] ⨂[R]^3 ((Fin n ⊕ Fin n) → R) :=
  ∑ p : Fin 3, (symplecticTripleCup R n p).comp (LinearMap.proj p)

@[simp]
theorem symplecticTripleCupSum_apply (v : Fin 3 → ((Fin n ⊕ Fin n) → R)) :
    symplecticTripleCupSum R n v = symplecticTripleCup R n 0 (v 0) +
      symplecticTripleCup R n 1 (v 1) + symplecticTripleCup R n 2 (v 2) := by
  simp [symplecticTripleCupSum, Fin.sum_univ_three, add_assoc]

variable {R n}

/-- Coordinates of the three cup placements in the standard monomial tensor basis. -/
theorem repr_symplecticTripleCup (p : Fin 3) (v : (Fin n ⊕ Fin n) → R)
    (w : Fin 3 → Fin n ⊕ Fin n) :
    (Basis.piTensorProduct (fun _ : Fin 3 => Pi.basisFun R (Fin n ⊕ Fin n))).repr
        (symplecticTripleCup R n p v) w =
      match p with
      | 0 => -(Matrix.J (Fin n) R (w 0) (w 1)) * v (w 2)
      | 1 => -(Matrix.J (Fin n) R (w 0) (w 2)) * v (w 1)
      | 2 => -(Matrix.J (Fin n) R (w 1) (w 2)) * v (w 0) := by
  fin_cases p <;>
    simp [symplecticTripleCup, -Fintype.sum_sum_type, Fin.prod_univ_three,
      Pi.single_apply, eq_comm, mul_ite, ite_mul, Function.update]

private theorem cupCapAt_tprod (p : Fin 3) (v : Fin 3 → ((Fin n ⊕ Fin n) → R)) :
    symplecticCupCapAt R n 3 (![0, 0, 1] p) (![1, 2, 2] p) (PiTensorProduct.tprod R v) =
      stdSymplecticBilinForm R n (v (![0, 0, 1] p)) (v (![1, 2, 2] p)) •
        symplecticTripleCup R n p (v (![2, 1, 0] p)) := by
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
  · simp [symplecticTripleCup_zero_apply, -Fintype.sum_sum_type, Finset.smul_sum,
      neg_smul (M := ⨂[R]^3 ((Fin n ⊕ Fin n) → R)), Finset.sum_neg_distrib]
  · simp [symplecticTripleCup_one_apply, -Fintype.sum_sum_type, Finset.smul_sum,
      neg_smul (M := ⨂[R]^3 ((Fin n ⊕ Fin n) → R)), Finset.sum_neg_distrib]
  · simp [symplecticTripleCup_two_apply, -Fintype.sum_sum_type, Finset.smul_sum,
      neg_smul (M := ⨂[R]^3 ((Fin n ⊕ Fin n) → R)), Finset.sum_neg_distrib]

private theorem range_cupCapAt (p : Fin 3) :
    LinearMap.range (symplecticCupCapAt R 1 3 (![0, 0, 1] p) (![1, 2, 2] p)) =
      LinearMap.range (symplecticTripleCup R 1 p) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, cupCapAt_tprod]
      exact Submodule.smul_mem _ r (Submodule.smul_mem _ _ ⟨_, rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · rintro _ ⟨v, rfl⟩
    let w : Fin 3 → ((Fin 1 ⊕ Fin 1) → R) := match p with
      | 0 => ![Pi.single (Sum.inl 0) 1, Pi.single (Sum.inr 0) 1, v]
      | 1 => ![Pi.single (Sum.inl 0) 1, v, Pi.single (Sum.inr 0) 1]
      | 2 => ![v, Pi.single (Sum.inl 0) 1, Pi.single (Sum.inr 0) 1]
    refine ⟨-PiTensorProduct.tprod R w, ?_⟩
    rw [map_neg, cupCapAt_tprod]
    fin_cases p <;> simp [w, Matrix.J, neg_smul (M := ⨂[R]^3 ((Fin 1 ⊕ Fin 1) → R))]

/-- The sum of the rank-one cup placements is exactly the trace-tensor space in degree three. -/
theorem range_symplecticTripleCupSum_rankOne :
    LinearMap.range (symplecticTripleCupSum R 1) =
      (symplecticTraceTensors R 1 3).toSubmodule := by
  have hcup (p : Fin 3) : LinearMap.range (symplecticTripleCup R 1 p) ≤
      LinearMap.range (symplecticTripleCupSum R 1) := by
    rintro _ ⟨v, rfl⟩
    refine ⟨Pi.single p v, ?_⟩
    fin_cases p <;> simp
  have htrace (p : Fin 3) : LinearMap.range (symplecticTripleCup R 1 p) ≤
      (symplecticTraceTensors R 1 3).toSubmodule := by
    rw [← range_cupCapAt p]
    apply range_symplecticCupCapAt_le_symplecticTraceTensors
    fin_cases p <;> decide
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [symplecticTripleCupSum_apply]
    exact add_mem (add_mem (htrace 0 ⟨_, rfl⟩) (htrace 1 ⟨_, rfl⟩)) (htrace 2 ⟨_, rfl⟩)
  · rw [symplecticTraceTensors_toSubmodule_le_iff]
    intro i j hij
    have h (p : Fin 3) := (range_cupCapAt (R := R) p).le.trans (hcup p)
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact h 0
    · exact h 1
    · exact (congrArg LinearMap.range
        (symplecticCupCapAt_comm (k := R) (n := 1) (d := 3) 1 0)).le.trans (h 0)
    · exact False.elim (hij rfl)
    · exact h 2
    · exact (congrArg LinearMap.range
        (symplecticCupCapAt_comm (k := R) (n := 1) (d := 3) 2 0)).le.trans (h 1)
    · exact (congrArg LinearMap.range
        (symplecticCupCapAt_comm (k := R) (n := 1) (d := 3) 2 1)).le.trans (h 2)
    · exact False.elim (hij rfl)

/-- In rank one, the alternating sum of the three cup placements vanishes. -/
theorem symplecticTripleCup_relation_rankOne :
    symplecticTripleCup R 1 0 - symplecticTripleCup R 1 1 + symplecticTripleCup R 1 2 = 0 := by
  apply LinearMap.ext
  intro v
  apply (Basis.piTensorProduct (fun _ : Fin 3 => Pi.basisFun R (Fin 1 ⊕ Fin 1))).repr.injective
  ext w
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply, map_add, map_sub,
    Finsupp.add_apply, Finsupp.sub_apply, repr_symplecticTripleCup, map_zero, Finsupp.zero_apply]
  rcases w 0 with a | a <;> rcases w 1 with b | b <;> rcases w 2 with c | c <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [Matrix.J]

/-- The full kernel of the sum of the rank-one cup placements. This holds over every
commutative ring, including characteristic two, where the signs coincide. -/
theorem symplecticTripleCupSum_eq_zero_iff_rankOne (v : Fin 3 → ((Fin 1 ⊕ Fin 1) → R)) :
    symplecticTripleCupSum R 1 v = 0 ↔ v 1 = -v 0 ∧ v 2 = v 0 := by
  constructor
  · intro h
    have coord (w : Fin 3 → Fin 1 ⊕ Fin 1) := congrArg
      (fun t => (Basis.piTensorProduct (fun _ : Fin 3 =>
        Pi.basisFun R (Fin 1 ⊕ Fin 1))).repr t w) h
    simp only [symplecticTripleCupSum_apply, map_add, Finsupp.add_apply,
      repr_symplecticTripleCup, map_zero, Finsupp.zero_apply] at coord
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
    have h := LinearMap.congr_fun (symplecticTripleCup_relation_rankOne (R := R)) (v 0)
    rw [symplecticTripleCupSum_apply, h₁, h₂, map_neg]
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      sub_eq_add_neg] using h

/-- The first two cup placements freely parametrize the sum of all three cup images in
rank one. The third placement is absorbed using `D₁₂ = D₀₂ - D₀₁`. -/
noncomputable def symplecticTripleCupRangeEquivRankOne :
    (((Fin 1 ⊕ Fin 1) → R) × ((Fin 1 ⊕ Fin 1) → R)) ≃ₗ[R]
      LinearMap.range (symplecticTripleCupSum R 1) := by
  let f : (((Fin 1 ⊕ Fin 1) → R) × ((Fin 1 ⊕ Fin 1) → R)) →ₗ[R]
      LinearMap.range (symplecticTripleCupSum R 1) :=
    { toFun := fun v => ⟨symplecticTripleCup R 1 0 v.1 + symplecticTripleCup R 1 1 v.2,
        ⟨![v.1, v.2, 0], by simp⟩⟩
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_add] }
  have hf (v) : (f v).val =
      symplecticTripleCup R 1 0 v.1 + symplecticTripleCup R 1 1 v.2 := rfl
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have hzero : symplecticTripleCupSum R 1 ![v.1, v.2, 0] = 0 := by
      simpa [hf] using congrArg Subtype.val hv
    have h := (symplecticTripleCupSum_eq_zero_iff_rankOne _).mp hzero
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
    exact Prod.ext h.2.symm (by simpa [← h.2] using h.1)
  · rintro ⟨t, v, rfl⟩
    refine ⟨(v 0 - v 2, v 1 + v 2), Subtype.ext ?_⟩
    simp only [hf, map_sub, map_add, symplecticTripleCupSum_apply]
    have h := LinearMap.congr_fun (symplecticTripleCup_relation_rankOne (R := R)) (v 2)
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply] at h
    linear_combination -h

/-- The multiplicity parametrization sends `(x,y)` to `D₀₁ x + D₀₂ y`. -/
@[simp]
theorem symplecticTripleCupRangeEquivRankOne_apply
    (v : ((Fin 1 ⊕ Fin 1) → R) × ((Fin 1 ⊕ Fin 1) → R)) :
    (symplecticTripleCupRangeEquivRankOne (R := R) v : ⨂[R]^3 ((Fin 1 ⊕ Fin 1) → R)) =
      symplecticTripleCup R 1 0 v.1 + symplecticTripleCup R 1 1 v.2 := (rfl)

/-- Each of the three rank-one cup placements is injective, even over a coefficient ring
of characteristic two. -/
theorem symplecticTripleCup_injective_rankOne (p : Fin 3) :
    Function.Injective (symplecticTripleCup R 1 p) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  have hzero : symplecticTripleCupSum R 1 (Pi.single p v) = 0 := by
    rcases p with ⟨p, hp⟩
    interval_cases p <;> simpa [Pi.single_apply] using hv
  have h := (symplecticTripleCupSum_eq_zero_iff_rankOne _).mp hzero
  fin_cases p
  · simpa [Pi.single_apply] using h.2.symm
  · simpa [Pi.single_apply] using h.1
  · simpa [Pi.single_apply] using h.2

/-- Each individual cup image has dimension two in symplectic rank one. -/
theorem finrank_range_symplecticTripleCup_rankOne {K : Type*} [Field K] (p : Fin 3) :
    Module.finrank K (LinearMap.range (symplecticTripleCup K 1 p)) = 2 := by
  rw [LinearMap.finrank_range_of_inj (symplecticTripleCup_injective_rankOne p)]
  simp

/-- The sum of the three rank-one cup images has dimension four. -/
theorem finrank_range_symplecticTripleCupSum_rankOne {K : Type*} [Field K] :
    Module.finrank K (LinearMap.range (symplecticTripleCupSum K 1)) = 4 := by
  rw [← (symplecticTripleCupRangeEquivRankOne (R := K)).finrank_eq]
  simp

/-- In symplectic rank one, the trace tensors in degree three have dimension four. -/
theorem finrank_symplecticTraceTensors_three_rankOne {K : Type*} [Field K] :
    Module.finrank K (symplecticTraceTensors K 1 3).toSubmodule = 4 := by
  rw [← range_symplecticTripleCupSum_rankOne, finrank_range_symplecticTripleCupSum_rankOne]

/-- The harmonic part of the rank-one tensor cube has dimension four over a star-ordered
field. Together with the trace tensors it accounts for all eight tensor coordinates. -/
theorem finrank_symplecticHarmonicTensors_three_rankOne {K : Type*} [Field K] [PartialOrder K]
    [StarRing K] [StarOrderedRing K] :
    Module.finrank K (symplecticHarmonicTensors K 1 3) = 4 := by
  have h := Submodule.finrank_add_eq_of_isCompl
    (isCompl_symplecticHarmonicTensors_iSup_range_symplecticCupCapAt K 1 3)
  rw [← symplecticTraceTensors_toSubmodule, finrank_symplecticTraceTensors_three_rankOne] at h
  have ht : Module.finrank K (⨂[K]^3 ((Fin 1 ⊕ Fin 1) → K)) = 8 := by
    rw [Module.finrank_eq_card_basis
      (Basis.piTensorProduct (fun _ : Fin 3 => Pi.basisFun K (Fin 1 ⊕ Fin 1)))]
    simp
  omega

end TauCeti
