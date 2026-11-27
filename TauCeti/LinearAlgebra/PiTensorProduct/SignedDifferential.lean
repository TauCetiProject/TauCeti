/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.PiTensorProduct.SlotSum

/-!
# The signed differential on a finite tensor product

For a finite ordered family of graded modules with differentials of degree one, the signed
tensor differential applies each factor differential with the Koszul sign of the degrees in
the preceding slots. It raises total degree by one and squares to zero over any commutative
coefficient ring. This is the differential of the tensor power used in the construction of
Evens' norm. The ordered slot operator is `TauCeti.PiTensorProduct.slotHomotopy` with
`TauCeti.InternalGrading.koszulTwist` acting in the preceding slots.

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §§2–5.
-/

public section

open scoped TensorProduct

namespace TauCeti.PiTensorProduct

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (G : ∀ i, InternalGrading R (M i) ℤ) (d : ∀ i, Module.End R (M i))

/-- The differential on a finite ordered tensor product of graded modules, with the sign
`(-1)^(∑ j < i, deg xⱼ)` on the summand differentiating the `i`-th homogeneous factor. -/
noncomputable def signedDifferential : Module.End R (⨂[R] i, M i) :=
  slotHomotopy ι (fun j ↦ (G j).koszulTwist 1) d

/-- The signed differential is the ordered slot operator with the degree-one Koszul twist
in the preceding slots. -/
theorem signedDifferential_def :
    signedDifferential G d = slotHomotopy ι (fun j ↦ (G j).koszulTwist 1) d :=
  (rfl)

/-- On a pure tensor, the signed differential applies the Koszul twist in the slots preceding
the differentiated slot. -/
@[simp]
theorem signedDifferential_tprod (x : ∀ i, M i) :
    signedDifferential G d (PiTensorProduct.tprod R x) = ∑ i,
      PiTensorProduct.tprod R
        (Function.update (fun j ↦ if j < i then (G j).koszulTwist 1 (x j) else x j) i
          (d i (x i))) :=
  slotHomotopy_tprod _ _ x

/-- On homogeneous factors the coefficient for slot `i` is the product of the signs of the
degrees preceding that slot. -/
theorem signedDifferential_tprod_of_mem {p : ι → ℤ} {x : ∀ i, M i}
    (hx : ∀ i, x i ∈ (G i).piece (p i)) :
    signedDifferential G d (PiTensorProduct.tprod R x) =
      ∑ i, (∏ j with j < i, (((p j).negOnePow : ℤ) : R)) •
        PiTensorProduct.tprod R (Function.update x i (d i (x i))) := by
  rw [signedDifferential_tprod]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let c (j : ι) : R := if j < i then ((p j).negOnePow : ℤ) else 1
  have hprod : ∏ j, c j = ∏ j with j < i, (((p j).negOnePow : ℤ) : R) := by
    simp [c, Finset.prod_ite]
  rw [← hprod]
  refine Eq.trans ?_ (by
    simpa only [RingHom.id_apply] using
      (PiTensorProduct.tprod R).map_smul_univ c (Function.update x i (d i (x i))))
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp [c]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    by_cases hji : j < i
    · simp [c, hji, (G j).koszulTwist_one_apply_of_mem (hx j)]
    · simp [c, hji]

/-- A tensor of cycles is killed by the signed differential. -/
theorem signedDifferential_tprod_eq_zero {x : ∀ i, M i} (hx : ∀ i, d i (x i) = 0) :
    signedDifferential G d (PiTensorProduct.tprod R x) = 0 := by
  rw [signedDifferential_tprod]
  exact Finset.sum_eq_zero fun i _ ↦
    (PiTensorProduct.tprod R).map_coord_zero i (by simpa using hx i)

/-- If the factor modules are killed by two, the signed differential is the usual slot sum. -/
theorem signedDifferential_eq_slotSum (hM : ∀ i (x : M i), x + x = 0) :
    signedDifferential G d = slotSum ι d := by
  have htwist (i : ι) : (G i).koszulTwist 1 = LinearMap.id := by
    refine (G i).linearMap_ext fun p x hx ↦ ?_
    rw [(G i).koszulTwist_one_apply_of_mem hx, LinearMap.id_apply]
    rcases Int.units_eq_one_or p.negOnePow with h | h
    · simp [h]
    · simpa [h] using (neg_eq_of_add_eq_zero_left (hM i x))
  ext x
  simp only [LinearMap.compMultilinearMap_apply, signedDifferential_tprod, slotSum_tprod,
    htwist, LinearMap.id_apply, ite_self]

/-- If the factor differentials have degree one, so does the signed differential. -/
theorem isHomogeneous_signedDifferential
    (hd : ∀ i, LinearMap.IsHomogeneous (d i) (G i).piece (G i).piece 1) :
    LinearMap.IsHomogeneous (signedDifferential G d)
      (totalDegreePiece ι fun i ↦ (G i).piece) (totalDegreePiece ι fun i ↦ (G i).piece) 1 :=
  isHomogeneous_slotHomotopy (fun i ↦ (G i).isHomogeneous_koszulTwist 1) hd

/-- Degree-preserving factorwise chain maps intertwine the signed tensor differentials. -/
theorem signedDifferential_comp_map {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (H : ∀ i, InternalGrading R (N i) ℤ) (d' : ∀ i, Module.End R (N i))
    (f : ∀ i, N i →ₗ[R] M i)
    (hf : ∀ i, LinearMap.IsHomogeneous (f i) (H i).piece (G i).piece 0)
    (hdf : ∀ i, d i ∘ₗ f i = f i ∘ₗ d' i) :
    signedDifferential G d ∘ₗ PiTensorProduct.map f =
      PiTensorProduct.map f ∘ₗ signedDifferential H d' :=
  slotHomotopy_comp_map f (fun i ↦ by simpa using (hf i).koszulTwist_comp_eq_smul 1) hdf

/-- The maps in the summand of the tensor differential at slot `i`. -/
private noncomputable def signedSlot (i : ι) (j : ι) : Module.End R (M j) :=
  Function.update (fun k ↦ if k < i then (G k).koszulTwist 1 else LinearMap.id) i (d i) j

omit [Fintype ι] in
private theorem signedSlot_apply (i j : ι) :
    signedSlot G d i j =
      if j < i then (G j).koszulTwist 1 else if j = i then d j else LinearMap.id := by
  rcases eq_or_ne j i with rfl | hj
  · simp [signedSlot]
  · simp [signedSlot, hj]

omit [Fintype ι] in
/-- Differentiating twice in the same slot vanishes when its differential squares to zero. -/
private theorem signedSlot_comp_self (i : ι) (hdd : d i ∘ₗ d i = 0) :
    PiTensorProduct.map (signedSlot G d i) ∘ₗ PiTensorProduct.map (signedSlot G d i) = 0 := by
  rw [← PiTensorProduct.map_comp]
  apply map_eq_zero_of_eq_zero (k := i)
  simpa [signedSlot_apply] using hdd

omit [Fintype ι] in
/-- Differentiating two different slots in opposite orders gives cancelling terms. -/
private theorem signedSlot_comp_add_comp_of_lt {i j : ι} (hij : i < j)
    (hd : LinearMap.IsHomogeneous (d i) (G i).piece (G i).piece 1) :
    PiTensorProduct.map (signedSlot G d i) ∘ₗ PiTensorProduct.map (signedSlot G d j) +
      PiTensorProduct.map (signedSlot G d j) ∘ₗ PiTensorProduct.map (signedSlot G d i) = 0 := by
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp,
    map_add_map_eq_map_update _ _ i]
  · apply map_eq_zero_of_eq_zero (k := i)
    have h : (G i).koszulTwist 1 ∘ₗ d i = -(d i ∘ₗ (G i).koszulTwist 1) := by
      simpa using hd.koszulTwist_comp_eq_smul 1
    simp [signedSlot_apply, hij, h]
  · intro k hk
    rcases eq_or_ne k j with rfl | hkj
    · simp [signedSlot_apply, not_lt_of_gt hij, hij.ne']
    by_cases hki : k < i
    · simp [signedSlot_apply, hki, hki.trans hij]
    · simp [signedSlot_apply, hki, hk, hkj]

/-- The signed tensor differential squares to zero when each factor differential does. The
off-diagonal terms cancel in pairs by the sign change induced by the earlier differential. -/
theorem signedDifferential_comp_self
    (hd : ∀ i, LinearMap.IsHomogeneous (d i) (G i).piece (G i).piece 1)
    (hdd : ∀ i, d i ∘ₗ d i = 0) :
    signedDifferential G d ∘ₗ signedDifferential G d = 0 := by
  let S (i : ι) := PiTensorProduct.map (signedSlot G d i)
  have hs : signedDifferential G d = ∑ i, S i := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, signedDifferential_tprod,
      LinearMap.sum_apply, S, signedSlot, PiTensorProduct.map_tprod]
    refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (funext fun j ↦ ?_)
    rw [Function.apply_update (fun k (f : Module.End R (M k)) ↦ f (x k))]
    congr 2
    funext k
    split_ifs <;> rfl
  rw [hs, ← Module.End.mul_eq_comp, Finset.sum_mul_sum]
  refine Finset.sum_sum_eq_zero_of_diag _ (fun i _ ↦ signedSlot_comp_self G d i (hdd i))
    (fun i _ j _ hij ↦ ?_)
  rcases lt_or_gt_of_ne hij with h | h
  · exact signedSlot_comp_add_comp_of_lt G d h (hd i)
  · rw [add_comm]
    exact signedSlot_comp_add_comp_of_lt G d h (hd j)

end TauCeti.PiTensorProduct
