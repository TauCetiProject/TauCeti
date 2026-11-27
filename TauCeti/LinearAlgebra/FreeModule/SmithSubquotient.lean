/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import TauCeti.Algebra.Module.Submodule.Quotient
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Subquotients of a free module by rescaled basis vectors

Let `b` be a basis of an `R`-module `M`, let `e : κ ↪ ι` select finitely many of its vectors and
let `a : κ → R`. Write `B` for the span of the rescaled vectors `a j • b (e j)` and `W` for the
span of the unselected basis vectors, the vectors whose coordinates along `e` vanish. If a
submodule `Z` contains every selected vector `b (e j)`, then

* `Z ≃ (κ → R) × (Z ⊓ W)`, splitting off the coordinates along `e`
  (`Module.Basis.equivPiProdOfMem`), and
* `Z ⧸ B ≃ (Π j, R ⧸ (a j)) × (Z ⊓ W)` (`Module.Basis.quotientSpanSMulEquivOfMem`).

This is how a Smith normal form of the boundaries `B = im d` inside a free term `C` of a complex
computes the homology `Z ⧸ B`, where `Z = ker d'` is the module of cycles: the Smith basis
vectors along which `B` is supported are cycles as soon as the next term is torsion-free, and the
cycles off them form the free part of the homology. Over a principal ideal domain the free part
`Z ⊓ W` is free of rank `rank Z - |κ|` (`Module.Basis.finrank_eq_card_add_finrank_inf`).

The span `B` of the rescaled vectors is cut out by divisibility of the coordinates along `e` and
vanishing of the others (`Module.Basis.mem_span_range_smul_comp_iff`). A Smith normal form
`Module.Basis.SmithNormalForm N ι n` in Mathlib's sense presents `N` in this way
(`Module.Basis.SmithNormalForm.eq_span_range_smul`).

## Main definitions

* `Module.Basis.equivPiProdOfMem`: the splitting `Z ≃ (κ → R) × (Z ⊓ W)`.
* `Module.Basis.quotientSpanSMulEquivOfMem`: the subquotient `Z ⧸ B ≃ (Π j, R ⧸ (a j)) × (Z ⊓ W)`.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, Addison-Wesley, 1984, §11, where the
  homology of a complex of finitely generated free abelian groups is read off the Smith normal
  forms of its boundary matrices.
-/

public section

open Module Submodule

namespace Module.Basis

section Ring

variable {R M ι κ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (b : Basis ι R M) (e : κ ↪ ι)

section Coordinates

variable [Fintype κ]

/-- Removing from `x` its components along the selected basis vectors leaves no coordinate along
them. -/
theorem repr_sub_sum_repr_smul_apply_embedding (x : M) (j : κ) :
    b.repr (x - ∑ j', b.repr x (e j') • b (e j')) (e j) = 0 := by
  classical
  simp [Finsupp.single_apply, e.injective.eq_iff]

/-- Removing from `x` its components along the selected basis vectors keeps its coordinates off
the range of `e`. -/
theorem repr_sub_sum_repr_smul_apply_of_notMem (x : M) {i : ι} (hi : i ∉ Set.range e) :
    b.repr (x - ∑ j, b.repr x (e j) • b (e j)) i = b.repr x i := by
  classical
  have : ∀ j, e j ≠ i := fun j h ↦ hi ⟨j, h⟩
  simp [this]

/-- The components of `x` along the selected basis vectors are the only ones removed: the
remainder lies in the span of the unselected basis vectors. -/
theorem sub_sum_repr_smul_mem_span_image_compl (x : M) :
    x - ∑ j, b.repr x (e j) • b (e j) ∈ span R (b '' (Set.range e)ᶜ) := by
  rw [b.mem_span_image]
  rintro i hi ⟨j, rfl⟩
  exact Finsupp.mem_support_iff.1 hi (b.repr_sub_sum_repr_smul_apply_embedding e x j)

/-- The remainder of `x` off the selected basis vectors vanishes exactly when the coordinates of
`x` off the range of `e` vanish. -/
theorem sub_sum_repr_smul_eq_zero_iff {x : M} :
    x - ∑ j, b.repr x (e j) • b (e j) = 0 ↔ ∀ i ∉ Set.range e, b.repr x i = 0 := by
  rw [← b.repr.injective.eq_iff, map_zero, Finsupp.ext_iff]
  refine ⟨fun h i hi ↦ ?_, fun h i ↦ ?_⟩
  · rw [← b.repr_sub_sum_repr_smul_apply_of_notMem e x hi]
    exact h i
  · by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      exact b.repr_sub_sum_repr_smul_apply_embedding e x j
    · rw [b.repr_sub_sum_repr_smul_apply_of_notMem e x hi]
      exact h i hi

/-- A vector whose coordinates off the range of `e` vanish is the sum of its components along
the selected basis vectors. -/
theorem sum_repr_smul_eq_self {x : M} (hx : ∀ i ∉ Set.range e, b.repr x i = 0) :
    ∑ j, b.repr x (e j) • b (e j) = x :=
  (sub_eq_zero.1 ((b.sub_sum_repr_smul_eq_zero_iff e).2 hx)).symm

end Coordinates

variable [Fintype κ] {Z : Submodule R M} (hZ : ∀ j, b (e j) ∈ Z)

/-- **Splitting off the selected coordinates.** If a submodule `Z` contains the selected basis
vectors `b (e j)`, then `Z` is the product of the free module on those vectors, through their
coordinates, and of its intersection with the span of the unselected basis vectors. -/
noncomputable def equivPiProdOfMem :
    Z ≃ₗ[R] (κ → R) × ↥(Z ⊓ span R (b '' (Set.range e)ᶜ)) where
  toFun z := (fun j ↦ b.repr z (e j), ⟨z - ∑ j, b.repr z (e j) • b (e j),
    Submodule.mem_inf.2 ⟨Z.sub_mem z.property (Z.sum_mem fun j _ ↦ Z.smul_mem _ (hZ j)),
      b.sub_sum_repr_smul_mem_span_image_compl e z⟩⟩)
  invFun p := ⟨∑ j, p.1 j • b (e j) + p.2,
    Z.add_mem (Z.sum_mem fun j _ ↦ Z.smul_mem _ (hZ j)) (Submodule.mem_inf.1 p.2.property).1⟩
  map_add' y z := by
    ext j
    · simp
    · simp [add_smul, Finset.sum_add_distrib]
      abel
  map_smul' r z := by
    ext j <;> simp [mul_smul, Finset.smul_sum, smul_sub]
  left_inv z := by
    ext
    simp
  right_inv p := by
    obtain ⟨c, w, hwZ, hw⟩ := p
    -- a vector off the selected basis vectors has no coordinates along them
    have h0 : ∀ j, b.repr w (e j) = 0 := fun j ↦
      Finsupp.notMem_support_iff.1 fun h ↦ (b.mem_span_image.1 hw) h ⟨j, rfl⟩
    have hc : ∀ j, ∑ j', Finsupp.single (e j') (c j') (e j) = c j := fun j ↦ by
      classical
      simp [Finsupp.single_apply, e.injective.eq_iff]
    ext j <;> simp [h0, hc]

@[simp]
theorem equivPiProdOfMem_apply_fst (z : Z) (j : κ) :
    (b.equivPiProdOfMem e hZ z).1 j = b.repr z (e j) := (rfl)

@[simp]
theorem coe_equivPiProdOfMem_apply_snd (z : Z) :
    ((b.equivPiProdOfMem e hZ z).2 : M) = z - ∑ j, b.repr z (e j) • b (e j) := (rfl)

@[simp]
theorem coe_equivPiProdOfMem_symm_apply (c : κ → R) (w : ↥(Z ⊓ span R (b '' (Set.range e)ᶜ))) :
    ((b.equivPiProdOfMem e hZ).symm (c, w) : M) = ∑ j, c j • b (e j) + w := (rfl)

include hZ in
/-- **The rank of a submodule containing the selected basis vectors.** When the part of `Z` off the
selected basis vectors is finite free, the rank of `Z` is the number of selected vectors plus the
rank of that part. -/
theorem finrank_eq_card_add_finrank_inf [StrongRankCondition R]
    [Module.Free R ↥(Z ⊓ span R (b '' (Set.range e)ᶜ))]
    [Module.Finite R ↥(Z ⊓ span R (b '' (Set.range e)ᶜ))] :
    finrank R Z = Fintype.card κ + finrank R ↥(Z ⊓ span R (b '' (Set.range e)ᶜ)) := by
  rw [(b.equivPiProdOfMem e hZ).finrank_eq, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

end Ring

section CommRing

variable {R M ι κ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (b : Basis ι R M) (e : κ ↪ ι) [Fintype κ] {Z : Submodule R M} (hZ : ∀ j, b (e j) ∈ Z)

/-- The classes of the coordinates along `e` modulo the `a j`, and the remainder off the selected
basis vectors. Its kernel is the span of the rescaled vectors `a j • b (e j)`. -/
private noncomputable def quotientMapOfMem (a : κ → R) :
    Z →ₗ[R] (∀ j, R ⧸ Ideal.span ({a j} : Set R)) × ↥(Z ⊓ span R (b '' (Set.range e)ᶜ)) :=
  LinearMap.prodMap (LinearMap.pi fun j ↦ (Ideal.span ({a j} : Set R)).mkQ ∘ₗ LinearMap.proj j)
      LinearMap.id ∘ₗ (b.equivPiProdOfMem e hZ).toLinearMap

private theorem quotientMapOfMem_apply (a : κ → R) (z : Z) :
    b.quotientMapOfMem e hZ a z =
      (fun j ↦ Ideal.Quotient.mk _ (b.repr z (e j)), (b.equivPiProdOfMem e hZ z).2) := by
  ext j <;> simp [quotientMapOfMem, Ideal.Quotient.mk_eq_mk]

private theorem quotientMapOfMem_surjective (a : κ → R) :
    Function.Surjective (b.quotientMapOfMem e hZ a) := by
  rintro ⟨q, w⟩
  choose c hc using fun j ↦ Ideal.Quotient.mk_surjective (q j)
  refine ⟨(b.equivPiProdOfMem e hZ).symm (c, w), ?_⟩
  ext j
  · simp [quotientMapOfMem, ← hc, Ideal.Quotient.mk_eq_mk]
  · simp [quotientMapOfMem]

private theorem ker_quotientMapOfMem (a : κ → R) :
    LinearMap.ker (b.quotientMapOfMem e hZ a) =
      (span R (Set.range fun j ↦ a j • b (e j))).comap Z.subtype := by
  ext z
  rw [LinearMap.mem_ker, quotientMapOfMem_apply, mem_comap, subtype_apply,
    b.mem_span_range_smul_comp_iff e a, ← b.sub_sum_repr_smul_eq_zero_iff e]
  simp [Prod.ext_iff, funext_iff, ← Subtype.coe_inj, Ideal.Quotient.eq_zero_iff_dvd]

/-- **The subquotient by rescaled selected basis vectors.** If a submodule `Z` contains the
selected basis vectors `b (e j)`, then its quotient by the span of the rescaled vectors
`a j • b (e j)` is the product of the cyclic modules `R ⧸ (a j)` and of the part of `Z` off the
selected basis vectors. -/
noncomputable def quotientSpanSMulEquivOfMem (a : κ → R) :
    (Z ⧸ (span R (Set.range fun j ↦ a j • b (e j))).comap Z.subtype) ≃ₗ[R]
      (∀ j, R ⧸ Ideal.span ({a j} : Set R)) × ↥(Z ⊓ span R (b '' (Set.range e)ᶜ)) :=
  (Submodule.quotEquivOfEq _ _ (b.ker_quotientMapOfMem e hZ a).symm).trans
    ((b.quotientMapOfMem e hZ a).quotKerEquivOfSurjective (b.quotientMapOfMem_surjective e hZ a))

/-- The subquotient equivalence sends the class of `z` to the classes of its coordinates along
`e` and to its remainder off the selected basis vectors. -/
@[simp]
theorem quotientSpanSMulEquivOfMem_mk (a : κ → R) (z : Z) :
    b.quotientSpanSMulEquivOfMem e hZ a (Submodule.Quotient.mk z) =
      (fun j ↦ Ideal.Quotient.mk _ (b.repr z (e j)), (b.equivPiProdOfMem e hZ z).2) := by
  simp [quotientSpanSMulEquivOfMem, quotientMapOfMem_apply]

end CommRing

end Module.Basis

namespace LinearMap

variable {R M M' ι ι' κ : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ]
  (f : M' →ₗ[R] M) {e : κ ↪ ι} {e' : κ ↪ ι'} {a : κ → R}

/-- **The range of a map with a rectangular diagonal matrix.** If the matrix of `f` in bases `b'`
and `b` has the entry `a j` in row `e j` and column `e' j` and vanishes elsewhere, then the range
of `f` is the span of the rescaled basis vectors `a j • b (e j)`. -/
theorem range_eq_span_range_smul_of_toMatrix_eq [Finite ι] (b' : Basis ι' R M') (b : Basis ι R M)
    (h : LinearMap.toMatrix b' b f = ∑ j, Matrix.single (e j) (e' j) (a j)) :
    range f = span R (Set.range fun j ↦ a j • b (e j)) := by
  have hrepr (l : ι') (i : ι) :
      b.repr (f (b' l)) i = ∑ j, if e j = i ∧ e' j = l then a j else 0 := by
    rw [← LinearMap.toMatrix_apply, h, Matrix.sum_apply]
    simp_rw [Matrix.single_apply]
  -- the columns of the matrix: the selected ones are rescaled basis vectors, the others vanish
  have hsel (j : κ) : f (b' (e' j)) = a j • b (e j) := by
    classical
    refine b.ext_elem fun i ↦ ?_
    simp [hrepr, Finsupp.single_apply, e'.injective.eq_iff, and_comm, ite_and]
  have hoff (l : ι') (hl : l ∉ Set.range e') : f (b' l) = 0 := by
    refine b.ext_elem fun i ↦ ?_
    rw [hrepr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right_iff.2 fun h ↦ absurd ⟨j, h.2⟩ hl
  rw [LinearMap.range_eq_map, ← b'.span_eq, Submodule.map_span, ← Set.range_comp,
    span_range_eq_span_range_comp_of_eq_zero (w := f ∘ b') e' hoff]
  simp only [Function.comp_def, hsel]

/-- **The range of a map whose matrix is equivalent to a rectangular diagonal matrix.** If
`L * A * Q` is the rectangular diagonal matrix with the entry `a j` in row `e j` and column `e' j`,
where `A` is the matrix of `f` in bases `b'` and `b` and `L`, `Q` have unit determinant, then in the
basis `c` of `M` with `c.toMatrix b = L` the range of `f` is the span of the rescaled vectors
`a j • c (e j)`. -/
theorem exists_basis_range_eq_span_range_smul_of_mul_toMatrix_mul_eq [Fintype ι]
    (b' : Basis ι' R M')
    (b : Basis ι R M) {L : Matrix ι ι R} {Q : Matrix ι' ι' R} (hL : IsUnit L.det)
    (hQ : IsUnit Q.det)
    (h : L * LinearMap.toMatrix b' b f * Q = ∑ j, Matrix.single (e j) (e' j) (a j)) :
    ∃ c : Basis ι R M, c.toMatrix b = L ∧
      range f = span R (Set.range fun j ↦ a j • c (e j)) := by
  let c := b.map (Matrix.toLinearEquiv b L⁻¹ (Matrix.isUnit_nonsing_inv_det L hL))
  let c' := b'.map (Matrix.toLinearEquiv b' Q hQ)
  have hbc : b.toMatrix c = L⁻¹ := by
    ext i p
    simp [c, Basis.toMatrix_apply, Matrix.toLin_self, Finsupp.single_apply]
  have hcb : c.toMatrix b = L := by
    rw [← Matrix.mul_nonsing_inv_cancel_left (A := L) (c.toMatrix b) hL, ← hbc,
      b.toMatrix_mul_toMatrix_flip, Matrix.mul_one]
  have hbc' : b'.toMatrix c' = Q := by
    ext l m
    simp [c', Basis.toMatrix_apply, Matrix.toLin_self, Finsupp.single_apply]
  refine ⟨c, hcb, f.range_eq_span_range_smul_of_toMatrix_eq (e' := e') c' c ?_⟩
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c' b' c b, hcb, hbc', h]

end LinearMap

namespace Module.Basis.SmithNormalForm

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : Submodule R M} {n : ℕ}

/-- A submodule in Smith normal form is the span of the rescaled selected basis vectors
`a j • bM (f j)`. -/
theorem eq_span_range_smul (snf : Basis.SmithNormalForm N ι n) :
    N = span R (Set.range fun j ↦ snf.a j • snf.bM (snf.f j)) :=
  N.eq_span_of_diagonal_basis (fun j ↦ snf.bM (snf.f j)) snf.bN snf.snf

/-- The diagonal coefficients of a Smith normal form over a nontrivial ring are nonzero, since the
basis vectors `a j • bM (f j)` of `N` are. -/
theorem a_ne_zero [Nontrivial R] (snf : Basis.SmithNormalForm N ι n) (j : Fin n) :
    snf.a j ≠ 0 := by
  intro h
  apply snf.bN.ne_zero j
  rw [← Subtype.coe_inj, snf.snf, h, zero_smul, ZeroMemClass.coe_zero]

end Module.Basis.SmithNormalForm
