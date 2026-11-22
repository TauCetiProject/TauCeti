/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# From Weyl-group elements to integer matrices on the simple roots

For a base `b` of a root pairing `P`, an element `w` of the Weyl group *acts by* the integer matrix
`W` (`RootPairing.Base.ActsBy b w W`) if `w • αⱼ = ∑ₖ W k j • αₖ` for every simple root `αⱼ`.
Acting-by is multiplicative, and the simple reflection `sᵢ` acts by `reflMatrix b.cartanMatrix i`.
The action is faithful for a finite anisotropic root pairing over a domain, in particular for a
crystallographic one in characteristic zero (`RootPairing.weylGroup.eq_one_of_forall_smul_root_eq`;
the roots need not span), so the order of `w` is the order of `W`.

Every element of the Weyl group acts by some integer matrix, because every root is an integer
combination of the simple roots. When the roots span, the simple roots form a basis of the weight
space and `W` is the matrix of `w` in that basis. So the characteristic polynomial of every
Weyl-group element has integer coefficients, and its roots are closed under Galois conjugation.

## Main results

* `RootPairing.Base.actsBy_wordProd`: a word in the simple reflections acts by the product of the
  corresponding reflection matrices.
* `RootPairing.Base.ActsBy.orderOf_eq`: if `w` acts by `W`, then `orderOf w = orderOf W`.
* `RootPairing.Base.exists_actsBy`: every element of the Weyl group acts by an integer matrix.
* `RootPairing.Base.ActsBy.toMatrix_weylGroupRootRep` and
  `RootPairing.Base.ActsBy.charpoly_weylGroupRootRep`: for a root system, the integer matrix of `w`
  is its matrix on the weight space in the basis of simple roots, so the two have the same
  characteristic polynomial.
* `RootPairing.Base.exists_charpoly_weylGroupRootRep_eq_map`: the characteristic polynomial of
  every Weyl-group element on the weight space of a root system has integer coefficients.
* `RootPairing.Base.exists_charpoly_weylGroupRootRep_eq_map_rat`: over a `ℚ`-algebra, the same
  characteristic polynomial has rational coefficients.
* `RootPairing.Base.orderOf_wordProd_of_cartanMatrix_eq`: for a base whose Cartan matrix is `A` up
  to a relabelling `e`, the Coxeter element spelled in the order `e` has the order of
  `coxeterElement A`.
-/

public section

open Matrix Submodule TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- The Weyl-group element `w` sends the simple root `αⱼ` of `b` to `∑ₖ W k j • αₖ`. -/
def ActsBy (b : P.Base) (w : P.weylGroup) (W : Matrix b.support b.support ℤ) : Prop :=
  ∀ j : b.support, w • P.root j = ∑ k, W k j • P.root k

omit [DecidableEq ι] in
/-- The defining property of `RootPairing.Base.ActsBy`. -/
theorem actsBy_iff {b : P.Base} {w : P.weylGroup} {W : Matrix b.support b.support ℤ} :
    ActsBy b w W ↔ ∀ j : b.support, w • P.root j = ∑ k, W k j • P.root k :=
  Iff.rfl

/-- The identity of the Weyl group acts by the identity matrix. -/
theorem actsBy_one (b : P.Base) : ActsBy b 1 1 := by
  intro j
  simp [Matrix.one_apply, ite_smul]

omit [DecidableEq ι] in
/-- Acting-by is multiplicative. -/
theorem ActsBy.mul {b : P.Base} {v w : P.weylGroup} {V W : Matrix b.support b.support ℤ}
    (hv : ActsBy b v V) (hw : ActsBy b w W) : ActsBy b (v * w) (V * W) := by
  intro j
  calc (v * w) • P.root j = v • (w • P.root j) := mul_smul v w _
    _ = v • ∑ k, W k j • P.root k := by rw [hw j]
    _ = ∑ k, W k j • (v • P.root k) := by
        rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun k _ => smul_comm v _ _
    _ = ∑ k, W k j • ∑ l, V l k • P.root l := Finset.sum_congr rfl fun k _ => by rw [hv k]
    _ = ∑ l, (V * W) l j • P.root l := by
        simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

/-- If `w` acts by `W`, then `w ^ k` acts by `W ^ k`. -/
theorem ActsBy.pow {b : P.Base} {w : P.weylGroup} {W : Matrix b.support b.support ℤ}
    (h : ActsBy b w W) (k : ℕ) : ActsBy b (w ^ k) (W ^ k) := by
  induction k with
  | zero => simpa using actsBy_one b
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

/-- The simple reflection `sᵢ` acts by `reflMatrix b.cartanMatrix i`. -/
theorem actsBy_ofIdx [P.IsCrystallographic] (b : P.Base) (i : b.support) :
    ActsBy b (weylGroup.ofIdx P i) (reflMatrix b.cartanMatrix i) := by
  intro j
  rw [weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply_root]
  simp only [reflMatrix_apply, sub_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [← Int.cast_smul_eq_zsmul R (b.cartanMatrix j i), ← eq_intCast (algebraMap ℤ R),
    b.algebraMap_cartanMatrixIn_apply (S := ℤ)]

variable [P.IsCrystallographic]

/-- A word in the simple reflections acts by the product of the corresponding reflection
matrices. -/
theorem actsBy_wordProd (b : P.Base) (l : List b.support) :
    ActsBy b (wordProd P b l) (l.map (reflMatrix b.cartanMatrix)).prod := by
  induction l with
  | nil => simpa [wordProd_nil] using actsBy_one b
  | cons i l ih =>
    simpa only [wordProd_cons, List.map_cons, List.prod_cons] using
      (actsBy_ofIdx b i).mul ih

/-- An element acting trivially on the simple roots is trivial. -/
theorem ActsBy.eq_one [Finite ι] [IsDomain R] [CharZero R] {b : P.Base}
    {w : P.weylGroup} (h : ActsBy b w 1) : w = 1 := by
  have := Fintype.ofFinite ι
  have hfix : ∀ j : b.support, w • P.root j = P.root j := fun j => by
    simpa [Matrix.one_apply, ite_smul] using h j
  have hspan : ∀ x ∈ span ℤ (P.root '' b.support), w • x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨j, hj, rfl⟩ := hx; exact hfix ⟨j, hj⟩
    | zero => exact smul_zero w
    | add x y _ _ hx hy => rw [smul_add, hx, hy]
    | smul n x _ hx => rw [smul_comm w n x, hx]
  exact weylGroup.eq_one_of_forall_smul_root_eq fun i => hspan _ (b.root_mem_span_int i)

omit [DecidableEq ι] [P.IsCrystallographic] in
/-- The matrix by which an element acts is unique. -/
theorem ActsBy.unique [CharZero R] {b : P.Base} {w : P.weylGroup}
    {V W : Matrix b.support b.support ℤ} (hV : ActsBy b w V) (hW : ActsBy b w W) : V = W := by
  have hli : LinearIndependent ℤ (fun k : b.support => P.root k) :=
    b.linearIndepOn_root.restrict_scalars' ℤ
  ext k j
  have h0 : ∑ l, (V l j - W l j) • P.root l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← hV j, ← hW j, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 k)

/-- If `w` acts by the integer matrix `W`, then `w` and `W` have the same order. -/
theorem ActsBy.orderOf_eq [CharZero R] [Finite ι] [IsDomain R] {b : P.Base}
    {w : P.weylGroup} {W : Matrix b.support b.support ℤ} (h : ActsBy b w W) :
    orderOf w = orderOf W := by
  refine orderOf_eq_orderOf_iff.2 fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · exact (h.pow k).unique (by simpa [hk] using actsBy_one b)
  · exact ActsBy.eq_one (by simpa [hk] using h.pow k)

/-! ### The matrix of the reflection representation -/

omit [DecidableEq ι] in
/-- The reflection in any root, simple or not, acts on the simple roots by an integer matrix,
since the root is an integer combination of the simple roots. -/
theorem exists_actsBy_ofIdx (b : P.Base) (i : ι) :
    ∃ W : Matrix b.support b.support ℤ, ActsBy b (weylGroup.ofIdx P i) W := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ι → ℤ, P.root i = ∑ j ∈ b.support, f j • P.root j := by
    obtain ⟨f, -, hf | hf⟩ := b.exists_root_eq_sum_nat_or_neg i
    · exact ⟨fun j ↦ f j, by simp [hf]⟩
    · exact ⟨fun j ↦ -f j, by simp [hf, neg_smul]⟩
  refine ⟨Matrix.of fun k j ↦ (if k = j then 1 else 0) - P.pairingIn ℤ j i * f k, fun j ↦ ?_⟩
  rw [weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply_root, hf,
    ← Finset.sum_coe_sort b.support, ← P.algebraMap_pairingIn ℤ]
  simp [Finset.smul_sum, sub_smul, ite_smul, Finset.sum_sub_distrib, mul_smul,
    Int.cast_smul_eq_zsmul]

omit [DecidableEq ι] in
/-- **Every element of the Weyl group acts by an integer matrix**, since the reflections
generating it do. -/
theorem exists_actsBy (b : P.Base) (w : P.weylGroup) :
    ∃ W : Matrix b.support b.support ℤ, ActsBy b w W := by
  classical
  obtain ⟨w, hw⟩ := w
  induction hw using weylGroup.induction with
  | mem i => exact b.exists_actsBy_ofIdx i
  | one => exact ⟨1, actsBy_one b⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨X, hX⟩ := ihx
    obtain ⟨Y, hY⟩ := ihy
    rw [← Submonoid.mk_mul_mk _ _ _ hx hy]
    exact ⟨X * Y, hX.mul hY⟩

section RootSystem

variable [P.IsRootSystem]

omit [P.IsCrystallographic] in
/-- If `w` acts by `W`, then `W`, read in `R`, is the matrix of `w` acting on the weight space in
the basis of simple roots of the root system. -/
theorem ActsBy.toMatrix_weylGroupRootRep {b : P.Base} {w : P.weylGroup}
    {W : Matrix b.support b.support ℤ} (h : ActsBy b w W) :
    LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep w) =
      W.map (Int.castRingHom R) := by
  ext k j
  have hj : w • P.root j = ∑ l, (W l j : R) • b.toWeightBasis l := by
    simp only [h j, Base.toWeightBasis_apply, Int.cast_smul_eq_zsmul]
  rw [LinearMap.toMatrix_apply, Base.toWeightBasis_apply, weylGroupRootRep_apply, hj,
    Module.Basis.repr_sum_self]
  simp

omit [P.IsCrystallographic] in
/-- **Integrality of the characteristic polynomial.** If `w` acts on the simple roots of a root
system by the integer matrix `W`, then the characteristic polynomial of `w` acting on the weight
space is the characteristic polynomial of `W`, with its coefficients cast to `R`. -/
theorem ActsBy.charpoly_weylGroupRootRep [Module.Free R M] [Module.Finite R M] {b : P.Base}
    {w : P.weylGroup} {W : Matrix b.support b.support ℤ} (h : ActsBy b w W) :
    (P.weylGroupRootRep w).charpoly = W.charpoly.map (Int.castRingHom R) := by
  rw [← LinearMap.charpoly_toMatrix _ b.toWeightBasis, h.toMatrix_weylGroupRootRep,
    Matrix.charpoly_map]

omit [DecidableEq ι] in
/-- **The characteristic polynomials of the Weyl group are integral**: for a base of a
crystallographic root system, every Weyl-group element has a characteristic polynomial on the
weight space with integer coefficients. -/
theorem exists_charpoly_weylGroupRootRep_eq_map [Module.Free R M] [Module.Finite R M]
    (b : P.Base) (w : P.weylGroup) :
    ∃ p : Polynomial ℤ, p.map (Int.castRingHom R) = (P.weylGroupRootRep w).charpoly := by
  classical
  obtain ⟨W, hW⟩ := b.exists_actsBy w
  exact ⟨W.charpoly, (ActsBy.charpoly_weylGroupRootRep hW).symm⟩

omit [DecidableEq ι] in
/-- **The characteristic polynomials of the Weyl group are rational**: over a `ℚ`-algebra, every
Weyl-group element of a crystallographic root system has a characteristic polynomial on the weight
space with rational coefficients. -/
theorem exists_charpoly_weylGroupRootRep_eq_map_rat [Algebra ℚ R] [Module.Free R M]
    [Module.Finite R M] (b : P.Base) (w : P.weylGroup) :
    ∃ q : Polynomial ℚ, q.map (algebraMap ℚ R) = (P.weylGroupRootRep w).charpoly := by
  obtain ⟨p, hp⟩ := b.exists_charpoly_weylGroupRootRep_eq_map w
  refine ⟨p.map (Int.castRingHom ℚ), ?_⟩
  rw [Polynomial.map_map, ← hp]
  congr 1
  exact Subsingleton.elim _ _

end RootSystem

/-! ### Relabelling along a Dynkin numbering -/

/-- The product of the simple-reflection matrices of `b`, in the order `e`, is the Coxeter
element of `A`, relabelled. -/
theorem prod_reflMatrix_eq {n : ℕ} (b : P.Base) (A : Matrix (Fin n) (Fin n) ℤ)
    (e : b.support ≃ Fin n) (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) :
    (((List.finRange n).map e.symm).map (reflMatrix b.cartanMatrix)).prod =
      reindexAlgEquiv ℤ ℤ e.symm (coxeterElement A) := by
  have hC : b.cartanMatrix = A.submatrix e e := by ext i j; exact hA i j
  rw [hC, coxeterElement]
  exact prod_map_reflMatrix_submatrix A e (List.finRange n)

omit [DecidableEq ι] in
/-- **The Weyl-group Coxeter element has the order of the Coxeter element of its Cartan
matrix.** -/
theorem orderOf_wordProd_of_cartanMatrix_eq [CharZero R] [Finite ι] [IsDomain R] {n : ℕ}
    (b : P.Base)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : b.support ≃ Fin n)
    (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) :
    orderOf (wordProd P b ((List.finRange n).map e.symm)) = orderOf (coxeterElement A) := by
  classical
  rw [(actsBy_wordProd b _).orderOf_eq, prod_reflMatrix_eq b A e hA]
  exact orderOf_injective (reindexAlgEquiv ℤ ℤ e.symm).toRingEquiv.toMulEquiv.toMonoidHom
    (reindexAlgEquiv ℤ ℤ e.symm).injective _

end RootPairing.Base

end
