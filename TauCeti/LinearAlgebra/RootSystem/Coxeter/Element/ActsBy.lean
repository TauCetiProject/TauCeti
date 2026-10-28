/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.E8
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Exceptional
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# From Weyl-group elements to integer matrices on the simple roots

For a base `b` of a root pairing `P`, an element `w` of the Weyl group *acts by* the integer matrix
`W` (`TauCeti.Coxeter.ActsBy b w W`) if `w • αⱼ = ∑ₖ W k j • αₖ` for every simple root `αⱼ`.
Acting-by is multiplicative, the simple reflection `sᵢ` acts by `reflMatrix b.cartanMatrix i`, and
when the roots span the weight space the action is faithful (no spanning hypothesis:
`TauCeti.Coxeter.eq_one_of_forall_smul_root_eq`), so the order of `w` is the order of `W`.

## Main results

* `TauCeti.Coxeter.actsBy_wordProd`: a word in the simple reflections acts by the product of the
  corresponding reflection matrices.
* `TauCeti.Coxeter.orderOf_eq_of_actsBy`: in a root system, `orderOf w = orderOf W`.
* `TauCeti.Coxeter.orderOf_wordProd_of_cartanMatrix_eq`: for a base whose Cartan matrix is `A` up to
  a relabelling `e`, the Coxeter element spelled in the order `e` has the order of
  `coxeterElement A`.
* `TauCeti.Coxeter.orderOf_coxeterElement_E8`, `…_E7`, `…_E6`, `…_F4`, `…_G2`: **the Coxeter
  number**.
* `TauCeti.Coxeter.charpoly_of_actsBy_wordProd`: its matrix on the simple roots has the
  characteristic polynomial of `coxeterElement A`; for `E₈` that is `Φ₃₀`
  (`TauCeti.Coxeter.charpoly_of_actsBy_coxeterElement_E8`).
-/

@[expose] public section

open Matrix RootPairing Submodule

namespace TauCeti.Coxeter

variable {ι R M N : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- The Weyl-group element `w` sends the simple root `αⱼ` of `b` to `∑ₖ W k j • αₖ`. -/
def ActsBy (b : P.Base) (w : P.weylGroup) (W : Matrix b.support b.support ℤ) : Prop :=
  ∀ j : b.support, w • P.root j = ∑ k, W k j • P.root k

omit [DecidableEq ι] in
/-- Weyl-group elements act additively, so they commute with integer multiples. -/
theorem smul_zsmul_comm (w : P.weylGroup) (n : ℤ) (x : M) : w • (n • x) = n • (w • x) :=
  smul_comm w n x

theorem actsBy_one (b : P.Base) : ActsBy b 1 1 := by
  intro j
  simp [Matrix.one_apply, ite_smul]

omit [DecidableEq ι] in
theorem ActsBy.mul {b : P.Base} {v w : P.weylGroup} {V W : Matrix b.support b.support ℤ}
    (hv : ActsBy b v V) (hw : ActsBy b w W) : ActsBy b (v * w) (V * W) := by
  intro j
  calc (v * w) • P.root j = v • (w • P.root j) := mul_smul v w _
    _ = v • ∑ k, W k j • P.root k := by rw [hw j]
    _ = ∑ k, W k j • (v • P.root k) := by
        rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun k _ => smul_zsmul_comm v _ _
    _ = ∑ k, W k j • ∑ l, V l k • P.root l := Finset.sum_congr rfl fun k _ => by rw [hv k]
    _ = ∑ l, (V * W) l j • P.root l := by
        simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem ActsBy.pow {b : P.Base} {w : P.weylGroup} {W : Matrix b.support b.support ℤ}
    (h : ActsBy b w W) (k : ℕ) : ActsBy b (w ^ k) (W ^ k) := by
  induction k with
  | zero => simpa using actsBy_one b
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem actsBy_ofIdx [P.IsCrystallographic] (b : P.Base) (i : b.support) :
    ActsBy b (weylGroup.ofIdx P i) (reflMatrix b.cartanMatrix i) := by
  intro j
  rw [weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply_root]
  simp only [reflMatrix, Matrix.of_apply, sub_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [← Int.cast_smul_eq_zsmul R (b.cartanMatrix j i)]
  congr 1
  rw [← P.algebraMap_pairingIn ℤ, algebraMap_int_eq, eq_intCast]
  rfl

variable [P.IsCrystallographic]

theorem actsBy_wordProd (b : P.Base) (l : List b.support) :
    ActsBy b (TauCeti.wordProd P b l) (l.map (reflMatrix b.cartanMatrix)).prod := by
  induction l with
  | nil => simpa [TauCeti.wordProd_nil] using actsBy_one b
  | cons i l ih =>
    simpa only [TauCeti.wordProd_cons, List.map_cons, List.prod_cons] using
      (actsBy_ofIdx b i).mul ih

omit [DecidableEq ι] in
/-- An element of the Weyl group fixing every root is trivial. No spanning hypothesis is needed:
`w • x - x` lies in the root span and pairs to zero with every coroot, and the root span meets
the kernel of the canonical form trivially. -/
theorem eq_one_of_forall_smul_root_eq [Finite ι] [IsDomain R] [CharZero R] {w : P.weylGroup}
    (hfix : ∀ i, w • P.root i = P.root i) : w = 1 := by
  have := Fintype.ofFinite ι
  have hidx : ∀ i, (w : P.Aut).indexEquiv i = i := fun i =>
    P.root.injective (by rw [Equiv.root_indexEquiv_eq_smul]; exact hfix i)
  have hcor : ∀ i x, P.coroot' i ((w : P.Aut) • x) = P.coroot' i x := fun i x => by
    have := Equiv.coroot'_weightEquiv (w : P.Aut) i x
    rw [hidx] at this
    exact this
  have hspan : ∀ g ∈ P.weylGroup, ∀ x : M, g • x - x ∈ P.rootSpan R := by
    intro g hg
    induction hg using weylGroup.induction with
    | mem i =>
      intro x
      rw [Equiv.reflection_smul, reflection_apply, sub_sub_cancel_left]
      exact neg_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    | one => intro x; simp
    | mul g h _ _ hg hh =>
      intro x
      rw [mul_smul, show g • h • x - x = (g • (h • x) - h • x) + (h • x - x) by abel]
      exact add_mem (hg _) (hh x)
  have hzero : ∀ x : M, (w : P.Aut) • x = x := by
    intro x
    have hker : (w : P.Aut) • x - x ∈ LinearMap.ker P.RootForm := by
      rw [LinearMap.mem_ker]
      ext z
      simp [rootForm_apply_apply, map_sub, hcor]
    exact sub_eq_zero.1
      (Submodule.disjoint_def.1 P.disjoint_rootSpan_ker_rootForm _ (hspan _ w.2 x) hker)
  refine Subtype.ext (Equiv.weightHom_injective P (LinearEquiv.ext fun x => ?_))
  change (w : P.Aut) • x = (1 : P.Aut) • x
  rw [one_smul]
  exact hzero x

/-- An element acting trivially on the simple roots is trivial. -/
theorem eq_one_of_actsBy_one [Finite ι] [IsDomain R] [CharZero R] {b : P.Base}
    {w : P.weylGroup}
    (h : ActsBy b w 1) : w = 1 := by
  have hfix : ∀ j : b.support, w • P.root j = P.root j := fun j => by
    simpa [Matrix.one_apply, ite_smul] using h j
  have hspan : ∀ x ∈ span ℤ (P.root '' b.support), w • x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨j, hj, rfl⟩ := hx; exact hfix ⟨j, hj⟩
    | zero => exact smul_zero w
    | add x y _ _ hx hy => rw [smul_add, hx, hy]
    | smul n x _ hx => rw [smul_zsmul_comm, hx]
  exact eq_one_of_forall_smul_root_eq fun i => hspan _ (b.root_mem_span_int i)

omit [DecidableEq ι] [P.IsCrystallographic] in
/-- The matrix by which an element acts is unique (simple roots are independent). -/
theorem eq_of_actsBy_of_actsBy [CharZero R] {b : P.Base} {w : P.weylGroup}
    {V W : Matrix b.support b.support ℤ} (hV : ActsBy b w V) (hW : ActsBy b w W) : V = W := by
  have hli : LinearIndependent ℤ (fun k : b.support => P.root k) :=
    b.linearIndepOn_root.restrict_scalars' ℤ
  ext k j
  have h0 : ∑ l, (V l j - W l j) • P.root l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← hV j, ← hW j, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 k)

theorem orderOf_eq_of_actsBy [CharZero R] [Finite ι] [IsDomain R] {b : P.Base}
    {w : P.weylGroup}
    {W : Matrix b.support b.support ℤ} (h : ActsBy b w W) : orderOf w = orderOf W := by
  refine orderOf_eq_orderOf_iff.2 fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · exact eq_of_actsBy_of_actsBy (h.pow k) (by simpa [hk] using actsBy_one b)
  · exact eq_one_of_actsBy_one (by simpa [hk] using h.pow k)

/-! ### Relabelling along a Dynkin numbering -/

theorem reflMatrix_submatrix {κ : Type*} [DecidableEq κ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (e : κ ≃ Fin n) (i : κ) :
    reflMatrix (A.submatrix e e) i = (reflMatrix A (e i)).submatrix e e := by
  ext k j
  simp [reflMatrix, e.injective.eq_iff]

/-- The product of the simple-reflection matrices of `b`, in the order `e`, is the Coxeter
element of `A`, relabelled. -/
theorem prod_reflMatrix_eq {n : ℕ} (b : P.Base) (A : Matrix (Fin n) (Fin n) ℤ)
    (e : b.support ≃ Fin n) (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) :
    (((List.finRange n).map e.symm).map (reflMatrix b.cartanMatrix)).prod =
      reindexAlgEquiv ℤ ℤ e.symm (coxeterElement A) := by
  have hC : b.cartanMatrix = A.submatrix e e := by ext i j; exact hA i j
  rw [hC, coxeterElement, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, reflMatrix_submatrix, Equiv.apply_symm_apply,
    coe_reindexAlgEquiv, reindex_apply, Equiv.symm_symm]

omit [DecidableEq ι] in
/-- **The Weyl-group Coxeter element has the order of the Coxeter element of its Cartan
matrix.** -/
theorem orderOf_wordProd_of_cartanMatrix_eq [CharZero R] [Finite ι] [IsDomain R] {n : ℕ}
    (b : P.Base)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : b.support ≃ Fin n)
    (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) :
    orderOf (TauCeti.wordProd P b ((List.finRange n).map e.symm)) = orderOf (coxeterElement A) := by
  classical
  rw [orderOf_eq_of_actsBy (actsBy_wordProd b _), prod_reflMatrix_eq b A e hA]
  exact orderOf_injective (reindexAlgEquiv ℤ ℤ e.symm).toRingEquiv.toMulEquiv.toMonoidHom
    (reindexAlgEquiv ℤ ℤ e.symm).injective _

/-! ### The Coxeter numbers of the exceptional types -/

omit [DecidableEq ι] in
/-- **The Coxeter number of `E₈` is 30**, for the Weyl group of any root system with a base of
type `E₈`. -/
theorem orderOf_coxeterElement_E8 [CharZero R] [Finite ι] [IsDomain R] (b : P.Base)
    (e : b.support ≃ Fin 8)
    (hA : ∀ i j, b.cartanMatrix i j = CartanMatrix.E 8 (e i) (e j)) :
    orderOf (TauCeti.wordProd P b ((List.finRange 8).map e.symm)) = 30 := by
  rw [orderOf_wordProd_of_cartanMatrix_eq b _ e hA]; exact orderOf_coxE8

omit [DecidableEq ι] in
theorem orderOf_coxeterElement_E7 [CharZero R] [Finite ι] [IsDomain R] (b : P.Base)
    (e : b.support ≃ Fin 7)
    (hA : ∀ i j, b.cartanMatrix i j = CartanMatrix.E 7 (e i) (e j)) :
    orderOf (TauCeti.wordProd P b ((List.finRange 7).map e.symm)) = 18 := by
  rw [orderOf_wordProd_of_cartanMatrix_eq b _ e hA]; exact orderOf_coxE7

omit [DecidableEq ι] in
theorem orderOf_coxeterElement_E6 [CharZero R] [Finite ι] [IsDomain R] (b : P.Base)
    (e : b.support ≃ Fin 6)
    (hA : ∀ i j, b.cartanMatrix i j = CartanMatrix.E 6 (e i) (e j)) :
    orderOf (TauCeti.wordProd P b ((List.finRange 6).map e.symm)) = 12 := by
  rw [orderOf_wordProd_of_cartanMatrix_eq b _ e hA]; exact orderOf_coxE6

omit [DecidableEq ι] in
theorem orderOf_coxeterElement_F4 [CharZero R] [Finite ι] [IsDomain R] (b : P.Base)
    (e : b.support ≃ Fin 4)
    (hA : ∀ i j, b.cartanMatrix i j = CartanMatrix.F₄ (e i) (e j)) :
    orderOf (TauCeti.wordProd P b ((List.finRange 4).map e.symm)) = 12 := by
  rw [orderOf_wordProd_of_cartanMatrix_eq b _ e hA]; exact orderOf_coxF4

omit [DecidableEq ι] in
theorem orderOf_coxeterElement_G2 [CharZero R] [Finite ι] [IsDomain R] (b : P.Base)
    (e : b.support ≃ Fin 2)
    (hA : ∀ i j, b.cartanMatrix i j = CartanMatrix.G₂ (e i) (e j)) :
    orderOf (TauCeti.wordProd P b ((List.finRange 2).map e.symm)) = 6 := by
  rw [orderOf_wordProd_of_cartanMatrix_eq b _ e hA]; exact orderOf_coxG2

/-- **The matrix of a Coxeter element on the simple roots has the characteristic polynomial of
the Coxeter element of its Cartan matrix.** -/
theorem charpoly_of_actsBy_wordProd [CharZero R] {n : ℕ} (b : P.Base)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : b.support ≃ Fin n)
    (hA : ∀ i j, b.cartanMatrix i j = A (e i) (e j)) {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (TauCeti.wordProd P b ((List.finRange n).map e.symm)) W) :
    W.charpoly = (coxeterElement A).charpoly := by
  rw [eq_of_actsBy_of_actsBy hW (actsBy_wordProd b _), prod_reflMatrix_eq b A e hA,
    coe_reindexAlgEquiv, charpoly_reindex]

/-- The matrix of the `E₈` Coxeter element on the simple roots has characteristic polynomial
`Φ₃₀`. -/
theorem charpoly_of_actsBy_coxeterElement_E8 [CharZero R] (b : P.Base) (e : b.support ≃ Fin 8)
    (hA : ∀ i j, b.cartanMatrix i j = CartanMatrix.E 8 (e i) (e j))
    {W : Matrix b.support b.support ℤ}
    (hW : ActsBy b (TauCeti.wordProd P b ((List.finRange 8).map e.symm)) W) :
    W.charpoly = Polynomial.cyclotomic 30 ℤ :=
  (charpoly_of_actsBy_wordProd b _ e hA hW).trans charpoly_coxE8

end TauCeti.Coxeter

end
