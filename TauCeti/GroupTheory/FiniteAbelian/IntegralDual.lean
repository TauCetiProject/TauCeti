/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Data.DFinsupp.FiniteInfinite
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# The integral basis of the dual of a finitely generated abelian group

Let `H` be a finitely generated abelian group and `K` a division ring of characteristic zero, such
as `ℝ`. The homomorphisms `H →+ K` form a finite-dimensional `K`-vector space, and the
integer-valued ones form a lattice in it: they are the `ℤ`-span of a `K`-basis
(`AddCommGroup.exists_basis_addMonoidHom`). The coordinates of `f : H →+ K` in this basis are
its values `f c₁, …, f c_n` at suitable elements `c₁, …, c_n` of `H`.

Torsion elements of `H` contribute nothing: a homomorphism into a torsion-free group is determined
by its values on the free part of a splitting `H ≃ ℤⁿ × T` with `T` finite
(`AddMonoidHom.apply_eq_sum_zsmul_of_addEquiv`). The basis vectors are the coordinate functionals
of the free part of `H`, read through the structure theorem
`AddCommGroup.equiv_free_prod_directSum_zmod`.

A typical instance is the first singular homology group `H = H₁(M; ℤ)` of a compact manifold. With
`K = ℝ`, the vector space `H →+ ℝ` is the first de Rham cohomology of `M`, and the integer-valued
homomorphisms are the classes with integral periods.
-/

public section

open Module Submodule

namespace AddMonoidHom

/-- **A homomorphism into a torsion-free group only sees the free part.** If
`e : H ≃+ (Fin n →₀ ℤ) × T` splits `H` into a free part and a finite group `T`, as in the structure
theorem `AddCommGroup.equiv_free_prod_directSum_zmod`, then a homomorphism `f` from `H` into an
abelian group without torsion is determined by its values on the elements
`e.symm (single i 1, 0)` of the free part. -/
theorem apply_eq_sum_zsmul_of_addEquiv {H T G : Type*} [AddCommGroup H] [AddCommGroup T] [Finite T]
    [AddCommGroup G] [HasUniqueDiv G] {n : ℕ} (e : H ≃+ (Fin n →₀ ℤ) × T) (f : H →+ G) (x : H) :
    f x = ∑ i, (e x).1 i • f (e.symm (Finsupp.single i 1, 0)) := by
  -- The torsion part of `x` is killed by `f`.
  have htors : f (e.symm (0, (e x).2)) = 0 :=
    (f.isOfFinAddOrder ((e.symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _)).isOfFinAddOrder
      (isOfFinAddOrder_of_finite (e x).2))).eq_zero'
  have hfree : e.symm ((e x).1, 0) = ∑ i, (e x).1 i • e.symm (Finsupp.single i 1, 0) := by
    apply e.injective
    simp only [AddEquiv.apply_symm_apply, map_sum, map_zsmul]
    ext1
    · simp only [Prod.fst_sum, Prod.smul_fst, Finsupp.smul_single, smul_eq_mul, mul_one]
      exact ((e x).1.univ_sum_single).symm
    · simp [Prod.snd_sum]
  have hx : x = e.symm ((e x).1, 0) + e.symm (0, (e x).2) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, AddEquiv.symm_apply_apply]
  conv_lhs => rw [hx, map_add, htors, add_zero, hfree, map_sum]
  simp

end AddMonoidHom

namespace AddCommGroup

variable (K H : Type*) [DivisionRing K] [CharZero K] [AddCommGroup H] [AddGroup.FG H]

/-- **The dual of a finitely generated abelian group in characteristic zero has an integral
basis.** For a finitely generated abelian group `H`, the `K`-vector space `H →+ K` has a
basis `b` whose coordinates are evaluations at elements `c i` of `H`, and whose `ℤ`-span is
exactly the set of integer-valued homomorphisms. -/
theorem exists_basis_addMonoidHom :
    ∃ (n : ℕ) (c : Fin n → H) (b : Basis (Fin n) K (H →+ K)),
      (∀ f i, b.repr f i = f (c i)) ∧
        ∀ f, f ∈ span ℤ (Set.range b) ↔ ∀ x, ∃ k : ℤ, f x = k := by
  classical
  obtain ⟨n, ι, _, p, hp, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod H
  have : ∀ i, NeZero (p i ^ k i) := fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i ↦ ZMod (p i ^ k i)) :=
    inferInstanceAs (Finite (Π₀ i, ZMod (p i ^ k i)))
  -- The free coordinates `q i` of `H` and the elements `c i` of the free part they are dual to.
  let q : Fin n → H →+ ℤ := fun i ↦
    (Finsupp.applyAddHom i).comp ((AddMonoidHom.fst _ _).comp e.toAddMonoidHom)
  let c : Fin n → H := fun i ↦ e.symm (Finsupp.single i 1, 0)
  have hqc (i j : Fin n) : q i (c j) = if j = i then 1 else 0 := by
    simp [q, c, Finsupp.single_apply]
  -- Every homomorphism into `K` is determined by its values on the `c i`.
  have hexp (f : H →+ K) (x : H) : f x = ∑ i, (q i x : K) * f (c i) := by
    simp [f.apply_eq_sum_zsmul_of_addEquiv e x, q, c, zsmul_eq_mul]
  -- Evaluation at the `c i` is a linear equivalence `(H →+ K) ≃ (Fin n → K)`.
  let L : (H →+ K) →ₗ[K] Fin n → K :=
    { toFun f i := f (c i)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hL : Function.Bijective L := by
    refine ⟨fun f g hfg ↦ AddMonoidHom.ext fun x ↦ ?_, fun t ↦ ?_⟩
    · rw [hexp f, hexp g]
      exact Finset.sum_congr rfl fun i _ ↦ congrArg _ (congrFun hfg i)
    · refine ⟨∑ i, t i • (Int.castAddHom K).comp (q i), funext fun j ↦ ?_⟩
      simp [L, hqc]
  let b : Basis (Fin n) K (H →+ K) := .ofEquivFun (.ofBijective L hL)
  have hrepr (f : H →+ K) (i : Fin n) : b.repr f i = f (c i) := Basis.ofEquivFun_repr_apply _ _ _
  refine ⟨n, c, b, hrepr, fun f ↦ ?_⟩
  rw [b.mem_span_iff_repr_mem ℤ]
  simp only [hrepr, algebraMap_int_eq, eq_intCast, Set.mem_range, eq_comm (b := f _)]
  refine ⟨fun h x ↦ ?_, fun h i ↦ h (c i)⟩
  choose m hm using h
  exact ⟨∑ i, q i x * m i, by simp [hexp f x, hm]⟩

end AddCommGroup
