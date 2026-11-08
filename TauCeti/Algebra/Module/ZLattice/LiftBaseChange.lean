/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.DFinsupp.FiniteInfinite
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Finitely generated abelian groups with injective real extension

Let `H` be a finitely generated abelian group and `l : H → E` an additive map into a real normed
space whose real extension `ℝ ⊗[ℤ] H → E`, `r ⊗ x ↦ r • l x`, is injective. Then `l` has finite
preimages of bounded sets (`LinearMap.finite_preimage_of_injective_liftBaseChange`). Under this
hypothesis the kernel of `l` is exactly the torsion subgroup of `H`, which is finite, and the
images of a basis of the free part are linearly independent over `ℝ`, so they span a discrete
subgroup of their real span.

The hypothesis cannot be weakened to injectivity of `l` itself: the map `ℤ² → ℝ`,
`(a, b) ↦ a + b √2`, is injective, but its image is dense, so the preimage of `[-1, 1]` is
infinite.

The typical instance is the period map of a compact manifold `X`: `H = H₂(X; ℤ)`, and `l` records
the integrals of finitely many closed forms whose de Rham classes span `H²(X; ℝ)`. By the de Rham
and universal coefficient theorems its real extension is injective. A bound on these integrals
then leaves only finitely many integral classes, including their torsion parts. This is the
finiteness step of Gromov compactness: integrals of a fixed form over a curve are bounded by the
comass of the form times the area of the curve.

## Main results

* `LinearIndependent.finite_setOf_sum_intCast_smul_mem`: only finitely many integer
  combinations of linearly independent vectors lie in a bounded set.
* `LinearMap.finite_preimage_of_injective_liftBaseChange`: the preimage of a bounded set is
  finite.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
-/

public section

open Module Submodule

namespace LinearIndependent

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Only finitely many integer combinations of finitely many linearly independent vectors of a
real normed space lie in a given bounded set. -/
theorem finite_setOf_sum_intCast_smul_mem {v : ι → E} (hv : LinearIndependent ℝ v) {s : Set E}
    (hs : Bornology.IsBounded s) : {a : ι → ℤ | ∑ i, (a i : ℝ) • v i ∈ s}.Finite := by
  classical
  -- Integer combinations of `v` lie in the lattice spanned by `v` in its real span.
  let b := Basis.span hv
  have : FiniteDimensional ℝ (span ℝ (Set.range v)) := Module.Finite.of_basis b
  let φ : (ι → ℤ) → span ℝ (Set.range v) := fun a => b.equivFun.symm fun i => (a i : ℝ)
  have hφ : Function.Injective φ :=
    b.equivFun.symm.injective.comp fun a a' h => funext fun i => by
      exact_mod_cast congrFun h i
  have hφv : ∀ a, (φ a : E) = ∑ i, (a i : ℝ) • v i := by
    intro a
    simp [φ, b, Basis.equivFun_symm_apply, Basis.span_apply]
  have hs' : Bornology.IsBounded (((↑) : span ℝ (Set.range v) → E) ⁻¹' s) :=
    isometry_subtype_coe.antilipschitzWith.isBounded_preimage hs
  refine ((ZSpan.setFinite_inter b hs').preimage hφ.injOn).subset fun a ha =>
    Set.mem_preimage.2 ⟨?_, ?_⟩
  · simpa [hφv] using ha
  · simp only [φ, Basis.equivFun_symm_apply, SetLike.mem_coe]
    exact sum_mem fun i _ => by
      rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (subset_span (Set.mem_range_self i)) _

end LinearIndependent

namespace LinearMap

variable {H E : Type*} [AddCommGroup H] [AddGroup.FG H] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finitely generated abelian group `H` mapped additively into a real normed space, with
injective real extension `ℝ ⊗[ℤ] H → E`, has finite preimages of bounded sets. -/
theorem finite_preimage_of_injective_liftBaseChange (l : H →ₗ[ℤ] E)
    (hl : Function.Injective (l.liftBaseChange ℝ)) {s : Set E} (hs : Bornology.IsBounded s) :
    (l ⁻¹' s).Finite := by
  classical
  obtain ⟨n, ι, _, p, hp, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod H
  have : ∀ i, NeZero (p i ^ k i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i => ZMod (p i ^ k i)) :=
    inferInstanceAs (Finite (Π₀ i, ZMod (p i ^ k i)))
  -- The free part `j : ℤⁿ → H` and the images `v` of its standard basis.
  let j : (Fin n →₀ ℤ) →ₗ[ℤ] H :=
    (e.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)).toIntLinearMap
  let v : Fin n → E := l ∘ j ∘ Finsupp.basisSingleOne
  -- The real extension of `l ∘ j` factors through that of `l`, along the base change of the
  -- injection `j`, which is injective since `ℝ` is flat over `ℤ`. So `v` is linearly independent.
  have hv : LinearIndependent ℝ v := by
    have hj : Function.Injective j := e.symm.injective.comp fun x y h => (Prod.mk.inj h).1
    have hfac : (l ∘ₗ j).liftBaseChange ℝ = l.liftBaseChange ℝ ∘ₗ j.baseChange ℝ := by
      ext; simp
    refine (liftBaseChange_injective_iff (l ∘ₗ j) Finsupp.basisSingleOne).1 ?_
    rw [hfac, LinearMap.coe_comp, LinearMap.baseChange_eq_lTensor]
    exact hl.comp (Module.Flat.lTensor_preserves_injective_linearMap j hj)
  -- The torsion part maps to zero, since `E` is torsion-free.
  have : HasUniqueDiv E := .of_isTorsionFree ℝ E
  have htors : ∀ t, l (e.symm (0, t)) = 0 := fun t =>
    (l.toAddMonoidHom.isOfFinAddOrder ((e.symm.toAddMonoidHom.comp
      (AddMonoidHom.inr _ _)).isOfFinAddOrder (isOfFinAddOrder_of_finite t))).eq_zero'
  -- So `l x` is the combination of `v` with the free coordinates of `x`.
  have hlx : ∀ x, l x = ∑ i, ((e x).1 i : ℝ) • v i := by
    intro x
    have hx : x = j (e x).1 + e.symm (0, (e x).2) := by
      simp [j, ← map_add]
    conv_lhs => rw [hx, map_add, htors, add_zero, ← (e x).1.univ_sum_single]
    simp only [map_sum, v, Function.comp_apply, Finsupp.coe_basisSingleOne,
      Int.cast_smul_eq_zsmul, ← map_zsmul, Finsupp.smul_single_one]
  -- An element of the preimage is determined by its free coordinates, of which there are finitely
  -- many choices, and its finitely many possible torsion parts.
  refine (((hv.finite_setOf_sum_intCast_smul_mem hs).prod Set.finite_univ).image
    fun y => e.symm (Finsupp.equivFunOnFinite.symm y.1, y.2)).subset fun x hx => ?_
  refine ⟨(⇑(e x).1, (e x).2), ⟨?_, Set.mem_univ _⟩, ?_⟩
  · simpa [hlx] using hx
  · simp

end LinearMap
