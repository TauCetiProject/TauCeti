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

* `LinearMap.finite_preimage_of_injective_liftBaseChange`: the preimage of a bounded set is
  finite.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
-/

public section

open Module Submodule

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
  -- split injection `j`, so it is injective and `v` is linearly independent.
  have hv : LinearIndependent ℝ v := by
    let q : H →ₗ[ℤ] Fin n →₀ ℤ :=
      ((AddMonoidHom.fst _ _).comp e.toAddMonoidHom).toIntLinearMap
    have hqj : q ∘ₗ j = LinearMap.id := by ext; simp [q, j]
    have hfac : (l ∘ₗ j).liftBaseChange ℝ = l.liftBaseChange ℝ ∘ₗ j.baseChange ℝ := by
      ext; simp
    have hinj : Function.Injective (j.baseChange ℝ) := by
      refine Function.LeftInverse.injective (g := q.baseChange ℝ) fun x => ?_
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hqj, LinearMap.baseChange_id,
        LinearMap.id_apply]
    refine (liftBaseChange_injective_iff (l ∘ₗ j) Finsupp.basisSingleOne).1 ?_
    rw [hfac]
    exact hl.comp hinj
  -- The torsion part maps to zero.
  have htors : ∀ t, l (e.symm (0, t)) = 0 := fun t => by
    obtain ⟨N, hN, hNt⟩ := (isOfFinAddOrder_of_finite t).exists_nsmul_eq_zero
    have h : (N : ℝ) • l (e.symm (0, t)) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← map_nsmul, Prod.smul_mk, smul_zero, hNt,
        Prod.mk_zero_zero, map_zero, map_zero]
    exact (smul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hN.ne')
  -- So `l x` is the combination of `v` with the free coordinates of `x`.
  have hlx : ∀ x, l x = ∑ i, ((e x).1 i : ℝ) • v i := by
    intro x
    have hx : x = j (e x).1 + e.symm (0, (e x).2) := by
      simp [j, ← map_add]
    conv_lhs => rw [hx, map_add, htors, add_zero, ← (e x).1.univ_sum_single]
    simp only [map_sum, v, Function.comp_apply, Finsupp.coe_basisSingleOne,
      Int.cast_smul_eq_zsmul, ← map_zsmul, Finsupp.smul_single_one]
  -- Integer combinations of `v` lie in the lattice spanned by `v` in its real span.
  let b := Basis.span hv
  have : FiniteDimensional ℝ (span ℝ (Set.range v)) := Module.Finite.of_basis b
  let φ : (Fin n → ℤ) → span ℝ (Set.range v) := fun a => b.equivFun.symm fun i => (a i : ℝ)
  have hφ : Function.Injective φ :=
    b.equivFun.symm.injective.comp fun a a' h => funext fun i => by
      exact_mod_cast congrFun h i
  have hφv : ∀ a, (φ a : E) = ∑ i, (a i : ℝ) • v i := by
    intro a
    simp [φ, b, Basis.equivFun_symm_apply, Basis.span_apply]
  have hs' : Bornology.IsBounded (((↑) : span ℝ (Set.range v) → E) ⁻¹' s) :=
    isometry_subtype_coe.antilipschitzWith.isBounded_preimage hs
  have hfin : {a : Fin n → ℤ | ∑ i, (a i : ℝ) • v i ∈ s}.Finite := by
    have h := (ZSpan.setFinite_inter b hs').preimage hφ.injOn
    refine h.subset fun a ha => Set.mem_preimage.2 ⟨?_, ?_⟩
    · simpa [hφv] using ha
    · simp only [φ, Basis.equivFun_symm_apply, SetLike.mem_coe]
      exact sum_mem fun i _ => by
        rw [Int.cast_smul_eq_zsmul]
        exact zsmul_mem (subset_span (Set.mem_range_self i)) _
  -- An element of the preimage is determined by its free coordinates in `hfin` and its finitely
  -- many possible torsion parts.
  refine ((hfin.prod Set.finite_univ).image
    fun y => e.symm (Finsupp.equivFunOnFinite.symm y.1, y.2)).subset fun x hx => ?_
  refine ⟨(⇑(e x).1, (e x).2), ⟨?_, Set.mem_univ _⟩, ?_⟩
  · simpa [hlx] using hx
  · simp

end LinearMap
