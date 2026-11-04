/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Pivotal
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Trace
public import Mathlib.LinearAlgebra.Trace

/-!
# Pivotal traces of finite-dimensional Hopf modules

For a group-like element `g` implementing the square of the antipode, the right categorical
trace of an intertwiner is its ordinary linear trace twisted by the action of `g`. The left
trace is twisted by the action of the inverse of `g`. These formulas compare the native
pivotal-category traces with linear algebra on the original module carriers.

The rigid and pivotal structures are selected explicitly in each statement, so the traces
use the inverse-antipode left duals and the double-dual comparison belonging to the same data.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Sections 4.7 and 4.8.
* C. Kassel, *Quantum Groups*, Chapter XIV.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]
variable (hS : Function.Bijective (HopfAlgebra.antipode k : H →ₗ[k] H))
  (g : GroupLike k H)
  (hg : ∀ a : H, HopfAlgebra.antipode k (HopfAlgebra.antipode k a) =
    (g : H) * a * HopfAlgebra.antipode k (g : H))

/-- The right pivotal trace is the ordinary trace of the intertwiner followed by the action
of the pivot, acting on the counit module by multiplication. -/
@[simp]
theorem rightTrace_apply {M : FiniteHopfModuleCat k H} (f : M ⟶ M)
    (c : (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) :
    letI := rigidCategory hS
    letI := pivotalCategory hS g hg
    (rightTrace f).hom.hom c =
      (trivialEquiv k H).symm
        (LinearMap.trace k M (Algebra.lsmul k k M (g : H) ∘ₗ
          f.hom.hom.restrictScalars k) * trivialEquiv k H c) := by
  let := rigidCategory hS
  let := pivotalCategory hS g hg
  classical
  rw [rightTrace_eq_pivotalIsoApp]
  simp only [hom_hom_comp, LinearMap.comp_apply]
  -- Name the dual vectors in the categorical carrier before using its tensor equations.
  let φ : Module.Basis.ofVectorSpaceIndex k M → ↑(Mᘁ : FiniteHopfModuleCat k H) :=
    fun i => (dualEquiv k H M).symm ((Module.Basis.ofVectorSpace k M).coord i)
  have hcoe : (η_ M Mᘁ).hom.hom c =
      ∑ i : Module.Basis.ofVectorSpaceIndex k M,
        (tmul k H (M := M) (N := (Mᘁ : FiniteHopfModuleCat k H))
          (trivialEquiv k H c • Module.Basis.ofVectorSpace k M i)
          (φ i) : ↑(M ⊗ Mᘁ)) := by
    rw [coevaluation_eq_dualCoevaluation, dualCoevaluation_hom_hom]
    exact dualCoeval_apply_eq_sum k H M c
  rw [hcoe]
  simp only [map_sum]
  rw [LinearMap.trace_eq_matrix_trace k (Module.Basis.ofVectorSpace k M), Matrix.trace]
  simp only [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [whiskerRight_tmul f, whiskerRight_tmul (pivotalIsoApp M).hom,
    evaluation_tmul, dualEquiv_pivotalIsoApp_hom_apply hS g hg]
  simp only [Module.Basis.coe_ofVectorSpace, LinearMap.map_smul_of_tower,
    Matrix.diag_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [smul_comm (g : H) (trivialEquiv k H c), map_smul]
  simp [φ, LinearMap.toMatrix_apply, mul_comm]

/-- The left pivotal trace is the ordinary trace twisted by the inverse pivot. For a
group-like element, its antipode is its inverse. -/
@[simp]
theorem leftTrace_apply {M : FiniteHopfModuleCat k H} (f : M ⟶ M)
    (c : (𝟙_ (FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H)) :
    letI := rigidCategory hS
    letI := pivotalCategory hS g hg
    (leftTrace f).hom.hom c =
      (trivialEquiv k H).symm
        (LinearMap.trace k M (Algebra.lsmul k k M (HopfAlgebra.antipode k (g : H)) ∘ₗ
          f.hom.hom.restrictScalars k) * trivialEquiv k H c) := by
  let := rigidCategory hS
  let := pivotalCategory hS g hg
  rw [← rightTrace_rightAdjointMate, rightTrace_apply hS g hg]
  congr 2
  -- The chosen right dual and the native linear dual have different scalar presentations.
  let e : (Mᘁ : FiniteHopfModuleCat k H) ≃ₗ[k] Module.Dual k M := dualEquiv k H M
  have heq : e.conj
      (Algebra.lsmul k k (Mᘁ : FiniteHopfModuleCat k H) (g : H) ∘ₗ
        (fᘁ).hom.hom.restrictScalars k) =
      Module.Dual.transpose (f.hom.hom.restrictScalars k ∘ₗ
        Algebra.lsmul k k M (HopfAlgebra.antipode k (g : H))) := by
    ext φ m
    simp only [LinearEquiv.conj_apply_apply, LinearMap.comp_apply,
      Algebra.lsmul_apply, LinearMap.coe_restrictScalars, Module.Dual.transpose_apply]
    have he (ψ : (Mᘁ : FiniteHopfModuleCat k H)) (x : M) :
        e ((g : H) • ψ) x = e ψ (HopfAlgebra.antipode k (g : H) • x) :=
      dualEquiv_smul_apply k H M (g : H) ψ x
    have hf (ψ : (Mᘁ : FiniteHopfModuleCat k H)) (x : M) :
        e ((fᘁ).hom.hom ψ) x = e ψ (f.hom.hom x) :=
      dualEquiv_rightAdjointMate_apply f ψ x
    rw [he, hf, LinearEquiv.apply_symm_apply]
  rw [← LinearMap.trace_conj' _ e, heq, LinearMap.trace_transpose',
    LinearMap.trace_comp_comm']

end TauCeti.FiniteHopfModuleCat
