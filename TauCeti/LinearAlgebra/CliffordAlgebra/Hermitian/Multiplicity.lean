/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.RingTheory.Morita.ModuleEnd

/-!
# The Hermitian metric on a Clifford multiplicity space

Let `S` be a nonzero finite-dimensional Hermitian Clifford module whose action is the full
endomorphism algebra, and let `E` be any Hermitian module with compatible real-vector actions.
The multiplicity space `Hom_Cl(S, E)` carries a positive definite Hermitian form characterized by

`⟪T s, U t⟫ = ⟪s, t⟫ multiplicityMetric T U`.

When the action on `S` is also faithful, the algebraic evaluation isomorphism
`S ⊗ Hom_Cl(S, E) ≃ E` identifies the metric of `E` with the product metric. In particular,
a compatible metric on a reducible module is controlled by its multiplicity metric, not by a
single rescaling of the spinor metric.

The construction evaluates at a chosen unit spinor, but the characterization proves independence
of this choice. No basis, dimension bound on `E`, or global inner product instance on the
multiplicity space is used. The zero module `E` is allowed. The nonzero hypothesis on `S`
permits the choice of a unit spinor.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open scoped TensorProduct ComplexOrder
open InnerProductSpace CliffordAlgebra

namespace TauCeti

variable {V S E : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [Nontrivial S]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

private def unitSpinor : S := by
  let := NormedSpace.restrictScalars ℝ ℂ S
  exact Classical.choose (exists_norm_eq S zero_le_one)

private theorem norm_unitSpinor : ‖unitSpinor (S := S)‖ = 1 := by
  let := NormedSpace.restrictScalars ℝ ℂ S
  exact Classical.choose_spec (exists_norm_eq S zero_le_one)

/-- The multiplicity metric evaluates intertwiners on a unit spinor. For compatible Clifford
modules with full action on `S`, `multiplicityMetric_apply_of_norm_eq_one` shows that any unit
spinor gives the same form. -/
def multiplicityMetric :
    (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ⋆[ℂ]
      (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ[ℂ] ℂ :=
  let ev := LinearMap.applyₗ' ℂ (R := CliffordAlgebra (Q.baseChange ℂ))
    (unitSpinor (S := S))
  ((innerₛₗ ℂ).comp ev).compl₂ ev

private theorem multiplicityMetric_apply (T U : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) :
    multiplicityMetric T U = inner ℂ (T (unitSpinor (S := S))) (U (unitSpinor (S := S))) :=
  (rfl)

/-- The multiplicity metric is Hermitian and nonnegative, even before imposing compatibility
of the Clifford actions. -/
theorem isPosSemidef_multiplicityMetric :
    (multiplicityMetric (Q := Q) (S := S) (E := E)).IsPosSemidef where
  eq T U := by simp only [multiplicityMetric_apply, inner_conj_symm]
  nonneg T := by simp [multiplicityMetric_apply]

/-- An isometric Clifford-module map induces an isometry of multiplicity metrics by
postcomposition. No compatibility or dimension hypothesis on the target modules is needed. -/
theorem _root_.LinearMap.cliffordMultiplicityMetric_comp {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) F]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) F]
    (g : E →ₗ[CliffordAlgebra (Q.baseChange ℂ)] F)
    (hg : ∀ x y, inner ℂ (g x) (g y) = inner ℂ x y)
    (T U : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) :
    multiplicityMetric (g.comp T) (g.comp U) = multiplicityMetric T U := by
  simpa only [multiplicityMetric_apply, LinearMap.comp_apply] using
    hg (T (unitSpinor (S := S))) (U (unitSpinor (S := S)))

/-- The multiplicity metric is positive definite when the spinor action is full, including
when `E` is zero. Neither metric compatibility nor finite-dimensionality is required. -/
@[simp]
theorem multiplicityMetric_self_eq_zero_iff
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]
    (hsurj : Function.Surjective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    (T : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) :
    multiplicityMetric T T = 0 ↔ T = 0 := by
  constructor
  · intro hT
    have hu : T (unitSpinor (S := S)) = 0 :=
      inner_self_eq_zero.mp ((multiplicityMetric_apply T T).symm.trans hT)
    ext s
    obtain ⟨a, ha⟩ := hsurj ((innerₛₗ ℂ (unitSpinor (S := S))).smulRight s)
    have has : a • unitSpinor (S := S) = s := by
      simpa only [Algebra.lsmul_coe, LinearMap.smulRight_apply, innerₛₗ_apply_apply,
        inner_self_eq_one_of_norm_eq_one norm_unitSpinor, one_smul] using
        congrArg (fun f : Module.End ℂ S => f (unitSpinor (S := S))) ha
    rw [← has, T.map_smul, hu, smul_zero, LinearMap.zero_apply]
  · rintro rfl
    simp

section Compatible

variable [FiniteDimensional ℂ S] [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]

variable
  (hsurj : Function.Surjective
    (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
  (hS : ∀ v : V,
    (Algebra.lsmul ℂ ℂ S (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
      -Algebra.lsmul ℂ ℂ S (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))
  (hE : ∀ (v : V) (x y : E),
    inner ℂ (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • x) y =
      -inner ℂ x (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • y))

include hsurj hS hE

omit [Nontrivial S] in
private theorem inner_map_map_eq_of_unit
    (T U : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)
    {u : S} (hu : ‖u‖ = 1) (s t : S) :
    inner ℂ (T s) (U t) = inner ℂ (T u) (U u) * inner ℂ s t := by
  let H : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ :=
    ((innerₛₗ ℂ).comp (T.restrictScalars ℂ)).compl₂ (U.restrictScalars ℂ)
  -- `H` is the mixed pullback form `(s,t) ↦ ⟪T s, U t⟫`.
  have hH (s t : S) : H s t = inner ℂ (T s) (U t) := rfl
  have hgen (v : V) (s t : S) :
      H (Algebra.lsmul ℂ ℂ S (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) s) t =
        -H s (Algebra.lsmul ℂ ℂ S (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) t) := by
    simpa only [hH, Algebra.lsmul_coe, T.map_smul, U.map_smul] using hE v (T s) (U t)
  have hadj (f : Module.End ℂ S) (s t : S) : H (f s) t = H s (f.adjoint t) := by
    obtain ⟨a, rfl⟩ := hsurj f
    rw [adjoint_map_eq_map_conjStar _ hS]
    exact sesqForm_map_eq_map_conjStar _ H hgen a s t
  exact H.eq_mul_inner_of_adjoint hadj hu s t

/-- Evaluation factors the Hermitian metric as the spinor metric times the multiplicity metric.
This is the metric comparison for the Morita evaluation isomorphism. -/
theorem inner_map_map_eq_multiplicityMetric
    (T U : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) (s t : S) :
    inner ℂ (T s) (U t) = inner ℂ s t * multiplicityMetric T U := by
  rw [multiplicityMetric_apply, mul_comm]
  exact inner_map_map_eq_of_unit hsurj hS hE T U norm_unitSpinor s t

/-- The multiplicity metric can be evaluated at any unit spinor, independently of the unit
spinor used in its construction. -/
theorem multiplicityMetric_apply_of_norm_eq_one
    (T U : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) {u : S} (hu : ‖u‖ = 1) :
    multiplicityMetric T U = inner ℂ (T u) (U u) := by
  rw [inner_map_map_eq_multiplicityMetric hsurj hS hE,
    inner_self_eq_one_of_norm_eq_one hu, one_mul]

/-- The product-metric equation uniquely determines the multiplicity metric. -/
theorem multiplicityMetric_eq_iff
    (H : (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ⋆[ℂ]
      (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ[ℂ] ℂ) :
    H = multiplicityMetric ↔ ∀ T U s t,
      inner ℂ (T s) (U t) = inner ℂ s t * H T U := by
  constructor
  · rintro rfl
    exact inner_map_map_eq_multiplicityMetric hsurj hS hE
  · intro hH
    ext T U
    have h := hH T U (unitSpinor (S := S)) (unitSpinor (S := S))
    simpa only [inner_self_eq_one_of_norm_eq_one norm_unitSpinor, one_mul,
      multiplicityMetric_apply] using h.symm

omit hsurj in
/-- The algebraic evaluation isomorphism preserves the product Hermitian metric. This version
uses a sesquilinear form characterized on pure tensors, so no auxiliary norm or inner product
instance on the multiplicity space is required. -/
theorem inner_isotypicTensorEquivOfBijective_eq
    (h : Function.Bijective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    (H : S ⊗[ℂ] (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ⋆[ℂ]
      S ⊗[ℂ] (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ[ℂ] ℂ)
    (hH : ∀ s t T U, H (s ⊗ₜ T) (t ⊗ₜ U) = inner ℂ s t * multiplicityMetric T U)
    (x y : S ⊗[ℂ] (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E)) :
    inner ℂ (isotypicTensorEquivOfBijective h x) (isotypicTensorEquivOfBijective h y) =
      H x y := by
  induction x with
  | tmul s T =>
    induction y with
    | tmul t U =>
      rw [hH, isotypicTensorEquivOfBijective_apply, isotypicTensorEquivOfBijective_apply,
        isotypicEval_tmul, isotypicEval_tmul]
      exact inner_map_map_eq_multiplicityMetric h.surjective hS hE T U s t
    | add y z hy hz => rw [map_add, inner_add_right, hy, hz, map_add]
  | add x z hx hz => rw [map_add, inner_add_left, hx, hz, map_add, LinearMap.add_apply]

end Compatible

end TauCeti
