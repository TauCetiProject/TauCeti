/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.Analysis.InnerProductSpace.Multiplicity
public import TauCeti.RingTheory.Morita.ModuleEnd

/-!
# Hermitian forms on Clifford multiplicity spaces

Fix a finite-dimensional spinor space `S` on which the complexified Clifford algebra acts
as the full endomorphism algebra, with a compatible inner product. A compatible
sesquilinear form `H` on any module `E` determines a unique sesquilinear form `K` on
`Hom_Cl(S, E)` such that

`H (T s) (U t) = inner ℂ s t * K T U`.

The multiplicity form is obtained by evaluating intertwiners at any unit spinor;
the result is independent of that choice. If `H` is positive definite Hermitian, so is `K`.
When `E` has an inner product, `TauCeti.multiplicityMetric` gives this form explicitly.
When the action is an algebra isomorphism, Morita evaluation `S ⊗ Hom_Cl(S, E) ≃ E`
factors the metric into the spinor metric and the multiplicity metric. Compatible forms
on `E` are then determined by their multiplicity forms, not in general by a single scalar.

Conversely, when the action on `S` is an algebra isomorphism, every positive definite
Hermitian multiplicity form gives a unique compatible form on `E`. No finite-dimensionality
or topology on `E` is needed, and the zero module is included.
The adjoint used here is the conjugate-linear `CliffordAlgebra.conjStar`, not the native
complex-linear Clifford star.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open scoped TensorProduct ComplexOrder

namespace CliffordAlgebra

variable {V S E : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]
  [AddCommGroup E] [Module ℂ E] [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

variable
  (hsurj : Function.Surjective
    (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
  (hS : ∀ v : V,
    (Algebra.lsmul ℂ ℂ S (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
      -Algebra.lsmul ℂ ℂ S (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))
  (H : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)
  (hH : ∀ (v : V) x y,
    H (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • x) y =
      -H x (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • y))

include hsurj hS hH

/-- The pairing of two Clifford intertwiners factors through the spinor inner product.
Its scalar coefficient can be computed at any unit spinor. Symmetry and positivity of `H`
are not required. -/
theorem sesqForm_apply_intertwiners
    {u : S} (hu : ‖u‖ = 1)
    (T U : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) (s t : S) :
    H (T s) (U t) = inner ℂ s t * H (T u) (U u) := by
  let G := (H.comp (T.restrictScalars ℂ)).compl₂ (U.restrictScalars ℂ)
  have hG (A : Module.End ℂ S) (x y : S) : G (A x) y = G x (A.adjoint y) := by
    obtain ⟨a, rfl⟩ := hsurj A
    rw [adjoint_map_eq_map_conjStar (Algebra.lsmul ℂ ℂ S) hS]
    simp only [G, LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, Algebra.lsmul_coe, T.map_smul, U.map_smul]
    exact sesqForm_map_eq_map_conjStar (Algebra.lsmul ℂ ℂ E) H hH a (T x) (U y)
  simpa only [G, LinearMap.compl₂_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, mul_comm] using G.eq_mul_inner_of_adjoint hG hu s t

/-- Every compatible sesquilinear form induces a unique form on the multiplicity space.
The displayed equation characterizes it without choosing a basis or a unit spinor. -/
theorem existsUnique_multiplicity_sesqForm [Nontrivial S] :
    ∃! K : (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ⋆[ℂ]
        (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ[ℂ] ℂ,
      ∀ T U s t, H (T s) (U t) = inner ℂ s t * K T U := by
  let := NormedSpace.restrictScalars ℝ ℂ S
  obtain ⟨u, hu⟩ := exists_norm_eq S zero_le_one
  let ev : (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ[ℂ] E :=
    LinearMap.applyₗ' ℂ u
  let K := (H.comp ev).compl₂ ev
  refine ⟨K, fun T U s t ↦ sesqForm_apply_intertwiners hsurj hS H hH hu T U s t, ?_⟩
  intro L hL
  ext T U
  have h := hL T U u u
  rw [inner_self_eq_one_of_norm_eq_one hu, one_mul] at h
  exact h.symm

/-- Positive definite compatible Hermitian forms induce positive definite Hermitian
multiplicity forms, including when the multiplicity space is zero. -/
theorem existsUnique_posDef_multiplicity_sesqForm [Nontrivial S]
    (hpos : H.IsPosSemidef) (hdef : ∀ x, x ≠ 0 → H x x ≠ 0) :
    ∃! K : (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ⋆[ℂ]
        (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ[ℂ] ℂ,
      (∀ T U s t, H (T s) (U t) = inner ℂ s t * K T U) ∧
        K.IsPosSemidef ∧ (∀ T, T ≠ 0 → K T T ≠ 0) := by
  obtain ⟨K, hK, huniq⟩ := existsUnique_multiplicity_sesqForm hsurj hS H hH
  let := NormedSpace.restrictScalars ℝ ℂ S
  obtain ⟨u, hu⟩ := exists_norm_eq S zero_le_one
  have heval (T U) : K T U = H (T u) (U u) := by
    simpa only [inner_self_eq_one_of_norm_eq_one hu, one_mul] using (hK T U u u).symm
  refine ⟨K, ⟨hK, ⟨⟨fun T U ↦ ?_⟩, ⟨fun T ↦ ?_⟩⟩, ?_⟩, fun L hL ↦ huniq L hL.1⟩
  · simp only [heval]
    exact hpos.isSymm.eq _ _
  · rw [heval]
    exact hpos.isNonneg.nonneg _
  · intro T hT hzero
    apply hT
    ext s
    by_contra hs
    exact hdef (T s) hs (by rw [hK, hzero, mul_zero])

omit hsurj hH in
/-- A positive definite Hermitian multiplicity form gives a positive definite compatible
Hermitian form on the entire module. Together with the uniqueness theorem this classifies
compatible metrics by metrics on the multiplicity space, rather than by scalar rescaling. -/
theorem existsUnique_posDef_sesqForm_of_multiplicity
    (hbij : Function.Bijective
      (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))
    (K : (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ⋆[ℂ]
      (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) →ₗ[ℂ] ℂ)
    (hpos : K.IsPosSemidef) (hdef : ∀ T, T ≠ 0 → K T T ≠ 0) :
    ∃! H : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ,
      (∀ T U s t, H (T s) (U t) = inner ℂ s t * K T U) ∧
        H.IsPosSemidef ∧ (∀ x, x ≠ 0 → H x x ≠ 0) ∧
        ∀ (v : V) x y, H (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • x) y =
          -H x (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • y) := by
  obtain ⟨H, ⟨hfactor, hHpos, hHdef⟩, huniq⟩ :=
    TauCeti.existsUnique_posDef_sesqForm_of_bijective_lsmul hbij K hpos hdef
  let b := stdOrthonormalBasis ℂ S
  let c := fun i ↦ TauCeti.homOfDual hbij (b.toBasis.coord i) (M := E)
  have hdecomp (x : E) : ∑ i, c i x (b i) = x :=
    TauCeti.sum_homOfDual_coord_apply hbij b.toBasis x
  refine ⟨H, ⟨hfactor, hHpos, hHdef, fun v x y ↦ ?_⟩,
    fun L hL ↦ huniq L ⟨hL.1, hL.2.1, hL.2.2.1⟩⟩
  let a := ι (Q.baseChange ℂ) (1 ⊗ₜ v)
  have hinner (s t : S) : inner ℂ (a • s) t = -inner ℂ s (a • t) := by
    have hi := LinearMap.adjoint_inner_right (Algebra.lsmul ℂ ℂ S a) s t
    rw [hS v] at hi
    simpa using hi.symm
  dsimp only [a] at hinner
  conv_lhs => rw [← hdecomp x, ← hdecomp y]
  conv_rhs => rw [← hdecomp x, ← hdecomp y]
  simp only [Finset.smul_sum, map_sum, LinearMap.sum_apply, ← LinearMap.map_smul, hfactor,
    hinner, neg_mul, Finset.sum_neg_distrib]

end CliffordAlgebra

noncomputable section

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

/-- Evaluation factors the Hermitian metric as the spinor metric times the multiplicity metric.
This is the metric comparison for the Morita evaluation isomorphism. -/
theorem inner_map_map_eq_multiplicityMetric
    (T U : S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) (s t : S) :
    inner ℂ (T s) (U t) = inner ℂ s t * multiplicityMetric T U := by
  rw [multiplicityMetric_apply]
  exact sesqForm_apply_intertwiners hsurj hS (innerₛₗ ℂ) hE norm_unitSpinor T U s t

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
