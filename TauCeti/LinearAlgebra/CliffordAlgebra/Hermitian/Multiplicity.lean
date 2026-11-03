/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex
public import TauCeti.Analysis.InnerProductSpace.Multiplicity
import TauCeti.RingTheory.Morita.ModuleEnd

/-!
# Hermitian forms on Clifford multiplicity spaces

Fix a finite-dimensional spinor space `S` on which the complexified Clifford algebra acts
as the full endomorphism algebra, with a compatible inner product. A compatible
sesquilinear form `H` on any module `E` determines a unique sesquilinear form `K` on
`Hom_Cl(S, E)` such that

`H (T s) (U t) = inner ℂ s t * K T U`.

The multiplicity form is obtained by evaluating intertwiners at any unit spinor;
the result is independent of that choice. If `H` is positive definite Hermitian, so is `K`.
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
