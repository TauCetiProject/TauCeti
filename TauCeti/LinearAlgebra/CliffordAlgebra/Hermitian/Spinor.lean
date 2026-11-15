/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
-- Private: the Fock model, its metric, the complex structure on `V`, anisotropy, the parity of the
-- dimension of `V` and the inner automorphisms of endomorphism algebras are used only inside the
-- proof.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.RepresentationTheory.Spin.Polarization.Fock.Metric

/-!
# Compatible Hermitian metrics on spinor modules

Let `V` be a Euclidean space and `Q v = -‖v‖²`, the geometric sign convention under which
Clifford multiplication satisfies `c(v)² = -‖v‖²`. A spinor module of `V` is a complex vector space
`S` with an algebra isomorphism `ρ : Cl_ℂ(V) ≃ End_ℂ(S)` from the complexified Clifford algebra;
one exists only in even dimension, since comparing dimensions gives `2 ^ dim V = (dim S)²`. This
file proves that `S` carries a **positive definite Hermitian form `H` for
which `ρ` is a `*`-representation**:

  `H (ρ a x) y = H x (ρ (a^*) y)`,

where `a^*` is the conjugate-linear Clifford involution `CliffordAlgebra.conjStar`. Equivalently,
Clifford multiplication by a real vector is skew-Hermitian.

The metric is transported from the Fock model. An orthogonal complex structure `J` on `V` gives
the normalized Fock action of the complexified Clifford algebra on `⋀ W`, which is an algebra
isomorphism onto `End(⋀ W)` and a `*`-representation for the exterior Gram metric of an
orthonormal basis of `W`. The composite `End(⋀ W) ≃ Cl_ℂ(V) ≃ End(S)` is an isomorphism of
endomorphism algebras, hence conjugation by a linear isomorphism `T : ⋀ W ≃ S`, which therefore
intertwines the two actions; `H` is the Fock metric read through `T⁻¹`.

By `CliffordAlgebra.existsUnique_pos_mul_of_surjective` the metric is unique up to a positive
real scalar.

## Main results

* `CliffordAlgebra.exists_sesqForm_map_eq_map_conjStar`: every spinor module of an
  even-dimensional Euclidean space carries a positive definite Hermitian form making it a
  `*`-representation of the complexified Clifford algebra.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} [AddCommGroup S] [Module ℂ S]

open scoped ComplexOrder in
/-- **Spinor modules carry compatible positive Hermitian metrics.** For a Euclidean space with
`Q v = -‖v‖²` and an algebra isomorphism `ρ` from the complexified Clifford algebra onto the
endomorphisms of `S`, there is a positive definite Hermitian form `H` on `S` with
`H (ρ a x) y = H x (ρ (conjStar Q a) y)` for every `a`.

The form is unique up to a positive real scalar
(`CliffordAlgebra.existsUnique_pos_mul_of_surjective`). No parity hypothesis is needed: `ρ` forces
`V` to have even dimension (`CliffordAlgebra.even_finrank_of_algEquiv_end`). Dimension zero, where
`S` is a line, is included. -/
theorem exists_sesqForm_map_eq_map_conjStar (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S) :
    ∃ H : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ, H.IsPosSemidef ∧ (∀ x, x ≠ 0 → H x x ≠ 0) ∧
      ∀ a x y, H (ρ a x) y = H x (ρ (conjStar Q a) y) := by
  obtain ⟨ℓ, hℓ⟩ : Even (finrank ℝ V) := by
    simpa [finrank_baseChange] using even_finrank_of_algEquiv_end (Q.baseChange ℂ) ρ
  -- The Fock model of an orthogonal complex structure, with an orthonormal basis of `W`.
  obtain ⟨J, hJ⟩ := TauCeti.AlmostComplexStructure.exists_forall_norm_apply_eq (V := V) ⟨ℓ, hℓ⟩
  have hQJ (v : V) : Q (J v) = Q v := by rw [hQ, hQ, hJ]
  have hQnd : Q.Nondegenerate := QuadraticMap.Anisotropic.nondegenerate fun v hv ↦ by
    simpa [hQ] using hv
  obtain ⟨b, hb⟩ := J.exists_basis_polar_tmulConj hQJ hQnd hQ ℓ (by omega)
  let ρF := AlgEquiv.ofBijective (J.fockAction hQJ hQnd) (J.fockAction_bijective hQJ hQnd)
  -- An intertwiner `T` from the Fock module to `S`.
  obtain ⟨T, hT⟩ := (ρF.symm.trans ρ).eq_linearEquivConjAlgEquiv
  have hρ (a : CliffordAlgebra (Q.baseChange ℂ)) (x : S) :
      T.symm (ρ a x) = J.fockAction hQJ hQnd a (T.symm x) := by
    have h := congr($hT (ρF a) x)
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, LinearEquiv.conjAlgEquiv_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe] at h
    rw [h, LinearEquiv.symm_apply_apply, AlgEquiv.ofBijective_apply]
  -- The Fock metric, read through `T⁻¹`.
  let G := Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ) b.ExteriorAlgebra b.ExteriorAlgebra
    (1 : Matrix (Finset (Fin ℓ)) (Finset (Fin ℓ)) ℂ)
  refine ⟨(G.comp T.symm.toLinearMap).compl₂ T.symm.toLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, fun x hx ↦ ?_, fun a x y ↦ ?_⟩
  all_goals simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  · exact Matrix.star_toLinearMapₛₗ₂_one_apply b.ExteriorAlgebra (T.symm x) (T.symm y)
  · exact Matrix.toLinearMapₛₗ₂_one_self_nonneg b.ExteriorAlgebra (T.symm x)
  · rw [Ne, Matrix.toLinearMapₛₗ₂_one_self_eq_zero_iff, LinearEquiv.map_eq_zero_iff]
    exact hx
  · simp only [hρ]
    exact J.toLinearMapₛₗ₂_fockAction_left hQJ hQnd b hb a _ _

end CliffordAlgebra
