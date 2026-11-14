/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.Algebra.Ring.SquareZero
import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

/-!
# Determinants of finite-order linear maps

A finite-order endomorphism fixing a hyperplane pointwise and having determinant one is
the identity when its order is invertible in the field. The invertibility hypothesis
excludes modular transvections. This is the linear-algebra input for faithfulness of the
determinant character of a hyperplane's pointwise stabilizer in a finite linear group.

In rank two over a domain away from characteristic two, an involutive endomorphism of
determinant one need not be given a fixed hyperplane: adjugation forces it to be scalar,
so it is either `1` or `-1` (`LinearMap.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one`).

## References

* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.
-/

public section

namespace LinearMap

section Hyperplane

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A finite-order endomorphism fixing a hyperplane pointwise and having determinant one
is the identity, provided its order is invertible in the field. -/
theorem eq_one_of_det_eq_one_of_pow_eq_one (f : V →ₗ[K] V) (W : Submodule K V)
    (hW : Module.finrank K (V ⧸ W) = 1) (hfix : ∀ x ∈ W, f x = x)
    (hdet : f.det = 1) {n : ℕ} (hn : (n : K) ≠ 0) (hpow : f ^ n = 1) : f = 1 := by
  have hstable : W ≤ W.comap f := fun x hx ↦ by
    simpa only [Submodule.mem_comap, hfix x hx] using hx
  have hrestrict : f.restrict hstable = 1 := by
    ext x
    exact hfix x x.2
  obtain ⟨c, hc, -⟩ :=
    (W.mapQ W f hstable).existsUnique_eq_smul_id_of_finrank_eq_one hW
  have hc1 : c = 1 := by
    simpa [hrestrict, hc, det_smul, hW] using
      (f.det_eq_det_mul_det W hstable).symm.trans hdet
  have hquot : W.mapQ W f hstable = LinearMap.id := by simpa [hc1] using hc
  have hdiff (x : V) : (f - 1) x ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W).1
    have hx := congrArg (fun q ↦ q (Submodule.Quotient.mk x)) hquot
    rw [Submodule.mapQ_apply, LinearMap.id_apply] at hx
    simpa only [LinearMap.sub_apply, one_apply_eq_self, Submodule.Quotient.mk_sub]
      using sub_eq_zero.2 hx
  have hsq : (f - 1) ^ 2 = 0 := by
    ext x
    simpa [sq, mul_apply_eq_comp, sub_eq_zero] using hfix ((f - 1) x) (hdiff x)
  have hunit : IsUnit (n : Module.End K V) := by
    rw [← map_natCast (algebraMap K (Module.End K V))]
    exact hn.isUnit.map _
  exact sub_eq_zero.1 (TauCeti.eq_zero_of_one_add_pow_eq_one_of_sq_eq_zero hsq hunit
    (by simpa using hpow))

end Hyperplane

section RankTwo

variable {R M : Type*} [CommRing R] [NoZeroDivisors R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- **Every involutive endomorphism of determinant one on a rank-two free module over a domain
away from characteristic two is `1` or `-1`.** -/
theorem eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one (h2 : (2 : R) ≠ 0)
    (hdim : Module.finrank R M = 2) {f : M →ₗ[R] M} (hf : f * f = 1) (hdet : f.det = 1) :
    f = 1 ∨ f = -1 := by
  have : Nontrivial R := ⟨⟨2, 0, h2⟩⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  let b : Module.Basis (Fin 2) R M := Module.finBasisOfFinrankEq R M hdim
  have hmat : LinearMap.toMatrix b b f * LinearMap.toMatrix b b f = 1 := by
    rw [← LinearMap.toMatrix_mul, hf, LinearMap.toMatrix_one]
  have hdet' : (LinearMap.toMatrix b b f).det = 1 := by
    rwa [LinearMap.det_toMatrix]
  rcases Matrix.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one h2 hmat hdet' with h | h
  · exact Or.inl ((LinearMap.toMatrix b b).injective (h.trans (LinearMap.toMatrix_one b).symm))
  · exact Or.inr ((LinearMap.toMatrix b b).injective
      (h.trans (by rw [map_neg, LinearMap.toMatrix_one])))

/-- **Power form of `LinearMap.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one`.** -/
theorem eq_one_or_eq_neg_one_of_sq_eq_one_of_det_eq_one (h2 : (2 : R) ≠ 0)
    (hdim : Module.finrank R M = 2) {f : M →ₗ[R] M} (hf : f ^ 2 = 1) (hdet : f.det = 1) :
    f = 1 ∨ f = -1 :=
  eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one h2 hdim (by rwa [← sq]) hdet

end RankTwo

end LinearMap
