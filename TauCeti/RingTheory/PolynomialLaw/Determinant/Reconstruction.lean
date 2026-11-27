/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant
public import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.TensorProduct.Tower
import TauCeti.RingTheory.Nilpotent.Span
import TauCeti.RingTheory.Polynomial.Truncated.Basic

/-!
# Reconstruction of determinants from characteristic polynomials

Two determinants of the same degree agree as polynomial laws if their characteristic
polynomials agree on a set spanning the algebra as a module. In particular the polynomials
at the individual monoid elements determine a determinant on a monoid algebra, including
its mixed coefficients in positive characteristic.

At a nilpotent scalar `t`, the elements `1 + t • x` are products of elementary factors
from the spanning set. Applying this in every truncated polynomial ring gives equality
along the whole polynomial line through `1`. The analogous spanning-set argument for
matrix representations appears in `AlgHom.charpoly_coeff_mem_range_of_span`.

## References

* G. Chenevier, [*The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*](https://arxiv.org/abs/0809.0415),
  Lemma 1.12(ii) and Corollary 1.14.
* S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*,
  Linear and Multilinear Algebra **8** (1980), 177–182.
-/

public section

open TensorProduct Polynomial

namespace TauCeti.Determinant

universe u

variable {A : Type u} [CommRing A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}
  (D E : Determinant A R d) {s : Set R}

private theorem toFun_one_add_X_smul_eq
    (hs : Submodule.span A s = ⊤) (h : Set.EqOn D.charpoly E.charpoly s)
    {S : Type*} [CommSemiring S] [Algebra A S] (y : S[X] ⊗[A] R) :
    D.toLaw.toFun S[X] (1 + (X : S[X]) • y) = E.toLaw.toFun S[X] (1 + (X : S[X]) • y) := by
  let : CommRing S := (algebraMap A S).commSemiringToCommRing
  apply (TensorProduct.rid A S[X]).injective
  ext k
  refine (AdjoinRoot.mk_X_pow_eq_mk_iff (n := k + 1)).mp ?_ k k.lt_succ_self
  let T := AdjoinRoot (X ^ (k + 1) : S[X])
  let q : S[X] →ₐ[A] T := (AdjoinRoot.mkₐ (X ^ (k + 1) : S[X])).restrictScalars A
  let z := 1 + (X : S[X]) • y
  -- Modulo X^(k+1), multiplicativity extends agreement to the entire spanning module.
  have he : D.toLaw.toFun T (q.toLinearMap.rTensor R z) =
      E.toLaw.toFun T (q.toLinearMap.rTensor R z) := by
    have hq : q.toLinearMap.rTensor R z = 1 + AdjoinRoot.root (X ^ (k + 1) : S[X]) •
        q.toLinearMap.rTensor R y := by
      rw [map_add, AlgHom.rTensor_toLinearMap_apply_smul]
      simp [q, AdjoinRoot.mk_X, Algebra.TensorProduct.one_def]
    rw [hq]
    let F (L : Determinant A R d) : T ⊗[A] R →* T ⊗[A] A :=
      ⟨⟨L.toLaw.toFun T, L.isMultiplicative.toFun_one T⟩, L.isMultiplicative.toFun_mul⟩
    apply ((F D).eqLocusM (F E)).one_add_smul_mem_of_isNilpotent_of_span_eq_top
      (isNilpotent_root_X_pow (k + 1)) (s := TensorProduct.mk A T R 1 '' s)
      (by rw [← Submodule.baseChange_span, hs, Submodule.baseChange_top])
    rintro _ ⟨b, hb, rfl⟩ c
    refine MonoidHom.mem_eqLocusM.mpr ?_
    dsimp only [F, MonoidHom.coe_mk, OneHom.coe_mk, TensorProduct.mk_apply]
    rw [smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.one_def, add_comm (1 ⊗ₜ[A] (1 : R)),
      D.toFun_tmul_add_tmul_one, E.toFun_tmul_add_tmul_one]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i ≤ d := by simpa using hi
    have he := congrArg (fun p : A[X] ↦ p.coeff (d - i)) (h hb)
    simp only [coeff_charpoly, ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hi'] at he
    rw [(isUnit_neg_one.pow i).isRegular.left he]
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.isCompat_apply] at he
  simpa only [LinearMap.rid_rTensor_apply, AlgHom.toLinearMap_apply, q, z,
    AlgHom.restrictScalars_apply, AdjoinRoot.coe_mkₐ] using congrArg (TensorProduct.rid A T) he

/-- Two determinants with the same characteristic polynomials on a module-spanning set
are equal after every scalar extension. -/
theorem eq_of_charpoly_eq_of_span_eq_top
    (hs : Submodule.span A s = ⊤) (h : Set.EqOn D.charpoly E.charpoly s) : D = E := by
  ext S _ _ x
  let : Ring (S ⊗[A] R) := Algebra.semiringToRing A
  let Cₐ := IsScalarTower.toAlgHom A S S[X]
  let y := Cₐ.toLinearMap.rTensor R (x - 1)
  -- Evaluation at 1 sends 1 + X(x - 1) back to x.
  let ev := (aeval (R := S) (1 : S)).restrictScalars A
  have hcomp : ev.comp Cₐ = AlgHom.id A S := by ext a; simp [ev, Cₐ]
  have hev : ev.toLinearMap.rTensor R (1 + (X : S[X]) • y) = x := by
    simp only [y, map_add, Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, _root_.map_one, AlgHom.rTensor_toLinearMap_apply_smul,
      ← LinearMap.rTensor_comp_apply, ← AlgHom.comp_toLinearMap, hcomp]
    simp [ev]
  rw [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun'_eq_toFun, ← hev,
    ← PolynomialLaw.isCompat_apply, ← PolynomialLaw.isCompat_apply,
    D.toFun_one_add_X_smul_eq E hs h]

/-- A determinant on a monoid algebra is determined by its characteristic polynomials
at monoid elements, over any commutative coefficient ring. -/
theorem eq_of_charpoly_eq {G : Type*} [Monoid G] (D E : Determinant A (MonoidAlgebra A G) d)
    (h : ∀ g : G, D.charpoly (MonoidAlgebra.of A G g) = E.charpoly (MonoidAlgebra.of A G g)) :
    D = E := by
  apply D.eq_of_charpoly_eq_of_span_eq_top E (s := Set.range (MonoidAlgebra.of A G))
  · refine top_unique fun x _ ↦ Submodule.span_mono ?_ x.mem_span_support_coeff
    exact Set.image_subset_range _ _
  · rintro _ ⟨g, rfl⟩
    exact h g

end TauCeti.Determinant
