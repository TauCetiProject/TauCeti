/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Reflection
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.FinTwo
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Generation

/-!
# Geometric connectedness of the special orthogonal groups

The coordinate Hopf algebra of the standard group `SOₙ` is geometrically connected in every
dimension away from characteristic two, and in dimension two over every field. Connectedness is
tested by
idempotents: over an algebraically closed extension an idempotent regular function is constant
once right translation by every rational point fixes it, and a rational point which is joined to
the identity by a path (a point over a domain specializing to it at one parameter and to the
identity at another) translates every idempotent to itself.

In every dimension, away from characteristic two, the paths come from reflections. Cartan-Dieudonné
writes a special orthogonal matrix as a product of pairs of reflections, and the points fixing a
given idempotent form a subgroup, so it is enough to join each product of two reflections to the
identity. Reflecting in a fixed anisotropic vector `v` and then in a vector moving along a
Laurent-polynomial family through the plane spanned by `v` and `w` does exactly that, by
`TauCeti.exists_laurentPath_reflectionMatrix_mul`.

Rank two is treated separately because that argument needs an invertible two, while the
determinant-one model of `SO₂` is geometrically connected over every field. Away from
characteristic two, after extending to an algebraically closed field, the explicit equivalence
`SO₂(K) ≃* Kˣ` writes every rational point on a Laurent-polynomial path from the identity; in
characteristic two, every rational point lies on the affine-line path of matrices
`!![1 + tb, tb; -tb, 1 + tb]`. That model is nonreduced in characteristic two, but its underlying
space is still connected.

## Main declarations

* `TauCeti.SpecialOrthogonal.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two`:
  `SO₂` is geometrically connected over every field.
* `TauCeti.SpecialOrthogonal.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  `SOₙ` is geometrically connected in every dimension over a field of characteristic different
  from two.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.3, 2.a and 18.c.
* T. A. Springer, *Linear Algebraic Groups*, §2.2.
-/

public section

open CategoryTheory WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.SpecialOrthogonal

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local instance : IsScalarTower k K (LaurentPolynomial K) :=
  IsScalarTower.of_algebraMap_eq (by simp)

/-- Base-changed `SOₙ` points identified with special orthogonal matrices. -/
private def baseChangePointsMulEquiv (n : ℕ)
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    WithConv (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] A) ≃*
      Matrix.specialOrthogonalGroup (Fin n) A :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
    (A := coordinateHopfAlgebra k n) (R := A)).symm.trans
      (pointsMulEquiv k n (A := A))

private theorem baseChangePointsMulEquiv_mapValue (n : ℕ)
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    [Algebra k B] [Algebra K B] [IsScalarTower k K B]
    (phi : A →ₐ[K] B) (f : WithConv (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] A)) :
    baseChangePointsMulEquiv (k := k) (K := K) n B
        (AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k n) phi f) =
      Matrix.SpecialOrthogonalGroup.map phi.toRingHom
        (baseChangePointsMulEquiv (k := k) (K := K) n A f) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply,
    AlgHom.baseChangePointsMulEquiv_symm_mapValue,
    baseChangePointsMulEquiv, MulEquiv.trans_apply]
  exact pointsMulEquiv_mapValue (R := k) (n := n) (phi.restrictScalars k) _

/-- The Laurent-polynomial path in `SO₂` attached to the generic unit. -/
private def laurentPath (i half : K) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1) :
    WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] LaurentPolynomial K) :=
  (baseChangePointsMulEquiv (k := k) (K := K) 2 (LaurentPolynomial K)).symm
    (Matrix.SpecialOrthogonalGroup.finTwoOfUnit
      (LaurentPolynomial.C i) (LaurentPolynomial.C half)
      (by simpa only [map_pow, map_neg, map_one] using
        congrArg LaurentPolynomial.C hi)
      (by simpa only [map_ofNat, map_mul, map_one] using
        congrArg LaurentPolynomial.C hhalf)
      (MultiplicativeGroup.genericUnit K))

private theorem mapValue_laurentPath
    (i half : K) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1) (u : Kˣ) :
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k 2)
        (MultiplicativeGroup.point u) (laurentPath (k := k) i half hi hhalf) =
      (baseChangePointsMulEquiv (k := k) (K := K) 2 K).symm
        (Matrix.SpecialOrthogonalGroup.finTwoOfUnit i half hi hhalf u) := by
  apply (baseChangePointsMulEquiv (k := k) (K := K) 2 K).injective
  rw [baseChangePointsMulEquiv_mapValue]
  simp only [laurentPath, MulEquiv.apply_symm_apply]
  rw [Matrix.SpecialOrthogonalGroup.map_finTwoOfUnit]
  have hu : Units.map (MultiplicativeGroup.point u).toRingHom.toMonoidHom
      (MultiplicativeGroup.genericUnit K) = u := by
    apply Units.ext
    simp
  apply Subtype.ext
  rw [Matrix.SpecialOrthogonalGroup.coe_finTwoOfUnit,
    Matrix.SpecialOrthogonalGroup.coe_finTwoOfUnit]
  ext j k
  fin_cases j
  · fin_cases k <;> norm_num [Matrix.of_apply, hu, MultiplicativeGroup.point_C]
  · fin_cases k <;> norm_num [Matrix.of_apply, hu, MultiplicativeGroup.point_C]

/-- The characteristic-two affine-line path with parameter `b`. -/
private noncomputable def charTwoMatrixPath (b : K) (h2 : (2 : K) = 0) :
    Matrix.specialOrthogonalGroup (Fin 2) (Polynomial K) := by
  let _ : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  let t : Polynomial K := Polynomial.X * Polynomial.C b
  refine ⟨!![1 + t, t; -t, 1 + t], ?_⟩
  rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  refine ⟨rfl, (neg_neg t).symm, ?_⟩
  rw [CharTwo.add_sq]
  simpa only [one_pow] using CharTwo.add_cancel_right (1 : Polynomial K) (t ^ 2)

private theorem coe_charTwoMatrixPath (b : K) (h2 : (2 : K) = 0) :
    (charTwoMatrixPath b h2 : Matrix (Fin 2) (Fin 2) (Polynomial K)) =
      let t := Polynomial.X * Polynomial.C b
      !![1 + t, t; -t, 1 + t] :=
  by
    unfold charTwoMatrixPath
    rfl

private theorem rightTranslationAlgHom_eq_self_of_char_two
    [IsAlgClosed K] (h2 : (2 : K) = 0)
    (e : K ⊗[k] coordinateHopfAlgebra k 2) (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  let _ : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  let E := baseChangePointsMulEquiv (k := k) (K := K) 2 K
  let M := E g
  let b : K := M.val 0 1
  let xX : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] Polynomial K) :=
    (baseChangePointsMulEquiv (k := k) (K := K) 2 (Polynomial K)).symm
      (charTwoMatrixPath b h2)
  let eval (c : K) : Polynomial K →ₐ[K] K :=
    Polynomial.aevalTower (AlgHom.id K K) c
  have hM := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp M.2
  have hM00 : M.val 0 0 = 1 + b := by
    have hab : M.val 0 0 + b = 1 := by
      apply CharTwo.sq_inj.mp
      rw [CharTwo.add_sq, hM.2.2, one_pow]
    calc
      M.val 0 0 = M.val 0 0 + b + b := (CharTwo.add_cancel_right _ _).symm
      _ = 1 + b := congrArg (· + b) hab
  have hM10 : M.val 1 0 = -b := by
    simpa only [b, neg_neg] using (congrArg Neg.neg hM.2.1).symm
  apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he g xX (eval 1) (eval 0)
  · apply E.injective
    rw [baseChangePointsMulEquiv_mapValue]
    simp only [xX, MulEquiv.apply_symm_apply, E]
    apply Subtype.ext
    rw [Matrix.SpecialOrthogonalGroup.coe_map, coe_charTwoMatrixPath]
    -- Expose the local name `M` so its entry relations rewrite the target matrix.
    change _ = (M : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i
    · fin_cases j <;>
        norm_num [Matrix.of_apply, eval, b, hM00]
    · fin_cases j
      · norm_num [Matrix.of_apply, eval, b, hM10]
      · norm_num [Matrix.of_apply, eval, b]
        exact hM00.symm.trans hM.1
  · apply E.injective
    rw [baseChangePointsMulEquiv_mapValue]
    simp only [xX, MulEquiv.apply_symm_apply, map_one, E]
    apply Subtype.ext
    rw [Matrix.SpecialOrthogonalGroup.coe_map, coe_charTwoMatrixPath]
    ext i j
    fin_cases i
    · fin_cases j <;> norm_num [Matrix.of_apply, eval]
    · fin_cases j <;> norm_num [Matrix.of_apply, eval]

private theorem rightTranslationAlgHom_eq_self_of_two_ne_zero
    [Invertible (2 : k)] [IsAlgClosed K]
    (e : K ⊗[k] coordinateHopfAlgebra k 2) (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (n := 2) (by norm_num)
  have h2k : (2 : k) ≠ 0 := Invertible.ne_zero _
  have h2 : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k K)).2 h2k
  let half : K := (2 : K)⁻¹
  have hhalf : 2 * half = 1 := by
    exact mul_inv_cancel₀ h2
  let E := baseChangePointsMulEquiv (k := k) (K := K) 2 K
  let u : Kˣ := Matrix.SpecialOrthogonalGroup.finTwoToUnit i hi (E g)
  let eval (v : Kˣ) : LaurentPolynomial K →ₐ[K] K := MultiplicativeGroup.point v
  apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he g
    (laurentPath (k := k) i half hi hhalf) (eval u) (eval 1)
  · rw [mapValue_laurentPath]
    simpa only [u, E, MulEquiv.symm_apply_apply] using
      congrArg E.symm
        (Matrix.SpecialOrthogonalGroup.finTwoOfUnit_finTwoToUnit i half hi hhalf (E g))
  · rw [mapValue_laurentPath]
    simp

private theorem rightTranslationAlgHom_eq_self
    [IsAlgClosed K]
    (e : K ⊗[k] coordinateHopfAlgebra k 2) (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k 2 →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  by_cases h2k : (2 : k) = 0
  · have h2K : (2 : K) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg (algebraMap k K) h2k
    exact rightTranslationAlgHom_eq_self_of_char_two (k := k) h2K e he g
  · let _ : Invertible (2 : k) := invertibleOfNonzero h2k
    exact rightTranslationAlgHom_eq_self_of_two_ne_zero (k := k) (K := K) e he g

/-- The coordinate Hopf algebra of the standard `SO₂` is geometrically connected over every
field. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra_two
    (k : Type u) [Field k] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k 2) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro K _ _ _
  let H := coordinateHopfAlgebra k 2
  let _ : Nontrivial H := Bialgebra.nontrivial (A := H) k
  let _ : Nontrivial (K ⊗[k] H) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k K H
      (RingHom.injective (algebraMap k H))
  have hconnected : ConnectedSpace (PrimeSpectrum (K ⊗[k] H)) :=
    HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
      (fun e he g ↦ rightTranslationAlgHom_eq_self (k := k) (K := K) e he g)
  let equiv : (H : Type u) ⊗[k] K ≃+* K ⊗[k] H :=
    (Algebra.TensorProduct.comm k H K).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv equiv).connectedSpace_iff.mpr hconnected

/-! ### Every dimension, away from characteristic two -/

section CharNeTwo

variable (n : ℕ)

/-- **Right translation by a product of two reflections fixes every idempotent.** The
Laurent-polynomial family joining that point to the identity is a path in the sense of
`TauCeti.HopfAlgebra.rightTranslationAlgHom_eq_self_of_path`, evaluated at the two units the
family singles out. -/
private theorem rightTranslationAlgHom_eq_self_of_reflectionPair
    [Invertible (2 : K)] [IsAlgClosed K]
    (e : K ⊗[k] coordinateHopfAlgebra k n) (he : IsIdempotentElem e)
    {v w : Fin n → K} {c d : K} (hc : c * (v ⬝ᵥ v) = 2) (hd : d * (w ⬝ᵥ w) = 2) :
    HopfAlgebra.rightTranslationAlgHom
        ((baseChangePointsMulEquiv (k := k) (K := K) n K).symm
          (reflectionPair v w c d hc hd)) e = e := by
  obtain ⟨M, a, b, hM⟩ := exists_laurentPath_reflectionMatrix_mul (n := Fin n) hc hd
  apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he _
    ((baseChangePointsMulEquiv (k := k) (K := K) n (LaurentPolynomial K)).symm M)
    (MultiplicativeGroup.point b) (MultiplicativeGroup.point a)
  · apply (baseChangePointsMulEquiv (k := k) (K := K) n K).injective
    rw [baseChangePointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [Matrix.SpecialOrthogonalGroup.coe_map, coe_reflectionPair]
    exact (hM (MultiplicativeGroup.point b)).2 (by simp)
  · apply (baseChangePointsMulEquiv (k := k) (K := K) n K).injective
    rw [baseChangePointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, map_one]
    refine Subtype.ext ?_
    rw [Matrix.SpecialOrthogonalGroup.coe_map, Submonoid.coe_one]
    exact (hM (MultiplicativeGroup.point a)).1 (by simp)

/-- Right translation by any rational point of `SOₙ` fixes every idempotent: the points fixing a
given idempotent form a subgroup, and products of two reflections generate. -/
private theorem rightTranslationAlgHom_eq_self_of_invertibleTwo
    [Invertible (2 : K)] [IsAlgClosed K]
    (e : K ⊗[k] coordinateHopfAlgebra k n) (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k n →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  let E := baseChangePointsMulEquiv (k := k) (K := K) n K
  let fixes (x : Matrix.specialOrthogonalGroup (Fin n) K) : Prop :=
    HopfAlgebra.rightTranslationAlgHom (E.symm x) e = e
  have fixes_one : fixes 1 := by
    dsimp only [fixes]
    rw [map_one, HopfAlgebra.rightTranslationAlgHom_one, AlgHom.id_apply]
  have fixes_mul {x y : Matrix.specialOrthogonalGroup (Fin n) K} (hx : fixes x) (hy : fixes y) :
      fixes (x * y) := by
    dsimp only [fixes] at hx hy ⊢
    rw [map_mul, HopfAlgebra.rightTranslationAlgHom_mul, AlgHom.comp_apply, hy, hx]
  have fixes_inv {x : Matrix.specialOrthogonalGroup (Fin n) K} (hx : fixes x) : fixes x⁻¹ := by
    dsimp only [fixes] at hx ⊢
    have h := DFunLike.congr_fun
      (HopfAlgebra.rightTranslationAlgHom_mul (E.symm x⁻¹) (E.symm x)) e
    rw [← map_mul E.symm, inv_mul_cancel x, map_one,
      HopfAlgebra.rightTranslationAlgHom_one, AlgHom.id_apply, AlgHom.comp_apply, hx] at h
    exact h.symm
  let P : Subgroup (Matrix.specialOrthogonalGroup (Fin n) K) :=
    { carrier := fixes
      one_mem' := fixes_one
      mul_mem' := fixes_mul
      inv_mem' := fixes_inv }
  have mem_P (x : Matrix.specialOrthogonalGroup (Fin n) K) : x ∈ P ↔ fixes x := Iff.rfl
  -- By Cartan-Dieudonné, the special orthogonal matrices form the monoid closure of the products
  -- of two reflections, and every such product lies in `P`.
  let Q := Matrix.toQuadraticForm' (1 : Matrix (Fin n) (Fin n) K)
  have hle : Submonoid.closure {A : Matrix (Fin n) (Fin n) K |
      ∃ (v w : Fin n → K) (_ : Invertible (Q v)) (_ : Invertible (Q w)),
        LinearMap.toMatrix' (QuadraticMap.reflection Q v).toLinearMap *
          LinearMap.toMatrix' (QuadraticMap.reflection Q w).toLinearMap = A} ≤
      P.toSubmonoid.map (Matrix.specialOrthogonalGroup (Fin n) K).subtype := by
    refine Submonoid.closure_le.mpr ?_
    rintro _ ⟨v, w, hv, hw, rfl⟩
    have hcv : 2 * ⅟(Q v) * (v ⬝ᵥ v) = 2 := by
      rw [← toQuadraticForm'_one_apply v, mul_assoc, invOf_mul_self, mul_one]
    have hcw : 2 * ⅟(Q w) * (w ⬝ᵥ w) = 2 := by
      rw [← toQuadraticForm'_one_apply w, mul_assoc, invOf_mul_self, mul_one]
    refine ⟨reflectionPair v w _ _ hcv hcw,
      (mem_P _).mpr (rightTranslationAlgHom_eq_self_of_reflectionPair n e he hcv hcw), ?_⟩
    -- The mapped subgroup witness coerces definitionally to its underlying matrix equality.
    change (reflectionPair v w _ _ hcv hcw : Matrix (Fin n) (Fin n) K) = _
    rw [coe_reflectionPair, toMatrix'_reflection, toMatrix'_reflection]
  have hP : P = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ :=
      hle ((closure_reflection_mul_eq_matrixSpecialOrthogonalGroup (n := Fin n) (K := K)).ge x.2)
    exact Subtype.ext hyx ▸ hy
  have hg : E g ∈ P := by
    rw [hP]
    exact Subgroup.mem_top _
  simpa only [fixes, MulEquiv.symm_apply_apply] using (mem_P _).mp hg

/-- **The coordinate Hopf algebra of `SOₙ` is geometrically connected over every field of
characteristic different from two**, in every dimension. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] [NeZero (2 : k)] (n : ℕ) :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro K _ _ _
  have h2 : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k K)).2 (NeZero.ne (2 : k))
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  let H := coordinateHopfAlgebra k n
  let _ : Nontrivial H := Bialgebra.nontrivial (A := H) k
  let _ : Nontrivial (K ⊗[k] H) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k K H
      (RingHom.injective (algebraMap k H))
  have hconnected : ConnectedSpace (PrimeSpectrum (K ⊗[k] H)) :=
    HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
      fun e he g ↦ rightTranslationAlgHom_eq_self_of_invertibleTwo (k := k) (K := K) n e he g
  let equiv : (H : Type u) ⊗[k] K ≃+* K ⊗[k] H :=
    (Algebra.TensorProduct.comm k H K).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv equiv).connectedSpace_iff.mpr hconnected

end CharNeTwo

end

end TauCeti.SpecialOrthogonal
