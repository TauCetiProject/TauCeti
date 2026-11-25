/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Geometry.Hodge.MumfordTate
import TauCeti.LinearAlgebra.TensorProduct.Pi

/-!
# The Hodge components of the representation of `S` of a Hodge structure

Let `hs` be a pure Hodge structure of weight `n` on a complex vector space `W` with conjugation
`ω`, and `e` a basis of `W` fixed by `ω`. The homomorphism `h : S → GL_{d,ℝ}` of the Deligne torus
(`TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom`) makes `ℝ^d` a representation of `S`,
the standard comodule corestricted along `h` (`TauCeti.GeneralLinear.corestrictStandardComodule`).
Its complexification `ℂ ⊗[ℝ] ℝ^d` is identified with `W` through `e`
(`TauCeti.Hodge.HodgeStructureOn.complexCoordinateEquiv`), and this file shows that the Hodge
components of the representation (`TauCeti.DeligneTorus.hodgeComponent`) are the Hodge
components of `hs`: `(ℝ^d)^{p,n-p}` corresponds to `H^{p,n-p}`, and `(ℝ^d)^{p,q} = 0` for
`p + q ≠ n`. So passing from a Hodge structure to its representation of `S` and back through
`TauCeti.DeligneTorus.isHodgeDecomposition_hodgeComponent` returns the Hodge decomposition of
`hs`, read in the coordinates `e`.

The proof evaluates the action at the universal point of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`, which acts through the
matrix `∑ p, P p * X^{(-p, p - n)}` of `TauCeti.Hodge.HodgeStructureOn.splitCoordinateMatrix`;
on the coordinates of a vector of `H^{p,n-p}` this matrix is multiplication by `X^{(-p, p - n)}`.
This gives one inclusion, and the two decompositions are both internal direct sums.

## Main definitions

* `TauCeti.Hodge.HodgeStructureOn.complexCoordinateEquiv e`: the identification
  `ℂ ⊗[ℝ] ℝ^d ≃ W`, `a ⊗ x ↦ a • ∑ i, x i • e i`.

## Main results

* `TauCeti.Hodge.HodgeStructureOn.hodgeComponent_corestrictStandardComodule`: the Hodge
  component `(ℝ^d)^{p,q}` is the image of `H^{p,q}` for `p + q = n`, and `0` otherwise.
* `TauCeti.Hodge.HodgeStructureOn.map_hodgeComponent_corestrictStandardComodule`: under
  `ℂ ⊗[ℝ] ℝ^d ≃ W`, `(ℝ^d)^{p,n-p}` is `H^{p,n-p}`.
* `TauCeti.Hodge.HodgeStructureOn.isHodgeDecomposition_corestrictStandardComodule`: the Hodge
  components of the representation form a Hodge decomposition of weight `n`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
-/

public section

open TauCeti.DeligneTorus TauCeti.GeneralLinear WithConv
open scoped TensorProduct Matrix

namespace TauCeti.Hodge.HodgeStructureOn

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ω : Conjugation W} {n : ℤ}
  (hs : HodgeStructureOn W ω n) {d : ℕ} {e : Module.Basis (Fin d) ℂ W}

/-- The universal point of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ` sends the generic matrix, through `h`, to the matrix
`∑ p, P p * X^{(-p, p - n)}` of the Hodge projections. -/
theorem splittingPoint_realCoordinateBialgHom_genericMatrix (he : ∀ i, ω.toEquiv (e i) = e i)
    (i j : Fin d) :
    splittingPoint.ofConv (hs.realCoordinateBialgHom he (genericMatrix ℝ d i j)) =
      hs.splitCoordinateMatrix e i j := by
  rw [← splittingBialgEquiv_one_tmul, one_tmul_realCoordinateBialgHom, genericMatrix_apply,
    complexCoordinateBialgHom_one_tmul_X, BialgEquiv.apply_symm_apply]

/-- The matrix of the complexified action of `S` in the basis `e`, applied to the coordinates of a
vector of `H^{p,n-p}`, multiplies them by the character `X^{(-p,p-n)}`. -/
theorem splitCoordinateMatrix_mulVec_of_mem {p : ℤ} {v : W} (hv : v ∈ hs.piece p) :
    hs.splitCoordinateMatrix e *ᵥ
        (fun j ↦ algebraMap ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) (e.repr v j)) =
      MonoidAlgebra.single (Multiplicative.ofAdd (-p, p - n)) (1 : ℂ) •
        fun j ↦ algebraMap ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) (e.repr v j) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, splitCoordinateMatrix_apply, Finset.sum_mul,
    Pi.smul_apply, smul_eq_mul, MonoidAlgebra.coe_algebraMap, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, MonoidAlgebra.single_mul_single, mul_one, one_mul]
  rw [Finset.sum_comm]
  have hp' (p' : ℤ) : ∑ j, MonoidAlgebra.single (Multiplicative.ofAdd (-p', p' - n))
      (e.repr (hs.proj p' (e j)) i * e.repr v j) =
        MonoidAlgebra.single (Multiplicative.ofAdd (-p', p' - n)) (e.repr (hs.proj p' v) i) := by
    rw [show ∑ j, MonoidAlgebra.single (Multiplicative.ofAdd (-p', p' - n))
        (e.repr (hs.proj p' (e j)) i * e.repr v j) = MonoidAlgebra.single
          (Multiplicative.ofAdd (-p', p' - n)) (∑ j, e.repr (hs.proj p' (e j)) i * e.repr v j) from
      (map_sum (MonoidAlgebra.singleAddHom _) _ _).symm]
    congr 1
    have hsum := congrArg (fun w ↦ e.repr (hs.proj p' w) i) (e.sum_repr v)
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at hsum
    rw [← hsum]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  simp_rw [hp']
  by_cases hmem : p ∈ hs.hodgeSupport
  · rw [Finset.sum_eq_single p (fun p' _ hp'p ↦ by
      rw [hs.proj_apply_eq_zero_of_mem_of_ne hv (Ne.symm hp'p), map_zero, Finsupp.zero_apply,
        MonoidAlgebra.single_zero]) (fun h ↦ absurd hmem h), hs.proj_apply_of_mem hv]
  · have hv0 : v = 0 := by
      have hbot : hs.piece p = ⊥ := by simpa [mem_hodgeSupport] using hmem
      simpa [hbot] using hv
    simp [hv0]

/-- The identification `ℂ ⊗[ℝ] ℝ^d ≃ W` of the complexification of `ℝ^d` with `W`, through the
basis `e`: `a ⊗ x ↦ a • ∑ i, x i • e i`. -/
noncomputable def complexCoordinateEquiv (e : Module.Basis (Fin d) ℂ W) :
    ℂ ⊗[ℝ] (Fin d → ℝ) ≃ₗ[ℂ] W :=
  (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin d)).trans e.equivFun.symm

/-- Read in `ℂ^d`, the inverse of `complexCoordinateEquiv e` takes a vector to its coordinates
in `e`. -/
theorem piScalarRight_complexCoordinateEquiv_symm (v : W) :
    TensorProduct.piScalarRight ℝ ℂ ℂ (Fin d) ((complexCoordinateEquiv e).symm v) = e.repr v := by
  simp [complexCoordinateEquiv]

/-- A vector of `H^{p,n-p}` lies in the Hodge component `(ℝ^d)^{p,n-p}` of the representation of
`S` given by `h`. -/
theorem complexCoordinateEquiv_symm_mem_hodgeComponent (he : ∀ i, ω.toEquiv (e i) = e i)
    {p : ℤ} {v : W} (hv : v ∈ hs.piece p) :
    letI := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
    (complexCoordinateEquiv e).symm v ∈ hodgeComponent (Fin d → ℝ) p (n - p) := by
  let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
  rw [mem_hodgeComponent_iff]
  apply (TensorProduct.piScalarRight ℝ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
    (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) (Fin d)).injective
  have hend : Comodule.endOfPoint (Fin d → ℝ) splittingPoint.ofConv =
      (let _ := standardComodule ℝ d
       Comodule.endOfPoint (Fin d → ℝ)
        (splittingPoint.ofConv.comp
          (hs.realCoordinateBialgHom he : coordinateHopfAlgebra ℝ d →ₐ[ℝ] S))) := by
    let _ := standardComodule ℝ d
    exact Comodule.endOfPoint_corestrict _ _
  have h := LinearMap.congr_fun (piScalarRight_comp_endOfPoint ℝ d
    (toConv (splittingPoint.ofConv.comp
      (hs.realCoordinateBialgHom he : coordinateHopfAlgebra ℝ d →ₐ[ℝ] S))))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  have hM : (pointToGeneralLinear d (toConv (splittingPoint.ofConv.comp
      (hs.realCoordinateBialgHom he : coordinateHopfAlgebra ℝ d →ₐ[ℝ] S))) :
        Matrix (Fin d) (Fin d) (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))) =
      hs.splitCoordinateMatrix e := by
    refine Matrix.ext fun i j ↦ ?_
    rw [pointToGeneralLinear_apply, toConv_ofConv, ← genericMatrix_apply, AlgHom.comp_apply]
    exact hs.splittingPoint_realCoordinateBialgHom_genericMatrix he i j
  rw [hend, h, map_smul, TensorProduct.piScalarRight_rTensor (S := ℂ),
    piScalarRight_complexCoordinateEquiv_symm, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply, hM, neg_sub]
  exact hs.splitCoordinateMatrix_mulVec_of_mem hv

/-- **The Hodge components of the representation of `S` of a Hodge structure.** In a basis `e`
fixed by the conjugation, `h : S → GL_{d,ℝ}` makes `ℝ^d` a representation of `S` whose Hodge
component `(ℝ^d)^{p,q}` is the image of `H^{p,q}` under `ℂ ⊗[ℝ] ℝ^d ≃ W` when `p + q = n`, and
`0` otherwise. -/
theorem hodgeComponent_corestrictStandardComodule (he : ∀ i, ω.toEquiv (e i) = e i) (p q : ℤ) :
    let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
    hodgeComponent (Fin d → ℝ) p q =
      if p + q = n then (hs.piece p).map (complexCoordinateEquiv e).symm.toLinearMap else ⊥ := by
  let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
  let G : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℝ] (Fin d → ℝ)) := fun pq ↦
    if pq.1 + pq.2 = n then (hs.piece pq.1).map (complexCoordinateEquiv e).symm.toLinearMap else ⊥
  have hle : G ≤ fun pq ↦ hodgeComponent (Fin d → ℝ) pq.1 pq.2 := fun pq ↦ by
    simp only [G]
    split_ifs with h
    · rw [Submodule.map_le_iff_le_comap]
      intro v hv
      have hq : pq.2 = n - pq.1 := by omega
      rw [Submodule.mem_comap, hq]
      exact hs.complexCoordinateEquiv_symm_mem_hodgeComponent he hv
    · exact bot_le
  have htop : ⨆ pq, G pq = ⊤ := by
    refine top_unique ?_
    calc ⊤ = (⨆ p, hs.piece p).map (complexCoordinateEquiv e).symm.toLinearMap := by
          rw [hs.iSup_piece_eq_top, Submodule.map_top, LinearEquiv.range]
      _ = ⨆ p, (hs.piece p).map (complexCoordinateEquiv e).symm.toLinearMap :=
          Submodule.map_iSup _ _
      _ ≤ ⨆ pq, G pq := iSup_le fun p ↦ le_iSup_of_le (p, n - p) (by simp [G])
  have hG := ((isInternal_hodgeComponent (Fin d → ℝ)).submodule_iSupIndep.le_iff_eq_of_iSup_eq_top
    htop).mp hle
  exact (congrFun hG (p, q)).symm

/-- **`h` carries `H^{p,n-p}` to the Hodge component `(ℝ^d)^{p,n-p}`**: under
`ℂ ⊗[ℝ] ℝ^d ≃ W`, the Hodge component `(ℝ^d)^{p,n-p}` of the representation of `S` given by `h`
is `H^{p,n-p}`. -/
theorem map_hodgeComponent_corestrictStandardComodule (he : ∀ i, ω.toEquiv (e i) = e i)
    (p : ℤ) :
    let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
    (hodgeComponent (Fin d → ℝ) p (n - p)).map (complexCoordinateEquiv e).toLinearMap =
      hs.piece p := by
  intro _
  rw [hs.hodgeComponent_corestrictStandardComodule he, add_sub_cancel, ite_eq_left rfl,
    ← Submodule.map_comp]
  simp

/-- **The representation of `S` of a Hodge structure of weight `n` is pure of weight `n`**: its
Hodge components `(ℝ^d)^{p,q}` with `p + q ≠ n` vanish. -/
theorem hodgeComponent_corestrictStandardComodule_eq_bot (he : ∀ i, ω.toEquiv (e i) = e i)
    {p q : ℤ} (hpq : p + q ≠ n) :
    let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
    hodgeComponent (Fin d → ℝ) p q = ⊥ := by
  intro _
  rw [hs.hodgeComponent_corestrictStandardComodule he]
  simp [hpq]

/-- The Hodge components of the representation of `S` of a Hodge structure of weight `n` form a
Hodge decomposition of weight `n` of `ℂ ⊗[ℝ] ℝ^d`. -/
theorem isHodgeDecomposition_corestrictStandardComodule (he : ∀ i, ω.toEquiv (e i) = e i) :
    let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
    IsHodgeDecomposition (complexificationConjugation (Fin d → ℝ)) n
      fun p ↦ hodgeComponent (Fin d → ℝ) p (n - p) := by
  intro _
  exact isHodgeDecomposition_hodgeComponent fun _ _ ↦
    hs.hodgeComponent_corestrictStandardComodule_eq_bot he

end TauCeti.Hodge.HodgeStructureOn
