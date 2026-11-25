/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Geometry.Hodge.MumfordTate.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Pi

/-!
# The Hodge components of the representation of `S` of a Hodge structure

Let `hs` be a pure Hodge structure of weight `n` on a complex vector space `W` with conjugation
`ω`, and `e` a basis of `W` fixed by `ω`. The homomorphism `h : S → GL_{d,ℝ}` of the Deligne torus
(`TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom`) makes `ℝ^d` a representation of `S`,
the standard comodule corestricted along `h` (`TauCeti.GeneralLinear.corestrictStandardComodule`).
Its complexification `ℂ ⊗[ℝ] ℝ^d` is identified with `W` through `e`
(`Module.Basis.tensorPiEquiv`), and this file shows that the Hodge components of the
representation (`TauCeti.DeligneTorus.hodgeComponent`) are the Hodge components of `hs`:
`(ℝ^d)^{p,n-p}` corresponds to `H^{p,n-p}`, and `(ℝ^d)^{p,q} = 0` for `p + q ≠ n`. So passing
from a Hodge structure to its representation of `S` and back through
`TauCeti.DeligneTorus.isHodgeDecomposition_hodgeComponent` returns the Hodge decomposition of
`hs`, read in the coordinates `e`.

The proof evaluates the action at the universal point of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`, which acts through the
matrix `∑ p, P p * X^{(-p, p - n)}` of `TauCeti.Hodge.HodgeStructureOn.splitCoordinateMatrix`;
on the coordinates of a vector of `H^{p,n-p}` this matrix is multiplication by `X^{(-p, p - n)}`.
This gives one inclusion, and the two decompositions are both internal direct sums.

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

/-- A vector of `H^{p,n-p}` lies in the Hodge component `(ℝ^d)^{p,n-p}` of the representation of
`S` given by `h`. -/
theorem tensorPiEquiv_symm_mem_hodgeComponent (he : ∀ i, ω.toEquiv (e i) = e i)
    {p : ℤ} {v : W} (hv : v ∈ hs.piece p) :
    letI := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
    (e.tensorPiEquiv ℝ).symm v ∈ hodgeComponent (Fin d → ℝ) p (n - p) := by
  let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
  rw [mem_hodgeComponent_iff]
  apply (TensorProduct.piScalarRight ℝ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
    (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) (Fin d)).injective
  have h := LinearMap.congr_fun (piScalarRight_comp_endOfPoint_corestrictStandardComodule ℝ d
    (hs.realCoordinateBialgHom he) splittingPoint.ofConv)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [h]
  simpa [hs.coe_pointToGeneralLinear_splittingPoint_comp_realCoordinateBialgHom he,
    TensorProduct.piScalarRight_rTensor ℂ] using hs.splitCoordinateMatrix_mulVec_of_mem e hv

/-- **The Hodge components of the representation of `S` of a Hodge structure.** In a basis `e`
fixed by the conjugation, `h : S → GL_{d,ℝ}` makes `ℝ^d` a representation of `S` whose Hodge
component `(ℝ^d)^{p,q}` is the image of `H^{p,q}` under `ℂ ⊗[ℝ] ℝ^d ≃ W` when `p + q = n`, and
`0` otherwise. -/
theorem hodgeComponent_corestrictStandardComodule (he : ∀ i, ω.toEquiv (e i) = e i) (p q : ℤ) :
    let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
    hodgeComponent (Fin d → ℝ) p q =
      if p + q = n then (hs.piece p).map (e.tensorPiEquiv ℝ).symm.toLinearMap else ⊥ := by
  let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
  let G : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℝ] (Fin d → ℝ)) := fun pq ↦
    if pq.1 + pq.2 = n then (hs.piece pq.1).map (e.tensorPiEquiv ℝ).symm.toLinearMap else ⊥
  have hle : G ≤ fun pq ↦ hodgeComponent (Fin d → ℝ) pq.1 pq.2 := fun pq ↦ by
    simp only [G]
    split_ifs with h
    · rw [Submodule.map_le_iff_le_comap]
      intro v hv
      have hq : pq.2 = n - pq.1 := by omega
      rw [Submodule.mem_comap, hq]
      exact hs.tensorPiEquiv_symm_mem_hodgeComponent he hv
    · exact bot_le
  have htop : ⨆ pq, G pq = ⊤ := by
    refine top_unique ?_
    calc ⊤ = (⨆ p, hs.piece p).map (e.tensorPiEquiv ℝ).symm.toLinearMap := by
          rw [hs.iSup_piece_eq_top, Submodule.map_top, LinearEquiv.range]
      _ = ⨆ p, (hs.piece p).map (e.tensorPiEquiv ℝ).symm.toLinearMap :=
          Submodule.map_iSup _ _
      _ ≤ ⨆ pq, G pq := iSup_le fun p ↦ le_iSup_of_le (p, n - p) (by simp [G])
  have hG := ((isInternal_hodgeComponent (Fin d → ℝ)).submodule_iSupIndep.le_iff_eq_of_iSup_eq_top
    htop).mp hle
  exact (congrFun hG (p, q)).symm

/-- **Under `ℂ ⊗[ℝ] ℝ^d ≃ W`, the Hodge component `(ℝ^d)^{p,n-p}` is `H^{p,n-p}`**: the
isomorphism `e.tensorPiEquiv ℝ` maps the Hodge component `(ℝ^d)^{p,n-p}` of the representation
of `S` given by `h` onto `H^{p,n-p}`. -/
theorem map_hodgeComponent_corestrictStandardComodule (he : ∀ i, ω.toEquiv (e i) = e i)
    (p : ℤ) :
    let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
    (hodgeComponent (Fin d → ℝ) p (n - p)).map (e.tensorPiEquiv ℝ).toLinearMap =
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
