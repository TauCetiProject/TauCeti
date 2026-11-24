/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp.QuadraticForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Comm
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
import TauCeti.Analysis.Normed.Lp.ProdLp.Orientation

/-!
# Graded symmetry of the tensor product of complex Clifford modules

Let `V` and `W` be even-dimensional oriented real inner product spaces of dimensions `n` and `m`
with `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`. Exchanging the summands via
`LinearIsometryEquiv.withLpProdComm 2 ℝ V W` preserves the ordered product orientation (`n * m` is
even) and carries `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)`. On complex Clifford modules `E` and `F`, the Koszul
swap `Module.End.koszulComm` built from `Γ_V` and `Γ_W` intertwines `complexProdTensor` of `V ⊕ W`
with that of `W ⊕ V` along `QuadraticMap.IsometryEquiv.withLpProdComm` and carries the product
chirality action on `E ⊗ F` to that on `F ⊗ E`.

## Main results

* `CliffordAlgebra.map_withLpProdComm_complexVolume`: volume compatibility under `withLpProdComm`.
* `CliffordAlgebra.koszulComm_complexProdTensor`,
  `CliffordAlgebra.conjAlgEquiv_complexProdTensor_comm`, and
  `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume`: Koszul-swap intertwining laws.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed. (2007), Definition 2.2.42.
-/

public section

noncomputable section

open Module Module.End TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q : QuadraticForm ℝ (WithLp 2 (V × W))} {Q' : QuadraticForm ℝ (WithLp 2 (W × V))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)

section ComplexVolume

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {n m : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = m)]
  (o₁ : Orientation ℝ V (Fin n)) (o₂ : Orientation ℝ W (Fin m))
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
  (o' : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n)))

/-- When `n * m` is even, `QuadraticMap.IsometryEquiv.withLpProdComm` carries the normalized
complex volume element of `V ⊕ W` to that of `W ⊕ V`. -/
theorem map_withLpProdComm_complexVolume
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    (heven : Even (n * m))
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out)
    (ho' : o'.map (Fin (m + n)) (WithLp.linearEquiv 2 ℝ (W × V)) = o₂.prod o₁ Fact.out Fact.out) :
    map ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').toIsometry.baseChange ℂ)
        (complexVolume Q o) =
      complexVolume Q' o' := by
  have := Fact.mk ((LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv.finrank_eq.symm.trans
    (Fact.out : finrank ℝ (WithLp 2 (V × W)) = n + m))
  rw [map_complexVolume o (QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ')
      (QuadraticMap.IsometryEquiv.norm_withLpProdComm hQ hQ'),
    QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdComm_eq_linearIsometryEquiv,
    Orientation.map_withLpProdComm_of_even o₁ o₂ o o' Fact.out Fact.out heven ho ho',
    complexVolume_reindex_finCongr]

end ComplexVolume

section Action

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {n m : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = m)]
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  (o₂ : Orientation ℝ W (Fin m)) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Graded symmetry of `CliffordAlgebra.complexProdTensor`**: the Koszul swap built from the
chiralities `Γ_V` and `Γ_W` intertwines `complexProdTensor` of `V ⊕ W` with `complexProdTensor` of
`W ⊕ V` along `QuadraticMap.IsometryEquiv.withLpProdComm`. -/
theorem koszulComm_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁
        (map ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').toIsometry.baseChange ℂ) a)
        ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
          (ρ₁.involutive_complexVolume o₁ hQ₁)
          (ρ₂.involutive_complexVolume o₂ hQ₂) z) := by
  have hdiag : (map (QuadraticMap.IsometryEquiv.prodComm
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
        (equivOfIsometry (complexWithLpProd hQ)).toAlgHom =
      (equivOfIsometry (complexWithLpProd hQ')).toAlgHom.comp
        (map ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').toIsometry.baseChange ℂ)) :=
    CliffordAlgebra.hom_ext <| TensorProduct.AlgebraTensorModule.ext fun c x ↦ by
      simp [equivOfIsometry_apply]
  have hdiag_a := DFunLike.congr_fun hdiag a
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hdiag_a
  rw [complexProdTensor_def, complexProdTensor_def, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, ← hdiag_a]
  exact AlgHom.koszulComm_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (ρ₁.involutive_complexVolume o₁ hQ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁)
    ρ₂ (ρ₂ (complexVolume Q₂ o₂))
    (ρ₂.involutive_complexVolume o₂ hQ₂) (map_complexVolume_mul_map_ι o₂ hm ρ₂)
    (equivOfIsometry (complexWithLpProd hQ) a) z

/-- Conjugating `complexProdTensor` of `V ⊕ W` by the Koszul swap gives `complexProdTensor` of
`W ⊕ V` pulled back along `QuadraticMap.IsometryEquiv.withLpProdComm`. -/
theorem conjAlgEquiv_complexProdTensor_comm :
    ((((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (ρ₁.involutive_complexVolume o₁ hQ₁)
        (ρ₂.involutive_complexVolume o₂ hQ₂)).conjAlgEquiv ℂ).toAlgHom).comp
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').baseChange ℂ)).toAlgHom := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun z ↦ ?_
  let κ := (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
    (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)
  simpa [LinearEquiv.conjAlgEquiv_apply, equivOfIsometry_apply, κ] using
    koszulComm_complexProdTensor hQ hQ' o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ a (κ.symm z)

/-- The Koszul swap carries the product chirality action on `E ⊗ F` to the product chirality action
on `F ⊗ E`. -/
theorem koszulComm_complexProdTensor_complexVolume
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (o' : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n)))
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out)
    (ho' : o'.map (Fin (m + n)) (WithLp.linearEquiv 2 ℝ (W × V)) = o₂.prod o₁ Fact.out Fact.out)
    (z : E ⊗[ℂ] F) :
    (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) z) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q' o')
        ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
          (ρ₁.involutive_complexVolume o₁ hQ₁)
          (ρ₂.involutive_complexVolume o₂ hQ₂) z) := by
  rw [koszulComm_complexProdTensor,
    map_withLpProdComm_complexVolume hQ hQ' o₁ o₂ o o' (hn.mul_right m) ho ho']

end Action

end CliffordAlgebra
