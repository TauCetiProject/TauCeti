/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Comm
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic

/-!
# Graded symmetry of the tensor product of complex Clifford modules

Let `V` and `W` be even-dimensional oriented real inner product spaces of dimensions `n` and `m`
with the negative-metric forms `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`. Exchanging the summands via
`LinearIsometryEquiv.withLpProdComm 2 ℝ V W` preserves the ordered product orientation because
`n * m` is even (`CliffordAlgebra.map_withLpProdComm_orientation_of_even`), and therefore carries
the normalized complex volume element `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)`
(`CliffordAlgebra.map_withLpProdCommIsometry_complexVolume`).

On complex Clifford modules `E` and `F`, the Koszul swap `Module.End.koszulComm` built from the
chiralities `Γ_V` and `Γ_W`, sending `e ⊗ f` to `(-1) ^ (|e| |f|) f ⊗ e` on homogeneous spinors
(`Module.End.koszulComm_tmul_of_apply_eq_neg_one_pow_smul`), intertwines `complexProdTensor` of
`V ⊕ W` with `complexProdTensor` of `W ⊕ V` along `withLpProdComm`
(`CliffordAlgebra.koszulComm_complexProdTensor`,
`CliffordAlgebra.conjAlgEquiv_complexProdTensor_comm`), and carries the product chirality action on
`E ⊗ F` to that on `F ⊗ E` (`CliffordAlgebra.koszulComm_complexProdTensor_complexVolume`).

## Main definitions

* `CliffordAlgebra.withLpProdCommIsometry`: `LinearIsometryEquiv.withLpProdComm 2 ℝ V W` as a
  quadratic isometry equivalence `Q ≃ Q'`.

## Main results

* `CliffordAlgebra.map_withLpProdComm_orientation_of_even` and
  `CliffordAlgebra.map_withLpProdCommIsometry_complexVolume`: orientation and volume compatibility
  under `withLpProdComm`.
* `CliffordAlgebra.koszulComm_complexProdTensor` and
  `CliffordAlgebra.conjAlgEquiv_complexProdTensor_comm`: the Koszul swap intertwines the two
  `complexProdTensor` actions.
* `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume`: the Koszul swap intertwines the
  product chiralities.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, the chapter on Clifford modules.
-/

public section

noncomputable section

open Module Module.End TensorProduct

namespace CliffordAlgebra

section Isometry

variable {V W : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup W] [NormedSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q : QuadraticForm ℝ (WithLp 2 (V × W))} {Q' : QuadraticForm ℝ (WithLp 2 (W × V))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)

include hQ hQ' in
/-- `LinearIsometryEquiv.withLpProdComm 2 ℝ V W` as a quadratic isometry equivalence between
`V ⊕ W` and `W ⊕ V`. -/
def withLpProdCommIsometry : Q.IsometryEquiv Q' where
  toLinearEquiv := (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv
  map_app' x := by simp [hQ, hQ', add_comm]

/-- Applying `CliffordAlgebra.withLpProdCommIsometry` swaps the two `L²`-product coordinates. -/
@[simp]
theorem withLpProdCommIsometry_apply (x : WithLp 2 (V × W)) :
    withLpProdCommIsometry hQ hQ' x = LinearIsometryEquiv.withLpProdComm 2 ℝ V W x :=
  (rfl)

/-- The linear equivalence underlying `CliffordAlgebra.withLpProdCommIsometry` is
`LinearIsometryEquiv.withLpProdComm`. -/
@[simp]
theorem withLpProdCommIsometry_toLinearEquiv :
    (withLpProdCommIsometry hQ hQ').toLinearEquiv =
      (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv :=
  (rfl)

end Isometry

section Orientation

variable {V W : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {n m : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = m)]
  (o₁ : Orientation ℝ V (Fin n)) (o₂ : Orientation ℝ W (Fin m))
  (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
  (o' : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n)))

/-- When `n * m` is even, `LinearIsometryEquiv.withLpProdComm` carries the ordered product
orientation of `V ⊕ W` to that of `W ⊕ V`, reindexed along `add_comm m n`. -/
theorem map_withLpProdComm_orientation_of_even (heven : Even (n * m))
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out)
    (ho' : o'.map (Fin (m + n)) (WithLp.linearEquiv 2 ℝ (W × V)) = o₂.prod o₁ Fact.out Fact.out) :
    o.map (Fin (n + m)) (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv =
      Orientation.reindex ℝ _ (finCongr (add_comm m n)) o' := by
  have hcomm : (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv.trans
      (WithLp.linearEquiv 2 ℝ (W × V)) =
      (WithLp.linearEquiv 2 ℝ (V × W)).trans (LinearEquiv.prodComm ℝ V W) := by
    ext x <;> rfl
  have key : (o.map (Fin (n + m))
      (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv).map
      (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (W × V)) =
      (Orientation.reindex ℝ _ (finCongr (add_comm m n)) o').map
      (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (W × V)) := by
    rw [← Orientation.map_trans, hcomm, Orientation.map_trans, ho,
      Orientation.map_prodComm_prod_of_even _ _ _ _ heven, Orientation.map_reindex, ho']
  exact (Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (W × V))).injective key

end Orientation

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

/-- When `n * m` is even, `CliffordAlgebra.withLpProdCommIsometry` carries the normalized complex
volume element of `V ⊕ W` to that of `W ⊕ V`. -/
theorem map_withLpProdCommIsometry_complexVolume
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    (heven : Even (n * m))
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)) = o₁.prod o₂ Fact.out Fact.out)
    (ho' : o'.map (Fin (m + n)) (WithLp.linearEquiv 2 ℝ (W × V)) = o₂.prod o₁ Fact.out Fact.out) :
    map ((withLpProdCommIsometry hQ hQ').toIsometry.baseChange ℂ) (complexVolume Q o) =
      complexVolume Q' o' := by
  have := Fact.mk ((LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv.finrank_eq.symm.trans
    (Fact.out : finrank ℝ (WithLp 2 (V × W)) = n + m))
  rw [map_complexVolume o (withLpProdCommIsometry hQ hQ')
      (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).norm_map,
    withLpProdCommIsometry_toLinearEquiv,
    map_withLpProdComm_orientation_of_even o₁ o₂ o o' heven ho ho',
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
`W ⊕ V` along `CliffordAlgebra.withLpProdCommIsometry`. -/
theorem koszulComm_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁) (map_complexVolume_involutive o₂ hQ₂ ρ₂)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁
        (map ((withLpProdCommIsometry hQ hQ').toIsometry.baseChange ℂ) a)
        ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
          (map_complexVolume_involutive o₁ hQ₁ ρ₁)
          (map_complexVolume_involutive o₂ hQ₂ ρ₂) z) := by
  have hdiag : (map (QuadraticMap.IsometryEquiv.prodComm
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
        (equivOfIsometry (complexWithLpProd hQ)).toAlgHom =
      (equivOfIsometry (complexWithLpProd hQ')).toAlgHom.comp
        (map ((withLpProdCommIsometry hQ hQ').toIsometry.baseChange ℂ)) := by
    apply CliffordAlgebra.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro c x
    simp [equivOfIsometry_apply]
  have h := AlgHom.koszulComm_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (map_complexVolume_involutive o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁)
    ρ₂ (ρ₂ (complexVolume Q₂ o₂))
    (map_complexVolume_involutive o₂ hQ₂ ρ₂) (map_complexVolume_mul_map_ι o₂ hm ρ₂)
    (equivOfIsometry (complexWithLpProd hQ) a) z
  have hdiag_a := DFunLike.congr_fun hdiag a
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hdiag_a
  rw [complexProdTensor_def, complexProdTensor_def, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, ← hdiag_a]
  exact h

/-- Conjugating `complexProdTensor` of `V ⊕ W` by the Koszul swap gives `complexProdTensor` of
`W ⊕ V` pulled back along `CliffordAlgebra.withLpProdCommIsometry`. -/
theorem conjAlgEquiv_complexProdTensor_comm :
    ((((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁)
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).conjAlgEquiv ℂ).toAlgHom).comp
      (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁).comp
        (equivOfIsometry ((withLpProdCommIsometry hQ hQ').baseChange ℂ)).toAlgHom := by
  apply AlgHom.ext
  intro a
  apply LinearMap.ext
  intro z
  let κ := (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
    (map_complexVolume_involutive o₁ hQ₁ ρ₁) (map_complexVolume_involutive o₂ hQ₂ ρ₂)
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
        (map_complexVolume_involutive o₁ hQ₁ ρ₁) (map_complexVolume_involutive o₂ hQ₂ ρ₂)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o) z) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q' o')
        ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
          (map_complexVolume_involutive o₁ hQ₁ ρ₁)
          (map_complexVolume_involutive o₂ hQ₂ ρ₂) z) := by
  rw [koszulComm_complexProdTensor,
    map_withLpProdCommIsometry_complexVolume hQ hQ' o₁ o₂ o o' (hn.mul_right m) ho ho']

end Action

end CliffordAlgebra
