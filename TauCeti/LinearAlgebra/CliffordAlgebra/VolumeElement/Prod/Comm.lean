/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp.QuadraticForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Comm
-- Private: ring-generic Koszul symmetry of `cliffordProdTensor` is used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Comm

/-!
# Koszul symmetry of `complexProdTensor`

Let `V` and `W` be even-dimensional oriented real inner product spaces of dimensions `n` and `m`
with negative-squared-norm quadratic forms `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and let `Q_VW` on
`WithLp 2 (V × W)` and `Q_WV` on `WithLp 2 (W × V)` be their orthogonal sums.

1. **Koszul intertwining**: the chiralities `Γ_V` on `E` and `Γ_W` on `F` are involutions
   (`CliffordAlgebra.map_complexVolume_involutive`), and specializing
   `AlgHom.koszulComm_cliffordProdTensor` from
   `TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Comm.lean` along the `WithLp` quadratic swap
   `TauCeti.withLpProdCommIsometryEquiv`
   (`TauCeti/Analysis/Normed/Lp/ProdLp/QuadraticForm.lean`), the Koszul commutor
   `Module.End.koszulComm Γ_V Γ_W` (`e ⊗ f ↦ (-1) ^ (|e| |f|) • (f ⊗ e)` on chirality-homogeneous
   elements) intertwines `complexProdTensor` of `V ⊕ W` with `complexProdTensor` of `W ⊕ V` on
   every Clifford element (`CliffordAlgebra.koszulComm_complexProdTensor` and
   `CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor`).
2. **Chirality intertwining**: for all even `n` and `m` (including `2 ⊕ 2`), `n * m` is even so
   swapping the factors preserves the canonical product orientation
   (`Orientation.map_withLpProdComm_prod` and `Orientation.map_withLpProdComm_prod_of_even` in
   `TauCeti/Analysis/Normed/Lp/ProdLp/Orientation.lean`), and the Koszul commutor intertwines the
   product chiralities `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W` and `Γ_(W ⊕ V) = Γ_W ⊗ Γ_V` without sign
   (`CliffordAlgebra.koszulComm_complexProdTensor_complexVolume`).

## Main results

* `CliffordAlgebra.koszulComm_complexProdTensor` and
  `CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor`: Koszul symmetry of
  `complexProdTensor`.
* `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume`: `koszulComm` intertwines the
  product chiralities for all even `n` and `m`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module Module.End TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q_VW : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q_WV : QuadraticForm ℝ (WithLp 2 (W × V))}
  (hQ_VW : ∀ x, Q_VW x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ_WV : ∀ y, Q_WV y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
  (hn : Even n) (hm : Even m)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Pointwise Koszul symmetry of `complexProdTensor`**: `Module.End.koszulComm Γ_V Γ_W`
intertwines the graded tensor actions of `V ⊕ W` and `W ⊕ V` along
`TauCeti.withLpProdCommIsometryEquiv` on every Clifford element `a` and tensor `z : E ⊗ F`. -/
theorem koszulComm_complexProdTensor (a : CliffordAlgebra (Q_VW.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁)
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)
        (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁
        (CliffordAlgebra.map
          ((TauCeti.withLpProdCommIsometryEquiv hQ_VW hQ_WV).toIsometry.baseChange ℂ) a)
        (koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
          (map_complexVolume_involutive o₁ hQ₁ ρ₁)
          (map_complexVolume_involutive o₂ hQ₂ ρ₂) z) := by
  have hmap :
      (CliffordAlgebra.map
          (QuadraticMap.IsometryEquiv.prodComm (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
        (equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ_VW ℂ)).toAlgHom =
      (equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ_WV ℂ)).toAlgHom.comp
        (CliffordAlgebra.map
          ((TauCeti.withLpProdCommIsometryEquiv hQ_VW hQ_WV).toIsometry.baseChange ℂ)) := by
    refine baseChange_algHom_ext Q_VW fun x ↦ ?_
    rcases x with ⟨v, w⟩
    simp [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.prodComm_toFun]
  have hmap_a := AlgHom.congr_fun hmap a
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hmap_a
  rw [complexProdTensor_def, complexProdTensor_def, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, ← hmap_a]
  exact AlgHom.koszulComm_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (map_complexVolume_involutive o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁)
    ρ₂ (ρ₂ (complexVolume Q₂ o₂)) (map_complexVolume_involutive o₂ hQ₂ ρ₂)
    (map_complexVolume_mul_map_ι o₂ hm ρ₂) _ z

/-- **Koszul symmetry of `complexProdTensor` as an `AlgHom` identity**: conjugating the graded
tensor action of `V ⊕ W` on `E ⊗ F` by the Koszul commutor `Module.End.koszulComm Γ_V Γ_W` yields
the graded tensor action of `W ⊕ V` on `F ⊗ E`, transported along
`TauCeti.withLpProdCommIsometryEquiv`. -/
theorem conjAlgEquiv_koszulComm_complexProdTensor :
    ((koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁)
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁).comp
        (CliffordAlgebra.map
          ((TauCeti.withLpProdCommIsometryEquiv hQ_VW hQ_WV).toIsometry.baseChange ℂ)) := by
  apply AlgHom.ext; intro a; apply LinearMap.ext; intro z
  simpa [LinearEquiv.conjAlgEquiv_apply, koszulComm_symm] using
    koszulComm_complexProdTensor hQ_VW hQ_WV o₁ o₂ hQ₁ hQ₂ hn hm ρ₁ ρ₂ a
      ((koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁)
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).symm z)

/-- **Koszul symmetry intertwines the product chiralities**: for even-dimensional `V` and `W` with
canonical product orientations `o_VW` and `o_WV`, `koszulComm` intertwines `Γ_(V ⊕ W) = Γ_V ⊗ Γ_W`
and `Γ_(W ⊕ V) = Γ_W ⊗ Γ_V`. -/
theorem koszulComm_complexProdTensor_complexVolume
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    {o_VW : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho_VW : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o_VW)
    {o_WV : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n))}
    (ho_WV : (Orientation.prod o₂ o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv 2 ℝ (W × V)).symm = o_WV)
    (z : E ⊗[ℂ] F) :
    koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁)
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)
        (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q_VW o_VW) z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q_WV o_WV)
        (koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
          (map_complexVolume_involutive o₁ hQ₁ ρ₁)
          (map_complexVolume_involutive o₂ hQ₂ ρ₂) z) := by
  rw [complexProdTensor_complexVolume_of_prod hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm hQ₂ ho_VW,
    complexProdTensor_complexVolume_of_prod hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ o₁ hn hQ₁ ho_WV]
  exact koszulComm_map _ _ _ _ z

end CliffordAlgebra
