/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Comm
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv

/-!
# Koszul symmetry of `CliffordAlgebra.complexProdTensor`

For even-dimensional oriented real inner product spaces `V` and `W` with `Q₁ v = -‖v‖²` and
`Q₂ w = -‖w‖²`, both chiralities `Γ_V` and `Γ_W` are involutions anticommuting with generating
vectors. Consequently, the Koszul commutor `Module.End.koszulComm Γ_V Γ_W : E ⊗ F ≃ F ⊗ E`:

* intertwines `CliffordAlgebra.complexProdTensor` on `V ⊕ W` with `complexProdTensor` on `W ⊕ V`
  along `QuadraticMap.IsometryEquiv.withLpProdComm` (`CliffordAlgebra.koszulComm_complexProdTensor`,
  `CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor`);
* conjugates `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)` for the ordered product orientations
  (`CliffordAlgebra.conj_koszulComm_complexProdTensor_complexVolume`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module Module.End TensorProduct

namespace CliffordAlgebra

attribute [local instance] instFactFinrankWithLpProd

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {n m : ℕ} [Fact (finrank ℝ V = n)] [Fact (finrank ℝ W = m)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q : QuadraticForm ℝ (WithLp 2 (V × W))} {Q' : QuadraticForm ℝ (WithLp 2 (W × V))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ' : ∀ y, Q' y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  (o₂ : Orientation ℝ W (Fin m)) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Koszul symmetry of `CliffordAlgebra.complexProdTensor`**: for even-dimensional negative-metric
spaces `V` and `W`, `Module.End.koszulComm Γ_V Γ_W : E ⊗ F ≃ F ⊗ E` intertwines `complexProdTensor`
on `V ⊕ W` with `complexProdTensor` on `W ⊕ V` along `withLpProdComm`. -/
theorem koszulComm_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').baseChange ℂ) a)
        ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
          (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂) z) := by
  have hcomm :
      ((equivOfIsometry
            ((QuadraticMap.IsometryEquiv.withLpProd hQ').baseChangeProd ℂ)).toAlgHom.comp
          (equivOfIsometry
            ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').baseChange ℂ)).toAlgHom) =
        (CliffordAlgebra.map (QuadraticMap.IsometryEquiv.prodComm
            (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
          (equivOfIsometry
            ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom := by
    refine AlgHom.ext fun x ↦ ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
      AlgEquiv.coe_toAlgHom,
      ← equivOfIsometry_apply (QuadraticMap.IsometryEquiv.prodComm
        (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)),
      ← AlgEquiv.trans_apply, ← AlgEquiv.trans_apply, equivOfIsometry_trans,
      equivOfIsometry_trans,
      QuadraticMap.IsometryEquiv.baseChange_withLpProdComm_trans_baseChangeProd
        (A := ℂ) hQ hQ']
  have hcomm_a := AlgHom.congr_fun hcomm a
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hcomm_a
  rw [complexProdTensor_eq_comp, complexProdTensor_eq_comp, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, hcomm_a]
  exact AlgHom.koszulComm_cliffordProdTensor
    ρ₁ (ρ₁ (complexVolume Q₁ o₁)) (ρ₁.involutive_complexVolume o₁ hQ₁)
    (map_complexVolume_mul_map_ι o₁ hn ρ₁)
    ρ₂ (ρ₂ (complexVolume Q₂ o₂)) (ρ₂.involutive_complexVolume o₂ hQ₂)
    (map_complexVolume_mul_map_ι o₂ hm ρ₂)
    (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) a) z

/-- Bundled algebra-homomorphism form of `CliffordAlgebra.koszulComm_complexProdTensor`. -/
theorem conjAlgEquiv_koszulComm_complexProdTensor :
    (((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (ρ₁.involutive_complexVolume o₁ hQ₁)
        (ρ₂.involutive_complexVolume o₂ hQ₂)).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').baseChange ℂ)).toAlgHom := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun z ↦ ?_
  simpa [LinearEquiv.conjAlgEquiv_apply] using
    koszulComm_complexProdTensor hQ hQ' o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ a
      (((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (ρ₁.involutive_complexVolume o₁ hQ₁)
        (ρ₂.involutive_complexVolume o₂ hQ₂)).symm z)

/-- **Koszul commutor and the product chirality**: for the ordered product orientations `o` on
`V ⊕ W` and `o'` on `W ⊕ V`, the Koszul commutor conjugates `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)`. -/
theorem conj_koszulComm_complexProdTensor_complexVolume
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (o' : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n)))
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (ho' : (Orientation.prod o₂ o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv 2 ℝ (W × V)).symm = o') :
    ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q' o') := by
  subst o o'
  have hvol := equivOfIsometry_withLpProdComm_complexVolume hQ hQ' o₁ o₂
  rw [(hn.mul_right m).neg_one_pow, one_smul] at hvol
  exact conj_complexVolume_of_conjAlgEquiv_comp
    (conjAlgEquiv_koszulComm_complexProdTensor hQ hQ' o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂) hvol

end CliffordAlgebra
