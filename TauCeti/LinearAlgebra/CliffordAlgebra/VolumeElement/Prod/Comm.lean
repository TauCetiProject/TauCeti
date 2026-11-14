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

Let `V` and `W` be even-dimensional oriented real inner product spaces with negative-metric
quadratic forms `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and let `E` and `F` be modules over their
complexified Clifford algebras. Both chirality operators `Γ_V = ρ₁ (complexVolume Q₁ o₁)` and
`Γ_W = ρ₂ (complexVolume Q₂ o₂)` are involutions anticommuting with generating vectors, so the
Koszul commutor

  `Module.End.koszulComm Γ_V Γ_W : E ⊗ F ≃ F ⊗ E`,

which sends `e ⊗ f` of `Γ`-parities `(-1) ^ p` and `(-1) ^ q` to `(-1) ^ (p * q) • (f ⊗ e)`,
intertwines `CliffordAlgebra.complexProdTensor` on `V ⊕ W` with `CliffordAlgebra.complexProdTensor`
on `W ⊕ V` along the `L²` summand swap `QuadraticMap.IsometryEquiv.withLpProdComm` on every
Clifford element (`CliffordAlgebra.koszulComm_complexProdTensor`,
`CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor`).

Because `n` is even, exchanging `V` and `W` multiplies the product orientation by
`(-1) ^ (n * m) = 1` (`Orientation.map_prodComm_prod_of_even`), so `koszulComm` also conjugates the
product chirality `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)`
(`CliffordAlgebra.conj_koszulComm_complexProdTensor_complexVolume`).

## Main results

* `CliffordAlgebra.koszulComm_complexProdTensor` and
  `CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor`: the Koszul commutor intertwines
  `complexProdTensor` on `V ⊕ W` and `W ⊕ V`.
* `CliffordAlgebra.conj_koszulComm_complexProdTensor_complexVolume`: the Koszul commutor conjugates
  `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)` for the ordered product orientations.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module Module.End TensorProduct

namespace CliffordAlgebra

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
spaces `V` and `W`, the Koszul commutor `Module.End.koszulComm Γ_V Γ_W : E ⊗ F ≃ F ⊗ E` intertwines
`complexProdTensor` on `V ⊕ W` with `complexProdTensor` on `W ⊕ V` along `withLpProdComm`. -/
theorem koszulComm_complexProdTensor (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁) (map_complexVolume_involutive o₂ hQ₂ ρ₂)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').baseChange ℂ) a)
        ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
          (map_complexVolume_involutive o₁ hQ₁ ρ₁) (map_complexVolume_involutive o₂ hQ₂ ρ₂) z) := by
  have hcomm :
      ((equivOfIsometry
            ((QuadraticMap.IsometryEquiv.withLpProd hQ').baseChangeProd ℂ)).toAlgHom.comp
          (equivOfIsometry
            ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').baseChange ℂ)).toAlgHom) =
        (CliffordAlgebra.map
            (QuadraticMap.IsometryEquiv.prodComm
              (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry).comp
          (equivOfIsometry
            ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ)).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul c x =>
      simp [equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcomm_a := AlgHom.congr_fun hcomm a
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at hcomm_a
  rw [complexProdTensor_eq_cliffordProdTensor, complexProdTensor_eq_cliffordProdTensor, hcomm_a]
  exact AlgHom.koszulComm_cliffordProdTensor
    ρ₁ (ρ₁ (complexVolume Q₁ o₁)) (map_complexVolume_involutive o₁ hQ₁ ρ₁)
    (fun v ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
    ρ₂ (ρ₂ (complexVolume Q₂ o₂)) (map_complexVolume_involutive o₂ hQ₂ ρ₂)
    (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg])
    (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) a) z

/-- Bundled algebra-homomorphism form of `CliffordAlgebra.koszulComm_complexProdTensor`. -/
theorem conjAlgEquiv_koszulComm_complexProdTensor :
    (((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁)
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').baseChange ℂ)).toAlgHom := by
  apply AlgHom.ext
  intro a
  apply LinearMap.ext
  intro z
  have h := koszulComm_complexProdTensor hQ hQ' o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ a
    (((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
      (map_complexVolume_involutive o₁ hQ₁ ρ₁)
      (map_complexVolume_involutive o₂ hQ₂ ρ₂)).symm z)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

/-- **Koszul commutor and the product chirality**: for the ordered product orientations `o` on
`V ⊕ W` and `o'` on `W ⊕ V`, the Koszul commutor conjugates `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)`. -/
theorem conj_koszulComm_complexProdTensor_complexVolume
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (o' : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n)))
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (ho' : (Orientation.prod o₂ o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv 2 ℝ (W × V)).symm = o') :
    ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁)
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).conj
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q' o') := by
  subst o o'
  have hnorm : ∀ x, ‖QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ' x‖ = ‖x‖ := fun x ↦ by
    simpa using (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).norm_map x
  have hcongr : (LinearEquiv.prodComm ℝ V W).withLpCongr 2 =
      ((WithLp.linearEquiv 2 ℝ (V × W)).trans (LinearEquiv.prodComm ℝ V W)).trans
        (WithLp.linearEquiv 2 ℝ (W × V)).symm := by
    ext x
    rfl
  have horient :
      Orientation.map (Fin (n + m))
          (QuadraticMap.IsometryEquiv.withLpProdComm hQ hQ').toLinearEquiv
          ((Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
            (WithLp.linearEquiv 2 ℝ (V × W)).symm) =
        Orientation.reindex ℝ (WithLp 2 (W × V)) (finCongr (add_comm m n))
          ((Orientation.prod o₂ o₁ Fact.out Fact.out).map (Fin (m + n))
            (WithLp.linearEquiv 2 ℝ (W × V)).symm) := by
    simp only [QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdComm, hcongr,
      Orientation.map_trans]
    rw [← Orientation.map_symm (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)),
      Equiv.apply_symm_apply,
      Orientation.map_prodComm_prod_of_even o₁ o₂ Fact.out Fact.out (hn.mul_right m),
      Orientation.map_reindex]
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply,
    koszulComm_complexProdTensor hQ hQ' o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ _
      (((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₁ hQ₁ ρ₁)
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).symm z),
    LinearEquiv.apply_symm_apply, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume_of_eq _ _ hnorm (add_comm n m), horient,
    Orientation.reindex_finCongr_reindex_finCongr]
  simp [finCongr_refl, Orientation.reindex_refl]

end CliffordAlgebra
