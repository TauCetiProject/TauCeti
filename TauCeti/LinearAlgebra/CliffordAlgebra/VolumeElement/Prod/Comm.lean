/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Comm
public import TauCeti.LinearAlgebra.Orientation.WithLp
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Comm
import TauCeti.LinearAlgebra.LinearEquiv.Basic

/-!
# Graded Koszul symmetry of `CliffordAlgebra.complexProdTensor`

For even-dimensional oriented real inner product spaces `(V, o₁)` and `(W, o₂)` with
`Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, `Module.End.koszulComm (ρ₁ Γ_V) (ρ₂ Γ_W)` intertwines
`complexProdTensor` of `V ⊕ W` on `E ⊗ F` with `complexProdTensor` of `W ⊕ V` on `F ⊗ E` along
`QuadraticMap.IsometryEquiv.withLpProdComm`, and carries the product chirality `Γ_V ⊗ Γ_W` to
`Γ_W ⊗ Γ_V`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor` and
  `CliffordAlgebra.koszulComm_complexProdTensor`: `Module.End.koszulComm` intertwines the swapped
  `complexProdTensor` actions along `QuadraticMap.IsometryEquiv.withLpProdComm`.
* `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume` and
  `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume_of_map_withLpProdComm`: `koszulComm`
  intertwines the product chiralities of `V ⊕ W` and `W ⊕ V`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 2, §2.2.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q_VW : QuadraticForm ℝ (WithLp 2 (V × W))} {Q_WV : QuadraticForm ℝ (WithLp 2 (W × V))}
  (hQ_VW : ∀ x, Q_VW x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ_WV : ∀ y, Q_WV y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Koszul symmetry of `complexProdTensor` (pointwise form).** The Koszul commutor intertwines
`complexProdTensor` of `V ⊕ W` and `W ⊕ V` for every Clifford element `a` and tensor `z : E ⊗ F`.
-/
theorem koszulComm_complexProdTensor
    (a : CliffordAlgebra (Q_VW.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    let K := Module.End.koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)
    K (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁
        (map ((QuadraticMap.IsometryEquiv.withLpProdComm hQ_VW hQ_WV).toIsometry.baseChange ℂ) a)
        (K z) := by
  intro K
  have hrhs := AlgHom.congr_fun
    (complexProdTensor_comp_map_baseChange hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ hQ_VW
      (QuadraticMap.IsometryEquiv.withLpProdComm hQ_VW hQ_WV).toIsometry
      (QuadraticMap.IsometryEquiv.prodComm (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry
      (QuadraticMap.IsometryEquiv.withLpProdComm_toIsometry_baseChange ℂ hQ_VW hQ_WV)) a
  rw [complexProdTensor_eq_comp, AlgHom.comp_apply,
    ← AlgHom.comp_apply (complexProdTensor hQ_WV _ _ _ _ _), hrhs,
    AlgHom.comp_apply, AlgHom.comp_apply]
  exact AlgHom.koszulComm_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (ρ₁.involutive_complexVolume o₁ hQ₁) (map_complexVolume_mul_map_ι o₁ hn ρ₁)
    ρ₂ (ρ₂ (complexVolume Q₂ o₂)) (ρ₂.involutive_complexVolume o₂ hQ₂)
    (map_complexVolume_mul_map_ι o₂ hm ρ₂) _ z

/-- **Koszul symmetry of `complexProdTensor` (algebra-map form).** Conjugating `complexProdTensor`
of `V ⊕ W` on `E ⊗ F` by `Module.End.koszulComm (ρ₁ Γ_V) (ρ₂ Γ_W)` gives `complexProdTensor` of
`W ⊕ V` on `F ⊗ E` transported along `QuadraticMap.IsometryEquiv.withLpProdComm`. -/
theorem conjAlgEquiv_koszulComm_complexProdTensor :
    let K := Module.End.koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)
    (K.conjAlgEquiv ℂ).toAlgHom.comp (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁).comp
        (map ((QuadraticMap.IsometryEquiv.withLpProdComm hQ_VW
          hQ_WV).toIsometry.baseChange ℂ)) :=
  (LinearEquiv.conjAlgEquiv_toAlgHom_comp_eq_iff _ _ _).2
    (koszulComm_complexProdTensor hQ_VW hQ_WV o₁ o₂ hQ₁ hn hQ₂ hm ρ₁ ρ₂)

section Volume

variable [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
  [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
  (o_VW : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
  (o_WV : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n)))

/-- **Koszul symmetry preserves the product chirality.** For the canonical product orientations
`o_VW` of `V ⊕ W` and `o_WV` of `W ⊕ V`, `Module.End.koszulComm` carries `Γ_V ⊗ Γ_W` to
`Γ_W ⊗ Γ_V`. -/
theorem koszulComm_complexProdTensor_complexVolume
    (ho_VW : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o_VW)
    (ho_WV : (o₂.prod o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv 2 ℝ (W × V)).symm = o_WV)
    (z : E ⊗[ℂ] F) :
    let K := Module.End.koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)
    K (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q_VW o_VW) z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q_WV o_WV) (K z) := by
  intro K
  rw [complexProdTensor_complexVolume_of_map_prod hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ o₂ o_VW hm ho_VW,
    complexProdTensor_complexVolume_of_map_prod hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ o₁ o_WV hn ho_WV]
  exact Module.End.koszulComm_map _ _ _ _ z

/-- Because the `L²` swap preserves even-dimensional product orientations
(`Orientation.map_withLpProdComm_prod_of_even`), transporting `o_VW` along
`(LinearEquiv.prodComm ℝ V W).withLpCongr 2` gives `o_WV` and `Module.End.koszulComm` intertwines
their chiralities. -/
theorem koszulComm_complexProdTensor_complexVolume_of_map_withLpProdComm
    (ho_VW : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o_VW)
    (ho_WV : Orientation.reindex ℝ (WithLp 2 (W × V)) (finCongr (add_comm n m))
      (o_VW.map (Fin (n + m)) ((LinearEquiv.prodComm ℝ V W).withLpCongr 2)) = o_WV)
    (z : E ⊗[ℂ] F) :
    let K := Module.End.koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (ρ₁.involutive_complexVolume o₁ hQ₁) (ρ₂.involutive_complexVolume o₂ hQ₂)
    K (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q_VW o_VW) z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q_WV o_WV) (K z) := by
  have ho_WV' : (o₂.prod o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv 2 ℝ (W × V)).symm = o_WV := by
    rw [← ho_WV, ← ho_VW,
      Orientation.map_withLpProdComm_prod_of_even o₁ o₂ Fact.out Fact.out (hn.mul_right m),
      eq_comm, Orientation.reindex_finCongr_eq_iff]
  exact koszulComm_complexProdTensor_complexVolume hQ_VW hQ_WV o₁ o₂ hQ₁ hn hQ₂ hm ρ₁ ρ₂
    o_VW o_WV ho_VW ho_WV' z

end Volume

end CliffordAlgebra
