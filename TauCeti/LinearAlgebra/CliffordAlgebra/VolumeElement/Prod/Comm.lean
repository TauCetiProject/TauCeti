/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Eigenspace
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Comm
import Mathlib.Tactic.Module

/-!
# Koszul symmetry of `complexProdTensor`

Let `V` and `W` be even-dimensional oriented real inner product spaces of dimensions `n` and `m`
with negative-squared-norm quadratic forms `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and let `Q_VW` on
`WithLp 2 (V × W)` and `Q_WV` on `WithLp 2 (W × V)` be their orthogonal sums.

1. **Metric swap**: `LinearIsometryEquiv.withLpProdComm 2 ℝ V W` induces a quadratic isometric
   equivalence `CliffordAlgebra.withLpProdCommIsometry : Q_VW.IsometryEquiv Q_WV`.
2. **Koszul intertwining**: the chiralities `Γ_V` on `E` and `Γ_W` on `F` are involutions
   (`CliffordAlgebra.involutive_apply_complexVolume`), and the Koszul commutor
   `Module.End.koszulComm Γ_V Γ_W` (`e ⊗ f ↦ (-1) ^ (|e| |f|) • (f ⊗ e)` on chirality-homogeneous
   elements) intertwines `complexProdTensor` of `V ⊕ W` with `complexProdTensor` of `W ⊕ V` along
   `withLpProdCommIsometry` on every Clifford element
   (`CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor` and
   `CliffordAlgebra.koszulComm_complexProdTensor`).
3. **Orientation preservation and chirality intertwining**: when `n * m` is even (in particular
   whenever `n` or `m` is even), `withLpProdComm` preserves the canonical product orientation up to
   `finCongr (add_comm m n)` (`Orientation.map_withLpProdComm_prod_of_even`), and for even `n`
   and `m` the Koszul commutor intertwines the product chiralities `Γ_(V ⊕ W)` and `Γ_(W ⊕ V)`
   (`CliffordAlgebra.koszulComm_complexProdTensor_complexVolume`).

## Main definitions

* `CliffordAlgebra.withLpProdCommIsometry`: `Q_VW.IsometryEquiv Q_WV` via
  `LinearIsometryEquiv.withLpProdComm 2 ℝ V W`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor` and
  `CliffordAlgebra.koszulComm_complexProdTensor`: Koszul symmetry of `complexProdTensor`.
* `Orientation.map_withLpProdComm_prod_of_even`: `withLpProdComm` preserves product
  orientations when `Even (n * m)`.
* `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume`: `koszulComm` intertwines the
  product chiralities.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module Module.End TensorProduct

namespace CliffordAlgebra

section Isometry

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q_VW : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q_WV : QuadraticForm ℝ (WithLp 2 (W × V))}
  (hQ_VW : ∀ x, Q_VW x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ_WV : ∀ y, Q_WV y = Q₂ (WithLp.ofLp y).1 + Q₁ (WithLp.ofLp y).2)

/-- `LinearIsometryEquiv.withLpProdComm 2 ℝ V W` as a quadratic isometric equivalence
`Q_VW.IsometryEquiv Q_WV` between `V ⊕ W` and `W ⊕ V`. -/
def withLpProdCommIsometry : Q_VW.IsometryEquiv Q_WV where
  toLinearEquiv := (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv
  map_app' x := by
    simp only [hQ_WV, hQ_VW, WithLp.ofLp_fst, WithLp.ofLp_snd, add_comm]
    rfl

/-- Evaluation of `CliffordAlgebra.withLpProdCommIsometry` swaps the two `L²` coordinates. -/
@[simp]
theorem withLpProdCommIsometry_apply (x : WithLp 2 (V × W)) :
    withLpProdCommIsometry hQ_VW hQ_WV x = WithLp.toLp 2 (x.snd, x.fst) :=
  (rfl)

/-- `CliffordAlgebra.withLpProdCommIsometry` preserves norms. -/
theorem norm_withLpProdCommIsometry (x : WithLp 2 (V × W)) :
    ‖withLpProdCommIsometry hQ_VW hQ_WV x‖ = ‖x‖ :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).norm_map x

/-! ### Orientation transport under factor swap -/

section OrientationComm

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

/-- **Even-product orientation preservation on `WithLp 2`**: when `n * m` is even (in particular
when either `V` or `W` is even-dimensional), `LinearIsometryEquiv.withLpProdComm 2 ℝ V W` carries
the canonical product orientation of `V ⊕ W` to that of `W ⊕ V`, reindexed along `m + n = n + m`. -/
theorem _root_.Orientation.map_withLpProdComm_prod_of_even (hnm : Even (n * m))
    {o_VW : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m))}
    (ho_VW : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o_VW)
    {o_WV : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n))}
    (ho_WV : (Orientation.prod o₂ o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv 2 ℝ (W × V)).symm = o_WV) :
    Orientation.map (Fin (n + m))
        (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv o_VW =
      Orientation.reindex ℝ (WithLp 2 (W × V)) (finCongr (add_comm m n)) o_WV := by
  subst ho_VW ho_WV
  rw [← Orientation.map_trans, ← Orientation.map_reindex,
    ← Orientation.map_prodComm_prod_of_even o₁ o₂ Fact.out Fact.out hnm, ← Orientation.map_trans]
  have heq : (WithLp.linearEquiv 2 ℝ (V × W)).symm.trans
      (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).toLinearEquiv =
    (LinearEquiv.prodComm ℝ V W).trans (WithLp.linearEquiv 2 ℝ (W × V)).symm := by
    ext; rfl
  rw [heq]

end OrientationComm

/-! ### Koszul symmetry of `complexProdTensor` -/

section Koszul

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2)
  (hn : Even n) (hm : Even m)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Pointwise Koszul symmetry of `complexProdTensor`**: `Module.End.koszulComm Γ_V Γ_W`
intertwines the graded tensor actions of `V ⊕ W` and `W ⊕ V` on every Clifford element `a` and
tensor `z : E ⊗ F`. -/
theorem koszulComm_complexProdTensor (a : CliffordAlgebra (Q_VW.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
        (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
        (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
        (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁
        (CliffordAlgebra.map
          ((withLpProdCommIsometry hQ_VW hQ_WV).toIsometry.baseChange ℂ) a)
        (koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
          (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
          (involutive_apply_complexVolume o₂ hQ₂ ρ₂) z) := by
  induction a using CliffordAlgebra.induction generalizing z with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | ι t =>
    induction t using TensorProduct.inductionOn with
    | tmul c x =>
      let v := (WithLp.ofLp x).1
      let w := (WithLp.ofLp x).2
      have hcx : c ⊗ₜ[ℝ] x = c • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 (v, w)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hcx, map_smul, map_smul, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
        map_smul]
      congr 1
      induction z using TensorProduct.inductionOn with
      | tmul e f =>
        have hinv₁ := involutive_apply_complexVolume o₁ hQ₁ ρ₁
        have hinv₂ := involutive_apply_complexVolume o₂ hQ₂ ρ₂
        have hv : ρ₁ (complexVolume Q₁ o₁) (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)) e) =
            -ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)) (ρ₁ (complexVolume Q₁ o₁) e) := by
          rw [← mul_apply_eq_comp, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg, map_mul,
            LinearMap.neg_apply, mul_apply_eq_comp]
        have hw : ρ₂ (complexVolume Q₂ o₂) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) f) =
            -ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) (ρ₂ (complexVolume Q₂ o₂) f) := by
          rw [← mul_apply_eq_comp, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg, map_mul,
            LinearMap.neg_apply, mul_apply_eq_comp]
        rw [complexProdTensor_ι_one_tmul_toLp]
        simp only [map_apply_ι, QuadraticMap.Isometry.baseChange_tmul,
          QuadraticMap.IsometryEquiv.toIsometry_apply, withLpProdCommIsometry_apply,
          WithLp.toLp_fst, WithLp.toLp_snd, complexProdTensor_ι_one_tmul_toLp,
          LinearMap.add_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, map_add,
          koszulComm_tmul, map_smul, map_sub, hinv₁ e, hinv₂ f, hv, hw, tmul_neg, neg_tmul]
        module
      | add y z hy hz => simp only [map_add, hy, hz]
    | add p q hp hq =>
      simp only [map_add, LinearMap.add_apply, hp, hq]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | mul a b ha hb => simp only [map_mul, mul_apply_eq_comp, ha, hb]

/-- **Koszul symmetry of `complexProdTensor` as an `AlgHom` identity**: conjugating the graded
tensor action of `V ⊕ W` on `E ⊗ F` by the Koszul commutor `Module.End.koszulComm Γ_V Γ_W` yields
the graded tensor action of `W ⊕ V` on `F ⊗ E`, transported along
`CliffordAlgebra.withLpProdCommIsometry`. -/
theorem conjAlgEquiv_koszulComm_complexProdTensor :
    ((koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
        (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
        (involutive_apply_complexVolume o₂ hQ₂ ρ₂)).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁).comp
        (CliffordAlgebra.map
          ((withLpProdCommIsometry hQ_VW hQ_WV).toIsometry.baseChange ℂ)) := by
  apply AlgHom.ext; intro a; apply LinearMap.ext; intro z
  simpa [LinearEquiv.conjAlgEquiv_apply, koszulComm_symm] using
    koszulComm_complexProdTensor hQ_VW hQ_WV o₁ o₂ hQ₁ hQ₂ hn hm ρ₁ ρ₂ a
      ((koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
        (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
        (involutive_apply_complexVolume o₂ hQ₂ ρ₂)).symm z)

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
        (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
        (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
        (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q_VW o_VW) z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q_WV o_WV)
        (koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
          (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
          (involutive_apply_complexVolume o₂ hQ₂ ρ₂) z) := by
  rw [complexProdTensor_complexVolume_of_prod hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm hQ₂ ho_VW,
    complexProdTensor_complexVolume_of_prod hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ o₁ hn hQ₁ ho_WV]
  exact koszulComm_map _ _ _ _ z

end Koszul

end Isometry

end CliffordAlgebra
