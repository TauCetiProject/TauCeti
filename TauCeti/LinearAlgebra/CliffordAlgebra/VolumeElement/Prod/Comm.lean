/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Comm
public import TauCeti.LinearAlgebra.Orientation.WithLp
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
import Mathlib.Tactic.Module

/-!
# Graded Koszul symmetry of `CliffordAlgebra.complexProdTensor`

Let `(V, o₁)` and `(W, o₂)` be even-dimensional oriented real inner product spaces of dimensions
`n` and `m` with `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and let `E` and `F` be complex Clifford
modules over `Q₁` and `Q₂`.

The chiralities `Γ_V` and `Γ_W` are involutions on `E` and `F`, and the Koszul commutor
`Module.End.koszulComm (ρ₁ Γ_V) (ρ₂ Γ_W)`, which sends `e ⊗ f ↦ (-1) ^ (|e| |f|) f ⊗ e` on
chirality-homogeneous vectors, intertwines `complexProdTensor` of `V ⊕ W` on `E ⊗ F` with
`complexProdTensor` of `W ⊕ V` on `F ⊗ E` along `QuadraticMap.IsometryEquiv.withLpProdComm`.
Because `n * m` is even, the `L²` swap preserves the ordered product orientations
(`Orientation.map_withLpProdComm_prod_of_even`), and `koszulComm` carries the product chirality
`Γ_V ⊗ Γ_W` of `V ⊕ W` to `Γ_W ⊗ Γ_V` of `W ⊕ V`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_koszulComm_complexProdTensor` and
  `CliffordAlgebra.koszulComm_complexProdTensor`: `Module.End.koszulComm` intertwines the swapped
  `complexProdTensor` actions along `QuadraticMap.IsometryEquiv.withLpProdComm`.
* `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume` and
  `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume_map`: `koszulComm` intertwines the
  product chiralities of `V ⊕ W` and `W ⊕ V`.

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

/-- **Koszul symmetry of `complexProdTensor` (algebra-map form).** Conjugating `complexProdTensor`
of `V ⊕ W` on `E ⊗ F` by `Module.End.koszulComm (ρ₁ Γ_V) (ρ₂ Γ_W)` gives `complexProdTensor` of
`W ⊕ V` on `F ⊗ E` transported along `QuadraticMap.IsometryEquiv.withLpProdComm`. -/
theorem conjAlgEquiv_koszulComm_complexProdTensor :
    let K := Module.End.koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
    (K.conjAlgEquiv ℂ).toAlgHom.comp (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁).comp
        (map ((QuadraticMap.IsometryEquiv.withLpProdComm hQ_VW
          hQ_WV).toIsometry.baseChange ℂ)) := by
  intro K
  have hsq₁ (e' : E) : ρ₁ (complexVolume Q₁ o₁) (ρ₁ (complexVolume Q₁ o₁) e') = e' :=
    involutive_apply_complexVolume o₁ hQ₁ ρ₁ e'
  have hsq₂ (f' : F) : ρ₂ (complexVolume Q₂ o₂) (ρ₂ (complexVolume Q₂ o₂) f') = f' :=
    involutive_apply_complexVolume o₂ hQ₂ ρ₂ f'
  have hanti₁ : ∀ v : V, ∀ e' : E,
      ρ₁ (complexVolume Q₁ o₁) (ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)) e') =
        -ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)) (ρ₁ (complexVolume Q₁ o₁) e') := fun v e' ↦ by
    have h := congrArg (fun φ : Module.End ℂ E ↦ φ e')
      (by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg] :
        ρ₁ (complexVolume Q₁ o₁) * ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)) =
          -(ρ₁ (ι (Q₁.baseChange ℂ) (1 ⊗ₜ v)) * ρ₁ (complexVolume Q₁ o₁)))
    simpa [LinearMap.comp_apply, ← Module.End.mul_eq_comp] using h
  have hanti₂ : ∀ w : W, ∀ f' : F,
      ρ₂ (complexVolume Q₂ o₂) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) f') =
        -ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) (ρ₂ (complexVolume Q₂ o₂) f') := fun w f' ↦ by
    have h := congrArg (fun φ : Module.End ℂ F ↦ φ f')
      (by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg] :
        ρ₂ (complexVolume Q₂ o₂) * ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) =
          -(ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w)) * ρ₂ (complexVolume Q₂ o₂)))
    simpa [LinearMap.comp_apply, ← Module.End.mul_eq_comp] using h
  have hintertwine (v : V) (w : W) (z : E ⊗[ℂ] F) :
      K (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂
          (ι (Q_VW.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (v, w))) z) =
        complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁
          (ι (Q_WV.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (w, v))) (K z) := by
    induction z using TensorProduct.inductionOn with
    | tmul e f =>
      simp only [complexProdTensor_ι_one_tmul_toLp, LinearMap.add_apply, TensorProduct.map_tmul,
        LinearMap.rTensor_tmul, map_add, K, Module.End.koszulComm_tmul, hsq₁, hsq₂, hanti₁,
        hanti₂, TensorProduct.tmul_neg, TensorProduct.neg_tmul, map_smul, map_sub]
      module
    | add x y hx hy => simp only [map_add, hx, hy]
  refine AlgHom.toRingHom_injective <| baseChange_ringHom_ext Q_VW (fun _ ↦ by simp) fun x ↦ ?_
  obtain ⟨⟨v, w⟩, rfl⟩ : ∃ p : V × W, WithLp.toLp 2 p = x :=
    ⟨WithLp.ofLp x, by simp⟩
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := K.surjective y
  simpa [LinearEquiv.conjAlgEquiv_apply, QuadraticMap.Isometry.baseChange_tmul] using
    hintertwine v w z

/-- **Koszul symmetry of `complexProdTensor` (pointwise form).** The Koszul commutor
`e ⊗ f ↦ (-1) ^ (|e| |f|) f ⊗ e` intertwines `complexProdTensor` of `V ⊕ W` and `W ⊕ V` for every
Clifford element `a` and tensor `z : E ⊗ F`. -/
theorem koszulComm_complexProdTensor
    (a : CliffordAlgebra (Q_VW.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    let K := Module.End.koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
    K (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁
        (map ((QuadraticMap.IsometryEquiv.withLpProdComm hQ_VW hQ_WV).toIsometry.baseChange ℂ) a)
        (K z) := by
  intro K
  have h := congrArg (fun φ : CliffordAlgebra (Q_VW.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (F ⊗[ℂ] E) ↦
      φ a (K z))
    (conjAlgEquiv_koszulComm_complexProdTensor hQ_VW hQ_WV o₁ o₂ hQ₁ hn hQ₂ hm ρ₁ ρ₂)
  simpa [K, LinearEquiv.conjAlgEquiv_apply] using h

/-- **Koszul symmetry preserves the product chirality.** For the canonical product orientations
`o_VW` of `V ⊕ W` and `o_WV` of `W ⊕ V`, `Module.End.koszulComm` carries the chirality action
`Γ_V ⊗ Γ_W` of `V ⊕ W` to `Γ_W ⊗ Γ_V` of `W ⊕ V`. -/
theorem koszulComm_complexProdTensor_complexVolume
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    (o_VW : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (o_WV : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n)))
    (ho_VW : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o_VW)
    (ho_WV : (o₂.prod o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv 2 ℝ (W × V)).symm = o_WV)
    (z : E ⊗[ℂ] F) :
    let K := Module.End.koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
    K (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q_VW o_VW) z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q_WV o_WV) (K z) := by
  intro K
  rw [complexProdTensor_complexVolume_of_map_prod hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ o₂ o_VW hm hQ₂ ho_VW,
    complexProdTensor_complexVolume_of_map_prod hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ o₁ o_WV hn hQ₁ ho_WV]
  exact Module.End.koszulComm_map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
    (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂) z

/-- Because the `L²` swap preserves even-dimensional product orientations
(`Orientation.map_withLpProdComm_prod_of_even`), transporting `o_VW` along
`(LinearEquiv.prodComm ℝ V W).withLpCongr 2` gives `o_WV` and `Module.End.koszulComm` intertwines
their chiralities. -/
theorem koszulComm_complexProdTensor_complexVolume_map
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    (o_VW : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (o_WV : Orientation ℝ (WithLp 2 (W × V)) (Fin (m + n)))
    (ho_VW : (o₁.prod o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o_VW)
    (ho_WV : Orientation.reindex ℝ (WithLp 2 (W × V)) (finCongr (add_comm n m))
      (o_VW.map (Fin (n + m)) ((LinearEquiv.prodComm ℝ V W).withLpCongr 2)) = o_WV)
    (z : E ⊗[ℂ] F) :
    let K := Module.End.koszulComm (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))
      (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
    K (complexProdTensor hQ_VW o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q_VW o_VW) z) =
      complexProdTensor hQ_WV o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q_WV o_WV) (K z) := by
  have ho_WV' : (o₂.prod o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv 2 ℝ (W × V)).symm = o_WV := by
    rw [← ho_WV, ← ho_VW,
      Orientation.map_withLpProdComm_prod_of_even o₁ o₂ Fact.out Fact.out (hn.mul_right m),
      Orientation.reindex_finCongr_reindex_finCongr, finCongr_refl, Orientation.reindex_refl,
      Equiv.refl_apply]
  exact koszulComm_complexProdTensor_complexVolume hQ_VW hQ_WV o₁ o₂ hQ₁ hn hQ₂ hm ρ₁ ρ₂
    o_VW o_WV ho_VW ho_WV' z

end CliffordAlgebra
