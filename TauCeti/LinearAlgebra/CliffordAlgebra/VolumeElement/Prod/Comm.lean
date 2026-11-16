/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct.Comm
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Comm

/-!
# Koszul symmetry of the graded tensor product of complex Clifford modules

Let `V` and `W` be oriented even-dimensional real inner product spaces of dimensions `n` and `m`,
with negative-metric quadratic forms `Q₁ v = -‖v‖²` and `Q₂ w = -‖w‖²`, and let `Q` on
`V ⊕ W = WithLp 2 (V × W)` and `Q'` on `W ⊕ V = WithLp 2 (W × V)` be their orthogonal sum forms.
Given Clifford modules `E` and `F`, the chirality operators `Γ_V` on `E` and `Γ_W` on `F` are
involutions, so `Module.End.koszulComm` defines the graded exchange equivalence
`E ⊗ F ≃ F ⊗ E` sending `x ⊗ y` to `(-1) ^ (p * q) • (y ⊗ x)` on homogeneous vectors.

Through `AlgHom.koszulComm_cliffordProdTensor`, the Koszul commutor intertwines the graded tensor
product action of `V ⊕ W` on `E ⊗ F` with that of `W ⊕ V` on `F ⊗ E` along any quadratic isometry
realizing `(v, w) ↦ (w, v)`. Moreover, because `n * m` is even whenever `n` or `m` is even,
exchanging the factors preserves the canonical product orientation
(`Orientation.map_prodComm_prod_of_even`), so the exchange carries `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)` and
the Koszul commutor intertwines the two product chirality operators.

## Main results

* `CliffordAlgebra.koszulComm_complexProdTensor`: the Koszul commutor intertwines
  `complexProdTensor` on `E ⊗ F` with that on `F ⊗ E` along `(v, w) ↦ (w, v)`.
* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_koszulComm`: conjugation form of Koszul symmetry.
* `CliffordAlgebra.koszulComm_complexProdTensor_complexVolume_prod`: the Koszul commutor
  intertwines the product chirality `Γ_(V ⊕ W)` with `Γ_(W ⊕ V)`.
* `CliffordAlgebra.map_complexVolume_prodComm`: for `Even (n * m)`, exchanging `V ⊕ W` and
  `W ⊕ V` carries `Γ_(V ⊕ W)` to `Γ_(W ⊕ V)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module Module.End TensorProduct
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q' : QuadraticForm ℝ (WithLp 2 (W × V))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ' : ∀ x, Q' x = Q₂ (WithLp.ofLp x).1 + Q₁ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₂ : Orientation ℝ W (Fin m))

section Action

variable (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Koszul symmetry of `CliffordAlgebra.complexProdTensor`**: the Koszul commutor for the
chirality operators `Γ_V` and `Γ_W` intertwines the graded Clifford action of `V ⊕ W` on `E ⊗ F`
with that of `W ⊕ V` on `F ⊗ E`, along any quadratic isometry `f : Q →qᵢ Q'` realizing
`(v, w) ↦ (w, v)`. -/
theorem koszulComm_complexProdTensor (f : Q →qᵢ Q')
    (hf : ∀ v w, f (WithLp.toLp 2 (v, w)) = WithLp.toLp 2 (w, v))
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] F) :
    (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁ (map (f.baseChange ℂ) a)
        ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
          (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
          (involutive_apply_complexVolume o₂ hQ₂ ρ₂) z) := by
  let e : Q.IsometryEquiv (Q₁.prod Q₂) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W), map_app' := fun x ↦ (hQ x).symm }
  let e' : Q'.IsometryEquiv (Q₂.prod Q₁) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (W × V), map_app' := fun x ↦ (hQ' x).symm }
  have hdiag : (equivOfIsometry (e'.baseChangeProd ℂ)).toAlgHom.comp (map (f.baseChange ℂ)) =
      (map (QuadraticMap.IsometryEquiv.prodComm (Q₁.baseChange ℂ)
        (Q₂.baseChange ℂ)).toIsometry).comp (equivOfIsometry (e.baseChangeProd ℂ)).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro c x
    rcases x with ⟨v, w⟩
    simp [e, e', hf, equivOfIsometry_apply, QuadraticMap.IsometryEquiv.baseChangeProd_tmul,
      QuadraticMap.IsometryEquiv.toIsometry_apply, QuadraticMap.IsometryEquiv.prodComm_toFun]
    rfl
  rw [complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl),
    complexProdTensor_eq_cliffordProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁ e' (fun _ ↦ rfl)]
  have hcomm := AlgHom.koszulComm_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
    (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
    (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
    ρ₂ (ρ₂ (complexVolume Q₂ o₂))
    (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
    (fun w ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg])
    (equivOfIsometry (e.baseChangeProd ℂ) a) z
  have hda : equivOfIsometry (e'.baseChangeProd ℂ) (map (f.baseChange ℂ) a) =
      map (QuadraticMap.IsometryEquiv.prodComm (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)).toIsometry
        (equivOfIsometry (e.baseChangeProd ℂ) a) :=
    congrArg (fun φ ↦ φ a) hdiag
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hda] using hcomm

/-- Conjugation form of `CliffordAlgebra.koszulComm_complexProdTensor`. -/
theorem conjAlgEquiv_complexProdTensor_koszulComm (f : Q →qᵢ Q')
    (hf : ∀ v w, f (WithLp.toLp 2 (v, w)) = WithLp.toLp 2 (w, v)) :
    (((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
        (involutive_apply_complexVolume o₂ hQ₂ ρ₂)).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      (complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁).comp (map (f.baseChange ℂ)) := by
  let k := (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
    (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
  apply AlgHom.ext
  intro a
  apply LinearMap.ext
  intro z
  have h := koszulComm_complexProdTensor hQ hQ' o₁ o₂ hQ₁ hn hQ₂ hm ρ₁ ρ₂ f hf a (k.symm z)
  simpa [k, LinearEquiv.conjAlgEquiv_apply] using h

/-- The Koszul commutor intertwines the product chirality `Γ_(V ⊕ W)` on `E ⊗ F` with the
product chirality `Γ_(W ⊕ V)` on `F ⊗ E`. -/
theorem koszulComm_complexProdTensor_complexVolume_prod
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)] (z : E ⊗[ℂ] F) :
    let oVW := Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm
      (o₁.prod o₂ Fact.out Fact.out)
    let oWV := Orientation.map (Fin (m + n)) (WithLp.linearEquiv 2 ℝ (W × V)).symm
      (o₂.prod o₁ Fact.out Fact.out)
    (ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
        (involutive_apply_complexVolume o₁ hQ₁ ρ₁) (involutive_apply_complexVolume o₂ hQ₂ ρ₂)
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q oVW) z) =
      complexProdTensor hQ' o₂ hQ₂ hm ρ₂ ρ₁ (complexVolume Q' oWV)
        ((ρ₁ (complexVolume Q₁ o₁)).koszulComm (ρ₂ (complexVolume Q₂ o₂))
          (involutive_apply_complexVolume o₁ hQ₁ ρ₁)
          (involutive_apply_complexVolume o₂ hQ₂ ρ₂) z) := by
  intro oVW oWV
  rw [complexProdTensor_complexVolume_prod hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm,
    complexProdTensor_complexVolume_prod hQ' o₂ hQ₂ hm ρ₂ ρ₁ o₁ hn]
  exact koszulComm_map _ _ _ _ z

end Action

section VolumeElement

/-- **Symmetry of product volume elements**: whenever `n * m` is even (in particular whenever `n`
or `m` is even), an isometric equivalence `e : Q.IsometryEquiv Q'` realizing `(v, w) ↦ (w, v)`
carries the normalized complex volume element of `V ⊕ W` to that of `W ⊕ V`. -/
theorem map_complexVolume_prodComm
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (W × V)) = m + n)]
    (hnm : Even (n * m)) (e : Q.IsometryEquiv Q')
    (he : ∀ v w, e (WithLp.toLp 2 (v, w)) = WithLp.toLp 2 (w, v)) :
    let oVW := Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm
      (o₁.prod o₂ Fact.out Fact.out)
    let oWV := Orientation.map (Fin (m + n)) (WithLp.linearEquiv 2 ℝ (W × V)).symm
      (o₂.prod o₁ Fact.out Fact.out)
    map (e.toIsometry.baseChange ℂ) (complexVolume Q oVW) = complexVolume Q' oWV := by
  intro oVW oWV
  have hnorm : ∀ x, ‖e x‖ = ‖x‖ := fun x ↦ by
    rcases x with ⟨v, w⟩
    have h := (LinearIsometryEquiv.withLpProdComm 2 ℝ V W).norm_map (WithLp.toLp 2 (v, w))
    simpa [he] using h
  have _ : Fact (finrank ℝ (WithLp 2 (W × V)) = n + m) :=
    ⟨by rw [Fact.out (p := finrank ℝ (WithLp 2 (W × V)) = m + n), add_comm]⟩
  rw [map_complexVolume oVW e hnorm]
  let φVW : (V × W) ≃ₗ[ℝ] WithLp 2 (V × W) := (WithLp.linearEquiv 2 ℝ (V × W)).symm
  let φWV : (W × V) ≃ₗ[ℝ] WithLp 2 (W × V) := (WithLp.linearEquiv 2 ℝ (W × V)).symm
  have heq : φVW.trans e.toLinearEquiv = (LinearEquiv.prodComm ℝ V W).trans φWV := by
    ext ⟨v, w⟩; simp [φVW, φWV, he]
  have hmap : oVW.map (Fin (n + m)) e.toLinearEquiv =
      Orientation.reindex ℝ (WithLp 2 (W × V)) (finCongr (add_comm m n)) oWV := by
    calc
      oVW.map (Fin (n + m)) e.toLinearEquiv
          = Orientation.map (Fin (n + m)) (φVW.trans e.toLinearEquiv)
              (o₁.prod o₂ Fact.out Fact.out) := by
            simp only [oVW, φVW, Orientation.map_trans]
      _ = Orientation.map (Fin (n + m)) ((LinearEquiv.prodComm ℝ V W).trans φWV)
              (o₁.prod o₂ Fact.out Fact.out) := by
            rw [heq]
      _ = Orientation.reindex ℝ (WithLp 2 (W × V)) (finCongr (add_comm m n)) oWV := by
            simp only [Orientation.map_trans,
              Orientation.map_prodComm_prod_of_even o₁ o₂ Fact.out Fact.out hnm,
              Orientation.map_reindex, oWV, φWV]
  rw [hmap, complexVolume_reindex oWV (add_comm m n)]

end VolumeElement

end CliffordAlgebra
