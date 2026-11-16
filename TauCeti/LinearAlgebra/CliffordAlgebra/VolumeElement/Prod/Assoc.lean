/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic

/-!
# Associativity of the graded tensor product of complex Clifford modules

Let `U`, `V`, and `W` be real inner product spaces with `U` and `V` finite-dimensional, oriented,
even-dimensional, and equipped with negative-metric quadratic forms `Q₁ u = -‖u‖²`, `Q₂ v = -‖v‖²`;
no finiteness, orientation, parity, or metric hypothesis is placed on `W`.

Equip `U ⊕ V = WithLp 2 (U × V)` with the canonical product orientation `o₁₂` and the orthogonal
sum form `Q₁₂ (u, v) = Q₁ u + Q₂ v = -‖(u, v)‖²`. Because `Γ_(U ⊕ V)` acts on `E ⊗ F` as
`Γ_U ⊗ Γ_V` (`CliffordAlgebra.complexProdTensor_complexVolume_prod`), the native tensor associator
`TensorProduct.assoc ℂ E F G` intertwines the left-associated graded Clifford action on
`(E ⊗ F) ⊗ G` with the right-associated action on `E ⊗ (F ⊗ G)` along any quadratic isometry
`f : Q_L →qᵢ Q_R` realizing `((u, v), w) ↦ (u, (v, w))`.

When `W` is also finite-dimensional and oriented, the associator isometry transports the iterated
product orientation `(o₁ × o₂) × o₃` to `o₁ × (o₂ × o₃)` (via `Orientation.map_prodAssoc_prod`)
and hence carries `Γ_((U ⊕ V) ⊕ W)` to `Γ_(U ⊕ (V ⊕ W))`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_assoc`: conjugating the left-associated
  `complexProdTensor` action by `TensorProduct.assoc` gives the right-associated action.
* `CliffordAlgebra.assoc_complexProdTensor`: pointwise intertwining on arbitrary Clifford elements
  and tensors.
* `CliffordAlgebra.map_complexVolume_prodAssoc`: reassociating `((U ⊕ V) ⊕ W)` as `(U ⊕ (V ⊕ W))`
  carries the iterated product volume element to the right-associated one.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace CliffordAlgebra

variable {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V} {Q₃ : QuadraticForm ℝ W}
  {Q₁₂ : QuadraticForm ℝ (WithLp 2 (U × V))}
  {Q₂₃ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q_L : QuadraticForm ℝ (WithLp 2 (WithLp 2 (U × V) × W))}
  {Q_R : QuadraticForm ℝ (WithLp 2 (U × WithLp 2 (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)

section Action

variable [FiniteDimensional ℝ U] {n : ℕ} [Fact (finrank ℝ U = n)]
  (o₁ : Orientation ℝ U (Fin n)) (hQ₁ : ∀ u, Q₁ u = -‖u‖ ^ 2) (hn : Even n)
  [FiniteDimensional ℝ V] {m : ℕ} [Fact (finrank ℝ V = m)]
  (o₂ : Orientation ℝ V (Fin m)) (hQ₂ : ∀ v, Q₂ v = -‖v‖ ^ 2) (hm : Even m)
  [Fact (finrank ℝ (WithLp 2 (U × V)) = n + m)]
  {E F G : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ρ₃ : CliffordAlgebra (Q₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ G)

/-- **Associativity of `CliffordAlgebra.complexProdTensor`**: conjugating the left-associated
graded tensor product action on `(E ⊗ F) ⊗ G` by the native tensor associator
`TensorProduct.assoc` yields the right-associated action on `E ⊗ (F ⊗ G)`, with the Clifford
algebra transported along any quadratic isometry `f` realizing `((u, v), w) ↦ (u, (v, w))`. No
finiteness, orientation, parity, or metric assumption is placed on `W`. -/
theorem conjAlgEquiv_complexProdTensor_assoc (f : Q_L →qᵢ Q_R)
    (hf : ∀ u v w, f (WithLp.toLp 2 (WithLp.toLp 2 (u, v), w)) =
      WithLp.toLp 2 (u, WithLp.toLp 2 (v, w))) :
    let o₁₂ := Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (U × V)).symm
      (o₁.prod o₂ Fact.out Fact.out)
    ((TensorProduct.assoc ℂ E F G).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ_L o₁₂
          (fun x ↦ by
            rw [hQ₁₂, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, neg_add]; rfl)
          (hn.add hm) (complexProdTensor hQ₁₂ o₁ hQ₁ hn ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ_R o₁ hQ₁ hn ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hm ρ₂ ρ₃)).comp (map (f.baseChange ℂ)) := by
  intro o₁₂
  apply CliffordAlgebra.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  rw [show a ⊗ₜ[ℝ] x = a • ((1 : ℂ) ⊗ₜ[ℝ] x) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, map_smul]
  congr 1
  rcases x with ⟨⟨u, v⟩, w⟩
  have hΓ := complexProdTensor_complexVolume_prod hQ₁₂ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm
  apply TensorProduct.ext_threefold'
  intro e f' g
  simp [LinearEquiv.conjAlgEquiv_apply, complexProdTensor_ι_one_tmul_toLp,
    QuadraticMap.Isometry.baseChange_tmul, hf, o₁₂, hΓ, tmul_add, add_assoc]

/-- Pointwise form of `CliffordAlgebra.conjAlgEquiv_complexProdTensor_assoc`: the native tensor
associator intertwines the left- and right-associated `complexProdTensor` actions on arbitrary
Clifford elements and tensors. -/
theorem assoc_complexProdTensor (f : Q_L →qᵢ Q_R)
    (hf : ∀ u v w, f (WithLp.toLp 2 (WithLp.toLp 2 (u, v), w)) =
      WithLp.toLp 2 (u, WithLp.toLp 2 (v, w)))
    (a : CliffordAlgebra (Q_L.baseChange ℂ)) (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    let o₁₂ := Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (U × V)).symm
      (o₁.prod o₂ Fact.out Fact.out)
    TensorProduct.assoc ℂ E F G
        (complexProdTensor hQ_L o₁₂
          (fun x ↦ by rw [hQ₁₂, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, neg_add]; rfl)
          (hn.add hm) (complexProdTensor hQ₁₂ o₁ hQ₁ hn ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ_R o₁ hQ₁ hn ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hm ρ₂ ρ₃)
        (map (f.baseChange ℂ) a) (TensorProduct.assoc ℂ E F G t) := by
  have h := congrArg (fun φ ↦ φ a (TensorProduct.assoc ℂ E F G t))
    (conjAlgEquiv_complexProdTensor_assoc hQ₁₂ hQ₂₃ hQ_L hQ_R o₁ hQ₁ hn o₂ hQ₂ hm ρ₁ ρ₂ ρ₃ f hf)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end Action

section VolumeElement

variable [FiniteDimensional ℝ U] {n : ℕ} [Fact (finrank ℝ U = n)]
  [FiniteDimensional ℝ V] {m : ℕ} [Fact (finrank ℝ V = m)]
  [FiniteDimensional ℝ W] {p : ℕ} [Fact (finrank ℝ W = p)]
  [Fact (finrank ℝ (WithLp 2 (U × V)) = n + m)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = m + p)]
  [Fact (finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = n + m + p)]
  [Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = n + (m + p))]

/-- **Associativity of product volume elements**: an isometric equivalence `e` realizing
`((u, v), w) ↦ (u, (v, w))` carries the left-associated product orientation's normalized complex
volume element to the right-associated one, for arbitrary dimensions `n`, `m`, `p` and arbitrary
quadratic forms. -/
theorem map_complexVolume_prodAssoc (o₁ : Orientation ℝ U (Fin n))
    (o₂ : Orientation ℝ V (Fin m)) (o₃ : Orientation ℝ W (Fin p))
    (e : Q_L.IsometryEquiv Q_R)
    (he : ∀ u v w, e (WithLp.toLp 2 (WithLp.toLp 2 (u, v), w)) =
      WithLp.toLp 2 (u, WithLp.toLp 2 (v, w))) :
    let o₁₂ := Orientation.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (U × V)).symm
      (o₁.prod o₂ Fact.out Fact.out)
    let o₂₃ := Orientation.map (Fin (m + p)) (WithLp.linearEquiv 2 ℝ (V × W)).symm
      (o₂.prod o₃ Fact.out Fact.out)
    let oL := Orientation.map (Fin (n + m + p))
      (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm (o₁₂.prod o₃ Fact.out Fact.out)
    let oR := Orientation.map (Fin (n + (m + p)))
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm (o₁.prod o₂₃ Fact.out Fact.out)
    map (e.toIsometry.baseChange ℂ) (complexVolume Q_L oL) = complexVolume Q_R oR := by
  intro o₁₂ o₂₃ oL oR
  have hnorm : ∀ x, ‖e x‖ = ‖x‖ := fun x ↦ by
    rcases x with ⟨⟨u, v⟩, w⟩
    have h := (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).norm_map
      (WithLp.toLp 2 (WithLp.toLp 2 (u, v), w))
    simpa [he] using h
  have _ : Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = n + m + p) :=
    ⟨by rw [Fact.out (p := finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = n + (m + p)),
      add_assoc]⟩
  rw [map_complexVolume oL e hnorm]
  let φL : (WithLp 2 (U × V) × W) ≃ₗ[ℝ] WithLp 2 (WithLp 2 (U × V) × W) :=
    (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm
  let φR : (U × WithLp 2 (V × W)) ≃ₗ[ℝ] WithLp 2 (U × WithLp 2 (V × W)) :=
    (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm
  let ψ₁ : (U × V) ≃ₗ[ℝ] WithLp 2 (U × V) := (WithLp.linearEquiv 2 ℝ (U × V)).symm
  let ψ₂ : (V × W) ≃ₗ[ℝ] WithLp 2 (V × W) := (WithLp.linearEquiv 2 ℝ (V × W)).symm
  have heq : (ψ₁.prodCongr (LinearEquiv.refl ℝ W)).trans (φL.trans e.toLinearEquiv) =
      (LinearEquiv.prodAssoc ℝ U V W).trans
        (((LinearEquiv.refl ℝ U).prodCongr ψ₂).trans φR) := by
    ext ⟨⟨u, v⟩, w⟩; simp [φL, φR, ψ₁, ψ₂, he]
  have hUV : finrank ℝ (U × V) = n + m := by
    rw [Module.finrank_prod, Fact.out (p := finrank ℝ U = n), Fact.out (p := finrank ℝ V = m)]
  have hVW : finrank ℝ (V × W) = m + p := by
    rw [Module.finrank_prod, Fact.out (p := finrank ℝ V = m), Fact.out (p := finrank ℝ W = p)]
  have h₁ : o₁₂.prod o₃ Fact.out Fact.out =
      Orientation.map (Fin (n + m + p)) (ψ₁.prodCongr (LinearEquiv.refl ℝ W))
        ((o₁.prod o₂ Fact.out Fact.out).prod o₃ hUV Fact.out) := by
    simp only [Orientation.map_prod, Orientation.map_refl, Equiv.refl_apply, o₁₂, ψ₁]
  have h₂ : o₁.prod o₂₃ Fact.out Fact.out =
      Orientation.map (Fin (n + (m + p))) ((LinearEquiv.refl ℝ U).prodCongr ψ₂)
        (o₁.prod (o₂.prod o₃ Fact.out Fact.out) Fact.out hVW) := by
    simp only [Orientation.map_prod, Orientation.map_refl, Equiv.refl_apply, o₂₃, ψ₂]
  have hmap : oL.map (Fin (n + m + p)) e.toLinearEquiv =
      Orientation.reindex ℝ (WithLp 2 (U × WithLp 2 (V × W)))
        (finCongr (add_assoc n m p).symm) oR := by
    calc
      oL.map (Fin (n + m + p)) e.toLinearEquiv
          = Orientation.map (Fin (n + m + p))
              ((ψ₁.prodCongr (LinearEquiv.refl ℝ W)).trans (φL.trans e.toLinearEquiv))
              ((o₁.prod o₂ Fact.out Fact.out).prod o₃ hUV Fact.out) := by
            simp only [oL, φL, h₁, Orientation.map_trans]
      _ = Orientation.map (Fin (n + m + p))
              ((LinearEquiv.prodAssoc ℝ U V W).trans
                (((LinearEquiv.refl ℝ U).prodCongr ψ₂).trans φR))
              ((o₁.prod o₂ Fact.out Fact.out).prod o₃ hUV Fact.out) := by
            rw [heq]
      _ = Orientation.reindex ℝ (WithLp 2 (U × WithLp 2 (V × W)))
            (finCongr (add_assoc n m p).symm) oR := by
            simp only [Orientation.map_trans, Orientation.map_prodAssoc_prod,
              Orientation.map_reindex, h₂, oR, φR]
  rw [hmap, complexVolume_reindex oR (add_assoc n m p).symm]

end VolumeElement

end CliffordAlgebra
