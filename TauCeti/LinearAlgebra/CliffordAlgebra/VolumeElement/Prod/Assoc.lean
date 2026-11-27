/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.Orientation.WithLp
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp.L2
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Assoc
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Map
import TauCeti.LinearAlgebra.LinearEquiv.Basic

/-!
# Associativity of graded tensor products of complex Clifford modules

For even-dimensional oriented real inner product spaces `(U, o₁)` and `(V, o₂)` with
`Q₁ u = -‖u‖²`, `Q₂ v = -‖v‖²`, `o₁₂` equal to `o₁.prod o₂` transported along
`(WithLp.linearEquiv 2 ℝ (U × V)).symm`, and arbitrary `(W, Q₃)`, `TensorProduct.assoc ℂ E F G`
intertwines the two iterated `CliffordAlgebra.complexProdTensor` actions along
`QuadraticMap.IsometryEquiv.withLpProdAssoc`. When `(W, o₃)` is also even-dimensional with
`Q₃ w = -‖w‖²`, it carries the left-associated product chirality to the right-associated one.

## Main results

* `CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor` and
  `CliffordAlgebra.assoc_complexProdTensor`: `TensorProduct.assoc ℂ E F G` intertwines the two
  iterated `complexProdTensor` actions along `QuadraticMap.IsometryEquiv.withLpProdAssoc` when
  `o₁₂` is `o₁.prod o₂` transported along `(WithLp.linearEquiv 2 ℝ (U × V)).symm`.
* `CliffordAlgebra.assoc_complexProdTensor_complexVolume`: for even-dimensional `(W, o₃)` with
  `Q₃ w = -‖w‖²`, `TensorProduct.assoc ℂ E F G` carries the left-associated chirality action to the
  right-associated one when `o_R` is transported from `o_L` along `LinearEquiv.withLpProdAssoc`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Chapter 2, §2.2.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V} {Q₃ : QuadraticForm ℝ W}
  {Q₁₂ : QuadraticForm ℝ (WithLp 2 (U × V))} {Q₂₃ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q_L : QuadraticForm ℝ (WithLp 2 (WithLp 2 (U × V) × W))}
  {Q_R : QuadraticForm ℝ (WithLp 2 (U × WithLp 2 (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ U] {k : ℕ} [Fact (finrank ℝ U = k)] (o₁ : Orientation ℝ U (Fin k))
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₂ : Orientation ℝ V (Fin n))
  [Fact (finrank ℝ (WithLp 2 (U × V)) = k + n)]
  (o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (k + n)))
  (hQ₁ : ∀ u, Q₁ u = -‖u‖ ^ 2) (hk : Even k)
  (hQ₂ : ∀ v, Q₂ v = -‖v‖ ^ 2) (hn : Even n)
  {E F G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup G] [Module ℂ G]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ρ₃ : CliffordAlgebra (Q₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ G)

include hQ₁ hQ₂ in
omit [Fact (finrank ℝ (WithLp 2 (U × V)) = k + n)] in
private theorem tensorProduct_map_complexVolume_mul_self :
    TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) *
        TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)) = 1 := by
  rw [← TensorProduct.map_mul, map_complexVolume_mul_self o₁ hQ₁ ρ₁,
    map_complexVolume_mul_self o₂ hQ₂ ρ₂, TensorProduct.map_one]

private theorem complexProdTensor_assoc_left
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂) :
    complexProdTensor hQ_L o₁₂ (QuadraticForm.withLpProd_eq_neg_norm_sq hQ₁₂ hQ₁ hQ₂)
        (hk.add hn) (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ =
      (AlgHom.cliffordProdTensor
        (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
          (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂)
        (TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)))
        (tensorProduct_map_complexVolume_mul_self o₁ o₂ hQ₁ hQ₂ ρ₁ ρ₂)
        (AlgHom.map_mul_cliffordProdTensor_ι ρ₁ (ρ₁ (complexVolume Q₁ o₁))
          (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁)
          ρ₂ (ρ₂ (complexVolume Q₂ o₂)) (map_complexVolume_mul_map_ι o₂ hn ρ₂))
        ρ₃).comp
        (map ((((QuadraticMap.IsometryEquiv.withLpProd hQ₁₂).baseChangeProd ℂ).toIsometry.prodMap
            (QuadraticMap.Isometry.id (Q₃.baseChange ℂ))).comp
          ((QuadraticMap.IsometryEquiv.withLpProd hQ_L).baseChangeProd ℂ).toIsometry)) := by
  set γ₁ := ρ₁ (complexVolume Q₁ o₁)
  set γ₂ := ρ₂ (complexVolume Q₂ o₂)
  set ρ₁₂_std := AlgHom.cliffordProdTensor ρ₁ γ₁
    (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂
  set e₁₂ := ((QuadraticMap.IsometryEquiv.withLpProd hQ₁₂).baseChangeProd ℂ).toIsometry
  have hγ₁₂_sq := tensorProduct_map_complexVolume_mul_self o₁ o₂ hQ₁ hQ₂ ρ₁ ρ₂
  have hγ₁₂_anti := AlgHom.map_mul_cliffordProdTensor_ι ρ₁ γ₁
    (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂ γ₂
    (map_complexVolume_mul_map_ι o₂ hn ρ₂)
  have hvol := complexProdTensor_complexVolume_of_map_prod hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂ o₂ o₁₂ hn hQ₂ ho₁₂
  have hcomp := AlgHom.cliffordProdTensor_comp_prodMap ρ₁₂_std (TensorProduct.map γ₁ γ₂)
    hγ₁₂_sq hγ₁₂_anti ρ₃ e₁₂ (QuadraticMap.Isometry.id (Q₃.baseChange ℂ))
  simp only [CliffordAlgebra.map_id, AlgHom.comp_id] at hcomp
  have hγ'ρ (v : ℂ ⊗[ℝ] WithLp 2 (U × V)) :
      TensorProduct.map γ₁ γ₂ * (ρ₁₂_std.comp (map e₁₂)) (ι (Q₁₂.baseChange ℂ) v) =
        -((ρ₁₂_std.comp (map e₁₂)) (ι (Q₁₂.baseChange ℂ) v) * TensorProduct.map γ₁ γ₂) := by
    rw [AlgHom.comp_apply, map_apply_ι]
    exact hγ₁₂_anti (e₁₂ v)
  have hL := complexProdTensor_eq_comp hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂
  rw [complexProdTensor_eq_comp,
    AlgHom.cliffordProdTensor_congr (hγ' := hγ₁₂_sq) (hγ'ρ := hγ'ρ) hL hvol rfl, ← hcomp]
  simp only [AlgHom.comp_assoc, map_comp_map]
  rfl

omit [Fact (finrank ℝ (WithLp 2 (U × V)) = k + n)] in
private theorem complexProdTensor_assoc_right :
    complexProdTensor hQ_R o₁ hQ₁ hk ρ₁ (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃) =
      (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
        (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁)
        (AlgHom.cliffordProdTensor ρ₂ (ρ₂ (complexVolume Q₂ o₂))
          (map_complexVolume_mul_self o₂ hQ₂ ρ₂)
          (map_complexVolume_mul_map_ι o₂ hn ρ₂) ρ₃)).comp
        (map (((QuadraticMap.Isometry.id (Q₁.baseChange ℂ)).prodMap
            ((QuadraticMap.IsometryEquiv.withLpProd hQ₂₃).baseChangeProd ℂ).toIsometry).comp
          ((QuadraticMap.IsometryEquiv.withLpProd hQ_R).baseChangeProd ℂ).toIsometry)) := by
  set γ₁ := ρ₁ (complexVolume Q₁ o₁)
  set γ₂ := ρ₂ (complexVolume Q₂ o₂)
  set ρ₂₃_std := AlgHom.cliffordProdTensor ρ₂ γ₂
    (map_complexVolume_mul_self o₂ hQ₂ ρ₂) (map_complexVolume_mul_map_ι o₂ hn ρ₂) ρ₃
  set e₂₃ := ((QuadraticMap.IsometryEquiv.withLpProd hQ₂₃).baseChangeProd ℂ).toIsometry
  have hcomp := AlgHom.cliffordProdTensor_comp_prodMap ρ₁ γ₁ (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
    (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂₃_std (QuadraticMap.Isometry.id (Q₁.baseChange ℂ)) e₂₃
  simp only [CliffordAlgebra.map_id, AlgHom.comp_id] at hcomp
  have hR := complexProdTensor_eq_comp hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃
  rw [complexProdTensor_eq_comp,
    AlgHom.cliffordProdTensor_congr (hγ' := map_complexVolume_mul_self o₁ hQ₁ ρ₁)
      (hγ'ρ := map_complexVolume_mul_map_ι o₁ hk ρ₁) rfl rfl hR, ← hcomp]
  simp only [AlgHom.comp_assoc, map_comp_map]
  rfl

/-- **Associativity of `complexProdTensor` (algebra-map form).** When `o₁₂` is `o₁.prod o₂`
transported along `(WithLp.linearEquiv 2 ℝ (U × V)).symm`, conjugating the left-associated action
on `(E ⊗ F) ⊗ G` by `TensorProduct.assoc ℂ E F G` gives the right-associated action on
`E ⊗ (F ⊗ G)` transported along `QuadraticMap.IsometryEquiv.withLpProdAssoc`. -/
theorem conjAlgEquiv_assoc_complexProdTensor
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂) :
    ((TensorProduct.assoc ℂ E F G).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ_L o₁₂ (QuadraticForm.withLpProd_eq_neg_norm_sq hQ₁₂ hQ₁ hQ₂)
          (hk.add hn) (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
          (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)).comp
        (map ((QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L
          hQ_R).toIsometry.baseChange ℂ)) := by
  rw [complexProdTensor_assoc_left hQ₁₂ hQ_L o₁ o₂ o₁₂ hQ₁ hk hQ₂ hn ρ₁ ρ₂ ρ₃ ho₁₂,
    complexProdTensor_assoc_right hQ₂₃ hQ_R o₁ o₂ hQ₁ hk hQ₂ hn ρ₁ ρ₂ ρ₃,
    ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_cliffordProdTensor_assoc ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂
      (ρ₂ (complexVolume Q₂ o₂)) (map_complexVolume_mul_self o₂ hQ₂ ρ₂)
      (map_complexVolume_mul_map_ι o₂ hn ρ₂) ρ₃,
    equivOfIsometry_toAlgHom]
  simp only [AlgHom.comp_assoc, map_comp_map]
  rw [QuadraticMap.IsometryEquiv.withLpProdAssoc_toIsometry_baseChange]

/-- **Associativity of `complexProdTensor` (pointwise form).** When `o₁₂` is `o₁.prod o₂`
transported along `(WithLp.linearEquiv 2 ℝ (U × V)).symm`, `TensorProduct.assoc ℂ E F G`
intertwines the two iterated `complexProdTensor` actions for every Clifford element `a` and tensor
`t : (E ⊗ F) ⊗ G`. -/
theorem assoc_complexProdTensor
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (a : CliffordAlgebra (Q_L.baseChange ℂ)) (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    (TensorProduct.assoc ℂ E F G)
        (complexProdTensor hQ_L o₁₂ (QuadraticForm.withLpProd_eq_neg_norm_sq hQ₁₂ hQ₁ hQ₂)
          (hk.add hn) (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)
        (map ((QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L
          hQ_R).toIsometry.baseChange ℂ) a)
        ((TensorProduct.assoc ℂ E F G) t) :=
  (LinearEquiv.conjAlgEquiv_toAlgHom_comp_eq_iff _ _ _).1
    (conjAlgEquiv_assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ_L hQ_R o₁ o₂ o₁₂ hQ₁ hk hQ₂ hn
      ρ₁ ρ₂ ρ₃ ho₁₂) a t

/-- **Associativity on the product chirality.** When `(W, o₃)` is also even-dimensional with
`Q₃ w = -‖w‖²` and `o_R` is obtained from the left-associated product orientation `o_L` along
`LinearEquiv.withLpProdAssoc`, `TensorProduct.assoc ℂ E F G` carries the left-associated chirality
action `(Γ_U ⊗ Γ_V) ⊗ Γ_W` to `Γ_U ⊗ (Γ_V ⊗ Γ_W)`. -/
theorem assoc_complexProdTensor_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)] (o₃ : Orientation ℝ W (Fin m))
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    (o₂₃ : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    [Fact (finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = k + n + m)]
    (o_L : Orientation ℝ (WithLp 2 (WithLp 2 (U × V) × W)) (Fin (k + n + m)))
    [Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = k + (n + m))]
    (o_R : Orientation ℝ (WithLp 2 (U × WithLp 2 (V × W))) (Fin (k + (n + m))))
    (hQ₃ : ∀ w, Q₃ w = -‖w‖ ^ 2) (hm : Even m)
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (ho₂₃ : (o₂.prod o₃ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o₂₃)
    (ho_L : (o₁₂.prod o₃ Fact.out Fact.out).map (Fin (k + n + m))
      (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm = o_L)
    (ho_R : Orientation.reindex ℝ (WithLp 2 (U × WithLp 2 (V × W))) (finCongr (add_assoc k n m))
      (o_L.map (Fin (k + n + m)) (LinearEquiv.withLpProdAssoc 2 ℝ U V W)) = o_R)
    (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    (TensorProduct.assoc ℂ E F G)
        (complexProdTensor hQ_L o₁₂ (QuadraticForm.withLpProd_eq_neg_norm_sq hQ₁₂ hQ₁ hQ₂)
          (hk.add hn) (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ (complexVolume Q_L o_L) t) =
      complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃) (complexVolume Q_R o_R)
        ((TensorProduct.assoc ℂ E F G) t) := by
  have ho_R' : (o₁.prod o₂₃ Fact.out Fact.out).map (Fin (k + (n + m)))
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm = o_R := by
    have hassoc := Orientation.map_withLpProdAssoc_prod (p := 2) o₁ o₂ o₃
      (Fact.out : finrank ℝ U = k) (Fact.out : finrank ℝ V = n) (Fact.out : finrank ℝ W = m)
    simp only [ho₁₂, ho₂₃] at hassoc
    rw [← ho_R, ← ho_L, hassoc, eq_comm, Orientation.reindex_finCongr_eq_iff]
  rw [complexProdTensor_complexVolume_of_map_prod hQ_L o₁₂
      (QuadraticForm.withLpProd_eq_neg_norm_sq hQ₁₂ hQ₁ hQ₂) (hk.add hn) _ ρ₃ o₃ o_L hm hQ₃ ho_L,
    complexProdTensor_complexVolume_of_map_prod hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂ o₂ o₁₂ hn hQ₂ ho₁₂,
    complexProdTensor_complexVolume_of_map_prod hQ_R o₁ hQ₁ hk ρ₁ _ o₂₃ o_R (hn.add hm)
      (QuadraticForm.withLpProd_eq_neg_norm_sq hQ₂₃ hQ₂ hQ₃) ho_R',
    complexProdTensor_complexVolume_of_map_prod hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃ o₃ o₂₃ hm hQ₃ ho₂₃]
  exact (TensorProduct.map_map_assoc _ _ _ t).symm

end CliffordAlgebra
