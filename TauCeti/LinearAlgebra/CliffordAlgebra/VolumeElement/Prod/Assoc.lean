/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Assoc

/-!
# Associativity of `CliffordAlgebra.complexProdTensor`

For even-dimensional oriented real inner product spaces `U` and `V` with `Q₁ u = -‖u‖²` and
`Q₂ v = -‖v‖²`, any real inner product space `W` with form `Q₃`, and the ordered product orientation
`o₁₂` on `U ⊕ V`, the chirality of `U ⊕ V` on `E ⊗ F` is `Γ_U ⊗ Γ_V`. Consequently:

* `CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor` and
  `CliffordAlgebra.assoc_complexProdTensor`: `TensorProduct.assoc ℂ E F G` intertwines the two
  iterated `complexProdTensor` representations along `QuadraticMap.IsometryEquiv.withLpProdAssoc`.
* `CliffordAlgebra.conj_assoc_complexProdTensor_complexVolume`: `TensorProduct.assoc` conjugates the
  left-associated action of `complexVolume` to the right-associated one for the iterated product
  orientations.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

variable {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {k n : ℕ} [Fact (finrank ℝ U = k)] [Fact (finrank ℝ V = n)]
  [Fact (finrank ℝ (WithLp 2 (U × V)) = k + n)]
  {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V} {Q₃ : QuadraticForm ℝ W}
  {Q₁₂ : QuadraticForm ℝ (WithLp 2 (U × V))} {Q₂₃ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q₁₂_₃ : QuadraticForm ℝ (WithLp 2 (WithLp 2 (U × V) × W))}
  {Q₁_₂₃ : QuadraticForm ℝ (WithLp 2 (U × WithLp 2 (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ U (Fin k)) (hQ₁ : ∀ u, Q₁ u = -‖u‖ ^ 2) (hk : Even k)
  (o₂ : Orientation ℝ V (Fin n)) (hQ₂ : ∀ v, Q₂ v = -‖v‖ ^ 2) (hn : Even n)
  (o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (k + n)))
  {E F G : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ρ₃ : CliffordAlgebra (Q₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ G)

/-- **Associativity of `CliffordAlgebra.complexProdTensor`**: when `U` and `V` are even-dimensional
with `Q₁ u = -‖u‖²` and `Q₂ v = -‖v‖²` and `U ⊕ V` carries the ordered product orientation `o₁₂`,
conjugating `(complexProdTensor ρ₁ ρ₂) ⊗̂ ρ₃` by `TensorProduct.assoc ℂ E F G` gives
`ρ₁ ⊗̂ (complexProdTensor ρ₂ ρ₃)` transported along `withLpProdAssoc`. -/
theorem conjAlgEquiv_assoc_complexProdTensor
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂) :
    ((TensorProduct.assoc ℂ E F G).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ₁₂_₃ o₁₂
          (fun x ↦ by
            rw [hQ₁₂ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd]
            ring) (hk.add hn)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ₁_₂₃ o₁ hQ₁ hk ρ₁
          (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)).comp
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdAssoc
          hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ)).toAlgHom := by
  have hvol := complexProdTensor_complexVolume_of_map_prod hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂ o₂ o₁₂ hn ho₁₂
  let fL := equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ₁₂_₃).baseChangeProd ℂ)
  let fR := equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ₁_₂₃).baseChangeProd ℂ)
  let fA := equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdAssoc
    hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ)
  let gL := equivOfIsometry
    (((QuadraticMap.IsometryEquiv.withLpProd hQ₁₂).baseChangeProd ℂ).prod
      (QuadraticMap.IsometryEquiv.refl (Q₃.baseChange ℂ)))
  let gR := equivOfIsometry
    ((QuadraticMap.IsometryEquiv.refl (Q₁.baseChange ℂ)).prod
      ((QuadraticMap.IsometryEquiv.withLpProd hQ₂₃).baseChangeProd ℂ))
  have hLHS :
      complexProdTensor hQ₁₂_₃ o₁₂
          (fun x ↦ by
            rw [hQ₁₂ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd]
            ring) (hk.add hn)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ =
        (AlgHom.cliffordProdTensor
            (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
              (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂)
            (TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂)))
            (by rw [← TensorProduct.map_mul, map_complexVolume_mul_self o₁ hQ₁ ρ₁,
              map_complexVolume_mul_self o₂ hQ₂ ρ₂, TensorProduct.map_one])
            (AlgHom.map_mul_cliffordProdTensor_ι ρ₁ (ρ₁ (complexVolume Q₁ o₁))
              (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂
              (ρ₂ (complexVolume Q₂ o₂)) (map_complexVolume_mul_map_ι o₂ hn ρ₂))
            ρ₃).comp (gL.toAlgHom.comp fL.toAlgHom) := by
    rw [complexProdTensor_eq_comp]
    refine CliffordAlgebra.hom_ext <| LinearMap.ext fun u ↦ ?_
    induction u using TensorProduct.inductionOn with
    | tmul z x =>
      simp [fL, gL, equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply,
        AlgHom.cliffordProdTensor_ι, hvol]
      simp [complexProdTensor_eq_comp, equivOfIsometry_apply,
        QuadraticMap.IsometryEquiv.toIsometry_apply, AlgHom.cliffordProdTensor_ι]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hRHS :
      complexProdTensor hQ₁_₂₃ o₁ hQ₁ hk ρ₁ (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃) =
        (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
            (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁)
            (AlgHom.cliffordProdTensor ρ₂ (ρ₂ (complexVolume Q₂ o₂))
              (map_complexVolume_mul_self o₂ hQ₂ ρ₂)
              (map_complexVolume_mul_map_ι o₂ hn ρ₂) ρ₃)).comp
          (gR.toAlgHom.comp fR.toAlgHom) := by
    rw [complexProdTensor_eq_comp]
    refine CliffordAlgebra.hom_ext <| LinearMap.ext fun u ↦ ?_
    induction u using TensorProduct.inductionOn with
    | tmul z x =>
      simp [fR, gR, equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply,
        AlgHom.cliffordProdTensor_ι, complexProdTensor_eq_comp]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hdiag :
      (equivOfIsometry (QuadraticMap.IsometryEquiv.prodAssoc
          (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (Q₃.baseChange ℂ))).toAlgHom.comp
          (gL.toAlgHom.comp fL.toAlgHom) =
        (gR.toAlgHom.comp fR.toAlgHom).comp fA.toAlgHom := by
    refine CliffordAlgebra.hom_ext <| LinearMap.ext fun u ↦ ?_
    induction u using TensorProduct.inductionOn with
    | tmul z x =>
      simp [fL, fR, fA, gL, gR, equivOfIsometry_apply, QuadraticMap.IsometryEquiv.toIsometry_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [hLHS, hRHS, ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_cliffordProdTensor_assoc ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁)
      ρ₂ (ρ₂ (complexVolume Q₂ o₂)) (map_complexVolume_mul_self o₂ hQ₂ ρ₂)
      (map_complexVolume_mul_map_ι o₂ hn ρ₂) ρ₃,
    AlgHom.comp_assoc, hdiag, ← AlgHom.comp_assoc]

/-- Applied form of `CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor`: `TensorProduct.assoc`
intertwines the two iterated `complexProdTensor` actions on every Clifford element and tensor. -/
theorem assoc_complexProdTensor
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (a : CliffordAlgebra (Q₁₂_₃.baseChange ℂ)) (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    TensorProduct.assoc ℂ E F G
        (complexProdTensor hQ₁₂_₃ o₁₂
          (fun x ↦ by
            rw [hQ₁₂ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd]
            ring) (hk.add hn)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ₁_₂₃ o₁ hQ₁ hk ρ₁ (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdAssoc
          hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ) a)
        (TensorProduct.assoc ℂ E F G t) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using LinearMap.congr_fun
    (AlgHom.congr_fun (conjAlgEquiv_assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ o₁ hQ₁ hk
      o₂ hQ₂ hn o₁₂ ρ₁ ρ₂ ρ₃ ho₁₂) a)
    (TensorProduct.assoc ℂ E F G t)

/-- **Compatibility of `TensorProduct.assoc` with the product volume elements**: for oriented
`U`, `V`, `W` of dimensions `k`, `n`, `m` (`k`, `n` even) and the iterated `Orientation.prod`
orientations `o₁₂_₃` and `o₁_₂₃`, `TensorProduct.assoc ℂ E F G` conjugates the action of
`complexVolume Q₁₂_₃ o₁₂_₃` to that of `complexVolume Q₁_₂₃ o₁_₂₃`. -/
theorem conj_assoc_complexProdTensor_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    [Fact (finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = k + n + m)]
    [Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = k + (n + m))]
    (o₃ : Orientation ℝ W (Fin m)) (o₂₃ : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    (o₁₂_₃ : Orientation ℝ (WithLp 2 (WithLp 2 (U × V) × W)) (Fin (k + n + m)))
    (o₁_₂₃ : Orientation ℝ (WithLp 2 (U × WithLp 2 (V × W))) (Fin (k + (n + m))))
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (ho₂₃ : (Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o₂₃)
    (ho₁₂_₃ : (Orientation.prod o₁₂ o₃ Fact.out Fact.out).map (Fin (k + n + m))
      (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm = o₁₂_₃)
    (ho₁_₂₃ : (Orientation.prod o₁ o₂₃ Fact.out Fact.out).map (Fin (k + (n + m)))
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm = o₁_₂₃) :
    (TensorProduct.assoc ℂ E F G).conj
        (complexProdTensor hQ₁₂_₃ o₁₂
          (fun x ↦ by
            rw [hQ₁₂ x, hQ₁, hQ₂, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd]
            ring) (hk.add hn)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ (complexVolume Q₁₂_₃ o₁₂_₃)) =
      complexProdTensor hQ₁_₂₃ o₁ hQ₁ hk ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃) (complexVolume Q₁_₂₃ o₁_₂₃) := by
  subst o₁₂ o₂₃ o₁₂_₃ o₁_₂₃
  exact conj_complexVolume_of_conjAlgEquiv_comp
    (conjAlgEquiv_assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ o₁ hQ₁ hk o₂ hQ₂ hn _ ρ₁ ρ₂ ρ₃
      rfl)
    (equivOfIsometry_withLpProdAssoc_complexVolume hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ o₁ o₂ o₃)

end CliffordAlgebra
