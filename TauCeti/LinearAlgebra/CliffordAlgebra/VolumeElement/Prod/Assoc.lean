/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv

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
  (hQ₁₂_norm : ∀ x, Q₁₂ x = -‖x‖ ^ 2) (hkn : Even (k + n))
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
        (complexProdTensor hQ₁₂_₃ o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ₁_₂₃ o₁ hQ₁ hk ρ₁
          (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)).comp
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdAssoc
          hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ)).toAlgHom := by
  have hvol := complexProdTensor_complexVolume_of_map_prod hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂ o₂ o₁₂ hQ₂ hn ho₁₂
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun u ↦ ?_
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    have hx : z ⊗ₜ[ℝ] x = z • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2
        (WithLp.toLp 2 ((WithLp.ofLp (WithLp.ofLp x).1).1, (WithLp.ofLp (WithLp.ofLp x).1).2),
          (WithLp.ofLp x).2)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
    rw [hx, map_smul, map_smul]
    refine TensorProduct.ext' fun e y ↦ ?_
    induction y using TensorProduct.inductionOn with
    | tmul f g =>
      simp [LinearEquiv.conjAlgEquiv_apply, equivOfIsometry_apply,
        complexProdTensor_ι_one_tmul_toLp, hvol, tmul_add, add_assoc]
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Applied form of `CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor`: `TensorProduct.assoc`
intertwines the two iterated `complexProdTensor` actions on every Clifford element and tensor. -/
theorem assoc_complexProdTensor
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (a : CliffordAlgebra (Q₁₂_₃.baseChange ℂ)) (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    TensorProduct.assoc ℂ E F G
        (complexProdTensor hQ₁₂_₃ o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ₁_₂₃ o₁ hQ₁ hk ρ₁ (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdAssoc
          hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ) a)
        (TensorProduct.assoc ℂ E F G t) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using LinearMap.congr_fun
    (AlgHom.congr_fun (conjAlgEquiv_assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ o₁ hQ₁ hk
      o₂ hQ₂ hn o₁₂ hQ₁₂_norm hkn ρ₁ ρ₂ ρ₃ ho₁₂) a)
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
        (complexProdTensor hQ₁₂_₃ o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ (complexVolume Q₁₂_₃ o₁₂_₃)) =
      complexProdTensor hQ₁_₂₃ o₁ hQ₁ hk ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃) (complexVolume Q₁_₂₃ o₁_₂₃) := by
  subst o₁₂ o₂₃ o₁₂_₃ o₁_₂₃
  have hnorm : ∀ x,
      ‖QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ x‖ = ‖x‖ := fun x ↦ by
    simpa using (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).norm_map x
  have hUV : finrank ℝ (U × V) = k + n := by
    rw [Module.finrank_prod, Fact.out (p := finrank ℝ U = k), Fact.out (p := finrank ℝ V = n)]
  have hVW : finrank ℝ (V × W) = n + m := by
    rw [Module.finrank_prod, Fact.out (p := finrank ℝ V = n), Fact.out (p := finrank ℝ W = m)]
  have horient :
      Orientation.map (Fin (k + n + m))
          (QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).toLinearEquiv
          ((Orientation.prod
              ((Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (k + n))
                (WithLp.linearEquiv 2 ℝ (U × V)).symm) o₃ Fact.out Fact.out).map (Fin (k + n + m))
            (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm) =
        Orientation.reindex ℝ (WithLp 2 (U × WithLp 2 (V × W))) (finCongr (add_assoc k n m).symm)
          ((Orientation.prod o₁ ((Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n + m))
              (WithLp.linearEquiv 2 ℝ (V × W)).symm) Fact.out Fact.out).map (Fin (k + (n + m)))
            (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm) := by
    have hstep1 : Orientation.map (Fin (k + n + m))
        ((WithLp.linearEquiv 2 ℝ (U × V)).prodCongr (LinearEquiv.refl ℝ W))
        (Orientation.prod ((Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (k + n))
          (WithLp.linearEquiv 2 ℝ (U × V)).symm) o₃ Fact.out Fact.out) =
        Orientation.prod (Orientation.prod o₁ o₂ Fact.out Fact.out) o₃ hUV Fact.out := by
      rw [Orientation.map_prod]; congr 1 <;> simp [← Orientation.map_symm]
    have hstep2 : Orientation.map (Fin (k + (n + m)))
        ((LinearEquiv.refl ℝ U).prodCongr (WithLp.linearEquiv 2 ℝ (V × W)).symm)
        (Orientation.prod o₁ (Orientation.prod o₂ o₃ Fact.out Fact.out) Fact.out hVW) =
        Orientation.prod o₁ ((Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n + m))
          (WithLp.linearEquiv 2 ℝ (V × W)).symm) Fact.out Fact.out := by
      rw [Orientation.map_prod]; congr 1; simp
    simp only [QuadraticMap.IsometryEquiv.toLinearEquiv_withLpProdAssoc, Orientation.map_trans]
    rw [← Orientation.map_symm (Fin (k + n + m)) (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)),
      Equiv.apply_symm_apply, hstep1,
      Orientation.map_prodAssoc_prod o₁ o₂ o₃ Fact.out Fact.out Fact.out,
      Orientation.map_reindex, Orientation.map_reindex, hstep2]
  refine LinearMap.ext fun t ↦ ?_
  rw [LinearEquiv.conj_apply_apply,
    assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ o₁ hQ₁ hk o₂ hQ₂ hn _ hQ₁₂_norm hkn
      ρ₁ ρ₂ ρ₃ rfl _ ((TensorProduct.assoc ℂ E F G).symm t),
    LinearEquiv.apply_symm_apply, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume_of_eq _ _ hnorm (add_assoc k n m), horient,
    Orientation.reindex_finCongr_reindex_finCongr]
  simp [finCongr_refl, Orientation.reindex_refl]

end CliffordAlgebra
