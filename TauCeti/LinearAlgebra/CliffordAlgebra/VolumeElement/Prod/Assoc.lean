/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.Analysis.Normed.Lp.ProdLp.QuadraticForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
-- Private: ring-generic associativity of `cliffordProdTensor` is used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Assoc

/-!
# Associativity of `complexProdTensor`

Let `U` and `V` be even-dimensional oriented real inner product spaces with `Q₁ u = -‖u‖²` and
`Q₂ v = -‖v‖²`, let `(W, Q₃)` be any real quadratic space, and let `Q₁₂` on `U ⊕ V`, `Q₂₃` on
`V ⊕ W`, `Q_L` on `(U ⊕ V) ⊕ W`, and `Q_R` on `U ⊕ (V ⊕ W)` be their `WithLp 2` orthogonal sums.

1. **Clifford-module associativity**: for the canonical product orientation `o₁₂` of `U ⊕ V`, the
   chirality of `U ⊕ V` acts on `E ⊗ F` by `Γ_U ⊗ Γ_V`
   (`CliffordAlgebra.complexProdTensor_complexVolume_of_prod`). Specializing the ring-generic
   associativity theorems `AlgHom.conjAlgEquiv_cliffordProdTensor_assoc` and
   `AlgHom.assoc_cliffordProdTensor` from
   `TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Assoc.lean` along the `WithLp` quadratic associator
   `TauCeti.withLpProdAssocIsometryEquiv`
   (`TauCeti/Analysis/Normed/Lp/ProdLp/QuadraticForm.lean`), Mathlib's
   `TensorProduct.assoc ℂ E F G : (E ⊗ F) ⊗ G ≃ₗ[ℂ] E ⊗ (F ⊗ G)` intertwines the left-associated
   and right-associated `complexProdTensor` actions for *any* third factor `(W, Q₃)`
   (`CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor` and
   `CliffordAlgebra.assoc_complexProdTensor`).
2. **Triple chirality compatibility**: when `W` is also an even-dimensional oriented real inner
   product space with `Q₃ w = -‖w‖²` (whose product orientations associate via
   `Orientation.map_withLpProdAssoc_prod` in
   `TauCeti/Analysis/Normed/Lp/ProdLp/Orientation.lean`), `TensorProduct.assoc` intertwines the
   triple product chiralities `(Γ_U ⊗ Γ_V) ⊗ Γ_W` and `Γ_U ⊗ (Γ_V ⊗ Γ_W)`
   (`CliffordAlgebra.assoc_complexProdTensor_complexVolume`).

## Main results

* `CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor` and
  `CliffordAlgebra.assoc_complexProdTensor`: associativity of `complexProdTensor`.
* `CliffordAlgebra.assoc_complexProdTensor_complexVolume`: `TensorProduct.assoc` intertwines the
  triple product chiralities.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, Definition 2.2.42.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

section Action

private theorem cliffordProdTensor_congr_left
    {M₁ M₁' M₂ E F : Type*} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₁'] [Module ℂ M₁'] [AddCommGroup M₂] [Module ℂ M₂]
    {Q₁ : QuadraticForm ℂ M₁} {Q₁' : QuadraticForm ℂ M₁'} {Q₂ : QuadraticForm ℂ M₂}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e₁ : Q₁.IsometryEquiv Q₁')
    (τ₁ : CliffordAlgebra Q₁ →ₐ[ℂ] Module.End ℂ E)
    (σ₁ : CliffordAlgebra Q₁' →ₐ[ℂ] Module.End ℂ E)
    (hτ₁ : τ₁ = σ₁.comp (equivOfIsometry e₁).toAlgHom)
    (τγ γ : Module.End ℂ E) (hγ_eq : τγ = γ)
    (hτγ : τγ * τγ = 1) (hτγ_ι : ∀ v, τγ * τ₁ (ι Q₁ v) = -(τ₁ (ι Q₁ v) * τγ))
    (hγ : γ * γ = 1) (hγσ₁ : ∀ v, γ * σ₁ (ι Q₁' v) = -(σ₁ (ι Q₁' v) * γ))
    (σ₂ : CliffordAlgebra Q₂ →ₐ[ℂ] Module.End ℂ F) :
    AlgHom.cliffordProdTensor τ₁ τγ hτγ hτγ_ι σ₂ =
      (AlgHom.cliffordProdTensor σ₁ γ hγ hγσ₁ σ₂).comp
        (equivOfIsometry (e₁.prod (.refl Q₂))).toAlgHom := by
  subst hτ₁ hγ_eq
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  simp [AlgHom.cliffordProdTensor_ι, equivOfIsometry_apply]

private theorem cliffordProdTensor_comp_equivOfIsometry_right
    {M₁ M₂ M₂' E F : Type*} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₂'] [Module ℂ M₂']
    {Q₁ : QuadraticForm ℂ M₁} {Q₂ : QuadraticForm ℂ M₂} {Q₂' : QuadraticForm ℂ M₂'}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e₂ : Q₂.IsometryEquiv Q₂')
    (σ₁ : CliffordAlgebra Q₁ →ₐ[ℂ] Module.End ℂ E) (γ : Module.End ℂ E) (hγ : γ * γ = 1)
    (hγσ₁ : ∀ v, γ * σ₁ (ι Q₁ v) = -(σ₁ (ι Q₁ v) * γ))
    (σ₂ : CliffordAlgebra Q₂' →ₐ[ℂ] Module.End ℂ F) :
    AlgHom.cliffordProdTensor σ₁ γ hγ hγσ₁ (σ₂.comp (equivOfIsometry e₂).toAlgHom) =
      (AlgHom.cliffordProdTensor σ₁ γ hγ hγσ₁ σ₂).comp
        (equivOfIsometry ((QuadraticMap.IsometryEquiv.refl Q₁).prod e₂)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  simp [AlgHom.cliffordProdTensor_ι, equivOfIsometry_apply]

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [AddCommGroup W] [Module ℝ W]
  {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V} {Q₃ : QuadraticForm ℝ W}
  {Q₁₂ : QuadraticForm ℝ (WithLp 2 (U × V))}
  {Q₂₃ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q_L : QuadraticForm ℝ (WithLp 2 (WithLp 2 (U × V) × W))}
  {Q_R : QuadraticForm ℝ (WithLp 2 (U × WithLp 2 (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_L : ∀ x, Q_L x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ_R : ∀ x, Q_R x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ U] {n₁ : ℕ} [Fact (finrank ℝ U = n₁)] (o₁ : Orientation ℝ U (Fin n₁))
  [FiniteDimensional ℝ V] {n₂ : ℕ} [Fact (finrank ℝ V = n₂)] (o₂ : Orientation ℝ V (Fin n₂))
  [Fact (finrank ℝ (WithLp 2 (U × V)) = n₁ + n₂)]
  (hQ₁ : ∀ u, Q₁ u = -‖u‖ ^ 2) (hQ₂ : ∀ v, Q₂ v = -‖v‖ ^ 2)
  (hn₁ : Even n₁) (hn₂ : Even n₂)
  {E F G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup G] [Module ℂ G]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ρ₃ : CliffordAlgebra (Q₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ G)

/-- **Associativity of `complexProdTensor` as an `AlgHom` identity**: for even-dimensional oriented
`U` and `V` with `Q₁ u = -‖u‖²`, `Q₂ v = -‖v‖²`, canonical product orientation `o₁₂` on `U ⊕ V`,
and any third factor `(W, Q₃)`, conjugating the left-associated `complexProdTensor` action on
`(E ⊗ F) ⊗ G` by `TensorProduct.assoc ℂ E F G` gives the right-associated action on `E ⊗ (F ⊗ G)`
transported along `TauCeti.withLpProdAssocIsometryEquiv`. -/
theorem conjAlgEquiv_assoc_complexProdTensor
    {o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (n₁ + n₂))}
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n₁ + n₂))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂) :
    ((TensorProduct.assoc ℂ E F G).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ_L o₁₂ (TauCeti.apply_eq_neg_norm_sq_of_withLp_prod hQ₁₂ hQ₁ hQ₂)
          (hn₁.add hn₂) (complexProdTensor hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ_R o₁ hQ₁ hn₁ ρ₁
          (complexProdTensor hQ₂₃ o₂ hQ₂ hn₂ ρ₂ ρ₃)).comp
        (CliffordAlgebra.map ((TauCeti.withLpProdAssocIsometryEquiv
          hQ₁₂ hQ₂₃ hQ_L hQ_R).toIsometry.baseChange ℂ)) := by
  have hγ₁ := map_complexVolume_mul_self o₁ hQ₁ ρ₁
  have hγ₁ρ := map_complexVolume_mul_map_ι o₁ hn₁ ρ₁
  have hγ₂ := map_complexVolume_mul_self o₂ hQ₂ ρ₂
  have hγ₂ρ := map_complexVolume_mul_map_ι o₂ hn₂ ρ₂
  have hQ₁₂_norm := TauCeti.apply_eq_neg_norm_sq_of_withLp_prod hQ₁₂ hQ₁ hQ₂
  have hvol₁₂ := complexProdTensor_complexVolume_of_prod hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂ o₂ hn₂ hQ₂ ho₁₂
  -- Mathlib's `IsometryEquiv.prod` has no `@[simp]` application lemma; its `toLinearEquiv` is
  -- `LinearEquiv.prodCongr`.
  have hp₁ (a) (b) :
      ((TauCeti.baseChangeWithLpProdIsometryEquiv hQ₁₂ ℂ).prod (.refl (Q₃.baseChange ℂ))) (a, b) =
        (TauCeti.baseChangeWithLpProdIsometryEquiv hQ₁₂ ℂ a, b) := rfl
  have hp₂ (a) (b) :
      ((QuadraticMap.IsometryEquiv.refl (Q₁.baseChange ℂ)).prod
        (TauCeti.baseChangeWithLpProdIsometryEquiv hQ₂₃ ℂ)) (a, b) =
        (a, TauCeti.baseChangeWithLpProdIsometryEquiv hQ₂₃ ℂ b) := rfl
  have hmap :
      ((equivOfIsometry (QuadraticMap.IsometryEquiv.prodAssoc
          (Q₁.baseChange ℂ) (Q₂.baseChange ℂ) (Q₃.baseChange ℂ))).toAlgHom.comp
        (equivOfIsometry ((TauCeti.baseChangeWithLpProdIsometryEquiv hQ₁₂ ℂ).prod
          (.refl (Q₃.baseChange ℂ)))).toAlgHom).comp
        (equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ_L ℂ)).toAlgHom =
      ((equivOfIsometry ((QuadraticMap.IsometryEquiv.refl (Q₁.baseChange ℂ)).prod
          (TauCeti.baseChangeWithLpProdIsometryEquiv hQ₂₃ ℂ))).toAlgHom.comp
        (equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ_R ℂ)).toAlgHom).comp
        (CliffordAlgebra.map ((TauCeti.withLpProdAssocIsometryEquiv
          hQ₁₂ hQ₂₃ hQ_L hQ_R).toIsometry.baseChange ℂ)) := by
    refine baseChange_algHom_ext Q_L fun x ↦ ?_
    rcases x with ⟨⟨u, v⟩, w⟩
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, equivOfIsometry_apply,
      TauCeti.baseChangeWithLpProdIsometryEquiv_tmul, hp₁, hp₂,
      QuadraticMap.IsometryEquiv.prodAssoc_apply, map_apply_ι,
      QuadraticMap.Isometry.baseChange_tmul, QuadraticMap.IsometryEquiv.toIsometry_apply,
      TauCeti.withLpProdAssocIsometryEquiv_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  have hL := cliffordProdTensor_congr_left
    (TauCeti.baseChangeWithLpProdIsometryEquiv hQ₁₂ ℂ)
    (complexProdTensor hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂)
    (AlgHom.cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁)) hγ₁ hγ₁ρ ρ₂)
    (complexProdTensor_def hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂)
    _ (TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (complexVolume Q₂ o₂))) hvol₁₂
    (map_complexVolume_mul_self o₁₂ hQ₁₂_norm _)
    (map_complexVolume_mul_map_ι o₁₂ (hn₁.add hn₂) _)
    (by rw [← TensorProduct.map_mul, hγ₁, hγ₂, TensorProduct.map_one])
    (AlgHom.map_mul_cliffordProdTensor_ι ρ₁ _ hγ₁ hγ₁ρ ρ₂ _ hγ₂ρ) ρ₃
  have hR := cliffordProdTensor_comp_equivOfIsometry_right
    (TauCeti.baseChangeWithLpProdIsometryEquiv hQ₂₃ ℂ)
    ρ₁ (ρ₁ (complexVolume Q₁ o₁)) hγ₁ hγ₁ρ
    (AlgHom.cliffordProdTensor ρ₂ (ρ₂ (complexVolume Q₂ o₂)) hγ₂ hγ₂ρ ρ₃)
  have hassoc := AlgHom.conjAlgEquiv_cliffordProdTensor_assoc
    ρ₁ (ρ₁ (complexVolume Q₁ o₁)) hγ₁ hγ₁ρ ρ₂ (ρ₂ (complexVolume Q₂ o₂)) hγ₂ hγ₂ρ ρ₃
  apply AlgHom.ext
  intro a
  have hmap_a := AlgHom.congr_fun hmap a
  simp only [AlgHom.comp_apply] at hmap_a ⊢
  rw [complexProdTensor_def hQ_L, AlgHom.comp_apply, hL, AlgHom.comp_apply]
  have hassoc_a := AlgHom.congr_fun hassoc
    ((equivOfIsometry ((TauCeti.baseChangeWithLpProdIsometryEquiv hQ₁₂ ℂ).prod
      (.refl (Q₃.baseChange ℂ)))).toAlgHom
      ((equivOfIsometry (TauCeti.baseChangeWithLpProdIsometryEquiv hQ_L ℂ)).toAlgHom a))
  simp only [AlgHom.comp_apply] at hassoc_a
  rw [hassoc_a, hmap_a, complexProdTensor_def hQ_R, complexProdTensor_def hQ₂₃, hR]
  rfl

/-- **Pointwise associativity of `complexProdTensor`** on every Clifford element `a` and tensor
`t : (E ⊗ F) ⊗ G`. -/
theorem assoc_complexProdTensor
    {o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (n₁ + n₂))}
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n₁ + n₂))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (a : CliffordAlgebra (Q_L.baseChange ℂ)) (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    TensorProduct.assoc ℂ E F G
        (complexProdTensor hQ_L o₁₂ (TauCeti.apply_eq_neg_norm_sq_of_withLp_prod hQ₁₂ hQ₁ hQ₂)
          (hn₁.add hn₂) (complexProdTensor hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ_R o₁ hQ₁ hn₁ ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn₂ ρ₂ ρ₃)
        (CliffordAlgebra.map
          ((TauCeti.withLpProdAssocIsometryEquiv hQ₁₂ hQ₂₃ hQ_L hQ_R).toIsometry.baseChange ℂ) a)
        (TensorProduct.assoc ℂ E F G t) := by
  have h := congrArg
    (fun φ : CliffordAlgebra (Q_L.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] (F ⊗[ℂ] G)) ↦
      φ a (TensorProduct.assoc ℂ E F G t))
    (conjAlgEquiv_assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ_L hQ_R o₁ o₂ hQ₁ hQ₂ hn₁ hn₂ ρ₁ ρ₂ ρ₃
      ho₁₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end Action

/-! ### Triple product chiralities -/

section TripleOrientation

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
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
  [FiniteDimensional ℝ U] {n₁ : ℕ} [Fact (finrank ℝ U = n₁)] (o₁ : Orientation ℝ U (Fin n₁))
  [FiniteDimensional ℝ V] {n₂ : ℕ} [Fact (finrank ℝ V = n₂)] (o₂ : Orientation ℝ V (Fin n₂))
  [FiniteDimensional ℝ W] {n₃ : ℕ} [Fact (finrank ℝ W = n₃)] (o₃ : Orientation ℝ W (Fin n₃))
  [Fact (finrank ℝ (WithLp 2 (U × V)) = n₁ + n₂)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n₂ + n₃)]
  [Fact (finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = n₁ + n₂ + n₃)]
  [Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = n₁ + (n₂ + n₃))]
  (hQ₁ : ∀ u, Q₁ u = -‖u‖ ^ 2) (hQ₂ : ∀ v, Q₂ v = -‖v‖ ^ 2)
  (hn₁ : Even n₁) (hn₂ : Even n₂)
  {E F G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup G] [Module ℂ G]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ρ₃ : CliffordAlgebra (Q₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ G)

/-- **Triple product chirality compatibility**: when `U`, `V`, `W` all have even dimensions with
negative-squared-norm forms, `TensorProduct.assoc ℂ E F G` intertwines the left-associated and
right-associated product chiralities `(Γ_U ⊗ Γ_V) ⊗ Γ_W` and `Γ_U ⊗ (Γ_V ⊗ Γ_W)`. -/
theorem assoc_complexProdTensor_complexVolume (hn₃ : Even n₃) (hQ₃ : ∀ w, Q₃ w = -‖w‖ ^ 2)
    {o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (n₁ + n₂))}
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n₁ + n₂))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    {o₂₃ : Orientation ℝ (WithLp 2 (V × W)) (Fin (n₂ + n₃))}
    (ho₂₃ : (Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n₂ + n₃))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o₂₃)
    {o_L : Orientation ℝ (WithLp 2 (WithLp 2 (U × V) × W)) (Fin (n₁ + n₂ + n₃))}
    (ho_L : (Orientation.prod o₁₂ o₃ Fact.out Fact.out).map (Fin (n₁ + n₂ + n₃))
      (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm = o_L)
    {o_R : Orientation ℝ (WithLp 2 (U × WithLp 2 (V × W))) (Fin (n₁ + (n₂ + n₃)))}
    (ho_R : (Orientation.prod o₁ o₂₃ Fact.out Fact.out).map (Fin (n₁ + (n₂ + n₃)))
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm = o_R)
    (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    TensorProduct.assoc ℂ E F G
        (complexProdTensor hQ_L o₁₂ (TauCeti.apply_eq_neg_norm_sq_of_withLp_prod hQ₁₂ hQ₁ hQ₂)
          (hn₁.add hn₂) (complexProdTensor hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂) ρ₃ (complexVolume Q_L o_L) t) =
      complexProdTensor hQ_R o₁ hQ₁ hn₁ ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn₂ ρ₂ ρ₃) (complexVolume Q_R o_R)
        (TensorProduct.assoc ℂ E F G t) := by
  rw [complexProdTensor_complexVolume_of_prod hQ_L o₁₂ _ (hn₁.add hn₂) _ ρ₃ o₃ hn₃ hQ₃ ho_L,
    complexProdTensor_complexVolume_of_prod hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂ o₂ hn₂ hQ₂ ho₁₂,
    complexProdTensor_complexVolume_of_prod hQ_R o₁ hQ₁ hn₁ ρ₁ _ o₂₃ (hn₂.add hn₃)
      (TauCeti.apply_eq_neg_norm_sq_of_withLp_prod hQ₂₃ hQ₂ hQ₃) ho_R,
    complexProdTensor_complexVolume_of_prod hQ₂₃ o₂ hQ₂ hn₂ ρ₂ ρ₃ o₃ hn₃ hQ₃ ho₂₃]
  exact (TensorProduct.map_map_assoc _ _ _ t).symm

end TripleOrientation

end CliffordAlgebra
