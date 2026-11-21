/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Orientation
public import TauCeti.LinearAlgebra.Orientation.WithLp
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Assoc

/-!
# Associativity of graded tensor products of complex Clifford modules

For even-dimensional oriented real inner product spaces `(U, o₁)` and `(V, o₂)` with
`Q₁ u = -‖u‖²`, `Q₂ v = -‖v‖²`, and arbitrary `(W, Q₃)`, `TensorProduct.assoc ℂ E F G` intertwines
the two iterated `CliffordAlgebra.complexProdTensor` actions along
`QuadraticMap.IsometryEquiv.withLpProdAssoc`. When `(W, o₃)` is also even-dimensional with
`Q₃ w = -‖w‖²`, it carries the left-associated product chirality to the right-associated one.

## Main results

* `CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor` and
  `CliffordAlgebra.assoc_complexProdTensor`: `TensorProduct.assoc ℂ E F G` intertwines the two
  iterated `complexProdTensor` actions along `QuadraticMap.IsometryEquiv.withLpProdAssoc`.
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

private theorem cliffordProdTensor_comp_prodMap {R M₁ M₂ M₁' M₂' E F : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₁'] [Module R M₁'] [AddCommGroup M₂'] [Module R M₂']
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₁' : QuadraticForm R M₁'} {Q₂' : QuadraticForm R M₂'}
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (ρ₁ : CliffordAlgebra Q₁' →ₐ[R] Module.End R E) (γ : Module.End R E)
    (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁' v) = -(ρ₁ (ι Q₁' v) * γ))
    (ρ₂ : CliffordAlgebra Q₂' →ₐ[R] Module.End R F)
    (f₁ : Q₁ →qᵢ Q₁') (f₂ : Q₂ →qᵢ Q₂') :
    (AlgHom.cliffordProdTensor ρ₁ γ hγ hγρ ρ₂).comp (map (f₁.prodMap f₂)) =
      AlgHom.cliffordProdTensor (ρ₁.comp (map f₁)) γ hγ (fun v ↦ by simpa using hγρ (f₁ v))
        (ρ₂.comp (map f₂)) := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun ⟨v₁, v₂⟩ ↦ ?_
  simp [AlgHom.cliffordProdTensor_ι]

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
  (hQ₁₂_norm : ∀ x, Q₁₂ x = -‖x‖ ^ 2) (hkn : Even (k + n))
  {E F G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup G] [Module ℂ G]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ρ₃ : CliffordAlgebra (Q₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ G)

/-- **Associativity of `complexProdTensor` (algebra-map form).** Conjugating the left-associated
action on `(E ⊗ F) ⊗ G` by `TensorProduct.assoc ℂ E F G` gives the right-associated action on
`E ⊗ (F ⊗ G)` transported along `QuadraticMap.IsometryEquiv.withLpProdAssoc`. -/
theorem conjAlgEquiv_assoc_complexProdTensor
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂) :
    ((TensorProduct.assoc ℂ E F G).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ_L o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
          (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)).comp
        (map ((QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L
          hQ_R).toIsometry.baseChange ℂ)) := by
  have hvol := complexProdTensor_complexVolume_of_map_prod hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂ o₂ o₁₂ hn hQ₂ ho₁₂
  set γ₁ := ρ₁ (complexVolume Q₁ o₁)
  set γ₂ := ρ₂ (complexVolume Q₂ o₂)
  set ρ₁₂_std := AlgHom.cliffordProdTensor ρ₁ γ₁
    (map_complexVolume_mul_self o₁ hQ₁ ρ₁) (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂
  set ρ₂₃_std := AlgHom.cliffordProdTensor ρ₂ γ₂
    (map_complexVolume_mul_self o₂ hQ₂ ρ₂) (map_complexVolume_mul_map_ι o₂ hn ρ₂) ρ₃
  set e₁₂ := ((QuadraticMap.IsometryEquiv.withLpProd hQ₁₂).baseChangeProd ℂ).toIsometry
  set e₂₃ := ((QuadraticMap.IsometryEquiv.withLpProd hQ₂₃).baseChangeProd ℂ).toIsometry
  set eL := ((QuadraticMap.IsometryEquiv.withLpProd hQ_L).baseChangeProd ℂ).toIsometry
  set eR := ((QuadraticMap.IsometryEquiv.withLpProd hQ_R).baseChangeProd ℂ).toIsometry
  have hL (x : CliffordAlgebra (Q_L.baseChange ℂ)) :
      complexProdTensor hQ_L o₁₂ hQ₁₂_norm hkn (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ x =
        AlgHom.cliffordProdTensor ρ₁₂_std (TensorProduct.map γ₁ γ₂)
          (by rw [← TensorProduct.map_mul, map_complexVolume_mul_self o₁ hQ₁ ρ₁,
            map_complexVolume_mul_self o₂ hQ₂ ρ₂, TensorProduct.map_one])
          (AlgHom.map_mul_cliffordProdTensor_ι ρ₁ γ₁ (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
            (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂ γ₂ (map_complexVolume_mul_map_ι o₂ hn ρ₂))
          ρ₃ (map ((e₁₂.prodMap (QuadraticMap.Isometry.id (Q₃.baseChange ℂ))).comp eL) x) := by
    have hcongrL :
        ∀ (ρ' : CliffordAlgebra (Q₁₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] F))
          (γ' : Module.End ℂ (E ⊗[ℂ] F)) (h1 : γ' * γ' = 1)
          (h2 : ∀ v, γ' * ρ' (ι (Q₁₂.baseChange ℂ) v) = -(ρ' (ι (Q₁₂.baseChange ℂ) v) * γ')),
          ρ' = ρ₁₂_std.comp (map e₁₂) →
          γ' = TensorProduct.map γ₁ γ₂ →
          AlgHom.cliffordProdTensor ρ' γ' h1 h2 ρ₃ =
            AlgHom.cliffordProdTensor (ρ₁₂_std.comp (map e₁₂)) (TensorProduct.map γ₁ γ₂)
              (by rw [← TensorProduct.map_mul, map_complexVolume_mul_self o₁ hQ₁ ρ₁,
                map_complexVolume_mul_self o₂ hQ₂ ρ₂, TensorProduct.map_one])
              (fun v ↦ by
                simpa using AlgHom.map_mul_cliffordProdTensor_ι ρ₁ γ₁
                  (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
                  (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂ γ₂
                  (map_complexVolume_mul_map_ι o₂ hn ρ₂) (e₁₂ v))
              (ρ₃.comp (map (QuadraticMap.Isometry.id (Q₃.baseChange ℂ)))) := by
      rintro ρ' γ' h1 h2 rfl rfl
      simp [map_id]
    have hcompL := cliffordProdTensor_comp_prodMap ρ₁₂_std (TensorProduct.map γ₁ γ₂)
      (by rw [← TensorProduct.map_mul, map_complexVolume_mul_self o₁ hQ₁ ρ₁,
        map_complexVolume_mul_self o₂ hQ₂ ρ₂, TensorProduct.map_one])
      (AlgHom.map_mul_cliffordProdTensor_ι ρ₁ γ₁ (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
        (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂ γ₂ (map_complexVolume_mul_map_ι o₂ hn ρ₂))
      ρ₃ e₁₂ (QuadraticMap.Isometry.id (Q₃.baseChange ℂ))
    rw [complexProdTensor_eq_comp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      hcongrL _ _ _ _ (complexProdTensor_eq_comp hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) hvol,
      ← AlgHom.congr_fun hcompL _, AlgHom.comp_apply, equivOfIsometry_apply,
      ← AlgHom.comp_apply (map _), map_comp_map]
  have hR (x : CliffordAlgebra (Q_R.baseChange ℂ)) :
      complexProdTensor hQ_R o₁ hQ₁ hk ρ₁ (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃) x =
        AlgHom.cliffordProdTensor ρ₁ γ₁ (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
          (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂₃_std
          (map (((QuadraticMap.Isometry.id (Q₁.baseChange ℂ)).prodMap e₂₃).comp eR) x) := by
    have hcongrR :
        ∀ (ρ' : CliffordAlgebra (Q₂₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (F ⊗[ℂ] G)),
          ρ' = ρ₂₃_std.comp (map e₂₃) →
          AlgHom.cliffordProdTensor ρ₁ γ₁ (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
            (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ' =
            AlgHom.cliffordProdTensor (ρ₁.comp (map (QuadraticMap.Isometry.id (Q₁.baseChange ℂ))))
              γ₁ (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
              (fun v ↦ by simpa using map_complexVolume_mul_map_ι o₁ hk ρ₁ v)
              (ρ₂₃_std.comp (map e₂₃)) := by
      rintro ρ' rfl
      simp [map_id]
    have hcompR := cliffordProdTensor_comp_prodMap ρ₁ γ₁ (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
      (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂₃_std
      (QuadraticMap.Isometry.id (Q₁.baseChange ℂ)) e₂₃
    rw [complexProdTensor_eq_comp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      hcongrR _ (complexProdTensor_eq_comp hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃),
      ← AlgHom.congr_fun hcompR _, AlgHom.comp_apply, equivOfIsometry_apply,
      ← AlgHom.comp_apply (map _), map_comp_map]
  have hisom :
      (QuadraticMap.IsometryEquiv.prodAssoc (Q₁.baseChange ℂ) (Q₂.baseChange ℂ)
        (Q₃.baseChange ℂ)).toIsometry.comp
          ((e₁₂.prodMap (QuadraticMap.Isometry.id (Q₃.baseChange ℂ))).comp eL) =
        (((QuadraticMap.Isometry.id (Q₁.baseChange ℂ)).prodMap e₂₃).comp eR).comp
          ((QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L
            hQ_R).toIsometry.baseChange ℂ) := by
    refine QuadraticMap.Isometry.ext fun y ↦ ?_
    induction y using TensorProduct.inductionOn with
    | tmul c x =>
      rcases x with ⟨⟨⟨⟨u, v⟩⟩, w⟩⟩
      simp [e₁₂, e₂₃, eL, eR, QuadraticMap.Isometry.baseChange_tmul,
        QuadraticMap.IsometryEquiv.baseChangeProd_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine AlgHom.ext fun a ↦ ?_
  have hassoc := AlgHom.congr_fun
    (AlgHom.conjAlgEquiv_cliffordProdTensor_assoc ρ₁ γ₁ (map_complexVolume_mul_self o₁ hQ₁ ρ₁)
      (map_complexVolume_mul_map_ι o₁ hk ρ₁) ρ₂ γ₂ (map_complexVolume_mul_self o₂ hQ₂ ρ₂)
      (map_complexVolume_mul_map_ι o₂ hn ρ₂) ρ₃)
    (map ((e₁₂.prodMap (QuadraticMap.Isometry.id (Q₃.baseChange ℂ))).comp eL) a)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hassoc ⊢
  rw [hL, hR, hassoc, equivOfIsometry_apply, ← AlgHom.comp_apply (map _),
    ← AlgHom.comp_apply (map _), map_comp_map, map_comp_map, hisom]

/-- **Associativity of `complexProdTensor` (pointwise form).** `TensorProduct.assoc ℂ E F G`
intertwines the two iterated `complexProdTensor` actions for every Clifford element `a` and tensor
`t : (E ⊗ F) ⊗ G`. -/
theorem assoc_complexProdTensor
    (ho₁₂ : (o₁.prod o₂ Fact.out Fact.out).map (Fin (k + n))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (a : CliffordAlgebra (Q_L.baseChange ℂ)) (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    (TensorProduct.assoc ℂ E F G)
        (complexProdTensor hQ_L o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃)
        (map ((QuadraticMap.IsometryEquiv.withLpProdAssoc hQ₁₂ hQ₂₃ hQ_L
          hQ_R).toIsometry.baseChange ℂ) a)
        ((TensorProduct.assoc ℂ E F G) t) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg
    (fun φ : CliffordAlgebra (Q_L.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] (F ⊗[ℂ] G)) ↦
      φ a ((TensorProduct.assoc ℂ E F G) t))
    (conjAlgEquiv_assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ_L hQ_R o₁ o₂ o₁₂ hQ₁ hk hQ₂ hn
      hQ₁₂_norm hkn ρ₁ ρ₂ ρ₃ ho₁₂)

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
    (hQ₂₃_norm : ∀ y, Q₂₃ y = -‖y‖ ^ 2) (hnm : Even (n + m))
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
        (complexProdTensor hQ_L o₁₂ hQ₁₂_norm hkn
          (complexProdTensor hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂) ρ₃ (complexVolume Q_L o_L) t) =
      complexProdTensor hQ_R o₁ hQ₁ hk ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃) (complexVolume Q_R o_R)
        ((TensorProduct.assoc ℂ E F G) t) := by
  have ho_R' : (o₁.prod o₂₃ Fact.out Fact.out).map (Fin (k + (n + m)))
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm = o_R := by
    have hassoc := Orientation.map_withLpProdAssoc_prod (p := 2) o₁ o₂ o₃
      (Fact.out : finrank ℝ U = k) (Fact.out : finrank ℝ V = n) (Fact.out : finrank ℝ W = m)
    simp only [ho₁₂, ho₂₃] at hassoc
    rw [← ho_R, ← ho_L, hassoc, Orientation.reindex_finCongr_reindex_finCongr, finCongr_refl,
      Orientation.reindex_refl, Equiv.refl_apply]
  rw [complexProdTensor_complexVolume_of_map_prod hQ_L o₁₂ hQ₁₂_norm hkn _ ρ₃ o₃ o_L hm hQ₃ ho_L,
    complexProdTensor_complexVolume_of_map_prod hQ₁₂ o₁ hQ₁ hk ρ₁ ρ₂ o₂ o₁₂ hn hQ₂ ho₁₂,
    complexProdTensor_complexVolume_of_map_prod hQ_R o₁ hQ₁ hk ρ₁ _ o₂₃ o_R hnm hQ₂₃_norm ho_R',
    complexProdTensor_complexVolume_of_map_prod hQ₂₃ o₂ hQ₂ hn ρ₂ ρ₃ o₃ o₂₃ hm hQ₃ ho₂₃]
  exact (TensorProduct.map_map_assoc _ _ _ t).symm

end CliffordAlgebra
