/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Unit

/-!
# Associativity of `complexProdTensor`

Let `U`, `V`, `W` be real inner product spaces with orthogonal-sum quadratic forms `Q₁₂` on
`U ⊕ V`, `Q₂₃` on `V ⊕ W`, `Q_L` on `(U ⊕ V) ⊕ W`, and `Q_R` on `U ⊕ (V ⊕ W)` (`WithLp 2`).

1. **Metric associator**: `LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W` induces a quadratic
   isometric equivalence `CliffordAlgebra.withLpProdAssocIsometry : Q_L.IsometryEquiv Q_R`.
2. **Clifford-module associativity**: when `U` and `V` are even-dimensional oriented spaces with
   `Q₁ u = -‖u‖²` and `Q₂ v = -‖v‖²`, and `o₁₂` is the canonical product orientation of `U ⊕ V`,
   the chirality of `U ⊕ V` acts on `E ⊗ F` by `Γ_U ⊗ Γ_V`
   (`CliffordAlgebra.complexProdTensor_complexVolume_of_prod`). Consequently, Mathlib's
   `TensorProduct.assoc ℂ E F G : (E ⊗ F) ⊗ G ≃ₗ[ℂ] E ⊗ (F ⊗ G)` intertwines the left-associated
   and right-associated `complexProdTensor` actions along `withLpProdAssocIsometry` for *any* third
   factor `(W, Q₃)` (`CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor` and
   `CliffordAlgebra.assoc_complexProdTensor`).
3. **Orientation and triple chirality compatibility**: when `W` also has finite dimension `n₃` with
   orientation `o₃`, `withLpProdAssoc` carries the iterated product orientation `(o₁ × o₂) × o₃` to
    `o₁ × (o₂ × o₃)` reindexed along `n₁ + n₂ + n₃ = n₁ + (n₂ + n₃)`
    (`Orientation.map_withLpProdAssoc_prod`), and for even `n₃` with `Q₃ w = -‖w‖²`,
    `TensorProduct.assoc` intertwines the triple product chiralities
    (`CliffordAlgebra.assoc_complexProdTensor_complexVolume`).

## Main definitions

* `CliffordAlgebra.withLpProdAssocIsometry`: `Q_L.IsometryEquiv Q_R` via
  `LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_assoc_complexProdTensor` and
  `CliffordAlgebra.assoc_complexProdTensor`: associativity of `complexProdTensor`.
* `Orientation.map_withLpProdAssoc_prod`: associativity of `L²` product orientations.
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

section Isometry

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

/-- `LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W` as a quadratic isometric equivalence
`Q_L.IsometryEquiv Q_R` between `(U ⊕ V) ⊕ W` and `U ⊕ (V ⊕ W)`. -/
def withLpProdAssocIsometry : Q_L.IsometryEquiv Q_R where
  toLinearEquiv := (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv
  map_app' x := by
    simp only [hQ_R, hQ₂₃, hQ_L, hQ₁₂, WithLp.ofLp_fst, WithLp.ofLp_snd, add_assoc]
    rfl

/-- Evaluation of `CliffordAlgebra.withLpProdAssocIsometry` on a triple `L²` vector. -/
@[simp]
theorem withLpProdAssocIsometry_apply (x : WithLp 2 (WithLp 2 (U × V) × W)) :
    withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ_L hQ_R x =
      WithLp.toLp 2 (x.fst.fst, WithLp.toLp 2 (x.fst.snd, x.snd)) :=
  (rfl)

/-- `CliffordAlgebra.withLpProdAssocIsometry` preserves norms. -/
theorem norm_withLpProdAssocIsometry (x : WithLp 2 (WithLp 2 (U × V) × W)) :
    ‖withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ_L hQ_R x‖ = ‖x‖ :=
  (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).norm_map x

/-! ### Associativity of `complexProdTensor` -/

variable [FiniteDimensional ℝ U] {n₁ : ℕ} [Fact (finrank ℝ U = n₁)] (o₁ : Orientation ℝ U (Fin n₁))
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
transported along `CliffordAlgebra.withLpProdAssocIsometry`. -/
theorem conjAlgEquiv_assoc_complexProdTensor
    {o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (n₁ + n₂))}
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n₁ + n₂))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂) :
    ((TensorProduct.assoc ℂ E F G).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ_L o₁₂ (norm_sq_of_withLp_prod hQ₁₂ hQ₁ hQ₂) (hn₁.add hn₂)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ_R o₁ hQ₁ hn₁ ρ₁
          (complexProdTensor hQ₂₃ o₂ hQ₂ hn₂ ρ₂ ρ₃)).comp
        (CliffordAlgebra.map
          ((withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ_L hQ_R).toIsometry.baseChange ℂ)) := by
  refine baseChange_algHom_ext Q_L fun x ↦ ?_
  apply TensorProduct.ext_threefold'
  intro e f g
  let u := x.fst.fst
  let v := x.fst.snd
  let w := x.snd
  have hx : x = WithLp.toLp 2 (WithLp.toLp 2 (u, v), w) := rfl
  rw [hx, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.comp_apply,
    complexProdTensor_ι_one_tmul_toLp, complexProdTensor_ι_one_tmul_toLp,
    complexProdTensor_complexVolume_of_prod hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂ o₂ hn₂ hQ₂ ho₁₂]
  simp only [map_apply_ι, QuadraticMap.Isometry.baseChange_tmul,
    QuadraticMap.IsometryEquiv.toIsometry_apply, withLpProdAssocIsometry_apply, WithLp.toLp_fst,
    WithLp.toLp_snd, complexProdTensor_ι_one_tmul_toLp, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, assoc_symm_tmul, map_add, assoc_tmul,
    LinearMap.add_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, tmul_add, add_tmul,
    add_assoc]

/-- **Pointwise associativity of `complexProdTensor`** on every Clifford element `a` and tensor
`t : (E ⊗ F) ⊗ G`. -/
theorem assoc_complexProdTensor
    {o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (n₁ + n₂))}
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n₁ + n₂))
      (WithLp.linearEquiv 2 ℝ (U × V)).symm = o₁₂)
    (a : CliffordAlgebra (Q_L.baseChange ℂ)) (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    TensorProduct.assoc ℂ E F G
        (complexProdTensor hQ_L o₁₂ (norm_sq_of_withLp_prod hQ₁₂ hQ₁ hQ₂) (hn₁.add hn₂)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ_R o₁ hQ₁ hn₁ ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn₂ ρ₂ ρ₃)
        (CliffordAlgebra.map
          ((withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ_L hQ_R).toIsometry.baseChange ℂ) a)
        (TensorProduct.assoc ℂ E F G t) := by
  have h := congrArg
    (fun φ : CliffordAlgebra (Q_L.baseChange ℂ) →ₐ[ℂ] Module.End ℂ (E ⊗[ℂ] (F ⊗[ℂ] G)) ↦
      φ a (TensorProduct.assoc ℂ E F G t))
    (conjAlgEquiv_assoc_complexProdTensor hQ₁₂ hQ₂₃ hQ_L hQ_R o₁ o₂ hQ₁ hQ₂ hn₁ hn₂ ρ₁ ρ₂ ρ₃
      ho₁₂)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

/-! ### Triple product orientations and chiralities -/

section TripleOrientation

variable [FiniteDimensional ℝ W] {n₃ : ℕ} [Fact (finrank ℝ W = n₃)] (o₃ : Orientation ℝ W (Fin n₃))
  [Fact (finrank ℝ (WithLp 2 (V × W)) = n₂ + n₃)]

/-- **Associativity of `L²` product orientations**: `LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W`
transports the left-iterated product orientation `(o₁ × o₂) × o₃` to the right-iterated product
orientation `o₁ × (o₂ × o₃)`, reindexed along `n₁ + n₂ + n₃ = n₁ + (n₂ + n₃)`. -/
theorem _root_.Orientation.map_withLpProdAssoc_prod
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
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm = o_R) :
    Orientation.map (Fin (n₁ + n₂ + n₃))
        (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv o_L =
      Orientation.reindex ℝ (WithLp 2 (U × WithLp 2 (V × W)))
        (finCongr (add_assoc n₁ n₂ n₃).symm) o_R := by
  subst ho₁₂ ho₂₃ ho_L ho_R
  have hUV : finrank ℝ (U × V) = n₁ + n₂ := by
    rw [Module.finrank_prod, Fact.out (p := finrank ℝ U = n₁), Fact.out (p := finrank ℝ V = n₂)]
  have hVW : finrank ℝ (V × W) = n₂ + n₃ := by
    rw [Module.finrank_prod, Fact.out (p := finrank ℝ V = n₂), Fact.out (p := finrank ℝ W = n₃)]
  have hL : Orientation.prod
      ((Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n₁ + n₂))
        (WithLp.linearEquiv 2 ℝ (U × V)).symm) o₃ Fact.out Fact.out =
      Orientation.map (Fin (n₁ + n₂ + n₃))
        (((WithLp.linearEquiv 2 ℝ (U × V)).symm).prodCongr (LinearEquiv.refl ℝ W))
        (Orientation.prod (Orientation.prod o₁ o₂ Fact.out Fact.out) o₃ hUV Fact.out) := by
    simpa using (Orientation.map_prod (Orientation.prod o₁ o₂ Fact.out Fact.out) o₃ hUV Fact.out
      (WithLp.linearEquiv 2 ℝ (U × V)).symm (LinearEquiv.refl ℝ W)).symm
  have hR : Orientation.prod o₁
      ((Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n₂ + n₃))
        (WithLp.linearEquiv 2 ℝ (V × W)).symm) Fact.out Fact.out =
      Orientation.map (Fin (n₁ + (n₂ + n₃)))
        ((LinearEquiv.refl ℝ U).prodCongr (WithLp.linearEquiv 2 ℝ (V × W)).symm)
        (Orientation.prod o₁ (Orientation.prod o₂ o₃ Fact.out Fact.out) Fact.out hVW) := by
    simpa using (Orientation.map_prod o₁ (Orientation.prod o₂ o₃ Fact.out Fact.out) Fact.out hVW
      (LinearEquiv.refl ℝ U) (WithLp.linearEquiv 2 ℝ (V × W)).symm).symm
  rw [hL, hR, ← Orientation.map_trans, ← Orientation.map_trans, ← Orientation.map_trans,
    ← Orientation.map_reindex, ← Orientation.map_prodAssoc_prod o₁ o₂ o₃ Fact.out Fact.out Fact.out,
    ← Orientation.map_trans]
  have heq :
      (((WithLp.linearEquiv 2 ℝ (U × V)).symm.prodCongr (LinearEquiv.refl ℝ W)).trans
        ((WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).symm.trans
          (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv)) =
      (LinearEquiv.prodAssoc ℝ U V W).trans
        (((LinearEquiv.refl ℝ U).prodCongr (WithLp.linearEquiv 2 ℝ (V × W)).symm).trans
          (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).symm) := by
    ext; rfl
  rw [heq]

variable [Fact (finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = n₁ + n₂ + n₃)]
  [Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = n₁ + (n₂ + n₃))]

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
        (complexProdTensor hQ_L o₁₂ (norm_sq_of_withLp_prod hQ₁₂ hQ₁ hQ₂) (hn₁.add hn₂)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂) ρ₃ (complexVolume Q_L o_L) t) =
      complexProdTensor hQ_R o₁ hQ₁ hn₁ ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hn₂ ρ₂ ρ₃) (complexVolume Q_R o_R)
        (TensorProduct.assoc ℂ E F G t) := by
  rw [complexProdTensor_complexVolume_of_prod hQ_L o₁₂ _ (hn₁.add hn₂) _ ρ₃ o₃ hn₃ hQ₃ ho_L,
    complexProdTensor_complexVolume_of_prod hQ₁₂ o₁ hQ₁ hn₁ ρ₁ ρ₂ o₂ hn₂ hQ₂ ho₁₂,
    complexProdTensor_complexVolume_of_prod hQ_R o₁ hQ₁ hn₁ ρ₁ _ o₂₃ (hn₂.add hn₃)
      (norm_sq_of_withLp_prod hQ₂₃ hQ₂ hQ₃) ho_R,
    complexProdTensor_complexVolume_of_prod hQ₂₃ o₂ hQ₂ hn₂ ρ₂ ρ₃ o₃ hn₃ hQ₃ ho₂₃]
  exact (TensorProduct.map_map_assoc _ _ _ t).symm

end TripleOrientation

end Isometry

end CliffordAlgebra
