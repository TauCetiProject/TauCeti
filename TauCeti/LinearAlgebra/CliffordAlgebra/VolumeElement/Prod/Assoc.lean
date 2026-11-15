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

Let `U`, `V`, `W` be real inner product spaces, with `U` and `V` oriented of even dimensions `n`
and `m` and carrying the negative-metric forms `Q₁ u = -‖u‖²` and `Q₂ v = -‖v‖²`. Equip `U ⊕ V`
with the ordered product orientation `Orientation.prod o₁ o₂`. By
`CliffordAlgebra.complexProdTensor_complexVolume_of_map_eq_prod`, the chirality of `U ⊕ V` acts on
`E ⊗ F` as the tensor grading `Γ_U ⊗ Γ_V`, so Mathlib's `TensorProduct.assoc ℂ E F G` intertwines
the two iterated `complexProdTensor` actions along `LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W`
(`CliffordAlgebra.conjAlgEquiv_complexProdTensor_assoc`,
`CliffordAlgebra.assoc_complexProdTensor`), realizing the abstract associativity law of
`TauCeti/LinearAlgebra/CliffordAlgebra/Prod/Assoc.lean` on `L²` orthogonal sums. Neither
finite-dimensionality of `W` nor a metric hypothesis on `Q₃` is required for the action associator.

When `W` is also finite-dimensional of dimension `p` with orientation `o₃`,
`LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W` transports the left-associated ordered product
orientation `((o₁ × o₂) × o₃)` to the right-associated one `(o₁ × (o₂ × o₃))` (reindexed along
`n + m + p = n + (m + p)`), and hence carries `Γ_((U ⊕ V) ⊕ W)` to `Γ_(U ⊕ (V ⊕ W))`
(`CliffordAlgebra.map_withLpProdAssocIsometry_complexVolume`).

## Main definitions

* `CliffordAlgebra.withLpProdAssocIsometry`: `LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W` as a
  quadratic isometry equivalence `Q₁₂_₃ ≃ Q₁_₂₃`.

## Main results

* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_assoc` and
  `CliffordAlgebra.assoc_complexProdTensor`: `TensorProduct.assoc ℂ E F G` intertwines the iterated
  graded tensor product actions.
* `CliffordAlgebra.map_withLpProdAssoc_orientation` and
  `CliffordAlgebra.map_withLpProdAssocIsometry_complexVolume`: compatibility with the iterated
  ordered product orientations and their normalized complex volume elements.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

section Isometry

variable {U V W : Type*} [SeminormedAddCommGroup U] [NormedSpace ℝ U]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup W] [NormedSpace ℝ W]
  {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V} {Q₃ : QuadraticForm ℝ W}
  {Q₁₂ : QuadraticForm ℝ (WithLp 2 (U × V))}
  {Q₂₃ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q₁₂_₃ : QuadraticForm ℝ (WithLp 2 (WithLp 2 (U × V) × W))}
  {Q₁_₂₃ : QuadraticForm ℝ (WithLp 2 (U × WithLp 2 (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)

include hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ in
/-- `LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W` as a quadratic isometry equivalence between
the iterated `L²` orthogonal sums `((U ⊕ V) ⊕ W)` and `(U ⊕ (V ⊕ W))`. -/
def withLpProdAssocIsometry : Q₁₂_₃.IsometryEquiv Q₁_₂₃ where
  toLinearEquiv := (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv
  map_app' x := by simp [hQ₁₂_₃, hQ₁_₂₃, hQ₁₂, hQ₂₃, add_assoc]

/-- Applying `CliffordAlgebra.withLpProdAssocIsometry` evaluates
`LinearIsometryEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssocIsometry_apply (x : WithLp 2 (WithLp 2 (U × V) × W)) :
    withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ x =
      LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W x :=
  (rfl)

/-- The linear equivalence underlying `CliffordAlgebra.withLpProdAssocIsometry` is
`LinearIsometryEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssocIsometry_toLinearEquiv :
    (withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).toLinearEquiv =
      (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv :=
  (rfl)

end Isometry

section Orientation

variable {U V W : Type*} [SeminormedAddCommGroup U] [NormedSpace ℝ U]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {n m p : ℕ} [Fact (finrank ℝ U = n)] [Fact (finrank ℝ V = m)] [Fact (finrank ℝ W = p)]
  [Fact (finrank ℝ (WithLp 2 (U × V)) = n + m)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = m + p)]
  (o₁ : Orientation ℝ U (Fin n)) (o₂ : Orientation ℝ V (Fin m)) (o₃ : Orientation ℝ W (Fin p))
  (o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (n + m)))
  (o₂₃ : Orientation ℝ (WithLp 2 (V × W)) (Fin (m + p)))
  (o₁₂_₃ : Orientation ℝ (WithLp 2 (WithLp 2 (U × V) × W)) (Fin (n + m + p)))
  (o₁_₂₃ : Orientation ℝ (WithLp 2 (U × WithLp 2 (V × W))) (Fin (n + (m + p))))

/-- `LinearIsometryEquiv.withLpProdAssoc` carries the left-associated ordered product orientation
to the right-associated one, reindexed along `(add_assoc n m p).symm`. -/
theorem map_withLpProdAssoc_orientation
    (ho₁₂ : o₁₂.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (U × V)) =
      o₁.prod o₂ Fact.out Fact.out)
    (ho₂₃ : o₂₃.map (Fin (m + p)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      o₂.prod o₃ Fact.out Fact.out)
    (ho₁₂_₃ : o₁₂_₃.map (Fin (n + m + p))
      (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)) =
      o₁₂.prod o₃ Fact.out Fact.out)
    (ho₁_₂₃ : o₁_₂₃.map (Fin (n + (m + p)))
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))) =
      o₁.prod o₂₃ Fact.out Fact.out) :
    o₁₂_₃.map (Fin (n + m + p)) (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv =
      Orientation.reindex ℝ _ (finCongr (add_assoc n m p).symm) o₁_₂₃ := by
  let eL : WithLp 2 (WithLp 2 (U × V) × W) ≃ₗ[ℝ] (U × V) × W :=
    (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)).trans
      ((WithLp.linearEquiv 2 ℝ (U × V)).prodCongr (LinearEquiv.refl ℝ W))
  let eR : WithLp 2 (U × WithLp 2 (V × W)) ≃ₗ[ℝ] U × V × W :=
    (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))).trans
      ((LinearEquiv.refl ℝ U).prodCongr (WithLp.linearEquiv 2 ℝ (V × W)))
  have hcomm : (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv.trans eR =
      eL.trans (LinearEquiv.prodAssoc ℝ U V W) := by
    ext x <;> rfl
  have hL : o₁₂_₃.map (Fin (n + m + p)) eL =
      (o₁.prod o₂ Fact.out Fact.out).prod o₃
        (by
          rw [Module.finrank_prod, (Fact.out : finrank ℝ U = n), (Fact.out : finrank ℝ V = m)])
        Fact.out := by
    rw [Orientation.map_trans, ho₁₂_₃, Orientation.map_prod, ho₁₂, Orientation.map_refl,
      Equiv.refl_apply]
  have hR : o₁_₂₃.map (Fin (n + (m + p))) eR =
      o₁.prod (o₂.prod o₃ Fact.out Fact.out) Fact.out
        (by
          rw [Module.finrank_prod, (Fact.out : finrank ℝ V = m),
            (Fact.out : finrank ℝ W = p)]) := by
    rw [Orientation.map_trans, ho₁_₂₃, Orientation.map_prod, ho₂₃, Orientation.map_refl,
      Equiv.refl_apply]
  have key : (o₁₂_₃.map (Fin (n + m + p))
      (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv).map
      (Fin (n + m + p)) eR =
      (Orientation.reindex ℝ _ (finCongr (add_assoc n m p).symm) o₁_₂₃).map
      (Fin (n + m + p)) eR := by
    rw [← Orientation.map_trans, hcomm, Orientation.map_trans, hL,
      Orientation.map_prodAssoc_prod, Orientation.map_reindex, hR]
  exact (Orientation.map (Fin (n + m + p)) eR).injective key

end Orientation

variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ U} {Q₂ : QuadraticForm ℝ V} {Q₃ : QuadraticForm ℝ W}
  {Q₁₂ : QuadraticForm ℝ (WithLp 2 (U × V))}
  {Q₂₃ : QuadraticForm ℝ (WithLp 2 (V × W))}
  {Q₁₂_₃ : QuadraticForm ℝ (WithLp 2 (WithLp 2 (U × V) × W))}
  {Q₁_₂₃ : QuadraticForm ℝ (WithLp 2 (U × WithLp 2 (V × W)))}
  (hQ₁₂ : ∀ x, Q₁₂ x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₂₃ : ∀ x, Q₂₃ x = Q₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁₂_₃ : ∀ x, Q₁₂_₃ x = Q₁₂ (WithLp.ofLp x).1 + Q₃ (WithLp.ofLp x).2)
  (hQ₁_₂₃ : ∀ x, Q₁_₂₃ x = Q₁ (WithLp.ofLp x).1 + Q₂₃ (WithLp.ofLp x).2)

section Action

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  {n m : ℕ} [Fact (finrank ℝ U = n)] [Fact (finrank ℝ V = m)]
  [Fact (finrank ℝ (WithLp 2 (U × V)) = n + m)]
  (o₁ : Orientation ℝ U (Fin n)) (hQ₁ : ∀ u, Q₁ u = -‖u‖ ^ 2) (hn : Even n)
  (o₂ : Orientation ℝ V (Fin m)) (hQ₂ : ∀ v, Q₂ v = -‖v‖ ^ 2) (hm : Even m)
  (o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (n + m)))
  (ho₁₂ : o₁₂.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (U × V)) =
    o₁.prod o₂ Fact.out Fact.out)
  {E F G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup G] [Module ℂ G]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)
  (ρ₃ : CliffordAlgebra (Q₃.baseChange ℂ) →ₐ[ℂ] Module.End ℂ G)

include ho₁₂

/-- **Associativity of `CliffordAlgebra.complexProdTensor`**: conjugating the left-associated
graded tensor product action by `TensorProduct.assoc ℂ E F G` yields the right-associated action
transported along `CliffordAlgebra.withLpProdAssocIsometry`. -/
theorem conjAlgEquiv_complexProdTensor_assoc :
    ((TensorProduct.assoc ℂ E F G).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ₁₂_₃ o₁₂ (eq_neg_norm_sq_of_withLpProd hQ₁₂ hQ₁ hQ₂) (hn.add hm)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hn ρ₁ ρ₂) ρ₃) =
      (complexProdTensor hQ₁_₂₃ o₁ hQ₁ hn ρ₁
          (complexProdTensor hQ₂₃ o₂ hQ₂ hm ρ₂ ρ₃)).comp
        (equivOfIsometry
          ((withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ)).toAlgHom := by
  have hγ := complexProdTensor_complexVolume_of_map_eq_prod hQ₁₂ o₁ hQ₁ hn ρ₁ ρ₂ o₂ o₁₂ hm ho₁₂
  apply CliffordAlgebra.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  have hzx : z ⊗ₜ[ℝ] x = z • (1 ⊗ₜ[ℝ] x) := by rw [smul_tmul', smul_eq_mul, mul_one]
  rw [hzx, map_smul, map_smul]
  refine congrArg (z • ·) ?_
  let u := (WithLp.ofLp (WithLp.ofLp x).1).1
  let v := (WithLp.ofLp (WithLp.ofLp x).1).2
  let w := (WithLp.ofLp x).2
  have hx : x = WithLp.toLp 2 (WithLp.toLp 2 (u, v), w) := by
    simp only [u, v, w, Prod.mk.eta, WithLp.toLp_ofLp]
  rw [hx]
  have hiso : equivOfIsometry ((withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ)
      (ι (Q₁₂_₃.baseChange ℂ) (1 ⊗ₜ[ℝ] WithLp.toLp 2 (WithLp.toLp 2 (u, v), w))) =
      ι (Q₁_₂₃.baseChange ℂ) (1 ⊗ₜ[ℝ] WithLp.toLp 2 (u, WithLp.toLp 2 (v, w))) := by
    rw [equivOfIsometry_apply, map_apply_ι, QuadraticMap.IsometryEquiv.toIsometry_apply,
      QuadraticMap.IsometryEquiv.baseChange_tmul, withLpProdAssocIsometry_apply,
      LinearIsometryEquiv.withLpProdAssoc_apply, WithLp.toLp_fst, WithLp.toLp_fst,
      WithLp.toLp_snd, WithLp.toLp_snd]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.coe_toAlgHom, hiso, LinearEquiv.conjAlgEquiv_apply,
    complexProdTensor_ι_one_tmul_toLp, complexProdTensor_ι_one_tmul_toLp, hγ,
    complexProdTensor_ι_one_tmul_toLp, complexProdTensor_ι_one_tmul_toLp]
  apply TensorProduct.ext_threefold'
  intro e f g
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, TensorProduct.assoc_symm_tmul,
    LinearMap.add_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, map_add,
    TensorProduct.assoc_tmul, tmul_add, add_tmul, add_assoc]

/-- `TensorProduct.assoc ℂ E F G` intertwines the two iterated `complexProdTensor` actions on
every Clifford element and every tensor. -/
theorem assoc_complexProdTensor (a : CliffordAlgebra (Q₁₂_₃.baseChange ℂ))
    (t : (E ⊗[ℂ] F) ⊗[ℂ] G) :
    TensorProduct.assoc ℂ E F G
        (complexProdTensor hQ₁₂_₃ o₁₂ (eq_neg_norm_sq_of_withLpProd hQ₁₂ hQ₁ hQ₂) (hn.add hm)
          (complexProdTensor hQ₁₂ o₁ hQ₁ hn ρ₁ ρ₂) ρ₃ a t) =
      complexProdTensor hQ₁_₂₃ o₁ hQ₁ hn ρ₁
        (complexProdTensor hQ₂₃ o₂ hQ₂ hm ρ₂ ρ₃)
        (equivOfIsometry
          ((withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).baseChange ℂ) a)
        (TensorProduct.assoc ℂ E F G t) := by
  have h := congrArg (fun f ↦ f a (TensorProduct.assoc ℂ E F G t))
    (conjAlgEquiv_complexProdTensor_assoc hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃ o₁ hQ₁ hn o₂ hQ₂ hm o₁₂ ho₁₂
      ρ₁ ρ₂ ρ₃)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end Action

section ComplexVolume

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  {n m p : ℕ} [Fact (finrank ℝ U = n)] [Fact (finrank ℝ V = m)] [Fact (finrank ℝ W = p)]
  [Fact (finrank ℝ (WithLp 2 (U × V)) = n + m)]
  [Fact (finrank ℝ (WithLp 2 (V × W)) = m + p)]
  (o₁ : Orientation ℝ U (Fin n)) (o₂ : Orientation ℝ V (Fin m)) (o₃ : Orientation ℝ W (Fin p))
  (o₁₂ : Orientation ℝ (WithLp 2 (U × V)) (Fin (n + m)))
  (o₂₃ : Orientation ℝ (WithLp 2 (V × W)) (Fin (m + p)))
  (o₁₂_₃ : Orientation ℝ (WithLp 2 (WithLp 2 (U × V) × W)) (Fin (n + m + p)))
  (o₁_₂₃ : Orientation ℝ (WithLp 2 (U × WithLp 2 (V × W))) (Fin (n + (m + p))))

/-- `CliffordAlgebra.withLpProdAssocIsometry` transports the normalized complex volume element of
`((U ⊕ V) ⊕ W)` to that of `(U ⊕ (V ⊕ W))` for the iterated ordered product orientations. -/
theorem map_withLpProdAssocIsometry_complexVolume
    [Fact (finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = n + m + p)]
    [Fact (finrank ℝ (WithLp 2 (U × WithLp 2 (V × W))) = n + (m + p))]
    (ho₁₂ : o₁₂.map (Fin (n + m)) (WithLp.linearEquiv 2 ℝ (U × V)) =
      o₁.prod o₂ Fact.out Fact.out)
    (ho₂₃ : o₂₃.map (Fin (m + p)) (WithLp.linearEquiv 2 ℝ (V × W)) =
      o₂.prod o₃ Fact.out Fact.out)
    (ho₁₂_₃ : o₁₂_₃.map (Fin (n + m + p))
      (WithLp.linearEquiv 2 ℝ (WithLp 2 (U × V) × W)) =
      o₁₂.prod o₃ Fact.out Fact.out)
    (ho₁_₂₃ : o₁_₂₃.map (Fin (n + (m + p)))
      (WithLp.linearEquiv 2 ℝ (U × WithLp 2 (V × W))) =
      o₁.prod o₂₃ Fact.out Fact.out) :
    map ((withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃).toIsometry.baseChange ℂ)
        (complexVolume Q₁₂_₃ o₁₂_₃) =
      complexVolume Q₁_₂₃ o₁_₂₃ := by
  have := Fact.mk
    ((LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).toLinearEquiv.finrank_eq.symm.trans
      (Fact.out : finrank ℝ (WithLp 2 (WithLp 2 (U × V) × W)) = n + m + p))
  rw [map_complexVolume o₁₂_₃ (withLpProdAssocIsometry hQ₁₂ hQ₂₃ hQ₁₂_₃ hQ₁_₂₃)
      (LinearIsometryEquiv.withLpProdAssoc 2 ℝ U V W).norm_map,
    withLpProdAssocIsometry_toLinearEquiv,
    map_withLpProdAssoc_orientation o₁ o₂ o₃ o₁₂ o₂₃ o₁₂_₃ o₁_₂₃ ho₁₂ ho₂₃ ho₁₂_₃ ho₁_₂₃,
    complexVolume_reindex_finCongr]

end ComplexVolume

end CliffordAlgebra
