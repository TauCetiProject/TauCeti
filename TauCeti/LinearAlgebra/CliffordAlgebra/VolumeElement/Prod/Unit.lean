/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.ProdEquiv
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit

/-!
# Orientation-sign and rank-zero unit laws of `CliffordAlgebra.complexProdTensor`

`CliffordAlgebra.complexProdTensor` depends on the orientation `o₁` of the left factor `V` through
its chirality operator `Γ_V = ρ₁ (complexVolume Q₁ o₁)`. This file establishes how changing `o₁`
affects the product representation and how `complexProdTensor` behaves when either `V` or `W` is
zero-dimensional:

1. **Reversing the orientation `o₁` of `V`**: replacing `o₁` by `-o₁` negates `Γ_V`, so `(0, w)`
   acts by `-Γ_V ⊗ c_W(w)`
   (`CliffordAlgebra.complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr`). When `W` is also
   even-dimensional, `1 ⊗ Γ_W` intertwines the product actions for `o₁` and `-o₁` on every Clifford
   element (`CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor`), and for
   `Q₂ w = -‖w‖²` this is an algebra-action conjugation by a linear equivalence
   (`CliffordAlgebra.conjAlgEquiv_lTensor_complexVolume_complexProdTensor`). Passing from the
   product orientation of `(o₁, o₂)` to that of `(-o₁, o₂)` simultaneously negates the total
   orientation `o`, so the product chirality `Γ_(V ⊕ W)` is negated when `m` is even and unchanged
   when `m` is odd.

2. **Rank-zero unit laws**:
   * When `V` is trivial (`[Unique V]`) and `ℂ` carries any action `ρ₁` of `CliffordAlgebra
     (Q₁.baseChange ℂ)`: for `o₁ = positiveOrientation`, `Γ_V = 1` and the left unitor
     `TensorProduct.lid ℂ F : ℂ ⊗ F ≃ F` intertwines `complexProdTensor` with `ρ₂` along
     `QuadraticMap.IsometryEquiv.withLpUniqueProd`, carrying `Γ_(0 ⊕ W)` to `Γ_W`. For
     `o₁ = -positiveOrientation`, `Γ_V = -1` and the same left unitor twists `ρ₂` by the grade
     involution `CliffordAlgebra.involute`, negating generating vectors and multiplying the volume
     action for the product orientation by `-(-1) ^ m`.
   * When `W` is trivial (`[Unique W]`) and `ℂ` carries any action `ρ₂`: the right unitor
     `TensorProduct.rid ℂ E : E ⊗ ℂ ≃ E` intertwines `complexProdTensor` with `ρ₁` along
     `QuadraticMap.IsometryEquiv.withLpProdUnique` for every orientation `o₁` of `V`, carrying
     `Γ_(V ⊕ 0)` for `positiveOrientation` on `W` to `Γ_V`.

## Main results

* `CliffordAlgebra.lTensor_complexVolume_comp_complexProdTensor` and
  `CliffordAlgebra.conjAlgEquiv_lTensor_complexVolume_complexProdTensor`: `1 ⊗ Γ_W` intertwines the
  product representations for `o₁` and `-o₁` when `m` is even.
* `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation` and
  `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`: left unit laws for
  both orientations of a zero-dimensional left factor.
* `CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`: right unit law for a zero-dimensional right
  factor.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct

namespace CliffordAlgebra

section NegOrientation

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {n : ℕ} [Fact (finrank ℝ V = n)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- Reversing the orientation `o₁` of `V` negates the action of `(0, w)` on `E ⊗ F`, since `(0, w)`
acts through `Γ_V`. -/
theorem complexProdTensor_neg_orientation_ι_one_tmul_toLp_inr (w : W) :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂
        (ι (Q.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, w))) =
      -TensorProduct.map (ρ₁ (complexVolume Q₁ o₁)) (ρ₂ (ι (Q₂.baseChange ℂ) (1 ⊗ₜ w))) := by
  rw [complexProdTensor_ι_one_tmul_toLp, TensorProduct.tmul_zero, map_zero, map_zero,
    LinearMap.rTensor_zero, zero_add, complexVolume_neg_orientation, map_neg,
    ← neg_one_smul ℂ (ρ₁ _), TensorProduct.map_smul_left]
  ext z
  simp

variable [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]

/-- **Intertwining under reversal of `o₁`**: when `W` is even-dimensional, `1 ⊗ Γ_W` intertwines
`complexProdTensor` for `o₁` with `complexProdTensor` for `-o₁` on every Clifford element, for any
quadratic form `Q₂` on `W`. -/
theorem lTensor_complexVolume_comp_complexProdTensor (o₂ : Orientation ℝ W (Fin m)) (hm : Even m)
    (x : CliffordAlgebra (Q.baseChange ℂ)) :
    (ρ₂ (complexVolume Q₂ o₂)).lTensor E ∘ₗ complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x =
      complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ x ∘ₗ (ρ₂ (complexVolume Q₂ o₂)).lTensor E := by
  have hneg : ρ₁ (complexVolume Q₁ (-o₁)) = -ρ₁ (complexVolume Q₁ o₁) := by
    rw [complexVolume_neg_orientation, map_neg]
  rw [complexProdTensor_eq_cliffordProdTensor, complexProdTensor_eq_cliffordProdTensor]
  simpa only [hneg] using
    AlgHom.lTensor_comp_cliffordProdTensor ρ₁ (ρ₁ (complexVolume Q₁ o₁))
      (by rw [← map_mul, complexVolume_mul_self o₁ hQ₁, map_one])
      (fun v ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₁ hn, map_neg])
      ρ₂ (ρ₂ (complexVolume Q₂ o₂))
      (fun u ↦ by rw [← map_mul, ← map_mul, complexVolume_mul_ι_of_even o₂ hm, map_neg])
      (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd ℂ) x)

/-- **Equivalence of product representations under `o₁ ↦ -o₁`**: when `W` is even-dimensional with
`Q₂ w = -‖w‖²`, conjugating `complexProdTensor` for `o₁` by the linear equivalence `1 ⊗ Γ_W` gives
`complexProdTensor` for `-o₁`. -/
theorem conjAlgEquiv_lTensor_complexVolume_complexProdTensor (o₂ : Orientation ℝ W (Fin m))
    (hQ₂ : ∀ w, Q₂ w = -‖w‖ ^ 2) (hm : Even m) :
    (((LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
        (map_complexVolume_involutive o₂ hQ₂ ρ₂)).lTensor E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ := by
  let e := (LinearEquiv.ofInvolutive (ρ₂ (complexVolume Q₂ o₂))
    (map_complexVolume_involutive o₂ hQ₂ ρ₂)).lTensor E
  have he : ∀ t, e t = (ρ₂ (complexVolume Q₂ o₂)).lTensor E t := fun t ↦ by
    induction t using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  apply AlgHom.ext
  intro x
  apply LinearMap.ext
  intro z
  obtain ⟨t, rfl⟩ := e.surjective z
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e.symm_apply_apply, he, he]
  exact LinearMap.congr_fun
    (lTensor_complexVolume_comp_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ o₂ hm x) t

/-- Reversing `o₁` in BOTH `complexProdTensor` and `Orientation.prod` multiplies the product volume
action by `-(-1) ^ m`: in particular it negates the product chirality when `m` is even, and leaves
the odd product volume element `1 ⊗ ω_W` invariant when `m` is odd. -/
theorem complexProdTensor_neg_orientation_complexVolume_of_map_prod
    [Fact (finrank ℝ (WithLp 2 (V × W)) = n + m)]
    (o₂ : Orientation ℝ W (Fin m))
    (o o' : Orientation ℝ (WithLp 2 (V × W)) (Fin (n + m)))
    {b₂ : OrthonormalBasis (Fin m) ℝ W}
    (hQb₂ : (QuadraticMap.associated Q₂).IsOrthoᵢ b₂.toBasis)
    (ho : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o)
    (ho' : (Orientation.prod (-o₁) o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv 2 ℝ (V × W)).symm = o') :
    complexProdTensor hQ (-o₁) hQ₁ hn ρ₁ ρ₂ (complexVolume Q o') =
      -((-1 : ℂ) ^ m • complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) := by
  subst o o'
  rw [Orientation.prod_neg_left, Orientation.map_neg, complexVolume_neg_orientation, map_neg,
    complexProdTensor_neg_orientation_complexVolume hQ o₁ hQ₁ hn ρ₁ ρ₂ _ hQb₂]

end NegOrientation

section UnitLeft

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Unique V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Fact (finrank ℝ V = 0)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2)
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

/-- **Left unit law (`positiveOrientation`)**: when `V` is zero-dimensional and positively oriented,
conjugating `complexProdTensor` on `ℂ ⊗ F` by `TensorProduct.lid ℂ F` recovers `ρ₂` along
`QuadraticMap.IsometryEquiv.withLpUniqueProd`. -/
theorem conjAlgEquiv_lid_complexProdTensor_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂) =
      ρ₂.comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro u
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    have hx : z ⊗ₜ[ℝ] x =
        z • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, WithLp.toLp_ofLp]
    rw [hx, map_smul, map_smul]
    ext f
    simp [LinearEquiv.conjAlgEquiv_apply, complexProdTensor_ι_one_tmul_toLp, equivOfIsometry_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Applied form of `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_positiveOrientation`. -/
theorem lid_complexProdTensor_positiveOrientation (x : CliffordAlgebra (Q.baseChange ℂ))
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ x z) =
      ρ₂ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ) x)
        (TensorProduct.lid ℂ F z) := by
  have h := AlgHom.congr_fun
    (conjAlgEquiv_lid_complexProdTensor_positiveOrientation hQ hQ₁ ρ₁ ρ₂) x
  have hz := LinearMap.congr_fun h (TensorProduct.lid ℂ F z)
  simpa [LinearEquiv.conjAlgEquiv_apply] using hz

/-- **Left unit law (`-positiveOrientation`)**: when `V` is zero-dimensional and negatively
oriented, `Γ_V = -1`, so conjugating `complexProdTensor` on `ℂ ⊗ F` by `TensorProduct.lid ℂ F`
twists `ρ₂` by the grade involution `CliffordAlgebra.involute`. -/
theorem conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂) =
      (ρ₂.comp
          (CliffordAlgebra.involute :
            CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] CliffordAlgebra (Q₂.baseChange ℂ))).comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro u
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    have hx : z ⊗ₜ[ℝ] x =
        z • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, WithLp.toLp_ofLp]
    rw [hx, map_smul, map_smul]
    ext f
    simp [LinearEquiv.conjAlgEquiv_apply, complexProdTensor_ι_one_tmul_toLp, equivOfIsometry_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Applied form of `CliffordAlgebra.conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation`. -/
theorem lid_complexProdTensor_neg_positiveOrientation (x : CliffordAlgebra (Q.baseChange ℂ))
    (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ x z) =
      ρ₂ (CliffordAlgebra.involute
          (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).baseChange ℂ) x))
        (TensorProduct.lid ℂ F z) := by
  have h := AlgHom.congr_fun
    (conjAlgEquiv_lid_complexProdTensor_neg_positiveOrientation hQ hQ₁ ρ₁ ρ₂) x
  have hz := LinearMap.congr_fun h (TensorProduct.lid ℂ F z)
  simpa [LinearEquiv.conjAlgEquiv_apply] using hz

/-- For `positiveOrientation` on trivial `V`, `TensorProduct.lid ℂ F` conjugates the action of
`complexVolume Q o` (with `o` the product orientation of `(positiveOrientation, o₂)`) to
`ρ₂ (complexVolume Q₂ o₂)`, for any quadratic form `Q₂` on `W`. -/
theorem conj_lid_complexProdTensor_positiveOrientation_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
    (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))
    (ho : (Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
      Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.lid ℂ F).conj
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ (complexVolume Q o)) =
      ρ₂ (complexVolume Q₂ o₂) := by
  subst o
  have hnorm : ∀ x, ‖QuadraticMap.IsometryEquiv.withLpUniqueProd hQ x‖ = ‖x‖ := fun x ↦ by
    simpa using (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).norm_map x
  have horient :
      Orientation.map (Fin (0 + m)) (QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).toLinearEquiv
          ((Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
            Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm) =
        Orientation.reindex ℝ W (finCongr (zero_add m).symm) o₂ := by
    simpa [← Orientation.map_symm] using
      Orientation.map_uniqueProd_prod_positiveOrientation o₂ Fact.out Fact.out
  apply LinearMap.ext
  intro f
  rw [LinearEquiv.conj_apply_apply,
    lid_complexProdTensor_positiveOrientation hQ hQ₁ ρ₁ ρ₂ _ ((TensorProduct.lid ℂ F).symm f),
    LinearEquiv.apply_symm_apply, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume_of_eq _ _ hnorm (zero_add m), horient,
    Orientation.reindex_finCongr_reindex_finCongr]
  simp [finCongr_refl, Orientation.reindex_refl]

/-- For `-positiveOrientation` on trivial `V` and the product orientation of
`(-positiveOrientation, o₂)`, `TensorProduct.lid ℂ F` conjugates the action of `complexVolume Q o`
to `-((-1) ^ m • ρ₂ (complexVolume Q₂ o₂))`: `-Γ_W` when `m` is even, and `+ω_W` when `m` is odd. -/
theorem conj_lid_complexProdTensor_neg_positiveOrientation_complexVolume
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
    (o₂ : Orientation ℝ W (Fin m))
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin (0 + m)))
    (ho : (Orientation.prod (-positiveOrientation : Orientation ℝ V (Fin 0)) o₂
      Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.lid ℂ F).conj
        (complexProdTensor hQ (-positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ Even.zero
          ρ₁ ρ₂ (complexVolume Q o)) =
      -((-1 : ℂ) ^ m • ρ₂ (complexVolume Q₂ o₂)) := by
  subst o
  have hnorm : ∀ x, ‖QuadraticMap.IsometryEquiv.withLpUniqueProd hQ x‖ = ‖x‖ := fun x ↦ by
    simpa using (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).norm_map x
  have horient :
      Orientation.map (Fin (0 + m)) (QuadraticMap.IsometryEquiv.withLpUniqueProd hQ).toLinearEquiv
          ((Orientation.prod (positiveOrientation : Orientation ℝ V (Fin 0)) o₂
            Fact.out Fact.out).map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm) =
        Orientation.reindex ℝ W (finCongr (zero_add m).symm) o₂ := by
    simpa [← Orientation.map_symm] using
      Orientation.map_uniqueProd_prod_positiveOrientation o₂ Fact.out Fact.out
  apply LinearMap.ext
  intro f
  rw [LinearEquiv.conj_apply_apply,
    lid_complexProdTensor_neg_positiveOrientation hQ hQ₁ ρ₁ ρ₂ _ ((TensorProduct.lid ℂ F).symm f),
    LinearEquiv.apply_symm_apply, Orientation.prod_neg_left, Orientation.map_neg,
    complexVolume_neg_orientation, map_neg, map_neg, map_neg, LinearMap.neg_apply,
    equivOfIsometry_apply, QuadraticMap.IsometryEquiv.baseChange_toIsometry,
    map_complexVolume_of_eq _ _ hnorm (zero_add m), horient,
    Orientation.reindex_finCongr_reindex_finCongr]
  simp [finCongr_refl, Orientation.reindex_refl, involute_complexVolume]

end UnitLeft

section UnitRight

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Unique W]
  {n : ℕ} [Fact (finrank ℝ V = n)]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W} {Q : QuadraticForm ℝ (WithLp 2 (V × W))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  (o₁ : Orientation ℝ V (Fin n)) (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

/-- **Right unit law**: when `W` is zero-dimensional, conjugating `complexProdTensor` on `E ⊗ ℂ`
by `TensorProduct.rid ℂ E` recovers `ρ₁` along `QuadraticMap.IsometryEquiv.withLpProdUnique`, for
either orientation `o₁` of `V`. -/
theorem conjAlgEquiv_rid_complexProdTensor :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp
        (equivOfIsometry
          ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ)).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro u
  induction u using TensorProduct.inductionOn with
  | tmul z x =>
    have hx : z ⊗ₜ[ℝ] x =
        z • ((1 : ℂ) ⊗ₜ[ℝ] WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, WithLp.toLp_ofLp]
    rw [hx, map_smul, map_smul]
    ext e
    simp [LinearEquiv.conjAlgEquiv_apply, complexProdTensor_ι_one_tmul_toLp, equivOfIsometry_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Applied form of `CliffordAlgebra.conjAlgEquiv_rid_complexProdTensor`. -/
theorem rid_complexProdTensor (x : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ x z) =
      ρ₁ (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProdUnique hQ).baseChange ℂ) x)
        (TensorProduct.rid ℂ E z) := by
  have h := AlgHom.congr_fun
    (conjAlgEquiv_rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) x
  have hz := LinearMap.congr_fun h (TensorProduct.rid ℂ E z)
  simpa [LinearEquiv.conjAlgEquiv_apply] using hz

/-- For `positiveOrientation` on trivial `W`, `TensorProduct.rid ℂ E` conjugates the action of
`complexVolume Q o` (with `o` the product orientation of `(o₁, positiveOrientation)`) to
`ρ₁ (complexVolume Q₁ o₁)`. -/
theorem conj_rid_complexProdTensor_complexVolume_positiveOrientation
    [Fact (finrank ℝ W = 0)] [Fact (finrank ℝ (WithLp 2 (V × W)) = n)]
    (o : Orientation ℝ (WithLp 2 (V × W)) (Fin n))
    (ho : (Orientation.prod o₁ (positiveOrientation : Orientation ℝ W (Fin 0))
      Fact.out Fact.out).map (Fin n) (WithLp.linearEquiv 2 ℝ (V × W)).symm = o) :
    (TensorProduct.rid ℂ E).conj (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ (complexVolume Q o)) =
      ρ₁ (complexVolume Q₁ o₁) := by
  subst o
  have hnorm : ∀ x, ‖QuadraticMap.IsometryEquiv.withLpProdUnique hQ x‖ = ‖x‖ := fun x ↦ by
    simpa using (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).norm_map x
  have horient :
      Orientation.map (Fin n) (QuadraticMap.IsometryEquiv.withLpProdUnique hQ).toLinearEquiv
          ((Orientation.prod o₁ (positiveOrientation : Orientation ℝ W (Fin 0))
            Fact.out Fact.out).map (Fin n) (WithLp.linearEquiv 2 ℝ (V × W)).symm) = o₁ := by
    simpa [← Orientation.map_symm] using
      Orientation.map_prodUnique_prod_positiveOrientation o₁ Fact.out Fact.out
  apply LinearMap.ext
  intro e
  rw [LinearEquiv.conj_apply_apply,
    rid_complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ _ ((TensorProduct.rid ℂ E).symm e),
    LinearEquiv.apply_symm_apply, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChange_toIsometry, map_complexVolume _ _ hnorm, horient]

end UnitRight

end CliffordAlgebra
