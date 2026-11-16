/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Prod.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Unit
import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# Left and right unit laws of the graded complex Clifford tensor product

When the left Euclidean factor `V` has rank zero (`Unique V`) and carries its canonical positive
orientation `positiveOrientation`, its normalized complex volume element is `Γ_V = 1`
(`CliffordAlgebra.complexVolume_positiveOrientation`). Hence the left unitor
`TensorProduct.lid ℂ F : ℂ ⊗ F ≃ F` intertwines `CliffordAlgebra.complexProdTensor` with the
action `ρ₂` of `CliffordAlgebra (Q₂.baseChange ℂ)` on `F` along any quadratic isometry realizing
`(0, w) ↦ w`. No finiteness, orientation, parity, or metric hypothesis is placed on `W`.

When the rank-zero left factor instead carries the negative orientation `-positiveOrientation`,
its chirality is `Γ_V = -1`, so every vector of `W` acts with an extra minus sign and
`TensorProduct.lid ℂ F` intertwines `complexProdTensor` with the grade-involuted action
`ρ₂ ∘ involute`.

When the right Euclidean factor `W` has rank zero (`Unique W`) and `F = ℂ`, the right unitor
`TensorProduct.rid ℂ E : E ⊗ ℂ ≃ E` intertwines `complexProdTensor` with `ρ₁` along `(v, 0) ↦ v`
for every even-dimensional oriented `V`.

On volume elements, deleting a positively oriented rank-zero left or right factor transports the
product volume element `Γ_(V ⊕ W)` to `Γ_W` or `Γ_V` respectively, for arbitrary dimension and
arbitrary quadratic form on the remaining factor.

## Main results

* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_lid`, `CliffordAlgebra.lid_complexProdTensor`:
  left unit law for `positiveOrientation`.
* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_lid_neg_positiveOrientation`,
  `CliffordAlgebra.lid_complexProdTensor_neg_positiveOrientation`: left unitor under
  `-positiveOrientation` intertwines with `ρ₂ ∘ involute`.
* `CliffordAlgebra.conjAlgEquiv_complexProdTensor_rid`, `CliffordAlgebra.rid_complexProdTensor`:
  right unit law.
* `CliffordAlgebra.map_complexVolume_uniqueProd`, `CliffordAlgebra.map_complexVolume_prodUnique`:
  unit laws for the product normalized complex volume element.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace CliffordAlgebra

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Q₁ : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ W}
  {Q : QuadraticForm ℝ (WithLp 2 (V × W))}

section LeftUnit

variable (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [Unique V] [Fact (finrank ℝ V = 0)]
  {hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2} {hn : Even (0 : ℕ)}
  {F : Type*} [AddCommGroup F] [Module ℂ F]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ F)

omit [Fact (finrank ℝ V = 0)] in
/-- Auxiliary diagonal identification for deleting a trivial left factor. -/
private theorem equivOfIsometry_uniqueProd_comp (f : Q →qᵢ Q₂)
    (hf : ∀ w, f (WithLp.toLp 2 (default, w)) = w)
    (e : Q.IsometryEquiv (Q₁.prod Q₂)) (he : ∀ x, e x = WithLp.ofLp x) :
    (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd (Q₁.baseChange ℂ)
        (Q₂.baseChange ℂ))).toAlgHom.comp
        (equivOfIsometry (e.baseChangeProd ℂ)).toAlgHom =
      map (f.baseChange ℂ) := by
  apply CliffordAlgebra.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  rcases x with ⟨v, w⟩
  have hv : v = default := Subsingleton.elim v default
  subst hv
  simp [equivOfIsometry_apply, he, hf, QuadraticMap.IsometryEquiv.baseChangeProd_tmul]

/-- **Left unit law of `CliffordAlgebra.complexProdTensor`**: when `V` has rank zero with its
positive orientation, conjugating `complexProdTensor` on `ℂ ⊗ F` by `TensorProduct.lid` yields `ρ₂`
transported along any quadratic isometry realizing `(0, w) ↦ w`. No finiteness, orientation,
parity, or metric assumption is placed on `W`. -/
theorem conjAlgEquiv_complexProdTensor_lid (f : Q →qᵢ Q₂)
    (hf : ∀ w, f (WithLp.toLp 2 (default, w)) = w) :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ hn ρ₁ ρ₂) =
      ρ₂.comp (map (f.baseChange ℂ)) := by
  let e : Q.IsometryEquiv (Q₁.prod Q₂) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W), map_app' := fun x ↦ (hQ x).symm }
  rw [complexProdTensor_eq_cliffordProdTensor hQ positiveOrientation hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl),
    ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_cliffordProdTensor_lid _ _ _ _ _
      (by rw [complexVolume_positiveOrientation, map_one]),
    AlgHom.comp_assoc, equivOfIsometry_uniqueProd_comp f hf e (fun _ ↦ rfl)]

/-- Pointwise left unit law: `TensorProduct.lid` intertwines `complexProdTensor` on `ℂ ⊗ F` with
`ρ₂` when `V` has rank zero and carries `positiveOrientation`. -/
theorem lid_complexProdTensor (f : Q →qᵢ Q₂)
    (hf : ∀ w, f (WithLp.toLp 2 (default, w)) = w)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (positiveOrientation : Orientation ℝ V (Fin 0)) hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₂ (map (f.baseChange ℂ) a) (TensorProduct.lid ℂ F z) := by
  have h := congrArg (fun φ ↦ φ a (TensorProduct.lid ℂ F z))
    (conjAlgEquiv_complexProdTensor_lid hQ (hQ₁ := hQ₁) (hn := hn) ρ₁ ρ₂ f hf)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

/-- **Negative-orientation rank-zero sign flip**: when `V` has rank zero with its negative
orientation `-positiveOrientation`, `Γ_V = -1`, so conjugating `complexProdTensor` on `ℂ ⊗ F` by
`TensorProduct.lid` yields the grade-involuted action `ρ₂ ∘ involute`. -/
theorem conjAlgEquiv_complexProdTensor_lid_neg_positiveOrientation (f : Q →qᵢ Q₂)
    (hf : ∀ w, f (WithLp.toLp 2 (default, w)) = w) :
    ((TensorProduct.lid ℂ F).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ (-(positiveOrientation : Orientation ℝ V (Fin 0))) hQ₁ hn ρ₁ ρ₂) =
      (ρ₂.comp involute).comp (map (f.baseChange ℂ)) := by
  let e : Q.IsometryEquiv (Q₁.prod Q₂) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W), map_app' := fun x ↦ (hQ x).symm }
  rw [complexProdTensor_eq_cliffordProdTensor hQ (-positiveOrientation) hQ₁ hn ρ₁ ρ₂ e
      (fun _ ↦ rfl),
    ← AlgHom.comp_assoc,
    AlgHom.conjAlgEquiv_cliffordProdTensor_lid_of_eq_neg_one _ _ _ _ _
      (by rw [complexVolume_neg_orientation, complexVolume_positiveOrientation, map_neg, map_one]),
    AlgHom.comp_assoc, equivOfIsometry_uniqueProd_comp f hf e (fun _ ↦ rfl)]

/-- Pointwise form of `CliffordAlgebra.conjAlgEquiv_complexProdTensor_lid_neg_positiveOrientation`:
under `-positiveOrientation` on a rank-zero left factor, `TensorProduct.lid` intertwines
`complexProdTensor` with `ρ₂ ∘ involute`. -/
theorem lid_complexProdTensor_neg_positiveOrientation (f : Q →qᵢ Q₂)
    (hf : ∀ w, f (WithLp.toLp 2 (default, w)) = w)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : ℂ ⊗[ℂ] F) :
    TensorProduct.lid ℂ F
        (complexProdTensor hQ (-(positiveOrientation : Orientation ℝ V (Fin 0))) hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₂ (involute (map (f.baseChange ℂ) a)) (TensorProduct.lid ℂ F z) := by
  have h := congrArg (fun φ ↦ φ a (TensorProduct.lid ℂ F z))
    (conjAlgEquiv_complexProdTensor_lid_neg_positiveOrientation hQ (hQ₁ := hQ₁) (hn := hn)
      ρ₁ ρ₂ f hf)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end LeftUnit

section RightUnit

variable (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)] (o₁ : Orientation ℝ V (Fin n))
  (hQ₁ : ∀ v, Q₁ v = -‖v‖ ^ 2) (hn : Even n)
  [Unique W]
  {E : Type*} [AddCommGroup E] [Module ℂ E]
  (ρ₁ : CliffordAlgebra (Q₁.baseChange ℂ) →ₐ[ℂ] Module.End ℂ E)
  (ρ₂ : CliffordAlgebra (Q₂.baseChange ℂ) →ₐ[ℂ] Module.End ℂ ℂ)

omit [FiniteDimensional ℝ V] in
/-- Auxiliary diagonal identification for deleting a trivial right factor. -/
private theorem equivOfIsometry_prodUnique_comp (f : Q →qᵢ Q₁)
    (hf : ∀ v, f (WithLp.toLp 2 (v, default)) = v)
    (e : Q.IsometryEquiv (Q₁.prod Q₂)) (he : ∀ x, e x = WithLp.ofLp x) :
    (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique (Q₁.baseChange ℂ)
        (Q₂.baseChange ℂ))).toAlgHom.comp
        (equivOfIsometry (e.baseChangeProd ℂ)).toAlgHom =
      map (f.baseChange ℂ) := by
  apply CliffordAlgebra.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  rcases x with ⟨v, w⟩
  have hw : w = default := Subsingleton.elim w default
  subst hw
  simp [equivOfIsometry_apply, he, hf, QuadraticMap.IsometryEquiv.baseChangeProd_tmul]

/-- **Right unit law of `CliffordAlgebra.complexProdTensor`**: when `W` has rank zero and `F = ℂ`,
conjugating `complexProdTensor` on `E ⊗ ℂ` by `TensorProduct.rid` yields `ρ₁` transported along
any quadratic isometry realizing `(v, 0) ↦ v`. -/
theorem conjAlgEquiv_complexProdTensor_rid (f : Q →qᵢ Q₁)
    (hf : ∀ v, f (WithLp.toLp 2 (v, default)) = v) :
    ((TensorProduct.rid ℂ E).conjAlgEquiv ℂ).toAlgHom.comp
        (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂) =
      ρ₁.comp (map (f.baseChange ℂ)) := by
  let e : Q.IsometryEquiv (Q₁.prod Q₂) :=
    { toLinearEquiv := WithLp.linearEquiv 2 ℝ (V × W), map_app' := fun x ↦ (hQ x).symm }
  rw [complexProdTensor_eq_cliffordProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ e (fun _ ↦ rfl),
    ← AlgHom.comp_assoc, AlgHom.conjAlgEquiv_cliffordProdTensor_rid, AlgHom.comp_assoc,
    equivOfIsometry_prodUnique_comp f hf e (fun _ ↦ rfl)]

/-- Pointwise right unit law: `TensorProduct.rid` intertwines `complexProdTensor` on `E ⊗ ℂ` with
`ρ₁` when `W` has rank zero. -/
theorem rid_complexProdTensor (f : Q →qᵢ Q₁)
    (hf : ∀ v, f (WithLp.toLp 2 (v, default)) = v)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (z : E ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ E (complexProdTensor hQ o₁ hQ₁ hn ρ₁ ρ₂ a z) =
      ρ₁ (map (f.baseChange ℂ) a) (TensorProduct.rid ℂ E z) := by
  have h := congrArg (fun φ ↦ φ a (TensorProduct.rid ℂ E z))
    (conjAlgEquiv_complexProdTensor_rid hQ o₁ hQ₁ hn ρ₁ ρ₂ f hf)
  simpa [LinearEquiv.conjAlgEquiv_apply] using h

end RightUnit

section VolumeElement

/-- **Left unit law for product volume elements**: deleting a positively oriented rank-zero left
factor carries the product normalized complex volume element to that of the right factor, for
arbitrary dimension `m` and arbitrary quadratic form `Q₂`. -/
theorem map_complexVolume_uniqueProd [Unique V] [Fact (finrank ℝ V = 0)]
    [FiniteDimensional ℝ W] {m : ℕ} [Fact (finrank ℝ W = m)]
    [Fact (finrank ℝ (WithLp 2 (V × W)) = 0 + m)]
    (o₂ : Orientation ℝ W (Fin m)) (e : Q.IsometryEquiv Q₂)
    (he : ∀ w, e (WithLp.toLp 2 (default, w)) = w) :
    let o := Orientation.map (Fin (0 + m)) (WithLp.linearEquiv 2 ℝ (V × W)).symm
      ((positiveOrientation : Orientation ℝ V (Fin 0)).prod o₂ Fact.out Fact.out)
    map (e.toIsometry.baseChange ℂ) (complexVolume Q o) = complexVolume Q₂ o₂ := by
  intro o
  have hnorm : ∀ x, ‖e x‖ = ‖x‖ := fun x ↦ by
    rcases x with ⟨v, w⟩
    have hv : v = default := Subsingleton.elim v default
    subst hv
    have h := (LinearIsometryEquiv.withLpUniqueProd 2 ℝ V W).norm_map (WithLp.toLp 2 (default, w))
    simpa [he] using h
  have _ : Fact (finrank ℝ W = 0 + m) :=
    ⟨by rw [Fact.out (p := finrank ℝ W = m), zero_add]⟩
  rw [map_complexVolume o e hnorm]
  let φ : (V × W) ≃ₗ[ℝ] WithLp 2 (V × W) := (WithLp.linearEquiv 2 ℝ (V × W)).symm
  have heq : φ.trans e.toLinearEquiv = (LinearEquiv.uniqueProd : (V × W) ≃ₗ[ℝ] W) := by
    ext ⟨v, w⟩
    have hv : v = default := Subsingleton.elim v default
    subst hv
    simp [φ, he]
  have hmap : o.map (Fin (0 + m)) e.toLinearEquiv =
      Orientation.reindex ℝ W (finCongr (zero_add m)).symm o₂ := by
    calc
      o.map (Fin (0 + m)) e.toLinearEquiv
          = Orientation.map (Fin (0 + m)) (φ.trans e.toLinearEquiv)
              ((positiveOrientation : Orientation ℝ V (Fin 0)).prod o₂ Fact.out Fact.out) := by
            simp only [o, φ, Orientation.map_trans]
      _ = Orientation.map (Fin (0 + m)) (LinearEquiv.uniqueProd : (V × W) ≃ₗ[ℝ] W)
              ((positiveOrientation : Orientation ℝ V (Fin 0)).prod o₂ Fact.out Fact.out) := by
            rw [heq]
      _ = Orientation.reindex ℝ W (finCongr (zero_add m)).symm o₂ :=
            Orientation.map_uniqueProd_prod o₂ Fact.out Fact.out
  rw [hmap, finCongr_symm, complexVolume_reindex o₂ (zero_add m).symm]

/-- **Right unit law for product volume elements**: deleting a positively oriented rank-zero right
factor carries the product normalized complex volume element to that of the left factor, for
arbitrary dimension `n` and arbitrary quadratic form `Q₁`. -/
theorem map_complexVolume_prodUnique [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]
    [Unique W] [Fact (finrank ℝ W = 0)] [Fact (finrank ℝ (WithLp 2 (V × W)) = n + 0)]
    (o₁ : Orientation ℝ V (Fin n)) (e : Q.IsometryEquiv Q₁)
    (he : ∀ v, e (WithLp.toLp 2 (v, default)) = v) :
    let o := Orientation.map (Fin (n + 0)) (WithLp.linearEquiv 2 ℝ (V × W)).symm
      (o₁.prod (positiveOrientation : Orientation ℝ W (Fin 0)) Fact.out Fact.out)
    map (e.toIsometry.baseChange ℂ) (complexVolume Q o) = complexVolume Q₁ o₁ := by
  intro o
  have hnorm : ∀ x, ‖e x‖ = ‖x‖ := fun x ↦ by
    rcases x with ⟨v, w⟩
    have hw : w = default := Subsingleton.elim w default
    subst hw
    have h := (LinearIsometryEquiv.withLpProdUnique 2 ℝ V W).norm_map (WithLp.toLp 2 (v, default))
    simpa [he] using h
  rw [map_complexVolume o e hnorm]
  let φ : (V × W) ≃ₗ[ℝ] WithLp 2 (V × W) := (WithLp.linearEquiv 2 ℝ (V × W)).symm
  have heq : φ.trans e.toLinearEquiv = (LinearEquiv.prodUnique : (V × W) ≃ₗ[ℝ] V) := by
    ext ⟨v, w⟩
    have hw : w = default := Subsingleton.elim w default
    subst hw
    simp [φ, he]
  have hmap : o.map (Fin (n + 0)) e.toLinearEquiv = o₁ := by
    calc
      o.map (Fin (n + 0)) e.toLinearEquiv
          = Orientation.map (Fin (n + 0)) (φ.trans e.toLinearEquiv)
              (o₁.prod (positiveOrientation : Orientation ℝ W (Fin 0)) Fact.out Fact.out) := by
            simp only [o, φ, Orientation.map_trans]
      _ = Orientation.map (Fin (n + 0)) (LinearEquiv.prodUnique : (V × W) ≃ₗ[ℝ] V)
              (o₁.prod (positiveOrientation : Orientation ℝ W (Fin 0)) Fact.out Fact.out) := by
            rw [heq]
      _ = o₁ := Orientation.map_prodUnique_prod o₁ Fact.out Fact.out
  rw [hmap]

end VolumeElement

end CliffordAlgebra
