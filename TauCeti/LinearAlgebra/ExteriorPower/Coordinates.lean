/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Set.PowersetCard
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.ExteriorPower.Prod
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Exterior powers of coordinate spaces in coordinates

The `j`th exterior power of the coordinate space `Fin m → R` is free on the wedges of standard
basis vectors indexed by the `j`-element subsets of `Fin m` (Mathlib's
`Module.Basis.exteriorPower`). Enumerating these subsets by `Fin (m.choose j)` gives the
coordinate identification `exteriorPower.piEquiv R m j` of `⋀[R]^j (Fin m → R)` with the
coordinate space `Fin (m.choose j) → R`.

Reading `exteriorPower.map j f` through these identifications gives
`LinearMap.exteriorPowerCoords j f`, the `j`th compound matrix of `f`. It is functorial
(`LinearMap.exteriorPowerCoords_id`, `LinearMap.exteriorPowerCoords_comp`), and its matrix
entries are the `j × j` minors of the matrix of `f` (`LinearMap.exteriorPowerCoords_single_apply`).
In degree zero it is the identity after identifying the coordinate space with the coordinate line
(`exteriorPower.piZeroEquiv_exteriorPowerCoords`), in degree one it is `f` itself
(`exteriorPower.piOneEquiv_exteriorPowerCoords`), and for an endomorphism of `Fin m → R` in the top
degree `m` it is multiplication by the determinant (`LinearMap.exteriorPowerCoords_self`).

For concatenated coordinates `Fin (a + d) → R`, transporting `TauCeti.exteriorPower.wedgeTensor`
and `TauCeti.exteriorPower.prodProj` across `exteriorPower.piEquiv`, `TauCeti.piTensorEquiv` and
`LinearEquiv.piFinAppend` gives the coordinate Künneth inclusions `TauCeti.exteriorPower.piProdInl`
and projections `TauCeti.exteriorPower.piProdProj`. They are mutually orthogonal, resolve the
identity of `Fin ((a + d).choose n) → R`, reduce to an isomorphism in the top degree `a + d`, and
intertwine the compound matrix of a block-diagonal map with the tensor products of the summand
compound matrices.

These coordinates express exterior powers of vector bundles given by transition matrices,
where the transitions of `⋀^j E` are the compound matrices of those of `E`.

## References

* M. F. Atiyah, *K-Theory*, §1.2.
* N. Bourbaki, *Algebra I*, Chapter III, §7.7.
* The coordinates use Mathlib's exterior-power basis from
  `Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison.
-/

public section

open Module

namespace exteriorPower

variable (R : Type*) [CommRing R]

/-- The basis of `⋀[R]^j (Fin m → R)` by wedges of standard basis vectors, indexed by
`Fin (m.choose j)` through `Set.powersetCard.finChooseEquiv`. -/
noncomputable def piBasis (m j : ℕ) : Basis (Fin (m.choose j)) R (⋀[R]^j (Fin m → R)) :=
  ((Pi.basisFun R (Fin m)).exteriorPower j).reindex (Set.powersetCard.finChooseEquiv m j)

/-- The basis vector indexed by `s` is the wedge of the standard basis vectors in the subset
enumerated by `s`, in increasing order. -/
theorem piBasis_apply (m j : ℕ) (s : Fin (m.choose j)) :
    piBasis R m j s = ιMulti_family R j (Pi.basisFun R (Fin m))
      ((Set.powersetCard.finChooseEquiv m j).symm s) := by
  rw [piBasis, Basis.reindex_apply, basis_apply]

/-- The coordinates of `⋀[R]^j (Fin m → R)` in the basis `exteriorPower.piBasis`. -/
noncomputable def piEquiv (m j : ℕ) : ⋀[R]^j (Fin m → R) ≃ₗ[R] (Fin (m.choose j) → R) :=
  (piBasis R m j).equivFun

/-- The coordinate indexed by `s` is the coefficient of the wedge of standard basis vectors in the
subset enumerated by `s`. -/
theorem piEquiv_apply (m j : ℕ) (x : ⋀[R]^j (Fin m → R)) (s : Fin (m.choose j)) :
    piEquiv R m j x s =
      ((Pi.basisFun R (Fin m)).exteriorPower j).repr x
        ((Set.powersetCard.finChooseEquiv m j).symm s) := by
  rw [piEquiv, Basis.equivFun_apply, piBasis, Basis.repr_reindex_apply]

theorem piEquiv_symm_apply_single (m j : ℕ) (s : Fin (m.choose j)) :
    (piEquiv R m j).symm (Pi.single s 1) = piBasis R m j s := by
  simp [piEquiv, Basis.equivFun_symm_apply, Pi.single_apply]

end exteriorPower

namespace LinearMap

open exteriorPower

variable {R : Type*} [CommRing R]

/-- The `j`th exterior power of a linear map between coordinate spaces, in the coordinates
`exteriorPower.piEquiv`: the `j`th compound matrix of the map. -/
noncomputable def exteriorPowerCoords (j : ℕ) {m n : ℕ} (f : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (Fin (m.choose j) → R) →ₗ[R] (Fin (n.choose j) → R) :=
  (piEquiv R n j).toLinearMap ∘ₗ map j f ∘ₗ (piEquiv R m j).symm.toLinearMap

/-- The compound map corresponds to the exterior-power map under the coordinates. -/
@[simp] theorem exteriorPowerCoords_piEquiv (j : ℕ) {m n : ℕ}
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) (x : ⋀[R]^j (Fin m → R)) :
    f.exteriorPowerCoords j (piEquiv R m j x) = piEquiv R n j (map j f x) := by
  simp [exteriorPowerCoords]

theorem piEquiv_symm_exteriorPowerCoords (j : ℕ) {m n : ℕ}
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) (v : Fin (m.choose j) → R) :
    (piEquiv R n j).symm (f.exteriorPowerCoords j v) = map j f ((piEquiv R m j).symm v) := by
  simp [exteriorPowerCoords]

@[simp] theorem exteriorPowerCoords_id (j m : ℕ) :
    (LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R)).exteriorPowerCoords j = LinearMap.id := by
  ext v : 1
  simp [exteriorPowerCoords, map_id]

@[simp] theorem exteriorPowerCoords_comp (j : ℕ) {l m n : ℕ} (g : (Fin m → R) →ₗ[R] (Fin n → R))
    (f : (Fin l → R) →ₗ[R] (Fin m → R)) :
    (g ∘ₗ f).exteriorPowerCoords j = g.exteriorPowerCoords j ∘ₗ f.exteriorPowerCoords j :=
  LinearMap.ext fun v ↦ by simp [exteriorPowerCoords, map_comp]

/-- The entries of the `j`th compound matrix are the `j × j` minors of the original matrix, with
rows and columns selected by the enumerated subsets in increasing order. -/
theorem exteriorPowerCoords_single_apply (j : ℕ) {m n : ℕ} (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (t : Fin (m.choose j)) (s : Fin (n.choose j)) :
    f.exteriorPowerCoords j (Pi.single t 1) s =
      (Matrix.of fun i k : Fin j ↦ f
        (Pi.single (Set.powersetCard.ofFinEmbEquiv.symm
          ((Set.powersetCard.finChooseEquiv m j).symm t) i) 1)
        (Set.powersetCard.ofFinEmbEquiv.symm
          ((Set.powersetCard.finChooseEquiv n j).symm s) k)).det := by
  have h := Basis.toMatrix_exteriorPower_map (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) j
    f ((Set.powersetCard.finChooseEquiv n j).symm s)
    ((Set.powersetCard.finChooseEquiv m j).symm t)
  simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply] at h
  rw [← h]
  simp [exteriorPowerCoords, piEquiv_symm_apply_single, piEquiv_apply, piBasis]

/-- In the top degree, the compound matrix of an endomorphism of `Fin m → R` is multiplication
by its determinant on the coordinate line `Fin (m.choose m) → R`. -/
@[simp] theorem exteriorPowerCoords_self {m : ℕ} (f : (Fin m → R) →ₗ[R] (Fin m → R)) :
    f.exteriorPowerCoords m = LinearMap.det f • LinearMap.id := by
  refine LinearMap.ext fun v ↦ ?_
  simp [exteriorPowerCoords, (Pi.basisFun R (Fin m)).map_exteriorPower_top_eq_det_smul f]

end LinearMap

namespace exteriorPower

variable {R : Type*} [CommRing R]

/-- The degree-zero coordinate space is the coordinate line, through
`exteriorPower.zeroEquiv`. -/
noncomputable def piZeroEquiv (m : ℕ) : (Fin (m.choose 0) → R) ≃ₗ[R] (Fin 1 → R) :=
  (piEquiv R m 0).symm ≪≫ₗ zeroEquiv R (Fin m → R) ≪≫ₗ (LinearEquiv.funUnique (Fin 1) R R).symm

/-- In degree zero, the coordinate of an exterior scalar is that scalar,
through `exteriorPower.zeroEquiv`. -/
@[simp] theorem piZeroEquiv_piEquiv (m : ℕ) (x : ⋀[R]^0 (Fin m → R)) :
    piZeroEquiv m (piEquiv R m 0 x) = fun _ ↦ zeroEquiv R (Fin m → R) x := by
  ext
  simp [piZeroEquiv]

/-- In degree zero, every compound map is the identity, read in `exteriorPower.piZeroEquiv`. -/
@[simp] theorem piZeroEquiv_exteriorPowerCoords {m n : ℕ} (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (v : Fin (m.choose 0) → R) :
    piZeroEquiv n (f.exteriorPowerCoords 0 v) = piZeroEquiv m v := by
  simp only [piZeroEquiv, LinearEquiv.trans_apply, LinearMap.piEquiv_symm_exteriorPowerCoords]
  congr 1
  exact congrArg (fun g : ⋀[R]^0 (Fin m → R) →ₗ[R] R ↦ g ((piEquiv R m 0).symm v))
    (zeroEquiv_naturality f)

/-- The degree-one coordinate space is the original coordinate space, through
`exteriorPower.oneEquiv`. -/
noncomputable def piOneEquiv (m : ℕ) : (Fin (m.choose 1) → R) ≃ₗ[R] (Fin m → R) :=
  (piEquiv R m 1).symm ≪≫ₗ oneEquiv R (Fin m → R)

/-- In degree one, the coordinates of an exterior vector are those of the vector,
through `exteriorPower.oneEquiv`. -/
@[simp] theorem piOneEquiv_piEquiv (m : ℕ) (x : ⋀[R]^1 (Fin m → R)) :
    piOneEquiv m (piEquiv R m 1 x) = oneEquiv R (Fin m → R) x := by
  simp [piOneEquiv]

/-- In degree one, the compound map of `f` is `f`, read in `exteriorPower.piOneEquiv`. -/
@[simp] theorem piOneEquiv_exteriorPowerCoords {m n : ℕ} (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (v : Fin (m.choose 1) → R) :
    piOneEquiv n (f.exteriorPowerCoords 1 v) = f (piOneEquiv m v) := by
  simp only [piOneEquiv, LinearEquiv.trans_apply, LinearMap.piEquiv_symm_exteriorPowerCoords]
  exact congrArg (fun g : ⋀[R]^1 (Fin m → R) →ₗ[R] (Fin n → R) ↦ g ((piEquiv R m 1).symm v))
    (oneEquiv_naturality f)

end exteriorPower

namespace TauCeti.exteriorPower

open scoped TensorProduct

variable {R : Type*} [CommRing R]

variable (R) in
/-- The bidegree-`(p, q)` Künneth inclusion `(Fin (a.choose p * d.choose q) → R) →ₗ[R]
(Fin ((a + d).choose n) → R)` in exterior-power coordinates, transporting `wedgeTensor` across
`_root_.exteriorPower.piEquiv`, `TauCeti.piTensorEquiv` and `LinearEquiv.piFinAppend`. -/
noncomputable def piProdInl (a d p q n : ℕ) (h : p + q = n) :
    (Fin (a.choose p * d.choose q) → R) →ₗ[R] (Fin ((a + d).choose n) → R) :=
  (_root_.exteriorPower.piEquiv R (a + d) n).toLinearMap ∘ₗ
    _root_.exteriorPower.map n (LinearEquiv.piFinAppend R R a d).symm.toLinearMap ∘ₗ
    wedgeTensor R (Fin a → R) (Fin d → R) p q n h ∘ₗ
    TensorProduct.map (_root_.exteriorPower.piEquiv R a p).symm.toLinearMap
      (_root_.exteriorPower.piEquiv R d q).symm.toLinearMap ∘ₗ
    (piTensorEquiv R (a.choose p) (d.choose q)).symm.toLinearMap

variable (R) in
/-- The bidegree-`(p, q)` Künneth projection `(Fin ((a + d).choose n) → R) →ₗ[R]
(Fin (a.choose p * d.choose q) → R)` in exterior-power coordinates, transporting `prodProj` across
`_root_.exteriorPower.piEquiv`, `TauCeti.piTensorEquiv` and `LinearEquiv.piFinAppend`. -/
noncomputable def piProdProj (a d p q n : ℕ) :
    (Fin ((a + d).choose n) → R) →ₗ[R] (Fin (a.choose p * d.choose q) → R) :=
  (piTensorEquiv R (a.choose p) (d.choose q)).toLinearMap ∘ₗ
    TensorProduct.map (_root_.exteriorPower.piEquiv R a p).toLinearMap
      (_root_.exteriorPower.piEquiv R d q).toLinearMap ∘ₗ
    prodProj R (Fin a → R) (Fin d → R) p q n ∘ₗ
    _root_.exteriorPower.map n (LinearEquiv.piFinAppend R R a d).toLinearMap ∘ₗ
    (_root_.exteriorPower.piEquiv R (a + d) n).symm.toLinearMap

private theorem map_piFinAppend_comp_symm (a d n : ℕ)
    (x : ⋀[R]^n ((Fin a → R) × (Fin d → R))) :
    _root_.exteriorPower.map n (LinearEquiv.piFinAppend R R a d).toLinearMap
      (_root_.exteriorPower.map n (LinearEquiv.piFinAppend R R a d).symm.toLinearMap x) = x := by
  rw [← LinearMap.comp_apply, ← _root_.exteriorPower.map_comp, LinearEquiv.comp_coe,
    LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, _root_.exteriorPower.map_id,
    LinearMap.id_apply]

private theorem map_piFinAppend_symm_comp (a d n : ℕ)
    (x : ⋀[R]^n (Fin (a + d) → R)) :
    _root_.exteriorPower.map n (LinearEquiv.piFinAppend R R a d).symm.toLinearMap
      (_root_.exteriorPower.map n (LinearEquiv.piFinAppend R R a d).toLinearMap x) = x := by
  rw [← LinearMap.comp_apply, ← _root_.exteriorPower.map_comp, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, _root_.exteriorPower.map_id,
    LinearMap.id_apply]

private theorem tensorMap_piEquiv_comp_symm (a d p q : ℕ)
    (z : (Fin (a.choose p) → R) ⊗[R] (Fin (d.choose q) → R)) :
    TensorProduct.map (_root_.exteriorPower.piEquiv R a p).toLinearMap
      (_root_.exteriorPower.piEquiv R d q).toLinearMap
      (TensorProduct.map (_root_.exteriorPower.piEquiv R a p).symm.toLinearMap
        (_root_.exteriorPower.piEquiv R d q).symm.toLinearMap z) = z := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearEquiv.comp_coe,
    LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, LinearEquiv.refl_toLinearMap, TensorProduct.map_id,
    LinearMap.id_apply]

private theorem tensorMap_piEquiv_symm_comp (a d p q : ℕ)
    (z : ⋀[R]^p (Fin a → R) ⊗[R] ⋀[R]^q (Fin d → R)) :
    TensorProduct.map (_root_.exteriorPower.piEquiv R a p).symm.toLinearMap
      (_root_.exteriorPower.piEquiv R d q).symm.toLinearMap
      (TensorProduct.map (_root_.exteriorPower.piEquiv R a p).toLinearMap
        (_root_.exteriorPower.piEquiv R d q).toLinearMap z) = z := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearEquiv.comp_coe,
    LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.self_trans_symm,
    LinearEquiv.refl_toLinearMap, LinearEquiv.refl_toLinearMap, TensorProduct.map_id,
    LinearMap.id_apply]

/-- `piProdProj` is left inverse to `piProdInl` in matching bidegree. -/
@[simp]
theorem piProdProj_comp_piProdInl_self (a d p q n : ℕ) (h : p + q = n) :
    piProdProj R a d p q n ∘ₗ piProdInl R a d p q n h = LinearMap.id := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [piProdProj, piProdInl, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, map_piFinAppend_comp_symm, prodProj_wedgeTensor_self,
    tensorMap_piEquiv_comp_symm, LinearEquiv.apply_symm_apply, LinearMap.id_apply]

/-- `piProdProj` vanishes on the image of `piProdInl` in any differing bidegree. -/
theorem piProdProj_comp_piProdInl_of_ne {a d p' q' p q n : ℕ} (h : p + q = n)
    (hne : p ≠ p' ∨ q ≠ q') :
    piProdProj R a d p' q' n ∘ₗ piProdInl R a d p q n h = 0 := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [piProdProj, piProdInl, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, map_piFinAppend_comp_symm,
    prodProj_wedgeTensor_of_ne h hne, map_zero, LinearMap.zero_apply]

/-- The coordinate Künneth projections and inclusions resolve the identity of
`Fin ((a + d).choose n) → R`. -/
theorem sum_piProdInl_comp_piProdProj (a d n : ℕ) :
    ∑ i : Fin (n + 1),
      piProdInl R a d i (n - i) n (by omega) ∘ₗ piProdProj R a d i (n - i) n = LinearMap.id := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [LinearMap.sum_apply, piProdInl, piProdProj, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply, tensorMap_piEquiv_symm_comp,
    LinearMap.id_apply]
  rw [← map_sum, ← map_sum, sum_wedgeTensor_prodProj, map_piFinAppend_symm_comp,
    LinearEquiv.apply_symm_apply]

/-- `piProdProj` vanishes outside total degree `n`. -/
theorem piProdProj_eq_zero_of_add_ne {a d p q n : ℕ} (h : p + q ≠ n) :
    piProdProj R a d p q n = 0 := by
  simp [piProdProj, prodProj_eq_zero_of_add_ne h]

/-- In the top degree `a + d`, the single bidegree `(a, d)` Künneth projection and inclusion are
two-sided inverses: every other summand has degree exceeding the rank of one of the two factors. -/
@[simp]
theorem piProdInl_comp_piProdProj_top (a d : ℕ) :
    piProdInl R a d a d (a + d) rfl ∘ₗ piProdProj R a d a d (a + d) = LinearMap.id := by
  refine LinearMap.ext fun v ↦ ?_
  have hv := DFunLike.congr_fun (sum_piProdInl_comp_piProdProj (R := R) a d (a + d)) v
  simp only [LinearMap.sum_apply, LinearMap.id_apply] at hv
  rw [Finset.sum_eq_single ⟨a, by omega⟩] at hv
  · have hcast : ∀ (q : ℕ) (_ : q = d) (h : a + q = a + d),
        (piProdInl R a d a q (a + d) h ∘ₗ piProdProj R a d a q (a + d)) v =
          (piProdInl R a d a d (a + d) rfl ∘ₗ piProdProj R a d a d (a + d)) v := by
      rintro _ rfl _
      rfl
    exact (hcast (a + d - a) (Nat.add_sub_cancel_left a d) (by omega)).symm.trans hv
  · rintro i - hi
    have hne : (i : ℕ) ≠ a := fun h ↦ hi (Fin.ext h)
    have hzero : a.choose i * d.choose (a + d - i) = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [Nat.choose_eq_zero_of_lt (by omega : d < a + d - i), mul_zero]
      · rw [Nat.choose_eq_zero_of_lt hgt, zero_mul]
    have hsub : Subsingleton (Fin (a.choose i * d.choose (a + d - i)) → R) := by
      rw [hzero]
      infer_instance
    simp only [LinearMap.comp_apply]
    rw [Subsingleton.elim (piProdProj R a d i (a + d - i) (a + d) v) 0, map_zero]
  · simp

/-- `piProdInl` intertwines the tensor product of compound matrices with the compound matrix of a
block-diagonal map on concatenated coordinates. -/
theorem exteriorPowerCoords_piFinAppend_comp_piProdInl {a a' d d' : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin a' → R)) (g : (Fin d → R) →ₗ[R] (Fin d' → R))
    (p q n : ℕ) (h : p + q = n) :
    ((LinearEquiv.piFinAppend R R a' d').symm.toLinearMap ∘ₗ f.prodMap g ∘ₗ
        (LinearEquiv.piFinAppend R R a d).toLinearMap).exteriorPowerCoords n ∘ₗ
      piProdInl R a d p q n h =
    piProdInl R a' d' p q n h ∘ₗ
      (piTensorEquiv R (a'.choose p) (d'.choose q)).toLinearMap ∘ₗ
      TensorProduct.map (f.exteriorPowerCoords p) (g.exteriorPowerCoords q) ∘ₗ
      (piTensorEquiv R (a.choose p) (d.choose q)).symm.toLinearMap := by
  refine LinearMap.ext fun v ↦ ?_
  have hfg : ((LinearEquiv.piFinAppend R R a' d').symm.toLinearMap ∘ₗ f.prodMap g ∘ₗ
        (LinearEquiv.piFinAppend R R a d).toLinearMap) ∘ₗ
      (LinearEquiv.piFinAppend R R a d).symm.toLinearMap =
    (LinearEquiv.piFinAppend R R a' d').symm.toLinearMap ∘ₗ f.prodMap g :=
    LinearMap.ext fun _ ↦ by simp
  have htp : ∀ z,
      TensorProduct.map (_root_.exteriorPower.piEquiv R a' p).symm.toLinearMap
        (_root_.exteriorPower.piEquiv R d' q).symm.toLinearMap
        (TensorProduct.map (f.exteriorPowerCoords p) (g.exteriorPowerCoords q) z) =
      TensorProduct.map (_root_.exteriorPower.map p f) (_root_.exteriorPower.map q g)
        (TensorProduct.map (_root_.exteriorPower.piEquiv R a p).symm.toLinearMap
          (_root_.exteriorPower.piEquiv R d q).symm.toLinearMap z) := by
    intro z
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp]
    congr 2 <;> refine LinearMap.ext fun w ↦ ?_ <;>
      simp [LinearMap.piEquiv_symm_exteriorPowerCoords]
  simp only [piProdInl, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  rw [LinearMap.exteriorPowerCoords]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  rw [← LinearMap.comp_apply (_root_.exteriorPower.map n _), ← _root_.exteriorPower.map_comp, hfg,
    _root_.exteriorPower.map_comp, LinearMap.comp_apply, map_prodMap_wedgeTensor_apply, ← htp]

/-- `piProdProj` intertwines the compound matrix of a block-diagonal map on concatenated
coordinates with the tensor product of compound matrices. -/
theorem piProdProj_comp_exteriorPowerCoords_piFinAppend {a a' d d' : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin a' → R)) (g : (Fin d → R) →ₗ[R] (Fin d' → R))
    (p q n : ℕ) :
    piProdProj R a' d' p q n ∘ₗ
      ((LinearEquiv.piFinAppend R R a' d').symm.toLinearMap ∘ₗ f.prodMap g ∘ₗ
        (LinearEquiv.piFinAppend R R a d).toLinearMap).exteriorPowerCoords n =
    (piTensorEquiv R (a'.choose p) (d'.choose q)).toLinearMap ∘ₗ
      TensorProduct.map (f.exteriorPowerCoords p) (g.exteriorPowerCoords q) ∘ₗ
      (piTensorEquiv R (a.choose p) (d.choose q)).symm.toLinearMap ∘ₗ
      piProdProj R a d p q n := by
  refine LinearMap.ext fun v ↦ ?_
  have hfg : (LinearEquiv.piFinAppend R R a' d').toLinearMap ∘ₗ
      ((LinearEquiv.piFinAppend R R a' d').symm.toLinearMap ∘ₗ f.prodMap g ∘ₗ
        (LinearEquiv.piFinAppend R R a d).toLinearMap) =
    f.prodMap g ∘ₗ (LinearEquiv.piFinAppend R R a d).toLinearMap :=
    LinearMap.ext fun _ ↦ by simp
  have htp : ∀ z,
      TensorProduct.map (_root_.exteriorPower.piEquiv R a' p).toLinearMap
        (_root_.exteriorPower.piEquiv R d' q).toLinearMap
        (TensorProduct.map (_root_.exteriorPower.map p f) (_root_.exteriorPower.map q g) z) =
      TensorProduct.map (f.exteriorPowerCoords p) (g.exteriorPowerCoords q)
        (TensorProduct.map (_root_.exteriorPower.piEquiv R a p).toLinearMap
          (_root_.exteriorPower.piEquiv R d q).toLinearMap z) := by
    intro z
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp]
    congr 2 <;> refine LinearMap.ext fun w ↦ ?_ <;> simp [LinearMap.exteriorPowerCoords_piEquiv]
  simp only [piProdProj, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  rw [LinearMap.exteriorPowerCoords]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  rw [← LinearMap.comp_apply (_root_.exteriorPower.map n _), ← _root_.exteriorPower.map_comp, hfg,
    _root_.exteriorPower.map_comp, LinearMap.comp_apply, prodProj_map_prodMap, htp]

end TauCeti.exteriorPower
