/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Set.PowersetCard
public import TauCeti.LinearAlgebra.ExteriorPower.Basis

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
(`exteriorPower.piZeroEquiv_exteriorPowerCoords`), and in degree one it is `f` itself
(`exteriorPower.piOneEquiv_exteriorPowerCoords`).

These coordinates express exterior powers of vector bundles given by transition matrices,
where the transitions of `⋀^j E` are the compound matrices of those of `E`.

## References

* M. F. Atiyah, *K-Theory*, §1.2.
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
