/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Determinant
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic

/-!
# Functoriality of adelic points

A homomorphism of affine group schemes `φ : G → G'` over `K` is given by a bialgebra map
`φ* : H' → H` of coordinate rings, and it induces on adelic points the homomorphism
`φ_𝔸 : G(𝔸_K) → G'(𝔸_K)`, `x ↦ x ∘ φ*`. This file defines it as
`TauCeti.AdelicPoints.map R φ*`, the precomposition `BialgHom.mapDomain φ*` on
`TauCeti.AdelicPoints R K H`, and proves that

* `φ_𝔸` is continuous for the point topologies;
* the identity induces the identity, and `(φ ∘ ψ)_𝔸 = φ_𝔸 ∘ ψ_𝔸` for `ψ : G₀ → G`, where
  `(φ ∘ ψ)* = ψ* ∘ φ*`;
* `φ_𝔸 (diagonal g) = diagonal (φ g)` for a rational point `g`, where `φ` acts on rational points by
  the same precomposition `BialgHom.mapDomain φ*`;
* `φ_𝔸` commutes with the finite and infinite components and with the local components
  `p_v ∘ φ_𝔸 = φ_v ∘ p_v` at every finite and infinite place, where `φ_v` is again
  `BialgHom.mapDomain φ*` on the local points;
* `φ_𝔸` commutes with the embedding `finiteEmbed` of finite adelic points.

Only the bialgebra structure of the coordinate rings is used; for Hopf algebras these are
homomorphisms of topological groups.

## Main declarations

* `TauCeti.AdelicPoints.map`: the homomorphism `φ_𝔸` of adelic points.
* `TauCeti.AdelicPoints.continuous_map`, `TauCeti.AdelicPoints.map_id`,
  `TauCeti.AdelicPoints.map_comp`.
* `TauCeti.AdelicPoints.map_diagonal`: compatibility with the rational diagonal.
* `TauCeti.AdelicPoints.localProjection_map`, `TauCeti.AdelicPoints.infinitePlaceProjection_map`:
  compatibility with the local components.
* `TauCeti.AdelicPoints.map_determinantCoordinateMap`,
  `TauCeti.AdelicPoints.pointsMulEquiv_map_determinantCoordinateMap`: the determinant
  `GLₙ → 𝔾ₘ` induces on adelic points the determinant of invertible adelic matrices.
* `TauCeti.AdelicPoints.pointsMulEquiv_map_determinantCoordinateMap_one`: for `n = 1`, the
  identification of `GL₁(𝔸_K)` with the ideles `𝔸_K^×` by the entry of a one-by-one matrix.

## References

* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.3, p. 7.
-/

public section

open IsDedekindDomain NumberField WithConv

namespace TauCeti

namespace AdelicPoints

variable (R : Type*) {K H H' H'' : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Semiring H] [Bialgebra K H] [Semiring H'] [Bialgebra K H']
  [Semiring H''] [Bialgebra K H'']

/-- The homomorphism `φ_𝔸 : G(𝔸_K) → G'(𝔸_K)` of adelic points induced by a homomorphism
`φ : G → G'` of affine group schemes, given by its coordinate map `φ* : H' → H`: an adelic point
`x : H → 𝔸_K` is sent to `x ∘ φ*`. -/
noncomputable def map (φ : H' →ₐc[K] H) : AdelicPoints R K H →* AdelicPoints R K H' :=
  BialgHom.mapDomain φ

variable {R}

/-- The map of adelic points is the precomposition `BialgHom.mapDomain φ*`. -/
theorem map_def (φ : H' →ₐc[K] H) : map R φ = BialgHom.mapDomain φ :=
  (rfl)

@[simp]
theorem map_apply_apply (φ : H' →ₐc[K] H) (x : AdelicPoints R K H) (h : H') :
    map R φ x h = x (φ h) :=
  BialgHom.mapDomain_apply_apply φ x h

/-- The map of adelic points induced by a homomorphism of affine group schemes is continuous. -/
@[fun_prop]
theorem continuous_map (φ : H' →ₐc[K] H) : Continuous (map R φ) :=
  BialgHom.continuous_mapDomain φ

/-- The identity homomorphism induces the identity on adelic points. -/
@[simp]
theorem map_id : map R (BialgHom.id K H) = MonoidHom.id (AdelicPoints R K H) :=
  BialgHom.mapDomain_id

/-- Functoriality: for `ψ : G₀ → G` and `φ : G → G'` with coordinate maps `ψ* : H → H''` and
`φ* : H' → H`, the composite `φ ∘ ψ`, with coordinate map `ψ* ∘ φ*`, induces `φ_𝔸 ∘ ψ_𝔸`. -/
theorem map_comp (ψ : H →ₐc[K] H'') (φ : H' →ₐc[K] H) :
    map R (ψ.comp φ) = (map R φ).comp (map R ψ) :=
  BialgHom.mapDomain_comp ψ φ

@[simp]
theorem map_map (ψ : H →ₐc[K] H'') (φ : H' →ₐc[K] H) (x : AdelicPoints R K H'') :
    map R φ (map R ψ x) = map R (ψ.comp φ) x :=
  (DFunLike.congr_fun (map_comp ψ φ) x).symm

/-- `φ_𝔸 (diagonal g) = diagonal (φ g)`: the map of adelic points restricts on the rational
diagonal to the map of rational points. -/
@[simp]
theorem map_diagonal (φ : H' →ₐc[K] H) (g : WithConv (H →ₐ[K] K)) :
    map R φ (diagonal R K H g) = diagonal R K H' (BialgHom.mapDomain φ g) :=
  ofConv_injective (AlgHom.ext fun h ↦ by simp)

/-- The finite component of `φ_𝔸 x` is the image of the finite component of `x`. -/
@[simp]
theorem finiteProjection_map (φ : H' →ₐc[K] H) (x : AdelicPoints R K H) :
    finiteProjection R K H' (map R φ x) = BialgHom.mapDomain φ (finiteProjection R K H x) :=
  ofConv_injective (AlgHom.ext fun h ↦ by simp)

/-- The infinite component of `φ_𝔸 x` is the image of the infinite component of `x`. -/
@[simp]
theorem infiniteProjection_map (φ : H' →ₐc[K] H) (x : AdelicPoints R K H) :
    infiniteProjection R K H' (map R φ x) = BialgHom.mapDomain φ (infiniteProjection R K H x) :=
  ofConv_injective (AlgHom.ext fun h ↦ by simp)

/-- `p_v ∘ φ_𝔸 = φ_v ∘ p_v` at a finite place `v`. -/
@[simp]
theorem localProjection_map (φ : H' →ₐc[K] H) (v : HeightOneSpectrum R)
    (x : AdelicPoints R K H) :
    localProjection R K H' v (map R φ x) = BialgHom.mapDomain φ (localProjection R K H v x) :=
  ofConv_injective (AlgHom.ext fun h ↦ by simp)

/-- `p_w ∘ φ_𝔸 = φ_w ∘ p_w` at an infinite place `w`. -/
@[simp]
theorem infinitePlaceProjection_map (φ : H' →ₐc[K] H) (w : InfinitePlace K)
    (x : AdelicPoints R K H) :
    infinitePlaceProjection R K H' w (map R φ x) =
      BialgHom.mapDomain φ (infinitePlaceProjection R K H w x) :=
  ofConv_injective (AlgHom.ext fun h ↦ by simp)

/-- The map of adelic points sends the finite embedding of a finite adelic point `x` to the finite
embedding of the image of `x`. -/
@[simp]
theorem map_finiteEmbed (φ : H' →ₐc[K] H) (x : FiniteAdelicPoints R K H) :
    map R φ (finiteEmbed R K H x) = finiteEmbed R K H' (BialgHom.mapDomain φ x) :=
  ofConv_injective (AlgHom.ext fun h ↦ by simp [CoalgHomClass.counit_comp_apply])

/-! ### The determinant of `GL₁` -/

section GeneralLinear

open GeneralLinear in
/-- The determinant `det : GLₙ → 𝔾ₘ` induces on adelic points the determinant map of points
`determinantPoints`. -/
theorem map_determinantCoordinateMap (n : ℕ) :
    map R (determinantCoordinateMap K n).hom = determinantPoints K n :=
  MonoidHom.ext fun x ↦ ofConv_injective (AlgHom.ext fun h ↦ by
    rw [map_apply_apply, determinantPoints_apply_apply])

open GeneralLinear in
/-- The determinant `det : GLₙ → 𝔾ₘ` induces on adelic points the determinant of invertible adelic
matrices, under the canonical identifications of `GLₙ(𝔸_K)` with `GLₙ(𝔸_K)` and of `𝔾ₘ(𝔸_K)`
with `𝔸_K^×`. -/
theorem pointsMulEquiv_map_determinantCoordinateMap (n : ℕ)
    (x : AdelicPoints R K (coordinateHopfAlgebra K n)) :
    DiagonalizableGroup.pointsMulEquiv (map R (determinantCoordinateMap K n).hom x)
        (Multiplicative.ofAdd 1) =
      Matrix.GeneralLinearGroup.det (pointsMulEquiv n x) := by
  rw [map_determinantCoordinateMap, pointsMulEquiv_determinantPoints]

open GeneralLinear in
/-- For `GL₁` the determinant `det : GL₁ → 𝔾ₘ` induces on adelic points the identity of the
ideles under the canonical identification of `GL₁(𝔸_K)` with `𝔸_K^×`: the idele given by the
image of `x` in `𝔾ₘ(𝔸_K)` is the single entry of the one-by-one matrix `x`. -/
theorem pointsMulEquiv_map_determinantCoordinateMap_one
    (x : AdelicPoints R K (coordinateHopfAlgebra K 1)) :
    ((DiagonalizableGroup.pointsMulEquiv (map R (determinantCoordinateMap K 1).hom x)
        (Multiplicative.ofAdd 1) : (AdeleRing R K)ˣ) : AdeleRing R K) =
      (pointsMulEquiv 1 x : Matrix (Fin 1) (Fin 1) (AdeleRing R K)) 0 0 := by
  rw [pointsMulEquiv_map_determinantCoordinateMap, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_unique, Fin.default_eq_zero]

end GeneralLinear

end AdelicPoints

end TauCeti
