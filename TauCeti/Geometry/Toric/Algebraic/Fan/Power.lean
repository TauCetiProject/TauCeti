/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

/-!
# Toric power morphisms

For a natural number `q`, multiplication by `q` on the lattice `N` carries every cone of a fan
into itself, so it is an endomorphism of the fan. On the dual side it multiplies every character
by `q`, so on the affine chart of a cone it pulls the monomial `χ^m` back to `χ^(q • m) = (χ^m)^q`
and fixes the coefficients. The induced endomorphism `φ_q` of the toric scheme is therefore the
toric power morphism: it raises every character to its `q`-th power. For `q = 1` it is the
identity (by `TauCeti.Toric.Fan.nsmulHom_one` and `TauCeti.Toric.FanHom.algebraicMap_id`), and
`φ_q ∘ φ_r = φ_(q * r)`.

The power morphism is a morphism over `Spec ℂ` by `TauCeti.Toric.FanHom.isOver_algebraicMap`, so
it fixes the coefficients. It intertwines the torus actions with the `q`-th power of the dense
torus by `TauCeti.Toric.FanHom.algebraicActionMap_comp_algebraicRealizationAction`.

On a chart `R[P_σ]` with coefficients in an arbitrary commutative ring `R`, the same operation is
`AddMonoidAlgebra.mapDomainRingHom` along `nsmulAddMonoidHom q`. For `q ≠ 0` it restricts on the
closed subscheme of every face of `P_σ` to the power map of that face
(`AddSubmonoid.faceRestriction_mapDomainRingHom_nsmul`), and the preimage of its underlying closed
set is that set (`AddSubmonoid.preimage_comap_mapDomainRingHom_nsmul_zeroLocus_faceIdeal`), so the
toric strata are preserved. In characteristic `p` and for `q = p`, it is the relative
Frobenius: composed with the Frobenius of the coefficients it gives the absolute Frobenius
`x ↦ x ^ p`, by `AddMonoidAlgebra.mapRingHom_frobenius_mapDomainRingHom_nsmulAddMonoidHom`.

## Main declarations

* `TauCeti.Toric.Fan.nsmulHom`: the fan endomorphism given by multiplication by `q`.
* `TauCeti.Toric.Fan.nsmulHom_one`, `TauCeti.Toric.Fan.nsmulHom_mul`: the identity and
  composition laws of these endomorphisms.
* `TauCeti.Toric.affineCoordinateRingMap_nsmul`: on the coordinate ring of an affine chart,
  multiplication by `q` acts by raising every monomial to its `q`-th power.
* `TauCeti.Toric.Fan.affineToricChartι_comp_algebraicMap_nsmulHom`: the toric power morphism
  maps every affine chart to itself, by `Spec` of that ring map.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §8, the paragraph preceding
  Theorem 8.5.
* W. Fulton, *Introduction to Toric Varieties*, §1.4.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric

variable {N : Type*} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-! ### Multiplication by `q` on cones and their affine charts -/

section Chart

variable (q : ℕ)

/-- Multiplication by `q` on the lattice is compatible with multiplication by `q` on the ambient
real vector space. -/
theorem nsmul_linearMap_id_apply_lattice (n : N) :
    (q • LinearMap.id : V →ₗ[ℝ] V) (i n) = i (nsmulAddMonoidHom q n) := by
  simp

/-- Multiplication by a natural number carries a cone into itself. -/
theorem mapsTo_nsmul_linearMap_id (σ : PointedCone ℝ V) :
    Set.MapsTo (q • LinearMap.id : V →ₗ[ℝ] V) σ σ := fun x hx ↦ by
  simpa using σ.nsmul_mem hx q

/-- On a dual semigroup, the map induced by multiplication by `q` on the lattice is
multiplication by `q`. -/
theorem dualSemigroupMap_nsmul (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    dualSemigroupMap hi hi (nsmulAddMonoidHom q) (q • LinearMap.id)
        (nsmul_linearMap_id_apply_lattice q) (mapsTo_nsmul_linearMap_id q σ) =
      nsmulAddMonoidHom q := by
  ext m n
  simp

/-- On the coordinate ring of an affine chart, multiplication by `q` on the lattice acts by
raising every monomial to its `q`-th power and fixing the coefficients. -/
theorem affineCoordinateRingMap_nsmul (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    affineCoordinateRingMap hi hi (nsmulAddMonoidHom q) (q • LinearMap.id)
        (nsmul_linearMap_id_apply_lattice q) (mapsTo_nsmul_linearMap_id q σ) =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ (powMonoidHom q) := by
  refine MonoidAlgebra.algHom_ext (fun m ↦ ?_) (Subsingleton.elim _ _)
  rw [← ofAdd_toAdd m, affineCoordinateRingMap_single, dualSemigroupMap_nsmul]
  simp

/-- On the affine toric scheme of a cone, multiplication by `q` on the lattice induces `Spec` of the
ring map raising every monomial to its `q`-th power. -/
theorem affineToricSchemeMap_nsmul (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    affineToricSchemeMap hi hi (nsmulAddMonoidHom q) (q • LinearMap.id)
        (nsmul_linearMap_id_apply_lattice q) (mapsTo_nsmul_linearMap_id q σ) =
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℂ (powMonoidHom q))) := by
  rw [affineToricSchemeMap_def, affineCoordinateRingMap_nsmul]
  -- `MonoidAlgebra.mapDomainAlgHom` is built with `toRingHom := MonoidAlgebra.mapDomainRingHom`.
  rfl

end Chart

/-! ### The power endomorphisms of a fan -/

namespace Fan

variable (Φ : Fan i)

/-- Multiplication by a natural number `q` on the lattice is an endomorphism of every fan, since
it carries each cone into itself. Its induced endomorphism of the toric scheme is the toric power
morphism, which raises every character to its `q`-th power. -/
def nsmulHom (q : ℕ) : FanHom Φ Φ where
  latticeMap := nsmulAddMonoidHom q
  realMap := q • LinearMap.id
  map_lattice := nsmul_linearMap_id_apply_lattice q
  map_cone σ hσ := ⟨σ, hσ, fun _ ⟨_, hx, hxy⟩ ↦ hxy ▸ mapsTo_nsmul_linearMap_id q σ hx⟩

/-- The integral part of the power endomorphism is multiplication by `q`. -/
@[simp]
theorem nsmulHom_latticeMap (q : ℕ) : (Φ.nsmulHom q).latticeMap = nsmulAddMonoidHom q := (rfl)

/-- The real-linear part of the power endomorphism is multiplication by `q`. -/
@[simp]
theorem nsmulHom_realMap (q : ℕ) : (Φ.nsmulHom q).realMap = q • LinearMap.id := (rfl)

/-- Multiplication by `1` is the identity endomorphism of a fan. -/
@[simp]
theorem nsmulHom_one : Φ.nsmulHom 1 = FanHom.id Φ :=
  FanHom.ext <| AddMonoidHom.ext fun n ↦ by simp

/-- Multiplication by `q * r` is the composite of multiplication by `r` and by `q`. -/
theorem nsmulHom_mul (q r : ℕ) : Φ.nsmulHom (q * r) = (Φ.nsmulHom q).comp (Φ.nsmulHom r) :=
  FanHom.ext <| AddMonoidHom.ext fun n ↦ by simp [mul_nsmul']

/-! ### The toric power morphism -/

variable (q : ℕ)

/-- The toric power morphism `φ_q` maps the affine chart of every cone to itself, by `Spec` of the
ring map raising every monomial to its `q`-th power. -/
@[reassoc]
theorem affineToricChartι_comp_algebraicMap_nsmulHom (σ : Φ.cones) :
    Φ.affineToricChartι σ ≫ (Φ.nsmulHom q).algebraicMap =
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℂ (powMonoidHom q))) ≫
        Φ.affineToricChartι σ :=
  ((Φ.nsmulHom q).affineToricChartι_comp_algebraicMap_of_mapsTo σ σ
    (mapsTo_nsmul_linearMap_id q σ.val)).trans
    (congrArg (· ≫ Φ.affineToricChartι σ) (affineToricSchemeMap_nsmul q Φ.lattice σ.val))

/-- The toric power morphisms satisfy `φ_(q * r) = φ_q ∘ φ_r`. -/
theorem algebraicMap_nsmulHom_mul (r : ℕ) :
    (Φ.nsmulHom (q * r)).algebraicMap =
      (Φ.nsmulHom r).algebraicMap ≫ (Φ.nsmulHom q).algebraicMap := by
  rw [nsmulHom_mul, FanHom.algebraicMap_comp]

end Fan

end TauCeti.Toric
