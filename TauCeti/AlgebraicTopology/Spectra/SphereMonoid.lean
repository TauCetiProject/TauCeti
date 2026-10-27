/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Spectra.SymmetricSpectrum
public import TauCeti.CategoryTheory.Monoidal.Mod.Comap

/-!
# The higher sphere monoids `S^(k)`

For a pointed simplicial set `X`, the symmetric sequence `n ↦ X^∧n` of smash powers, with
`Σ_n` permuting the smash factors and block concatenation `X^∧p ∧ X^∧q ≅ X^∧(p+q)`, is a
commutative monoid for the Day convolution product (`SymmetricSequence.smashPow X`). This is
Hovey's symmetric algebra `Sym(X)`, the free commutative monoid on `X` placed in level one, whose
modules are the symmetric spectra based on `X`. A based map `X ⟶ Y` applied in every coordinate is
a morphism of these monoids.

Taking `X` to be the simplicial `k`-sphere `S^k = (S¹)^∧k` gives the sphere monoid
`S^(k) = SymmetricSequence.sphereMonoid k`. Its `n`-th level is `(S^k)^∧n`, on which `Σ_n` acts
by permuting the `n` blocks of `k` circle coordinates, and its multiplication concatenates
blocks. Its modules, `SphereModule k`, are the symmetric spectra based on the `k`-sphere: the
structure maps have the form `(S^k)^∧p ∧ X_q → X_(p+q)`. They are the input of comparisons between
symmetric spectra indexed on different spheres, such as stabilization with respect to `S²`.

For `k = 1` the identification `(S¹)^∧1 ≅ S¹` of the single smash factor gives an isomorphism of
monoids `S^(1) ≅ S` with the sphere sequence (`SymmetricSequence.sphereMonoidOneIso`), so
restricting scalars identifies symmetric spectra with `S^(1)`-modules
(`SymmetricSpectrum.sphereModuleOneEquivalence`). The underlying symmetric sequences are not
changed: the chosen category of symmetric spectra is the `k = 1` instance of this family.

## Main definitions

* `SymmetricSequence.smashPow X`: the commutative monoid `n ↦ X^∧n` of smash powers.
* `SymmetricSequence.smashPowMap f`: the morphism of monoids induced by a based map `f`.
* `SymmetricSequence.sphereMonoid k`: the sphere monoid `S^(k)`, `n ↦ (S^k)^∧n`.
* `SphereModule k`: the category of `S^(k)`-modules.
* `SymmetricSequence.sphereMonoidOneIso`: the isomorphism of monoids `S^(1) ≅ S`.
* `SymmetricSpectrum.sphereModuleOneEquivalence`: symmetric spectra are the `S^(1)`-modules.

## References

* M. Hovey, *Spectra and symmetric spectra in general model categories*, J. Pure Appl. Algebra
  165 (2001), 63–127.
* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace TauCeti

open scoped DayFunctor

namespace SymmetricSequence

/-- The symmetric sequence `n ↦ X^∧n` of smash powers of a pointed simplicial set, with `Σ_n`
permuting the smash factors. Block concatenation `X^∧p ∧ X^∧q ≅ X^∧(p+q)` and `S⁰ ≅ X^∧0` make it
a commutative monoid for the Day convolution product, through the instances
`DayFunctor.monObj` and `DayFunctor.isCommMonObj`. -/
-- An abbreviation, so that the instances for lax braided functors apply to it.
noncomputable abbrev smashPow (X : PointedSSet.{u}) : SymmetricSequence.{u} :=
  .mk (PointedSSet.smashPowFunctor X)

/- The symmetric sequence of smash powers is a commutative monoid. -/
noncomputable example (X : PointedSSet.{u}) : IsCommMonObj (smashPow X) := inferInstance

/-- The multiplication `X^∧k ∧ X^∧l → X^∧(k+l)` of the monoid of smash powers, restricted along
the Day convolution unit, concatenates families of simplices. -/
lemma smashPow_mul_app_smashMk {X : PointedSSet.{u}} {k l : FiniteBijection}
    {n : SimplexCategoryᵒᵖ} (x : Fin k.len → X.right.obj n) (y : Fin l.len → X.right.obj n) :
    ((DayFunctor.η (smashPow X) (smashPow X)).app (k, l) ≫
        (MonObj.mul : smashPow X ⊗ smashPow X ⟶ smashPow X).natTrans.app (k ⊗ l)).right.app n
        (PointedSSet.smashMk (PointedSSet.smashPowMk x) (PointedSSet.smashPowMk y)) =
      PointedSSet.smashPowMk (ι := Fin (k ⊗ l).len) (Fin.append x y) := by
  rw [DayFunctor.η_app_comp_mul_natTrans_app]
  exact PointedSSet.smashPowFunctor_μ_app_smashMk x y

variable {X Y Z : PointedSSet.{u}}

/-- The morphism `X^∧n ⟶ Y^∧n` of symmetric sequences of smash powers induced by a based map
`f : X ⟶ Y`, applying `f` in every coordinate. It is a morphism of monoids, through the instance
`DayFunctor.isMonHom`. -/
noncomputable def smashPowMap (f : X ⟶ Y) : smashPow X ⟶ smashPow Y :=
  .mk (PointedSSet.smashPowFunctorMap f)

@[simp]
lemma smashPowMap_natTrans (f : X ⟶ Y) :
    (smashPowMap f).natTrans = PointedSSet.smashPowFunctorMap f := (rfl)

/-- Applying a based map in every coordinate is a monoidal natural transformation. -/
instance (f : X ⟶ Y) : NatTrans.IsMonoidal (smashPowMap f).natTrans :=
  inferInstanceAs (NatTrans.IsMonoidal (PointedSSet.smashPowFunctorMap f))

/- Applying a based map in every coordinate is a morphism of monoids of smash powers. -/
example (f : X ⟶ Y) : IsMonHom (smashPowMap f) := inferInstance

@[simp]
lemma smashPowMap_id : smashPowMap (𝟙 X) = 𝟙 _ := by
  ext1
  ext k
  simp

@[simp]
lemma smashPowMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    smashPowMap (f ≫ g) = smashPowMap f ≫ smashPowMap g := by
  ext1
  ext k
  simp

/-- The isomorphism of monoids of smash powers induced by an isomorphism `e : X ≅ Y`. -/
noncomputable def smashPowMapIso (e : X ≅ Y) : smashPow X ≅ smashPow Y where
  hom := smashPowMap e.hom
  inv := smashPowMap e.inv
  hom_inv_id := by rw [← smashPowMap_comp, e.hom_inv_id, smashPowMap_id]
  inv_hom_id := by rw [← smashPowMap_comp, e.inv_hom_id, smashPowMap_id]

@[simp]
lemma smashPowMapIso_hom (e : X ≅ Y) : (smashPowMapIso e).hom = smashPowMap e.hom := (rfl)

@[simp]
lemma smashPowMapIso_inv (e : X ≅ Y) : (smashPowMapIso e).inv = smashPowMap e.inv := (rfl)

/-- The isomorphism of smash powers induced by an isomorphism is an isomorphism of monoids. -/
instance (e : X ≅ Y) : IsMonHom (smashPowMapIso e).hom :=
  inferInstanceAs (IsMonHom (smashPowMap e.hom))

/-- The sphere monoid `S^(k)`: the symmetric sequence `n ↦ (S^k)^∧n` of smash powers of the
simplicial `k`-sphere `S^k = (S¹)^∧k`, on which `Σ_n` permutes the `n` blocks of `k` circle
coordinates. Block concatenation makes it a commutative monoid for the Day convolution product. -/
-- An abbreviation, so that the instances for lax braided functors apply to it.
noncomputable abbrev sphereMonoid (k : ℕ) : SymmetricSequence.{0} :=
  smashPow (PointedSSet.sphere k)

/- The sphere monoid `S^(k)` is a commutative monoid. -/
noncomputable example (k : ℕ) : IsCommMonObj (sphereMonoid k) := inferInstance

/-- The sphere monoid `S^(1)` is isomorphic, as a monoid, to the sphere sequence: in every level,
`((S¹)^∧1)^∧n ≅ (S¹)^∧n` identifies each block with its single circle coordinate. -/
noncomputable def sphereMonoidOneIso : sphereMonoid 1 ≅ sphere :=
  smashPowMapIso (PointedSSet.smashPowUniqueIso PointedSSet.circle (Fin 1))

/-- The isomorphism `S^(1) ≅ S` is an isomorphism of monoids. -/
instance : IsMonHom sphereMonoidOneIso.hom :=
  inferInstanceAs (IsMonHom (smashPowMapIso _).hom)

@[simp]
lemma sphereMonoidOneIso_hom :
    sphereMonoidOneIso.hom =
      smashPowMap (PointedSSet.smashPowUniqueIso PointedSSet.circle (Fin 1)).hom := (rfl)

@[simp]
lemma sphereMonoidOneIso_inv :
    sphereMonoidOneIso.inv =
      smashPowMap (PointedSSet.smashPowUniqueIso PointedSSet.circle (Fin 1)).inv := (rfl)

end SymmetricSequence

/-- The category of `S^(k)`-symmetric spectra: modules over the sphere monoid `S^(k)` for the Day
convolution product. -/
abbrev SphereModule (k : ℕ) := Mod SymmetricSequence.{0} (SymmetricSequence.sphereMonoid k)

/-- Symmetric spectra are the `S^(1)`-modules: restricting scalars along the isomorphism of
monoids `S^(1) ≅ S` is an equivalence of categories, which does not change the underlying
symmetric sequences. -/
noncomputable def SymmetricSpectrum.sphereModuleOneEquivalence :
    SymmetricSpectrum ≌ SphereModule 1 :=
  Mod.comapEquivalence SymmetricSequence.sphereMonoidOneIso

@[simp]
lemma SymmetricSpectrum.sphereModuleOneEquivalence_functor :
    sphereModuleOneEquivalence.functor = Mod.comap SymmetricSequence.sphereMonoidOneIso.hom :=
  Mod.comapEquivalence_functor _

@[simp]
lemma SymmetricSpectrum.sphereModuleOneEquivalence_inverse :
    sphereModuleOneEquivalence.inverse = Mod.comap SymmetricSequence.sphereMonoidOneIso.inv :=
  Mod.comapEquivalence_inverse _

end TauCeti
