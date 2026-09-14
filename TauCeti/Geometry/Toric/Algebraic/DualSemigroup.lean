/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import TauCeti.Geometry.Toric.Algebraic.Cone
public import TauCeti.Geometry.Toric.Algebraic.Lattice

/-!
# Dual semigroups of toric cones

An integral character of a lattice extends uniquely to a real-linear functional on the ambient
real vector space. The dual semigroup of a cone consists of the integral characters whose real
extensions are nonnegative on the cone. It is the additive monoid used to form the coordinate
ring of the corresponding affine toric variety.

The construction is expressed as the inverse image of Mathlib's `PointedCone.dual`, so its order
reversal and its behavior on cone hulls come directly from the convex-geometric duality API.
Maps of lattices carrying one cone into another induce contravariant maps of dual semigroups.

## Main declarations

* `TauCeti.Toric.IsIntegralLattice.realCharacter`: the real-linear extension of an integral
  character, additively in the character.
* `TauCeti.Toric.dualSemigroup`: integral characters nonnegative on a cone.
* `TauCeti.Toric.dualSemigroupMap`: the contravariant map induced by a compatible map of
  lattices and cones.

## References

The construction follows §1.2 of W. Fulton, *Introduction to Toric Varieties*, and §1.2 of
D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

open Function

variable {N N' N'' V V' V'' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'} {υ : PointedCone ℝ V''}

/-! ### Extending integral characters -/

/-- The real-linear extension of an integral character. Extension is additive in the character,
so this is bundled as an additive homomorphism into the real dual space. -/
noncomputable def IsIntegralLattice.realCharacter (hi : IsIntegralLattice i) :
    (N →+ ℤ) →+ Module.Dual ℝ V :=
  ((hi.isBaseChange.linearMapLeftRightHom (Int.castAddHom ℝ).toIntLinearMap).comp
    (addMonoidHomLequivInt ℤ).toLinearMap).toAddMonoidHom

/-- Extending an integral character and evaluating it on a lattice point recovers the integer
value of the character, viewed as a real number. -/
@[simp]
theorem IsIntegralLattice.realCharacter_apply_lattice (hi : IsIntegralLattice i)
    (m : N →+ ℤ) (n : N) : hi.realCharacter m (i n) = (m n : ℝ) :=
  by
    simpa [IsIntegralLattice.realCharacter] using
      hi.isBaseChange.linearMapLeftRightHom_comp_apply
        (Int.castAddHom ℝ).toIntLinearMap m.toIntLinearMap n

/-- Real extension of integral characters is injective. -/
theorem IsIntegralLattice.realCharacter_injective (hi : IsIntegralLattice i) :
    Function.Injective hi.realCharacter := by
  intro m m' h
  ext n
  have hc : (m n : ℝ) = (m' n : ℝ) := by
    simpa using DFunLike.congr_fun h (i n)
  exact Int.cast_injective hc

/-- Real extension commutes with a compatible map of lattices. This is the linear identity behind
contravariance of dual semigroups. -/
theorem IsIntegralLattice.realCharacter_comp (hi : IsIntegralLattice i)
    (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (m : N' →+ ℤ) :
    hi.realCharacter (m.comp f) = (hi'.realCharacter m).comp g := by
  apply hi.isBaseChange.algHom_ext
  intro n
  simp [hfg]

/-! ### The dual semigroup -/

/-- The dual semigroup of a cone consists of the integral characters whose real-linear
extensions are nonnegative on the cone. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
noncomputable def dualSemigroup (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    AddSubmonoid (N →+ ℤ) :=
  (PointedCone.dual (Module.Dual.eval ℝ V) σ).toAddSubmonoid.comap hi.realCharacter

/-- An integral character belongs to the dual semigroup exactly when its real extension is
nonnegative at every point of the cone. -/
@[simp]
theorem mem_dualSemigroup (hi : IsIntegralLattice i) (m : N →+ ℤ) :
    m ∈ dualSemigroup hi σ ↔ ∀ ⦃x⦄, x ∈ σ → 0 ≤ hi.realCharacter m x :=
  Iff.rfl

/-- Enlarging a cone shrinks its dual semigroup. -/
@[gcongr]
theorem dualSemigroup_anti (hi : IsIntegralLattice i) {σ τ : PointedCone ℝ V} (h : σ ≤ τ) :
    dualSemigroup hi τ ≤ dualSemigroup hi σ := by
  intro m hm x hx
  exact hm (h hx)

/-- Taking the dual semigroup reverses the order on pointed cones. -/
theorem dualSemigroup_antitone (hi : IsIntegralLattice i) :
    Antitone (dualSemigroup hi) := fun _ _ h ↦ dualSemigroup_anti hi h

/-- The dual semigroup of the zero cone is the full character group. -/
@[simp]
theorem dualSemigroup_bot (hi : IsIntegralLattice i) :
    dualSemigroup hi (⊥ : PointedCone ℝ V) = ⊤ := by
  ext m
  simp

/-- The dual semigroup of a join is the intersection of the two dual semigroups. -/
@[simp]
theorem dualSemigroup_sup (hi : IsIntegralLattice i) (σ τ : PointedCone ℝ V) :
    dualSemigroup hi (σ ⊔ τ) = dualSemigroup hi σ ⊓ dualSemigroup hi τ := by
  unfold dualSemigroup
  rw [PointedCone.dual_sup, PointedCone.dual_union]
  rfl

/-- On a cone generated by finitely many lattice vectors, membership in the dual semigroup is
equivalent to the corresponding finite family of integral inequalities.

This is not a `simp` lemma: `mem_dualSemigroup` already rewrites its left-hand side. -/
theorem mem_dualSemigroup_hull_image (hi : IsIntegralLattice i) (s : Finset N)
    (m : N →+ ℤ) :
    m ∈ dualSemigroup hi (PointedCone.hull ℝ (i '' (s : Set N))) ↔
      ∀ n ∈ s, 0 ≤ m n := by
  rw [dualSemigroup, AddSubmonoid.mem_comap, PointedCone.dual_hull]
  simp

/-! ### Functoriality -/

/-- A compatible map of lattices carrying a source cone into a target cone induces the
contravariant map on dual semigroups by precomposition of characters. -/
noncomputable def dualSemigroupMap (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) : dualSemigroup hi' τ →+ dualSemigroup hi σ :=
  ((AddMonoidHom.compHom' f).domRestrict (dualSemigroup hi' τ)).codRestrict
    (dualSemigroup hi σ) fun m ↦ by
      change m.1.comp f ∈ dualSemigroup hi σ
      rw [mem_dualSemigroup, hi.realCharacter_comp hi' f g hfg]
      intro x hx
      exact m.2 (hστ hx)

/-- The map on dual semigroups is precomposition by the underlying map of lattices. -/
@[simp]
theorem dualSemigroupMap_apply (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) (m : dualSemigroup hi' τ) (n : N) :
    (dualSemigroupMap hi hi' f g hfg hστ m : N →+ ℤ) n = (m : N' →+ ℤ) (f n) :=
  by simp [dualSemigroupMap]

/-- The identity map of a lattice induces the identity map of its dual semigroup. -/
@[simp]
theorem dualSemigroupMap_id (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
      (fun _ hx ↦ hx) = AddMonoidHom.id (dualSemigroup hi σ) := by
  ext m n
  rfl

/-- Contravariant dual-semigroup maps turn a composite of compatible cone maps into the
composite of the induced maps. -/
theorem dualSemigroupMap_comp (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (hi'' : IsIntegralLattice i'') (f : N →+ N') (f' : N' →+ N'')
    (g : V →ₗ[ℝ] V') (g' : V' →ₗ[ℝ] V'')
    (hfg : ∀ n, g (i n) = i' (f n)) (hf'g' : ∀ n, g' (i' n) = i'' (f' n))
    (hστ : Set.MapsTo g σ τ) (hτυ : Set.MapsTo g' τ υ) :
    dualSemigroupMap hi hi'' (f'.comp f) (g'.comp g)
        (fun n ↦ by simp [hfg, hf'g']) (hτυ.comp hστ) =
      (dualSemigroupMap hi hi' f g hfg hστ).comp
        (dualSemigroupMap hi' hi'' f' g' hf'g' hτυ) := by
  ext m n
  rfl

end TauCeti.Toric
