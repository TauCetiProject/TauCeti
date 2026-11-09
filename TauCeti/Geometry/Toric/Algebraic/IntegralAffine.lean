/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.RationalFunctional
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Integral affine equivalences

An integral affine equivalence is a real affine equivalence together with an
isomorphism of the integral lattices compatible with its linear part. Its
translation is arbitrary. Both directions pull rational functionals back to
rational functionals. In normed spaces the integral lattice supplies finite
dimensionality and hence continuity without further assumptions. These
equivalences transport affine inequalities by composition with their inverses.

Adapted from `Mei/Geometry/Toric/Algebraic/IntegralAffine.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `61509bfe75ce943898bc99cfa509fb40bb78c614` (Apache 2.0).
-/

public section

namespace TauCeti.Toric

section Algebra

variable {N N' N'' V V' V'' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}

/-- An affine equivalence whose linear part identifies the integral lattices. -/
structure IntegralAffineEquiv (h : IsIntegralLattice i) (h' : IsIntegralLattice i') where
  /-- The underlying real affine equivalence, with arbitrary translation. -/
  toAffineEquiv : V ≃ᵃ[ℝ] V'
  /-- The isomorphism of the integral vectors. -/
  latticeEquiv : N ≃+ N'
  /-- Compatibility concerns the linear part, not the translated lattice points. -/
  map_lattice : ∀ n, toAffineEquiv.linear (i n) = i' (latticeEquiv n)

namespace IntegralAffineEquiv

variable {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}
  {h'' : IsIntegralLattice i''}

instance : CoeFun (IntegralAffineEquiv h h') (fun _ => V → V') :=
  ⟨fun e => e.toAffineEquiv⟩

/-- The real affine equivalence determines the integral lattice map uniquely. -/
theorem toAffineEquiv_injective :
    Function.Injective (toAffineEquiv : IntegralAffineEquiv h h' → V ≃ᵃ[ℝ] V') := by
  rintro ⟨e, l, hl⟩ ⟨f, l', hl'⟩ (rfl : e = f)
  obtain rfl : l = l' := AddEquiv.ext fun n => h'.injective <| by rw [← hl, ← hl']
  rfl

/-- Integral affine equivalences agreeing pointwise are equal. -/
@[ext]
theorem ext {e f : IntegralAffineEquiv h h'} (H : ∀ x, e x = f x) : e = f :=
  toAffineEquiv_injective (AffineEquiv.ext H)

/-- The real linear part is the canonical scalar extension of the integral lattice map. -/
theorem linear_eq_extend (e : IntegralAffineEquiv h h') :
    e.toAffineEquiv.linear.toLinearMap = h.extend i' e.latticeEquiv.toAddMonoidHom :=
  h.eq_extend e.map_lattice

/-- The identity preserves the integral lattice. -/
def refl (h : IsIntegralLattice i) : IntegralAffineEquiv h h where
  toAffineEquiv := AffineEquiv.refl ℝ V
  latticeEquiv := AddEquiv.refl N
  map_lattice _ := rfl

/-- Inverting the affine and integral equivalences preserves compatibility. -/
def symm (e : IntegralAffineEquiv h h') : IntegralAffineEquiv h' h where
  toAffineEquiv := e.toAffineEquiv.symm
  latticeEquiv := e.latticeEquiv.symm
  map_lattice n := by
    apply e.toAffineEquiv.linear.injective
    simp [e.map_lattice]

/-- Compose integral affine equivalences, applying the left one first. -/
def trans (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') :
    IntegralAffineEquiv h h'' where
  toAffineEquiv := e.toAffineEquiv.trans f.toAffineEquiv
  latticeEquiv := e.latticeEquiv.trans f.latticeEquiv
  map_lattice n := by
    dsimp only [AffineEquiv.trans]
    rw [LinearEquiv.trans_apply, e.map_lattice, f.map_lattice]
    rfl

/-- The identity has the identity affine equivalence. -/
@[simp]
theorem refl_toAffineEquiv (h : IsIntegralLattice i) :
    (refl h).toAffineEquiv = AffineEquiv.refl ℝ V := (rfl)

/-- The identity has the identity lattice equivalence. -/
@[simp]
theorem refl_latticeEquiv (h : IsIntegralLattice i) :
    (refl h).latticeEquiv = AddEquiv.refl N := (rfl)

/-- Inversion inverts the underlying affine equivalence. -/
@[simp]
theorem symm_toAffineEquiv (e : IntegralAffineEquiv h h') :
    e.symm.toAffineEquiv = e.toAffineEquiv.symm := (rfl)

/-- Inversion inverts the lattice equivalence. -/
@[simp]
theorem symm_latticeEquiv (e : IntegralAffineEquiv h h') :
    e.symm.latticeEquiv = e.latticeEquiv.symm := (rfl)

/-- Composition composes the underlying affine equivalences. -/
@[simp]
theorem trans_toAffineEquiv (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') :
    (e.trans f).toAffineEquiv = e.toAffineEquiv.trans f.toAffineEquiv := (rfl)

/-- Composition composes the lattice equivalences. -/
@[simp]
theorem trans_latticeEquiv (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') :
    (e.trans f).latticeEquiv = e.latticeEquiv.trans f.latticeEquiv := (rfl)

/-- Inverting twice recovers the integral affine equivalence. -/
@[simp]
theorem symm_symm (e : IntegralAffineEquiv h h') : e.symm.symm = e := by
  ext; rfl

/-- Applying the inverse to an image recovers the original set carrier. -/
@[simp↓]
theorem symm_image_image (e : IntegralAffineEquiv h h') (P : Set V) :
    e.symm '' (e '' P) = P :=
  e.toAffineEquiv.toEquiv.symm_image_image P

/-- Applying an equivalence after its inverse recovers the set carrier. -/
@[simp↓]
theorem image_symm_image (e : IntegralAffineEquiv h h') (P : Set V') :
    e '' (e.symm '' P) = P :=
  e.toAffineEquiv.toEquiv.image_symm_image P

/-- Composition with the identity on the target changes nothing. -/
@[simp]
theorem trans_refl (e : IntegralAffineEquiv h h') : e.trans (refl h') = e := by
  ext; rfl

/-- Composition with the identity on the source changes nothing. -/
@[simp]
theorem refl_trans (e : IntegralAffineEquiv h h') : (refl h).trans e = e := by
  ext; rfl

/-- Composition with the inverse on the right gives the source identity. -/
@[simp]
theorem self_trans_symm (e : IntegralAffineEquiv h h') : e.trans e.symm = refl h := by
  ext; simp [trans, symm, refl]

/-- Composition with the inverse on the left gives the target identity. -/
@[simp]
theorem symm_trans_self (e : IntegralAffineEquiv h h') : e.symm.trans e = refl h' := by
  ext; simp [trans, symm, refl]

/-- Composition of integral affine equivalences is associative. -/
theorem trans_assoc {N''' V''' : Type*} [AddCommGroup N'''] [AddCommGroup V''']
    [Module ℝ V'''] {i''' : N''' →+ V'''} {h''' : IsIntegralLattice i'''}
    (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'')
    (g : IntegralAffineEquiv h'' h''') :
    (e.trans f).trans g = e.trans (f.trans g) := by
  ext; rfl

/-- The linear part is rational relative to the given integral lattices. -/
theorem isRationalLinearMap (e : IntegralAffineEquiv h h') :
    IsRationalLinearMap h h' e.toAffineEquiv.linear.toLinearMap :=
  .of_integral_compatible h h' e.latticeEquiv.toAddMonoidHom
    e.toAffineEquiv.linear.toLinearMap e.map_lattice

end IntegralAffineEquiv

end Algebra

namespace IntegralAffineEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V'] [NormedSpace ℝ V] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

/-- Continuity follows from the finite dimensionality supplied by the lattice. -/
theorem continuous (e : IntegralAffineEquiv h h') : Continuous e := by
  let := h.finiteDimensional
  exact e.toAffineEquiv.continuous_of_finiteDimensional

/-- The underlying continuous affine map used to transport affine inequalities. -/
def toContinuousAffineMap (e : IntegralAffineEquiv h h') : V →ᴬ[ℝ] V' :=
  { e.toAffineEquiv.toAffineMap with cont := e.continuous }

/-- Bundling continuity does not change evaluation. -/
@[simp]
theorem toContinuousAffineMap_apply (e : IntegralAffineEquiv h h') (x : V) :
    e.toContinuousAffineMap x = e x := (rfl)

/-- Forgetting continuity gives the original affine map. -/
@[simp]
theorem toContinuousAffineMap_toAffineMap (e : IntegralAffineEquiv h h') :
    e.toContinuousAffineMap.toAffineMap = e.toAffineEquiv.toAffineMap := (rfl)

/-- Rationality with the exact bundled continuous-map type, for use in public
constructions without relying on unfolding the rational-map predicate. -/
theorem isRational_toContinuousAffineMap (e : IntegralAffineEquiv h h') :
    IsRationalLinearMap h h' e.toContinuousAffineMap.toAffineMap.linear := by
  simpa only [toContinuousAffineMap_toAffineMap, AffineEquiv.linear_toAffineMap]
    using e.isRationalLinearMap

end IntegralAffineEquiv

end TauCeti.Toric
