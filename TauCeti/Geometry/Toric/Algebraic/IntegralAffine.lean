/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.RationalFunctional
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Integral affine equivalences

An integral affine equivalence is a real affine equivalence together with an
isomorphism of the integral lattices compatible with its linear part. Its
translation is arbitrary. The self-equivalences of a fixed lattice form a group acting on the
ambient space, and equivalences agreeing on a nonempty open set are equal. Consequently a map
that is locally a global integral affine equivalence on a connected open set agrees there with
a unique one. Both directions pull
rational functionals back to rational functionals. In normed spaces the integral lattice supplies
finite dimensionality and hence continuity without further assumptions. These equivalences
transport affine inequalities by composition with their inverses.

Adapted from `Mei/Geometry/Toric/Algebraic/IntegralAffine.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `61509bfe75ce943898bc99cfa509fb40bb78c614` (Apache 2.0). The group and action
structure on self-equivalences, `eq_of_eqOn_open` and the `existsUnique_extension*` theorems
were adapted from the same file at commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`.
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

/-- The identity acts as the identity map. -/
theorem refl_apply (h : IsIntegralLattice i) (x : V) : refl h x = x := (rfl)

/-- Composition applies the first equivalence and then the second. -/
theorem trans_apply (e : IntegralAffineEquiv h h') (f : IntegralAffineEquiv h' h'') (x : V) :
    e.trans f x = f (e x) := (rfl)

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

/-- Integral affine self-equivalences form a group under composition, with `e * f` the
equivalence applying `f` first. -/
instance : Group (IntegralAffineEquiv h h) where
  mul e f := f.trans e
  one := refl h
  inv := symm
  mul_assoc e f g := (trans_assoc g f e).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

/-- The product `e * f` applies `f` first. -/
theorem mul_def (e f : IntegralAffineEquiv h h) : e * f = f.trans e := (rfl)

/-- The identity of the group is the identity equivalence. -/
theorem one_def : (1 : IntegralAffineEquiv h h) = refl h := (rfl)

/-- The inverse in the group is the symmetric equivalence. -/
theorem inv_def (e : IntegralAffineEquiv h h) : e⁻¹ = e.symm := (rfl)

/-- A product acts by composing the actions. -/
theorem mul_apply (e f : IntegralAffineEquiv h h) (x : V) : (e * f) x = e (f x) := by
  rw [mul_def, trans_apply]

/-- The identity of the group acts as the identity map. -/
theorem one_apply (x : V) : (1 : IntegralAffineEquiv h h) x = x := by
  rw [one_def, refl_apply]

/-- The affine equivalence underlying a product is the composite of the affine equivalences. -/
@[simp]
theorem mul_toAffineEquiv (e f : IntegralAffineEquiv h h) :
    (e * f).toAffineEquiv = f.toAffineEquiv.trans e.toAffineEquiv := (rfl)

/-- The identity of the group has the identity affine equivalence. -/
@[simp]
theorem one_toAffineEquiv :
    (1 : IntegralAffineEquiv h h).toAffineEquiv = AffineEquiv.refl ℝ V := (rfl)

/-- The affine equivalence underlying an inverse is the inverse affine equivalence. -/
@[simp]
theorem inv_toAffineEquiv (e : IntegralAffineEquiv h h) :
    (e⁻¹).toAffineEquiv = e.toAffineEquiv.symm := (rfl)

/-- The lattice equivalence of a product is the composite of the lattice equivalences. -/
@[simp]
theorem mul_latticeEquiv (e f : IntegralAffineEquiv h h) :
    (e * f).latticeEquiv = f.latticeEquiv.trans e.latticeEquiv := by
  rw [mul_def, trans_latticeEquiv]

/-- The identity of the group has the identity lattice equivalence. -/
@[simp]
theorem one_latticeEquiv : (1 : IntegralAffineEquiv h h).latticeEquiv = AddEquiv.refl N := by
  rw [one_def, refl_latticeEquiv]

/-- The inverse has the inverse lattice equivalence. -/
@[simp]
theorem inv_latticeEquiv (e : IntegralAffineEquiv h h) :
    (e⁻¹).latticeEquiv = e.latticeEquiv.symm := by
  rw [inv_def, symm_latticeEquiv]

/-- Integral affine self-equivalences act on the ambient space by evaluation. -/
instance : MulAction (IntegralAffineEquiv h h) V where
  smul e x := e x
  one_smul x := one_apply x
  mul_smul e f x := mul_apply e f x

/-- The action of an integral affine self-equivalence on the ambient space is evaluation. -/
@[simp]
theorem smul_def (e : IntegralAffineEquiv h h) (x : V) : e • x = e x := (rfl)

/-- The linear part is rational relative to the given integral lattices. -/
theorem isRationalLinearMap (e : IntegralAffineEquiv h h') :
    IsRationalLinearMap h h' e.toAffineEquiv.linear.toLinearMap :=
  .of_integral_compatible h h' e.latticeEquiv.toAddMonoidHom
    e.toAffineEquiv.linear.toLinearMap e.map_lattice

end IntegralAffineEquiv

end Algebra

namespace IntegralAffineEquiv

section Rigidity

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [AddCommGroup V'] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

/-- Agreement on a nonempty open set determines the entire integral affine equivalence. -/
theorem eq_of_eqOn_open {e f : IntegralAffineEquiv h h'} {s : Set V}
    (hs : IsOpen s) (hne : s.Nonempty) (he : Set.EqOn e f s) : e = f := by
  apply toAffineEquiv_injective
  exact AffineEquiv.ext_on (hs.affineSpan_eq_top hne) e.toAffineEquiv f.toAffineEquiv he

open Set Filter Topology

/-- On a nonempty connected open set, a map that near each point agrees with one global integral
affine equivalence agrees with a unique global integral affine equivalence on the whole set. -/
theorem existsUnique_extension {f : V → V'} {s : Set V}
    (hf : ∀ x ∈ s, ∃ e : IntegralAffineEquiv h h', f =ᶠ[𝓝 x] e) (hs : IsOpen s)
    (hc : IsConnected s) : ∃! e : IntegralAffineEquiv h h', EqOn f e s := by
  classical
  have hw : ∀ x ∈ s, ∃ e : IntegralAffineEquiv h h', ∃ u : Set V,
      IsOpen u ∧ x ∈ u ∧ EqOn f e u := fun x hx => by
    obtain ⟨e, he⟩ := hf x hx
    obtain ⟨u, hu, hu', hxu⟩ := eventually_nhds_iff.mp he
    exact ⟨e, u, hu', hxu, hu⟩
  choose E U hU hxU hEq using fun x : s => hw x.val x.property
  have hE : IsLocallyConstant E := by
    apply (IsLocallyConstant.iff_exists_open E).mpr
    intro x
    refine ⟨Subtype.val ⁻¹' U x, (hU x).preimage continuous_subtype_val, hxU x, ?_⟩
    intro y hy
    apply eq_of_eqOn_open (hs.inter ((hU x).inter (hU y)))
      ⟨y.val, y.property, hy, hxU y⟩
    intro z hz
    exact (hEq y hz.2.2).symm.trans (hEq x hz.2.1)
  let : PreconnectedSpace s := Subtype.preconnectedSpace hc.isPreconnected
  obtain ⟨x, hx⟩ := hc.nonempty
  let e := E ⟨x, hx⟩
  have he : EqOn f e s := by
    intro y hy
    have hEy := hE.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨x, hx⟩
    exact (hEq ⟨y, hy⟩ (hxU ⟨y, hy⟩)).trans
      (congrArg (fun a : IntegralAffineEquiv h h' => a y) hEy)
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact eq_of_eqOn_open hs hc.nonempty
    (fun y hy => (he' hy).symm.trans (he hy))

/-- Every connected component of an open set has its own unique global extension of a map that
is locally a global integral affine equivalence. -/
theorem existsUnique_extension_connectedComponentIn {f : V → V'} {s : Set V}
    (hf : ∀ x ∈ s, ∃ e : IntegralAffineEquiv h h', f =ᶠ[𝓝 x] e) (hs : IsOpen s) {x : V}
    (hx : x ∈ s) :
    ∃! e : IntegralAffineEquiv h h', EqOn f e (connectedComponentIn s x) :=
  existsUnique_extension
    (fun y hy => hf y (connectedComponentIn_subset s x hy))
    hs.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr hx)

end Rigidity

end IntegralAffineEquiv

namespace IntegralAffineEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V'] [NormedSpace ℝ V] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

/-- Continuity follows from the finite dimensionality supplied by the lattice. -/
theorem continuous (e : IntegralAffineEquiv h h') : Continuous e := by
  let := h.finiteDimensional
  exact e.toAffineEquiv.continuous_of_finiteDimensional

instance : ContinuousConstSMul (IntegralAffineEquiv h h) V :=
  ⟨fun e => by simpa only [smul_def] using e.continuous⟩

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

/-- The underlying continuous affine equivalence, used to transport exposed subsets. -/
def toContinuousAffineEquiv (e : IntegralAffineEquiv h h') : V ≃ᴬ[ℝ] V' :=
  { e.toAffineEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }

/-- Bundling continuity does not change evaluation. -/
@[simp]
theorem coe_toContinuousAffineEquiv (e : IntegralAffineEquiv h h') :
    ⇑e.toContinuousAffineEquiv = e := (rfl)

/-- Rationality with the exact bundled continuous-map type, for use in public
constructions without relying on unfolding the rational-map predicate. -/
theorem isRational_toContinuousAffineMap (e : IntegralAffineEquiv h h') :
    IsRationalLinearMap h h' e.toContinuousAffineMap.toAffineMap.linear := by
  simpa only [toContinuousAffineMap_toAffineMap, AffineEquiv.linear_toAffineMap]
    using e.isRationalLinearMap

end IntegralAffineEquiv

end TauCeti.Toric
