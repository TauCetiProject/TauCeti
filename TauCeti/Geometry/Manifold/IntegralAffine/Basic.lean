/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Manifold.SMulGroupoid
public import TauCeti.Geometry.Toric.Algebraic.IntegralAffine
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The structure groupoid of integral affine chart changes

Integral affine maps agreeing on a nonempty open set have the same global
extension, including their integral lattice maps. Consequently a map locally
equal to integral affine equivalences on a connected open set extends uniquely
to one global integral affine equivalence. The integral affine self-equivalences
form a group acting on the ambient space, and the structure groupoid of integral
affine chart changes is the corresponding `TauCeti.smulGroupoid`.

Adapted from `yuma-mizuno-lean/Mei`, commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/Geometry/Manifold/IntegralAffine/Basic.lean` (Apache 2.0).
-/

public section

open Set Filter Topology

namespace TauCeti.Toric

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

/-- On a nonempty connected open set, a map that near each point agrees with one global integral
affine equivalence agrees with a unique global integral affine equivalence on the whole set. No
connectedness of the image is assumed. -/
theorem IntegralAffineEquiv.existsUnique_extension {f : V → W} {s : Set V}
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
    apply IntegralAffineEquiv.eq_of_eqOn_open (hs.inter ((hU x).inter (hU y)))
      ⟨y.val, y.property, hy, hxU y⟩
    intro z hz
    exact (hEq y hz.2.2).symm.trans (hEq x hz.2.1)
  let b : LocallyConstant s (IntegralAffineEquiv h h') := ⟨E, hE⟩
  let : PreconnectedSpace s := Subtype.preconnectedSpace hc.isPreconnected
  obtain ⟨x, hx⟩ := hc.nonempty
  let e := E ⟨x, hx⟩
  have he : EqOn f e s := by
    intro y hy
    have hEy := b.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨x, hx⟩
    exact (hEq ⟨y, hy⟩ (hxU ⟨y, hy⟩)).trans
      (congrArg (fun a : IntegralAffineEquiv h h' => a y) hEy)
  refine ⟨e, he, ?_⟩
  intro e' he'
  exact IntegralAffineEquiv.eq_of_eqOn_open hs hc.nonempty
    (fun y hy => (he' hy).symm.trans (he hy))

/-- Every connected component of an open set has its own unique global extension of a map that
is locally a global integral affine equivalence. -/
theorem IntegralAffineEquiv.existsUnique_extension_connectedComponentIn {f : V → W} {s : Set V}
    (hf : ∀ x ∈ s, ∃ e : IntegralAffineEquiv h h', f =ᶠ[𝓝 x] e) (hs : IsOpen s) {x : V}
    (hx : x ∈ s) :
    ∃! e : IntegralAffineEquiv h h', EqOn f e (connectedComponentIn s x) :=
  IntegralAffineEquiv.existsUnique_extension
    (fun y hy => hf y (connectedComponentIn_subset s x hy))
    hs.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr hx)

namespace IntegralAffineEquiv

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
@[simp]
theorem coe_mul (e f : IntegralAffineEquiv h h) (x : V) : (e * f) x = e (f x) := by
  rw [mul_def, trans_apply]

/-- The identity of the group acts as the identity map. -/
@[simp]
theorem coe_one (x : V) : (1 : IntegralAffineEquiv h h) x = x := by
  rw [one_def, refl_apply]

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
  one_smul x := coe_one x
  mul_smul e f x := coe_mul e f x

/-- The action of an integral affine self-equivalence on the ambient space is evaluation. -/
@[simp]
theorem smul_def (e : IntegralAffineEquiv h h) (x : V) : e • x = e x := (rfl)

instance : ContinuousConstSMul (IntegralAffineEquiv h h) V :=
  ⟨fun e => by simpa only [smul_def] using e.continuous⟩

end IntegralAffineEquiv

variable (h) in
/-- The structure groupoid of integral affine chart changes: open partial homeomorphisms of the
ambient space that are locally given by an integral affine self-equivalence. -/
abbrev integralAffineGroupoid : StructureGroupoid V :=
  smulGroupoid (IntegralAffineEquiv h h) V

/-- An open partial homeomorphism is an integral affine chart change exactly when near each point
of its source it agrees with an integral affine self-equivalence. -/
theorem mem_integralAffineGroupoid_iff {e : OpenPartialHomeomorph V V} :
    e ∈ integralAffineGroupoid h ↔
      ∀ x ∈ e.source, ∃ a : IntegralAffineEquiv h h, e =ᶠ[𝓝 x] a :=
  mem_smulGroupoid_iff

/-- A global integral affine self-equivalence, as a homeomorphism, is an integral affine chart
change. -/
theorem IntegralAffineEquiv.mem_integralAffineGroupoid (a : IntegralAffineEquiv h h) :
    (Homeomorph.smul a : V ≃ₜ V).toOpenPartialHomeomorph ∈ integralAffineGroupoid h :=
  smul_mem_smulGroupoid a

/-- A connected nonempty chart-change domain has a unique global integral affine extension. -/
theorem existsUnique_extension_of_mem_integralAffineGroupoid
    {e : OpenPartialHomeomorph V V} (he : e ∈ integralAffineGroupoid h)
    (hc : IsConnected e.source) :
    ∃! a : IntegralAffineEquiv h h, EqOn e a e.source :=
  IntegralAffineEquiv.existsUnique_extension (mem_smulGroupoid_iff.mp he)
    e.open_source hc

/-- Each connected component of the source of a chart change has a unique global integral
affine extension. -/
theorem existsUnique_extension_connectedComponentIn_of_mem_integralAffineGroupoid
    {e : OpenPartialHomeomorph V V} (he : e ∈ integralAffineGroupoid h) {x : V}
    (hx : x ∈ e.source) :
    ∃! a : IntegralAffineEquiv h h, EqOn e a (connectedComponentIn e.source x) :=
  IntegralAffineEquiv.existsUnique_extension_connectedComponentIn (mem_smulGroupoid_iff.mp he)
    e.open_source hx

end TauCeti.Toric
