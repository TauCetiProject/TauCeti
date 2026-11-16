/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.L0.Basic

/-!
# Order and lattice structure on `L⁰(μ; E)`

Pointwise almost-everywhere order and lattice operations on `Ω →ₘ[μ] E` (`MeasureTheory.AEEqFun`)
transfer along `TauCeti.L0.toAEEqFun` to `TauCeti.L0 E μ` for an arbitrary measure `μ`.

## Main declarations

* `TauCeti.L0.instPreorder`, `TauCeti.L0.instPartialOrder`: almost-everywhere pointwise order on
  `L0 E μ`, characterized by `TauCeti.L0.coeFn_le` and `TauCeti.L0.ofFun_le_ofFun`.
* `TauCeti.L0.instSup`, `TauCeti.L0.instInf`, `TauCeti.L0.instLattice`: pointwise supremum,
  infimum, and lattice structure on `L0 E μ` when `E` has continuous lattice operations.
-/

public noncomputable section

open MeasureTheory

namespace TauCeti.L0

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [TopologicalSpace E]

/-- Almost-everywhere pointwise preorder on `L0 E μ`, lifted from `Ω →ₘ[μ] E`. -/
instance instPreorder [Preorder E] : Preorder (L0 E μ) :=
  Preorder.lift toAEEqFun

/-- Order on `L0 E μ` is the almost-everywhere pointwise order inherited from `Ω →ₘ[μ] E`. -/
theorem le_def [Preorder E] {f g : L0 E μ} : f ≤ g ↔ f.toAEEqFun ≤ g.toAEEqFun :=
  (Iff.rfl)

/-- Order between constructed random variables is almost-everywhere pointwise order. -/
@[simp]
theorem ofFun_le_ofFun [Preorder E] {f g : Ω → E} {hf : AEStronglyMeasurable f μ}
    {hg : AEStronglyMeasurable g μ} :
    ofFun f hf ≤ ofFun g hg ↔ f ≤ᵐ[μ] g := by
  rw [le_def, toAEEqFun_ofFun, toAEEqFun_ofFun]
  exact AEEqFun.mk_le_mk hf hg

/-- Order in `L0 E μ` is equivalent to almost-everywhere pointwise order of representatives. -/
theorem coeFn_le [Preorder E] {f g : L0 E μ} : (f : Ω → E) ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [le_def, ← AEEqFun.coeFn_le]

/-- Almost-everywhere pointwise partial order on `L0 E μ`, lifted from `Ω →ₘ[μ] E`. -/
instance instPartialOrder [PartialOrder E] : PartialOrder (L0 E μ) :=
  PartialOrder.lift toAEEqFun toAEEqFun_injective

/-- Pointwise supremum on `L0 E μ`, inherited from `Ω →ₘ[μ] E`. -/
instance instSup [SemilatticeSup E] [ContinuousSup E] : Max (L0 E μ) :=
  ⟨fun f g ↦ ⟨f.toAEEqFun ⊔ g.toAEEqFun⟩⟩

/-- Forgetting the wrapper preserves suprema. -/
@[simp]
theorem toAEEqFun_sup [SemilatticeSup E] [ContinuousSup E] (f g : L0 E μ) :
    (f ⊔ g).toAEEqFun = f.toAEEqFun ⊔ g.toAEEqFun :=
  (rfl)

/-- Representative of `f ⊔ g` in `L0 E μ` agrees with `fun x ↦ f x ⊔ g x` almost everywhere. -/
theorem coeFn_sup [SemilatticeSup E] [ContinuousSup E] (f g : L0 E μ) :
    ((f ⊔ g : L0 E μ) : Ω → E) =ᵐ[μ] fun x ↦ f x ⊔ g x :=
  AEEqFun.coeFn_sup f.toAEEqFun g.toAEEqFun

/-- Constructing random variables commutes with suprema. -/
@[simp]
theorem ofFun_sup_ofFun [SemilatticeSup E] [ContinuousSup E] (f g : Ω → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ofFun f hf ⊔ ofFun g hg = ofFun (f ⊔ g) (hf.sup hg) := by
  refine ext ((coeFn_sup _ _).trans ?_)
  filter_upwards [coeFn_ofFun f hf, coeFn_ofFun g hg, coeFn_ofFun (f ⊔ g) (hf.sup hg)] with
    x hfx hgx hfgx
  rw [hfx, hgx, hfgx, Pi.sup_apply]

/-- Pointwise infimum on `L0 E μ`, inherited from `Ω →ₘ[μ] E`. -/
instance instInf [SemilatticeInf E] [ContinuousInf E] : Min (L0 E μ) :=
  ⟨fun f g ↦ ⟨f.toAEEqFun ⊓ g.toAEEqFun⟩⟩

/-- Forgetting the wrapper preserves infima. -/
@[simp]
theorem toAEEqFun_inf [SemilatticeInf E] [ContinuousInf E] (f g : L0 E μ) :
    (f ⊓ g).toAEEqFun = f.toAEEqFun ⊓ g.toAEEqFun :=
  (rfl)

/-- Representative of `f ⊓ g` in `L0 E μ` agrees with `fun x ↦ f x ⊓ g x` almost everywhere. -/
theorem coeFn_inf [SemilatticeInf E] [ContinuousInf E] (f g : L0 E μ) :
    ((f ⊓ g : L0 E μ) : Ω → E) =ᵐ[μ] fun x ↦ f x ⊓ g x :=
  AEEqFun.coeFn_inf f.toAEEqFun g.toAEEqFun

/-- Constructing random variables commutes with infima. -/
@[simp]
theorem ofFun_inf_ofFun [SemilatticeInf E] [ContinuousInf E] (f g : Ω → E)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    ofFun f hf ⊓ ofFun g hg = ofFun (f ⊓ g) (hf.inf hg) := by
  refine ext ((coeFn_inf _ _).trans ?_)
  filter_upwards [coeFn_ofFun f hf, coeFn_ofFun g hg, coeFn_ofFun (f ⊓ g) (hf.inf hg)] with
    x hfx hgx hfgx
  rw [hfx, hgx, hfgx, Pi.inf_apply]

/-- Lattice structure on `L0 E μ`, lifted from `Ω →ₘ[μ] E`. -/
instance instLattice [Lattice E] [TopologicalLattice E] : Lattice (L0 E μ) :=
  toAEEqFun_injective.lattice toAEEqFun .rfl .rfl toAEEqFun_sup toAEEqFun_inf

end TauCeti.L0
