/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.MapFiber
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic

/-!
# Principal bundle structures on fibres of an unbundled projection

Given a continuous map `f : E → B` and a right `G`-action on `E` whose orbits are the fibres of
`f` (`∀ x y, f x = f y ↔ ∃ g, op g • x = y`), `f` is `G`-invariant; when the action is also free,
`f x = f y` determines a unique `actionDivision horbit hxy : G` carrying `x` to `y`. For a local
section `s : B → E` over an open set `U ⊆ B` along which the action is free
(`∀ b ∈ U, ∀ g, op g • s b = s b → g = 1`), if `sectionCoord horbit hs` is continuous on `f ⁻¹' U`
and `(b, g) ↦ op g • s b` is continuous on `U ×ˢ univ`, then `s` defines an equivariant
`Bundle.Trivialization G f` over `U` (`Continuous.actionTrivializationOfSection`). These section
trivializations transport along `Bundle.Trivialization.toMapFiber` to equivariant trivializations
of `TauCeti.MapFiber f` (`Continuous.isEquivariant_toMapFiber_actionTrivializationOfSection`), which
feed `TauCeti.MapFiber.Atlas.principalBundle`.

## Main definitions and results

* `TauCeti.PrincipalBundle.actionDivision`, `actionDivisionOrOne`, `actionDivision_eq_iff`,
  `actionDivision_self`, `actionDivision_op_smul_left`, `actionDivision_op_smul_right`,
  `actionDivision_mul_actionDivision`, `inv_actionDivision`: fibrewise torsor division, totalized
  fibre division, and its characterization, equivariance, and cocycle identities.
* `TauCeti.PrincipalBundle.division_mapFiber_eq_actionDivision`: identifies the abstract
  `PrincipalBundle.division` on `MapFiber f` with `actionDivision`.
* `TauCeti.PrincipalBundle.sectionCoord`, `sectionCoord_eq_of_eqOn`,
  `Continuous.actionTrivializationOfSection`,
  `Continuous.isEquivariant_toMapFiber_actionTrivializationOfSection`,
  `Continuous.actionTrivializationOfSection_eq_of_eqOn`,
  `Continuous.actionTrivializationOfSection_coordChange`: fibre coordinate, equivariant
  `Trivialization G f` determined by a local section `s` over open `U`, and its `MapFiber`
  equivariance.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., GTM 20, Springer, 1994, Chapter 4, §2–§3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.1–§10.3.
-/

public section

open Bundle Function MulOpposite Set Topology

namespace TauCeti.PrincipalBundle

variable {G E B : Type*} [Group G] [MulAction Gᵐᵒᵖ E] {f : E → B}

section ActionDivision

variable (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)

include horbit

/-- If the fibres of `f : E → B` are the `G`-orbits (`f x = f y ↔ ∃ g, op g • x = y`), then `f` is
invariant under the right `G`-action. -/
theorem apply_op_smul_eq_of_orbit_eq_fiber (g : G) (x : E) : f (op g • x) = f x :=
  ((horbit x (op g • x)).2 ⟨g, rfl⟩).symm

/-- `Gᵐᵒᵖ`-form of `apply_op_smul_eq_of_orbit_eq_fiber`, suitable for `MapFiber.mulAction`. -/
theorem apply_smul_eq_of_orbit_eq_fiber (g : Gᵐᵒᵖ) (x : E) : f (g • x) = f x :=
  apply_op_smul_eq_of_orbit_eq_fiber horbit (unop g) x

/-- Given `horbit : ∀ x y, f x = f y ↔ ∃ g : G, op g • x = y` and `hxy : f x = f y`, an element
`g : G` carrying `x` to `y` (`op g • x = y`). When the action is free at `x`, this is the unique
torsor division element from `x` to `y` (`actionDivision_eq_iff`). -/
noncomputable def actionDivision {x y : E} (hxy : f x = f y) : G := ((horbit x y).1 hxy).choose

/-- Acting on `x` by `actionDivision horbit hxy` yields `y`. -/
@[simp]
theorem op_actionDivision_smul {x y : E} (hxy : f x = f y) :
    op (actionDivision horbit hxy) • x = y := ((horbit x y).1 hxy).choose_spec

/-- Totalized fibre division for `horbit : ∀ x y, f x = f y ↔ ∃ g : G, op g • x = y`: returns
`actionDivision horbit h` when `h : f x = f y`, and `1` otherwise. -/
noncomputable def actionDivisionOrOne (x y : E) : G := by
  classical exact if h : f x = f y then actionDivision horbit h else 1

/-- When `hxy : f x = f y`, `actionDivisionOrOne` evaluates to `actionDivision horbit hxy`. -/
theorem actionDivisionOrOne_of_eq {x y : E} (hxy : f x = f y) :
    actionDivisionOrOne horbit x y = actionDivision horbit hxy := by
  simp [actionDivisionOrOne, hxy]

/-- Outside a common fibre (`f x ≠ f y`), `actionDivisionOrOne` defaults to `1`. -/
theorem actionDivisionOrOne_of_ne {x y : E} (hxy : f x ≠ f y) :
    actionDivisionOrOne horbit x y = 1 := by
  simp [actionDivisionOrOne, hxy]

/-- Acting on `x` by `actionDivisionOrOne horbit x y` yields `y` when `f x = f y`. -/
@[simp]
theorem op_actionDivisionOrOne_smul {x y : E} (hxy : f x = f y) :
    op (actionDivisionOrOne horbit x y) • x = y := by
  rw [actionDivisionOrOne_of_eq horbit hxy, op_actionDivision_smul]

section Free

/-- When the right `G`-action is free at `x`, `actionDivision horbit hxy` is uniquely characterized
by `op g • x = y`. -/
theorem actionDivision_eq_iff {x y : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (hxy : f x = f y) {g : G} :
    actionDivision horbit hxy = g ↔ op g • x = y := by
  rw [← op_smul_left_inj_of_op_smul_eq_self_imp hfree, op_actionDivision_smul, eq_comm]

/-- Dividing a point `x` by itself under a free action at `x` yields `1`. -/
theorem actionDivision_self {x : E} (hfree : ∀ g : G, op g • x = x → g = 1) :
    actionDivision horbit (rfl : f x = f x) = 1 :=
  (actionDivision_eq_iff horbit hfree rfl).2 (by rw [op_one, one_smul])

/-- Right equivariance of `actionDivision` in the second argument. -/
theorem actionDivision_op_smul_right {x y : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (g : G) (hxy : f x = f (op g • y)) :
    actionDivision horbit hxy =
      actionDivision horbit (hxy.trans (apply_op_smul_eq_of_orbit_eq_fiber horbit g y)) * g :=
  (actionDivision_eq_iff horbit hfree hxy).2 (by rw [op_mul, mul_smul, op_actionDivision_smul])

/-- Equivariance of `actionDivision` in the first argument. -/
theorem actionDivision_op_smul_left {x y : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (g : G) (hxy : f (op g • x) = f y) :
    actionDivision horbit hxy = g⁻¹ *
      actionDivision horbit ((apply_op_smul_eq_of_orbit_eq_fiber horbit g x).symm.trans hxy) :=
  (actionDivision_eq_iff horbit (op_smul_eq_self_imp_of_op_smul hfree g) hxy).2 (by
    rw [op_mul, mul_smul, ← mul_smul (op g⁻¹), ← op_mul, mul_inv_cancel, op_one, one_smul,
      op_actionDivision_smul])

/-- Cocycle multiplicativity of `actionDivision` across three points in the same fibre. -/
theorem actionDivision_mul_actionDivision {x y z : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (hxy : f x = f y) (hyz : f y = f z) :
    actionDivision horbit hxy * actionDivision horbit hyz =
      actionDivision horbit (hxy.trans hyz) :=
  ((actionDivision_eq_iff horbit hfree (hxy.trans hyz)).2 (by
    rw [op_mul, mul_smul, op_actionDivision_smul, op_actionDivision_smul])).symm

/-- Inverting `actionDivision` swaps its arguments. -/
theorem inv_actionDivision {x y : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (hxy : f x = f y) :
    (actionDivision horbit hxy)⁻¹ = actionDivision horbit hxy.symm := by
  have hfree' : ∀ k : G, op k • y = y → k = 1 := by
    obtain ⟨h, rfl⟩ := (horbit x y).1 hxy
    exact op_smul_eq_self_imp_of_op_smul hfree h
  exact ((actionDivision_eq_iff horbit hfree' hxy.symm).2
    (by rw [op_inv, inv_smul_eq_iff, op_actionDivision_smul])).symm

end Free

/-- On `MapFiber f`, the abstract `PrincipalBundle.division` coincides with
`actionDivision` on the underlying points in `E`. -/
theorem division_mapFiber_eq_actionDivision [TopologicalSpace B] [TopologicalSpace G]
    [TopologicalSpace E] [FiberBundle G (MapFiber f)] {b : B} :
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
    ∀ [PrincipalBundle G (MapFiber f)] (p q : MapFiber f b),
      division G p q = actionDivision horbit (p.property.trans q.property.symm) := by
  let := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  intro _ p q
  exact division_eq_iff.2 (Subtype.ext
    ((MapFiber.coe_smul (apply_smul_eq_of_orbit_eq_fiber horbit) _ _).trans
      (op_actionDivision_smul horbit _)))

end ActionDivision

section SectionTrivialization

private theorem actionDivision_section_congr
    (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    {s₁ s₂ : B → E} {x : E} {b₁ b₂ : B}
    (hb₁ : f (s₁ b₁) = f x) (hb₂ : f (s₂ b₂) = f x) (h : s₁ b₁ = s₂ b₂) :
    actionDivision horbit hb₁ = actionDivision horbit hb₂ := by
  generalize s₁ b₁ = a at hb₁ h
  generalize s₂ b₂ = b at hb₂ h
  cases h
  rfl

section Coord

variable (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
  {U : Set B} {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)

/-- The `G`-valued fibre coordinate relative to a local section `s : B → E` of `f` over
`U : Set B`: for `x ∈ f ⁻¹' U`, a chosen element of `G` carrying `s (f x)` to `x` (unique when the
stabilizer of `s (f x)` is trivial), extended by `1` outside `f ⁻¹' U` without requiring
`Nonempty B` or `Nonempty E`. -/
noncomputable def sectionCoord (x : E) : G := by
  classical exact if hx : f x ∈ U then actionDivision horbit (hs (f x) hx) else 1

/-- On `f ⁻¹' U`, `sectionCoord` equals `actionDivision` from `s (f x)` to `x`. -/
theorem sectionCoord_of_mem {x : E} (hx : f x ∈ U) :
    sectionCoord horbit hs x = actionDivision horbit (hs (f x) hx) := by simp [sectionCoord, hx]

/-- Outside `f ⁻¹' U`, `sectionCoord` defaults to `1`. -/
@[simp]
theorem sectionCoord_of_notMem {x : E} (hx : f x ∉ U) :
    sectionCoord horbit hs x = 1 := by simp [sectionCoord, hx]

/-- Acting on `s (f x)` by `sectionCoord horbit hs x` recovers `x` for `x ∈ f ⁻¹' U`. -/
@[simp]
theorem op_sectionCoord_smul {x : E} (hx : f x ∈ U) :
    op (sectionCoord horbit hs x) • s (f x) = x := by
  rw [sectionCoord_of_mem horbit hs hx, op_actionDivision_smul]

/-- Two local sections that agree on `U` determine the same `sectionCoord`. -/
theorem sectionCoord_eq_of_eqOn {s₁ s₂ : B → E}
    (hs₁ : ∀ b ∈ U, f (s₁ b) = b) (hs₂ : ∀ b ∈ U, f (s₂ b) = b)
    (hs_eq : EqOn s₁ s₂ U) (x : E) :
    sectionCoord horbit hs₁ x = sectionCoord horbit hs₂ x := by
  by_cases hx : f x ∈ U
  · rw [sectionCoord_of_mem horbit hs₁ hx, sectionCoord_of_mem horbit hs₂ hx]
    exact actionDivision_section_congr horbit (hs₁ (f x) hx) (hs₂ (f x) hx) (hs_eq hx)
  · rw [sectionCoord_of_notMem horbit hs₁ hx, sectionCoord_of_notMem horbit hs₂ hx]

end Coord

section FreeCoord

variable (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
  {U : Set B} {s : B → E}
  (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1)
  (hs : ∀ b ∈ U, f (s b) = b)

include hfree

/-- When the right `G`-action is free along `s` over `U`, `sectionCoord` recovers `g` on
`op g • s b` for `b ∈ U`. -/
theorem sectionCoord_op_smul_section {b : B} (hb : b ∈ U) (g : G) :
    sectionCoord horbit hs (op g • s b) = g := by
  have hfb : f (op g • s b) = b :=
    (apply_op_smul_eq_of_orbit_eq_fiber horbit g (s b)).trans (hs b hb)
  rw [sectionCoord_of_mem horbit hs (by rwa [hfb]),
    actionDivision_section_congr horbit (hs _ (by rwa [hfb])) ((hs b hb).trans hfb.symm)
      (congrArg s hfb),
    actionDivision_eq_iff horbit (hfree b hb)]

/-- Right `G`-equivariance of `sectionCoord` on `f ⁻¹' U` when the action is free along `s` over
`U`. -/
theorem sectionCoord_op_smul {x : E} (hx : f x ∈ U) (g : G) :
    sectionCoord horbit hs (op g • x) = sectionCoord horbit hs x * g := by
  have hfx : f (op g • x) = f x := apply_op_smul_eq_of_orbit_eq_fiber horbit g x
  rw [sectionCoord_of_mem horbit hs (by rwa [hfx]), sectionCoord_of_mem horbit hs hx,
    actionDivision_section_congr horbit (hs _ (by rwa [hfx])) ((hs (f x) hx).trans hfx.symm)
      (congrArg s hfx)]
  exact actionDivision_op_smul_right horbit (hfree (f x) hx) g _

/-- On `f ⁻¹' U`, `actionDivision` between two points in the same fibre equals the quotient of
their `sectionCoord` coordinates relative to a local section `s` along which the action is
free. -/
theorem actionDivision_eq_inv_sectionCoord_mul_sectionCoord {x y : E} (hx : f x ∈ U)
    (hxy : f x = f y) :
    actionDivision horbit hxy = (sectionCoord horbit hs x)⁻¹ * sectionCoord horbit hs y := by
  rw [sectionCoord_of_mem horbit hs hx, sectionCoord_of_mem horbit hs (hxy ▸ hx),
    actionDivision_section_congr horbit (hs (f y) (hxy ▸ hx)) ((hs (f x) hx).trans hxy)
      (congrArg s hxy.symm),
    eq_inv_mul_iff_mul_eq]
  exact actionDivision_mul_actionDivision horbit (hfree (f x) hx) (hs (f x) hx) hxy

/-- Quotient formula for `actionDivisionOrOne` on `f ⁻¹' U` relative to a local section `s` along
which the action is free. -/
theorem actionDivisionOrOne_eq_inv_sectionCoord_mul_sectionCoord {x y : E} (hx : f x ∈ U)
    (hxy : f x = f y) :
    actionDivisionOrOne horbit x y =
      (sectionCoord horbit hs x)⁻¹ * sectionCoord horbit hs y :=
  (actionDivisionOrOne_of_eq horbit hxy).trans
    (actionDivision_eq_inv_sectionCoord_mul_sectionCoord horbit hfree hs hx hxy)

end FreeCoord

section ActionTriv

variable [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace E] (hf : Continuous f)
  (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
  {U : Set B} (hU : IsOpen U) {s : B → E}
  (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1)
  (hs : ∀ b ∈ U, f (s b) = b)
  (hcoord : ContinuousOn (sectionCoord horbit hs) (f ⁻¹' U))
  (hsmul : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ))

/-- Construct an unbundled `Bundle.Trivialization G f` over an open set `U ⊆ B` from a local
section `s : B → E` of `f` on `U`, assuming `f` is continuous, the right `G`-orbits equal the
fibres of `f` (`horbit`), the action is free along `s` over `U` (`hfree`), `sectionCoord horbit hs`
is continuous on `f ⁻¹' U`, and `(b, g) ↦ op g • s b` is continuous on `U ×ˢ univ`. Off `U`, the
inverse uses a fixed fallback independent of `s`. -/
noncomputable def _root_.Continuous.actionTrivializationOfSection : Trivialization G f where
  toFun x := (f x, sectionCoord horbit hs x)
  invFun q := by
    classical exact if q.1 ∈ U then op q.2 • s q.1 else Classical.choice ⟨s q.1⟩
  source := f ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' q hq := by
    simp [hq.1, apply_op_smul_eq_of_orbit_eq_fiber horbit, hs q.1 hq.1]
  left_inv' _ hx := by
    simp [mem_preimage.1 hx]
  right_inv' q hq := by
    simp [hq.1, (apply_op_smul_eq_of_orbit_eq_fiber horbit q.2 (s q.1)).trans (hs q.1 hq.1),
      sectionCoord_op_smul_section horbit hfree hs hq.1 q.2]
  open_source := hU.preimage hf
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := hf.continuousOn.prodMk hcoord
  continuousOn_invFun := by
    classical
    exact hsmul.congr fun q hq ↦ by simp only [hq.1, ↓reduceIte]
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- Forward map of `Continuous.actionTrivializationOfSection`. -/
@[simp]
theorem _root_.Continuous.actionTrivializationOfSection_apply (x : E) :
    hf.actionTrivializationOfSection horbit hU hfree hs hcoord hsmul x =
      (f x, sectionCoord horbit hs x) := (rfl)

private theorem actionTrivializationOfSection_toOpenPartialHomeomorph_symm_apply (q : B × G) :
    (hf.actionTrivializationOfSection horbit hU hfree hs hcoord
      hsmul).toOpenPartialHomeomorph.symm q =
      by classical exact if q.1 ∈ U then op q.2 • s q.1 else Classical.choice ⟨s q.1⟩ :=
  rfl

/-- Partial-homeomorphism inverse of `Continuous.actionTrivializationOfSection` over `U`. -/
@[simp]
theorem _root_.Continuous.actionTrivializationOfSection_symm_apply {q : B × G} (hq : q.1 ∈ U) :
    (hf.actionTrivializationOfSection horbit hU hfree hs hcoord
      hsmul).toOpenPartialHomeomorph.symm q = op q.2 • s q.1 := by
  rw [actionTrivializationOfSection_toOpenPartialHomeomorph_symm_apply]
  simp only [hq, ↓reduceIte]

/-- Base set of `Continuous.actionTrivializationOfSection`. -/
@[simp]
theorem _root_.Continuous.baseSet_actionTrivializationOfSection :
    (hf.actionTrivializationOfSection horbit hU hfree hs hcoord hsmul).baseSet = U := (rfl)

/-- Source set of `Continuous.actionTrivializationOfSection`. -/
@[simp]
theorem _root_.Continuous.actionTrivializationOfSection_source :
    (hf.actionTrivializationOfSection horbit hU hfree hs hcoord hsmul).source = f ⁻¹' U := (rfl)

/-- Target set of `Continuous.actionTrivializationOfSection`. -/
@[simp]
theorem _root_.Continuous.actionTrivializationOfSection_target :
    (hf.actionTrivializationOfSection horbit hU hfree hs hcoord hsmul).target = U ×ˢ univ := (rfl)

/-- Every `Continuous.actionTrivializationOfSection` transports to an equivariant trivialization of
`MapFiber f`. -/
theorem _root_.Continuous.isEquivariant_toMapFiber_actionTrivializationOfSection :
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
    (hf.actionTrivializationOfSection horbit hU hfree hs hcoord
      hsmul).toMapFiber.IsEquivariant :=
  ((hf.actionTrivializationOfSection horbit hU hfree hs hcoord
    hsmul).isEquivariant_toMapFiber_iff (apply_smul_eq_of_orbit_eq_fiber horbit)).2
      fun _ hx g ↦ sectionCoord_op_smul horbit hfree hs hx g

/-- Two local sections that agree on `U` produce equal trivializations via
`Continuous.actionTrivializationOfSection`. -/
theorem _root_.Continuous.actionTrivializationOfSection_eq_of_eqOn {s₁ s₂ : B → E}
    (hfree₁ : ∀ b ∈ U, ∀ g : G, op g • s₁ b = s₁ b → g = 1)
    (hs₁ : ∀ b ∈ U, f (s₁ b) = b)
    (hcoord₁ : ContinuousOn (sectionCoord horbit hs₁) (f ⁻¹' U))
    (hsmul₁ : ContinuousOn (fun q : B × G ↦ op q.2 • s₁ q.1) (U ×ˢ univ))
    (hfree₂ : ∀ b ∈ U, ∀ g : G, op g • s₂ b = s₂ b → g = 1)
    (hs₂ : ∀ b ∈ U, f (s₂ b) = b)
    (hcoord₂ : ContinuousOn (sectionCoord horbit hs₂) (f ⁻¹' U))
    (hsmul₂ : ContinuousOn (fun q : B × G ↦ op q.2 • s₂ q.1) (U ×ˢ univ))
    (hs_eq : EqOn s₁ s₂ U) :
    hf.actionTrivializationOfSection horbit hU hfree₁ hs₁ hcoord₁ hsmul₁ =
      hf.actionTrivializationOfSection horbit hU hfree₂ hs₂ hcoord₂ hsmul₂ := by
  apply Trivialization.ext'
  · apply OpenPartialHomeomorph.ext
    · intro x
      exact Prod.ext rfl (sectionCoord_eq_of_eqOn horbit hs₁ hs₂ hs_eq x)
    · intro q
      by_cases hq : q.1 ∈ U
      · rw [hf.actionTrivializationOfSection_symm_apply horbit hU hfree₁ hs₁ hcoord₁ hsmul₁ hq,
          hf.actionTrivializationOfSection_symm_apply horbit hU hfree₂ hs₂ hcoord₂ hsmul₂ hq,
          hs_eq hq]
      · rw [actionTrivializationOfSection_toOpenPartialHomeomorph_symm_apply,
          actionTrivializationOfSection_toOpenPartialHomeomorph_symm_apply]
        simp only [hq, ↓reduceIte]
    · rfl
  · rfl

/-- Coordinate change between two `Continuous.actionTrivializationOfSection` trivializations over
`U₁`. -/
theorem _root_.Continuous.actionTrivializationOfSection_coordChange
    {U₁ : Set B} (hU₁ : IsOpen U₁) {s₁ : B → E}
    (hfree₁ : ∀ b ∈ U₁, ∀ g : G, op g • s₁ b = s₁ b → g = 1)
    (hs₁ : ∀ b ∈ U₁, f (s₁ b) = b)
    (hcoord₁ : ContinuousOn (sectionCoord horbit hs₁) (f ⁻¹' U₁))
    (hsmul₁ : ContinuousOn (fun q : B × G ↦ op q.2 • s₁ q.1) (U₁ ×ˢ univ))
    {U₂ : Set B} (hU₂ : IsOpen U₂) {s₂ : B → E}
    (hfree₂ : ∀ b ∈ U₂, ∀ g : G, op g • s₂ b = s₂ b → g = 1)
    (hs₂ : ∀ b ∈ U₂, f (s₂ b) = b)
    (hcoord₂ : ContinuousOn (sectionCoord horbit hs₂) (f ⁻¹' U₂))
    (hsmul₂ : ContinuousOn (fun q : B × G ↦ op q.2 • s₂ q.1) (U₂ ×ˢ univ))
    {b : B} (hb : b ∈ U₁) (g : G) :
    (hf.actionTrivializationOfSection horbit hU₁ hfree₁ hs₁ hcoord₁ hsmul₁).coordChange
      (hf.actionTrivializationOfSection horbit hU₂ hfree₂ hs₂ hcoord₂ hsmul₂) b g =
      sectionCoord horbit hs₂ (op g • s₁ b) := by
  simp only [Trivialization.coordChange,
    Continuous.actionTrivializationOfSection_symm_apply,
    Continuous.actionTrivializationOfSection_apply, hb]

end ActionTriv

end SectionTrivialization

end TauCeti.PrincipalBundle
