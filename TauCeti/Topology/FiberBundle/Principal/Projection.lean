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

Given `f : E → B` and a right `G`-action on `E` whose orbits are the fibres
(`∀ x y, f x = f y ↔ ∃ g, op g • x = y`), `f` is `G`-invariant; when the action is also free,
`f x = f y` determines a unique `actionDivision horbit hxy : G` carrying `x` to `y`.
If `f` is continuous and `s : B → E` is a local section over open `U ⊆ B` such that
`sectionCoord horbit hs` is continuous on `f ⁻¹' U` and `(b, g) ↦ op g • s b` is continuous on
`U ×ˢ univ`, then `s` defines an equivariant `Bundle.Trivialization G f` over `U`. Transporting a
covering family along `Bundle.Trivialization.toMapFiber` equips `TauCeti.MapFiber f` with
`PrincipalBundle G (MapFiber f)` (via `TauCeti.MapFiber.Atlas.principalBundle`) whose
`PrincipalBundle.division` equals `actionDivision`.

## Main definitions and results

* `Bundle.Trivialization.isEquivariant_toMapFiber_iff`: equivariance characterization for
  `t.toMapFiber`.
* `TauCeti.PrincipalBundle.actionDivision`, `actionDivision_eq_iff`,
  `division_mapFiber_eq_actionDivision`: fibrewise torsor division and cocycle identities.
* `TauCeti.PrincipalBundle.sectionCoord`, `actionTrivializationOfSection`: fibre coordinate and
  equivariant `Trivialization G f` determined by a local section `s` over open `U`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., GTM 20, Springer, 1994, Chapter 4, §2–§3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.1–§10.3.
-/

public section

open Bundle Function MulOpposite Set Topology

namespace Bundle.Trivialization

variable {G E B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] [TopologicalSpace E]
  [MulAction Gᵐᵒᵖ E] {f : E → B}

/-- `t.toMapFiber` is `G`-equivariant iff `t` intertwines the right `G`-action on
`f ⁻¹' t.baseSet` with right multiplication on the second factor `G`. -/
theorem isEquivariant_toMapFiber_iff (t : Trivialization G f)
    (hinv : ∀ (g : Gᵐᵒᵖ) (x : E), f (g • x) = f x) :
    (letI := TauCeti.MapFiber.mulAction hinv; t.toMapFiber.IsEquivariant) ↔
      ∀ x : E, f x ∈ t.baseSet → ∀ g : G, (t (op g • x)).2 = (t x).2 * g :=
  letI := TauCeti.MapFiber.mulAction hinv
  isEquivariant_iff_of_equiv t.toMapFiber t (TauCeti.MapFiber.totalSpaceHomeomorph G f).toEquiv
    t.toMapFiber_baseSet
    (fun p ↦ TauCeti.MapFiber.proj_totalSpaceHomeomorph p)
    (fun p ↦ t.toMapFiber_apply p)
    fun g p ↦ by
      simp only [Homeomorph.coe_toEquiv, TauCeti.MapFiber.totalSpaceHomeomorph_apply]
      exact TauCeti.MapFiber.coe_smul hinv (op g) p.snd

end Bundle.Trivialization

namespace TauCeti.PrincipalBundle

variable {G E B : Type*} [Group G] [MulAction Gᵐᵒᵖ E] {f : E → B}

section ActionDivision

variable (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)

include horbit

/-- If the fibres of `f : E → B` are the `G`-orbits (`f x = f y ↔ ∃ g, op g • x = y`), then `f` is
invariant under the right `G`-action. -/
theorem map_op_smul_of_orbit_iff (g : G) (x : E) : f (op g • x) = f x :=
  ((horbit x (op g • x)).2 ⟨g, rfl⟩).symm

/-- `Gᵐᵒᵖ`-form of `map_op_smul_of_orbit_iff`, suitable for `MapFiber.mulAction`. -/
theorem map_smul_of_orbit_iff (g : Gᵐᵒᵖ) (x : E) : f (g • x) = f x :=
  map_op_smul_of_orbit_iff horbit (unop g) x

/-- Given `horbit : ∀ x y, f x = f y ↔ ∃ g : G, op g • x = y` and `hxy : f x = f y`, an element
`g : G` carrying `x` to `y` (`op g • x = y`). When the action is free, this is the unique torsor
division element from `x` to `y` (`actionDivision_eq_iff`). -/
noncomputable def actionDivision {x y : E} (hxy : f x = f y) : G := ((horbit x y).1 hxy).choose

/-- Acting on `x` by `actionDivision horbit hxy` yields `y`. -/
@[simp]
theorem op_actionDivision_smul {x y : E} (hxy : f x = f y) :
    op (actionDivision horbit hxy) • x = y := ((horbit x y).1 hxy).choose_spec

section Free

variable (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)

include hfree

/-- When the right `G`-action is free, `actionDivision horbit hxy` is uniquely characterized by
`op g • x = y`. -/
theorem actionDivision_eq_iff {x y : E} (hxy : f x = f y) {g : G} :
    actionDivision horbit hxy = g ↔ op g • x = y := by
  rw [← op_smul_eq_op_smul_iff_of_op_smul_eq_self_imp (hfree x), op_actionDivision_smul]
  exact eq_comm

/-- Dividing a point `x` by itself under a free action yields `1`. -/
theorem actionDivision_self (x : E) : actionDivision horbit (rfl : f x = f x) = 1 :=
  (actionDivision_eq_iff horbit hfree rfl).2 (one_smul Gᵐᵒᵖ x)

/-- Right equivariance of `actionDivision` in the second argument. -/
theorem actionDivision_op_smul_right {x y : E} (g : G) (hxy : f x = f (op g • y)) :
    actionDivision horbit hxy =
      actionDivision horbit (hxy.trans (map_op_smul_of_orbit_iff horbit g y)) * g :=
  (actionDivision_eq_iff horbit hfree hxy).2 (by rw [op_mul, mul_smul, op_actionDivision_smul])

/-- Equivariance of `actionDivision` in the first argument. -/
theorem actionDivision_op_smul_left {x y : E} (g : G) (hxy : f (op g • x) = f y) :
    actionDivision horbit hxy =
      g⁻¹ * actionDivision horbit ((map_op_smul_of_orbit_iff horbit g x).symm.trans hxy) :=
  (actionDivision_eq_iff horbit hfree hxy).2
    (by rw [op_mul, mul_smul, op_inv, inv_smul_smul, op_actionDivision_smul])

/-- Cocycle multiplicativity of `actionDivision` across three points in the same fibre. -/
theorem actionDivision_mul_actionDivision {x y z : E} (hxy : f x = f y) (hyz : f y = f z) :
    actionDivision horbit hxy * actionDivision horbit hyz =
      actionDivision horbit (hxy.trans hyz) :=
  ((actionDivision_eq_iff horbit hfree (hxy.trans hyz)).2
    (by rw [op_mul, mul_smul, op_actionDivision_smul, op_actionDivision_smul])).symm

/-- Inverting `actionDivision` swaps its arguments. -/
theorem inv_actionDivision {x y : E} (hxy : f x = f y) :
    (actionDivision horbit hxy)⁻¹ = actionDivision horbit hxy.symm := by
  rw [inv_eq_iff_mul_eq_one, actionDivision_mul_actionDivision horbit hfree,
    actionDivision_self horbit hfree]

end Free

/-- On `MapFiber f`, the abstract `PrincipalBundle.division` coincides with
`actionDivision` on the underlying points in `E`. -/
theorem division_mapFiber_eq_actionDivision [TopologicalSpace B] [TopologicalSpace G]
    [TopologicalSpace E] [FiberBundle G (MapFiber f)] {b : B} :
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (map_smul_of_orbit_iff horbit)
    ∀ [PrincipalBundle G (MapFiber f)] (p q : MapFiber f b),
      division G p q = actionDivision horbit (p.property.trans q.property.symm) := by
  let := MapFiber.mulAction (M := Gᵐᵒᵖ) (map_smul_of_orbit_iff horbit)
  intro _ p q
  exact division_eq_iff.2 (Subtype.ext
    ((MapFiber.coe_smul (map_smul_of_orbit_iff horbit) _ _).trans
      (op_actionDivision_smul horbit _)))

end ActionDivision

section SectionTrivialization

section Coord

variable (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
  {U : Set B} {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)

/-- The `G`-valued fibre coordinate relative to a local section `s : B → E` of `f` over `U : Set B`:
for `x ∈ f ⁻¹' U`, the group element carrying `s (f x)` to `x`, extended by `1` outside `f ⁻¹' U`
without requiring `Nonempty B` or `Nonempty E`. -/
noncomputable def sectionCoord (x : E) : G := by
  classical exact if hx : f x ∈ U then actionDivision horbit (hs (f x) hx) else 1

/-- On `f ⁻¹' U`, `sectionCoord` equals `actionDivision` from `s (f x)` to `x`. -/
theorem sectionCoord_of_mem {x : E} (hx : f x ∈ U) :
    sectionCoord horbit hs x = actionDivision horbit (hs (f x) hx) := by simp [sectionCoord, hx]

/-- Acting on `s (f x)` by `sectionCoord horbit hs x` recovers `x` for `x ∈ f ⁻¹' U`. -/
@[simp]
theorem op_sectionCoord_smul {x : E} (hx : f x ∈ U) :
    op (sectionCoord horbit hs x) • s (f x) = x := by
  rw [sectionCoord_of_mem horbit hs hx, op_actionDivision_smul]

end Coord

section FreeCoord

variable (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
  (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
  {U : Set B} {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)

include hfree

/-- Under a free action, `sectionCoord` recovers `g` on `op g • s b` for `b ∈ U`. -/
theorem sectionCoord_op_smul_section {b : B} (hb : b ∈ U) (g : G) :
    sectionCoord horbit hs (op g • s b) = g := by
  have hfb : f (op g • s b) = b := (map_op_smul_of_orbit_iff horbit g (s b)).trans (hs b hb)
  rw [sectionCoord_of_mem horbit hs (by rwa [hfb]), actionDivision_eq_iff horbit hfree, hfb]

/-- Right `G`-equivariance of `sectionCoord` on `f ⁻¹' U`. -/
theorem sectionCoord_op_smul {x : E} (hx : f x ∈ U) (g : G) :
    sectionCoord horbit hs (op g • x) = sectionCoord horbit hs x * g := by
  have hfx : f (op g • x) = f x := map_op_smul_of_orbit_iff horbit g x
  rw [sectionCoord_of_mem horbit hs (by rwa [hfx]), actionDivision_eq_iff horbit hfree, hfx,
    op_mul, mul_smul, op_sectionCoord_smul horbit hs hx]

/-- On `f ⁻¹' U`, `actionDivision` between two points in the same fibre equals the quotient of
their `sectionCoord` coordinates relative to a local section `s`. -/
theorem actionDivision_eq_inv_sectionCoord_mul_sectionCoord {x y : E} (hx : f x ∈ U)
    (hxy : f x = f y) :
    actionDivision horbit hxy = (sectionCoord horbit hs x)⁻¹ * sectionCoord horbit hs y := by
  rw [actionDivision_eq_iff horbit hfree]
  nth_rw 2 [← op_sectionCoord_smul horbit hs hx]
  rw [← mul_smul, ← op_mul, mul_inv_cancel_left, hxy, op_sectionCoord_smul horbit hs (hxy ▸ hx)]

end FreeCoord

section ActionTriv

variable [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace E] (hf : Continuous f)
  (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
  (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
  {U : Set B} (hU : IsOpen U) {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)
  (hcoord : ContinuousOn (sectionCoord horbit hs) (f ⁻¹' U))
  (hsmul : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ))

/-- Construct an unbundled `Bundle.Trivialization G f` over an open set `U ⊆ B` from a local
section `s : B → E` of `f` on `U`, given continuity of `f`, of `sectionCoord horbit hs` on
`f ⁻¹' U`, and of `(b, g) ↦ op g • s b` on `U ×ˢ univ`. -/
noncomputable def actionTrivializationOfSection : Trivialization G f where
  toFun x := (f x, sectionCoord horbit hs x)
  invFun q := op q.2 • s q.1
  source := f ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' q hq := by simpa [map_op_smul_of_orbit_iff horbit, hs q.1 hq.1] using hq.1
  left_inv' _ hx := op_sectionCoord_smul horbit hs hx
  right_inv' q hq := Prod.ext
    ((map_op_smul_of_orbit_iff horbit q.2 (s q.1)).trans (hs q.1 hq.1))
    (sectionCoord_op_smul_section horbit hfree hs hq.1 q.2)
  open_source := hU.preimage hf
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := hf.continuousOn.prodMk hcoord
  continuousOn_invFun := hsmul
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- Forward map of `actionTrivializationOfSection`. -/
@[simp]
theorem actionTrivializationOfSection_apply (x : E) :
    actionTrivializationOfSection hf horbit hfree hU hs hcoord hsmul x =
      (f x, sectionCoord horbit hs x) := (rfl)

/-- Partial-homeomorphism inverse of `actionTrivializationOfSection`. -/
@[simp]
theorem actionTrivializationOfSection_symm_apply (q : B × G) :
    (actionTrivializationOfSection hf horbit hfree hU hs hcoord hsmul).toOpenPartialHomeomorph.symm
      q = op q.2 • s q.1 := (rfl)

/-- Base set of `actionTrivializationOfSection`. -/
@[simp]
theorem baseSet_actionTrivializationOfSection :
    (actionTrivializationOfSection hf horbit hfree hU hs hcoord hsmul).baseSet = U := (rfl)

/-- Every `actionTrivializationOfSection` transports to an equivariant trivialization of
`MapFiber f`. -/
theorem isEquivariant_toMapFiber_actionTrivializationOfSection :
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (map_smul_of_orbit_iff horbit)
    (actionTrivializationOfSection hf horbit hfree hU hs hcoord
      hsmul).toMapFiber.IsEquivariant :=
  ((actionTrivializationOfSection hf horbit hfree hU hs hcoord
    hsmul).isEquivariant_toMapFiber_iff (map_smul_of_orbit_iff horbit)).2
      fun _ hx g ↦ sectionCoord_op_smul horbit hfree hs hx g

end ActionTriv

end SectionTrivialization

end TauCeti.PrincipalBundle
