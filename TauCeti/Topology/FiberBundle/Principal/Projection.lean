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
If `f` is continuous, the right `G`-orbits equal the fibres of `f`
(`∀ x y, f x = f y ↔ ∃ g, op g • x = y`), and `s : B → E` is a local section over open `U ⊆ B`
along which the action is free (`∀ b ∈ U, ∀ g, op g • s b = s b → g = 1`) such that
`sectionCoord horbit hs` is continuous on `f ⁻¹' U` and `(b, g) ↦ op g • s b` is continuous on
`U ×ˢ univ`, then `s` defines an equivariant `Bundle.Trivialization G f` over `U`. Transporting a
covering family along `Bundle.Trivialization.toMapFiber` equips `TauCeti.MapFiber f` with
`PrincipalBundle G (MapFiber f)` (via `TauCeti.MapFiber.Atlas.principalBundle`) whose
`PrincipalBundle.division` equals `actionDivision`.

## Main definitions and results

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

section Free

private theorem op_smul_eq_self_imp_of_eq {x y : E} (hxy : f x = f y)
    (hfree : ∀ g : G, op g • x = x → g = 1) (g : G) (hg : op g • y = y) : g = 1 := by
  obtain ⟨h, rfl⟩ := (horbit x y).1 hxy
  have hconj : op (h * g * h⁻¹) • x = x := by
    rw [op_mul, op_mul, mul_smul, mul_smul, hg, ← mul_smul, ← op_mul, mul_inv_cancel, op_one,
      one_smul]
  exact mul_left_cancel ((mul_inv_eq_one.1 (hfree _ hconj)).trans (mul_one h).symm)

omit horbit in
@[instance_reducible]
private noncomputable def mapFiberTorsor
    (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y) {x₀ : E}
    (hfree : ∀ g : G, op g • x₀ = x₀ → g = 1) :
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
    Torsor Gᵐᵒᵖ (MapFiber f (f x₀)) :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  { nonempty := ⟨⟨x₀, rfl⟩⟩
    sdiv q p := op (actionDivision horbit (p.property.trans q.property.symm))
    sdiv_smul' q p := Subtype.ext
      ((MapFiber.coe_smul (apply_smul_eq_of_orbit_eq_fiber horbit) _ _).trans
        (op_actionDivision_smul horbit _))
    smul_sdiv' g p := by
      apply MulOpposite.unop_injective
      simp only [MulOpposite.unop_op]
      refine (op_smul_left_inj_of_op_smul_eq_self_imp
        (op_smul_eq_self_imp_of_eq horbit p.property.symm hfree)).1 ?_
      rw [op_actionDivision_smul]
      exact MapFiber.coe_smul _ g p }

private theorem mapFiberTorsor_sdiv {x₀ : E} (hfree : ∀ g : G, op g • x₀ = x₀ → g = 1)
    (q p : MapFiber f (f x₀)) :
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
    letI := mapFiberTorsor horbit hfree
    q /ₛ p = op (actionDivision horbit (p.property.trans q.property.symm)) :=
  rfl

/-- When the right `G`-action is free at `x`, `actionDivision horbit hxy` is uniquely characterized
by `op g • x = y`. -/
theorem actionDivision_eq_iff {x y : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (hxy : f x = f y) {g : G} :
    actionDivision horbit hxy = g ↔ op g • x = y :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit hfree
  by
    have hsmul : (op g • (⟨x, rfl⟩ : MapFiber f (f x))) =
        ⟨op g • x, apply_op_smul_eq_of_orbit_eq_fiber horbit g x⟩ :=
      Subtype.ext (MapFiber.coe_smul _ _ _)
    rw [← MulOpposite.op_injective.eq_iff,
      ← mapFiberTorsor_sdiv horbit hfree ⟨y, hxy.symm⟩ ⟨x, rfl⟩,
      ← eq_smul_iff_sdiv_eq (⟨y, hxy.symm⟩ : MapFiber f (f x)) (op g) ⟨x, rfl⟩,
      hsmul, Subtype.ext_iff]
    exact eq_comm

/-- Dividing a point `x` by itself under a free action at `x` yields `1`. -/
theorem actionDivision_self {x : E} (hfree : ∀ g : G, op g • x = x → g = 1) :
    actionDivision horbit (rfl : f x = f x) = 1 :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit hfree
  congrArg MulOpposite.unop (sdiv_self (⟨x, rfl⟩ : MapFiber f (f x)))

/-- Right equivariance of `actionDivision` in the second argument. -/
theorem actionDivision_op_smul_right {x y : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (g : G) (hxy : f x = f (op g • y)) :
    actionDivision horbit hxy =
      actionDivision horbit (hxy.trans (apply_op_smul_eq_of_orbit_eq_fiber horbit g y)) * g :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit hfree
  by
    have hsmul : (op g •
        (⟨y, (hxy.trans (apply_op_smul_eq_of_orbit_eq_fiber horbit g y)).symm⟩ :
          MapFiber f (f x))) = ⟨op g • y, hxy.symm⟩ :=
      Subtype.ext (MapFiber.coe_smul _ _ _)
    have h := congrArg MulOpposite.unop (smul_sdiv_assoc (op g)
      (⟨y, (hxy.trans (apply_op_smul_eq_of_orbit_eq_fiber horbit g y)).symm⟩ : MapFiber f (f x))
      ⟨x, rfl⟩)
    rw [hsmul, mapFiberTorsor_sdiv horbit hfree, mapFiberTorsor_sdiv horbit hfree] at h
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using h

/-- Equivariance of `actionDivision` in the first argument. -/
theorem actionDivision_op_smul_left {x y : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (g : G) (hxy : f (op g • x) = f y) :
    actionDivision horbit hxy = g⁻¹ *
      actionDivision horbit ((apply_op_smul_eq_of_orbit_eq_fiber horbit g x).symm.trans hxy) :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit hfree
  by
    have hsmul : (op g • (⟨x, rfl⟩ : MapFiber f (f x))) =
        ⟨op g • x, apply_op_smul_eq_of_orbit_eq_fiber horbit g x⟩ :=
      Subtype.ext (MapFiber.coe_smul _ _ _)
    have h := congrArg MulOpposite.unop (sdiv_smul_eq_sdiv_div
      (⟨y, ((apply_op_smul_eq_of_orbit_eq_fiber horbit g x).symm.trans hxy).symm⟩ :
        MapFiber f (f x))
      ⟨x, rfl⟩ (op g))
    rw [hsmul, mapFiberTorsor_sdiv horbit hfree, mapFiberTorsor_sdiv horbit hfree] at h
    simpa only [div_eq_mul_inv, MulOpposite.unop_mul, MulOpposite.unop_inv, MulOpposite.unop_op]
      using h

/-- Cocycle multiplicativity of `actionDivision` across three points in the same fibre. -/
theorem actionDivision_mul_actionDivision {x y z : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (hxy : f x = f y) (hyz : f y = f z) :
    actionDivision horbit hxy * actionDivision horbit hyz =
      actionDivision horbit (hxy.trans hyz) :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit hfree
  by
    have h := congrArg MulOpposite.unop
      (sdiv_mul_sdiv_cancel (⟨z, (hxy.trans hyz).symm⟩ : MapFiber f (f x))
        ⟨y, hxy.symm⟩ ⟨x, rfl⟩)
    rw [mapFiberTorsor_sdiv horbit hfree, mapFiberTorsor_sdiv horbit hfree,
      mapFiberTorsor_sdiv horbit hfree] at h
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using h

/-- Inverting `actionDivision` swaps its arguments. -/
theorem inv_actionDivision {x y : E} (hfree : ∀ g : G, op g • x = x → g = 1)
    (hxy : f x = f y) :
    (actionDivision horbit hxy)⁻¹ = actionDivision horbit hxy.symm :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit hfree
  congrArg MulOpposite.unop
    (inv_sdiv_eq_sdiv_rev (⟨y, hxy.symm⟩ : MapFiber f (f x)) ⟨x, rfl⟩)

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

/-- Outside `f ⁻¹' U`, `sectionCoord` defaults to `1`. -/
@[simp]
theorem sectionCoord_of_not_mem {x : E} (hx : f x ∉ U) :
    sectionCoord horbit hs x = 1 := by simp [sectionCoord, hx]

/-- Acting on `s (f x)` by `sectionCoord horbit hs x` recovers `x` for `x ∈ f ⁻¹' U`. -/
@[simp]
theorem op_sectionCoord_smul {x : E} (hx : f x ∈ U) :
    op (sectionCoord horbit hs x) • s (f x) = x := by
  rw [sectionCoord_of_mem horbit hs hx, op_actionDivision_smul]

end Coord

section FreeCoord

variable (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
  {U : Set B} {s : B → E}
  (hfree : ∀ b ∈ U, ∀ g : G, op g • s b = s b → g = 1)
  (hs : ∀ b ∈ U, f (s b) = b)

include hfree

omit hfree in
private theorem actionDivision_section_congr {x : E} {b₁ b₂ : B}
    (hb₁ : f (s b₁) = f x) (hb₂ : f (s b₂) = f x) (h : b₁ = b₂) :
    actionDivision horbit hb₁ = actionDivision horbit hb₂ := by
  subst h; rfl

/-- When the right `G`-action is free along `s` over `U`, `sectionCoord` recovers `g` on
`op g • s b` for `b ∈ U`. -/
theorem sectionCoord_op_smul_section {b : B} (hb : b ∈ U) (g : G) :
    sectionCoord horbit hs (op g • s b) = g :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit (hfree b hb)
  by
    have hfb : f (op g • s b) = b :=
      (apply_op_smul_eq_of_orbit_eq_fiber horbit g (s b)).trans (hs b hb)
    have hsmul : (op g • (⟨s b, rfl⟩ : MapFiber f (f (s b)))) =
        ⟨op g • s b, apply_op_smul_eq_of_orbit_eq_fiber horbit g (s b)⟩ :=
      Subtype.ext (MapFiber.coe_smul _ _ _)
    rw [sectionCoord_of_mem horbit hs (by rwa [hfb]),
      actionDivision_section_congr horbit (b₁ := f (op g • s b)) (b₂ := b)
        (hs _ (by rwa [hfb])) ((hs b hb).trans hfb.symm) hfb]
    have h := congrArg MulOpposite.unop (smul_sdiv (op g) (⟨s b, rfl⟩ : MapFiber f (f (s b))))
    rw [hsmul, mapFiberTorsor_sdiv horbit (hfree b hb)] at h
    simpa only [MulOpposite.unop_op] using h

/-- Right `G`-equivariance of `sectionCoord` on `f ⁻¹' U` when the action is free along `s` over
`U`. -/
theorem sectionCoord_op_smul {x : E} (hx : f x ∈ U) (g : G) :
    sectionCoord horbit hs (op g • x) = sectionCoord horbit hs x * g :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit (hfree (f x) hx)
  by
    have hfx : f (op g • x) = f x := apply_op_smul_eq_of_orbit_eq_fiber horbit g x
    have hsmul : (op g • (⟨x, (hs (f x) hx).symm⟩ : MapFiber f (f (s (f x))))) =
        ⟨op g • x, ((hs (f x) hx).trans hfx.symm).symm⟩ :=
      Subtype.ext (MapFiber.coe_smul _ _ _)
    rw [sectionCoord_of_mem horbit hs (by rwa [hfx]), sectionCoord_of_mem horbit hs hx,
      actionDivision_section_congr horbit (b₁ := f (op g • x)) (b₂ := f x)
        (hs _ (by rwa [hfx])) ((hs (f x) hx).trans hfx.symm) hfx]
    have h := congrArg MulOpposite.unop (smul_sdiv_assoc (op g)
      (⟨x, (hs (f x) hx).symm⟩ : MapFiber f (f (s (f x)))) ⟨s (f x), rfl⟩)
    rw [hsmul, mapFiberTorsor_sdiv horbit (hfree (f x) hx),
      mapFiberTorsor_sdiv horbit (hfree (f x) hx)] at h
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op] using h

/-- On `f ⁻¹' U`, `actionDivision` between two points in the same fibre equals the quotient of
their `sectionCoord` coordinates relative to a local section `s` along which the action is
free. -/
theorem actionDivision_eq_inv_sectionCoord_mul_sectionCoord {x y : E} (hx : f x ∈ U)
    (hxy : f x = f y) :
    actionDivision horbit hxy = (sectionCoord horbit hs x)⁻¹ * sectionCoord horbit hs y :=
  letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
  letI := mapFiberTorsor horbit (hfree (f x) hx)
  by
    let ps : MapFiber f (f (s (f x))) := ⟨s (f x), rfl⟩
    let px : MapFiber f (f (s (f x))) := ⟨x, (hs (f x) hx).symm⟩
    let py : MapFiber f (f (s (f x))) := ⟨y, ((hs (f x) hx).trans hxy).symm⟩
    have hdiv : actionDivision horbit hxy =
        (actionDivision horbit (hs (f x) hx))⁻¹ *
          actionDivision horbit ((hs (f x) hx).trans hxy) := by
      have h := congrArg MulOpposite.unop ((sdiv_mul_sdiv_cancel py ps px).symm.trans
        (congrArg ((py /ₛ ps) * ·) (inv_sdiv_eq_sdiv_rev px ps).symm))
      rw [mapFiberTorsor_sdiv horbit (hfree (f x) hx),
        mapFiberTorsor_sdiv horbit (hfree (f x) hx),
        mapFiberTorsor_sdiv horbit (hfree (f x) hx)] at h
      simpa only [MulOpposite.unop_mul, MulOpposite.unop_inv, MulOpposite.unop_op] using h
    rw [hdiv, sectionCoord_of_mem horbit hs hx, sectionCoord_of_mem horbit hs (hxy ▸ hx)]
    congr 1
    exact actionDivision_section_congr horbit _ _ hxy

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
is continuous on `f ⁻¹' U`, and `(b, g) ↦ op g • s b` is continuous on `U ×ˢ univ`. -/
noncomputable def actionTrivializationOfSection : Trivialization G f where
  toFun x := (f x, sectionCoord horbit hs x)
  invFun q := op q.2 • s q.1
  source := f ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' q hq := by simpa [apply_op_smul_eq_of_orbit_eq_fiber horbit, hs q.1 hq.1] using hq.1
  left_inv' _ hx := op_sectionCoord_smul horbit hs hx
  right_inv' q hq := Prod.ext
    ((apply_op_smul_eq_of_orbit_eq_fiber horbit q.2 (s q.1)).trans (hs q.1 hq.1))
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
    actionTrivializationOfSection hf horbit hU hfree hs hcoord hsmul x =
      (f x, sectionCoord horbit hs x) := (rfl)

/-- Partial-homeomorphism inverse of `actionTrivializationOfSection`. -/
@[simp]
theorem actionTrivializationOfSection_symm_apply (q : B × G) :
    (actionTrivializationOfSection hf horbit hU hfree hs hcoord hsmul).toOpenPartialHomeomorph.symm
      q = op q.2 • s q.1 := (rfl)

/-- Base set of `actionTrivializationOfSection`. -/
@[simp]
theorem baseSet_actionTrivializationOfSection :
    (actionTrivializationOfSection hf horbit hU hfree hs hcoord hsmul).baseSet = U := (rfl)

/-- Every `actionTrivializationOfSection` transports to an equivariant trivialization of
`MapFiber f`. -/
theorem isEquivariant_toMapFiber_actionTrivializationOfSection :
    letI := MapFiber.mulAction (M := Gᵐᵒᵖ) (apply_smul_eq_of_orbit_eq_fiber horbit)
    (actionTrivializationOfSection hf horbit hU hfree hs hcoord
      hsmul).toMapFiber.IsEquivariant :=
  ((actionTrivializationOfSection hf horbit hU hfree hs hcoord
    hsmul).isEquivariant_toMapFiber_iff (apply_smul_eq_of_orbit_eq_fiber horbit)).2
      fun _ hx g ↦ sectionCoord_op_smul horbit hfree hs hx g

end ActionTriv

end SectionTrivialization

end TauCeti.PrincipalBundle
