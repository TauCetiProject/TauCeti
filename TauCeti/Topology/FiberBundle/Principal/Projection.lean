/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.Projection

/-!
# Principal bundle structures on fibres of an unbundled projection

Given a map `f : E → B` and a right action of a group `G` on `E` whose orbits are the fibres of `f`
(`∀ x y, f x = f y ↔ ∃ g : G, op g • x = y`), `f` is automatically `G`-invariant and each fibre of
`f` is a `G`-orbit. When the action is also free (`∀ x g, op g • x = x → g = 1`), any pair of
points `x, y : E` in the same fibre determines a unique transition element
`actionDivision horbit hxy : G` carrying `x` to `y`, and any local section `s : B → E` over an open
set `U ⊆ B` whose induced coordinate map `sectionCoord horbit hs` is continuous on `f ⁻¹' U`
produces an equivariant `Bundle.Trivialization G f` over `U`.

Transporting a covering family of such equivariant trivializations along
`Bundle.Trivialization.projectionFiber` equips `TauCeti.ProjectionFiber G f` with both
`FiberBundle G (ProjectionFiber G f)` and `TauCeti.PrincipalBundle G (ProjectionFiber G f)`, whose
abstract `PrincipalBundle.division` agrees with `actionDivision`.

## Main definitions and results

* `TauCeti.ProjectionFiber.mulAction`: restricts a fibre-preserving `M`-action on `E` to each fibre
  `ProjectionFiber F f b`, intertwining `ProjectionFiber.totalSpaceEquiv F f` with the induced
  fibrewise action on `TotalSpace F (ProjectionFiber F f)`.
* `Bundle.Trivialization.isEquivariant_projectionFiber_iff`: `t.projectionFiber` is `G`-equivariant
  if and only if `(t (op g • x)).2 = (t x).2 * g` for all `x ∈ f ⁻¹' t.baseSet` and `g : G`.
* `TauCeti.ProjectionFiber.principalBundle`: packages a covering family of equivariant
  trivializations of `f : E → B` into `PrincipalBundle G (ProjectionFiber G f)`.
* `TauCeti.PrincipalBundle.actionDivision`: for `f x = f y`, a group element `g : G` with
  `op g • x = y`, unique and satisfying the torsor cocycle identities when the action is free.
* `TauCeti.PrincipalBundle.sectionCoord`, `TauCeti.PrincipalBundle.actionTrivializationOfSection`:
  the fibre coordinate and equivariant `Trivialization G f` determined by a local section `s` of `f`
  over an open set `U`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4, §2–§3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.1–§10.3.
-/

public section

open Bundle Function MulOpposite Set Topology

namespace TauCeti.ProjectionFiber

section MulAction

variable (F : Type*) {M E B : Type*} [Monoid M] [MulAction M E] {f : E → B}

/-- Restrict an `M`-action on `E` preserving the fibres of `f : E → B` to each bundled fibre
`ProjectionFiber F f b`. Install locally via `letI := ProjectionFiber.mulAction F hinv`. -/
@[instance_reducible]
def mulAction (hinv : ∀ (m : M) (x : E), f (m • x) = f x) (b : B) :
    MulAction M (ProjectionFiber F f b) where
  smul m y := ⟨m • y.val, (hinv m y.val).trans y.map_val⟩
  one_smul y := ProjectionFiber.ext (one_smul M y.val)
  mul_smul m₁ m₂ y := ProjectionFiber.ext (mul_smul m₁ m₂ y.val)

/-- Fibrewise scalar multiplication acts on the underlying point in `E`. -/
@[simp]
theorem val_smul (hinv : ∀ (m : M) (x : E), f (m • x) = f x) {b : B} (m : M)
    (y : ProjectionFiber F f b) :
    (letI := mulAction F hinv; (m • y).val) = m • y.val :=
  (rfl)

/-- `totalSpaceEquiv F f` intertwines the fibrewise `M`-action on `TotalSpace` with the action on
`E`. -/
theorem totalSpaceEquiv_smul (hinv : ∀ (m : M) (x : E), f (m • x) = f x) (m : M)
    (p : TotalSpace F (ProjectionFiber F f)) :
    (letI := mulAction F hinv; totalSpaceEquiv F f (m • p)) =
      m • totalSpaceEquiv F f p := by
  simp

/-- `(totalSpaceEquiv F f).symm` intertwines the `M`-action on `E` with the fibrewise action on
`TotalSpace`. -/
theorem totalSpaceEquiv_symm_smul (hinv : ∀ (m : M) (x : E), f (m • x) = f x) (m : M) (x : E) :
    (letI := mulAction F hinv; (totalSpaceEquiv F f).symm (m • x)) =
      (letI := mulAction F hinv; m • (totalSpaceEquiv F f).symm x) :=
  (totalSpaceEquiv F f).injective (by simp)

end MulAction

end TauCeti.ProjectionFiber

namespace Bundle.Trivialization

variable {G E B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] [TopologicalSpace E]
  [MulAction Gᵐᵒᵖ E] {f : E → B}

/-- `t.projectionFiber` is `G`-equivariant if and only if `t` intertwines the right `G`-action on
`f ⁻¹' t.baseSet` with right multiplication on the second factor `G`. -/
theorem isEquivariant_projectionFiber_iff (t : Trivialization G f)
    (hinv : ∀ (g : Gᵐᵒᵖ) (x : E), f (g • x) = f x) :
    (letI := TauCeti.ProjectionFiber.mulAction G hinv; t.projectionFiber.IsEquivariant) ↔
      ∀ x : E, f x ∈ t.baseSet → ∀ g : G, (t (op g • x)).2 = (t x).2 * g := by
  let := TauCeti.ProjectionFiber.mulAction G hinv
  constructor
  · intro heq x hx g
    simpa using heq.snd_apply_smul (f x) (by simpa using hx) ⟨x, rfl⟩ g
  · refine fun h ↦ ⟨fun b hb y g ↦ ?_⟩
    simpa using h y.val (by simpa [y.map_val] using hb) g

end Bundle.Trivialization

namespace TauCeti.ProjectionFiber

variable {G E B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] [TopologicalSpace E]
  [MulAction Gᵐᵒᵖ E] {f : E → B}

/-- Package a covering set `A` of right-equivariant local trivializations of `f : E → B` into a
`PrincipalBundle G (ProjectionFiber G f)` structure. -/
theorem principalBundle (A : Set (Trivialization G f))
    (hA : ∀ b : B, ∃ t ∈ A, b ∈ t.baseSet)
    (hinv : ∀ (g : Gᵐᵒᵖ) (x : E), f (g • x) = f x)
    (heq : ∀ t ∈ A, ∀ x : E, f x ∈ t.baseSet → ∀ g : G, (t (op g • x)).2 = (t x).2 * g) :
    letI := fiberBundle A hA
    letI := mulAction G hinv
    PrincipalBundle G (ProjectionFiber G f) := by
  have hatlas : ∀ e : Trivialization G (π G (ProjectionFiber G f)),
      (letI := fiberBundle A hA; e ∈ trivializationAtlas G (ProjectionFiber G f)) →
        e ∈ Bundle.Trivialization.projectionFiber '' A := by
    simp
  let := fiberBundle A hA
  let := mulAction G hinv
  refine ⟨fun e ↦ ?_⟩
  intro he
  rcases hatlas e he.out with ⟨t, htA, rfl⟩
  exact (t.isEquivariant_projectionFiber_iff hinv).2 (heq t htA)

end TauCeti.ProjectionFiber

namespace TauCeti.PrincipalBundle

section ActionDivision

variable {G E B : Type*} [Group G] [MulAction Gᵐᵒᵖ E] {f : E → B}

/-- If the fibres of `f : E → B` are the `G`-orbits (`f x = f y ↔ ∃ g, op g • x = y`), then `f` is
invariant under the right `G`-action. -/
theorem map_op_smul_of_orbit_iff (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (g : G) (x : E) : f (op g • x) = f x :=
  ((horbit x (op g • x)).2 ⟨g, rfl⟩).symm

/-- `Gᵐᵒᵖ`-form of `map_op_smul_of_orbit_iff`, suitable for `ProjectionFiber.mulAction`. -/
theorem map_smul_of_orbit_iff (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (g : Gᵐᵒᵖ) (x : E) : f (g • x) = f x :=
  map_op_smul_of_orbit_iff horbit (unop g) x

/-- Pointwise freeness at identity (`op g • x = x → g = 1`) implies cancellation in every orbit. -/
theorem op_smul_eq_op_smul_iff_of_free (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
    {x : E} {g h : G} : op g • x = op h • x ↔ g = h := by
  refine ⟨fun hgh ↦ ?_, fun hgh ↦ hgh ▸ rfl⟩
  have h1 : op (g * h⁻¹) • x = x := by
    rw [op_mul, mul_smul, hgh, ← mul_smul, ← op_mul, mul_inv_cancel, op_one, one_smul]
  exact mul_inv_eq_one.1 (hfree x (g * h⁻¹) h1)

/-- Given `horbit : ∀ x y, f x = f y ↔ ∃ g : G, op g • x = y` and `hxy : f x = f y`, an element
`g : G` carrying `x` to `y` (`op g • x = y`). When the action is free, this is the unique torsor
division element from `x` to `y` (`actionDivision_eq_iff`). -/
noncomputable def actionDivision (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    {x y : E} (hxy : f x = f y) : G :=
  ((horbit x y).1 hxy).choose

/-- Acting on `x` by `actionDivision horbit hxy` yields `y`. -/
@[simp]
theorem op_actionDivision_smul (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    {x y : E} (hxy : f x = f y) :
    op (actionDivision horbit hxy) • x = y :=
  ((horbit x y).1 hxy).choose_spec

/-- When the right `G`-action is free, `actionDivision horbit hxy` is uniquely characterized by
`op g • x = y`. -/
theorem actionDivision_eq_iff (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1) {x y : E} (hxy : f x = f y) {g : G} :
    actionDivision horbit hxy = g ↔ op g • x = y := by
  rw [← op_smul_eq_op_smul_iff_of_free hfree (x := x), op_actionDivision_smul]
  exact eq_comm

/-- Dividing a point `x` by itself under a free action yields `1`. -/
theorem actionDivision_self (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1) (x : E) :
    actionDivision horbit (rfl : f x = f x) = 1 :=
  (actionDivision_eq_iff horbit hfree rfl).2 (one_smul Gᵐᵒᵖ x)

/-- Right equivariance of `actionDivision` in the second argument. -/
theorem actionDivision_op_smul_right (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1) {x y : E} (g : G)
    (hxy : f x = f (op g • y)) :
    actionDivision horbit hxy =
      actionDivision horbit (hxy.trans (map_op_smul_of_orbit_iff horbit g y)) * g :=
  (actionDivision_eq_iff horbit hfree hxy).2 (by rw [op_mul, mul_smul, op_actionDivision_smul])

/-- Equivariance of `actionDivision` in the first argument. -/
theorem actionDivision_op_smul_left (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1) {x y : E} (g : G)
    (hxy : f (op g • x) = f y) :
    actionDivision horbit hxy =
      g⁻¹ * actionDivision horbit ((map_op_smul_of_orbit_iff horbit g x).symm.trans hxy) :=
  (actionDivision_eq_iff horbit hfree hxy).2
    (by rw [op_mul, mul_smul, op_inv, inv_smul_smul, op_actionDivision_smul])

/-- Cocycle multiplicativity of `actionDivision` across three points in the same fibre. -/
theorem actionDivision_mul_actionDivision (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1) {x y z : E}
    (hxy : f x = f y) (hyz : f y = f z) :
    actionDivision horbit hxy * actionDivision horbit hyz =
      actionDivision horbit (hxy.trans hyz) :=
  ((actionDivision_eq_iff horbit hfree (hxy.trans hyz)).2
    (by rw [op_mul, mul_smul, op_actionDivision_smul, op_actionDivision_smul])).symm

/-- Inverting `actionDivision` swaps its arguments. -/
theorem inv_actionDivision (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1) {x y : E} (hxy : f x = f y) :
    (actionDivision horbit hxy)⁻¹ = actionDivision horbit hxy.symm := by
  rw [inv_eq_iff_mul_eq_one, actionDivision_mul_actionDivision horbit hfree,
    actionDivision_self horbit hfree]

/-- On `ProjectionFiber G f`, the abstract `PrincipalBundle.division` coincides with
`actionDivision` on the underlying points in `E`. -/
theorem division_projectionFiber_eq_actionDivision [TopologicalSpace B] [TopologicalSpace G]
    [TopologicalSpace E] (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    [FiberBundle G (ProjectionFiber G f)] {b : B} :
    letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
    ∀ [PrincipalBundle G (ProjectionFiber G f)] (p q : ProjectionFiber G f b),
      division G p q = actionDivision horbit (p.map_val.trans q.map_val.symm) := by
  let := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
  intro _ p q
  exact division_eq_iff.2 (ProjectionFiber.ext (op_actionDivision_smul horbit _))

end ActionDivision

section SectionTrivialization

variable {G E B : Type*} [Group G] [MulAction Gᵐᵒᵖ E] {f : E → B}

/-- The `G`-valued fibre coordinate relative to a local section `s : B → E` of `f` over `U : Set B`:
for `x ∈ f ⁻¹' U`, the group element carrying `s (f x)` to `x`, extended by `1` outside `f ⁻¹' U`
without requiring `Nonempty B` or `Nonempty E`. -/
noncomputable def sectionCoord (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    {U : Set B} {s : B → E} (hs : ∀ b ∈ U, f (s b) = b) (x : E) : G := by
  classical
  exact if hx : f x ∈ U then actionDivision horbit (hs (f x) hx) else 1

/-- On `f ⁻¹' U`, `sectionCoord` equals `actionDivision` from `s (f x)` to `x`. -/
theorem sectionCoord_of_mem (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    {U : Set B} {s : B → E} (hs : ∀ b ∈ U, f (s b) = b) {x : E} (hx : f x ∈ U) :
    sectionCoord horbit hs x = actionDivision horbit (hs (f x) hx) := by
  simp [sectionCoord, hx]

/-- Acting on `s (f x)` by `sectionCoord horbit hs x` recovers `x` for `x ∈ f ⁻¹' U`. -/
@[simp]
theorem op_sectionCoord_smul (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    {U : Set B} {s : B → E} (hs : ∀ b ∈ U, f (s b) = b) {x : E} (hx : f x ∈ U) :
    op (sectionCoord horbit hs x) • s (f x) = x := by
  rw [sectionCoord_of_mem horbit hs hx, op_actionDivision_smul]

/-- Under a free action, `sectionCoord` recovers `g` on `op g • s b` for `b ∈ U`. -/
theorem sectionCoord_op_smul_section (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
    {U : Set B} {s : B → E} (hs : ∀ b ∈ U, f (s b) = b) {b : B} (hb : b ∈ U) (g : G) :
    sectionCoord horbit hs (op g • s b) = g := by
  have hfb : f (op g • s b) = b := (map_op_smul_of_orbit_iff horbit g (s b)).trans (hs b hb)
  have hx : f (op g • s b) ∈ U := by rwa [hfb]
  rw [sectionCoord_of_mem horbit hs hx, actionDivision_eq_iff horbit hfree, hfb]

/-- Right `G`-equivariance of `sectionCoord` on `f ⁻¹' U`. -/
theorem sectionCoord_op_smul (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
    {U : Set B} {s : B → E} (hs : ∀ b ∈ U, f (s b) = b) {x : E} (hx : f x ∈ U) (g : G) :
    sectionCoord horbit hs (op g • x) = sectionCoord horbit hs x * g := by
  have hfx : f (op g • x) = f x := map_op_smul_of_orbit_iff horbit g x
  have hxg : f (op g • x) ∈ U := by rwa [hfx]
  rw [sectionCoord_of_mem horbit hs hxg, actionDivision_eq_iff horbit hfree, hfx, op_mul, mul_smul,
    op_sectionCoord_smul horbit hs hx]

/-- Construct an unbundled `Bundle.Trivialization G f` over an open set `U ⊆ B` from a local
section `s : B → E` of `f` on `U`, given continuity of `f`, of `sectionCoord horbit hs` on
`f ⁻¹' U`, and of `(b, g) ↦ op g • s b` on `U ×ˢ univ`. -/
noncomputable def actionTrivializationOfSection [TopologicalSpace B] [TopologicalSpace G]
    [TopologicalSpace E] (hf : Continuous f)
    (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
    {U : Set B} (hU : IsOpen U) {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)
    (hcoord : ContinuousOn (sectionCoord horbit hs) (f ⁻¹' U))
    (hsmul : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) :
    Trivialization G f where
  toFun x := (f x, sectionCoord horbit hs x)
  invFun q := op q.2 • s q.1
  source := f ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' q hq := by
    rw [mem_preimage, map_op_smul_of_orbit_iff horbit, hs q.1 hq.1]
    exact hq.1
  left_inv' x hx := op_sectionCoord_smul horbit hs hx
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
theorem actionTrivializationOfSection_apply [TopologicalSpace B] [TopologicalSpace G]
    [TopologicalSpace E] (hf : Continuous f)
    (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
    {U : Set B} (hU : IsOpen U) {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)
    (hcoord : ContinuousOn (sectionCoord horbit hs) (f ⁻¹' U))
    (hsmul : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) (x : E) :
    actionTrivializationOfSection hf horbit hfree hU hs hcoord hsmul x =
      (f x, sectionCoord horbit hs x) :=
  (rfl)

/-- Partial-homeomorphism inverse of `actionTrivializationOfSection`. -/
@[simp]
theorem actionTrivializationOfSection_symm_apply [TopologicalSpace B] [TopologicalSpace G]
    [TopologicalSpace E] (hf : Continuous f)
    (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
    {U : Set B} (hU : IsOpen U) {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)
    (hcoord : ContinuousOn (sectionCoord horbit hs) (f ⁻¹' U))
    (hsmul : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) (q : B × G) :
    (actionTrivializationOfSection hf horbit hfree hU hs hcoord hsmul).toOpenPartialHomeomorph.symm
      q = op q.2 • s q.1 :=
  (rfl)

/-- Base set of `actionTrivializationOfSection`. -/
@[simp]
theorem baseSet_actionTrivializationOfSection [TopologicalSpace B] [TopologicalSpace G]
    [TopologicalSpace E] (hf : Continuous f)
    (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
    {U : Set B} (hU : IsOpen U) {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)
    (hcoord : ContinuousOn (sectionCoord horbit hs) (f ⁻¹' U))
    (hsmul : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) :
    (actionTrivializationOfSection hf horbit hfree hU hs hcoord hsmul).baseSet = U :=
  (rfl)

/-- Every `actionTrivializationOfSection` transports to an equivariant trivialization of
`ProjectionFiber G f`. -/
theorem isEquivariant_projectionFiber_actionTrivializationOfSection [TopologicalSpace B]
    [TopologicalSpace G] [TopologicalSpace E] (hf : Continuous f)
    (horbit : ∀ x y : E, f x = f y ↔ ∃ g : G, op g • x = y)
    (hfree : ∀ (x : E) (g : G), op g • x = x → g = 1)
    {U : Set B} (hU : IsOpen U) {s : B → E} (hs : ∀ b ∈ U, f (s b) = b)
    (hcoord : ContinuousOn (sectionCoord horbit hs) (f ⁻¹' U))
    (hsmul : ContinuousOn (fun q : B × G ↦ op q.2 • s q.1) (U ×ˢ univ)) :
    letI := ProjectionFiber.mulAction G (map_smul_of_orbit_iff horbit)
    (actionTrivializationOfSection hf horbit hfree hU hs hcoord
      hsmul).projectionFiber.IsEquivariant :=
  ((actionTrivializationOfSection hf horbit hfree hU hs hcoord
    hsmul).isEquivariant_projectionFiber_iff (map_smul_of_orbit_iff horbit)).2
      fun _ hx g ↦ sectionCoord_op_smul horbit hfree hs hx g

end SectionTrivialization

end TauCeti.PrincipalBundle
