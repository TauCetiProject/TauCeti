/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Principal bundles

A principal `G`-bundle is a fibre bundle `P` with model fibre a group `G` with a topology, whose
fibres carry right actions of `G`, such that every trivialization of its atlas intertwines the
action on the fibres with right multiplication on `G`: over a point `b` of its base set,

`e (p • g) = (b, (e p).2 * g)`.

Right actions are encoded, as in Mathlib, by actions `MulAction Gᵐᵒᵖ (P b)` of the opposite group,
with `p • g` written `MulOpposite.op g • p`. Principal structure is a mixin on Mathlib's
fibre-bundle data, in the way `VectorBundle` is: the predicate
`Bundle.Trivialization.IsEquivariant` is the analogue of `Bundle.Trivialization.IsLinear`, and the
class `TauCeti.PrincipalBundle` asks for it on every trivialization of the atlas, not only on the
preferred trivialization at each point. No second topology is put on the total space.

From equivariance alone each fibre is a `G`-torsor: the action is free
(`TauCeti.PrincipalBundle.smul_eq_smul_iff`) and transitive
(`TauCeti.PrincipalBundle.isPretransitive`). The *division map*
`TauCeti.PrincipalBundle.division G p q` is the unique `g` with `p • g = q`; in any equivariant
trivialization whose base set contains the base point it reads `(e p).2⁻¹ * (e q).2`. Coordinate
changes between equivariant trivializations are left multiplications,
`e.coordChange e' b g = e.coordChange e' b 1 * g` (`Bundle.Trivialization.coordChange_eq_mul`), so
the transition functions of a principal bundle are the `G`-valued functions
`b ↦ e.coordChange e' b 1`. Continuity of the group operations is
not part of the structure: assuming `ContinuousMul G`, the right action is jointly continuous on
the total space (`Continuous.totalSpaceMk_smul`), and assuming `IsTopologicalGroup G`, the division
map is continuous on pairs of points in a common fibre (`Continuous.division`); both are stated
for continuous families over a varying base point, so that no cast between fibres is needed.
Conversely to the local sections `b ↦ e⁻¹ (b, 1)` of an equivariant trivialization `e`, a section
`σ` continuous on an open set `U` determines the equivariant trivialization
`p ↦ (p.proj, division G (σ p.proj) p)` over `U`
(`TauCeti.PrincipalBundle.trivializationOfSection`). The trivial bundle `Bundle.Trivial B G`
with `G` acting by right multiplication is principal, with division map `(p, q) ↦ p⁻¹ * q`.

The fibres are not given Mathlib's multiplicative `Torsor` structure: its acting group is an
`outParam`, and a group `G` is already a torsor for its own left action (`Group.instTorsor`), so
the fibre `G` of the trivial bundle cannot also be a torsor for the right action of `Gᵐᵒᵖ`.

## Main declarations

* `Bundle.Trivialization.IsEquivariant`: a trivialization intertwining the right action on the
  fibres with right multiplication on `G`.
* `TauCeti.PrincipalBundle`: every trivialization of the atlas is equivariant.
* `TauCeti.PrincipalBundle.division`: the division map of a principal bundle, with
  `TauCeti.PrincipalBundle.smul_division` and `TauCeti.PrincipalBundle.division_eq_iff`.
* `Bundle.Trivialization.coordChange_eq_mul`: transition maps are left multiplications.
* `Continuous.totalSpaceMk_smul` and `Continuous.division`: continuity of the action and of the
  division map.
* `TauCeti.PrincipalBundle.trivializationOfSection`: the equivariant trivialization determined by a
  continuous local section.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 4, §2–§3 (principal bundles and their translation function).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.1–§10.2 (principal fibre bundles and their transition functions).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5.
-/

public section

open Bundle Filter MulOpposite Set Topology

/-! ### Equivariant trivializations -/

namespace Bundle.Trivialization

variable {B G : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] {P : B → Type*}
  [TopologicalSpace (TotalSpace G P)] [∀ b, MulAction Gᵐᵒᵖ (P b)]

/-- A trivialization `e` of a bundle with model fibre a group `G`, whose fibres carry right actions
of `G`, is *equivariant* if over every point `b` of its base set it intertwines the right action on
the fibre with right multiplication on `G`: `e (p • g) = (b, (e p).2 * g)`. -/
protected class IsEquivariant (e : Trivialization G (π G P)) : Prop where
  snd_apply_smul : ∀ b ∈ e.baseSet, ∀ (p : P b) (g : G), (e ⟨b, op g • p⟩).2 = (e ⟨b, p⟩).2 * g

variable (e : Trivialization G (π G P)) [e.IsEquivariant] {b : B}

/-- An equivariant trivialization turns the right action on a fibre over its base set into right
multiplication on the fibre coordinate. -/
theorem snd_apply_smul (hb : b ∈ e.baseSet) (p : P b) (g : G) :
    (e ⟨b, op g • p⟩).2 = (e ⟨b, p⟩).2 * g :=
  IsEquivariant.snd_apply_smul b hb p g

/-- An equivariant trivialization sends `p • g` over a point `b` of its base set to
`(b, (e p).2 * g)`. -/
theorem apply_smul (hb : b ∈ e.baseSet) (p : P b) (g : G) :
    e ⟨b, op g • p⟩ = (b, (e ⟨b, p⟩).2 * g) :=
  Prod.ext (e.coe_coe_fst hb) (e.snd_apply_smul hb p g)

/-- The inverse of an equivariant trivialization sends `(b, g)` to `s • g`, where `s` is the point
over `b` with fibre coordinate `1`. -/
theorem symm_apply_eq_smul (hb : b ∈ e.baseSet) (g : G) :
    e.toOpenPartialHomeomorph.symm (b, g) =
      ⟨(e.toOpenPartialHomeomorph.symm (b, 1)).proj,
        op g • (e.toOpenPartialHomeomorph.symm (b, 1)).2⟩ := by
  set s := e.toOpenPartialHomeomorph.symm (b, 1)
  have hsb : s.proj = b := e.proj_symm_apply' hb
  have hs : s.proj ∈ e.baseSet := by rwa [hsb]
  have hes : (e s).2 = 1 := congrArg Prod.snd (e.apply_symm_apply' hb)
  have hy : (⟨s.proj, op g • s.2⟩ : TotalSpace G P) ∈ e.source := e.mem_source.2 hs
  refine ((e.toOpenPartialHomeomorph.eq_symm_apply hy ((e.mem_target (x := (b, g))).2 hb)).2
    ?_).symm
  rw [e.coe_coe, e.apply_smul hs, TotalSpace.eta, hes, one_mul, hsb]

/-- An equivariant trivialization exhibits the element carrying `p` to `q` in a fibre over its base
set: it is `(e p).2⁻¹ * (e q).2`. -/
private theorem op_inv_mul_smul (hb : b ∈ e.baseSet) (p q : P b) :
    op ((e ⟨b, p⟩).2⁻¹ * (e ⟨b, q⟩).2) • p = q := by
  refine TotalSpace.mk_injective b (e.toOpenPartialHomeomorph.injOn (e.mem_source.2 hb)
    (e.mem_source.2 hb) ?_)
  rw [e.coe_coe, e.apply_smul hb, mul_inv_cancel_left]
  exact e.mk_proj_snd' (x := ⟨b, q⟩) hb

/-- **Transition maps of equivariant trivializations are left multiplications.** Over a point of
both base sets, the coordinate change between two equivariant trivializations is left
multiplication by its value at `1`. -/
theorem coordChange_eq_mul (e' : Trivialization G (π G P)) [e'.IsEquivariant]
    (h : b ∈ e.baseSet) (h' : b ∈ e'.baseSet) (g : G) :
    e.coordChange e' b g = e.coordChange e' b 1 * g := by
  have hs : (e.toOpenPartialHomeomorph.symm (b, 1)).proj ∈ e'.baseSet := by
    rwa [e.proj_symm_apply' h]
  rw [coordChange, e.symm_apply_eq_smul h, e'.snd_apply_smul hs, TotalSpace.eta, coordChange]

end Bundle.Trivialization

namespace TauCeti

variable (G : Type*) {B : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  (P : B → Type*) [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)]

/-- A *principal `G`-bundle* is a fibre bundle with model fibre a group `G` with a topology, whose
fibres carry right actions of `G` (actions of `Gᵐᵒᵖ`), such that every trivialization of its
atlas is equivariant: it turns the action on the fibres into right multiplication on `G`.
Continuity of the group operations is not assumed; continuity results take `ContinuousMul G` or
`IsTopologicalGroup G` as extra hypotheses. -/
class PrincipalBundle : Prop where
  isEquivariant_trivialization' :
    ∀ (e : Trivialization G (π G P)) [MemTrivializationAtlas e], e.IsEquivariant

namespace PrincipalBundle

/-- Every trivialization of the atlas of a principal bundle is equivariant. -/
instance (priority := 100) isEquivariant_trivialization [PrincipalBundle G P]
    (e : Trivialization G (π G P)) [MemTrivializationAtlas e] : e.IsEquivariant :=
  isEquivariant_trivialization' e

variable {G P} [PrincipalBundle G P] {b : B}

/-! ### The fibres are torsors -/

/-- **The action on a fibre is free.** -/
@[simp]
theorem smul_eq_smul_iff {p : P b} {g h : G} : op g • p = op h • p ↔ g = h := by
  refine ⟨fun hgh ↦ ?_, fun hgh ↦ hgh ▸ rfl⟩
  have hb := mem_baseSet_trivializationAt G P b
  have := congrArg (fun y : P b ↦ (trivializationAt G P b ⟨b, y⟩).2) hgh
  simpa only [(trivializationAt G P b).snd_apply_smul hb, mul_right_inj] using this

/-- An element of `G` fixes a point of a fibre only if it is `1`. -/
@[simp]
theorem smul_eq_self_iff {p : P b} {g : G} : op g • p = p ↔ g = 1 := by
  simpa using smul_eq_smul_iff (G := G) (p := p) (g := g) (h := 1)

variable (G) in
/-- The division map of a principal bundle: for points `p` and `q` of the fibre over `b`, the unique
`g : G` with `p • g = q` (`TauCeti.PrincipalBundle.smul_division`,
`TauCeti.PrincipalBundle.division_eq_iff`). In any equivariant trivialization whose base set
contains `b` it reads `(e p).2⁻¹ * (e q).2`
(`TauCeti.PrincipalBundle.division_eq_of_mem_baseSet`). The group `G` is explicit, since the fibres
alone do not determine it. -/
noncomputable def division (p q : P b) : G :=
  (trivializationAt G P b ⟨b, p⟩).2⁻¹ * (trivializationAt G P b ⟨b, q⟩).2

/-- The division map of `p` and `q` carries `p` to `q`. -/
@[simp]
theorem smul_division (p q : P b) : op (division G p q) • p = q :=
  (trivializationAt G P b).op_inv_mul_smul (mem_baseSet_trivializationAt G P b) p q

/-- The division map of `p` and `q` is the unique `g` with `p • g = q`. -/
theorem division_eq_iff {p q : P b} {g : G} : division G p q = g ↔ op g • p = q := by
  rw [← smul_eq_smul_iff (p := p), smul_division]
  exact eq_comm

/-- **The action on a fibre is transitive.** -/
instance isPretransitive (b : B) : MulAction.IsPretransitive Gᵐᵒᵖ (P b) :=
  ⟨fun p q ↦ ⟨op (division G p q), smul_division p q⟩⟩

/-- The division map read in an equivariant trivialization `e` whose base set contains `b`. -/
theorem division_eq_of_mem_baseSet {e : Trivialization G (π G P)} [e.IsEquivariant]
    (hb : b ∈ e.baseSet) (p q : P b) : division G p q = (e ⟨b, p⟩).2⁻¹ * (e ⟨b, q⟩).2 :=
  division_eq_iff.2 (e.op_inv_mul_smul hb p q)

@[simp]
theorem division_self (p : P b) : division G p p = 1 :=
  division_eq_iff.2 (by simp)

@[simp]
theorem division_smul_right (p q : P b) (g : G) : division G p (op g • q) = division G p q * g :=
  division_eq_iff.2 (by rw [op_mul, mul_smul, smul_division])

@[simp]
theorem division_smul_left (p q : P b) (g : G) : division G (op g • p) q = g⁻¹ * division G p q :=
  division_eq_iff.2 (by rw [op_mul, mul_smul, op_inv, inv_smul_smul, smul_division])

@[simp]
theorem division_mul_division (p q r : P b) : division G p q * division G q r = division G p r :=
  (division_eq_iff.2 (by rw [op_mul, mul_smul, smul_division, smul_division])).symm

@[simp]
theorem inv_division (p q : P b) : (division G p q)⁻¹ = division G q p := by
  rw [inv_eq_iff_mul_eq_one, division_mul_division, division_self]

end PrincipalBundle

/-! ### The trivial principal bundle -/

/-- The trivial bundle `B × G`, with `G` acting on the fibres by right multiplication, is a
principal `G`-bundle. -/
instance PrincipalBundle.trivial (B G : Type*) [TopologicalSpace B] [Group G] [TopologicalSpace G] :
    PrincipalBundle G (Bundle.Trivial B G) where
  isEquivariant_trivialization' e _ := by
    rw [Trivial.eq_trivialization B G e]
    exact ⟨fun _ _ p g ↦ by simp only [Trivial.trivialization_apply, op_smul_eq_mul]⟩

/-- On the trivial principal bundle the division map is `(p, q) ↦ p⁻¹ * q`. -/
@[simp]
theorem PrincipalBundle.division_trivial {B G : Type*} [TopologicalSpace B] [Group G]
    [TopologicalSpace G] {b : B} (p q : Bundle.Trivial B G b) :
    PrincipalBundle.division G p q = p⁻¹ * q :=
  PrincipalBundle.division_eq_iff.2 (by rw [op_smul_eq_mul, mul_inv_cancel_left])

end TauCeti

/-! ### Continuity of the action and of the division map -/

open TauCeti TauCeti.PrincipalBundle

variable {B G : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G] {P : B → Type*}
  [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {X : Type*} [TopologicalSpace X] {f : X → B} {p q : ∀ x, P (f x)} {g : X → G} {s : Set X}
  {x₀ : X}

/-- **The right action of a principal bundle is continuous**, for a continuous family of points
`p x` of the total space over a varying base point and a continuous family `g x` of group
elements. -/
theorem ContinuousWithinAt.totalSpaceMk_smul [ContinuousMul G]
    (hp : ContinuousWithinAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) s x₀)
    (hg : ContinuousWithinAt g s x₀) :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' G (f x) (op (g x) • p x)) s x₀ := by
  set e := trivializationAt G P (f x₀)
  have hx₀ := mem_baseSet_trivializationAt G P (f x₀)
  have hf : ContinuousWithinAt f s x₀ :=
    (FiberBundle.continuous_proj G P).continuousAt.comp_continuousWithinAt hp
  have he : ContinuousWithinAt (fun x ↦ (f x, (e ⟨f x, p x⟩).2 * g x)) s x₀ :=
    hf.prodMk ((continuous_snd.continuousAt.comp_continuousWithinAt
      ((e.continuousAt (e.mem_source.2 hx₀)).comp_continuousWithinAt hp)).mul hg)
  have hsymm : ContinuousAt e.toOpenPartialHomeomorph.symm (f x₀, (e ⟨f x₀, p x₀⟩).2 * g x₀) :=
    e.continuousAt_symm (e.mem_target.2 hx₀)
  -- Over the base set of `e`, the point `p x • g x` is `e⁻¹ (f x, (e (p x)).2 * g x)`.
  have heq : ∀ {x}, f x ∈ e.baseSet →
      e.toOpenPartialHomeomorph.symm (f x, (e ⟨f x, p x⟩).2 * g x) = ⟨f x, op (g x) • p x⟩ :=
    fun hx ↦ by rw [← e.apply_smul hx, e.symm_apply_apply (e.mem_source.2 hx)]
  refine (hsymm.comp_continuousWithinAt (x := x₀) he).congr_of_eventuallyEq ?_ (heq hx₀).symm
  filter_upwards [hf (e.open_baseSet.mem_nhds hx₀)] with x hx using (heq hx).symm

/-- The right action of a principal bundle is continuous at a point: `x ↦ ⟨f x, p x • g x⟩` is
continuous at `x₀` when `x ↦ ⟨f x, p x⟩` and `g` are. -/
theorem ContinuousAt.totalSpaceMk_smul [ContinuousMul G]
    (hp : ContinuousAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) x₀) (hg : ContinuousAt g x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' G (f x) (op (g x) • p x)) x₀ :=
  (continuousWithinAt_univ _ _).1 <|
    hp.continuousWithinAt.totalSpaceMk_smul (s := univ) hg.continuousWithinAt

/-- The right action of a principal bundle is continuous on a set: `x ↦ ⟨f x, p x • g x⟩` is
continuous on `s` when `x ↦ ⟨f x, p x⟩` and `g` are. -/
theorem ContinuousOn.totalSpaceMk_smul [ContinuousMul G]
    (hp : ContinuousOn (fun x ↦ TotalSpace.mk' G (f x) (p x)) s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x ↦ TotalSpace.mk' G (f x) (op (g x) • p x)) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_smul (hg x hx)

/-- The right action of a principal bundle is continuous: `x ↦ ⟨f x, p x • g x⟩` is continuous
when `x ↦ ⟨f x, p x⟩` and `g` are. -/
theorem Continuous.totalSpaceMk_smul [ContinuousMul G]
    (hp : Continuous fun x ↦ TotalSpace.mk' G (f x) (p x)) (hg : Continuous g) :
    Continuous fun x ↦ TotalSpace.mk' G (f x) (op (g x) • p x) :=
  continuous_iff_continuousAt.2 fun _ ↦ hp.continuousAt.totalSpaceMk_smul hg.continuousAt

/-- **The division map of a principal bundle is continuous**, for two continuous families of points
`p x` and `q x` of the total space lying over a common varying base point `f x`. -/
theorem ContinuousWithinAt.division [IsTopologicalGroup G]
    (hp : ContinuousWithinAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) s x₀)
    (hq : ContinuousWithinAt (fun x ↦ TotalSpace.mk' G (f x) (q x)) s x₀) :
    ContinuousWithinAt (fun x ↦ division G (p x) (q x)) s x₀ := by
  set e := trivializationAt G P (f x₀)
  have hx₀ := mem_baseSet_trivializationAt G P (f x₀)
  have hf : ContinuousWithinAt f s x₀ :=
    (FiberBundle.continuous_proj G P).continuousAt.comp_continuousWithinAt hp
  have he : ∀ {r : ∀ x, P (f x)}, ContinuousWithinAt (fun x ↦ TotalSpace.mk' G (f x) (r x)) s x₀ →
      ContinuousWithinAt (fun x ↦ (e ⟨f x, r x⟩).2) s x₀ := fun hr ↦
    continuous_snd.continuousAt.comp_continuousWithinAt
      ((e.continuousAt (e.mem_source.2 hx₀)).comp_continuousWithinAt hr)
  refine ((he hp).inv.mul (he hq)).congr_of_eventuallyEq ?_ (division_eq_of_mem_baseSet hx₀ _ _)
  filter_upwards [hf (e.open_baseSet.mem_nhds hx₀)] with x hx
  exact division_eq_of_mem_baseSet hx _ _

/-- The division map of a principal bundle is continuous at a point: `x ↦ division G (p x) (q x)`
is continuous at `x₀` when `x ↦ ⟨f x, p x⟩` and `x ↦ ⟨f x, q x⟩` are. -/
theorem ContinuousAt.division [IsTopologicalGroup G]
    (hp : ContinuousAt (fun x ↦ TotalSpace.mk' G (f x) (p x)) x₀)
    (hq : ContinuousAt (fun x ↦ TotalSpace.mk' G (f x) (q x)) x₀) :
    ContinuousAt (fun x ↦ division G (p x) (q x)) x₀ :=
  (continuousWithinAt_univ _ _).1 <|
    hp.continuousWithinAt.division (s := univ) hq.continuousWithinAt

/-- The division map of a principal bundle is continuous on a set: `x ↦ division G (p x) (q x)`
is continuous on `s` when `x ↦ ⟨f x, p x⟩` and `x ↦ ⟨f x, q x⟩` are. -/
theorem ContinuousOn.division [IsTopologicalGroup G]
    (hp : ContinuousOn (fun x ↦ TotalSpace.mk' G (f x) (p x)) s)
    (hq : ContinuousOn (fun x ↦ TotalSpace.mk' G (f x) (q x)) s) :
    ContinuousOn (fun x ↦ division G (p x) (q x)) s :=
  fun x hx ↦ (hp x hx).division (hq x hx)

/-- The division map of a principal bundle is continuous: `x ↦ division G (p x) (q x)` is
continuous when `x ↦ ⟨f x, p x⟩` and `x ↦ ⟨f x, q x⟩` are. -/
theorem Continuous.division [IsTopologicalGroup G]
    (hp : Continuous fun x ↦ TotalSpace.mk' G (f x) (p x))
    (hq : Continuous fun x ↦ TotalSpace.mk' G (f x) (q x)) :
    Continuous fun x ↦ division G (p x) (q x) :=
  continuous_iff_continuousAt.2 fun _ ↦ hp.continuousAt.division hq.continuousAt

/-! ### Trivializations from local sections -/

namespace TauCeti.PrincipalBundle

variable [IsTopologicalGroup G] (σ : ∀ b, P b) {U : Set B} (hU : IsOpen U)
  (hσ : ContinuousOn (fun b ↦ TotalSpace.mk' G b (σ b)) U)

/-- The trivialization of a principal bundle determined by a section `σ` continuous on an open set
`U`: it sends `p` over `b ∈ U` to `(b, g)`, where `g` is the division map of `σ b` and `p`, and its
inverse sends `(b, g)` to `σ b • g`. It is equivariant
(`TauCeti.PrincipalBundle.isEquivariant_trivializationOfSection`). -/
noncomputable def trivializationOfSection : Trivialization G (π G P) where
  toFun p := (p.proj, division G (σ p.proj) p.2)
  invFun x := ⟨x.1, op x.2 • σ x.1⟩
  source := π G P ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hx := hx.1
  left_inv' p _ := by simp
  right_inv' x _ := by simp
  open_source := hU.preimage (FiberBundle.continuous_proj G P)
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := (FiberBundle.continuous_proj G P).continuousOn.prodMk <|
    ContinuousOn.division (f := π G P) (p := fun x ↦ σ x.proj) (q := fun x ↦ x.2)
      (hσ.comp (FiberBundle.continuous_proj G P).continuousOn fun _ hx ↦ hx) continuousOn_id
  continuousOn_invFun :=
    ContinuousOn.totalSpaceMk_smul (f := Prod.fst) (p := fun x ↦ σ x.1)
      (hσ.comp continuousOn_fst fun _ hx ↦ hx.1) continuousOn_snd
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem trivializationOfSection_apply (p : TotalSpace G P) :
    trivializationOfSection σ hU hσ p = (p.proj, division G (σ p.proj) p.2) :=
  (rfl)

@[simp]
theorem trivializationOfSection_symm_apply (x : B × G) :
    (trivializationOfSection σ hU hσ).toOpenPartialHomeomorph.symm x = ⟨x.1, op x.2 • σ x.1⟩ :=
  (rfl)

@[simp]
theorem baseSet_trivializationOfSection : (trivializationOfSection σ hU hσ).baseSet = U :=
  (rfl)

/-- The trivialization determined by a local section is equivariant. -/
instance isEquivariant_trivializationOfSection :
    (trivializationOfSection σ hU hσ).IsEquivariant :=
  ⟨fun _ _ _ _ ↦ by simp⟩

end TauCeti.PrincipalBundle
