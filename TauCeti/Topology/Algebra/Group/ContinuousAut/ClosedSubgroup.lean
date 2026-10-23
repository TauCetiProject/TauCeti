/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic

/-!
# Continuous outer automorphisms acting on closed subgroups up to conjugacy

A continuous automorphism `φ` of a topological group `G` is a homeomorphism, so it carries a
closed subgroup `H` to the closed subgroup `φ • H`, its image. This is an action of
`ContinuousAut G` on Mathlib's `ClosedSubgroup G`. Through the inner automorphisms
`ContinuousAut.conj`, the group `G` itself acts on its closed subgroups by conjugation; this is
recorded as an action of Mathlib's `ConjAct G`, whose orbits are the conjugacy classes of closed
subgroups, `ClosedSubgroupConjClasses G`.

A continuous automorphism carries conjugate closed subgroups to conjugate closed subgroups,
because `φ * conj g = conj (φ g) * φ`, so the action descends to `ClosedSubgroupConjClasses G`.
Inner automorphisms fix every class, so the action on classes factors through the continuous
outer automorphism group `ContinuousOut G`. This is the action in which outer actions on
profinite groups, such as an outer Galois action on a profinite fundamental group, are stated on
closed subgroups (for instance decomposition and inertia groups), which are only defined up to
conjugacy. The companion action on conjugacy classes of elements is in
`TauCeti.Topology.Algebra.Group.ContinuousAut.ConjClasses`.

All actions here are algebraic: they need a topology on `G` to speak of continuous automorphisms
and closed subgroups, but no topology on `ContinuousAut G`.

## Main definitions

* The action of `ContinuousAut G` on `ClosedSubgroup G` by images, with
  `ContinuousAut.smul_closedSubgroup_toSubgroup` computing the underlying subgroup.
* The conjugation action of `ConjAct G` on `ClosedSubgroup G`, through `ContinuousAut.conj`
  (`ConjAct.smul_closedSubgroup_eq_conj_smul`), compatible with Mathlib's pointwise conjugation
  of subgroups (`ConjAct.smul_closedSubgroup_toSubgroup`).
* `TauCeti.ClosedSubgroupConjClasses G`: closed subgroups of `G` up to conjugacy, the orbit
  quotient of that action, with the class map `TauCeti.ClosedSubgroupConjClasses.mk`.
* The actions of `ContinuousAut G` and of `ContinuousOut G` on `ClosedSubgroupConjClasses G`.

## Main results

* `TauCeti.ClosedSubgroupConjClasses.mk_eq_mk_iff`: two closed subgroups have the same class
  exactly when one is a conjugate of the other.
* `TauCeti.ContinuousAut.smul_closedSubgroupConjClass`: a continuous automorphism sends the
  class of `H` to the class of `φ • H`.
* `TauCeti.ContinuousAut.conj_smul_closedSubgroupConjClasses`: inner automorphisms fix every
  class.
* `TauCeti.ContinuousOut.mk_smul_closedSubgroupConjClass`: the class of `φ` in `ContinuousOut G`
  sends the class of `H` to the class of `φ • H`.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace ContinuousAut

/-- A continuous automorphism acts on closed subgroups by taking images; the image is closed
because a continuous automorphism is a homeomorphism. -/
instance : MulAction (ContinuousAut G) (ClosedSubgroup G) where
  smul φ H := φ.closedSubgroupOrderIso H
  one_smul H := SetLike.ext fun _ ↦ ContinuousMulEquiv.mem_closedSubgroupOrderIso _ H
  mul_smul φ ψ H := SetLike.ext fun _ ↦ ((φ * ψ).mem_closedSubgroupOrderIso H).trans <|
    (ψ.mem_closedSubgroupOrderIso H).symm.trans (φ.mem_closedSubgroupOrderIso _).symm

/-- The action of a continuous automorphism on closed subgroups is transport along it by
`ContinuousMulEquiv.closedSubgroupOrderIso`, so that API applies to it. -/
theorem smul_closedSubgroup_def (φ : ContinuousAut G) (H : ClosedSubgroup G) :
    φ • H = φ.closedSubgroupOrderIso H :=
  (rfl)

/-- The underlying subgroup of `φ • H` is the image of `H` under `φ`. -/
@[simp]
theorem smul_closedSubgroup_toSubgroup (φ : ContinuousAut G) (H : ClosedSubgroup G) :
    (φ • H).toSubgroup = H.toSubgroup.map φ.toMulEquiv.toMonoidHom :=
  φ.closedSubgroupOrderIso_apply_toSubgroup H

/-- An element lies in `φ • H` exactly when its preimage under `φ` lies in `H`. -/
@[simp]
theorem mem_smul_closedSubgroup_iff {φ : ContinuousAut G} {H : ClosedSubgroup G} {x : G} :
    x ∈ φ • H ↔ φ.symm x ∈ H :=
  φ.mem_closedSubgroupOrderIso H

end ContinuousAut

section Conjugation

variable [SeparatelyContinuousMul G]

/-- The group acts on its closed subgroups by conjugation, through the continuous inner
automorphisms `ContinuousAut.conj`. -/
instance instMulActionConjActClosedSubgroup : MulAction (ConjAct G) (ClosedSubgroup G) :=
  MulAction.compHom (ClosedSubgroup G)
    ((ContinuousAut.conj : G →* ContinuousAut G).comp ConjAct.ofConjAct.toMonoidHom)

/-- Conjugating a closed subgroup by `g` is acting on it by the inner automorphism `conj g`. This
is the normal form: `simp` reduces the conjugation action to the action of continuous
automorphisms. -/
@[simp]
theorem _root_.ConjAct.smul_closedSubgroup_eq_conj_smul (g : ConjAct G) (H : ClosedSubgroup G) :
    g • H = ContinuousAut.conj (ConjAct.ofConjAct g) • H :=
  (rfl)

/-- Conjugating a closed subgroup is Mathlib's pointwise conjugation of the underlying
subgroup. -/
theorem _root_.ConjAct.smul_closedSubgroup_toSubgroup (g : ConjAct G) (H : ClosedSubgroup G) :
    (g • H).toSubgroup = g • H.toSubgroup := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
  -- Membership in the underlying subgroup of a closed subgroup is membership in it.
  change x ∈ g • H ↔ _ ∈ H
  simp

/-- Applying a continuous automorphism after conjugating by `g` is conjugating by `φ g` after
applying the automorphism: `φ * conj g = conj (φ g) * φ`. -/
theorem ContinuousAut.smul_conj_smul_closedSubgroup (φ : ContinuousAut G) (g : G)
    (H : ClosedSubgroup G) : φ • conj g • H = conj (φ g) • φ • H := by
  rw [smul_smul, smul_smul, ← mul_conj_mul_inv, inv_mul_cancel_right]

end Conjugation

variable (G) in
/-- The closed subgroups of `G` up to conjugacy: the orbits of the conjugation action of `G` on
`ClosedSubgroup G`. -/
abbrev ClosedSubgroupConjClasses [SeparatelyContinuousMul G] : Type _ :=
  MulAction.orbitRel.Quotient (ConjAct G) (ClosedSubgroup G)

namespace ClosedSubgroupConjClasses

variable [SeparatelyContinuousMul G]

/-- The conjugacy class of a closed subgroup. -/
def mk (H : ClosedSubgroup G) : ClosedSubgroupConjClasses G :=
  Quotient.mk _ H

/-- The class map is the quotient map of the orbit relation; `simp` rewrites the latter to the
former. -/
@[simp]
theorem quotient_mk_eq_mk (H : ClosedSubgroup G) :
    Quotient.mk (MulAction.orbitRel (ConjAct G) (ClosedSubgroup G)) H = mk H :=
  (rfl)

/-- Every conjugacy class of closed subgroups is the class of a closed subgroup. -/
theorem mk_surjective :
    Function.Surjective (mk : ClosedSubgroup G → ClosedSubgroupConjClasses G) :=
  Quotient.mk_surjective

/-- Two closed subgroups have the same conjugacy class exactly when one is a conjugate of the
other. -/
theorem mk_eq_mk_iff {H K : ClosedSubgroup G} :
    mk H = mk K ↔ ∃ g : G, ContinuousAut.conj g • H = K := by
  rw [mk, mk, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_symm,
    MulAction.mem_orbit_iff, ConjAct.toConjAct.surjective.exists]
  simp

end ClosedSubgroupConjClasses

namespace ContinuousAut

variable [SeparatelyContinuousMul G]

/-- A continuous automorphism acts on closed subgroups up to conjugacy: it carries conjugate
closed subgroups to conjugate closed subgroups. -/
instance : MulAction (ContinuousAut G) (ClosedSubgroupConjClasses G) where
  smul φ := Quotient.map (φ • ·) fun H K hHK ↦ by
    obtain ⟨g, rfl⟩ := hHK
    exact ⟨ConjAct.toConjAct (φ (ConjAct.ofConjAct g)), by
      simp only [ConjAct.smul_closedSubgroup_eq_conj_smul, ConjAct.ofConjAct_toConjAct,
        smul_conj_smul_closedSubgroup]⟩
  one_smul c := Quotient.inductionOn c fun H ↦ congrArg (Quotient.mk _) (one_smul _ H)
  mul_smul φ ψ c := Quotient.inductionOn c fun H ↦ congrArg (Quotient.mk _) (mul_smul φ ψ H)

/-- A continuous automorphism sends the class of `H` to the class of `φ • H`. -/
@[simp]
theorem smul_closedSubgroupConjClass (φ : ContinuousAut G) (H : ClosedSubgroup G) :
    φ • ClosedSubgroupConjClasses.mk H = ClosedSubgroupConjClasses.mk (φ • H) :=
  (rfl)

/-- Inner automorphisms fix every conjugacy class of closed subgroups. -/
@[simp]
theorem conj_smul_closedSubgroupConjClasses (g : G) (c : ClosedSubgroupConjClasses G) :
    conj g • c = c := by
  obtain ⟨H, rfl⟩ := ClosedSubgroupConjClasses.mk_surjective c
  rw [smul_closedSubgroupConjClass, ClosedSubgroupConjClasses.mk_eq_mk_iff]
  exact ⟨g⁻¹, by rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩

end ContinuousAut

namespace ContinuousOut

variable [SeparatelyContinuousMul G]

/-- The action of continuous automorphisms on closed subgroups up to conjugacy factors through
continuous outer automorphisms. -/
instance : MulAction (ContinuousOut G) (ClosedSubgroupConjClasses G) :=
  MulAction.compHom (ClosedSubgroupConjClasses G) <|
    QuotientGroup.lift (ContinuousAut.conj : G →* ContinuousAut G).range
      (MulAction.toPermHom (ContinuousAut G) (ClosedSubgroupConjClasses G)) (by
        rintro φ ⟨g, rfl⟩
        exact MonoidHom.mem_ker.mpr <| Equiv.ext fun c ↦ by
          simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply,
            Equiv.Perm.one_apply] using ContinuousAut.conj_smul_closedSubgroupConjClasses g c)

/-- The outer action on closed subgroups up to conjugacy is computed using any representative
continuous automorphism. -/
@[simp]
theorem mk_smul_closedSubgroupConjClasses (φ : ContinuousAut G)
    (c : ClosedSubgroupConjClasses G) : (φ : ContinuousOut G) • c = φ • c := by
  -- The quotient coercion exposes the `QuotientGroup.lift` computation.
  rw [MulAction.compHom_smul_def, QuotientGroup.lift_mk, Equiv.Perm.smul_def,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]

/-- The class of `φ` in `ContinuousOut G` sends the class of `H` to the class of `φ • H`. -/
theorem mk_smul_closedSubgroupConjClass (φ : ContinuousAut G) (H : ClosedSubgroup G) :
    (φ : ContinuousOut G) • ClosedSubgroupConjClasses.mk H =
      ClosedSubgroupConjClasses.mk (φ • H) := by
  rw [mk_smul_closedSubgroupConjClasses, ContinuousAut.smul_closedSubgroupConjClass]

end ContinuousOut

end TauCeti
