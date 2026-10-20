/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Group

/-!
# Quotients of torsors by normal subgroups

Let `G` be a group acting on `P` and let `H` be a normal subgroup of `G`. The space
`MulAction.orbitRel.Quotient H P` of `H`-orbits in `P` carries an action of the quotient group
`G ⧸ H`, given on representatives by `(g : G ⧸ H) • ⟦p⟧ = ⟦g • p⟧`. If `P` is a torsor under
`G`, then the orbit space is a torsor under `G ⧸ H`, with `⟦p⟧ /ₛ ⟦q⟧ = (p /ₛ q : G ⧸ H)`.

Additively: if `P` is an `AddTorsor` under `G` and `H` is a normal additive subgroup, then the
space of `H`-orbits is an `AddTorsor` under `G ⧸ H`. This is how a torsor under a group of
classes descends to a torsor under a quotient of that group.

## Main definitions

* `MulAction.orbitRel.Quotient.instMulActionQuotientGroup`: the action of `G ⧸ H` on the space
  of `H`-orbits, and its additive version.
* `MulAction.orbitRel.Quotient.instTorsorQuotientGroup`: the space of `H`-orbits of a
  `G`-torsor is a `G ⧸ H`-torsor, and its additive version.

## Main results

* `MulAction.orbitRel.Quotient.mk_eq_mk_iff_sdiv_mem`: two points of a torsor lie in the same
  `H`-orbit exactly when their difference lies in `H`.
* `MulAction.orbitRel.Quotient.mk_smul_mk`, `MulAction.orbitRel.Quotient.mk_sdiv_mk`: the action
  and the difference on the orbit space are computed on representatives.
-/

public section

namespace MulAction.orbitRel.Quotient

variable {G P : Type*} [Group G] (H : Subgroup G)

section Action

variable [MulAction G P] [H.Normal]

/-- Translating by elements of `G` that agree modulo the normal subgroup `H` sends points in the
same `H`-orbit to points in the same `H`-orbit. -/
@[to_additive /-- Translating by elements of `G` that agree modulo the normal subgroup `H` sends
points in the same `H`-orbit to points in the same `H`-orbit. -/]
theorem orbitRel_smul_smul {g g' : G} {p q : P} (hg : g⁻¹ * g' ∈ H)
    (hpq : orbitRel H P p q) : orbitRel H P (g • p) (g' • q) := by
  rw [orbitRel_apply, mem_orbit_iff] at hpq ⊢
  obtain ⟨⟨h, hh⟩, rfl⟩ := hpq
  refine ⟨⟨g * h * g'⁻¹, ?_⟩, ?_⟩
  · have hk : g * (h * (g⁻¹ * g')⁻¹) * g⁻¹ ∈ H :=
      ‹H.Normal›.conj_mem _ (H.mul_mem hh (H.inv_mem hg)) g
    simpa [mul_assoc] using hk
  · simp [subgroup_smul_def, smul_smul, mul_assoc]

/-- The quotient group `G ⧸ H` acts on the space of `H`-orbits by translating representatives. -/
@[to_additive /-- The quotient group `G ⧸ H` acts on the space of `H`-orbits by translating
representatives. -/]
instance instSMulQuotientGroup : SMul (G ⧸ H) (orbitRel.Quotient H P) where
  smul := Quotient.map₂ (· • ·) fun _ _ hg _ _ hpq =>
    orbitRel_smul_smul H (QuotientGroup.leftRel_apply.1 hg) hpq

/-- The action of `G ⧸ H` on `H`-orbits is computed on representatives. -/
@[to_additive (attr := simp) /-- The action of `G ⧸ H` on `H`-orbits is computed on
representatives. -/]
theorem mk_smul_mk (g : G) (p : P) :
    (g : G ⧸ H) • (Quotient.mk'' p : orbitRel.Quotient H P) = Quotient.mk'' (g • p) :=
  rfl

/-- The quotient group `G ⧸ H` acts on the space of `H`-orbits. -/
@[to_additive /-- The quotient group `G ⧸ H` acts on the space of `H`-orbits. -/]
instance instMulActionQuotientGroup : MulAction (G ⧸ H) (orbitRel.Quotient H P) where
  one_smul x := by
    induction x using Quotient.inductionOn' with
    | h p => rw [← QuotientGroup.mk_one, mk_smul_mk, one_smul]
  mul_smul g g' x := by
    induction g using QuotientGroup.induction_on with | H g =>
    induction g' using QuotientGroup.induction_on with | H g' =>
    induction x using Quotient.inductionOn' with
    | h p => rw [← QuotientGroup.mk_mul, mk_smul_mk, mk_smul_mk, mk_smul_mk, mul_smul]

end Action

section Torsor

variable [Torsor G P]

/-- Two points of a torsor lie in the same `H`-orbit exactly when their difference lies in
`H`. -/
@[to_additive /-- Two points of an additive torsor lie in the same `H`-orbit exactly when their
difference lies in `H`. -/]
theorem orbitRel_iff_sdiv_mem {p q : P} : orbitRel H P p q ↔ p /ₛ q ∈ H := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    simpa [subgroup_smul_def] using hh
  · intro h
    exact ⟨⟨p /ₛ q, h⟩, by simp [subgroup_smul_def]⟩

/-- Two points of a torsor have the same `H`-orbit exactly when their difference lies in `H`. -/
@[to_additive /-- Two points of an additive torsor have the same `H`-orbit exactly when their
difference lies in `H`. -/]
theorem mk_eq_mk_iff_sdiv_mem {p q : P} :
    (Quotient.mk'' p : orbitRel.Quotient H P) = Quotient.mk'' q ↔ p /ₛ q ∈ H := by
  rw [Quotient.eq'', orbitRel_iff_sdiv_mem]

variable [H.Normal]

/-- The class of `p /ₛ q` in `G ⧸ H` depends only on the `H`-orbits of `p` and `q`. -/
@[to_additive /-- The class of `p -ᵥ q` in `G ⧸ H` depends only on the `H`-orbits of `p` and
`q`. -/]
theorem mk_sdiv_eq_mk_sdiv {p p' q q' : P} (hp : orbitRel H P p p')
    (hq : orbitRel H P q q') : ((p /ₛ q : G) : G ⧸ H) = (p' /ₛ q' : G) := by
  rw [orbitRel_iff_sdiv_mem] at hp hq
  rw [QuotientGroup.eq]
  have hk : (p /ₛ q)⁻¹ * (p /ₛ p')⁻¹ * (p /ₛ q)⁻¹⁻¹ * (q /ₛ q') ∈ H :=
    H.mul_mem (‹H.Normal›.conj_mem _ (H.inv_mem hp) (p /ₛ q)⁻¹) hq
  rw [← sdiv_mul_sdiv_cancel p' p q', ← sdiv_mul_sdiv_cancel p q q', ← inv_sdiv_eq_sdiv_rev p p']
  convert hk using 1
  group

/-- The difference of two `H`-orbits in a torsor, as an element of `G ⧸ H`. -/
@[to_additive /-- The difference of two `H`-orbits in an additive torsor, as an element of
`G ⧸ H`. -/]
instance instSDivQuotientGroup : SDiv (G ⧸ H) (orbitRel.Quotient H P) where
  sdiv := Quotient.lift₂ (fun p q => ((p /ₛ q : G) : G ⧸ H)) fun _ _ _ _ hp hq =>
    mk_sdiv_eq_mk_sdiv H hp hq

/-- The difference of two `H`-orbits is computed on representatives. -/
@[to_additive (attr := simp) /-- The difference of two `H`-orbits is computed on
representatives. -/]
theorem mk_sdiv_mk (p q : P) :
    (Quotient.mk'' p : orbitRel.Quotient H P) /ₛ Quotient.mk'' q = ((p /ₛ q : G) : G ⧸ H) :=
  rfl

/-- The space of `H`-orbits of a `G`-torsor is a torsor under `G ⧸ H`. -/
@[to_additive /-- The space of `H`-orbits of an additive `G`-torsor is an additive torsor under
`G ⧸ H`. -/]
instance instTorsorQuotientGroup : Torsor (G ⧸ H) (orbitRel.Quotient H P) where
  nonempty := (Torsor.nonempty (G := G) (P := P)).map Quotient.mk''
  sdiv_smul' x y := by
    induction x using Quotient.inductionOn' with | h p =>
    induction y using Quotient.inductionOn' with
    | h q => rw [mk_sdiv_mk, mk_smul_mk, sdiv_smul]
  smul_sdiv' g x := by
    induction g using QuotientGroup.induction_on with | H g =>
    induction x using Quotient.inductionOn' with
    | h p => rw [mk_smul_mk, mk_sdiv_mk, smul_sdiv]

end Torsor

end MulAction.orbitRel.Quotient
