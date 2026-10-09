/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.Topology.Algebra.ContinuousZModDual

/-!
# The `ZMod n`-module structure on `H¹` and its continuous-dual interpretation

For a topological group `G` acting continuously on a `ZMod n`-module `A`, the quotient
`H¹(G, A) = Z¹/B¹` carries a `ZMod n`-module structure: scalar `n` annihilates every
`A`-valued element of the ambient group, hence every continuous `1`-cocycle, hence the
`1`-coboundaries and their cosets, so `TauCeti.instModuleH1` transports the module structure to
the quotient. This is the same
observation that gives the continuous character group its own `ZMod n`-module structure in
`TauCeti.Topology.Algebra.ContinuousZModDual`, and it needs no profiniteness and no pro-`p`
hypothesis: it holds for every `n` and every continuous action.

When the action is trivial, a continuous `1`-cocycle is a continuous character, so
`TauCeti.ContCohomology.H1EquivOfSmulEqSelf` identifies `H¹(G, ZMod n)` additively with the
continuous character group, and `TauCeti.h1EquivContinuousZModDual` upgrades that to an
isomorphism of `ZMod n`-modules with the continuous `ZMod n`-dual
`TauCeti.continuousZModDual n G` that the module structure makes meaningful. The modulus `n` is
arbitrary, so this is a statement about modules; when `n` is prime, `ZMod n` is a field and the
statement is one about vector spaces. The two application lemmas
`TauCeti.h1EquivContinuousZModDual_apply_mk` and
`TauCeti.h1EquivContinuousZModDual_symm_apply` compute the isomorphism in both directions, so the
identification is usable without unfolding it.

Taking `n` to be a prime `p` and `G` a pro-`p` group makes this the coefficient-level input to the
`H¹` interpretation of such a group: the pro-`p` consequence, the identification of `H¹(G, 𝔽_p)`
with the continuous `𝔽_p`-dual of the Frattini quotient and the transfer of Burnside's basis
theorem, is in `TauCeti.Topology.Algebra.Group.Profinite.ProP.H1Dual`.

## Main definitions

* `TauCeti.instModuleH1`: `H¹(G, A)` is a `ZMod n`-module when `A` is, for any continuous action.
* `TauCeti.h1EquivContinuousZModHom`: for a trivial action, `H¹(G, A)` is the module of
  continuous homomorphisms from `G` to the additive group of `A`.
* `TauCeti.h1EquivContinuousZModDual`: for a trivial action, `H¹(G, ZMod n)` is the continuous
  `ZMod n`-dual `TauCeti.continuousZModDual n G` of `G`, as `ZMod n`-modules.

## Main results

* `TauCeti.h1EquivContinuousZModDual_apply_mk`: the class of a continuous `1`-cocycle is sent to the
  character it defines.
* `TauCeti.h1EquivContinuousZModDual_symm_apply`: a continuous character is sent to the class of
  the `1`-cocycle it defines.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.1).
-/

public section

namespace TauCeti

open ContCohomology

universe u v

-- For prime `p`, `AddCommGroup (ZMod p)` is also derivable from `[IsSimpleAddGroup (ZMod p)]
-- [AddGroup.IsNilpotent (ZMod p)]`; that structure is not reducibly the ring one, so the
-- `DistribMulAction G (ZMod p)` hypothesis below would not match what `H1` expects. Preferring the
-- ring path locally keeps a single additive structure on `ZMod p` in every statement here.
attribute [local instance 2000] Ring.toAddCommGroup

section ModuleStructure

variable {n : ℕ} {G : Type u} [Monoid G] [TopologicalSpace G]
  {A : Type v} [AddCommGroup A] [Module (ZMod n) A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [DistribMulAction G A] [ContinuousSMul G A]

/-- **`H¹(G, A)` inherits the `ZMod n`-module structure of `A`.** Scalar `n` annihilates every
continuous `A`-valued `1`-cocycle, so it annihilates the subgroup of `1`-coboundaries, and the
quotient `Z¹/B¹` inherits a `ZMod n`-module structure. The coefficient action is arbitrary. -/
noncomputable instance instModuleH1 : Module (ZMod n) (H1 G A) :=
  QuotientAddGroup.zmodModule fun x ↦ by
    have hx : (n • x : Z1 G A) = 0 := by
      apply Subtype.ext
      funext g
      exact ZModModule.char_nsmul_eq_zero n _
    rw [hx]
    exact AddSubgroup.zero_mem _

end ModuleStructure

section ContinuousHom

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G]
  {A : Type v} [AddCommGroup A] [Module (ZMod n) A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [DistribMulAction G A] [ContinuousSMul G A]
  (htriv : ∀ (g : G) (a : A), g • a = a)

include htriv

/-- For a trivial action on a `ZMod n`-module `A`, first cohomology is the `ZMod n`-module of
continuous homomorphisms from `G` to the additive group of `A`. -/
noncomputable def h1EquivContinuousZModHom :
    H1 G A ≃ₗ[ZMod n] Additive (G →ₜ* Multiplicative A) :=
  (H1EquivOfSmulEqSelf htriv).toLinearEquiv
    (ZMod.map_smul (H1EquivOfSmulEqSelf htriv))

/-- The underlying additive equivalence of `h1EquivContinuousZModHom` is
`H1EquivOfSmulEqSelf`. -/
@[simp]
theorem h1EquivContinuousZModHom_apply (x : H1 G A) :
    h1EquivContinuousZModHom (n := n) htriv x = H1EquivOfSmulEqSelf htriv x :=
  congrFun (AddEquiv.coe_toLinearEquiv (H1EquivOfSmulEqSelf htriv)
    (ZMod.map_smul (H1EquivOfSmulEqSelf htriv))) x

/-- Applying `H1EquivOfSmulEqSelf` to the inverse of the linear equivalence recovers the
continuous homomorphism. -/
@[simp]
theorem H1EquivOfSmulEqSelf_h1EquivContinuousZModHom_symm_apply
    (f : Additive (G →ₜ* Multiplicative A)) :
    H1EquivOfSmulEqSelf htriv
      ((h1EquivContinuousZModHom (n := n) htriv).symm f) = f := by
  rw [← h1EquivContinuousZModHom_apply (n := n) htriv,
    LinearEquiv.apply_symm_apply]

end ContinuousHom

section ContinuousDual

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [DistribMulAction G (ZMod n)]
  [ContinuousSMul G (ZMod n)] (htriv : ∀ (g : G) (m : ZMod n), g • m = m)

include htriv

/-- **`H¹(G, ZMod n)` is the continuous `ZMod n`-dual of `G`.** A class of `H¹(G, ZMod n)` is
sent to the continuous homomorphism `G → Multiplicative ZMod n` that its cocycle defines, which
for trivial coefficients is that cocycle itself, as an isomorphism of `ZMod n`-modules. -/
noncomputable def h1EquivContinuousZModDual :
    H1 G (ZMod n) ≃ₗ[ZMod n] continuousZModDual n G :=
  h1EquivContinuousZModHom (n := n) htriv

/-- The continuous-dual equivalence has the same underlying map as
`H1EquivOfSmulEqSelf`. -/
@[simp]
theorem h1EquivContinuousZModDual_apply (x : H1 G (ZMod n)) :
    h1EquivContinuousZModDual htriv x = H1EquivOfSmulEqSelf htriv x :=
  h1EquivContinuousZModHom_apply htriv x

/-- The image of a class of `H¹(G, ZMod n)` is the character its cocycle defines: evaluated at `g`
it is the cocycle's value at `g`, read in the multiplicative encoding of `ZMod n`. -/
theorem h1EquivContinuousZModDual_apply_mk (f : Z1 G (ZMod n)) (g : G) :
    Additive.toMul (h1EquivContinuousZModDual htriv (f : H1 G (ZMod n))) g
      = Multiplicative.ofAdd ((f : G → ZMod n) g) := by
  simp [h1EquivContinuousZModDual]

/-- The inverse image of a continuous character is the class of the `1`-cocycle it defines. -/
@[simp]
theorem h1EquivContinuousZModDual_symm_apply (φ : continuousZModDual n G) :
    (h1EquivContinuousZModDual htriv).symm φ
      = ((Z1EquivOfSmulEqSelf htriv).symm φ : H1 G (ZMod n)) :=
  -- `h1EquivContinuousZModDual` is `H1EquivOfSmulEqSelf` read as a `ZMod n`-module isomorphism,
  -- so the inverse of the former is the inverse of the latter.
  (congrFun (AddEquiv.coe_toLinearEquiv_symm (H1EquivOfSmulEqSelf htriv)
      (ZMod.map_smul (H1EquivOfSmulEqSelf htriv))) φ).trans
    (H1EquivOfSmulEqSelf_symm_apply htriv φ)

end ContinuousDual

end TauCeti
