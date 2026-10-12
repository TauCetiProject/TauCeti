/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Functoriality of the pro-`p` Frattini quotient

For a prime `p`, every continuous homomorphism of profinite groups carries the pro-`p` Frattini
subgroup into the pro-`p` Frattini subgroup. It therefore induces a continuous homomorphism on
the Frattini quotients. Since these quotients are elementary abelian `p`-groups, the induced map
is also canonically `ZMod p`-linear after switching to additive notation.

The induced maps preserve identities and composition. A continuous surjection induces a
surjection on Frattini quotients, expressing that the Frattini quotient construction commutes
with continuous quotients.

## Main definitions

* `TauCeti.frattiniQuotientMap`: the continuous map on Frattini quotients induced by a continuous
  homomorphism of profinite groups.
* `TauCeti.frattiniQuotientLinearMap`: the same map as a `ZMod p`-linear map.

## Main results

* `TauCeti.frattiniQuotientMap_id`, `TauCeti.frattiniQuotientMap_comp`: the Frattini quotient is
  functorial.
* `TauCeti.frattiniQuotientMap_surjective`: a continuous surjection remains surjective on
  Frattini quotients.
* `TauCeti.frattiniQuotientLinearMap_id`, `TauCeti.frattiniQuotientLinearMap_comp`: the same
  functoriality in the category of `ZMod p`-modules.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

universe u v w

variable {p : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {K : Type w} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- The continuous homomorphism on pro-`p` Frattini quotients induced by a continuous
homomorphism from a profinite group. Its value on a class is given by
`TauCeti.frattiniQuotientMap_mk`. -/
def frattiniQuotientMap (hp : p.Prime) (f : G →ₜ* H) :
    (G ⧸ proPFrattini p G) →ₜ* (H ⧸ proPFrattini p H) :=
  ContinuousMonoidHom.quotientLift (proPFrattini p G)
    ((ContinuousMonoidHom.quotientMk (proPFrattini p H)).comp f)
    (by
      intro g hg
      rw [MonoidHom.mem_ker]
      simpa only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
        ContinuousMonoidHom.coe_comp, Function.comp_apply,
        ContinuousMonoidHom.quotientMk_apply] using
        (QuotientGroup.eq_one_iff (f g)).mpr
          (f.toMonoidHom.proPFrattini_le_comap_of_prime hp f.continuous hg))

/-- The map induced on Frattini quotients sends the class of `g` to the class of its image. -/
@[simp]
theorem frattiniQuotientMap_mk (hp : p.Prime) (f : G →ₜ* H) (g : G) :
    frattiniQuotientMap hp f (g : G ⧸ proPFrattini p G) =
      (f g : H ⧸ proPFrattini p H) := by
  rw [frattiniQuotientMap, ContinuousMonoidHom.quotientLift_mk,
    ContinuousMonoidHom.coe_comp, Function.comp_apply,
    ContinuousMonoidHom.quotientMk_apply]

/-- The identity homomorphism induces the identity on the pro-`p` Frattini quotient. -/
@[simp]
theorem frattiniQuotientMap_id (hp : p.Prime) :
    frattiniQuotientMap hp (ContinuousMonoidHom.id G) =
      ContinuousMonoidHom.id (G ⧸ proPFrattini p G) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => simp

/-- The map on pro-`p` Frattini quotients induced by a composite is the composite of the induced
maps. -/
@[simp]
theorem frattiniQuotientMap_comp [CompactSpace H] [TotallyDisconnectedSpace H]
    (hp : p.Prime) (g : H →ₜ* K) (f : G →ₜ* H) :
    frattiniQuotientMap hp (g.comp f) =
      (frattiniQuotientMap hp g).comp (frattiniQuotientMap hp f) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x => simp

/-- A continuous surjection of profinite groups induces a surjection on pro-`p` Frattini
quotients. -/
theorem frattiniQuotientMap_surjective (hp : p.Prime) (f : G →ₜ* H)
    (hf : Function.Surjective f) :
    Function.Surjective (frattiniQuotientMap hp f) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (proPFrattini p H) y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨(x : G ⧸ proPFrattini p G), frattiniQuotientMap_mk hp f x⟩

section Linear

variable [Fact p.Prime]

/-- The `ZMod p`-linear map on additive pro-`p` Frattini quotients induced by a continuous
homomorphism of profinite groups. -/
def frattiniQuotientLinearMap (f : G →ₜ* H) :
    Additive (G ⧸ proPFrattini p G) →ₗ[ZMod p]
      Additive (H ⧸ proPFrattini p H) :=
  (MonoidHom.toAdditive (frattiniQuotientMap Fact.out f).toMonoidHom).toZModLinearMap p

/-- The linear map induced on additive Frattini quotients sends the class of `g` to the class of
its image. -/
@[simp]
theorem frattiniQuotientLinearMap_mk (f : G →ₜ* H) (g : G) :
    frattiniQuotientLinearMap (p := p) f
        (Additive.ofMul (g : G ⧸ proPFrattini p G)) =
      Additive.ofMul (f g : H ⧸ proPFrattini p H) := by
  exact congrArg Additive.ofMul (frattiniQuotientMap_mk Fact.out f g)

/-- The identity homomorphism induces the identity linear map on the additive pro-`p` Frattini
quotient. -/
@[simp]
theorem frattiniQuotientLinearMap_id :
    frattiniQuotientLinearMap (p := p) (ContinuousMonoidHom.id G) =
      LinearMap.id (R := ZMod p) (M := Additive (G ⧸ proPFrattini p G)) := by
  ext x
  cases x with
  | ofMul x =>
    induction x using QuotientGroup.induction_on with
    | H g => simp

/-- The linear map on additive pro-`p` Frattini quotients induced by a composite is the composite
of the induced linear maps. -/
@[simp]
theorem frattiniQuotientLinearMap_comp [CompactSpace H] [TotallyDisconnectedSpace H]
    (g : H →ₜ* K) (f : G →ₜ* H) :
    frattiniQuotientLinearMap (p := p) (g.comp f) =
      (frattiniQuotientLinearMap (p := p) g).comp
        (frattiniQuotientLinearMap (p := p) f) := by
  ext x
  cases x with
  | ofMul x =>
    induction x using QuotientGroup.induction_on with
    | H x => simp

/-- A continuous surjection of profinite groups induces a surjective linear map on their
additive pro-`p` Frattini quotients. -/
theorem frattiniQuotientLinearMap_surjective (f : G →ₜ* H) (hf : Function.Surjective f) :
    Function.Surjective (frattiniQuotientLinearMap (p := p) f) := by
  intro y
  obtain ⟨x, hx⟩ := frattiniQuotientMap_surjective (p := p) Fact.out f hf y.toMul
  exact ⟨Additive.ofMul x, Additive.toMul.injective (hx.trans (ofMul_toMul y).symm)⟩

end Linear

end TauCeti
