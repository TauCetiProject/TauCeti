/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini
public import TauCeti.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.Topology.Algebra.Group.Generation

/-!
# Continuous characters and the pro-`p` Frattini subgroup

A continuous homomorphism to a discrete group of cardinality `p` is either trivial or has kernel
of index `p`. Thus every continuous character into the multiplicative encoding
`Multiplicative (ZMod p)` of `𝔽_p` factors through the pro-`p` Frattini quotient. This is the
character-theoretic input to describing the generator rank of a pro-`p` group by its continuous
`𝔽_p`-valued characters. The lift uses the quotient topology.

The characters with values in `𝔽_p` themselves form the **continuous `𝔽_p`-dual**
`TauCeti.continuousFpDual p G`, an `𝔽_p`-vector space because `𝔽_p` has exponent `p`. When the group
is itself elementary abelian, a character of it is in particular a linear functional on it, so
`TauCeti.continuousFpDualToDual` embeds the continuous dual in the algebraic dual. Conversely
an open normal subgroup of index `p` has cyclic quotient of order `p` and is therefore the kernel
of such a character, so the pro-`p` Frattini subgroup is exactly the intersection of the kernels
of the continuous `𝔽_p`-valued characters. Precomposition with the projection to the Frattini
quotient is an isomorphism of `𝔽_p`-vector spaces from the dual of the quotient onto the dual
of `G`.

## Main definitions

* `TauCeti.continuousFpDual`: the group of continuous `𝔽_p`-valued characters, written additively.
* `TauCeti.continuousFpDualToDual`: a continuous `𝔽_p`-valued character of an elementary abelian
  group, read as a linear functional on it.

## Main results

* `TauCeti.proPFrattini_le_ker`: the pro-`p` Frattini subgroup is killed by every continuous
  character into a discrete group of cardinality `p`.
* `TauCeti.exists_continuousMonoidHom_ker_eq`: an open normal subgroup of index `p` is the kernel
  of a continuous `𝔽_p`-valued character.
* `TauCeti.proPFrattini_eq_iInf_ker`: the pro-`p` Frattini subgroup is the intersection of the
  kernels of the continuous `𝔽_p`-valued characters.
* `TauCeti.frattiniQuotientDualEquiv`: the continuous `𝔽_p`-dual of the Frattini quotient is the
  continuous `𝔽_p`-dual of `G`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

universe u

section FpDual

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-- The **continuous `𝔽_p`-dual** of a topological group: its group of continuous characters with
values in `𝔽_p`, written additively so that it is an `𝔽_p`-vector space. It is the discrete
companion of the compact Frattini quotient: by `TauCeti.frattiniQuotientDualEquiv` a character of
`G` is the same thing as a character of `G ⧸ proPFrattini p G`, and its dimension is the
topological generator rank of a pro-`p` group. -/
abbrev continuousFpDual (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Type u :=
  Additive (G →ₜ* Multiplicative (ZMod p))

/-- The continuous `ZMod n`-valued characters form a `ZMod n`-module: the target has exponent
dividing `n`, hence so does the character group. -/
instance instModuleContinuousFpDual : Module (ZMod n) (continuousFpDual n G) :=
  AddCommGroup.zmodModule fun x ↦ by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    ext g
    simp [ContinuousMonoidHom.pow_apply, toAdd_pow, nsmul_eq_mul]

end FpDual

section ToDual

variable {p : ℕ} {W : Type u} [CommGroup W] [TopologicalSpace W]
  [Module (ZMod p) (Additive W)]

/-- A continuous `𝔽_p`-valued character of an elementary abelian group `W`, read as a linear
functional on the `𝔽_p`-vector space `Additive W`. It is injective
(`TauCeti.continuousFpDualToDual_injective`), so the continuous dual is a subspace of the
algebraic dual. -/
def continuousFpDualToDual :
    continuousFpDual p W →ₗ[ZMod p] Module.Dual (ZMod p) (Additive W) :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun x ↦ AddMonoidHom.toZModLinearMap p
        { toFun := fun w ↦ Multiplicative.toAdd (Additive.toMul x (Additive.toMul w))
          map_zero' := by simp
          map_add' := fun a b ↦ by simp [toMul_add] }
      map_zero' := by ext w; simp
      map_add' := fun x y ↦ by ext w; simp }

@[simp]
theorem continuousFpDualToDual_apply (x : continuousFpDual p W) (w : Additive W) :
    continuousFpDualToDual x w = Multiplicative.toAdd (Additive.toMul x (Additive.toMul w)) :=
  (rfl)

theorem continuousFpDualToDual_injective :
    Function.Injective (continuousFpDualToDual (p := p) (W := W)) := fun x y h ↦ by
  apply Additive.toMul.injective
  ext w
  have hw := congrArg (fun f ↦ f (Additive.ofMul w)) h
  simp only [continuousFpDualToDual_apply, toMul_ofMul] at hw
  exact Multiplicative.toAdd.injective hw

theorem continuousFpDualToDual_eq_zero_iff {x : continuousFpDual p W} {w : Additive W} :
    continuousFpDualToDual x w = 0 ↔ Additive.toMul w ∈ (Additive.toMul x).ker := by
  simp [MonoidHom.mem_ker]

end ToDual

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The pro-`p` Frattini subgroup lies in the kernel of every continuous homomorphism to a
discrete group of cardinality `p`. -/
theorem proPFrattini_le_ker {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) :
    proPFrattini p G ≤ f.ker := by
  by_cases hf : ∀ x, f x = 1
  · intro x hx
    exact MonoidHom.mem_ker.mpr (hf x)
  · have hrange : f.toMonoidHom.range = ⊤ := by
      rcases (f.toMonoidHom.range).eq_bot_or_eq_top_of_prime_card
          (hp := ⟨hH ▸ Fact.out⟩) with hbot | htop
      · rw [MonoidHom.range_eq_bot_iff] at hbot
        exact (hf fun x => by simpa using DFunLike.congr_fun hbot x).elim
      · exact htop
    have hopen : IsOpen (f.ker : Set G) := by
      rw [MonoidHom.coe_ker]
      exact (isOpen_discrete {1}).preimage f.continuous
    have hindex : f.toMonoidHom.ker.index = p := by
      rw [Subgroup.index_ker, hrange]
      simp [hH]
    exact proPFrattini_le (U := ⟨⟨f.ker, hopen⟩, inferInstance⟩) hindex

/-- **An open normal subgroup of index `p` is the kernel of a continuous `𝔽_p`-valued
character.** Its quotient has prime order `p`, hence is cyclic of order `p`, and a homomorphism
with open kernel is continuous. -/
theorem exists_continuousMonoidHom_ker_eq [ContinuousMul G] {U : OpenNormalSubgroup G}
    (hU : U.toSubgroup.index = p) :
    ∃ φ : G →ₜ* Multiplicative (ZMod p), φ.ker = U.toSubgroup := by
  have hcard : Nat.card (G ⧸ U.toSubgroup) = p := (Subgroup.index_eq_card _).symm.trans hU
  let e : (G ⧸ U.toSubgroup) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcard (by simp)
  let f : G →* Multiplicative (ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' U.toSubgroup)
  have hker : f.ker = U.toSubgroup := by
    ext y
    simp [f]
  exact ⟨⟨f, f.continuous_of_isOpen_ker (hker ▸ U.isOpen)⟩, hker⟩

/-- **The pro-`p` Frattini subgroup is the intersection of the kernels of the continuous
`𝔽_p`-valued characters.** One inclusion is `TauCeti.proPFrattini_le_ker`; the other realises each
open normal subgroup of index `p` as such a kernel. -/
theorem proPFrattini_eq_iInf_ker [ContinuousMul G] :
    proPFrattini p G = ⨅ φ : G →ₜ* Multiplicative (ZMod p), φ.ker := by
  refine le_antisymm (le_iInf fun φ ↦ proPFrattini_le_ker (by simp) φ) fun x hx ↦ ?_
  refine mem_proPFrattini_iff.mpr fun U hU ↦ ?_
  obtain ⟨φ, hφ⟩ := exists_continuousMonoidHom_ker_eq hU
  exact hφ ▸ Subgroup.mem_iInf.mp hx φ

/-- Precomposition with the Frattini quotient projection identifies continuous homomorphisms
from the quotient with continuous homomorphisms from `G` for a discrete target of cardinality
`p`. -/
def frattiniQuotientHomEquiv {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) :
    ((G ⧸ proPFrattini p G) →ₜ* H) ≃ (G →ₜ* H) :=
  (ContinuousMonoidHom.quotientHomEquiv (proPFrattini p G)).trans
    (Equiv.subtypeUnivEquiv fun f => proPFrattini_le_ker hH f)

/-- Evaluation of precomposition with the Frattini quotient projection. -/
@[simp]
theorem frattiniQuotientHomEquiv_apply {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p)
    (g : (G ⧸ proPFrattini p G) →ₜ* H) :
    frattiniQuotientHomEquiv hH g =
      g.comp (ContinuousMonoidHom.quotientMk (proPFrattini p G)) := by
  dsimp [frattiniQuotientHomEquiv]
  exact ContinuousMonoidHom.quotientHomEquiv_apply_coe _ _

/-- Evaluation of the inverse Frattini quotient homomorphism equivalence. -/
@[simp]
theorem frattiniQuotientHomEquiv_symm_apply {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p)
    (f : G →ₜ* H) :
    (frattiniQuotientHomEquiv hH).symm f =
      ContinuousMonoidHom.quotientLift (proPFrattini p G) f
        (proPFrattini_le_ker hH f) := by
  dsimp [frattiniQuotientHomEquiv]
  exact ContinuousMonoidHom.quotientHomEquiv_symm_apply _ _

/-- Continuous homomorphisms to a discrete group of cardinality `p` factor uniquely through the
pro-`p` Frattini quotient. -/
theorem existsUnique_frattiniQuotient_lift {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) :
    ∃! g : (G ⧸ proPFrattini p G) →ₜ* H,
      g.comp (ContinuousMonoidHom.quotientMk (proPFrattini p G)) = f := by
  simpa only [frattiniQuotientHomEquiv_apply] using
    (frattiniQuotientHomEquiv hH).bijective.existsUnique f

/-- **Precomposition with the projection to the Frattini quotient is an isomorphism of
`𝔽_p`-vector spaces** from the continuous `𝔽_p`-dual of `G ⧸ proPFrattini p G` onto that of `G`:
every continuous `𝔽_p`-valued character of `G` kills the pro-`p` Frattini subgroup. -/
def frattiniQuotientDualEquiv :
    continuousFpDual p (G ⧸ proPFrattini p G) ≃ₗ[ZMod p] continuousFpDual p G :=
  let e : continuousFpDual p (G ⧸ proPFrattini p G) ≃+ continuousFpDual p G :=
    { Additive.ofMul.symm.trans
        ((frattiniQuotientHomEquiv (H := Multiplicative (ZMod p)) (by simp)).trans
          Additive.ofMul) with
      map_add' := fun x y ↦ by
        apply Additive.toMul.injective
        ext g
        simp [frattiniQuotientHomEquiv_apply] }
  { e with map_smul' := ZMod.map_smul e }

@[simp]
theorem frattiniQuotientDualEquiv_apply (x : continuousFpDual p (G ⧸ proPFrattini p G)) (g : G) :
    Additive.toMul (frattiniQuotientDualEquiv x) g = Additive.toMul x g := by
  simp [frattiniQuotientDualEquiv, frattiniQuotientHomEquiv_apply]

end TauCeti
