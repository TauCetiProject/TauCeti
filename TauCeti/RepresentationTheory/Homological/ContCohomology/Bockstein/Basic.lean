/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.ZMod.Four
public import TauCeti.Data.ZMod.MulCastHom
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Cup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ZModFourLift

/-!
# The mod-two Bockstein in degree one

The short exact sequence of trivial discrete modules
`0 → ℤ/2 → ℤ/4 → ℤ/2 → 0`, with doubling followed by reduction, defines a connecting map
`H¹(G, 𝔽₂) → H²(G, 𝔽₂)`. This file constructs that map on the explicit cochain model and
transports it to Mathlib's canonical continuous cohomology through the existing comparisons.
It is the cup square: lifting a character to its representatives in `{0, 1} ⊆ ℤ/4` gives a
coboundary whose half is the product cocycle `(g, h) ↦ χ(g)χ(h)`.

The resulting additive homomorphism `bockstein1` is natural in the group, and its kernel consists
exactly of the characters that lift to `ℤ/4`. Only degree one is treated here. Local compactness
is needed only for the comparison with the canonical degree-two model, not for the explicit
connecting map or its cup-square formula.

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (3.9.10).

The coefficient maps use `ZMod.mulCastHom` and `ZMod.castHom`. The connecting map is the existing
`DiscreteShortExact.explicitDelta1`, not a second construction of cohomology.
-/

public section

namespace TauCeti

open ContCohomology

universe u

-- Use the same additive structure as the explicit comparison for `ZMod` coefficients.
attribute [local instance 2000] Ring.toAddCommGroup

attribute [local instance] trivialZModAction

section Coefficients

variable (G : Type u) [Monoid G]

/-- The coefficient sequence defining the mod-two Bockstein: doubling into `ℤ/4`, followed by
reduction modulo two, with trivial `G`-action on all three terms. -/
def bocksteinShortExact : DiscreteShortExact G (ZMod 2) (ZMod 4) (ZMod 2) where
  incl := ZMod.mulCastHom 2 rfl
  proj := (ZMod.castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom
  incl_equivariant := fun _ _ ↦ rfl
  proj_equivariant := fun _ _ ↦ rfl
  incl_injective := ZMod.mulCastHom_injective 2 rfl two_ne_zero
  proj_surjective := ZMod.castHom_surjective (by decide : (2 : ℕ) ∣ 4)
  exact := ZMod.exact_mulCastHom_castHom 2 rfl

/-- The inclusion in the Bockstein sequence is doubling. -/
@[simp]
theorem bocksteinShortExact_incl :
    (bocksteinShortExact G).incl = ZMod.mulCastHom 2 rfl := (rfl)

/-- The projection in the Bockstein sequence is reduction modulo two. -/
@[simp]
theorem bocksteinShortExact_proj :
    (bocksteinShortExact G).proj =
      (ZMod.castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom := (rfl)

end Coefficients

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- The trivial actions on the discrete cyclic coefficient modules are continuous. -/
local instance bocksteinContinuousSMul (n : ℕ) : ContinuousSMul G (ZMod n) :=
  ⟨continuous_snd⟩

section Explicit

variable [ContinuousMul G]

/-- The mod-two Bockstein `H¹ → H²` on explicit continuous cohomology, defined by the connecting
map of the doubling-and-reduction sequence. -/
noncomputable def explicitBockstein1 : H1 G (ZMod 2) →+ H2 G (ZMod 2) :=
  (bocksteinShortExact G).explicitDelta1

/-- The explicit Bockstein is the connecting map of its named coefficient sequence. -/
theorem explicitBockstein1_def :
    explicitBockstein1 G = (bocksteinShortExact G).explicitDelta1 := (rfl)

/-- On a continuous one-cocycle, the mod-two Bockstein is represented by the product cocycle
`(g, h) ↦ f(g)f(h)`. -/
@[simp]
theorem explicitBockstein1_mk (f : Z1 G (ZMod 2)) :
    explicitBockstein1 G (f : H1 G (ZMod 2)) =
      ((⟨fun q : G × G ↦ f.val q.1 * f.val q.2,
        cup11_mem_Z2 G (ZMod 2) (ZMod 2) (ZMod 2) AddMonoidHom.mul continuous_mul
          (fun _ _ _ ↦ rfl) f.property f.property⟩ : Z2 G (ZMod 2)) : H2 G (ZMod 2)) := by
  rw [explicitBockstein1_def]
  apply (bocksteinShortExact G).explicitDelta1_apply f
    ((continuous_of_discreteTopology (f := fun x : ZMod 2 ↦ (x.cast : ZMod 4))).comp
      (mem_Z1_iff.mp f.property).1)
  · intro g
    simp only [bocksteinShortExact_proj, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass, ZMod.castHom_apply]
    simpa using ZMod.cast_cast_add_two_mul_cast (f.val g) 0
  · intro g h
    rw [bocksteinShortExact_incl, ZMod.mulCastHom_apply]
    have hf := (mem_Z1_iff.mp f.property).2 g h
    -- The action is trivial, so the cocycle identity is additivity of the character.
    have hadd : f.val (g * h) = f.val h + f.val g := hf
    simp only [Function.comp_apply]
    rw [hadd]
    have hcarry : ∀ a b : ZMod 2,
        (ZMod.cast (a * b) : ZMod 4) * 2 =
          (b.cast : ZMod 4) - (b + a).cast + a.cast := by
      intro a b
      have h := ZMod.cast_add_two_mul_cast_sub_mul b a 0 0
      simp only [add_zero, zero_sub, ZMod.neg_eq_self_mod_two, ZMod.cast_zero, mul_zero,
        mul_comm b a] at h
      linear_combination h
    exact hcarry _ _

/-- The degree-one mod-two Bockstein equals the cup square on explicit classes.
Use this as an explicit rewrite; a simp rule here would shadow the representative formula
`explicitBockstein1_mk`. -/
theorem explicitBockstein1_eq_explicitCup11_self (x : H1 G (ZMod 2)) :
    explicitBockstein1 G x =
      explicitCup11 G (ZMod 2) (ZMod 2) (ZMod 2) AddMonoidHom.mul continuous_mul
        (fun _ _ _ ↦ rfl) x x := by
  induction x using QuotientAddGroup.induction_on with
  | H f =>
    rw [explicitBockstein1_mk]
    exact (explicitCup11_mk G (ZMod 2) (ZMod 2) (ZMod 2) AddMonoidHom.mul continuous_mul
      (fun _ _ _ ↦ rfl) f f).symm

/-- A class is killed by the explicit Bockstein exactly when it comes from a class with trivial
`ℤ/4` coefficients under reduction modulo two. -/
theorem explicitBockstein1_eq_zero_iff (x : H1 G (ZMod 2)) :
    explicitBockstein1 G x = 0 ↔
      ∃ y : H1 G (ZMod 4),
        explicitCoeff1 G (ZMod 4) (bocksteinShortExact G).projDistribMulActionHom
          continuous_of_discreteTopology y = x := by
  rw [explicitBockstein1_def, ← AddMonoidHom.mem_ker,
    ← (bocksteinShortExact G).explicitLongExact_H1C]
  rfl

end Explicit

section Canonical

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The degree-one mod-two Bockstein on canonical continuous cohomology, transported from the
connecting map of `bocksteinShortExact` through the explicit comparisons. -/
noncomputable def bockstein1 : cohomFp 2 G 1 →+ cohomFp 2 G 2 :=
  (cohomFpAddEquivH2 2 G (fun _ _ ↦ rfl)).symm.toAddMonoidHom.comp
    ((explicitBockstein1 G).comp (cohomFpAddEquivH1 2 G (fun _ _ ↦ rfl)).toAddMonoidHom)

/-- The degree-two comparison carries the canonical Bockstein to the explicit connecting map. -/
@[simp]
theorem cohomFpAddEquivH2_bockstein1 (x : cohomFp 2 G 1) :
    cohomFpAddEquivH2 2 G (fun _ _ ↦ rfl) (bockstein1 G x) =
      explicitBockstein1 G (cohomFpAddEquivH1 2 G (fun _ _ ↦ rfl) x) := by
  simp [bockstein1]

/-- The mod-two Bockstein of a degree-one class is its cup square.
Use this as an explicit rewrite; a simp rule here would shadow the comparison, naturality,
and cyclic-value simp rules for `bockstein1`. -/
theorem bockstein1_eq_cupFp_self (x : cohomFp 2 G 1) :
    bockstein1 G x = cupFp 2 G x x := by
  apply (cohomFpAddEquivH2 2 G (fun _ _ ↦ rfl)).injective
  rw [cohomFpAddEquivH2_bockstein1, explicitBockstein1_eq_explicitCup11_self,
    cohomFpAddEquivH2_cupFp]

/-- The degree-one Bockstein commutes with pullback along a continuous group homomorphism. -/
@[simp]
theorem bockstein1_map {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] (φ : H →ₜ* G) (x : cohomFp 2 G 1) :
    bockstein1 H (cohomFpMap 2 φ 1 x) = cohomFpMap 2 φ 2 (bockstein1 G x) := by
  rw [bockstein1_eq_cupFp_self, bockstein1_eq_cupFp_self, cupFp_map]

/-- The kernel of the degree-one Bockstein consists exactly of classes of characters lifting to
`ℤ/4`. -/
theorem bockstein1_eq_zero_iff_exists_zmodFourReductionClass_eq (x : cohomFp 2 G 1) :
    bockstein1 G x = 0 ↔
      ∃ φ : G →ₜ* Multiplicative (ZMod 4), φ.zmodFourReductionClass = x := by
  rw [bockstein1_eq_cupFp_self, cupFp_self_eq_zero_iff_exists_zmodFourReductionClass_eq]

end Canonical

end TauCeti
