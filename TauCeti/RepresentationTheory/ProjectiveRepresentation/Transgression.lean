/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ProjectiveRepresentation.CommonExtension
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Finite

/-!
# Surjective character transgression for the common lifting extension

Every Schur-multiplier class is obtained by pushing the common lifting factor set
forward along a character of its kernel. Together with the extension criterion in
`TauCeti.FactorSet.cohomologyClass_map_eq_iff`, this describes both the image and
the fibers of its character transgression. The kernel characters that extend to the
whole group are exactly those invisible to second cohomology.

This is the character-side input to reducing a common lifting extension to a Schur
cover: stem extensions have injective transgression, while this extension has
surjective transgression. No stem property of the common extension is asserted.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapters 2–3.
-/

public section

namespace TauCeti

attribute [local instance] trivialMulDistribMulAction

variable (k G : Type) [Field k] [IsAlgClosed k] [Group G] [Finite G]

/-- The character transgression of the common finite lifting extension is surjective
onto the Schur multiplier, in arbitrary characteristic. -/
theorem projectiveLiftingFactorSet_cohomologyClass_map_surjective :
    Function.Surjective (fun χ :
      (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k) →*[G] kˣ ↦
        ((projectiveLiftingFactorSet k G).map χ).cohomologyClass) := by
  intro x
  obtain ⟨α, hα, hpow, hx⟩ := exists_isFactorSet_pow_card_eq_one_cohomologyClass_eq x
  let b : FactorSet G (rootsOfUnity (Nat.card G) k) :=
    { toFun p := ⟨α p.1 p.2, (mem_rootsOfUnity _ _).2 (hpow p.1 p.2)⟩
      isMulCocycle₂' g h j := Subtype.ext (hα.cocycle g h j)
      map_one_one' := Subtype.ext (hα.one_left 1) }
  let ev : (FactorSet G (rootsOfUnity (Nat.card G) k) → rootsOfUnity (Nat.card G) k)
      →*[G] kˣ :=
    { (rootsOfUnity (Nat.card G) k).subtype.comp
        (Pi.evalMonoidHom (fun _ : FactorSet G (rootsOfUnity (Nat.card G) k) ↦
          rootsOfUnity (Nat.card G) k) b) with
      map_smul' _ _ := rfl }
  have hev (a) : ev a = (a b : kˣ) := rfl
  refine ⟨ev, ?_⟩
  have hfac : (projectiveLiftingFactorSet k G).map ev =
      (isProjectiveRep_twistedRegularRep k G α).factorSet := by
    ext p
    simp only [FactorSet.map_apply, hev, projectiveLiftingFactorSet_apply,
      IsProjectiveRep.factorSet_apply]
    rfl
  exact (congrArg FactorSet.cohomologyClass hfac).trans
    ((IsProjectiveRep.cohomologyClass_def _).symm.trans hx)

end TauCeti
