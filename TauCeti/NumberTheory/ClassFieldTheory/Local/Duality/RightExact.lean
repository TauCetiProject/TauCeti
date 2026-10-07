/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Perfect

import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero
import TauCeti.Algebra.Module.ZMod.Extend
import TauCeti.Algebra.Module.ZMod.Injective

/-!
# Right exactness of local second cohomology

For finite smooth discrete coefficients of exponent invertible in a nonarchimedean local field,
`H²` carries surjections to surjections. Consequently the long exact sequence of a short exact
sequence of such coefficients terminates at `H²`. This is the endpoint needed for
multiplicativity of the three-term local Euler characteristic.

The proof uses local Tate duality for the named evaluation pairing
(`tateDualityPairing_flip_perfect`). The dual coefficient map is injective on invariants, and
characters of these invariants extend because `ZMod n` is self-injective. Naturality of the
pairing then transports the extended character back to a second cohomology class.

## Main results

* `TauCeti.ClassFieldTheory.coeffMap_two_surjective`: a surjective coefficient morphism induces
  a surjection on local `H²`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.6), (7.3.1).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory ContCohomology

variable {n : ℕ} {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A surjection from a finite smooth discrete Galois representation to a discrete representation
induces a surjection on second continuous cohomology when the coefficient exponent is invertible
in the local field. The target is automatically finite and smooth. -/
theorem coeffMap_two_surjective (hn : IsUnit (n : F)) {B C : GalRep n F}
    [DiscreteTopology B.V] [DiscreteTopology C.V] [Finite B.V]
    [Fact (IsSmoothDiscrete (ZMod n) B)]
    (f : B ⟶ C) (hf : Function.Surjective f.hom) :
    Function.Surjective (ContinuousCohomology.coeffMap f 2).hom := by
  have : NeZero n := NeZero.of_neZero_natCast F (h := ⟨hn.ne_zero⟩)
  have : Finite C.V := Finite.of_surjective f.hom hf
  have : Fact (IsSmoothDiscrete (ZMod n) C) := by
    let := B.distribMulAction
    let := C.distribMulAction
    refine ⟨⟨inferInstance, fun c ↦ ?_⟩⟩
    obtain ⟨b, rfl⟩ := hf c
    -- The target stabilizer contains the open stabilizer of any lift.
    rw [← TopRep.coe_stabilizer]
    apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Field.absoluteGaloisGroup F) b)
    · intro g hg
      simp only [MulAction.mem_stabilizer_iff, TopRep.distribMulAction_smul] at hg ⊢
      rw [← f.hom.isIntertwining, hg]
    · simpa only [TopRep.coe_stabilizer] using
        (Fact.out : IsSmoothDiscrete (ZMod n) B).stabilizer_isOpen b
  let tr := h2MuEquivZMod F hn
  let ι := (ContinuousCohomology.coeffMap (tateDualMap f) 0).hom.toAddMonoidHom
  -- On H⁰ the dual map is its restriction to invariants, hence is injective.
  have hι : Function.Injective ι := by
    intro x y hxy
    apply (ContinuousCohomology.zeroIso (tateDual C)).toContinuousLinearEquiv.injective
    rw [Iso.toContinuousLinearEquiv_apply, Iso.toContinuousLinearEquiv_apply]
    apply Subtype.ext
    apply tateDualMap_injective_of_surjective hf
    have h := congrArg (fun z => ((ContinuousCohomology.zeroIso (tateDual B)).hom z).val) hxy
    have hnat := ContinuousCohomology.coeffMap_comp_zeroIso_hom (tateDualMap f)
    have hx := ConcreteCategory.congr_hom hnat x
    have hy := ConcreteCategory.congr_hom hnat y
    simpa only [ι, ConcreteCategory.comp_apply, TopModuleCat.hom_ofHom,
      ContIntertwiningMap.mapInvariants_apply] using
      (congrArg Subtype.val hx).symm.trans (h.trans (congrArg Subtype.val hy))
  intro y
  let φ : continuousCohomology 0 (tateDual C) →+ ZMod n :=
    { toFun := fun x => tateDualityPairing C tr 0 2 rfl x y
      map_zero' := tateDualityPairing_zero_left C tr 0 2 rfl y
      map_add' := fun x x' => tateDualityPairing_add_left C tr 0 2 rfl x x' y }
  obtain ⟨ψ, hψ⟩ := AddMonoidHom.exists_comp_eq_of_injective_of_baer
    (Module.Baer.zmod_self n)
    (fun x : continuousCohomology 0 (tateDual B) =>
      ZModModule.char_nsmul_eq_zero n x) hι φ
  obtain ⟨b, hb⟩ := (tateDualityPairing_flip_perfect hn B tr 0 2 rfl).2 ψ
  refine ⟨b, ?_⟩
  apply sub_eq_zero.mp
  apply (tateDualityPairing_flip_perfect hn C tr 0 2 rfl).1
  intro x
  have hpair : tateDualityPairing C tr 0 2 rfl x
      ((ContinuousCohomology.coeffMap f 2).hom b) = tateDualityPairing C tr 0 2 rfl x y := by
    rw [← tateDualityPairing_tateDualMap, hb]
    exact DFunLike.congr_fun hψ x
  -- Additivity turns equality of all evaluations into annihilation of the difference.
  have hadd := tateDualityPairing_add_right C tr 0 2 rfl x
    ((ContinuousCohomology.coeffMap f 2).hom b - y) y
  rw [sub_add_cancel, hpair] at hadd
  exact add_eq_right.mp hadd.symm

end TauCeti.ClassFieldTheory
