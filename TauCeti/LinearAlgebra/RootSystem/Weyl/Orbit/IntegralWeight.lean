/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Base
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.RestrictScalars
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.MixedSign
import TauCeti.Algebra.Group.Subsemigroup.Pointwise
import TauCeti.LinearAlgebra.RootSystem.SimpleReflections

/-!
# The Weyl orbits of integral weights

Let `b` be a base of a finite reduced crystallographic root system. An integral family
`χ : b.support → ℤ` is the family of pairings of a unique vector with the simple coroots, and the
simple reflections act on these families by `χ ↦ χ - χ i • b.cartanMatrix.row i`. Reading the Weyl
orbit dichotomy of `TauCeti/LinearAlgebra/RootSystem/Weyl/Orbit/MixedSign.lean` on such families,
over the form of the root system over `ℚ` given by
`TauCeti/LinearAlgebra/RootSystem/BaseChange/RestrictScalars.lean`, gives an induction principle: a
property of integral weights that is stable under the simple reflections, and that holds on all the
weights outside `Q⁺ ∪ -Q⁺` and on the proper multiples of the weights of roots, holds at every
nonzero family that is not the weight of a root.

This is the combinatorial step in Serre's theorem presenting a split semisimple Lie algebra: the
weight spaces of the presented algebra are permuted by the simple reflections, and vanish on the
weights named in the hypotheses.

## Main results

* `RootPairing.Base.mem_posRootCone_of_mem_closure_range_row`: a vector whose pairings with the
  simple coroots are a sum of rows of the Cartan matrix lies in the positive root cone.
* `RootPairing.Base.forall_coroot'_smul_iff`: a property of integral families stable under the
  simple reflections is invariant under the Weyl group, read on the pairings with simple coroots.
* `RootPairing.Base.induction_integralWeight_reflection`: the induction principle.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §18.3.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, Appendix.
-/

public section

open TauCeti

namespace RootPairing.Base

section Coordinates

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

variable [P.IsCrystallographic]

/-- A vector whose pairings with the simple coroots are a sum of rows of the Cartan matrix lies in
the positive root cone. -/
theorem mem_posRootCone_of_mem_closure_range_row [P.IsRootSystem] [CharZero R]
    {χ : b.support → ℤ}
    (hχ : χ ∈ AddSubsemigroup.closure (Set.range b.cartanMatrix.row)) {x : M}
    (hx : ∀ k : b.support, P.coroot' k x = (χ k : R)) : x ∈ posRootCone P b := by
  have key : ∃ y ∈ posRootCone P b, ∀ k : b.support, P.coroot' k y = (χ k : R) := by
    clear hx
    induction hχ using AddSubsemigroup.closure_induction with
    | mem _ hψ =>
      obtain ⟨i, rfl⟩ := hψ
      exact ⟨P.root i, root_mem_posRootCone_of_mem_posRoots P b
        ((mem_posRoots P b _).2 (b.isPos_of_mem_support i.2)),
        coroot'_root_eq_cartanMatrix_row b i⟩
    | add _ _ _ _ h₁ h₂ =>
      obtain ⟨y₁, hy₁, h₁⟩ := h₁
      obtain ⟨y₂, hy₂, h₂⟩ := h₂
      exact ⟨y₁ + y₂, add_mem hy₁ hy₂, fun k ↦ by
        rw [map_add, h₁, h₂, Pi.add_apply, Int.cast_add]⟩
  obtain ⟨y, hy, hyx⟩ := key
  rwa [b.ext_coroot' fun k ↦ (hx k).trans (hyx k).symm]

/-- A property of integral families that is stable under the simple reflections holds at the
pairings of a vector with the simple coroots exactly when it holds at those of its Weyl translates:
the simple reflections act on these pairings by `χ ↦ χ - χ i • b.cartanMatrix.row i`. -/
theorem forall_coroot'_smul_iff [Finite ι] [CharZero R] [IsDomain R] [P.IsReduced]
    {Q : (b.support → ℤ) → Prop}
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (w : P.weylGroup) (y : M) :
    (∀ ψ : b.support → ℤ, (∀ k : b.support, P.coroot' k (w • y) = (ψ k : R)) → Q ψ) ↔
      ∀ ψ : b.support → ℤ, (∀ k : b.support, P.coroot' k y = (ψ k : R)) → Q ψ := by
  have hstep (i : b.support) (y : M)
      (hy : ∀ ψ : b.support → ℤ,
        (∀ k : b.support, P.coroot' k (weylGroup.ofIdx P i • y) = (ψ k : R)) → Q ψ)
      (ψ : b.support → ℤ) (hψ : ∀ k : b.support, P.coroot' k y = (ψ k : R)) : Q ψ := by
    have hreflect : ∀ k : b.support, P.coroot' k (weylGroup.ofIdx P i • y) =
        ((ψ - ψ i • b.cartanMatrix.row i) k : R) := fun k ↦ by
      simp only [weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply, map_sub, map_smul,
        coroot'_root_eq_cartanMatrix_row b i k, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Int.cast_sub, Int.cast_mul]
      rw [hψ k, hψ i]
    have hinv : (ψ - ψ i • b.cartanMatrix.row i) -
        (ψ - ψ i • b.cartanMatrix.row i) i • b.cartanMatrix.row i = ψ := by
      funext k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply,
        cartanMatrix_apply_same]
      ring
    exact hinv ▸ hrefl _ i (hy _ hreflect)
  have hw : w ∈ Subgroup.closure (Set.range fun i : b.support ↦ weylGroup.ofIdx P (i : ι)) :=
    weylGroup_eq_closure_simple P b ▸ Subgroup.mem_top w
  induction hw using Subgroup.closure_induction generalizing y with
  | mem _ hw =>
    obtain ⟨i, rfl⟩ := hw
    refine ⟨hstep i y, fun hy ↦ hstep i _ ?_⟩
    rwa [smul_smul, weylGroup.ofIdx_mul_self, one_smul]
  | one => simp
  | mul u v _ _ hu hv =>
    rw [mul_smul]
    exact (hu _).trans (hv y)
  | inv u _ hu => simpa only [smul_inv_smul] using (hu (u⁻¹ • y)).symm

end Coordinates

section Ordered

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsRootSystem] [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- The induction principle `RootPairing.Base.induction_integralWeight_reflection` for a root system
over a linearly ordered field, where the Weyl orbit dichotomy applies. The family `χ` is the family
of pairings of a vector `x`, which either is a proper multiple of a root or has a Weyl translate
outside `Q⁺ ∪ -Q⁺`. -/
private theorem induction_integralWeight_reflection_of_ordered {Q : (b.support → ℤ) → Prop}
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (hcone : ∀ χ : b.support → ℤ, χ ≠ 0 →
      χ ∉ AddSubsemigroup.closure (Set.range b.cartanMatrix.row) →
      χ ∉ AddSubsemigroup.closure (Set.range (-b.cartanMatrix.row)) → Q χ)
    (hmul : ∀ (j : ι) {m : ℕ}, 2 ≤ m → Q fun k : b.support ↦ m * P.pairingIn ℤ j k)
    {χ : b.support → ℤ} (h0 : χ ≠ 0)
    (hroot : ∀ j : ι, χ ≠ fun k : b.support ↦ P.pairingIn ℤ j k) : Q χ := by
  classical
  -- The coroot functionals of `P` are by definition the root functionals of its flip.
  obtain ⟨x, hx'⟩ := b.flip.exists_forall_root'_eq (P := P.flip)
    fun i ↦ if h : i ∈ b.support then (χ ⟨i, h⟩ : R) else 0
  have hx (k : b.support) : P.coroot' k x = (χ k : R) :=
    (hx' k k.2).trans (by simp)
  have hx₀ : x ≠ 0 := by
    rintro rfl
    refine h0 (funext fun k ↦ Int.cast_injective (α := R) ?_)
    simpa using (hx k).symm
  have hxroot (j : ι) : x ≠ P.root j := by
    rintro rfl
    refine hroot j (funext fun k ↦ Int.cast_injective (α := R) ?_)
    rw [← hx k, root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, eq_intCast]
  obtain ⟨w, h₁, h₂⟩ | ⟨j, m, hm, rfl⟩ :=
    P.exists_weylGroup_smul_notMem_posRootCone_or_eq_nsmul_root b hx₀ hxroot
  · refine (forall_coroot'_smul_iff b hrefl w x).1 (fun ψ hψ ↦ hcone ψ ?_ ?_ ?_) χ hx
    · rintro rfl
      refine hx₀ (smul_eq_zero_iff_eq w |>.1 (b.ext_coroot' fun k ↦ ?_))
      simpa using hψ k
    · exact fun hc ↦ h₁ (mem_posRootCone_of_mem_closure_range_row b hc hψ)
    · refine fun hc ↦ h₂ (mem_posRootCone_of_mem_closure_range_row b
        ((AddSubsemigroup.mem_closure_neg _ _).1 (Set.neg_range' (f := b.cartanMatrix.row) ▸ hc))
        fun k ↦ ?_)
      rw [map_neg, hψ k, Pi.neg_apply, Int.cast_neg]
  · have hχ : χ = fun k : b.support ↦ m * P.pairingIn ℤ j k := by
      refine funext fun k ↦ Int.cast_injective (α := R) ?_
      rw [← hx k, map_nsmul, root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, eq_intCast]
      simp
    exact hχ ▸ hmul j hm

end Ordered

variable {ι R M N : Type*} [Field R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsRootSystem] [Finite ι] [P.IsCrystallographic]
  [P.IsReduced] (b : P.Base)

/-- **Induction on the integral weights.** For a base of a finite reduced crystallographic root
system over a field of characteristic zero, a property of integral families that is stable under the
simple reflections, that holds at the nonzero families outside the additive semigroups generated by
the rows of the Cartan matrix and by their negatives, and that holds at the multiples `m ≥ 2` of the
weights `k ↦ ⟨αⱼ, αₖ∨⟩` of the roots, holds at every nonzero family that is not the weight of a
root. -/
theorem induction_integralWeight_reflection {Q : (b.support → ℤ) → Prop}
    (hrefl : ∀ (χ : b.support → ℤ) (i : b.support), Q χ → Q (χ - χ i • b.cartanMatrix.row i))
    (hcone : ∀ χ : b.support → ℤ, χ ≠ 0 →
      χ ∉ AddSubsemigroup.closure (Set.range b.cartanMatrix.row) →
      χ ∉ AddSubsemigroup.closure (Set.range (-b.cartanMatrix.row)) → Q χ)
    (hmul : ∀ (j : ι) {m : ℕ}, 2 ≤ m → Q fun k : b.support ↦ m * P.pairingIn ℤ j k)
    {χ : b.support → ℤ} (h0 : χ ≠ 0)
    (hroot : ∀ j : ι, χ ≠ fun k : b.support ↦ P.pairingIn ℤ j k) : Q χ := by
  -- Pass to the form of the root system over `ℚ`, which has the same integer pairings.
  let _ : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _ : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  have hrow : (b.restrictScalars' ℚ).cartanMatrix = b.cartanMatrix :=
    b.cartanMatrix_restrictScalars' ℚ
  refine induction_integralWeight_reflection_of_ordered (b.restrictScalars' ℚ) (Q := Q)
    (by rwa [hrow]) (by rwa [hrow]) (fun j m hm ↦ ?_) h0 fun j ↦ ?_
  · have hpair : (fun k : b.support ↦ (m : ℤ) * (P.restrictScalars' ℚ).pairingIn ℤ j k) =
        fun k : b.support ↦ (m : ℤ) * P.pairingIn ℤ j k :=
      funext fun k ↦ by rw [pairingIn_restrictScalars']
    exact (congrArg Q hpair).mpr (hmul j hm)
  · refine fun h ↦ hroot j (h.trans (funext fun k ↦ ?_))
    exact pairingIn_restrictScalars' ℚ j k

end RootPairing.Base
