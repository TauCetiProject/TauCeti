/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import TauCeti.SetTheory.Cardinal.Finite

/-!
# The transfer sequence of a double cover in characteristic two

Let `p : E ⟶ B` be a covering map with finite fibres and `R` a ring. The permutation local system
`R[p]` of `p`, whose fibre over `b` is the free module on the sheets over `b`, receives the transfer
`R ⟶ R[p]`, sending `r` to the sum of all sheets with coefficient `r`
(`IsCoveringMap.permutationLocalSystemTransfer`), and maps onto `R` by the augmentation
`R[p] ⟶ R`, which adds up the coefficients of the sheets
(`IsCoveringMap.permutationLocalSystemAugmentation`). Their composite multiplies by the number of
sheets.

For a double cover, every fibre having exactly two points, and `R` of characteristic two, this
composite vanishes and the sequence

`0 ⟶ R ⟶ R[p] ⟶ R ⟶ 0`

is short exact (`IsCoveringMap.shortExact_permutationLocalSystemTransfer_augmentation`): a
formal sum `a e + b e'` of the two sheets over a point has augmentation `a + b`, which vanishes
exactly when `b = -a = a`, that is when the formal sum is the transfer of `a`. So in characteristic
two the kernel of the augmentation is the constant local system. In general it is the sign local
system of the involution exchanging the two sheets
(`IsCoveringMap.shortExact_signPermutationShortComplex`), on which a loop acts by `-1` when its
lift exchanges them; in characteristic two `-1 = 1`. The Thom isomorphism of a line bundle holds
for every short exact sequence `0 ⟶ L ⟶ R[p] ⟶ R ⟶ 0` on the double cover of its unit vectors
(`TauCeti.thomPairSingularHomologySuccIsoTwistedHomology`); with this sequence it is the mod `2`
Thom isomorphism with constant coefficients.

## Main results

* `IsCoveringMap.permutationLocalSystemTransfer_comp_augmentation_eq_zero`: for a double cover
  and `R` of characteristic two, the transfer followed by the augmentation is zero.
* `IsCoveringMap.shortExact_permutationLocalSystemTransfer_augmentation`: for a double cover and `R`
  of characteristic two, `0 ⟶ R ⟶ R[p] ⟶ R ⟶ 0` is short exact.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients and the local
  system of a covering space.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace IsCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} (hp : IsCoveringMap p) (R : Type u) [Ring R]
  (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))

variable {R} (hcard : ∀ b, Nat.card ↥(p ⁻¹' {b}) = 2)

variable [CharP R 2]

include hcard in
/-- **The transfer of a double cover is killed by the augmentation in characteristic two**: it
multiplies by the number of sheets, `2 = 0`. -/
@[reassoc (attr := simp)]
theorem permutationLocalSystemTransfer_comp_augmentation_eq_zero :
    hp.permutationLocalSystemTransfer R hfin ≫ hp.permutationLocalSystemAugmentation R = 0 := by
  refine NatTrans.ext (funext fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_))
  have := Fintype.ofFinite (p ⁻¹' {x.as})
  obtain ⟨e⟩ := (Nat.card_ne_zero.1 (hcard x.as ▸ two_ne_zero)).1
  obtain ⟨e', he'⟩ := ((Nat.card_eq_two_iff' e).1 (hcard x.as)).exists
  -- The fibre of the constant system is `R` only after unfolding the constant functor, so `simp`
  -- cannot evaluate the composite as stated; `change` states it as the augmentation of the
  -- transfer of `r`. For the same reason the coefficients of the transfer are rewritten with
  -- fully applied instances of `permutationLocalSystemTransfer_app_hom_apply_apply`.
  change ((hp.permutationLocalSystemAugmentation R).app x).hom
    (((hp.permutationLocalSystemTransfer R hfin).app x).hom r) = 0
  -- The transfer has coefficient `r` at both sheets, which the augmentation adds up to `2 r = 0`.
  refine (hp.permutationLocalSystemAugmentation_app_apply_eq_sum R x _).trans ?_
  simp only [Fintype.sum_eq_add_of_natCard_le_two (hcard x.as).le he',
    hp.permutationLocalSystemTransfer_app_hom_apply_apply R hfin x r e,
    hp.permutationLocalSystemTransfer_app_hom_apply_apply R hfin x r e']
  exact CharTwo.add_self_eq_zero (R := R) r

include hcard in
/-- **The transfer sequence of a double cover in characteristic two is short exact**: when every
fibre of `p` has exactly two points and `R` has characteristic two, the transfer followed by the
augmentation is a short exact sequence `0 ⟶ R ⟶ R[p] ⟶ R ⟶ 0` of local systems. -/
theorem shortExact_permutationLocalSystemTransfer_augmentation :
    (ShortComplex.mk (hp.permutationLocalSystemTransfer R hfin)
      (hp.permutationLocalSystemAugmentation R)
      (hp.permutationLocalSystemTransfer_comp_augmentation_eq_zero hfin hcard)).ShortExact := by
  refine ShortComplex.shortExact_of_forall_evaluation _ fun x ↦ ?_
  have := Fintype.ofFinite (p ⁻¹' {x.as})
  obtain ⟨e⟩ := (Nat.card_ne_zero.1 (hcard x.as ▸ two_ne_zero)).1
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 fun r s hrs ↦ ?_)
    ((ModuleCat.epi_iff_surjective _).2 fun r ↦ ⟨Finsupp.single e r, ?_⟩)
  · refine (ShortComplex.moduleCat_exact_iff _).2 fun (g : (p ⁻¹' {x.as}) →₀ R) hg ↦ ?_
    -- A formal sum of the two sheets whose coefficients add up to zero has equal coefficients,
    -- since `-1 = 1`, so it is the transfer of either coefficient.
    refine ⟨g e, Finsupp.ext fun e' ↦ ?_⟩
    refine (hp.permutationLocalSystemTransfer_app_hom_apply_apply R hfin x (g e) e').trans ?_
    obtain rfl | he' := eq_or_ne e' e
    · rfl
    have hg' : ∑ e'', g e'' = 0 :=
      (hp.permutationLocalSystemAugmentation_app_apply_eq_sum R x g).symm.trans hg
    rw [Fintype.sum_eq_add_of_natCard_le_two (hcard x.as).le he'.symm, add_eq_zero_iff_eq_neg,
      CharTwo.neg_eq] at hg'
    exact hg'
  · have h := congrArg (fun v : (p ⁻¹' {x.as}) →₀ R ↦ v e) hrs
    exact (hp.permutationLocalSystemTransfer_app_hom_apply_apply R hfin x r e).symm.trans
      (h.trans (hp.permutationLocalSystemTransfer_app_hom_apply_apply R hfin x s e))
  · exact (hp.permutationLocalSystemAugmentation_app_apply R x _).trans
      (Finsupp.sum_single_index rfl)

end IsCoveringMap
