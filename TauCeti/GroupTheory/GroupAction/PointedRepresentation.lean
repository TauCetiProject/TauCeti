/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.PermutationRepresentation
public import TauCeti.GroupTheory.GroupAction.Transitive
public import TauCeti.Data.Fintype.Equiv
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Transitive permutation representations with a prescribed stabilizer

Fix a subgroup `H` of a group `G` and a point `x` of a set `X`. Transitive permutation
representations of `G` on `X` whose stabilizer at `x` is `H` correspond bijectively to
labellings `G ⧸ H ≃ X` taking the identity coset to `x`. The labelling sends the coset of
`g` to `ρ g x`; conversely a labelling transports the coset action to `X`.

When `X` has `n` points and `H` has index `n`, there are exactly `(n - 1)!` such
representations. Consequently a sum of nonnegative extended real weights depending only
on the stabilizer is `(n - 1)!` times the sum over subgroups of index `n`.

This pointed correspondence retains the labellings, rather than passing to conjugacy
classes. It is the counting ingredient for converting sums over labelled transitive
Galois actions into sums over subextensions of a separable closure.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the
  density of number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

open MulAction Equiv

namespace Subgroup

variable {G X : Type*} [Group G] (H : Subgroup G) (x : X)

private noncomputable def cosetLabel (ρ : G →* Perm X)
    (hρ : IsPretransitive ρ.range X)
    (hH : (stabilizer (Perm X) x).comap ρ = H) : G ⧸ H ≃ X :=
  (quotientEquivOfEq hH.symm).trans (ρ.quotientComapStabilizerEquiv hρ x)

private theorem cosetLabel_mk (ρ : G →* Perm X)
    (hρ : IsPretransitive ρ.range X)
    (hH : (stabilizer (Perm X) x).comap ρ = H) (g : G) :
    cosetLabel H x ρ hρ hH (QuotientGroup.mk g) = ρ g x := by
  rw [cosetLabel, Equiv.trans_apply, quotientEquivOfEq_mk,
    MonoidHom.quotientComapStabilizerEquiv_mk]

private theorem cosetLabel_smul (ρ : G →* Perm X)
    (hρ : IsPretransitive ρ.range X)
    (hH : (stabilizer (Perm X) x).comap ρ = H) (g : G) (q : G ⧸ H) :
    cosetLabel H x ρ hρ hH (g • q) = ρ g (cosetLabel H x ρ hρ hH q) := by
  induction q using QuotientGroup.induction_on with
  | H a => simp [cosetLabel_mk, Perm.mul_apply]

/-- Transitive representations with point stabilizer `H` are precisely the labellings of
the coset space of `H` that take the identity coset to the distinguished point. -/
noncomputable def transitiveRepresentationEquiv :
    {ρ : G →* Perm X // IsPretransitive ρ.range X ∧
      (stabilizer (Perm X) x).comap ρ = H} ≃
      {e : G ⧸ H ≃ X // e (QuotientGroup.mk 1) = x} where
  toFun ρ := ⟨cosetLabel H x ρ.1 ρ.2.1 ρ.2.2, by simp [cosetLabel_mk]⟩
  invFun e := ⟨e.1.permutationRepresentation,
    (isPretransitive_range_permutationRepresentation_iff e.1).2 inferInstance, by
      simpa only [e.2, stabilizer_quotient] using
        comap_stabilizer_permutationRepresentation (G := G) e.1 (QuotientGroup.mk 1)⟩
  left_inv ρ := by
    apply Subtype.ext
    exact permutationRepresentation_eq_of_map_smul _ (cosetLabel_smul H x ρ.1 ρ.2.1 ρ.2.2)
  right_inv e := by
    apply Subtype.ext
    ext q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [cosetLabel_mk, permutationRepresentation_apply]
      have hx : e.1.symm x = QuotientGroup.mk 1 := e.1.symm_apply_eq.2 e.2.symm
      simp [hx]

/-- The labelling attached to a representation sends the coset of `g` to `ρ g x`. -/
@[simp]
theorem transitiveRepresentationEquiv_apply_mk
    (ρ : {ρ : G →* Perm X // IsPretransitive ρ.range X ∧
      (stabilizer (Perm X) x).comap ρ = H}) (g : G) :
    (transitiveRepresentationEquiv H x ρ).1 (QuotientGroup.mk g) = ρ.1 g x :=
  cosetLabel_mk H x ρ.1 ρ.2.1 ρ.2.2 g

/-- The inverse correspondence transports the coset action along the labelling. -/
@[simp]
theorem transitiveRepresentationEquiv_symm_apply
    (e : {e : G ⧸ H ≃ X // e (QuotientGroup.mk 1) = x}) :
    ((transitiveRepresentationEquiv H x).symm e).1 = e.1.permutationRepresentation :=
  (rfl)

/-- A subgroup of index `n` is the stabilizer of a distinguished point in exactly
`(n - 1)!` transitive representations on any given set of size `n`. -/
theorem natCard_transitiveRepresentation [Finite X] (h : H.index = Nat.card X) :
    Nat.card {ρ : G →* Perm X // IsPretransitive ρ.range X ∧
      (stabilizer (Perm X) x).comap ρ = H} = (Nat.card X - 1).factorial := by
  have : Nonempty X := ⟨x⟩
  have : Finite (G ⧸ H) := H.index_ne_zero_iff_finite.1 (h ▸ Nat.card_pos.ne')
  rw [Nat.card_congr (transitiveRepresentationEquiv H x),
    Nat.card_equiv_apply_eq (QuotientGroup.mk 1) x h, ← h]
  rfl

end Subgroup

namespace TauCeti

open scoped ENNReal

/-- Sum a stabilizer-dependent weight over all transitive representations on a finite,
pointed set. Each subgroup of the appropriate index occurs `(n - 1)!` times. No finiteness
or topological assumption on the group is required, and the sums may be infinite. -/
theorem tsum_isPretransitive {G X : Type*} [Group G] [Finite X] (x : X)
    (w : Subgroup G → ℝ≥0∞) :
    (∑' ρ : {ρ : G →* Perm X // IsPretransitive ρ.range X},
      w ((stabilizer (Perm X) x).comap ρ.1)) =
      ((Nat.card X - 1).factorial : ℝ≥0∞) *
        ∑' H : {H : Subgroup G // H.index = Nat.card X}, w H.1 := by
  classical
  let S := {ρ : G →* Perm X // IsPretransitive ρ.range X}
  let stab : S → {H : Subgroup G // H.index = Nat.card X} := fun ρ ↦
    ⟨(stabilizer (Perm X) x).comap ρ.1,
      Nat.card_congr (ρ.1.quotientComapStabilizerEquiv ρ.2 x)⟩
  rw [← tsum_fiberwise (fun ρ : S ↦ w (stab ρ).1) stab, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro H
  let F := stab ⁻¹' {H}
  let C := {ρ : G →* Perm X // IsPretransitive ρ.range X ∧
    (stabilizer (Perm X) x).comap ρ = H.1}
  let e : F ≃ C :=
    { toFun := fun ρ ↦ ⟨ρ.1.1, ρ.1.2, congrArg Subtype.val ρ.2⟩
      invFun := fun ρ ↦ ⟨⟨ρ.1, ρ.2.1⟩, Subtype.ext ρ.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hc : Nat.card F = (Nat.card X - 1).factorial :=
    (Nat.card_congr e).trans (H.1.natCard_transitiveRepresentation x H.2)
  have : Finite F := Nat.finite_of_card_ne_zero (hc ▸ Nat.factorial_pos _).ne'
  let := Fintype.ofFinite F
  calc
    (∑' ρ : F, w (stab ρ.1).1) = ∑' _ : F, w H.1 :=
      tsum_congr fun ρ ↦ congrArg w (congrArg Subtype.val ρ.2)
    _ = ((Nat.card X - 1).factorial : ℝ≥0∞) * w H.1 := by
      simp [tsum_fintype, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hc]

end TauCeti
