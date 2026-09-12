/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Left translation on a coset space

A group `G` acts on the quotient `G ⧸ H` by translation.  This file records the stabilizer of a
coset for that action, and, for the trivial subgroup, the compatibility of the identification
`QuotientGroup.quotientBot : G ⧸ ⊥ ≃* G` with translation.

The stabilizer of the coset `sH` is the conjugate subgroup `sHs⁻¹`
(`TauCeti.stabilizer_quotientGroup_mk`); this is Mathlib's `MulAction.stabilizer_quotient`, which
covers the trivial coset, transported along `MulAction.stabilizer_smul_eq_stabilizer_map_conj`.
Read on elements, it says that `g` fixes `sH` exactly when `s⁻¹ g s` lies in `H`
(`TauCeti.smul_quotientGroup_mk_eq_self_iff`), which is the form a fixed-coset count is checked
in.

The cosets of `⊥` in a group `G` are the elements of `G`, and Mathlib's
`QuotientGroup.quotientBot` is that identification.  The identification is equivariant for left
translation, and the only element of `G` fixing a coset of `⊥` is the identity.

For a finite group, a sum can also be split over the left or right cosets of a subgroup by using
`Quotient.out` as a transversal.

## Main statements

* `TauCeti.stabilizer_quotientGroup_mk`: the stabilizer of `sH` in `G` is `sHs⁻¹`.
* `TauCeti.smul_quotientGroup_mk_eq_self_iff`: `g` fixes the coset `sH` exactly when `s⁻¹ g s`
  lies in `H`.
* `TauCeti.quotientBot_equivariant`: `QuotientGroup.quotientBot` intertwines left translation on
  `G ⧸ ⊥` with left translation in `G`.
* `TauCeti.quotientBot_smul_eq_self_iff`: a group element fixes a coset of the trivial subgroup
  only when it is the identity.
* `TauCeti.sum_eq_sum_quotient_sum` and `TauCeti.sum_eq_sum_quotient_sum'`: split a finite sum
  along the left or right cosets of a subgroup.
-/

public section

open MulAction
open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- The stabilizer of the coset `sH`, for the translation action of `G` on `G ⧸ H`, is the
conjugate subgroup `sHs⁻¹`.  This is Mathlib's `MulAction.stabilizer_quotient` transported off the
trivial coset along `MulAction.stabilizer_smul_eq_stabilizer_map_conj`. -/
@[simp]
theorem stabilizer_quotientGroup_mk (H : Subgroup G) (s : G) :
    stabilizer G ((s : G ⧸ H)) = MulAut.conj s • H := by
  have hs : ((s : G) : G ⧸ H) = s • ((1 : G) : G ⧸ H) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_one]
  rw [hs, stabilizer_smul_eq_stabilizer_map_conj, stabilizer_quotient]
  -- `stabilizer_smul_eq_stabilizer_map_conj` leaves the conjugate as `H.map (MulAut.conj s)`,
  -- so the two descriptions are compared on elements rather than as subgroup maps.
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv]

/-- **A group element fixes the coset `sH` exactly when its conjugate `s⁻¹gs` lies in `H`.**  This
is `TauCeti.stabilizer_quotientGroup_mk` read on elements.

Not a `simp` lemma: `MulAction.Quotient.smul_coe` rewrites the translation inside the left-hand
side first, so the left-hand side is not in `simp`-normal form. -/
theorem smul_quotientGroup_mk_eq_self_iff (H : Subgroup G) (g s : G) :
    g • (s : G ⧸ H) = s ↔ s⁻¹ * g * s ∈ H := by
  rw [← mem_stabilizer_iff, stabilizer_quotientGroup_mk,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply]
  simp

/-- Left translation on the cosets of the trivial subgroup is left translation in the group.

Not a `simp` lemma: `simp` rewrites the left-hand side further, to
`QuotientGroup.quotientBot (↑g * ↑x)`. -/
theorem quotientBot_smul (g x : G) :
    QuotientGroup.quotientBot (g • (x : G ⧸ (⊥ : Subgroup G))) =
      g * QuotientGroup.quotientBot (x : G ⧸ (⊥ : Subgroup G)) :=
  rfl

/-- Identifying the cosets of the trivial subgroup with the group is equivariant for left
translation.

Not a `simp` lemma: `simp` rewrites `MulEquiv.toEquiv` away in the left-hand side. -/
theorem quotientBot_equivariant (g : G) (q : G ⧸ (⊥ : Subgroup G)) :
    QuotientGroup.quotientBot.toEquiv (g • q) =
      g • QuotientGroup.quotientBot.toEquiv q := by
  induction q using QuotientGroup.induction_on with
  | H x => exact quotientBot_smul g x

/-- A group element fixes a coset of the trivial subgroup exactly when it is the identity. -/
@[simp]
theorem quotientBot_smul_eq_self_iff (g : G) (q : G ⧸ (⊥ : Subgroup G)) :
    g • q = q ↔ g = 1 := by
  constructor
  · intro h
    have := congrArg QuotientGroup.quotientBot h
    induction q using QuotientGroup.induction_on with
    | H x => simpa [quotientBot_smul] using this
  · rintro rfl
    exact one_smul _ _

section Finite

variable {M : Type*} [AddCommMonoid M] [Fintype G] (H : Subgroup G)

/-- A subgroup of a finite group is a finite type. -/
noncomputable local instance fintypeSubgroup : Fintype H := Fintype.ofFinite H

/-- The quotient of a finite group by a subgroup is a finite type. -/
noncomputable local instance fintypeQuotientGroup : Fintype (G ⧸ H) :=
  H.fintypeQuotientOfFiniteIndex

/-- Every element of a finite group `G` is uniquely the product of the `Quotient.out`
representative of a left coset of `H` and an element of `H`. -/
theorem sum_eq_sum_quotient_sum (f : G → M) :
    ∑ g : G, f g = ∑ q : G ⧸ H, ∑ h : H, f (q.out * h) := by
  have hmk (q : G ⧸ H) (h : H) : ((q.out * h : G) : G ⧸ H) = q := by
    rw [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']
  have hbij : Function.Bijective fun p : (G ⧸ H) × H => (p.1.out : G) * (p.2 : G) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun g => ((g : G ⧸ H),
      ⟨(Quotient.out (g : G ⧸ H))⁻¹ * g, QuotientGroup.eq.mp (QuotientGroup.out_eq' _)⟩),
      fun p => ?_, fun g => ?_⟩
    · refine Prod.ext (hmk p.1 p.2) (Subtype.ext ?_)
      simp [hmk p.1 p.2]
    · simp
  have key := Fintype.sum_bijective _ hbij
    (fun p : (G ⧸ H) × H => f ((p.1.out : G) * (p.2 : G))) f fun _ => rfl
  rw [← key, Fintype.sum_prod_type]

/-- The right-coset form of `TauCeti.sum_eq_sum_quotient_sum`. -/
theorem sum_eq_sum_quotient_sum' (f : G → M) :
    ∑ g : G, f g = ∑ q : G ⧸ H, ∑ h : H, f ((h : G) * (q.out : G)⁻¹) := by
  have h1 : ∑ g : G, f g = ∑ g : G, f g⁻¹ :=
    Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => by simp
  rw [h1, sum_eq_sum_quotient_sum H fun g => f g⁻¹]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact (Fintype.sum_equiv (Equiv.inv H) (fun h => f ((h : G) * (q.out : G)⁻¹))
    (fun h => f ((q.out * (h : G))⁻¹)) fun _ => by simp).symm

end Finite

end TauCeti
