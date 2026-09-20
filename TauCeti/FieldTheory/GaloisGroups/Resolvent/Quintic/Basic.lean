/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Spec
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification

/-!
# The quintic `F₂₀` resolvent specification and the resolvent sextic

Index five formal roots by `ℤ/5` and set

`Φ = ∑ a, xₐ² (xₐ₊₁ xₐ₋₁ + xₐ₊₂ xₐ₋₂)`,

the ten monomials `x₀²x₁x₄ + x₀²x₂x₃ + x₁²x₂x₀ + x₁²x₃x₄ + ⋯`. The stabilizer of `Φ` under
permutation of the variables is exactly the reference subgroup of the transitive-group label
`5T3`, the Frobenius group `F₂₀ = AGL(1, 5)` of affine maps of `ℤ/5`, of order twenty: the
affine maps `a ↦ a + 1` and `a ↦ 2a + 1` that generate it permute the summands of `Φ`. The
orbit of `Φ` under the whole symmetric group therefore has `120 / 20 = 6` elements, and the
orbit resolvent of a quintic is a sextic.

That the stabilizer is *exactly* `F₂₀`, and not merely contained in it, is what lets the
factorization of the sextic detect `F₂₀`: a mere containment would leave the orbit smaller than
the coset space `S₅ / F₂₀`, and the resolvent would no longer separate the cosets.

`TauCeti.resolventSextic f` is the specialization of this specification at a quintic `f` over
`ℤ`. Integrality is a theorem about `ResolventSpec.specialize` and not an extra hypothesis, so
the sextic is a monic integral polynomial of degree six; the sextic over `ℚ` is its image under
`Polynomial.map`, by `TauCeti.ResolventSpec.specialize_map`. Being monic and integral, it has
only integral rational roots, which is what makes "the Galois image lies in a conjugate of
`F₂₀`" a finite condition on integers for an irreducible quintic.

## Main definitions

* `TauCeti.quinticF20Invariant`: the invariant `Φ`.
* `TauCeti.quinticF20Spec`: the resolvent specification of `Φ`, for the subgroup `5T3`.
* `TauCeti.resolventSextic`: the resolvent sextic of an integral quintic.

## Main results

* `TauCeti.rename_quinticF20Invariant_eq_self_iff`: the stabilizer of the invariant is exactly
  the reference subgroup of `5T3`.
* `TauCeti.card_renameOrbit_quinticF20Invariant`: its orbit has six elements.
* `TauCeti.natDegree_resolventSextic`: the resolvent sextic has degree six.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), §1. The
  invariant is his, with his `x₁, …, x₅` read as `x₀, …, x₄`.
-/

public section

open Equiv Equiv.Perm Polynomial

namespace TauCeti

open MvPolynomial (renameOrbit renameStabilizer)

/-- Dummit's `F₂₀`-invariant of five formal roots indexed by `ℤ/5`:
`∑ a, xₐ² (xₐ₊₁ xₐ₋₁ + xₐ₊₂ xₐ₋₂)`, a sum of ten monomials of shape `xₐ² x_b x_c`. -/
noncomputable def quinticF20Invariant : MvPolynomial (Fin 5) ℤ :=
  ∑ a : Fin 5, MvPolynomial.X a ^ 2 *
    (MvPolynomial.X (a + 1) * MvPolynomial.X (a - 1) +
      MvPolynomial.X (a + 2) * MvPolynomial.X (a - 2))

/-- The defining formula of the quintic `F₂₀`-invariant. -/
theorem quinticF20Invariant_def :
    quinticF20Invariant =
      ∑ a : Fin 5, MvPolynomial.X a ^ 2 *
        (MvPolynomial.X (a + 1) * MvPolynomial.X (a - 1) +
          MvPolynomial.X (a + 2) * MvPolynomial.X (a - 2)) :=
  (rfl)

/-- Renaming the variables of the `F₂₀`-invariant along `σ`. -/
theorem rename_quinticF20Invariant (σ : Perm (Fin 5)) :
    MvPolynomial.rename (⇑σ) quinticF20Invariant =
      ∑ a : Fin 5, MvPolynomial.X (σ a) ^ 2 *
        (MvPolynomial.X (σ (a + 1)) * MvPolynomial.X (σ (a - 1)) +
          MvPolynomial.X (σ (a + 2)) * MvPolynomial.X (σ (a - 2))) := by
  simp [quinticF20Invariant]

/-- The translation `a ↦ a + 1` fixes the `F₂₀`-invariant: it reindexes the sum. -/
private theorem rename_finRotate_quinticF20Invariant :
    MvPolynomial.rename (⇑(finRotate 5)) quinticF20Invariant = quinticF20Invariant := by
  have e1 : ∀ a : Fin 5, a - 1 + 1 = a + 1 - 1 := by decide
  have e2 : ∀ a : Fin 5, a + 2 + 1 = a + 1 + 2 := by decide
  have e3 : ∀ a : Fin 5, a - 2 + 1 = a + 1 - 2 := by decide
  rw [rename_quinticF20Invariant, quinticF20Invariant]
  refine Fintype.sum_bijective (fun a : Fin 5 => a + 1) (by decide) _ _ fun a => ?_
  simp only [finRotate_apply, e1, e2, e3]

/-- The affine map `a ↦ 2 a + 1`, that is the four-cycle `[0, 1, 3, 2].formPerm`, fixes the
`F₂₀`-invariant: doubling exchanges the two products inside each summand. -/
private theorem rename_formPerm_quinticF20Invariant :
    MvPolynomial.rename (⇑(([0, 1, 3, 2] : List (Fin 5)).formPerm)) quinticF20Invariant =
      quinticF20Invariant := by
  have hs : ∀ a : Fin 5, ([0, 1, 3, 2] : List (Fin 5)).formPerm a = 2 * a + 1 := by decide
  have e1 : ∀ a : Fin 5, 2 * (a + 1) + 1 = 2 * a + 1 + 2 := by decide
  have e2 : ∀ a : Fin 5, 2 * (a - 1) + 1 = 2 * a + 1 - 2 := by decide
  have e3 : ∀ a : Fin 5, 2 * (a + 2) + 1 = 2 * a + 1 - 1 := by decide
  have e4 : ∀ a : Fin 5, 2 * (a - 2) + 1 = 2 * a + 1 + 1 := by decide
  rw [rename_quinticF20Invariant, quinticF20Invariant]
  refine Fintype.sum_bijective (fun a : Fin 5 => 2 * a + 1) (by decide) _ _ fun a => ?_
  simp only [hs, e1, e2, e3, e4]
  ring

/-- The reference subgroup of `5T3` fixes the `F₂₀`-invariant. -/
private theorem referenceSubgroup_five_two_le_renameStabilizer :
    referenceSubgroup 5 ⟨2, by simp⟩ ≤ renameStabilizer quinticF20Invariant := by
  rw [referenceSubgroup_five_two, Subgroup.closure_le]
  rintro τ (rfl | rfl)
  · exact MvPolynomial.mem_renameStabilizer.2 rename_finRotate_quinticF20Invariant
  · exact MvPolynomial.mem_renameStabilizer.2 rename_formPerm_quinticF20Invariant

/-- The transposition of the first two variables moves the `F₂₀`-invariant: at the point
`(1, 2, 3, 5, 7)` the invariant takes the value `1448`, and the transposed invariant `1512`. -/
private theorem rename_swap_quinticF20Invariant_ne :
    MvPolynomial.rename (⇑(swap (0 : Fin 5) 1)) quinticF20Invariant ≠ quinticF20Invariant := by
  intro h
  have h2 := congrArg (MvPolynomial.eval ![1, 2, 3, 5, 7]) h
  rw [rename_quinticF20Invariant, quinticF20Invariant] at h2
  simp only [map_sum, map_mul, map_add, map_pow, MvPolynomial.eval_X] at h2
  revert h2
  decide

/-- **The exact stabilizer.** A permutation fixes the `F₂₀`-invariant if and only if it lies in
the reference subgroup of `5T3`, the Frobenius group of affine maps of `ℤ/5`. -/
theorem rename_quinticF20Invariant_eq_self_iff (σ : Perm (Fin 5)) :
    MvPolynomial.rename (⇑σ) quinticF20Invariant = quinticF20Invariant ↔
      σ ∈ referenceSubgroup 5 ⟨2, by simp⟩ := by
  have hle := referenceSubgroup_five_two_le_renameStabilizer
  have hstab : renameStabilizer quinticF20Invariant = referenceSubgroup 5 ⟨2, by simp⟩ := by
    -- The stabilizer contains the transitive group `5T3`, so it is itself transitive and its
    -- order is one of `5`, `10`, `20`, `60`, `120`. The first two are not multiples of the
    -- order `20` of `5T3`; order `60` is the alternating group, which does not contain the odd
    -- permutations of `5T3`; and order `120` is the whole group, which does not fix the
    -- invariant. So the order is `20` and the containment is an equality.
    have : MulAction.IsPretransitive (renameStabilizer quinticF20Invariant) (Fin 5) := by
      constructor
      intro x y
      obtain ⟨g, hg⟩ := (isPretransitive_referenceSubgroup 5 ⟨2, by simp⟩).exists_smul_eq x y
      exact ⟨⟨(g : Perm (Fin 5)), hle g.2⟩, hg⟩
    have hmem := natCard_mem_of_natCard_eq_five_of_isPretransitive (α := Fin 5) (by simp)
      (renameStabilizer quinticF20Invariant)
    have hmul := (renameStabilizer quinticF20Invariant).index_mul_card
    rw [Nat.card_perm, Nat.card_fin] at hmul
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [natCard_referenceSubgroup_five_two] at hdvd
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [natCard_referenceSubgroup_five_two]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    simp only [Nat.factorial] at hmul
    rcases hmem with h | h | h | h | h
    · rw [h] at hdvd; norm_num at hdvd
    · rw [h] at hdvd; norm_num at hdvd
    · omega
    · rw [h] at hmul
      have halt : renameStabilizer quinticF20Invariant = alternatingGroup (Fin 5) :=
        eq_alternatingGroup_of_index_eq_two (by omega)
      exact absurd (halt ▸ hle) not_referenceSubgroup_five_two_le_alternatingGroup
    · rw [h] at hmul
      have htop : renameStabilizer quinticF20Invariant = ⊤ :=
        Subgroup.index_eq_one.1 (by omega)
      exact absurd (MvPolynomial.mem_renameStabilizer.1
        (htop ▸ Subgroup.mem_top (swap (0 : Fin 5) 1))) rename_swap_quinticF20Invariant_ne
  rw [← MvPolynomial.mem_renameStabilizer, hstab]

/-- **The quintic resolvent specification**: Dummit's `F₂₀`-invariant, whose stabilizer is
exactly the reference subgroup of `5T3`. -/
noncomputable def quinticF20Spec : ResolventSpec 5 :=
  ResolventSpec.mk' (referenceSubgroup 5 ⟨2, by simp⟩) quinticF20Invariant
    rename_quinticF20Invariant_eq_self_iff

@[simp]
theorem quinticF20Spec_H : quinticF20Spec.H = referenceSubgroup 5 ⟨2, by simp⟩ :=
  ResolventSpec.mk'_H _ _ _

@[simp]
theorem quinticF20Spec_Φ : quinticF20Spec.Φ = quinticF20Invariant :=
  ResolventSpec.mk'_Φ _ _ _

/-- **The orbit of the `F₂₀`-invariant has six elements**, so its resolvent is a sextic. -/
theorem card_renameOrbit_quinticF20Invariant : (renameOrbit quinticF20Invariant).card = 6 := by
  rw [← quinticF20Spec_Φ, ResolventSpec.card_renameOrbit, quinticF20Spec_H,
    index_referenceSubgroup_five_two]

/-- **The resolvent sextic** of an integral quintic `f`: the specialization of the quintic
`F₂₀` specification at `f`, over `ℤ`. It is monic of degree six
(`TauCeti.natDegree_resolventSextic`), and the resolvent sextic over any other coefficient ring
is its image under `Polynomial.map`, by `TauCeti.ResolventSpec.specialize_map`. -/
noncomputable def resolventSextic (f : ℤ[X]) : ℤ[X] :=
  quinticF20Spec.specialize ℤ f

/-- The defining formula of the resolvent sextic. -/
theorem resolventSextic_def (f : ℤ[X]) : resolventSextic f = quinticF20Spec.specialize ℤ f :=
  (rfl)

/-- The resolvent sextic is monic. -/
theorem monic_resolventSextic (f : ℤ[X]) : (resolventSextic f).Monic :=
  quinticF20Spec.monic_specialize ℤ f

/-- The resolvent sextic has degree six, for every `f`: it is the image of a monic polynomial of
degree `[S₅ : F₂₀] = 6`, so a specialization never lowers its degree. -/
@[simp]
theorem natDegree_resolventSextic (f : ℤ[X]) : (resolventSextic f).natDegree = 6 := by
  rw [resolventSextic_def, ResolventSpec.natDegree_specialize, quinticF20Spec_H,
    index_referenceSubgroup_five_two]

end TauCeti
