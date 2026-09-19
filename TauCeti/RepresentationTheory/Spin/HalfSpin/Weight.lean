/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
public import TauCeti.RepresentationTheory.Spin.Weight
-- Private: `Module.Basis.exteriorAlgebra_mem_evenOdd_iff` is used only inside proofs, and
-- `HalfSpin/Basic.lean` imports this module privately too, so it is not available transitively.
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

/-!
# The weights of the half-spin summands

`TauCeti/RepresentationTheory/Spin/Weight.lean` diagonalizes the spinor module `S = ⋀·W` of a
polarization under the commuting diagonal bivectors `H i`: the weight spaces are the lines spanned
by the exterior basis vectors, the weight of the vector indexed by a finite set `s` of coordinates
being the sign vector `spinWeight K s = ½(±1, …, ±1)` whose `+` signs are the elements of `s`.
`TauCeti/RepresentationTheory/Spin/HalfSpin/Basic.lean` splits the same module along exterior
parity, as `S⁺ ⊕ S⁻`.

This file matches the two decompositions. Each is indexed by the exterior basis, so they are
compatible in the strongest sense: **every weight line lies in one of the two half-spin summands**,
and which one is decided by the parity of the number of `+` signs of its weight. So the weights of
`S⁺` are the sign vectors with an even number of `+` signs, those of `S⁻` the ones with an odd
number, and `S⁺` and `S⁻` are the sums of the corresponding weight lines.

The count that comes with this is the one a half-spin representation should have. On `l`
coordinates there are `2 ^ l` sign vectors (`TauCeti.ncard_range_spinWeight`), split evenly by
parity, so each summand carries `2 ^ (l - 1)` weights — exactly its dimension, computed
independently in `TauCeti/RepresentationTheory/Spin/Dimension.lean` by a Clifford-algebraic
argument.

Nothing here needs a field, a nondegeneracy hypothesis, a finite dimension, or a polarization
without a line summand: the parity grading of `⋀·W` and the diagonalization are both available
over the commutative ring the polarization data lives over. Even nontriviality of the ring is
needed only where a parity is *read off* a basis vector, that vector having to be nonzero for its
parity to be well defined; the inclusions and the identification of the two summands hold over any
commutative ring.

As in `TauCeti/RepresentationTheory/Spin/Weight.lean`, "weight" means a tuple of simultaneous
eigenvalues for the family `H`, no Cartan subalgebra being exhibited; and no weight is called
highest, since no ordering of the coordinates is used to single out a Borel. What the parity
statements do supply for the type-`Dₗ` fork is that the two candidate highest-weight vectors of
`TauCeti/RepresentationTheory/Spin/Polarization/TypeD/ForkWeights.lean` — the basis vector with
every coordinate occupied and the one obtained from it by erasing a coordinate — lie in *different*
half-spin summands, which is `TauCeti.basis_univ_mem_spinPlus_iff_basis_univ_erase_mem_spinMinus`.

## Main results

* `TauCeti.basis_mem_spinPlus_iff` and `TauCeti.basis_mem_spinMinus_iff`: **an exterior basis
  vector lies in the half-spin summand selected by the parity of its number of coordinates.**
* `TauCeti.spinWeightSpace_le_spinPlus_iff` and `TauCeti.spinWeightSpace_le_spinMinus_iff`: the
  same statement for the weight line the basis vector spans.
* `TauCeti.iSup_spinWeightSpace_even_eq_spinPlus` and
  `TauCeti.iSup_spinWeightSpace_odd_eq_spinMinus`: **each half-spin summand is the sum of the
  weight lines of its parity**, with `TauCeti.iSup_spinWeightSpace_even_le_spinPlus` and
  `TauCeti.iSup_spinWeightSpace_odd_le_spinMinus` the easy inclusions.
* `TauCeti.setOf_spinWeightSpace_le_spinPlus` and `TauCeti.setOf_spinWeightSpace_le_spinMinus`:
  **the weights of a half-spin summand are the sign vectors of the matching parity**, and
  `TauCeti.ncard_spinWeightSpace_le_spinPlus` and `TauCeti.ncard_spinWeightSpace_le_spinMinus`
  count them, `2 ^ (l - 1)` each.
* `TauCeti.basis_univ_mem_spinPlus_iff_basis_univ_erase_mem_spinMinus`: **the two type-`Dₗ` fork
  vectors lie in different half-spin summands.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.2: the half-spin
  representations `S⁺`, `S⁻` of `𝔰𝔬(2l)` and their weights, the sign vectors of even and of odd
  parity.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

open CliffordAlgebra

namespace TauCeti

universe u v w

section Parity

variable {K : Type u} [CommRing K] [Nontrivial K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [LinearOrder ι] (b : Module.Basis ι K P.W)

/-- **An exterior basis vector lies in `S⁺` exactly when it has an even number of coordinates.**
Its weight is then a sign vector with an even number of `+` signs. -/
theorem basis_mem_spinPlus_iff (s : Finset ι) :
    b.ExteriorAlgebra s ∈ spinPlus Q P ↔ Even s.card := by
  rw [mem_spinPlus, b.exteriorAlgebra_mem_evenOdd_iff s 0, ZMod.natCast_eq_zero_iff_even]

/-- **An exterior basis vector lies in `S⁻` exactly when it has an odd number of coordinates.**
Its weight is then a sign vector with an odd number of `+` signs. -/
theorem basis_mem_spinMinus_iff (s : Finset ι) :
    b.ExteriorAlgebra s ∈ spinMinus Q P ↔ Odd s.card := by
  rw [mem_spinMinus, b.exteriorAlgebra_mem_evenOdd_iff s 1, ZMod.natCast_eq_one_iff_odd]

omit [Nontrivial K] in
/-- **The two type-`Dₗ` fork vectors lie in different half-spin summands.** The vector with every
coordinate occupied and the vector obtained from it by erasing one coordinate differ in parity, so
whenever the first is even the second is odd and conversely. These are the two vectors that
`TauCeti/RepresentationTheory/Spin/Polarization/TypeD/ForkWeights.lean` shows to be annihilated by
every positive simple generator, with the fork fundamental weights. -/
theorem basis_univ_mem_spinPlus_iff_basis_univ_erase_mem_spinMinus [Fintype ι] (i : ι) :
    b.ExteriorAlgebra Finset.univ ∈ spinPlus Q P ↔
      b.ExteriorAlgebra (Finset.univ.erase i) ∈ spinMinus Q P := by
  rcases subsingleton_or_nontrivial K with _ | _
  -- Over a trivial ring every spinor is `0`, so both sides hold.
  · have : Subsingleton (ExteriorAlgebra K P.W) := Module.subsingleton K _
    have hmem : ∀ (x : ExteriorAlgebra K P.W) (N : Submodule K (ExteriorAlgebra K P.W)), x ∈ N :=
      fun x N => by rw [Subsingleton.elim x 0]; exact N.zero_mem
    exact ⟨fun _ => hmem _ _, fun _ => hmem _ _⟩
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [basis_mem_spinPlus_iff, basis_mem_spinMinus_iff,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Nat.even_iff, Nat.odd_iff]
  omega

end Parity

section WeightSpace

variable {K : Type u} [CommRing K] [Invertible (2 : K)] [Nontrivial K] {V : Type v}
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [LinearOrder ι] (b : Module.Basis ι K P.W)

/-- **A weight line lies in `S⁺` exactly when its sign vector has an even number of `+` signs.**
The weight space is the line spanned by an exterior basis vector, so this is
`TauCeti.basis_mem_spinPlus_iff` read on that line. -/
theorem spinWeightSpace_le_spinPlus_iff (s : Finset ι) :
    spinWeightSpace Q P b (spinWeight K s) ≤ spinPlus Q P ↔ Even s.card := by
  rw [spinWeightSpace_spinWeight, Submodule.span_singleton_le_iff_mem, basis_mem_spinPlus_iff]

/-- **A weight line lies in `S⁻` exactly when its sign vector has an odd number of `+` signs.** -/
theorem spinWeightSpace_le_spinMinus_iff (s : Finset ι) :
    spinWeightSpace Q P b (spinWeight K s) ≤ spinMinus Q P ↔ Odd s.card := by
  rw [spinWeightSpace_spinWeight, Submodule.span_singleton_le_iff_mem, basis_mem_spinMinus_iff]

omit [Nontrivial K] in
/-- Splitting the exhaustion `TauCeti.iSup_spinWeightSpace_eq_top` by the parity of the index set:
the two parities of weight line already span the whole spinor module. -/
private theorem sup_iSup_spinWeightSpace_parity_eq_top :
    (⨆ (s : Finset ι) (_ : Even s.card), spinWeightSpace Q P b (spinWeight K s)) ⊔
        ⨆ (s : Finset ι) (_ : Odd s.card), spinWeightSpace Q P b (spinWeight K s) = ⊤ := by
  rw [eq_top_iff, ← iSup_spinWeightSpace_eq_top P b]
  refine iSup_le fun s => ?_
  rcases Nat.even_or_odd s.card with hs | hs
  · exact le_sup_of_le_left (le_iSup_of_le s (le_iSup_of_le hs le_rfl))
  · exact le_sup_of_le_right (le_iSup_of_le s (le_iSup_of_le hs le_rfl))

omit [Nontrivial K] in
/-- The sum of the weight lines of even parity is contained in `S⁺`. -/
theorem iSup_spinWeightSpace_even_le_spinPlus :
    (⨆ (s : Finset ι) (_ : Even s.card), spinWeightSpace Q P b (spinWeight K s)) ≤
      spinPlus Q P := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [spinWeightSpace_spinWeight, Submodule.span_singleton_le_iff_mem, mem_spinPlus]
  have hcard := b.exteriorAlgebra_mem_evenOdd_card s
  rwa [ZMod.natCast_eq_zero_iff_even.mpr hs] at hcard

omit [Nontrivial K] in
/-- The sum of the weight lines of odd parity is contained in `S⁻`. -/
theorem iSup_spinWeightSpace_odd_le_spinMinus :
    (⨆ (s : Finset ι) (_ : Odd s.card), spinWeightSpace Q P b (spinWeight K s)) ≤
      spinMinus Q P := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [spinWeightSpace_spinWeight, Submodule.span_singleton_le_iff_mem, mem_spinMinus]
  have hcard := b.exteriorAlgebra_mem_evenOdd_card s
  rwa [ZMod.natCast_eq_one_iff_odd.mpr hs] at hcard

omit [Nontrivial K] in
/-- **`S⁺` is the sum of the weight lines of even parity.** -/
theorem iSup_spinWeightSpace_even_eq_spinPlus :
    (⨆ (s : Finset ι) (_ : Even s.card), spinWeightSpace Q P b (spinWeight K s)) =
      spinPlus Q P := by
  refine eq_of_le_of_inf_le_of_le_sup
    (z := ⨆ (s : Finset ι) (_ : Odd s.card), spinWeightSpace Q P b (spinWeight K s))
    (iSup_spinWeightSpace_even_le_spinPlus P b) ?_ ?_
  · refine le_trans (le_trans (inf_le_inf le_rfl (iSup_spinWeightSpace_odd_le_spinMinus P b))
      (isCompl_spinPlus_spinMinus P).inf_eq_bot.le) bot_le
  · rw [sup_iSup_spinWeightSpace_parity_eq_top P b]
    exact le_top

omit [Nontrivial K] in
/-- **`S⁻` is the sum of the weight lines of odd parity**, the other half of
`TauCeti.iSup_spinWeightSpace_even_eq_spinPlus`. -/
theorem iSup_spinWeightSpace_odd_eq_spinMinus :
    (⨆ (s : Finset ι) (_ : Odd s.card), spinWeightSpace Q P b (spinWeight K s)) =
      spinMinus Q P := by
  refine eq_of_le_of_inf_le_of_le_sup
    (z := ⨆ (s : Finset ι) (_ : Even s.card), spinWeightSpace Q P b (spinWeight K s))
    (iSup_spinWeightSpace_odd_le_spinMinus P b) ?_ ?_
  · refine le_trans (le_trans (inf_le_inf le_rfl (iSup_spinWeightSpace_even_le_spinPlus P b))
      (isCompl_spinPlus_spinMinus P).symm.inf_eq_bot.le) bot_le
  · rw [sup_comm, sup_iSup_spinWeightSpace_parity_eq_top P b]
    exact le_top

variable [NoZeroDivisors K]

/-- **The weights of `S⁺` are exactly the sign vectors with an even number of `+` signs.** A tuple
of eigenvalues counts as a weight of `S⁺` when its weight space is nonzero and contained in `S⁺`;
the nonvanishing clause is what rules out the tuples that occur nowhere, whose weight space is `⊥`
and so vacuously contained in both summands. -/
theorem setOf_spinWeightSpace_le_spinPlus :
    {χ : ι → K | spinWeightSpace Q P b χ ≠ ⊥ ∧ spinWeightSpace Q P b χ ≤ spinPlus Q P} =
      spinWeight K '' {s : Finset ι | Even s.card} := by
  ext χ
  constructor
  · rintro ⟨hne, hle⟩
    obtain ⟨s, rfl⟩ := (spinWeightSpace_ne_bot_iff P b).mp hne
    exact ⟨s, (spinWeightSpace_le_spinPlus_iff P b s).mp hle, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(spinWeightSpace_ne_bot_iff P b).mpr ⟨s, rfl⟩,
      (spinWeightSpace_le_spinPlus_iff P b s).mpr hs⟩

/-- **The weights of `S⁻` are exactly the sign vectors with an odd number of `+` signs.** -/
theorem setOf_spinWeightSpace_le_spinMinus :
    {χ : ι → K | spinWeightSpace Q P b χ ≠ ⊥ ∧ spinWeightSpace Q P b χ ≤ spinMinus Q P} =
      spinWeight K '' {s : Finset ι | Odd s.card} := by
  ext χ
  constructor
  · rintro ⟨hne, hle⟩
    obtain ⟨s, rfl⟩ := (spinWeightSpace_ne_bot_iff P b).mp hne
    exact ⟨s, (spinWeightSpace_le_spinMinus_iff P b s).mp hle, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(spinWeightSpace_ne_bot_iff P b).mpr ⟨s, rfl⟩,
      (spinWeightSpace_le_spinMinus_iff P b s).mpr hs⟩

/-- **`S⁺` carries `2 ^ (l - 1)` weights** on `l` coordinates: half the `2 ^ l` weights of the
spinor module. Over a field this is the dimension `TauCeti.finrank_spinPlus` of `S⁺`, as it must
be, each weight space being a line. -/
theorem ncard_spinWeightSpace_le_spinPlus [Finite ι] [Nonempty ι] :
    {χ : ι → K | spinWeightSpace Q P b χ ≠ ⊥ ∧
        spinWeightSpace Q P b χ ≤ spinPlus Q P}.ncard = 2 ^ (Nat.card ι - 1) := by
  rw [setOf_spinWeightSpace_le_spinPlus P b, ncard_spinWeight_image_even]

/-- **`S⁻` carries `2 ^ (l - 1)` weights**, matching `TauCeti.finrank_spinMinus` over a field. -/
theorem ncard_spinWeightSpace_le_spinMinus [Finite ι] [Nonempty ι] :
    {χ : ι → K | spinWeightSpace Q P b χ ≠ ⊥ ∧
        spinWeightSpace Q P b χ ≤ spinMinus Q P}.ncard = 2 ^ (Nat.card ι - 1) := by
  rw [setOf_spinWeightSpace_le_spinMinus P b, ncard_spinWeight_image_odd]

end WeightSpace

end TauCeti
