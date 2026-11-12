/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.LengthFiltration
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Matched
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# The primitive idempotents of the matched subalgebra

The algebra `A(Z)` of a pointed matched circle, the matched subalgebra of the strands algebra
(`TauCeti.StrandsAlgebra.matchedSubalgebra`), has the idempotents `I(s)`
(`TauCeti.StrandsAlgebra.matchedIdem`), one for each set `s` of matched pairs. They are orthogonal
and sum to the unit (`TauCeti.StrandsAlgebra.completeOrthogonalIdempotents_matchedIdem`), and
this file shows that they are **primitive** idempotents of `A(Z)`, provided `1` is primitive in the
ground semiring, that is, the ground semiring is nontrivial and `1` is not the sum of two nonzero
orthogonal idempotents. So when `1` is primitive in the ground semiring (for instance over `𝔽₂`),
the `I(s)` form a complete family of orthogonal primitive idempotents of `A(Z)`; they span the
subalgebra of idempotents `I(Z)` of [LOT, §3.2], the ground ring of type `D` structures and type
`A` modules of bordered Floer theory. Precisely, `I(s)` is primitive exactly when `s` consists of
matched pairs and `1` is primitive in the ground semiring
(`TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`).

The proof uses the filtration of the strands algebra by the total length of the strands
(`TauCeti.StrandsAlgebra.lengthFiltration`), whose part `F_1`, the elements with no identity
diagram in their support, consists of nilpotent elements, and the multiplicativity of the
coefficient at an identity diagram `I(S)` (`TauCeti.StrandsAlgebra.repr_mul_apply_idOn`). An
element `f` of the corner ring `I(s) A(Z) I(s)` takes the same value `c` at every identity diagram
`I(S)` with `S` a set of points over `s`, because the coefficients of an element of the matched
subalgebra do not change when a horizontal strand moves within a matched pair, and it vanishes at
the other identity diagrams. So when `c = 0`, `f` lies in `F_1`; if `f` is moreover idempotent, it
is nilpotent and zero. In a decomposition `I(s) = f₁ + f₂` into orthogonal idempotents, the
coefficients at `I(S)` decompose `1` into orthogonal idempotents of the ground semiring, so one of
them vanishes, and with it the corresponding summand.

## Main results

* `TauCeti.StrandsAlgebra.eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero`: an idempotent
  of the corner ring of `I(s)` in the matched subalgebra whose coefficient at an identity diagram
  over `s` vanishes is zero.
* `TauCeti.StrandsAlgebra.eq_zero_or_eq_matchedIdem_of_isIdempotentElem`: over a ring in which `1`
  is primitive, the only idempotents of the corner ring of `I(s)` in the matched subalgebra are `0`
  and `I(s)`.
* `TauCeti.StrandsAlgebra.isPrimitiveIdempotent_matchedIdem_iff`: `I(s)` is a primitive idempotent
  of the matched subalgebra exactly when `s` is a set of matched pairs and `1` is primitive in the
  ground semiring.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  idempotents `I(s)` and the subalgebra of idempotents of `A(Z)`).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram

/-! ### The primitive idempotents of the matched subalgebra -/

variable {R α β : Type*} [CommSemiring R] [LinearOrder α] [Fintype α] [DecidableEq β]
  {M : α → β} {s : Finset β}

/-- **The idempotents of the corner ring of `I(s)` vanishing at an identity diagram.** An
idempotent `x` of the matched subalgebra with `I(s) x = x` whose coefficient vanishes at the
identity diagram of some set `S` of points over `s` is zero. -/
theorem eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) (hxx : IsIdempotentElem x) (hex : matchedIdem R M s * x = x)
    {S : Finset α} (hS : S ∈ matchedChoices M s) (h0 : (basis R α).repr x (idOn S) = 0) :
    x = 0 := by
  refine hxx.eq_zero_of_isNilpotent (isNilpotent_of_mem_lengthFiltration_one
    (mem_lengthFiltration_one_iff.2 fun T ↦ ?_))
  by_cases hT : T ∈ matchedChoices M s
  · rw [← repr_apply_idOn_eq hx hS hT, h0]
  · rw [← hex, repr_matchedIdem_mul_apply, source_idOn]
    simp [hT]

/-- **The idempotents of the corner ring of `I(s)`.** When `1` is primitive in the ground ring,
that is, the ground ring is nontrivial and has no idempotents besides `0` and `1`, the only
idempotents `x` of the matched subalgebra with `I(s) x = x I(s) = x` are `0` and `I(s)`. Unlike
the primitivity of `I(s)`, this needs a ring rather than a semiring. -/
theorem eq_zero_or_eq_matchedIdem_of_isIdempotentElem {R : Type*} [CommRing R]
    (h1 : IsPrimitiveIdempotent (1 : R)) {x : StrandsAlgebra R α}
    (hx : x ∈ matchedSubalgebra R M) (hxx : IsIdempotentElem x) (hex : matchedIdem R M s * x = x)
    (hxe : x * matchedIdem R M s = x) : x = 0 ∨ x = matchedIdem R M s := by
  by_cases hs : s ⊆ univ.image M
  swap
  · left
    rw [← hex, matchedIdem_eq_horizontalCompletion, horizontalCompletion_eq_zero_of_not_subset _ hs,
      zero_mul]
  obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
  have := h1.nontrivial
  -- The coefficient of `x` at `I(S)` is an idempotent of `R`, so it is `0` or `1`.
  have hc : IsIdempotentElem ((basis R α).repr x (idOn S)) := by
    rw [IsIdempotentElem, ← repr_mul_apply_idOn, hxx.eq]
  rcases isPrimitiveIdempotent_one_iff.1 h1 _ hc with h0 | h0
  · exact .inl (eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero hx hxx hex hS h0)
  -- Otherwise `I(s) - x` is an idempotent of the corner ring with coefficient `0` at `I(S)`.
  refine .inr (sub_eq_zero.1 (eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero
    (sub_mem (matchedIdem_mem_matchedSubalgebra M s) hx)
    (hxx.sub (isIdempotentElem_matchedIdem M s) hxe hex) ?_ hS ?_)).symm
  · rw [mul_sub, (isIdempotentElem_matchedIdem M s).eq, hex]
  · rw [map_sub, Finsupp.sub_apply, repr_matchedIdem_apply_idOn hS, h0, sub_self]

/-- **The idempotents `I(s)` are primitive.** The idempotent `I(s)` of the matched subalgebra is
primitive exactly when `s` is a set of matched pairs and `1` is primitive in the ground semiring,
that is, the ground semiring is nontrivial and `1` is not the sum of two nonzero orthogonal
idempotents, as for `𝔽₂`. -/
theorem isPrimitiveIdempotent_matchedIdem_iff :
    IsPrimitiveIdempotent
        (⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩ : matchedSubalgebra R M) ↔
      IsPrimitiveIdempotent (1 : R) ∧ s ⊆ univ.image M := by
  set e : matchedSubalgebra R M := ⟨matchedIdem R M s, matchedIdem_mem_matchedSubalgebra M s⟩
  have he : IsIdempotentElem e := Subtype.ext (isIdempotentElem_matchedIdem M s)
  constructor
  · intro hprim
    have hs : s ⊆ univ.image M := by
      by_contra hs
      exact hprim.ne_zero (Subtype.ext ((matchedIdem_eq_horizontalCompletion M s).trans
        (horizontalCompletion_eq_zero_of_not_subset _ hs)))
    obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
    have : Nontrivial R := by
      refine (subsingleton_or_nontrivial R).resolve_left fun _ ↦ hprim.ne_zero ?_
      exact Subtype.ext ((basis R α).repr.injective (Subsingleton.elim _ _))
    -- A decomposition `1 = a + b` gives the decomposition `I(s) = a I(s) + b I(s)`, and the
    -- coefficient of `r I(s)` at `I(S)` is `r`.
    have hcoeff (r : R) : (basis R α).repr ((r • e : matchedSubalgebra R M) : StrandsAlgebra R α)
        (idOn S) = r := by
      rw [NonUnitalSubalgebra.coe_smul, map_smul, Finsupp.smul_apply,
        repr_matchedIdem_apply_idOn hS, smul_eq_mul, mul_one]
    have hidem {r : R} (hr : IsIdempotentElem r) : IsIdempotentElem (r • e) := by
      rw [IsIdempotentElem, smul_mul_smul_comm, hr.eq, he.eq]
    have horth {r r' : R} (h : r * r' = 0) : (r • e) * (r' • e) = 0 := by
      rw [smul_mul_smul_comm, h, zero_smul]
    refine ⟨⟨.one, one_ne_zero, fun {a b} ha hb hab hba hsum ↦ ?_⟩, hs⟩
    refine (hprim.eq_zero_or_eq_zero_of_add (hidem ha) (hidem hb) (horth hab) (horth hba)
      (by rw [← add_smul, hsum, one_smul])).imp (fun h ↦ ?_) fun h ↦ ?_
    · rw [← hcoeff a, h]
      simp
    · rw [← hcoeff b, h]
      simp
  · rintro ⟨h1, hs⟩
    have := h1.nontrivial
    obtain ⟨S, hS⟩ := exists_mem_matchedChoices hs
    refine ⟨he, fun he0 ↦ ?_, fun {f₁ f₂} h₁ h₂ h₁₂ h₂₁ hsum ↦ ?_⟩
    · -- The ambient element of `e = 0` is `I(s) = 0`, but `I(s)` has coefficient `1` at `I(S)`.
      have h0 : matchedIdem R M s = 0 := by simpa [e] using congrArg Subtype.val he0
      simpa [h0] using repr_matchedIdem_apply_idOn (R := R) hS
    -- The coefficients at `I(S)` decompose `1` into orthogonal idempotents of `R`, so one of them
    -- vanishes, and then so does the corresponding summand.
    have hmul (f g : matchedSubalgebra R M) : (basis R α).repr (f * g : matchedSubalgebra R M)
        (idOn S) = (basis R α).repr f (idOn S) * (basis R α).repr g (idOn S) :=
      repr_mul_apply_idOn _ _ _
    have hcorner₁ : e * f₁ = f₁ := by rw [← hsum, add_mul, h₁.eq, h₂₁, add_zero]
    have hcorner₂ : e * f₂ = f₂ := by rw [← hsum, add_mul, h₁₂, h₂.eq, zero_add]
    have hone : (basis R α).repr f₁ (idOn S) + (basis R α).repr f₂ (idOn S) = 1 := by
      rw [← Finsupp.add_apply, ← map_add]
      exact (congrArg (fun y ↦ (basis R α).repr y (idOn S)) (congrArg Subtype.val hsum)).trans
        (repr_matchedIdem_apply_idOn hS)
    refine (h1.eq_zero_or_eq_zero_of_add (by rw [IsIdempotentElem, ← hmul, h₁.eq])
      (by rw [IsIdempotentElem, ← hmul, h₂.eq]) (by rw [← hmul, h₁₂]; simp)
      (by rw [← hmul, h₂₁]; simp) hone).imp (fun h ↦ ?_) fun h ↦ ?_
    · exact Subtype.ext (eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero f₁.2
        (congrArg Subtype.val h₁.eq) (congrArg Subtype.val hcorner₁) hS h)
    · exact Subtype.ext (eq_zero_of_isIdempotentElem_of_repr_apply_idOn_eq_zero f₂.2
        (congrArg Subtype.val h₂.eq) (congrArg Subtype.val hcorner₂) hS h)

end StrandsAlgebra

end TauCeti
