/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear independence over a fixed field

Let `σ` be an endomorphism of a field `E` whose fixed elements all come from a field `F`
(for instance the fixed field of a field automorphism). Suppose a family `v` in an `E`-module
`M` lies in the equalizer of a `σ`-semilinear map `P : M → N` and an injective `E`-linear map
`Q : M → N`. Then `v` is linearly independent over `E` as soon as it is linearly independent
over `F`: `LinearIndependent.extend_scalars_of_semilinear_eq`.

Taking `P` to be a `σ`-semilinear endomorphism of `M` and `Q` the identity recovers the
injectivity half of Galois descent for vector spaces (Speiser's lemma): vectors fixed by `P`
that are linearly independent over `F` stay linearly independent over `E`. The equalizer
form also covers endomorphisms commuting with a semilinear map `φ`, taking `P g = φ ∘ g` and
`Q g = g ∘ φ`, where only surjectivity of `φ` is needed.

The proof is the minimal-relation argument of Artin's proof of Dedekind's independence of
characters (Mathlib's `linearIndependent_monoidHom`), also used by Mathlib for
`FixedPoints.linearIndependent_smul_of_linearIndependent`.
-/

public section

open Finsupp

/-- **Descent of linear independence.** Let `σ` be an endomorphism of `E` whose fixed elements lie
in `F`, `P` a `σ`-semilinear map and `Q` an injective `E`-linear map with the same domain and
codomain. A family on which `P` and `Q` agree is linearly independent over `E` as soon as it is
linearly independent over `F`. -/
theorem LinearIndependent.extend_scalars_of_semilinear_eq {F E M N ι : Type*} [CommRing F]
    [Field E] [Algebra F E] [AddCommGroup M] [Module F M] [Module E M] [IsScalarTower F E M]
    [AddCommGroup N] [Module E N] {σ : E →+* E}
    (hσ : ∀ x, σ x = x → x ∈ (algebraMap F E).range) (P : M →ₛₗ[σ] N) (Q : M →ₗ[E] N)
    (hQ : Function.Injective Q) {v : ι → M} (hPQ : ∀ i, P (v i) = Q (v i))
    (hv : LinearIndependent F v) : LinearIndependent E v := by
  classical
  -- Applying `σ` to the coefficients of a relation gives a relation.
  have hrel (l : ι →₀ E) (hl : linearCombination E v l = 0) :
      linearCombination E v (l.mapRange σ (map_zero σ)) = 0 := by
    apply hQ
    simpa [apply_linearCombinationₛₗ, apply_linearCombination, Function.comp_def, hPQ] using
      congrArg P hl
  -- A nonzero relation of minimal support, normalized to have a coefficient `1`, is fixed by
  -- `σ`; so it is a relation over `F`.
  rw [linearIndependent_iff]
  intro l
  induction hn : l.support.card using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  intro hl
  by_contra hne
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
  set l' := (l i)⁻¹ • l
  have hl' : linearCombination E v l' = 0 := by simp [l', hl]
  have hl'i : l' i = 1 := by simp [l', inv_mul_cancel₀ hi]
  set d := l'.mapRange σ (map_zero σ) - l'
  have hd : linearCombination E v d = 0 := by simp [d, hrel l' hl', hl']
  have hsub : d.support ⊂ l.support := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simpa using hi, by simp [d, hl'i]⟩
    · intro j hj
      rw [Finsupp.mem_support_iff] at hj ⊢
      intro hlj
      simp [d, l', hlj] at hj
  have hd0 : d = 0 := ih _ (hn ▸ Finset.card_lt_card hsub) d rfl hd
  have hfix (j : ι) : σ (l' j) = l' j := by
    simpa [d, sub_eq_zero] using DFunLike.congr_fun hd0 j
  choose a ha using fun j ↦ hσ _ (hfix j)
  have ha0 : a i = 0 := by
    refine linearIndependent_iff'.1 hv l'.support a ?_ i (by simp [hl'i])
    rw [← hl', linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [← ha j, algebraMap_smul]
  simpa [ha0, hl'i] using ha i
