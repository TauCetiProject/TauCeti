/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.WeightSpace
import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.Rep.DirectSum.AsModule
import TauCeti.RepresentationTheory.Rep.DirectSum.Character
import TauCeti.RepresentationTheory.Semisimple
import TauCeti.RepresentationTheory.Semisimplification
import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# Cancellation of linear characters from semisimple representations

Let `ρ₀` and `ρ₁` be finite-dimensional representations of a monoid `G` over a field `k` of
characteristic zero, with `ρ₀` semisimple, and let `ψ₀ i` and `ψ₁ j` be two finite families of
linear characters `G →* kˣ` with no member in common. If the virtual characters `tr ρ₀ - ∑ i, ψ₀ i`
and `tr ρ₁ - ∑ j, ψ₁ j` are the same function `T`, then `T` is the character of a semisimple
representation: of a subrepresentation of `ρ₀` of codimension the number of the `ψ₀ i`
(`Representation.exists_subrepresentation_character_eq_sub_sum`).

This is the form in which strings of characters are removed from a representation known only
through its character: if `T + ∑ i, ψ₀ i` and `T + ∑ j, ψ₁ j` are both characters of
representations, the first of them semisimple, the common part `T` is the character of a
semisimple representation as well.

The proof peels the `ψ₀ i` off `ρ₀` one at a time. Write `D ψ` for the direct sum of the lines of a
family `ψ` of linear characters, and `ρ₁ˢˢ` for the semisimplification of `ρ₁`. The representations
`ρ₀ × D ψ₁` and `ρ₁ˢˢ × D ψ₀` are semisimple with the same character, so they are equivalent
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`). A character `χ`
among the `ψ₀ i` has a nonzero weight vector in `ρ₁ˢˢ × D ψ₀`, hence in `ρ₀ × D ψ₁`; as `χ` is none
of the `ψ₁ j`, the summand `D ψ₁` has no vector of weight `χ`, so the weight vector lies in `ρ₀`
(`Representation.weightSpace_ne_bot_of_character_sub_sum_eq`). Its line has a complementary
subrepresentation `σ`, with `ρ₀ ≃ σ × χ` (`Representation.exists_equiv_prod_ofLinearCharacter`), and
the argument continues with `σ` in place of `ρ₀`.

Neither algebraic closedness of `k` nor finiteness of `G` is used, and `G` need only be a monoid.
Characteristic zero enters only through the theorem that a semisimple representation is
determined by its character.

## Main results

* `Representation.weightSpace_ofLinearCharacter_eq_bot`: the line of `ψ` has no nonzero vector on
  which `G` acts through a different linear character.
* `Representation.weightSpace_ne_bot_of_character_add_eq`: for semisimple `ρ₀`, `σ₀`, `σ₁` and
  any `ρ₁` with `tr ρ₀ + tr σ₁ = tr ρ₁ + tr σ₀`, a weight of `σ₀` that is not a weight of `σ₁` is
  a weight of `ρ₀`.
* `Representation.weightSpace_ne_bot_of_character_sub_sum_eq`: under the hypotheses of the
  cancellation theorem, every `ψ₀ i` is a weight of `ρ₀`.
* `Representation.exists_equiv_prod_ofLinearCharacter`: a semisimple representation with a
  nonzero vector of weight `χ` is the product of a subrepresentation and the line of `χ`.
* `Representation.exists_subrepresentation_character_eq_sub_sum`: **cancellation of linear
  characters**.

## References

The statement is `New.IsTraceNondeg.exists_cancel_chars` of the formal development
<https://github.com/lsernau/grh-lean> (commit `72fead102f663d5c7a407964a13dc0cf9d977207`, file
`grh/src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean`), stated there for
representations into `GL_{n+t}` over an algebraically closed field, with families of the same
length `t`, and proved through a Wedderburn decomposition of the span of the image; the proof here
goes through weight vectors instead.
-/

public section

open Module

namespace Representation

variable {k G : Type*} [Monoid G]

section Lines

/-- **The line of `ψ` has no vector of weight `χ ≠ ψ`.** If `ψ` and `χ` are different linear
characters, no nonzero vector of the line of `ψ` is acted on through `χ`. -/
theorem weightSpace_ofLinearCharacter_eq_bot [CommRing k] [NoZeroDivisors k] {ψ χ : G →* kˣ}
    (h : ψ ≠ χ) :
    (ofLinearCharacter ψ).weightSpace ((Units.coeHom k).comp χ) = ⊥ := by
  obtain ⟨g, hg⟩ : ∃ g, (ψ g : k) ≠ χ g := by
    by_contra! H
    exact h (MonoidHom.ext fun g ↦ Units.ext (H g))
  refine eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot k).mpr ?_
  have hx := mem_weightSpace.mp hx g
  rw [ofLinearCharacter_apply, MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul,
    mul_comm] at hx
  have hx' : x * ((ψ g : k) - χ g) = 0 := by rw [mul_sub, hx, mul_comm, sub_self]
  exact (mul_eq_zero.mp hx').resolve_right (sub_ne_zero.mpr hg)

/-- Every vector of the line of `χ` is acted on through `χ`. -/
@[simp]
theorem weightSpace_ofLinearCharacter_self [CommSemiring k] (χ : G →* kˣ) :
    (ofLinearCharacter χ).weightSpace ((Units.coeHom k).comp χ) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ mem_weightSpace.mpr fun g ↦ by
    rw [ofLinearCharacter_apply, MonoidHom.comp_apply, Units.coeHom_apply, smul_eq_mul, mul_comm]

end Lines

variable [Field k] {V₀ V₁ W₀ W₁ : Type*} [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
  [Module k V₁] [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁] [Module k W₁]

/-- **A weight survives cancellation.** Let `ρ₀`, `ρ₁`, `σ₀` and `σ₁` be finite-dimensional
representations over a field of characteristic zero, all but `ρ₁` semisimple, with
`tr ρ₀ + tr σ₁ = tr ρ₁ + tr σ₀`. If `G` acts through `c` on a nonzero vector of `σ₀` but on no
nonzero vector of `σ₁`, then it acts through `c` on a nonzero vector of `ρ₀`. -/
theorem weightSpace_ne_bot_of_character_add_eq [CharZero k] [FiniteDimensional k V₀]
    [FiniteDimensional k V₁] [FiniteDimensional k W₀] [FiniteDimensional k W₁]
    {ρ₀ : Representation k G V₀} {ρ₁ : Representation k G V₁} {σ₀ : Representation k G W₀}
    {σ₁ : Representation k G W₁} [ρ₀.IsSemisimpleRepresentation] [σ₀.IsSemisimpleRepresentation]
    [σ₁.IsSemisimpleRepresentation] {c : G →* k}
    (h : ρ₀.character + σ₁.character = ρ₁.character + σ₀.character)
    (h₀ : σ₀.weightSpace c ≠ ⊥) (h₁ : σ₁.weightSpace c = ⊥) : ρ₀.weightSpace c ≠ ⊥ := by
  -- `ρ₁` need not be semisimple: compare `ρ₀ × σ₁` with `ρ₁ˢˢ × σ₀`, for the semisimplification
  -- `ρ₁ˢˢ`, which has the same character as `ρ₁`
  obtain ⟨e⟩ := nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation (ρ₀.prod σ₁)
    (ρ₁.semisimplification.prod σ₀) (funext fun g ↦ by
      simpa [char_semisimplification] using congrFun h g)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₀
  -- the weight vector `(0, w)` of `ρ₁ × σ₀` comes from a weight vector `(v, u)` of `ρ₀ × σ₁`
  have hmem : e.symm (0, w) ∈ (ρ₀.prod σ₁).weightSpace c := by
    rw [← e.apply_mem_weightSpace_iff, Equiv.apply_symm_apply, weightSpace_prod]
    exact ⟨Submodule.zero_mem _, hw⟩
  rw [weightSpace_prod, h₁] at hmem
  refine fun h0 ↦ hw0 ?_
  rw [h0, Submodule.prod_bot, Submodule.mem_bot] at hmem
  have h0w := congrArg e hmem
  rw [Equiv.apply_symm_apply, map_zero] at h0w
  exact congrArg Prod.snd h0w

/-- **Splitting off a line.** A semisimple representation `ρ` with a nonzero vector on which `G`
acts through the linear character `χ` is the product of a subrepresentation and the line of
`χ`. -/
theorem exists_equiv_prod_ofLinearCharacter {ρ : Representation k G V₀}
    [ρ.IsSemisimpleRepresentation] {χ : G →* kˣ}
    (h : ρ.weightSpace ((Units.coeHom k).comp χ) ≠ ⊥) :
    ∃ σ : Subrepresentation ρ,
      Nonempty (ρ.Equiv (σ.toRepresentation.prod (ofLinearCharacter χ))) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  -- the line through `v` is the image of the line of `χ` under `t ↦ t • v`
  let f : IntertwiningMap (ofLinearCharacter χ) ρ :=
    (LinearMap.toSpanSingleton k V₀ v).intertwiningMap_of_isIntertwiningMap _ _ fun g t ↦ by
      simp [ofLinearCharacter_apply, mem_weightSpace.mp hv g, smul_smul, mul_comm]
  have hf : Function.Injective f := fun s t hst ↦ smul_left_injective k hv0 hst
  obtain ⟨σ, hσ⟩ := exists_isCompl f.range
  exact ⟨σ, ⟨(Subrepresentation.equivProdOfIsCompl hσ.symm).trans
    ((Equiv.refl _).prodCongr
      (f.equivOfRange hf (IntertwiningMap.range_toSubmodule _ _ f).symm).symm)⟩⟩

/-- **A character to be cancelled is a weight.** Let `ρ₀` and `ρ₁` be finite-dimensional
representations over a field of characteristic zero, with `ρ₀` semisimple, and let `ψ₀ i` and
`ψ₁ j` be finite families of linear characters with no member in common. If
`tr ρ₀ - ∑ i, ψ₀ i = tr ρ₁ - ∑ j, ψ₁ j`, then every `ψ₀ i` is the action of `G` on some nonzero
vector of `ρ₀`. -/
theorem weightSpace_ne_bot_of_character_sub_sum_eq [CharZero k] [FiniteDimensional k V₀]
    [FiniteDimensional k V₁] {ρ₀ : Representation k G V₀} {ρ₁ : Representation k G V₁}
    [ρ₀.IsSemisimpleRepresentation] {ι₀ ι₁ : Type*} [Fintype ι₀]
    [Fintype ι₁] {ψ₀ : ι₀ → G →* kˣ} {ψ₁ : ι₁ → G →* kˣ} (hψ : ∀ i j, ψ₀ i ≠ ψ₁ j)
    (h : ∀ g, ρ₀.character g - ∑ i, (ψ₀ i g : k) = ρ₁.character g - ∑ j, (ψ₁ j g : k))
    (i : ι₀) : ρ₀.weightSpace ((Units.coeHom k).comp (ψ₀ i)) ≠ ⊥ := by
  classical
  -- compare `ρ₀ × D ψ₁` with `ρ₁ × D ψ₀`, where `D ψ` is the direct sum of the lines of the `ψ`
  refine weightSpace_ne_bot_of_character_add_eq (ρ₁ := ρ₁)
    (σ₀ := directSum fun j ↦ ofLinearCharacter (ψ₀ j))
    (σ₁ := directSum fun j ↦ ofLinearCharacter (ψ₁ j)) (funext fun g ↦ ?_) ?_ ?_
  · simp only [Pi.add_apply, char_directSum, char_ofLinearCharacter]
    linear_combination h g
  · -- the vector `1` in the summand of `ψ₀ i` has weight `ψ₀ i`
    refine Submodule.ne_bot_iff _ |>.mpr ⟨DirectSum.lof k _ _ i 1,
      (mem_weightSpace_directSum _).mpr fun j ↦ ?_, fun h0 ↦ ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [DirectSum.lof_apply, weightSpace_ofLinearCharacter_self]
        exact Submodule.mem_top
      · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
        exact Submodule.zero_mem _
    · have h0i := DFunLike.congr_fun h0 i
      rw [DirectSum.lof_apply, DirectSum.zero_apply] at h0i
      exact one_ne_zero h0i
  · -- no summand of `D ψ₁` has weight `ψ₀ i`
    refine eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot k).mpr <| DirectSum.ext fun j ↦ ?_
    have hxj := (mem_weightSpace_directSum _).mp hx j
    rw [weightSpace_ofLinearCharacter_eq_bot (hψ i j).symm] at hxj
    rw [DirectSum.zero_apply]
    exact (Submodule.mem_bot k).mp hxj

/-- **Cancellation of linear characters.** Let `ρ₀` and `ρ₁` be finite-dimensional representations
over a field of characteristic zero, with `ρ₀` semisimple, and let `ψ₀ i` and `ψ₁ j` be finite
families of linear characters with no member in common. If `tr ρ₀ - ∑ i, ψ₀ i = tr ρ₁ - ∑ j, ψ₁ j`,
then this function is the character of a subrepresentation `σ` of `ρ₀` of codimension the number of
the `ψ₀ i`; being a subrepresentation of `ρ₀`, `σ` is semisimple. -/
theorem exists_subrepresentation_character_eq_sub_sum [CharZero k] [FiniteDimensional k V₀]
    [FiniteDimensional k V₁] {ρ₀ : Representation k G V₀} {ρ₁ : Representation k G V₁}
    [ρ₀.IsSemisimpleRepresentation] {ι₀ ι₁ : Type*} [Fintype ι₀]
    [Fintype ι₁] {ψ₀ : ι₀ → G →* kˣ} {ψ₁ : ι₁ → G →* kˣ} (hψ : ∀ i j, ψ₀ i ≠ ψ₁ j)
    (h : ∀ g, ρ₀.character g - ∑ i, (ψ₀ i g : k) = ρ₁.character g - ∑ j, (ψ₁ j g : k)) :
    ∃ σ : Subrepresentation ρ₀, σ.toRepresentation.IsSemisimpleRepresentation ∧
      finrank k σ.toSubmodule + Fintype.card ι₀ = finrank k V₀ ∧
      ∀ g, σ.toRepresentation.character g = ρ₀.character g - ∑ i, (ψ₀ i g : k) := by
  classical
  have hss (σ : Subrepresentation ρ₀) : σ.toRepresentation.IsSemisimpleRepresentation :=
    σ.subtype.isSemisimpleRepresentation_of_injective σ.subtype_injective
  -- peel off the characters `ψ₀ i` for `i ∈ s`, by induction on the finite set `s`
  suffices H : ∀ s : Finset ι₀, ∃ σ : Subrepresentation ρ₀,
      finrank k σ.toSubmodule + s.card = finrank k V₀ ∧
      ∀ g, σ.toRepresentation.character g = ρ₀.character g - ∑ i ∈ s, (ψ₀ i g : k) by
    obtain ⟨σ, hσ⟩ := H Finset.univ
    exact ⟨σ, hss σ, by simpa using hσ⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⊤, by simp, fun g ↦ ?_⟩
    rw [Finset.sum_empty, sub_zero, char_iso
      ((⊤ : Subrepresentation ρ₀).subtype.ofBijective ⟨Subrepresentation.subtype_injective _,
        (Subrepresentation.subtype_surjective_iff _).mpr rfl⟩)]
  | insert i s hi ih =>
    obtain ⟨σ, hσr, hσc⟩ := ih
    have := hss σ
    -- the character `ψ₀ i` is still to be cancelled from `σ`, so it is a weight of `σ`
    have hw : σ.toRepresentation.weightSpace ((Units.coeHom k).comp (ψ₀ i)) ≠ ⊥ :=
      weightSpace_ne_bot_of_character_sub_sum_eq (ρ₁ := ρ₁)
        (ψ₀ := fun j : (sᶜ : Finset ι₀) ↦ ψ₀ j)
        (fun j l ↦ hψ j l) (fun g ↦ by
          rw [hσc, Finset.sum_coe_sort sᶜ fun j ↦ (ψ₀ j g : k), ← h g,
            ← Finset.sum_compl_add_sum s]
          ring) ⟨i, Finset.mem_compl.mpr hi⟩
    obtain ⟨τ, ⟨e⟩⟩ := exists_equiv_prod_ofLinearCharacter hw
    -- carry `τ ≤ σ` back to a subrepresentation of `ρ₀`
    let f := σ.subtype.comp τ.subtype
    have hf : Function.Injective f := σ.subtype_injective.comp τ.subtype_injective
    let e' := f.equivOfRange hf (IntertwiningMap.range_toSubmodule _ _ f).symm
    refine ⟨f.range, ?_, fun g ↦ ?_⟩
    · rw [← e'.toLinearEquiv.finrank_eq, Finset.card_insert_of_notMem hi, ← hσr,
        e.toLinearEquiv.finrank_eq, finrank_prod, finrank_self]
      ring
    · rw [← char_iso e', Finset.sum_insert hi, ← sub_sub, sub_right_comm, ← hσc, char_iso e,
        char_prod, char_ofLinearCharacter, add_sub_cancel_right]

end Representation
