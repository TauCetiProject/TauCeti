/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.Pi
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Character.Basic
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Pi.Basic
public import TauCeti.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.Semisimplification
public import TauCeti.RepresentationTheory.Subrepresentation.Eigenvector

/-!
# Cancelling two disjoint families of characters

Let `ρ₀` and `ρ₁` be representations of a monoid `G` over a field `k` of characteristic zero,
and let `ψ₀ : ι₀ → G →* kˣ` and `ψ₁ : ι₁ → G →* kˣ` be finite families of characters with
`ψ₀ i ≠ ψ₁ j` for all `i` and `j`. If `χ_{ρ₀} - ∑ i, ψ₀ i = χ_{ρ₁} - ∑ j, ψ₁ j`, this common
function is the character of a semisimple representation of dimension `dim ρ₀ - card ι₀`
(`Representation.exists_isSemisimpleRepresentation_character_eq_sub_sum`).

Write `Ψ` for the direct sum `Representation.pi fun i ↦ ofLinearCharacter (ψ i)` of the lines of a
family of characters. For `ρ₀` semisimple, the proof compares the semisimple representations
`ρ₀ ⊕ Ψ₁` and `ρ₁^ss ⊕ Ψ₀`, which have the same character, so they are equivalent by
`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`. Restricted to
`Ψ₀`, the equivalence has no component in `Ψ₁`, because an intertwining map between the line
sums of two disjoint families of characters is zero
(`Representation.IntertwiningMap.eq_zero_of_pi_ofLinearCharacter`). So `Ψ₀` embeds into `ρ₀`
(`Representation.exists_injective_intertwiningMap_pi_ofLinearCharacter`), and an invariant
complement of its image is the required representation. In general `ρ₀` and `ρ₁` are replaced by
semisimple finite-dimensional representations with the same characters and dimensions
(`Representation.exists_fdRep_isSemisimpleRepresentation_character_eq`): their
semisimplifications, or the zero representation for an infinite-dimensional one, whose character
and `Module.finrank` are zero.

## Main results

* `Representation.char_pi`: the character of a finite product is the sum of the characters.
* `Representation.char_pi_ofLinearCharacter`: the character of `Ψ` is `∑ i, ψ i`.
* `Representation.isSemisimpleRepresentation_pi_ofLinearCharacter`: `Ψ` is semisimple.
* `Representation.exists_fdRep_isSemisimpleRepresentation_character_eq`: every representation has
  a semisimple counterpart in `FDRep k G` with the same character and dimension.
* `Representation.IntertwiningMap.eq_zero_of_pi_ofLinearCharacter`: an intertwining map `Ψ₀ → Ψ₁`
  between the line sums of two disjoint families of characters is zero.
* `Representation.exists_injective_intertwiningMap_pi_ofLinearCharacter`: under the hypotheses
  above, with `ρ₀` semisimple, `Ψ₀` embeds into `ρ₀`.
* `Representation.exists_isSemisimpleRepresentation_character_eq_sub_sum`: under the hypotheses
  above, `χ_{ρ₀} - ∑ i, ψ₀ i` is the character of a semisimple representation of dimension
  `dim ρ₀ - card ι₀`.

## Provenance

The statement is part (e) of a cancellation lemma for semisimple representations in characteristic
zero, formalised in `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic, PBC) as `New.IsTraceNondeg.exists_cancel_chars` through a common Wedderburn
decomposition. The proof here is independent: it reduces to the character criterion
for equivalence of semisimple representations.
-/

public section

namespace Representation

variable {k G V₀ V₁ ι ι₀ ι₁ : Type*} [Field k] [Monoid G]

section LineSum

variable (ψ : ι → G →* kˣ)

/-- **The character of a finite product of representations** is the sum of the characters of
the factors. -/
@[simp]
theorem char_pi [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)] (ρ : ∀ i, Representation k G (V i)) (g : G) :
    (pi ρ).character g = ∑ i, (ρ i).character g := by
  have hg : pi ρ g = LinearMap.piMap fun i ↦ ρ i g :=
    LinearMap.ext fun x ↦ funext fun i ↦ pi_apply ρ g x i
  rw [character, hg, LinearMap.trace_piMap]
  rfl

/-- **The character of a sum of lines** is the sum of their characters. -/
theorem char_pi_ofLinearCharacter [Fintype ι] (g : G) :
    (pi fun i ↦ ofLinearCharacter (ψ i)).character g = ∑ i, (ψ i g : k) := by
  simp only [char_pi, char_ofLinearCharacter]

/-- **A finite sum of lines is semisimple**: it is spanned by the standard basis vectors, which
are common eigenvectors. -/
instance isSemisimpleRepresentation_pi_ofLinearCharacter [Finite ι] :
    (pi fun i ↦ ofLinearCharacter (ψ i)).IsSemisimpleRepresentation := by
  classical
  refine isSemisimpleRepresentation_of_span_eq_top _
    (S := Set.range fun i ↦ Pi.single i (1 : k)) ?_ ?_
  · rintro _ ⟨i, rfl⟩ g
    refine ⟨ψ i g, funext fun j ↦ ?_⟩
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  · simpa only [← funext (Pi.basisFun_apply k ι)] using (Pi.basisFun k ι).span_eq

end LineSum

/-- **Disjoint families of characters admit no intertwining maps**: an intertwining map between
the sums of the lines of two families of characters `ψ₀` and `ψ₁` with `ψ₀ i ≠ ψ₁ j` for all `i`
and `j` is zero. -/
theorem IntertwiningMap.eq_zero_of_pi_ofLinearCharacter [Finite ι₀] {ψ₀ : ι₀ → G →* kˣ}
    {ψ₁ : ι₁ → G →* kˣ} (hne : ∀ i j, ψ₀ i ≠ ψ₁ j)
    (f : IntertwiningMap (pi fun i ↦ ofLinearCharacter (ψ₀ i))
      (pi fun j ↦ ofLinearCharacter (ψ₁ j))) :
    f = 0 := by
  classical
  refine IntertwiningMap.ext (LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring (funext fun j ↦ ?_))
  obtain ⟨g, hg⟩ : ∃ g, ψ₀ i g ≠ ψ₁ j g := not_forall.mp fun h ↦ hne i j (MonoidHom.ext h)
  have hx : (pi fun l ↦ ofLinearCharacter (ψ₀ l)) g (Pi.single i 1) =
      (ψ₀ i g : k) • Pi.single i 1 := by
    ext l
    by_cases h : l = i
    · subst h
      simp
    · simp [h]
  have h := congrFun (LinearMap.congr_fun (f.isIntertwining' g) (Pi.single i 1)) j
  simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] at h
  rw [hx, map_smul, pi_apply, ofLinearCharacter_apply, Pi.smul_apply, smul_eq_mul] at h
  have h' : ((ψ₀ i g : k) - ψ₁ j g) * f (Pi.single i 1) j = 0 := by
    rw [sub_mul, h, sub_self]
  simpa using (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Units.val_injective.ne hg))

variable [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]

/-- **A semisimple representation with the character and dimension of a given one.** Every
representation `ρ` has a semisimple counterpart in `FDRep k G` with the same character and the same
`Module.finrank`: the semisimplification of `ρ` if `ρ` is finite-dimensional, and the zero
representation otherwise, the character and `Module.finrank` of `ρ` then being zero. -/
theorem exists_fdRep_isSemisimpleRepresentation_character_eq (ρ : Representation k G V₀) :
    ∃ s : FDRep k G, IsSemisimpleRepresentation s.ρ ∧ s.character = ρ.character ∧
      Module.finrank k s = Module.finrank k V₀ := by
  by_cases hV : FiniteDimensional k V₀
  · refine ⟨FDRep.ofShrink ρ.semisimplification,
      (FDRep.ofShrinkEquiv _).toIntertwiningMap.isSemisimpleRepresentation_of_injective
        (FDRep.ofShrinkEquiv _).injective,
      funext fun g ↦ by rw [FDRep.character_ofShrink, char_semisimplification], ?_⟩
    rw [FDRep.finrank_ofShrink, ← (ρ.semisimplification 1).charpoly_natDegree,
      charpoly_semisimplification_apply, LinearMap.charpoly_natDegree]
  · have : (trivial k G PUnit.{1}).IsSemisimpleRepresentation :=
      isSemisimpleRepresentation_of_span_eq_top _ (S := ∅) (by simp) (Subsingleton.elim _ _)
    refine ⟨FDRep.ofShrink (trivial k G PUnit.{1}),
      (FDRep.ofShrinkEquiv _).toIntertwiningMap.isSemisimpleRepresentation_of_injective
        (FDRep.ofShrinkEquiv _).injective,
      funext fun g ↦ ?_, ?_⟩
    · rw [FDRep.character_ofShrink, char_trivial, character_eq_zero_of_not_finite ρ hV,
        Module.finrank_zero_of_subsingleton, Nat.cast_zero, Pi.zero_apply]
    · rw [FDRep.finrank_ofShrink, Module.finrank_of_not_finite hV,
        Module.finrank_zero_of_subsingleton]

/-- **Disjoint characters cancelled from a semisimple representation split off.** Let `ρ₀` be a
finite-dimensional semisimple representation and `ρ₁` any representation over a field of
characteristic zero, and let `ψ₀` and `ψ₁` be finite families of characters with `ψ₀ i ≠ ψ₁ j`
for all `i` and `j`. If `χ_{ρ₀} - ∑ i, ψ₀ i = χ_{ρ₁} - ∑ j, ψ₁ j`, then the sum of the lines of
`ψ₀` embeds into `ρ₀`. -/
theorem exists_injective_intertwiningMap_pi_ofLinearCharacter [CharZero k] [Fintype ι₀]
    [Fintype ι₁] [FiniteDimensional k V₀] (ρ₀ : Representation k G V₀)
    (ρ₁ : Representation k G V₁) [ρ₀.IsSemisimpleRepresentation] {ψ₀ : ι₀ → G →* kˣ}
    {ψ₁ : ι₁ → G →* kˣ} (hne : ∀ i j, ψ₀ i ≠ ψ₁ j)
    (h : ∀ g, ρ₀.character g - ∑ i, (ψ₀ i g : k) = ρ₁.character g - ∑ j, (ψ₁ j g : k)) :
    ∃ f : IntertwiningMap (pi fun i ↦ ofLinearCharacter (ψ₀ i)) ρ₀, Function.Injective f := by
  obtain ⟨s₁, hs₁, hc₁, -⟩ := exists_fdRep_isSemisimpleRepresentation_character_eq ρ₁
  have hc₁' : Representation.character s₁.ρ = ρ₁.character := hc₁
  obtain ⟨e⟩ := nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation
    (Representation.prod s₁.ρ (pi fun i ↦ ofLinearCharacter (ψ₀ i)))
    (ρ₀.prod (pi fun j ↦ ofLinearCharacter (ψ₁ j))) <| funext fun g ↦ by
      rw [char_prod, char_prod, hc₁', char_pi_ofLinearCharacter, char_pi_ofLinearCharacter]
      linear_combination -(h g)
  let φ := e.toIntertwiningMap.comp (IntertwiningMap.inr k _ _)
  have h0 := IntertwiningMap.eq_zero_of_pi_ofLinearCharacter hne
    ((IntertwiningMap.snd k _ _).comp φ)
  refine ⟨(IntertwiningMap.fst k _ _).comp φ, fun x y hxy ↦ ?_⟩
  have hφ : φ x = φ y := Prod.ext hxy <| by
    have hx := congrArg (fun f : IntertwiningMap _ _ ↦ f x) h0
    have hy := congrArg (fun f : IntertwiningMap _ _ ↦ f y) h0
    exact hx.trans hy.symm
  exact congrArg Prod.snd (e.injective hφ)

/-- **Cancelling two disjoint families of characters.** Let `ρ₀` and `ρ₁` be representations over
a field of characteristic zero, and let `ψ₀` and `ψ₁` be finite families of characters with
`ψ₀ i ≠ ψ₁ j` for all `i` and `j`. If `χ_{ρ₀} - ∑ i, ψ₀ i = χ_{ρ₁} - ∑ j, ψ₁ j`, this function is
the character of a semisimple representation `s` with `dim s + card ι₀ = dim ρ₀`. -/
theorem exists_isSemisimpleRepresentation_character_eq_sub_sum [CharZero k] [Fintype ι₀]
    [Fintype ι₁] (ρ₀ : Representation k G V₀) (ρ₁ : Representation k G V₁)
    {ψ₀ : ι₀ → G →* kˣ} {ψ₁ : ι₁ → G →* kˣ} (hne : ∀ i j, ψ₀ i ≠ ψ₁ j)
    (h : ∀ g, ρ₀.character g - ∑ i, (ψ₀ i g : k) = ρ₁.character g - ∑ j, (ψ₁ j g : k)) :
    ∃ s : FDRep k G, IsSemisimpleRepresentation s.ρ ∧
      (∀ g, s.character g = ρ₀.character g - ∑ i, (ψ₀ i g : k)) ∧
      Module.finrank k s + Fintype.card ι₀ = Module.finrank k V₀ := by
  obtain ⟨s₀, hs₀, hc₀, hd₀⟩ := exists_fdRep_isSemisimpleRepresentation_character_eq ρ₀
  have hc₀' : Representation.character s₀.ρ = ρ₀.character := hc₀
  obtain ⟨f, hf⟩ := exists_injective_intertwiningMap_pi_ofLinearCharacter s₀.ρ ρ₁ hne
    fun g ↦ by rw [hc₀']; exact h g
  obtain ⟨C, hC⟩ := exists_isCompl f.range
  have hC' : C.toRepresentation.IsSemisimpleRepresentation :=
    C.subtype.isSemisimpleRepresentation_of_injective C.subtype_injective
  have hchar (g : G) : (FDRep.ofShrink C.toRepresentation).character g =
      ρ₀.character g - ∑ i, (ψ₀ i g : k) := by
    have hsum := congrFun (Subrepresentation.char_add_eq_of_isCompl hC) g
    rw [Pi.add_apply, ← char_iso (f.equivOfRange hf rfl), char_pi_ofLinearCharacter, hc₀'] at hsum
    rw [FDRep.character_ofShrink, ← hsum, add_sub_cancel_left]
  refine ⟨FDRep.ofShrink C.toRepresentation,
    (FDRep.ofShrinkEquiv _).toIntertwiningMap.isSemisimpleRepresentation_of_injective
      (FDRep.ofShrinkEquiv _).injective, hchar, ?_⟩
  have h1 := hchar 1
  rw [FDRep.char_one, ← hc₀', char_one, hd₀] at h1
  simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at h1
  exact_mod_cast eq_sub_iff_add_eq.mp h1

end Representation
