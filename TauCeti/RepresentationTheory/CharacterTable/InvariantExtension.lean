/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
import TauCeti.GroupTheory.SemidirectProduct
import TauCeti.RepresentationTheory.CharacterTable.Automorphism
import TauCeti.RepresentationTheory.Induction.Clifford.Decomposition

/-!
# Extending an invariant irreducible character by a virtual character

Let `N` be a normal subgroup of a finite group `G`, of index `n`, and let `Y` be an irreducible
character of `N` that is invariant under conjugation by `G`. Given a virtual character `Θ` of `G`,
glue the function `χ` equal to `Y` on `N` and to `Θ` off `N`. This file proves that `χ` is an
irreducible character of `G` as soon as two numerical conditions hold:

* `n ⟨Θ, Θ⟩_G = ⟨Θ|_N, Θ|_N⟩_N + n - 1`, which says that `Θ` has, off `N`, the norm
  `|G| - |N|` of an irreducible character extending `Y`;
* `⟨Y, Θ|_N⟩_N = 1 + n m` for an integer `m`.

So an extension of `Y` can be produced without constructing a representation: it suffices to find
a virtual character `Θ` with the right values off `N`, whose pairings are computed by other means.

The argument is a norm computation. Splitting the sums over `G` into `N` and its complement, the
pairing of a class function `c` of `G` with `χ` is
`⟨c, χ⟩_G = ⟨c, Θ⟩_G + n⁻¹ (⟨c|_N, Y⟩_N - ⟨c|_N, Θ|_N⟩_N)`
(`TauCeti.ClassFunction.characterPairing_eq_add_inv_index_mul`). Taking `c = χ` and `c = Θ`, the
first condition gives `⟨χ, χ⟩_G = 1`. Taking for `c` an irreducible character, the coefficients of
`χ` in the basis of irreducible characters lie in `n⁻¹ ℤ`. Restricting the expansion of `χ` to `N`
and pairing with `Y` shows that some irreducible character `ψ` lying over `Y` has a nonzero
coefficient; by Clifford's theorem `ψ|_N = e Y`
(`TauCeti.exists_restrict_eq_natCast_mul_of_mem_irreducibleCharactersOver`), and then the second
condition makes this coefficient the integer `⟨ψ, Θ⟩_G - e m`. A sum of squares of numbers in
`n⁻¹ ℤ` equal to `1` with a nonzero integer term has only that term, which is `±1`, so `χ = ±ψ`,
and the degree `χ(1) = Y(1)`, a positive natural number, fixes the sign
(`TauCeti.mem_irreducibleCharacters_of_forall_exists_natCast_mul_eq_intCast`).

The pairing is `TauCeti.ClassFunction.characterPairing`, `⟨f, f'⟩ = |G|⁻¹ ∑ g, f g f' g⁻¹`; on
virtual characters over `ℂ` it is the hermitian inner product `|G|⁻¹ ∑ g, conj (f g) f' g`, since
`conj (f g) = f g⁻¹` there (`TauCeti.conj_apply_of_mem_virtualCharacters`).

## Main results

* `TauCeti.mem_irreducibleCharacters_of_restrict_eq_of_eqOn_compl`: **the extension criterion**
  for a normal subgroup `N` of `G`.
* `TauCeti.mem_irreducibleCharacters_semidirectProduct_of_comp_inl_eq`: the criterion for the
  normal factor of a semidirect product `N ⋊[φ] S`, where the index is `|S|`, the invariance is
  under the action `φ` of `S`, and `χ` is `Y` on the elements `x` with `x.right = 1`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapters 2 and 6.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/LocalGL/Shintani/CosetRootChoice.lean` (declaration
  `New.IsIrreducibleChar.extend_semidirect`); Apache 2.0, Copyright 2026 Anthropic, PBC. The
  criterion for a semidirect product and the route of its proof, by the norm, the integrality of
  the pairings with the characters lying over `Y`, and the positivity of the degree, follow it.
-/

public section

namespace TauCeti

open ClassFunction Finset

variable {k : Type*} {G : Type*} [Field k] [Group G] [Fintype G] {N : Subgroup G} [Fintype N]

section Pairing

variable {Y : ClassFunction k N} {Θ F : ClassFunction k G}

/-- The glued class function has norm one under the first numerical condition. -/
private theorem characterPairing_self_eq_one [NeZero (N.index : k)]
    (hres : ∀ n : N, F.val n = Y.val n) (hoff : Set.EqOn F.val Θ.val (N : Set G)ᶜ)
    (hYY : characterPairing Y Y = 1)
    (h₁ : (N.index : k) * characterPairing Θ Θ =
      characterPairing (comap N.subtype Θ) (comap N.subtype Θ) + N.index - 1) :
    characterPairing F F = 1 := by
  have hP := characterPairing_eq_add_inv_index_mul hres hoff
  have hFN : comap N.subtype F = Y := Subtype.ext (funext fun n => by simp [hres])
  have hi : (N.index : k) ≠ 0 := NeZero.ne _
  rw [hP F, hFN, characterPairing_symm F Θ, hP Θ, characterPairing_symm (comap _ Θ) Y, hYY]
  field_simp
  linear_combination h₁

variable [IsAlgClosed k] [Invertible (Nat.card G : k)]

omit [Fintype N] in
/-- The coefficients of the glued class function in the basis of irreducible characters lie in
`n⁻¹ ℤ` for the index `n` of `N`, since the three pairings that make them up are pairings of
virtual characters. -/
private theorem exists_index_mul_characterPairing_eq_intCast (hres : ∀ n : N, F.val n = Y.val n)
    (hoff : Set.EqOn F.val Θ.val (N : Set G)ᶜ) (hY : (Y : N → k) ∈ virtualCharacters k N)
    (hΘ : (Θ : G → k) ∈ virtualCharacters k G) (i : Fin (Nat.card (ConjClasses G))) :
    ∃ z : ℤ, (N.index : k) *
      characterPairing (ofCharacter (irreducibleRepresentation k i)) F = z := by
  let _ : Fintype N := Fintype.ofFinite N
  have hχ := ofCharacter_mem_virtualCharacters (irreducibleRepresentation k i)
  -- restrictions of virtual characters to `N` are virtual characters
  have hχN := comap_mem_virtualCharacters N.subtype hχ
  obtain ⟨z₁, hz₁⟩ := exists_characterPairing_eq_intCast hχ hΘ
  obtain ⟨z₂, hz₂⟩ := exists_characterPairing_eq_intCast hχN hY
  obtain ⟨z₃, hz₃⟩ := exists_characterPairing_eq_intCast hχN
    (comap_mem_virtualCharacters N.subtype hΘ)
  have hi : (N.index : k) ≠ 0 :=
    left_ne_zero_of_mul (by rw [← Nat.cast_mul, N.index_mul_card]; exact Invertible.ne_zero _)
  refine ⟨N.index * z₁ + z₂ - z₃, ?_⟩
  rw [characterPairing_eq_add_inv_index_mul hres hoff, hz₁, hz₂, hz₃]
  field_simp
  push_cast
  ring

/-- Some coefficient of the glued class function is a nonzero integer: restricting the expansion
to `N` and pairing with `Y` finds an irreducible character `ψ` lying over `Y` with a nonzero
coefficient, by Clifford's theorem `ψ|_N = e Y`, and then the second numerical condition makes the
coefficient `⟨ψ, Θ⟩_G - e m`. The invariance of `Y` that Clifford's theorem needs comes from `F`
being a class function. -/
private theorem exists_characterPairing_eq_intCast_ne_zero [N.Normal]
    (hres : ∀ n : N, F.val n = Y.val n) (hoff : Set.EqOn F.val Θ.val (N : Set G)ᶜ)
    (hY : (Y : N → k) ∈ irreducibleCharacters k N) (hΘ : (Θ : G → k) ∈ virtualCharacters k G)
    {m : ℤ} (h₂ : characterPairing Y (comap N.subtype Θ) = 1 + N.index * m) :
    ∃ (i : Fin (Nat.card (ConjClasses G))) (w : ℤ), w ≠ 0 ∧
      characterPairing (ofCharacter (irreducibleRepresentation k i)) F = w := by
  -- `|G| = n |N|` is invertible in `k`, hence so are the index `n` and `|N|`
  have hG : (N.index : k) * Nat.card N ≠ 0 := by
    rw [← Nat.cast_mul, N.index_mul_card]
    exact Invertible.ne_zero _
  have hYY := characterPairing_self_of_mem_irreducibleCharacters hY (right_ne_zero_of_mul hG)
  -- `Y` is invariant under `G`, being the restriction of the class function `F`
  have hFN : comap N.subtype F = Y := Subtype.ext (funext fun n => by simp [hres])
  have hinv (g : G) : (Y : N → k) ∘ MulAut.conjNormal g = Y :=
    hFN ▸ funext (comap_subtype_apply_conjNormal F g)
  set c := fun i : Fin (Nat.card (ConjClasses G)) => ofCharacter (irreducibleRepresentation k i)
  have hc (i) : (c i : G → k) = irreducibleCharacter k i :=
    funext fun g => by simp [c, character_irreducibleRepresentation]
  -- pairing the restriction of the expansion of `F` with `Y` gives `⟨Y, Y⟩ = 1`
  obtain ⟨i, ha, hY₀⟩ :
      ∃ i, characterPairing (c i) F ≠ 0 ∧ characterPairing Y (comap N.subtype (c i)) ≠ 0 := by
    have h := congrArg (fun f => characterPairing Y (comap N.subtype f))
      (sum_characterPairing_smul_ofCharacter (irreducibleRepresentation k)
        (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) F)
    simp only [map_sum, map_smul, smul_eq_mul, hFN, hYY] at h
    obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero (h ▸ one_ne_zero)
    exact ⟨i, left_ne_zero_of_mul hi, right_ne_zero_of_mul hi⟩
  -- by Clifford's theorem the `i`-th irreducible character is `e • Y` on `N`
  have hmem : irreducibleCharacter k i ∈ irreducibleCharactersOver k N Y := by
    refine mem_irreducibleCharactersOver_iff_sum.mpr ⟨irreducibleCharacter_mem k i,
      fun h0 => hY₀ ?_⟩
    rw [characterPairing_symm, characterPairing_apply]
    simp [comap_apply, hc, h0]
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  obtain ⟨e, -, he⟩ :=
    exists_restrict_eq_natCast_mul_of_mem_irreducibleCharactersOver hY hinv hmem
  have hcN : comap N.subtype (c i) = (e : k) • Y :=
    Subtype.ext (funext fun n => by simp [comap_apply, hc, he])
  obtain ⟨t, ht⟩ :=
    exists_characterPairing_eq_intCast (f₁ := c i) (ofCharacter_mem_virtualCharacters _) hΘ
  have hi : (N.index : k) ≠ 0 := left_ne_zero_of_mul hG
  have hai : characterPairing (c i) F = ((t - e * m : ℤ) : k) := by
    rw [characterPairing_eq_add_inv_index_mul hres hoff, hcN]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hYY, h₂, ht]
    field_simp
    push_cast
    ring
  exact ⟨i, t - e * m, fun h0 => ha (by rw [hai, h0, Int.cast_zero]), hai⟩

end Pairing

variable [IsAlgClosed k] [CharZero k] [N.Normal]

/-- **Extending an invariant irreducible character by a virtual character.** Let `N` be a normal
subgroup of the finite group `G`, of index `n`, let `Y` be an irreducible character of `N`
invariant under conjugation by `G`, and let `Θ` be a virtual character of `G` with
`n ⟨Θ, Θ⟩_G = ⟨Θ|_N, Θ|_N⟩_N + n - 1` and `⟨Y, Θ|_N⟩_N = 1 + n m` for an integer `m`. Then the
function `χ` equal to `Y` on `N` and to `Θ` off `N` is an irreducible character of `G`; in
particular it extends `Y`.

The field `k` is algebraically closed of characteristic zero, for instance `ℂ`, where the pairing
of virtual characters is the hermitian inner product. -/
theorem mem_irreducibleCharacters_of_restrict_eq_of_eqOn_compl {Y : ClassFunction k N}
    (hY : (Y : N → k) ∈ irreducibleCharacters k N)
    (hinv : ∀ g : G, (Y : N → k) ∘ MulAut.conjNormal g = Y) {Θ : ClassFunction k G}
    (hΘ : (Θ : G → k) ∈ virtualCharacters k G)
    (h₁ : (N.index : k) * characterPairing Θ Θ =
      characterPairing (comap N.subtype Θ) (comap N.subtype Θ) + N.index - 1)
    {m : ℤ} (h₂ : characterPairing Y (comap N.subtype Θ) = 1 + N.index * m) {χ : G → k}
    (hres : ∀ n : N, χ n = (Y : N → k) n) (hoff : Set.EqOn χ Θ (N : Set G)ᶜ) :
    χ ∈ irreducibleCharacters k G := by
  let _ : Invertible (Nat.card G : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : NeZero (N.index : k) := ⟨Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite⟩
  -- `χ` is a class function: on `N` by the invariance of `Y`, off `N` because `Θ` is one
  have hcl : χ ∈ ClassFunction k G := by
    refine ClassFunction.mem_iff.mpr fun g h => ?_
    by_cases hg : g ∈ N
    · rw [← MulAut.conjNormal_apply h ⟨g, hg⟩, hres, hres ⟨g, hg⟩]
      exact congrFun (hinv h) ⟨g, hg⟩
    · have hc : h * g * h⁻¹ ∉ N := fun hc => hg (by
        simpa [mul_assoc] using Subgroup.Normal.conj_mem _ hc h⁻¹)
      rw [hoff hc, hoff hg]
      exact ClassFunction.mem_iff.mp Θ.property g h
  let F : ClassFunction k G := ⟨χ, hcl⟩
  have hYY :=
    characterPairing_self_of_mem_irreducibleCharacters hY (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨i₀, w, hw, hi₀⟩ :=
    exists_characterPairing_eq_intCast_ne_zero (F := F) hres hoff hY hΘ h₂
  obtain ⟨d, ρ, -, hρ⟩ := mem_irreducibleCharacters_iff.mp hY
  exact mem_irreducibleCharacters_of_forall_exists_natCast_mul_eq_intCast
    (characterPairing_self_eq_one (F := F) hres hoff hYY h₁) Subgroup.index_ne_zero_of_finite
    (exists_index_mul_characterPairing_eq_intCast (F := F) hres hoff
      (irreducibleCharacters_subset_virtualCharacters hY) hΘ) hw hi₀
    (by simpa [F, ← hρ, Representation.char_one] using hres 1)

open SemidirectProduct in
/-- **Extending an invariant irreducible character from the normal factor of a semidirect
product.** Let a finite group `S` act on a finite group `N` through `φ`, let `Y` be an irreducible
character of `N` invariant under `S`, and let `Θ` be a virtual character of `N ⋊[φ] S` with
`|S| ⟨Θ, Θ⟩ = ⟨Θ|_N, Θ|_N⟩_N + |S| - 1` and `⟨Y, Θ|_N⟩_N = 1 + |S| m` for an integer `m`, where
`Θ|_N` is `Θ ∘ inl`. Then the function `χ` equal to `Y` on `N`, read through `inl`, and to `Θ` on
the elements `x` with `x.right ≠ 1` is an irreducible character of `N ⋊[φ] S`.

This is `TauCeti.mem_irreducibleCharacters_of_restrict_eq_of_eqOn_compl` for the kernel of
`SemidirectProduct.rightHom`, which has index `|S|`. -/
theorem mem_irreducibleCharacters_semidirectProduct_of_comp_inl_eq {N S : Type*} [Group N]
    [Group S] {φ : S →* MulAut N} [Fintype N] [Fintype (N ⋊[φ] S)] {Y : ClassFunction k N}
    (hY : (Y : N → k) ∈ irreducibleCharacters k N) (hinv : ∀ s : S, (Y : N → k) ∘ φ s = Y)
    {Θ : ClassFunction k (N ⋊[φ] S)} (hΘ : (Θ : N ⋊[φ] S → k) ∈ virtualCharacters k (N ⋊[φ] S))
    (h₁ : (Nat.card S : k) * characterPairing Θ Θ =
      characterPairing (comap inl Θ) (comap inl Θ) + Nat.card S - 1)
    {m : ℤ} (h₂ : characterPairing Y (comap inl Θ) = 1 + Nat.card S * m)
    {χ : N ⋊[φ] S → k} (hres : χ ∘ inl = Y)
    (hoff : ∀ x : N ⋊[φ] S, x.right ≠ 1 → χ x = (Θ : N ⋊[φ] S → k) x) :
    χ ∈ irreducibleCharacters k (N ⋊[φ] S) := by
  classical
  -- `N` is the kernel of the projection onto `S`, which has index `|S|`
  let e : N ≃* (rightHom : N ⋊[φ] S →* S).ker := mulEquivKerRightHom
  have hidx : (rightHom : N ⋊[φ] S →* S).ker.index = Nat.card S := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr rightHom_surjective, Subgroup.card_top]
  have hcomap (f : ClassFunction k (N ⋊[φ] S)) :
      comap (e : N →* _) (comap (rightHom : N ⋊[φ] S →* S).ker.subtype f) = comap inl f :=
    Subtype.ext (funext fun n => by simp [comap_apply, e])
  have hpair (f₁ f₂ : ClassFunction k (rightHom : N ⋊[φ] S →* S).ker) :
      characterPairing f₁ f₂ = characterPairing (comap (e : N →* _) f₁) (comap (e : N →* _) f₂) :=
    (characterPairing_comap_mulEquiv e f₁ f₂).symm
  -- `Y`, read on the kernel
  let Y' : ClassFunction k (rightHom : N ⋊[φ] S →* S).ker := comap (e.symm : _ →* N) Y
  have hYe : comap (e : N →* _) Y' = Y := Subtype.ext (funext fun n => by simp [Y', comap_apply])
  have hY' (x : (rightHom : N ⋊[φ] S →* S).ker) : Y'.val x = Y.val (x : N ⋊[φ] S).left := by
    simp [Y', comap_apply, e]
  refine mem_irreducibleCharacters_of_restrict_eq_of_eqOn_compl (Y := Y') ?_ ?_ hΘ ?_ (m := m) ?_
    ?_ ?_
  · have h : (Y' : _ → k) = (Y : N → k) ∘ e.symm := funext fun x => by simp [Y', comap_apply]
    exact h ▸ e.symm.comp_mem_irreducibleCharacters_iff.2 hY
  · -- conjugating `inl n` by `g` gives `inl (g.left * φ g.right n * g.left⁻¹)`
    intro g
    funext x
    obtain ⟨n, rfl⟩ := e.surjective x
    rw [Function.comp_apply, hY', hY', MulAut.conjNormal_apply]
    simp only [e, coe_mulEquivKerRightHom_apply, mul_inl_mul_inv, left_inl]
    rw [ClassFunction.mem_iff.mp Y.property]
    exact congrFun (hinv g.right) n
  · rw [hidx, hpair, hcomap]
    exact h₁
  · rw [hidx, hpair, hYe, hcomap]
    exact h₂
  · intro x
    obtain ⟨n, rfl⟩ := e.surjective x
    simp [hY', e, ← hres]
  · intro x hx
    exact hoff x fun h => hx (by simpa using h)

end TauCeti
