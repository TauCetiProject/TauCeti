/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import TauCeti.RepresentationTheory.Induction.ClassFunction
import TauCeti.RepresentationTheory.CharacterTable.CyclicExtension
import TauCeti.RepresentationTheory.CharacterTable.CyclicQuotient
import TauCeti.RepresentationTheory.CharacterTable.Restriction
import TauCeti.RepresentationTheory.Induction.Clifford.PrimeIndex

/-!
# Virtual character expansion in prime index

Gather irreducible characters extending a fixed stable character of a normal subgroup into a
packet indexed by the powers of a quotient character. The remaining irreducibles are induced.
This separates the coefficients that contribute on a generator coset from the induced terms.

The expansion uses Clifford theory and Gallagher's correspondence (Isaacs, *Character Theory of
Finite Groups*, Theorem 6.11 and Corollary 6.17).
-/

public section

open Finset

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Finite G]
  {N : Subgroup G} [N.Normal] {x : G}

/-- An irreducible character outside the range of the stable packets must be induced. -/
private theorem exists_indClassFun_eq_of_not_mem_packets (hp : N.index.Prime)
    {f : {i : Fin (Nat.card (ConjClasses N)) //
      irreducibleCharacter k i ∘ MulAut.conjNormal x = irreducibleCharacter k i} →
      Fin N.index → G → k}
    (hf : ∀ i, Set.SurjOn (f i) Set.univ (irreducibleCharactersOver k N
      (irreducibleCharacter k i.val))) {ψ : G → k} (hψ : ψ ∈ irreducibleCharacters k G)
    (hnot : ∀ i j, f i j ≠ ψ) : ∃ θ ∈ irreducibleCharacters k N, N.indClassFun θ = ψ := by
  let : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨θ, hθ, hψθ⟩ := exists_mem_irreducibleCharactersOver (N := N) hψ
  obtain ⟨i, rfl⟩ := exists_irreducibleCharacter_eq k hθ
  by_cases hi : irreducibleCharacter k i ∘ MulAut.conjNormal x = irreducibleCharacter k i
  · obtain ⟨j, -, hj⟩ := (hf ⟨i, hi⟩) hψθ
    exact (hnot _ _ hj).elim
  · have hm : ∃ n : N, irreducibleCharacter k i (MulAut.conjNormal x n) ≠
        irreducibleCharacter k i n := not_forall.mp (mt funext hi)
    rw [irreducibleCharactersOver_eq_singleton_indClassFun_of_index_prime hp hθ hm,
      Set.mem_singleton_iff] at hψθ
    exact ⟨_, hθ, hψθ.symm⟩

/-- Expand a virtual character in the packets of extensions of stable irreducibles of `N`,
plus induction of a virtual character of `N`. The coefficients within each packet are integers
indexed by the powers of a primitive quotient character. -/
theorem exists_sum_quotient_twists_add_indClassFun (hp : N.index.Prime) (hx : x ∉ N)
    {ζ : k} (hζ : IsPrimitiveRoot ζ N.index) {X : G → k} (hX : X ∈ virtualCharacters k G) :
    let I := {i : Fin (Nat.card (ConjClasses N)) //
      irreducibleCharacter k i ∘ MulAut.conjNormal x = irreducibleCharacter k i}
    ∃ (χ : I → G → k) (ε : G ⧸ N →* kˣ) (a : I → Fin N.index → ℤ) (Y : N → k),
      (∀ i, χ i ∈ irreducibleCharacters k G) ∧
      (∀ i (n : N), χ i n = irreducibleCharacter k i.val n) ∧
      (ε (QuotientGroup.mk' N x) : k) = ζ ∧ Y ∈ virtualCharacters k N ∧
      X = (∑ᶠ i, ∑ j, (a i j : k) • fun g => χ i g * (ε (QuotientGroup.mk' N g) : k) ^ j.val) +
        N.indClassFun Y := by
  classical
  let : Invertible (Nat.card G : k) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fact N.index.Prime := ⟨hp⟩
  let I := {i : Fin (Nat.card (ConjClasses N)) //
    irreducibleCharacter k i ∘ MulAut.conjNormal x = irreducibleCharacter k i}
  let : Fintype I := Fintype.ofFinite I
  have hgen := zpowers_eq_top_of_prime_card N.index_eq_card.symm
    (show QuotientGroup.mk' N x ≠ 1 from fun h => hx ((QuotientGroup.eq_one_iff x).mp h))
  obtain ⟨ε, hε, -⟩ := exists_gallagher_bijOn_pow
    (one_mem_irreducibleCharacters (k := k) (G := G))
    (one_mem_irreducibleCharacters (k := k) (G := N)) (fun _ => rfl) hgen hζ
  choose χ hχ hres using fun i : I =>
    exists_irreducibleCharacter_extension_of_index_prime hp hx
      (irreducibleCharacter_mem k i.val) i.property
  have ht (i : I) := gallagher_bijOn_pow (hχ i) (irreducibleCharacter_mem k i.val)
    (congrFun (hres i)) ε (hε ▸ hζ)
  choose e he using fun p : I × Fin N.index =>
    exists_irreducibleCharacter_eq k
      (irreducibleCharactersOver_subset _ ((ht p.1).mapsTo (Set.mem_univ p.2)))
  have hrestrict (p : I × Fin N.index) : irreducibleCharacter k (e p) ∘ N.subtype =
      irreducibleCharacter k p.1.val := by
    rw [he]
    funext n
    have hq := (QuotientGroup.eq_one_iff (N := N) (n : G)).mpr n.property
    simpa [Function.comp_apply, hq] using congrFun (hres p.1) n
  have hinj : Function.Injective e := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hi : i = i' := Subtype.ext (irreducibleCharacter_injective (k := k)
      ((hrestrict (i, j)).symm.trans (h ▸ hrestrict (i', j'))))
    subst i'
    exact Prod.ext rfl ((ht i).injOn (Set.mem_univ j) (Set.mem_univ j')
      ((he (i, j)).symm.trans (h ▸ he (i, j'))))
  let s := univ.image e
  have hother (j : Fin (Nat.card (ConjClasses G))) (hj : j ∈ sᶜ) : ∃ θ ∈ irreducibleCharacters k N,
      N.indClassFun θ = irreducibleCharacter k j := by
    refine exists_indClassFun_eq_of_not_mem_packets hp (fun i => (ht i).surjOn)
      (irreducibleCharacter_mem k j) fun i l hl => ?_
    exact mem_compl.mp hj (mem_image.mpr ⟨(i, l), mem_univ _,
      irreducibleCharacter_injective (k := k) ((he _).trans hl)⟩)
  obtain ⟨c, hc⟩ := mem_virtualCharacters_iff.mp hX
  choose θ hθ hθeq using fun j : ↥(sᶜ) => hother j.val j.property
  let Y := ∑ j : ↥(sᶜ), c j.val • θ j
  refine ⟨χ, ε, fun i j => c (e (i, j)), Y, hχ, fun i => congrFun (hres i), hε,
    sum_mem fun j _ => zsmul_mem (irreducibleCharacters_subset_virtualCharacters (hθ j)) _, ?_⟩
  have hY : N.indClassFun Y = ∑ j ∈ sᶜ, (c j : k) • irreducibleCharacter k j := by
    rw [← Subgroup.indClassFunAddHom_apply]
    simp only [Y, map_sum, map_zsmul, Subgroup.indClassFunAddHom_apply, hθeq,
      Int.cast_smul_eq_zsmul k]
    exact sum_attach sᶜ (fun j => c j • irreducibleCharacter k j)
  rw [finsum_eq_sum_of_fintype, hc, hY, ← sum_compl_add_sum s,
    add_comm (∑ j ∈ sᶜ, _), add_right_cancel_iff, sum_image hinj.injOn, Fintype.sum_prod_type]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ =>
    congrArg (fun f => (c (e (i, j)) : k) • f) (he (i, j))

end TauCeti
