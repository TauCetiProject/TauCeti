/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
import TauCeti.RepresentationTheory.CharacterTable.Automorphism
import TauCeti.RepresentationTheory.LinHom.SubgroupSum

/-!
# Gallagher's correspondence

Let `N` be a normal subgroup of a finite group `G`, let `θ` be an irreducible character of `N` and
let `χ` be an irreducible character of `G` extending `θ`, that is, `χ n = θ n` for `n ∈ N`.
**Gallagher's theorem** says that `β ↦ χ · (β ∘ π)`, for `π : G → G ⧸ N`, is a bijection from the
irreducible characters of `G ⧸ N` onto the irreducible characters of `G` lying over `θ`
(`TauCeti.gallagher_bijOn`). Here a character `ψ` of `G` lies over `θ` when
`∑ n ∈ N, ψ n θ n⁻¹ ≠ 0`; over an algebraically closed field of characteristic zero this says
that `θ` occurs in the restriction of `ψ` to `N`. These form the set
`TauCeti.irreducibleCharactersOver`.

The proof is character-theoretic. Its key input is that, over an algebraically closed field of
characteristic zero, `χ` has the same unnormalized self-pairing on every coset of `N`:
`∑ n ∈ N, χ(g n) χ((g n)⁻¹) = |N|` for every `g`
(`Representation.sum_character_mul_mul_character_mul_inv_eq_card`). Indeed, writing `χ` as the
character of `ρ` on `V`, the left side is the trace of `σ g ∘ S` on `End V`, where `σ` is the
conjugation action of `G` and `S = ∑ n ∈ N, σ n`. Every value of `S` commutes with `N`, hence is a
scalar since `ρ` restricts irreducibly to `N`, hence is fixed by `σ g`; so the trace is that of
`S`, which is the unnormalized self-pairing `∑ n ∈ N, θ(n) θ(n⁻¹) = |N|` of `θ`.
Consequently multiplication by `χ` preserves the
character pairing of functions inflated from `G ⧸ N`, up to the normalisation
(`Representation.sum_mul_comp_mk_mul_mul_comp_mk_inv`), which gives irreducibility and
injectivity; the column orthogonality of `G ⧸ N` gives surjectivity.

## Main results

* `Representation.sum_character_mul_mul_character_mul_inv_eq_card`: over an algebraically closed
  field of characteristic zero, a character restricting irreducibly to `N` has unnormalized
  self-pairing `|N|` on every coset of `N`.
* `Representation.sum_mul_comp_mk_mul_mul_comp_mk_inv`: multiplication by such a character is an
  isometry on functions inflated from `G ⧸ N`.
* `TauCeti.gallagher_bijOn`: **Gallagher's correspondence** `Irr(G ⧸ N) ≃ Irr(G | θ)`,
  `β ↦ χ · (β ∘ π)`.
* `TauCeti.gallagher_bijOn_bot`: the case `N = 1` for a linear character `χ`, a permutation of
  the irreducible characters of `G` read through `G ⧸ ⊥`.
* `TauCeti.gallagher_bijOn_of_surjective`: the same with `G ⧸ N` replaced by the target `Q` of a
  surjection `f : G →* Q` with kernel `N`, `β ↦ χ · (β ∘ f)`.
* `TauCeti.gallagher_bijOn_semidirectProduct`: the case `N = Γ` of `G = Γ ⋊[φ] S`,
  `Irr(S) ≃ Irr(Γ ⋊ S | χ)`, `β ↦ (g ↦ ψ g · β g.right)` for an irreducible extension `ψ` of `χ`.
* `TauCeti.irreducibleCharactersOver_eq_setOf_restrict_eq_of_isMulCommutative` and
  `TauCeti.card_irreducibleCharacter_extensions_of_isMulCommutative`: for an abelian quotient, the
  characters over `θ` are exactly the irreducible extensions of `θ`, and there are `|G : N|` of
  them.

## References

* G. Glauberman, *Correspondences of characters for relatively prime operator groups*,
  Canad. J. Math. 20 (1968), Theorem 2 (c), p. 1470, citing Gallagher.
* I. M. Isaacs, *Character Theory of Finite Groups*, Corollary 6.17.
-/

public section

namespace TauCeti

open Module Finset

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

section Coset

variable {V : Type*} [AddCommGroup V] [Module k V]

variable [IsAlgClosed k] [CharZero k]

/-- **A character restricting irreducibly to `N` has unnormalized self-pairing `|N|` on every
coset of `N`**: over an algebraically closed field of characteristic zero, if the restriction to
`N` of the character of `ρ` is an irreducible character of `N`, then
`∑ n ∈ N, χ(g n) χ((g n)⁻¹) = |N|` for every `g ∈ G`. The space `V` need not be assumed
finite-dimensional. -/
theorem _root_.Representation.sum_character_mul_mul_character_mul_inv_eq_card
    (ρ : Representation k G V) (N : Subgroup G) [Fintype N]
    (hθ : (fun n : N => ρ.character n) ∈ irreducibleCharacters k N) (g : G) :
    ∑ n : N, ρ.character (g * n) * ρ.character (g * n)⁻¹ = Nat.card N := by
  -- The character is nonzero at `1`, as its restriction to `N` is irreducible.
  have h1 : ρ.character (1 : G) ≠ 0 := by
    simpa only [Subgroup.coe_one] using apply_one_ne_zero_of_mem_irreducibleCharacters hθ
  have : FiniteDimensional k V := ρ.finiteDimensional_of_character_ne_zero h1
  have hN : (Nat.card N : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card N : k) := invertibleOfNonzero hN
  let ρN : Representation k N V := ρ.comp N.subtype
  have hnorm : ∑ n : N, ρ.character n * ρ.character (n : G)⁻¹ = Nat.card N := by
    simpa using sum_mul_inv_self_of_mem_irreducibleCharacters hθ
  -- The norm of `θ` is `1`, so the `N`-equivariant endomorphisms of `V` form a line.
  have hfin : finrank k (Representation.IntertwiningMap ρN ρN) = 1 := by
    have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρN ρN
    simp only [ρN, Representation.character_comp, Function.comp_apply, Subgroup.subtype_apply,
      Subgroup.coe_inv, hnorm, inv_mul_cancel₀ hN] at h
    exact_mod_cast h.symm
  -- The left side is the trace of `σ g ∘ S` for the conjugation action `σ` of `G` on `End V` and
  -- `S = ∑ n ∈ N, σ n` (`Representation.sum_character_mul_mul_character_mul_inv_eq_trace`). The
  -- values of `S` are scalars, hence fixed by `σ g`, so the trace is that of `S`: the case `g = 1`.
  have hS : Representation.linHom ρ ρ g * Representation.norm ((Representation.linHom ρ ρ).comp
      N.subtype) = Representation.norm ((Representation.linHom ρ ρ).comp N.subtype) := by
    rw [Representation.norm]
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply] using
      ρ.linHom_mul_sum_linHom_eq N hfin g
  have htr (x : G) := ρ.sum_character_mul_mul_character_mul_inv_eq_trace ρ N.subtype x
  simp only [Subgroup.subtype_apply] at htr
  calc ∑ n : N, ρ.character (g * n) * ρ.character (g * n)⁻¹
      = LinearMap.trace k _
          (Representation.linHom ρ ρ 1 *
            Representation.norm ((Representation.linHom ρ ρ).comp N.subtype)) := by
        rw [htr, hS, map_one, one_mul]
    _ = Nat.card N := by
        rw [← htr]
        simpa only [one_mul] using hnorm

/-- **Multiplication by a character restricting irreducibly to a normal subgroup `N` is an
isometry on functions inflated from `G ⧸ N`**: if `χ` is the character of `ρ` and its restriction
to `N` is irreducible, then for all `β β' : G ⧸ N → k`,
`∑ g, χ g β g · χ g⁻¹ β' g⁻¹ = |N| ∑ q, β q β' q⁻¹`. -/
theorem _root_.Representation.sum_mul_comp_mk_mul_mul_comp_mk_inv [Fintype G]
    (ρ : Representation k G V) (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]
    (hθ : (fun n : N => ρ.character n) ∈ irreducibleCharacters k N) (β β' : G ⧸ N → k) :
    ∑ g : G, ρ.character g * β g * (ρ.character g⁻¹ * β' (g⁻¹ : G)) =
      Nat.card N * ∑ q : G ⧸ N, β q * β' q⁻¹ := by
  classical
  -- Group the left side by cosets of `N`: the coset of `q` contributes `β q β' q⁻¹` times the
  -- norm of `χ` on that coset. The fibre of `q` is the coset `q.out N`, on which `χ` has
  -- norm `|N|`.
  have hfib (q : G ⧸ N) :
      ∑ g ∈ univ.filter (fun g : G => (g : G ⧸ N) = q), ρ.character g * ρ.character g⁻¹ =
        Nat.card N := by
    rw [← ρ.sum_character_mul_mul_character_mul_inv_eq_card N hθ q.out]
    symm
    refine Finset.sum_bij (fun n _ => q.out * n) (fun n _ => ?_) (fun n _ m _ h => ?_)
      (fun g hg => ?_) (fun n _ => rfl)
    · rw [mem_filter, QuotientGroup.mk_mul_of_mem _ n.property, QuotientGroup.out_eq']
      exact ⟨mem_univ _, rfl⟩
    · exact Subtype.ext (mul_left_cancel h)
    · refine ⟨⟨q.out⁻¹ * g, ?_⟩, mem_univ _, mul_inv_cancel_left _ _⟩
      refine QuotientGroup.eq.mp ?_
      rw [QuotientGroup.out_eq', (mem_filter.mp hg).2]
  rw [← Finset.sum_fiberwise univ (fun g : G => (g : G ⧸ N)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← hfib q, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [(mem_filter.mp hg).2, QuotientGroup.mk_inv, (mem_filter.mp hg).2]
  ring

end Coset

section Gallagher

variable [Finite G] [IsAlgClosed k] [CharZero k]

variable {N : Subgroup G} [N.Normal] {χ : G → k}

/-- **The product of `χ` with an inflated irreducible character is irreducible**, when `χ` is an
irreducible character of `G` restricting irreducibly to the normal subgroup `N`. -/
theorem mul_comp_mk_mem_irreducibleCharacters (hχ : χ ∈ irreducibleCharacters k G)
    (hθ : (fun n : N => χ n) ∈ irreducibleCharacters k N) {β : G ⧸ N → k}
    (hβ : β ∈ irreducibleCharacters k (G ⧸ N)) :
    (fun g : G => χ g * β g) ∈ irreducibleCharacters k G := by
  -- Its norm is that of `β` by `Representation.sum_mul_comp_mk_mul_mul_comp_mk_inv`.
  classical
  have := Fintype.ofFinite G
  obtain ⟨d, ρ, -, rfl⟩ := mem_irreducibleCharacters_iff.mp hχ
  obtain ⟨W, hW⟩ := irreducibleCharacters_subset_range hβ
  have hv : (fun g : G => ρ.character g * β g) ∈ virtualCharacters k G :=
    mul_mem_virtualCharacters (character_mem_virtualCharacters (FDRep.of ρ))
      (hW ▸ comp_mem_virtualCharacters (QuotientGroup.mk' N) (character_mem_virtualCharacters W))
  have hG : (Nat.card G : k) = Nat.card (G ⧸ N) * Nat.card N := by
    exact_mod_cast Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hN0 : (Nat.card N : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hQ0 : (Nat.card (G ⧸ N) : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨m, σ, -, rfl⟩ := mem_irreducibleCharacters_iff.mp hβ
  refine mem_irreducibleCharacters_of_characterPairing_self_eq_one
    (f := ⟨_, virtualCharacters_le_classFunction hv⟩) hv ?_ (n := d * m) ?_
  · rw [ClassFunction.characterPairing_apply]
    dsimp only
    rw [ρ.sum_mul_comp_mk_mul_mul_comp_mk_inv N hθ,
      sum_mul_inv_self_of_mem_irreducibleCharacters hβ, hG]
    field_simp
  · simp

/-- **Every irreducible character of `G` over `θ` is a product `χ · (β ∘ π)`**, for `χ` an
irreducible character of `G` extending the irreducible character `θ` of the normal subgroup `N`. -/
theorem exists_mem_irreducibleCharacters_eq_mul_comp_mk {θ : N → k}
    (hχ : χ ∈ irreducibleCharacters k G) (hres : ∀ n : N, χ n = θ n)
    (hθ : θ ∈ irreducibleCharacters k N) {ψ : G → k} (hψ : ψ ∈ irreducibleCharactersOver k N θ) :
    ∃ β ∈ irreducibleCharacters k (G ⧸ N), (fun g : G => χ g * β g) = ψ := by
  -- If `ψ` were orthogonal to every `χ · β`, it would be orthogonal to `χ · ρ_{G ⧸ N}`, where
  -- `ρ_{G ⧸ N} = ∑ β(1) β` is the regular character, which is `|G : N|` on `N` and `0` elsewhere;
  -- but that pairing is `|G : N|` times `∑ n ∈ N, ψ n θ n⁻¹ ≠ 0`.
  classical
  have := Fintype.ofFinite G
  have hθ' : (fun n : N => χ n) ∈ irreducibleCharacters k N := funext hres ▸ hθ
  obtain ⟨hψ, hsum⟩ := mem_irreducibleCharactersOver_iff_sum.mp hψ
  by_contra hcon
  have hzero (i : Fin (Nat.card (ConjClasses (G ⧸ N)))) :
      ∑ g : G, ψ g * (χ g⁻¹ * irreducibleCharacter k i ((g⁻¹ : G) : G ⧸ N)) = 0 :=
    sum_mul_inv_eq_zero_of_mem_irreducibleCharacters hψ
      (mul_comp_mk_mem_irreducibleCharacters hχ hθ' (irreducibleCharacter_mem k i))
      fun h' => hcon ⟨_, irreducibleCharacter_mem k i, h'.symm⟩
  have hQ0 : (Nat.card (G ⧸ N) : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card (G ⧸ N) : k) := invertibleOfNonzero hQ0
  -- Column orthogonality of `G ⧸ N` at the identity.
  have hcol (g : G) : ∑ i, (characterDegree k (G := G ⧸ N) i : k) *
      irreducibleCharacter k i ((g⁻¹ : G) : G ⧸ N) =
        if g ∈ N then (Nat.card (G ⧸ N) : k) else 0 := by
    have h := sum_finrank_mul_character (irreducibleRepresentation k (G := G ⧸ N))
      (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) (g⁻¹ : G)
    simpa [QuotientGroup.eq_one_iff] using h
  refine hsum (mul_left_cancel₀ hQ0 ?_)
  calc (Nat.card (G ⧸ N) : k) * ∑ n : N, ψ n * θ n⁻¹
      = ∑ g : G, if g ∈ N then ψ g * χ g⁻¹ * Nat.card (G ⧸ N) else 0 := by
        rw [← Finset.sum_filter, Finset.mul_sum,
          Finset.sum_subtype (p := (· ∈ N)) (univ.filter (· ∈ N)) (by simp)]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← hres n⁻¹]
        simp only [Subgroup.coe_inv]
        ring
    _ = ∑ i, (characterDegree k (G := G ⧸ N) i : k) *
          ∑ g : G, ψ g * (χ g⁻¹ * irreducibleCharacter k i ((g⁻¹ : G) : G ⧸ N)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← mul_ite_zero, ← hcol g, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = (Nat.card (G ⧸ N) : k) * 0 := by
        rw [Finset.sum_eq_zero fun i _ => by rw [hzero i, mul_zero], mul_zero]

/-- **Gallagher's correspondence.** Let `N` be a normal subgroup of the finite group `G`, `θ` an
irreducible character of `N` and `χ` an irreducible character of `G` extending `θ`. Then
`β ↦ χ · (β ∘ π)` is a bijection from the irreducible characters of `G ⧸ N` onto the irreducible
characters of `G` lying over `θ`, over an algebraically closed field of characteristic zero. -/
theorem gallagher_bijOn {θ : N → k} (hχ : χ ∈ irreducibleCharacters k G)
    (hθ : θ ∈ irreducibleCharacters k N) (hres : ∀ n : N, χ n = θ n) :
    Set.BijOn (fun (β : G ⧸ N → k) (g : G) => χ g * β g)
      (irreducibleCharacters k (G ⧸ N)) (irreducibleCharactersOver k N θ) := by
  -- Multiplication by `χ` preserves the character pairing of inflated functions, so the products
  -- are irreducible and pairwise distinct.
  classical
  have := Fintype.ofFinite G
  have hθ' : (fun n : N => χ n) ∈ irreducibleCharacters k N := funext hres ▸ hθ
  have hN0 : (Nat.card N : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hQ0 : (Nat.card (G ⧸ N) : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨d, ρ, -, rfl⟩ := mem_irreducibleCharacters_iff.mp hχ
  have hiso := ρ.sum_mul_comp_mk_mul_mul_comp_mk_inv N hθ'
  refine ⟨fun β hβ => mem_irreducibleCharactersOver_iff_sum.mpr
      ⟨mul_comp_mk_mem_irreducibleCharacters hχ hθ' hβ, ?_⟩,
    fun β hβ β' hβ' heq => ?_,
    fun ψ hψ => exists_mem_irreducibleCharacters_eq_mul_comp_mk hχ hres hθ hψ⟩
  · -- `χ · β` lies over `θ`: on `N` it is `β(1) θ`.
    have h : ∑ n : N, ρ.character n * β (n : G) * θ n⁻¹ = β 1 * Nat.card N := by
      rw [← sum_mul_inv_self_of_mem_irreducibleCharacters hθ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [(QuotientGroup.eq_one_iff (n : G)).mpr n.property, hres]
      ring
    rw [h]
    exact mul_ne_zero (apply_one_ne_zero_of_mem_irreducibleCharacters hβ) hN0
  · -- Distinct `β` give orthogonal, hence distinct, products.
    by_contra hne
    have h1 := hiso β β'
    have h2 := hiso β β
    rw [sum_mul_inv_eq_zero_of_mem_irreducibleCharacters hβ hβ' hne] at h1
    rw [sum_mul_inv_self_of_mem_irreducibleCharacters hβ] at h2
    have h12 : ∑ g : G, ρ.character g * β g * (ρ.character g⁻¹ * β' (g⁻¹ : G)) =
        ∑ g : G, ρ.character g * β g * (ρ.character g⁻¹ * β (g⁻¹ : G)) :=
      Finset.sum_congr rfl fun g _ => by
        have h := congrFun heq g⁻¹
        dsimp only at h
        rw [h]
    rw [h12, h2, mul_zero] at h1
    exact mul_ne_zero hN0 hQ0 h1

/-- **Gallagher's correspondence for `N = 1`.** For a linear character `χ`, every irreducible
character lies over the trivial character of `⊥`, so multiplication by `χ`, read through `G ⧸ ⊥`,
maps the irreducible characters of `G ⧸ ⊥` bijectively onto those of `G`. -/
theorem gallagher_bijOn_bot (hχ : χ ∈ irreducibleCharacters k G) (h1 : χ 1 = 1) :
    Set.BijOn (fun (β : G ⧸ (⊥ : Subgroup G) → k) (g : G) => χ g * β g)
      (irreducibleCharacters k (G ⧸ (⊥ : Subgroup G))) (irreducibleCharacters k G) := by
  have hθ : (fun _ => 1 : (⊥ : Subgroup G) → k) ∈ irreducibleCharacters k (⊥ : Subgroup G) := by
    simp
  have h := gallagher_bijOn hχ hθ fun n => by
    rw [Subgroup.mem_bot.mp n.property, h1]
  rwa [irreducibleCharactersOver_bot one_ne_zero] at h

/-- **Gallagher's correspondence along a surjection.** Let `f : G →* Q` be a surjection from the
finite group `G`, `θ` an irreducible character of its kernel and `χ` an irreducible character of
`G` extending `θ`. Then `β ↦ χ · (β ∘ f)` is a bijection from the irreducible characters of `Q`
onto the irreducible characters of `G` lying over `θ`. -/
theorem gallagher_bijOn_of_surjective {Q : Type*} [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) {θ : f.ker → k} (hχ : χ ∈ irreducibleCharacters k G)
    (hθ : θ ∈ irreducibleCharacters k f.ker) (hres : ∀ n : f.ker, χ n = θ n) :
    Set.BijOn (fun (β : Q → k) (g : G) => χ g * β (f g)) (irreducibleCharacters k Q)
      (irreducibleCharactersOver k f.ker θ) := by
  let q := QuotientGroup.quotientKerEquivOfSurjective f hf
  -- `q` is `QuotientGroup.kerLift f` on the quotient, which sends `g` to `f g` by definition.
  have hq (g : G) : q g = f g := QuotientGroup.kerLift_mk f g
  convert (gallagher_bijOn hχ hθ hres).comp q.bijOn_comp_irreducibleCharacters using 1
  funext β g
  simp only [Function.comp_apply, hq]

open SemidirectProduct in
/-- **Gallagher's correspondence over a semidirect product.** If an irreducible character `ψ` of
`Γ ⋊[φ] S` restricts to an irreducible character `χ` of `Γ`, then `β ↦ (g ↦ ψ g · β g.right)` is
a bijection from the irreducible characters of `S` onto the irreducible characters of `Γ ⋊[φ] S`
lying over `χ`, read on the kernel of `rightHom` through `mulEquivKerRightHom`. -/
theorem gallagher_bijOn_semidirectProduct {Γ S : Type*} [Group Γ] [Group S] [Finite Γ] [Finite S]
    {φ : S →* MulAut Γ} {χ : Γ → k} {ψ : Γ ⋊[φ] S → k}
    (hψ : ψ ∈ irreducibleCharacters k (Γ ⋊[φ] S)) (hχ : χ ∈ irreducibleCharacters k Γ)
    (hres : ψ ∘ inl = χ) :
    Set.BijOn (fun (β : S → k) (g : Γ ⋊[φ] S) => ψ g * β g.right) (irreducibleCharacters k S)
      (irreducibleCharactersOver k (rightHom : Γ ⋊[φ] S →* S).ker
        (χ ∘ mulEquivKerRightHom.symm)) := by
  refine gallagher_bijOn_of_surjective rightHom rightHom_surjective hψ
    (mulEquivKerRightHom.symm.comp_mem_irreducibleCharacters_iff.2 hχ) fun n => ?_
  rw [← hres, Function.comp_apply, Function.comp_apply, ← coe_mulEquivKerRightHom_apply,
    MulEquiv.apply_symm_apply]

/-- If an irreducible character extends across an abelian quotient, an irreducible character lies
above it if and only if it restricts to it: the inflated characters of the quotient are linear. -/
theorem irreducibleCharactersOver_eq_setOf_restrict_eq_of_isMulCommutative
    [IsMulCommutative (G ⧸ N)] {θ : N → k} (hχ : χ ∈ irreducibleCharacters k G)
    (hθ : θ ∈ irreducibleCharacters k N) (hres : ∀ n : N, χ n = θ n) :
    irreducibleCharactersOver k N θ =
      {ψ | ψ ∈ irreducibleCharacters k G ∧ ∀ n : N, ψ n = θ n} := by
  ext ψ
  refine ⟨fun hψ => ⟨irreducibleCharactersOver_subset θ hψ, fun n => ?_⟩,
    fun ⟨hψ, hψres⟩ => mem_irreducibleCharactersOver_of_restrict_eq hψ hθ hψres⟩
  obtain ⟨β, hβ, rfl⟩ := (gallagher_bijOn hχ hθ hres).surjOn hψ
  simp [(QuotientGroup.eq_one_iff (n : G)).mpr n.property, hres,
    apply_one_eq_one_of_mem_irreducibleCharacters_of_isMulCommutative hβ]

open scoped IsMulCommutative in
/-- The number of irreducible extensions of an extendible irreducible character across an abelian
quotient is the index of the subgroup. -/
theorem card_irreducibleCharacter_extensions_of_isMulCommutative [IsMulCommutative (G ⧸ N)]
    {θ : N → k} (hχ : χ ∈ irreducibleCharacters k G) (hθ : θ ∈ irreducibleCharacters k N)
    (hres : ∀ n : N, χ n = θ n) :
    Nat.card {ψ : G → k | ψ ∈ irreducibleCharacters k G ∧ ∀ n : N, ψ n = θ n} = N.index := by
  let : Invertible (Nat.card (G ⧸ N) : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [← irreducibleCharactersOver_eq_setOf_restrict_eq_of_isMulCommutative hχ hθ hres,
    ← Nat.card_congr ((gallagher_bijOn hχ hθ hres).equiv _),
    card_irreducibleCharacters, N.index_eq_card]
  exact Nat.card_congr ConjClasses.mkEquiv.symm

end Gallagher

end TauCeti
