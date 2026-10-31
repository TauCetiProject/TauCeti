/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Exchange
public import TauCeti.GroupTheory.Coxeter.ExchangeCondition

/-!
# The Coxeter system of a Tits system

The Weyl group of a Tits system is a Coxeter group, with the prescribed simple reflections.
Its Coxeter matrix records the orders of products of pairs of simple reflections, with zero
representing infinite order. The Coxeter length agrees with the word length already used to
control multiplication of Bruhat cells. Consequently the Coxeter-group API applies to the
Weyl quotient of any BN-pair, without finiteness assumptions.

The construction combines `TitsSystem.exists_eraseIdx_prod_eq_of_wordLength_lt_right`, the
exchange condition obtained from Bruhat cells, with `CoxeterSystem.ofExchange`, the recognition
theorem for Coxeter presentations. No additional relations or exchange axioms are assumed.

The Weyl group is **irreducible**, `TauCeti.TitsSystem.IsIrreducible`, if every subset `J` of
the simple reflections `S` that commutes elementwise with its complement is empty or all of `S`.
For nonempty `S` this says exactly that the Coxeter graph of `(W, S)` is connected.

## Main definitions

* `TauCeti.TitsSystem.coxeterMatrix`: the Coxeter matrix of the simple reflections.
* `TauCeti.TitsSystem.coxeterSystem`: the Coxeter system on the Weyl group.
* `TauCeti.TitsSystem.IsIrreducible`: every set of simple reflections commuting elementwise with
  its complement is empty or everything.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, no. 4,
  Theorem 2, and §1, no. 6.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.3.
-/

public section

namespace TauCeti.TitsSystem

universe u v

variable {G : Type u} [Group G] (T : TitsSystem G)

noncomputable section

/-- The Coxeter matrix of a Tits system: the entry at `s, t` is the order of `s * t` in
its Weyl group. An entry zero denotes infinite order. -/
def coxeterMatrix : CoxeterMatrix T.simple where
  M := Matrix.of fun s t ↦ orderOf ((s : T.WeylGroup) * t)
  isSymm := by
    apply Matrix.ext
    intro s t
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    have h := orderOf_inv ((s : T.WeylGroup) * t)
    simpa only [mul_inv_rev, T.inv_simple s.property,
      T.inv_simple t.property] using h
  diagonal s := by simp [T.simple_sq_eq_one s.property]
  off_diagonal s t hst := by
    intro horder
    have h := orderOf_eq_one_iff.mp horder
    apply hst
    apply Subtype.ext
    exact (eq_inv_of_mul_eq_one_left h).trans (T.inv_simple t.property)

/-- The entries of the Coxeter matrix are the orders of the products of simple reflections. -/
@[simp]
theorem coxeterMatrix_apply (s t : T.simple) :
    T.coxeterMatrix s t = orderOf ((s : T.WeylGroup) * t) :=
  (rfl)

/-- The Weyl group of a Tits system is **irreducible** if every set `J` of simple reflections that
commutes elementwise with its complement is empty or all of `S`. For nonempty `S` this says exactly
that the Coxeter graph of `(W, S)` is connected. -/
def IsIrreducible : Prop :=
  ∀ J : Set T.simple, (∀ s ∈ J, ∀ t ∉ J, (s : T.WeylGroup) * t = t * s) → J = ∅ ∨ J = Set.univ

/-- Unfolds `TauCeti.TitsSystem.IsIrreducible`. -/
theorem isIrreducible_iff : T.IsIrreducible ↔
    ∀ J : Set T.simple, (∀ s ∈ J, ∀ t ∉ J, (s : T.WeylGroup) * t = t * s) →
      J = ∅ ∨ J = Set.univ :=
  Iff.rfl

/-- Irreducibility transfers along an isomorphism of Weyl groups identifying the simple
reflections. -/
theorem IsIrreducible.of_mulEquiv {T : TitsSystem G} (hirr : T.IsIrreducible) {H : Type v}
    [Group H] {T' : TitsSystem H} (e : T'.WeylGroup ≃* T.WeylGroup)
    (he : e ⁻¹' T.simple = T'.simple) : T'.IsIrreducible := by
  have hmem : ∀ w, w ∈ T'.simple ↔ e w ∈ T.simple := fun w ↦ by rw [← he, Set.mem_preimage]
  refine T'.isIrreducible_iff.mpr fun J hJ ↦ ?_
  -- Transport `J` to the simple reflections of `T`, where irreducibility applies.
  let J₀ : Set T.simple := {s | ∃ t ∈ J, e t = s}
  have hJ₀ : ∀ s ∈ J₀, ∀ t ∉ J₀, (s : T.WeylGroup) * t = t * s := by
    rintro s ⟨s', hs', hs⟩ t ht
    have ht' : (⟨e.symm t, (hmem _).mpr (by simp)⟩ : T'.simple) ∉ J :=
      fun h ↦ ht ⟨_, h, by simp⟩
    simpa [hs] using congrArg e (hJ s' hs' _ ht')
  have hmemJ₀ : ∀ s : T'.simple, s ∈ J ↔ (⟨e s, (hmem _).mp s.2⟩ : T.simple) ∈ J₀ := by
    refine fun s ↦ ⟨fun hs ↦ ⟨s, hs, rfl⟩, ?_⟩
    rintro ⟨t, ht, hts⟩
    rwa [← Subtype.ext (e.injective hts)]
  rcases T.isIrreducible_iff.mp hirr J₀ hJ₀ with h | h
  · exact Or.inl (Set.eq_empty_of_forall_notMem fun s hs ↦ by simpa [h] using (hmemJ₀ s).mp hs)
  · exact Or.inr (Set.eq_univ_of_forall fun s ↦ (hmemJ₀ s).mpr (by simp [h]))

/-- The canonical map from the Coxeter presentation to the Weyl quotient. -/
private def coxeterPresentationHom : T.coxeterMatrix.Group →* T.WeylGroup :=
  T.coxeterMatrix.toCoxeterSystem.lift
    ⟨Subtype.val, fun s t ↦ by simp only [coxeterMatrix_apply, pow_orderOf_eq_one]⟩

private theorem coxeterPresentationHom_simple (s : T.simple) :
    T.coxeterPresentationHom (T.coxeterMatrix.toCoxeterSystem.simple s) = s :=
  CoxeterSystem.lift_apply_simple _ _ _

private theorem coxeterPresentationHom_wordProd (l : List T.simple) :
    T.coxeterPresentationHom (T.coxeterMatrix.toCoxeterSystem.wordProd l) =
      (l.map Subtype.val).prod := by
  simp only [CoxeterSystem.wordProd, map_list_prod, List.map_map, Function.comp_def,
    coxeterPresentationHom_simple]

private theorem wordLength_isLeast (w : T.WeylGroup) :
    IsLeast {n | ∃ l : List T.simple,
      T.coxeterPresentationHom (T.coxeterMatrix.toCoxeterSystem.wordProd l) = w ∧
        l.length = n} (T.simpleGenerators.wordLength w) := by
  constructor
  · obtain ⟨l, hl, hlen, hprod⟩ := T.exists_prod_eq_of_wordLength w
    refine ⟨l.attach.map (fun s ↦ (⟨s.val, hl s.val s.property⟩ : T.simple)), ?_, by simp [hlen]⟩
    rw [coxeterPresentationHom_wordProd, List.map_map]
    simpa only [Function.comp_def, List.attach_map_subtype_val] using hprod
  · rintro n ⟨l, hl, rfl⟩
    rw [coxeterPresentationHom_wordProd] at hl
    rw [← hl]
    have hs : ∀ x ∈ l.map Subtype.val, x ∈ T.simple := by
      rintro x hx
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
      exact s.property
    exact (T.wordLength_prod_le hs).trans_eq (List.length_map _)

private theorem coxeterPresentationHom_exchange (l : List T.simple) (s : T.simple)
    (hlen : T.simpleGenerators.wordLength
      (T.coxeterPresentationHom (T.coxeterMatrix.toCoxeterSystem.wordProd l)) = l.length)
    (hshort : T.simpleGenerators.wordLength
      (T.coxeterPresentationHom (T.coxeterMatrix.toCoxeterSystem.wordProd l *
        T.coxeterMatrix.toCoxeterSystem.simple s)) ≤ l.length) :
    ∃ j < l.length,
      T.coxeterPresentationHom (T.coxeterMatrix.toCoxeterSystem.wordProd (l.eraseIdx j)) =
        T.coxeterPresentationHom (T.coxeterMatrix.toCoxeterSystem.wordProd l *
          T.coxeterMatrix.toCoxeterSystem.simple s) := by
  simp only [map_mul, coxeterPresentationHom_wordProd, coxeterPresentationHom_simple] at *
  have hlt : T.simpleGenerators.wordLength ((l.map Subtype.val).prod * s) <
      T.simpleGenerators.wordLength (l.map Subtype.val).prod := by
    have hne := T.wordLength_mul_simple_ne (l.map Subtype.val).prod s.property
    omega
  have hs : ∀ x ∈ l.map Subtype.val, x ∈ T.simple := by
    rintro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact t.property
  obtain ⟨j, hj, heq⟩ :=
    T.exists_eraseIdx_prod_eq_of_wordLength_lt_right hs s.property hlt
  exact ⟨j, by simpa using hj, by simpa only [List.eraseIdx_map] using heq.symm⟩

/-- The Weyl quotient of a Tits system, equipped with its canonical Coxeter system indexed
by the prescribed simple reflections. -/
def coxeterSystem : CoxeterSystem T.coxeterMatrix T.WeylGroup :=
  T.coxeterMatrix.toCoxeterSystem.ofExchange T.coxeterPresentationHom
    T.simpleGenerators.wordLength
    (fun s t ↦ by simp only [coxeterPresentationHom_simple, coxeterMatrix_apply])
    T.wordLength_isLeast T.coxeterPresentationHom_exchange

/-- The simple generators of the Coxeter system are the original simple reflections of
the BN-pair, as elements of its Weyl quotient. -/
@[simp]
theorem coxeterSystem_simple (s : T.simple) : T.coxeterSystem.simple s = s := by
  rw [coxeterSystem, CoxeterSystem.ofExchange_simple, coxeterPresentationHom_simple]

/-- A Coxeter word evaluates to the product of its original simple reflections in the Weyl
quotient. -/
@[simp]
theorem coxeterSystem_wordProd (l : List T.simple) :
    T.coxeterSystem.wordProd l = (l.map Subtype.val).prod := by
  rw [coxeterSystem, CoxeterSystem.ofExchange_wordProd, coxeterPresentationHom_wordProd]

/-- Coxeter length is the word length governing the Bruhat multiplication laws. -/
@[simp]
theorem coxeterSystem_length (w : T.WeylGroup) :
    T.coxeterSystem.length w = T.simpleGenerators.wordLength w := by
  rw [coxeterSystem, CoxeterSystem.length_ofExchange]

/-- The Weyl group of every Tits system is a Coxeter group, with no rank or finiteness
assumptions. -/
instance : IsCoxeterGroup T.WeylGroup :=
  ⟨⟨T.simple, T.coxeterMatrix, ⟨T.coxeterSystem⟩⟩⟩

end

end TauCeti.TitsSystem
