/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Counting transitive permutation representations

A permutation representation `ρ : Γ →* Equiv.Perm α` of a group on a finite set splits along
the orbit `s` of any point `a`. The orbit is invariant, `ρ` restricts to a transitive
representation on `s` and to an arbitrary representation on the complement, and conversely
every such pair glues back to a representation in which the orbit of `a` is `s`. Summing over
the possible orbits, and noting that there are `n.choose k` subsets of `Fin (n + 1)` of size
`k + 1` containing `0`, gives the classical recursion

```text
#Hom(Γ, S_{n+1}) = ∑_{k=0}^{n} C(n, k) · #TransHom(Γ, S_{k+1}) · #Hom(Γ, S_{n-k})
```

for the number of transitive representations. For a free group of rank `r`, where
`#Hom(Γ, S_m) = (m!)^r`, this is the recursion behind Hall's count of the subgroups of finite
index.

## Main definitions

* `MonoidHom.subtypePerm`: the restriction of a permutation representation to an invariant
  subset.
* `TauCeti.orbitSplitEquiv`: representations in which the orbit of `a` is `s`, as pairs of a
  transitive representation on `s` and a representation on its complement.

## Main results

* `TauCeti.natCard_monoidHom_perm_eq_sum`: the number of representations on a finite set, as a
  sum over the possible orbits of a point.
* `TauCeti.natCard_monoidHom_perm_fin_succ_eq_sum`: the recursion above.

## References

* M. Hall, Jr., *Subgroups of finite index in free groups*, Canad. J. Math. 1 (1949), 187–190.
-/

public section

open Equiv Finset MulAction

namespace MonoidHom

variable {Γ α : Type*} [Group Γ]

/-- The restriction of a permutation representation to a subset that every `ρ g` preserves. -/
def subtypePerm (ρ : Γ →* Perm α) (p : α → Prop) (h : ∀ g x, p (ρ g x) ↔ p x) :
    Γ →* Perm {x // p x} where
  toFun g := (ρ g).subtypePerm (h g)
  map_one' := by ext; simp
  map_mul' g g' := by ext x; exact DFunLike.congr_fun (map_mul ρ g g') (x : α)

@[simp]
theorem subtypePerm_apply_coe (ρ : Γ →* Perm α) (p : α → Prop) (h : ∀ g x, p (ρ g x) ↔ p x)
    (g : Γ) (x : {x // p x}) : (ρ.subtypePerm p h g x : α) = ρ g x :=
  (rfl)

/-- The image of a permutation representation is transitive exactly when every point is
reached from a fixed base point. -/
theorem isPretransitive_range_iff (ρ : Γ →* Perm α) (a : α) :
    IsPretransitive ρ.range α ↔ ∀ x, ∃ g, ρ g a = x := by
  rw [isPretransitive_iff_base a]
  refine forall_congr' fun x => ⟨?_, ?_⟩
  · rintro ⟨⟨_, g, rfl⟩, hg⟩
    exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨ρ g, g, rfl⟩, hg⟩

end MonoidHom

namespace TauCeti

variable {Γ α : Type*} [Group Γ] [DecidableEq α] {a : α} {s : Finset α}

/-- **Splitting a permutation representation along an orbit.** A representation in which the
orbit of `a` is `s` is the same thing as a transitive representation on `s` together with an
arbitrary representation on the complement of `s`. -/
def orbitSplitEquiv (ha : a ∈ s) :
    {ρ : Γ →* Perm α // Set.range (fun g => ρ g a) = s} ≃
      {σ : Γ →* Perm s // IsPretransitive σ.range s} × (Γ →* Perm {x // x ∉ s}) where
  toFun ρ :=
    -- The orbit of `a` is invariant under every `ρ g`.
    have hs : ∀ g x, ρ.1 g x ∈ s ↔ x ∈ s := by
      obtain ⟨ρ, hρ⟩ := ρ
      intro g x
      dsimp only
      rw [← Finset.mem_coe, ← Finset.mem_coe, ← hρ]
      constructor
      · rintro ⟨h, hh⟩
        exact ⟨g⁻¹ * h, by simp [hh]⟩
      · rintro ⟨h, rfl⟩
        exact ⟨g * h, by simp⟩
    (⟨ρ.1.subtypePerm (· ∈ s) hs, (MonoidHom.isPretransitive_range_iff _ ⟨a, ha⟩).2
      fun x => by
        obtain ⟨g, hg⟩ : (x : α) ∈ Set.range (fun g => ρ.1 g a) := by
          rw [ρ.2]
          exact x.2
        exact ⟨g, Subtype.ext hg⟩⟩,
      ρ.1.subtypePerm (· ∉ s) fun g x => not_congr (hs g x))
  invFun στ :=
    ⟨(Perm.subtypeCongrHom (· ∈ s)).comp (στ.1.1.prod στ.2), by
      ext x
      simp only [Set.mem_range, MonoidHom.comp_apply, MonoidHom.prod_apply,
        Perm.subtypeCongrHom_apply, Finset.mem_coe]
      constructor
      · rintro ⟨g, rfl⟩
        rw [Perm.subtypeCongr.left_apply _ _ ha]
        exact (στ.1.1 g ⟨a, ha⟩).2
      · intro hx
        obtain ⟨g, hg⟩ := (MonoidHom.isPretransitive_range_iff _ ⟨a, ha⟩).1 στ.1.2 ⟨x, hx⟩
        exact ⟨g, by rw [Perm.subtypeCongr.left_apply _ _ ha, hg]⟩⟩
  left_inv ρ := by
    ext g x
    by_cases hx : x ∈ s
    · simp [Perm.subtypeCongr.left_apply _ _ hx]
    · simp [Perm.subtypeCongr.right_apply _ _ hx]
  right_inv στ := by
    ext g x
    · simp
    · simp [Perm.subtypeCongr.right_apply_subtype]

/-- On the orbit, the split representation acts as the original one. -/
@[simp]
theorem orbitSplitEquiv_apply_fst_coe_apply (ha : a ∈ s)
    (ρ : {ρ : Γ →* Perm α // Set.range (fun g => ρ g a) = s}) (g : Γ) (x : s) :
    ((orbitSplitEquiv ha ρ).1.1 g x : α) = ρ.1 g x :=
  (rfl)

/-- Off the orbit, the split representation acts as the original one. -/
@[simp]
theorem orbitSplitEquiv_apply_snd_apply (ha : a ∈ s)
    (ρ : {ρ : Γ →* Perm α // Set.range (fun g => ρ g a) = s}) (g : Γ) (x : {x // x ∉ s}) :
    ((orbitSplitEquiv ha ρ).2 g x : α) = ρ.1 g x :=
  (rfl)

/-- The glued representation acts on the orbit and on its complement by the two pieces. -/
@[simp]
theorem orbitSplitEquiv_symm_apply_coe (ha : a ∈ s)
    (στ : {σ : Γ →* Perm s // IsPretransitive σ.range s} × (Γ →* Perm {x // x ∉ s})) :
    ((orbitSplitEquiv ha).symm στ).1 = (Perm.subtypeCongrHom (· ∈ s)).comp (στ.1.1.prod στ.2) :=
  (rfl)

variable [Fintype α]

/-- **The orbit decomposition of the number of permutation representations.** A representation
of `Γ` on a finite set is determined by the orbit `s` of a point `a`, a transitive representation
on `s`, and a representation on the complement of `s`. -/
theorem natCard_monoidHom_perm_eq_sum [Finite (Γ →* Perm α)] (a : α) :
    Nat.card (Γ →* Perm α) = ∑ s ∈ (univ : Finset (Finset α)).filter (a ∈ ·),
      Nat.card {σ : Γ →* Perm (Fin s.card) // IsPretransitive σ.range (Fin s.card)} *
        Nat.card (Γ →* Perm (Fin (Fintype.card α - s.card))) := by
  classical
  let orbit : (Γ →* Perm α) → {s : Finset α // a ∈ s} := fun ρ =>
    ⟨univ.filter (· ∈ Set.range fun g => ρ g a), by simpa using ⟨1, by simp⟩⟩
  have horbit (ρ : Γ →* Perm α) (s : {s : Finset α // a ∈ s}) :
      orbit ρ = s ↔ Set.range (fun g => ρ g a) = s := by
    rw [Subtype.ext_iff, ← Finset.coe_inj]
    simp only [orbit, Finset.coe_filter, Finset.mem_univ, true_and, Set.ofPred_mem_eq]
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv orbit), Nat.card_sigma,
    Finset.sum_subtype (univ.filter (a ∈ ·)) (p := (a ∈ ·)) (by simp)]
  refine Fintype.sum_congr _ _ fun s => ?_
  rw [Nat.card_congr ((Equiv.subtypeEquivRight (horbit · s)).trans (orbitSplitEquiv s.2)),
    Nat.card_prod, Nat.card_congr ((MulEquiv.monoidHomCongrRightEquiv
      s.1.equivFin.permCongrHom).subtypeEquiv
        (q := fun σ => IsPretransitive σ.range (Fin s.1.card)) fun σ => by
        rw [MulEquiv.monoidHomCongrRightEquiv_apply, MonoidHom.range_comp,
          isPretransitive_map_permCongrHom_iff]),
    Nat.card_congr (MulEquiv.monoidHomCongrRightEquiv
      (Fintype.equivFinOfCardEq (α := {x // x ∉ s.1}) (n := Fintype.card α - s.1.card)
        (by rw [Fintype.card_subtype_compl, Fintype.card_coe])).permCongrHom)]

/-- **The orbit recursion for permutation representations.** Splitting a representation of `Γ`
on `Fin (n + 1)` along the orbit of `0`: the orbit has some size `k + 1`, there are
`n.choose k` choices for it, the representation is transitive on it and arbitrary on the
remaining `n - k` points. -/
theorem natCard_monoidHom_perm_fin_succ_eq_sum (n : ℕ) [Finite (Γ →* Perm (Fin (n + 1)))] :
    Nat.card (Γ →* Perm (Fin (n + 1))) = ∑ k ∈ range (n + 1), n.choose k *
      (Nat.card {σ : Γ →* Perm (Fin (k + 1)) // IsPretransitive σ.range (Fin (k + 1))} *
        Nat.card (Γ →* Perm (Fin (n - k)))) := by
  rw [natCard_monoidHom_perm_eq_sum (0 : Fin (n + 1))]
  have himage : univ.filter ((0 : Fin (n + 1)) ∈ ·) =
      (univ.erase (0 : Fin (n + 1))).powerset.image (insert 0) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_powerset]
    refine ⟨fun hs => ⟨s.erase 0, fun x hx => ?_, insert_erase hs⟩, ?_⟩
    · simp only [mem_erase] at hx ⊢
      exact ⟨hx.1, mem_univ x⟩
    · rintro ⟨t, -, rfl⟩
      exact mem_insert_self 0 t
  have h0 (t : Finset (Fin (n + 1))) (ht : t ∈ (univ.erase 0).powerset) : 0 ∉ t :=
    fun h => by simpa using mem_powerset.1 ht h
  rw [himage, sum_image fun t ht t' ht' h => by
    rw [← erase_insert (h0 t ht), h, erase_insert (h0 t' ht')]]
  let G : ℕ → ℕ := fun k =>
    Nat.card {σ : Γ →* Perm (Fin (k + 1)) // IsPretransitive σ.range (Fin (k + 1))} *
      Nat.card (Γ →* Perm (Fin (n - k)))
  rw [sum_congr rfl (g := fun t => G t.card) fun t ht => by
      simp only [G]
      rw [card_insert_of_notMem (h0 t ht), Fintype.card_fin, Nat.add_sub_add_right],
    sum_powerset_apply_card G, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
    Nat.add_sub_cancel]
  simp only [smul_eq_mul, G]

end TauCeti
