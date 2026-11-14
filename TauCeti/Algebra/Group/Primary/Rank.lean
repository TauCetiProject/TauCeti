/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Group.Primary.Generators
public import TauCeti.GroupTheory.PGroup
public import TauCeti.LinearAlgebra.FreeModule.ModN

/-!
# Generator rank of finite abelian `p`-groups and primary components of products

For a finite abelian `p`-group `G` (`IsAddPGroup p G` with `p` prime), the Frattini / Burnside
reduction identifies the minimal number of generators `AddGroup.rank G` with the `ZMod p`-dimension
of `ModN G p = G / pG`. Because `ModN · p` distributes `ZMod p`-linearly over products
(`ModN.prodLinearEquiv`, `ModN.piLinearEquiv`), generator rank is **additive** on products of finite
abelian `p`-groups, whereas it takes the **maximum** on products of finite abelian groups of
coprime orders (`AddGroup.rank_prod_eq_max_of_coprime_card`).

## Main definitions and statements

* `IsAddPGroup.rank_eq_finrank_modN`: `AddGroup.rank G = finrank (ZMod p) (ModN G p)` for a finite
  abelian `p`-group `G`.
* `IsAddPGroup.rank_prod`, `IsAddPGroup.rank_pi`: generator rank is additive on products of finite
  abelian `p`-groups.
* `AddGroup.rank_zmod_prime_pow`, `AddGroup.rank_prod_zmod_prime_pow`,
  `AddGroup.rank_pi_zmod_prime_pow`: generator ranks of prime-power cyclic groups and their
  products.
* `AddCommGroup.primaryComponentProdAddEquiv`: `(A × B)[p^∞] ≃+ A[p^∞] × B[p^∞]`, with
  `AddGroup.rank_primaryComponent_prod` giving additivity of `l(A_p)` on products.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

namespace IsAddPGroup

/-- **Burnside basis theorem for finite abelian `p`-groups**: for prime `p`, the minimal number of
generators `AddGroup.rank G` of a finite abelian `p`-group `G` equals `finrank (ZMod p) (ModN G p)`.
Any lift of a generating set of `G / pG` generates `G` modulo `p • G`, hence modulo `p ^ k • G` for
every `k`, and `p ^ k • G = 0` for large `k`. -/
theorem rank_eq_finrank_modN {p : ℕ} (hp : p.Prime) {G : Type*} [AddCommGroup G] [Finite G]
    (hG : IsAddPGroup p G) :
    AddGroup.rank G = Module.finrank (ZMod p) (ModN G p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hsurj : Function.Surjective (ModN.mkQ p : G →+ ModN G p) := Submodule.mkQ_surjective _
  rw [← AddGroup.rank_eq_finrank_zmod (ModN G p)]
  refine le_antisymm ?_ (AddGroup.rank_le_of_surjective (ModN.mkQ p) hsurj)
  obtain ⟨S, hScard, hS⟩ := AddGroup.rank_spec (ModN G p)
  let T : Finset G := S.image (Function.surjInv hsurj)
  let H : AddSubgroup G := AddSubgroup.closure (T : Set G)
  have hmap : H.map (ModN.mkQ p) = ⊤ := by
    dsimp only [H, T]
    rw [AddMonoidHom.map_closure, Finset.coe_image, ← Set.image_comp,
      Function.comp_surjInv hsurj, Set.image_id, hS]
  have hstep (g : G) : ∃ h ∈ H, ∃ g' : G, g = h + p • g' := by
    have hmem : ModN.mkQ p g ∈ H.map (ModN.mkQ p) := hmap ▸ trivial
    obtain ⟨h, hh, hgh⟩ := hmem
    have hsub : g - h ∈ LinearMap.range (LinearMap.lsmul ℤ G (p : ℤ)) :=
      (Submodule.Quotient.eq _).mp hgh.symm
    obtain ⟨g', hg'⟩ := hsub
    refine ⟨h, hh, g', ?_⟩
    calc g = h + (g - h) := (add_sub_cancel h g).symm
      _ = h + p • g' := by
        rw [← hg', LinearMap.lsmul_apply, natCast_zsmul]
  have hiter (k : ℕ) : ∀ g : G, ∃ h ∈ H, ∃ g' : G, g = h + p ^ k • g' := by
    induction k with
    | zero =>
        intro g
        exact ⟨0, H.zero_mem, g, by simp⟩
    | succ k ih =>
        intro g
        obtain ⟨h₁, hh₁, g₁, rfl⟩ := ih g
        obtain ⟨h₂, hh₂, g₂, rfl⟩ := hstep g₁
        refine ⟨h₁ + p ^ k • h₂, H.add_mem hh₁ (H.nsmul_mem hh₂ _), g₂, ?_⟩
        rw [nsmul_add, add_assoc, smul_smul, ← pow_succ]
  obtain ⟨K, hkill⟩ := isAddPGroup_iff_exists_pow_nsmul_eq_zero.mp hG
  have htop : H = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨h, hh, g', rfl⟩ := hiter K x
    simpa [hkill g'] using hh
  exact (AddGroup.rank_le (S := T) htop).trans (Finset.card_image_le.trans_eq hScard)

/-- Generator rank is additive on binary products of finite abelian `p`-groups. -/
theorem rank_prod {p : ℕ} (hp : p.Prime) {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Finite G] [Finite H] (hG : IsAddPGroup p G) (hH : IsAddPGroup p H) :
    AddGroup.rank (G × H) = AddGroup.rank G + AddGroup.rank H := by
  have : Fact p.Prime := ⟨hp⟩
  have : Module.Finite (ZMod p) (ModN G p) := Module.Finite.of_finite
  have : Module.Finite (ZMod p) (ModN H p) := Module.Finite.of_finite
  rw [(IsAddPGroup.prod hG hH).rank_eq_finrank_modN hp, hG.rank_eq_finrank_modN hp,
    hH.rank_eq_finrank_modN hp, (ModN.prodLinearEquiv G H p).finrank_eq, Module.finrank_prod]

/-- Generator rank is additive on finite indexed products of finite abelian `p`-groups. -/
theorem rank_pi {p : ℕ} (hp : p.Prime) {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, Finite (G i)] (hG : ∀ i, IsAddPGroup p (G i)) :
    AddGroup.rank (∀ i, G i) = ∑ i, AddGroup.rank (G i) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : ∀ i, Module.Finite (ZMod p) (ModN (G i) p) := fun _ ↦ Module.Finite.of_finite
  rw [(IsAddPGroup.pi hG).rank_eq_finrank_modN hp, (ModN.piLinearEquiv G p).finrank_eq,
    Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ ↦ ((hG i).rank_eq_finrank_modN hp).symm

/-- For any `p` and `k`, `ZMod (p ^ k)` is an additive `p`-group. -/
theorem zmod_prime_pow (p k : ℕ) : IsAddPGroup p (ZMod (p ^ k)) :=
  fun _ ↦ ⟨k, by simp⟩

end IsAddPGroup

namespace AddCommGroup

/-- The `n`-primary component of a binary product of additive commutative groups splits as the
product of their `n`-primary components. -/
def primaryComponentProdAddEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    AddCommGroup.primaryComponent (A × B) n ≃+
      AddCommGroup.primaryComponent A n × AddCommGroup.primaryComponent B n where
  toFun x :=
    ⟨⟨x.1.1, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, congrArg Prod.fst hk⟩⟩,
     ⟨x.1.2, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, congrArg Prod.snd hk⟩⟩⟩
  invFun y :=
    ⟨(y.1.1, y.2.1), by
      obtain ⟨k₁, hk₁⟩ := AddCommGroup.mem_primaryComponent.mp y.1.2
      obtain ⟨k₂, hk₂⟩ := AddCommGroup.mem_primaryComponent.mp y.2.2
      refine AddCommGroup.mem_primaryComponent.mpr ⟨k₁ + k₂, ?_⟩
      rw [Prod.smul_mk, Prod.mk_eq_zero]
      exact ⟨by rw [add_comm, pow_add, ← smul_smul, hk₁, nsmul_zero],
        by rw [pow_add, ← smul_smul, hk₂, nsmul_zero]⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem primaryComponentProdAddEquiv_apply_fst (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (x : AddCommGroup.primaryComponent (A × B) n) :
    ((primaryComponentProdAddEquiv A B n x).1 : A) = x.1.1 := by
  rfl

@[simp]
theorem primaryComponentProdAddEquiv_apply_snd (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (x : AddCommGroup.primaryComponent (A × B) n) :
    ((primaryComponentProdAddEquiv A B n x).2 : B) = x.1.2 := by
  rfl

@[simp]
theorem coe_primaryComponentProdAddEquiv_symm_apply (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (x : AddCommGroup.primaryComponent A n) (y : AddCommGroup.primaryComponent B n) :
    ((primaryComponentProdAddEquiv A B n).symm (x, y) : A × B) = (x.1, y.1) := by
  rfl

/-- Every element of `AddCommGroup.primaryComponent A n` is annihilated by a power of `n`. -/
theorem primaryComponent.isAddPGroup (A : Type*) [AddCommGroup A] (n : ℕ) :
    IsAddPGroup n (AddCommGroup.primaryComponent A n) := by
  intro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hx
  exact ⟨k, Subtype.ext hk⟩

end AddCommGroup

namespace AddGroup

/-- For prime `p` and `k > 0`, `ZMod (p ^ k)` has generator rank `1`. -/
theorem rank_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    AddGroup.rank (ZMod (p ^ k)) = 1 :=
  AddGroup.rank_zmod_of_ne_one (Nat.one_lt_pow hk.ne' hp.one_lt).ne'

/-- A binary product `ZMod (p ^ k₁) × ZMod (p ^ k₂)` of nontrivial `p`-power cyclic groups has
generator rank `2`. -/
theorem rank_prod_zmod_prime_pow {p k₁ k₂ : ℕ} (hp : p.Prime) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    AddGroup.rank (ZMod (p ^ k₁) × ZMod (p ^ k₂)) = 2 := by
  have : NeZero (p ^ k₁) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero (p ^ k₂) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [(IsAddPGroup.zmod_prime_pow p k₁).rank_prod hp (IsAddPGroup.zmod_prime_pow p k₂),
    rank_zmod_prime_pow hp hk₁, rank_zmod_prime_pow hp hk₂]

/-- A finite indexed product `∀ i, ZMod (p ^ k i)` of nontrivial `p`-power cyclic groups has
generator rank `Fintype.card ι`. -/
theorem rank_pi_zmod_prime_pow {p : ℕ} (hp : p.Prime) {ι : Type*} [Fintype ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) :
    AddGroup.rank (∀ i, ZMod (p ^ k i)) = Fintype.card ι := by
  have : ∀ i, NeZero (p ^ k i) := fun _ ↦ ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [IsAddPGroup.rank_pi hp (fun i ↦ IsAddPGroup.zmod_prime_pow p (k i))]
  simp_rw [rank_zmod_prime_pow hp (hk _), Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-- On any binary product of finite abelian groups, the generator rank of the `p`-primary component
is additive for prime `p`. -/
theorem rank_primaryComponent_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Finite A] [Finite B] {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (AddCommGroup.primaryComponent (A × B) p) =
      AddGroup.rank (AddCommGroup.primaryComponent A p) +
        AddGroup.rank (AddCommGroup.primaryComponent B p) := by
  rw [AddGroup.rank_congr (AddCommGroup.primaryComponentProdAddEquiv A B p),
    (AddCommGroup.primaryComponent.isAddPGroup A p).rank_prod hp
      (AddCommGroup.primaryComponent.isAddPGroup B p)]

/-- For prime `p`, the elementary abelian group `ZMod p × ZMod p` has generator rank `2`. -/
theorem rank_prod_zmod_prime {p : ℕ} (hp : p.Prime) :
    AddGroup.rank (ZMod p × ZMod p) = 2 := by
  have h := rank_prod_zmod_prime_pow hp Nat.one_pos Nat.one_pos
  rwa [pow_one] at h

/-- For distinct primes `p ≠ q`, `ZMod p × ZMod q` is cyclic of generator rank `1`. -/
theorem rank_prod_zmod_prime_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    AddGroup.rank (ZMod p × ZMod q) = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have hcop : (Nat.card (ZMod p)).Coprime (Nat.card (ZMod q)) := by
    simpa [Nat.card_zmod] using (Nat.coprime_primes hp hq).mpr hpq
  rw [AddGroup.rank_prod_eq_max_of_coprime_card _ _ hcop,
    AddGroup.rank_zmod_of_ne_one hp.ne_one, AddGroup.rank_zmod_of_ne_one hq.ne_one, max_self]

/-- For distinct primes `p ≠ q`, `(ZMod p × ZMod p) × ZMod q` has generator rank `2` (`2` at `p`
and `1` at `q`). -/
theorem rank_prod_prod_zmod_prime_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    AddGroup.rank ((ZMod p × ZMod p) × ZMod q) = 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have hcop : (Nat.card (ZMod p × ZMod p)).Coprime (Nat.card (ZMod q)) := by
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, ← sq]
    exact ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  rw [AddGroup.rank_prod_eq_max_of_coprime_card _ _ hcop, rank_prod_zmod_prime hp,
    AddGroup.rank_zmod_of_ne_one hq.ne_one]
  rfl

end AddGroup
