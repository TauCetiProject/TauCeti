/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.GroupTheory.Transfer.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle

/-!
# The crossed transfer of a multiplicative crossed homomorphism

Let `G` act on a commutative group `M` by automorphisms, let `H` be a subgroup of finite index
and `t : G ⧸ H → G` a transversal. The **crossed transfer** of a map `c : H → M` is
`T_t c : G → M`, `T_t c g = ∏ u, t u • c (ℓᵗ_u g)`, where `ℓᵗ_u g = (t u)⁻¹ * g * t (g⁻¹ • u)` is
the transversal word `TauCeti.lWord`. It is the degree-one corestriction cochain
`TauCeti.ContCohomology.cochainsCor1` read multiplicatively on `Additive M`, and for a trivial
action and a homomorphism `c` it is Mathlib's transfer `MonoidHom.transfer`.

The crossed transfer carries crossed homomorphisms (multiplicative `1`-cocycles) on `H` to
crossed homomorphisms on `G`, and changing the transversal multiplies it by a principal crossed
homomorphism `g ↦ g • a / a`. Its value on a normal subgroup `N ≤ H` on which `c` is
`G`-equivariant is the `[G : H]`-th power of `c`. When `[G : H]` is prime to `|M|`, raising the
crossed transfer to an inverse of `[G : H]` modulo `|M|` therefore extends the restriction of `c`
to `N` to a crossed homomorphism on all of `G`. This is the core of Gaschütz's splitting theorem:
for `M = N` an abelian normal subgroup acted on by conjugation and `c` the projection along a
complement of `N` in `H`, the kernel of the extended crossed homomorphism is a complement of `N`
in `G`.

## Main results

* `TauCeti.crossedTransfer`: the crossed transfer, a homomorphism `(H → M) →* (G → M)`.
* `TauCeti.isMulCocycle₁_crossedTransfer`: it carries crossed homomorphisms to crossed
  homomorphisms.
* `TauCeti.crossedTransfer_changeTransversal`: two transversals give crossed transfers differing
  by an explicit principal crossed homomorphism.
* `TauCeti.crossedTransfer_restrict`: the crossed transfer of a restricted crossed homomorphism
  is its `[G : H]`-th power times a principal crossed homomorphism.
* `TauCeti.crossedTransfer_eq_transfer`: for a trivial action it is the classical transfer.
* `TauCeti.crossedTransfer_apply_of_mem`: its value on a normal subgroup `N ≤ H` on which `c` is
  equivariant is `c n ^ [G : H]`.
* `TauCeti.exists_isMulCocycle₁_eq_of_coprime_index`: for `[G : H]` prime to `|M|`, such a
  crossed homomorphism on `H` agrees on `N` with a crossed homomorphism on `G`.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Theorem 1.
-/

public section

namespace TauCeti

open groupCohomology

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
  (H : Subgroup G) [H.FiniteIndex] (t : G ⧸ H → G)
  (ht : ∀ u : G ⧸ H, (QuotientGroup.mk (t u) : G ⧸ H) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The **crossed transfer** `(T_t c) g = ∏ u : G ⧸ H, t u • c (ℓᵗ_u g)` of a map `c : H → M` along
a transversal `t` of a finite-index subgroup `H`, where `ℓᵗ_u g` is the transversal word
`TauCeti.lWord`. It is the degree-one corestriction cochain read multiplicatively
(`TauCeti.ofMul_crossedTransfer_apply`). -/
noncomputable def crossedTransfer : (H → M) →* (G → M) where
  toFun c g := ∏ u : G ⧸ H, t u • c ⟨lWord H t u g, lWord_mem H t ht u g⟩
  map_one' := by
    ext
    simp
  map_mul' c d := by
    ext
    simp [smul_mul', Finset.prod_mul_distrib]

/-- The defining formula for the crossed transfer. -/
@[simp]
theorem crossedTransfer_apply (c : H → M) (g : G) :
    crossedTransfer H t ht c g = ∏ u : G ⧸ H, t u • c ⟨lWord H t u g, lWord_mem H t ht u g⟩ :=
  (rfl)

/-- The crossed transfer is the degree-one corestriction cochain on the additive coefficient
module `Additive M`. -/
theorem ofMul_crossedTransfer_apply (c : H → M) (g : G) :
    Additive.ofMul (crossedTransfer H t ht c g) =
      ContCohomology.cochainsCor1 G (Additive M) H t ht (fun x => Additive.ofMul (c x)) g := by
  simp [crossedTransfer_apply, ofMul_prod]

/-- **The crossed transfer of a crossed homomorphism is a crossed homomorphism.** -/
theorem isMulCocycle₁_crossedTransfer {c : H → M} (hc : IsMulCocycle₁ c) :
    IsMulCocycle₁ (crossedTransfer H t ht c) := by
  intro g k
  apply Additive.ofMul.injective
  simpa only [ofMul_crossedTransfer_apply, ofMul_mul, Additive.ofMul_smul] using
    ContCohomology.cochainsCor1_isCocycle₁ G (Additive M) H t ht
      (f := fun x => Additive.ofMul (c x)) (fun x y => congrArg Additive.ofMul (hc x y)) g k

/-- **Change of transversal.** For a crossed homomorphism `c` on `H`, the crossed transfers along
two transversals `t` and `t'` differ by the principal crossed homomorphism `g ↦ g • a / a` of
`a = ∏ v, t v • c ((t v)⁻¹ * t' v)`, where `(t v)⁻¹ * t' v` is `TauCeti.transversalDiff`. -/
theorem crossedTransfer_changeTransversal (t' : G ⧸ H → G)
    (ht' : ∀ u : G ⧸ H, (QuotientGroup.mk (t' u) : G ⧸ H) = u) {c : H → M}
    (hc : IsMulCocycle₁ c) (g : G) :
    crossedTransfer H t' ht' c g = crossedTransfer H t ht c g *
      (g • (∏ v : G ⧸ H, t v • c ⟨transversalDiff H t t' v, transversalDiff_mem H t t' ht ht' v⟩) /
        ∏ v : G ⧸ H, t v • c ⟨transversalDiff H t t' v, transversalDiff_mem H t t' ht ht' v⟩) := by
  apply Additive.ofMul.injective
  simpa [ofMul_crossedTransfer_apply, ofMul_prod, ContCohomology.d0_apply, Finset.smul_sum] using
    congrFun (ContCohomology.cochainsCor1_changeTransversal G (Additive M) H t ht t' ht'
      (f := fun x => Additive.ofMul (c x)) (fun x y => congrArg Additive.ofMul (hc x y))) g

/-- **The crossed transfer of a restriction.** For a crossed homomorphism `c` on `G`, the crossed
transfer of its restriction to `H` is `c ^ [G : H]` times the principal crossed homomorphism of
`∏ u, c (t u)`. -/
theorem crossedTransfer_restrict {c : G → M} (hc : IsMulCocycle₁ c) (g : G) :
    crossedTransfer H t ht (fun x : H => c x) g =
      c g ^ H.index * (g • (∏ u : G ⧸ H, c (t u)) / ∏ u : G ⧸ H, c (t u)) := by
  apply Additive.ofMul.injective
  simpa [ofMul_crossedTransfer_apply, ofMul_prod, ContCohomology.d0_apply, Finset.smul_sum] using
    congrFun (ContCohomology.cochainsCor1_res G (Additive M) H t ht
      (c := fun x => Additive.ofMul (c x)) (fun x y => congrArg Additive.ofMul (hc x y))) g

/-- For a trivial action, the crossed transfer of a homomorphism `φ : H →* M` is its transfer
`MonoidHom.transfer φ`. -/
theorem crossedTransfer_eq_transfer (htriv : ∀ (g : G) (m : M), g • m = m) (φ : H →* M) :
    crossedTransfer H t ht φ = φ.transfer := by
  ext g
  simp [crossedTransfer_apply, htriv, transfer_eq_prod_lWord t ht]

/-- **The crossed transfer on a normal subgroup.** Let `N ≤ H` be normal in `G` and let `c` be
`G`-equivariant on `N`: `g • c x = c (g * x * g⁻¹)` for `x ∈ N`. Then the crossed transfer of `c`
agrees on `N` with `c ^ [G : H]`. For the conjugation action on `M = N` the equivariance holds
for every map which is the identity on `N`. -/
theorem crossedTransfer_apply_of_mem {N : Subgroup G} [N.Normal] (hNH : N ≤ H) {c : H → M}
    (hcN : ∀ (g : G) (x y : H), (x : G) ∈ N → (y : G) = g * x * g⁻¹ → g • c x = c y)
    {n : G} (hn : n ∈ N) :
    crossedTransfer H t ht c n = c ⟨n, hNH hn⟩ ^ H.index := by
  have hterm (u : G ⧸ H) :
      t u • c ⟨lWord H t u n, lWord_mem H t ht u n⟩ = c ⟨n, hNH hn⟩ := by
    have hw := lWord_of_mem_of_normal H t hNH hn u
    refine hcN (t u) _ _ ?_ ?_
    · simpa only [hw, inv_inv] using ‹N.Normal›.conj_mem' n hn (t u)
    · simp only [hw]
      group
  rw [crossedTransfer_apply, Finset.prod_congr rfl fun u _ => hterm u, Finset.prod_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← H.index_eq_card]

/-- **Normalization by an inverse exponent.** Under the hypotheses of
`TauCeti.crossedTransfer_apply_of_mem`, if `[G : H]` is prime to `|M|`, then the crossed transfer
raised to the inverse of `[G : H]` modulo `|M|` agrees with `c` on `N`. -/
theorem crossedTransfer_pow_inv_index_apply_of_mem
    (hcop : Nat.Coprime H.index (Nat.card M)) {N : Subgroup G} [N.Normal] (hNH : N ≤ H)
    {c : H → M}
    (hcN : ∀ (g : G) (x y : H), (x : G) ∈ N → (y : G) = g * x * g⁻¹ → g • c x = c y)
    {n : G} (hn : n ∈ N) :
    crossedTransfer H t ht c n ^ ((H.index : ZMod (Nat.card M))⁻¹).val = c ⟨n, hNH hn⟩ := by
  rw [crossedTransfer_apply_of_mem H t ht hNH hcN hn, pow_pow_zmod_val_inv hcop.symm]

variable {H} in
/-- **Extension of crossed homomorphisms across a coprime index.** Let `N ≤ H` be normal in `G`
with `[G : H]` prime to `|M|`, and let `c` be a crossed homomorphism on `H` which is
`G`-equivariant on `N`. Then some crossed homomorphism on `G` agrees with `c` on `N`: a power of
the crossed transfer of `c`. -/
theorem exists_isMulCocycle₁_eq_of_coprime_index (hcop : Nat.Coprime H.index (Nat.card M))
    {N : Subgroup G} [N.Normal] (hNH : N ≤ H) {c : H → M} (hc : IsMulCocycle₁ c)
    (hcN : ∀ (g : G) (x y : H), (x : G) ∈ N → (y : G) = g * x * g⁻¹ → g • c x = c y) :
    ∃ d : G → M, IsMulCocycle₁ d ∧ ∀ (n : G) (hn : n ∈ N), d n = c ⟨n, hNH hn⟩ := by
  have ht (u : G ⧸ H) : (QuotientGroup.mk u.out : G ⧸ H) = u := u.out_eq'
  exact ⟨crossedTransfer H _ ht c ^ ((H.index : ZMod (Nat.card M))⁻¹).val,
    (isMulCocycle₁_crossedTransfer H _ ht hc).pow _,
    fun n hn => crossedTransfer_pow_inv_index_apply_of_mem H _ ht hcop hNH hcN hn⟩

end TauCeti
