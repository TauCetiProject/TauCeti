/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.Adjoin
public import TauCeti.RingTheory.RootsOfUnity.Action
public import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The automorphisms fixing the roots of unity

The `K`-automorphisms of `M` fixing `K(μ_m)` pointwise are exactly the kernel of the cyclotomic
character `IsPrimitiveRoot.autToPow`. No Galois, normality or separability hypothesis is needed —
only that `M` contains a primitive `m`-th root of unity — although when `M / K` is Galois this
subgroup is `Gal(M/K(μ_m))`, which is the reading the crossing argument uses.

Without a primitive root, the same subgroup is the kernel of the action of `Aut(M/K)` on the
group `μ_m(M)`. For `m ≠ 0` this group is cyclic, so the index divides the order `φ(#μ_m(M))` of
the automorphism group of `μ_m(M)`. For a prime `p` this index is prime to `p`: adjoining the
`p`-th roots of unity is a step of degree prime to `p`, the reduction step in the Kummer-theoretic
proofs of class field theory.

## Main results

* `IsPrimitiveRoot.fixingSubgroup_adjoin_nth_roots_eq_ker_autToPow`
* `IntermediateField.fixingSubgroup_adjoin_nth_roots_eq_ker`: the fixers of `K(μ_m)` are the
  automorphisms acting trivially on `μ_m(M)`.
* `IntermediateField.index_fixingSubgroup_adjoin_nth_roots_dvd_totient`: their index divides
  `φ(#μ_m(M))`.
* `IntermediateField.coprime_index_fixingSubgroup_adjoin_nth_roots`: for a prime `p`, their index
  is prime to `p`.

## References

The identification of `Gal(M/K(μ_m))` with the `G × 1` factor of a Galois splitting is due to the
Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0).
-/

public section

open IntermediateField

/-- **The fixers of `K(μ_m)` are the kernel of the cyclotomic character.**

Use it to move between a condition on `Gal(M/K(μ_m))` and one on the cyclotomic character, which
is the form a Galois splitting presents. -/
theorem IsPrimitiveRoot.fixingSubgroup_adjoin_nth_roots_eq_ker_autToPow
    {K M : Type*} [Field K] [Field M] [Algebra K M] {m : ℕ} [NeZero m] {ζ : M}
    (hζ : IsPrimitiveRoot ζ m) :
    (adjoin K {b : M | b ^ m = 1}).fixingSubgroup = (hζ.autToPow K).ker := by
  ext x
  -- `K(μ_m) = K(ζ)`, so fixing the whole root-of-unity set is fixing the single generator.
  rw [MonoidHom.mem_ker, hζ.autToPow_eq_one_iff, ← hζ.adjoin_singleton_eq_adjoin_nth_roots,
    IntermediateField.mem_fixingSubgroup_iff]
  simp only [← AlgEquiv.smul_def]
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  simp [AlgEquiv.smul_def]

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **The fixers of `K(μ_m)` are the automorphisms acting trivially on `μ_m(M)`.** Unlike
`IsPrimitiveRoot.fixingSubgroup_adjoin_nth_roots_eq_ker_autToPow`, this needs no primitive root:
the action on the group `μ_m(M)` replaces the cyclotomic character. -/
theorem fixingSubgroup_adjoin_nth_roots_eq_ker (m : ℕ) :
    (adjoin K {b : M | b ^ m = 1}).fixingSubgroup =
      (MulDistribMulAction.toMulAut (M ≃ₐ[K] M) (rootsOfUnity m M)).ker := by
  ext σ
  rw [MonoidHom.mem_ker, mem_fixingSubgroup_iff]
  simp only [← AlgEquiv.smul_def]
  rw [forall_mem_adjoin_smul_eq_self_iff]
  refine ⟨fun h ↦ MulEquiv.ext fun ζ ↦ Subtype.ext <| Units.ext ?_, fun h b hb ↦ ?_⟩
  · simpa [AlgEquiv.smul_units_def] using h _ ((mem_rootsOfUnity' m _).1 ζ.2)
  · -- A root of unity is a unit, except when `m = 0` and `b = 0`, which every `σ` fixes.
    rcases eq_or_ne b 0 with rfl | hb0
    · exact smul_zero σ
    · have hζ : Units.mk0 b hb0 ∈ rootsOfUnity m M := (mem_rootsOfUnity' m _).2 hb
      have := congrArg (fun f : MulAut (rootsOfUnity m M) ↦ ((f ⟨_, hζ⟩ : rootsOfUnity m M) : Mˣ))
        h
      simpa [AlgEquiv.smul_units_def] using congrArg Units.val this

/-- **The index of `Aut(M/K(μ_m))` divides `φ(#μ_m(M))`**, the order of the automorphism group of
the cyclic group `μ_m(M)`, through whose action it is the kernel. -/
theorem index_fixingSubgroup_adjoin_nth_roots_dvd_totient (m : ℕ) [NeZero m] :
    (adjoin K {b : M | b ^ m = 1}).fixingSubgroup.index ∣
      (Nat.card (rootsOfUnity m M)).totient := by
  rw [fixingSubgroup_adjoin_nth_roots_eq_ker, Subgroup.index_ker,
    ← IsCyclic.card_mulAut]
  exact Subgroup.card_subgroup_dvd_card _

/-- **Adjoining the `p`-th roots of unity is a step of degree prime to `p`**: for a prime `p`, the
index of `Aut(M/K(μ_p))` in `Aut(M/K)` is prime to `p`. It divides `φ(#μ_p(M))`, and
`#μ_p(M) ≤ p`. -/
theorem coprime_index_fixingSubgroup_adjoin_nth_roots {p : ℕ} (hp : p.Prime) :
    (adjoin K {b : M | b ^ p = 1}).fixingSubgroup.index.Coprime p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdvd := index_fixingSubgroup_adjoin_nth_roots_dvd_totient (K := K) (M := M) p
  have hpos : 0 < Nat.card (rootsOfUnity p M) := Nat.card_pos
  have hlt : (Nat.card (rootsOfUnity p M)).totient < p := by
    rcases (Nat.one_le_iff_ne_zero.2 hpos.ne').eq_or_lt with h | h
    · rw [← h, Nat.totient_one]
      exact hp.one_lt
    · exact (Nat.totient_lt _ h).trans_le (card_rootsOfUnity M p)
  exact (Nat.coprime_of_lt_prime (Nat.pos_of_dvd_of_pos hdvd (Nat.totient_pos.2 hpos)).ne'
    ((Nat.le_of_dvd (Nat.totient_pos.2 hpos) hdvd).trans_lt hlt) hp).symm

end IntermediateField
