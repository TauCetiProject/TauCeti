/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality

/-!
# The index of the auxiliary Kummer idele classes

Let `K` be a number field containing the `p`-th roots of unity for a prime `p`. Let `S` and `T`
be disjoint finite sets of finite places of `K`, with `S` containing the places above `p` and
generating the ideal class group, and suppose that the `S`-units surject onto the local unit
`p`-th power classes at the places of `T`. This file computes the index of the image of the
auxiliary Kummer idele subgroup `E_{S,T}` in the idele class group `C_K`:

```text
[C_K : E_{S,T} Kˣ / Kˣ] · p ^ #T = p ^ (#S + r₁ + r₂).
```

The principal ideles in `E_{S,T}` are exactly those of the `(S ∪ T)`-units that are `p`-th
powers. One inclusion is immediate. Conversely, let `a ∈ Kˣ` have its principal idele in
`E_{S,T}`. Then `a` is an `(S ∪ T)`-unit and a local `p`-th power at `S` and at the infinite
places. The surjectivity hypothesis at `T` therefore makes every idele class of `K` a norm from
the cyclic extension `K(a^{1/p})`, so this extension is trivial by the first fundamental
inequality, and `a` is a `p`-th power.

Writing `I_{S∪T}` for the `(S ∪ T)`-ideles and `U_{S∪T}` for the `(S ∪ T)`-units, the index of
the auxiliary idele classes is `[I_{S∪T} : E_{S,T}] / [U_{S∪T} : U_{S∪T} ∩ E_{S,T}]`
(`index_auxiliaryKummerIdeleClassSubgroup_mul_relIndex`). The numerator is `p ^ (2 (#S + r₁ + r₂))`
by the product formula, and the denominator is `[U_{S∪T} : U_{S∪T}ᵖ] = p ^ (#S + #T + r₁ + r₂)` by
Dirichlet's `S`-unit theorem.

For a cyclic extension `L/K` of degree `p` contained in `K(U_S^{1/p})`, an auxiliary set `T`
with `p ^ #T = [K(U_S^{1/p}) : L]` and `E_{S,T} ⊆ N_{L/K}(C_L)` exists by
`exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap`; with the index computed
here this bounds `[C_K : N_{L/K}(C_L)]` by `p`, which is the Kummer case of the second
fundamental inequality.

## Main results

* `TauCeti.ClassFieldTheory.unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_iff`: the principal
  ideles in `E_{S,T}` are those of the `(S ∪ T)`-units that are `p`-th powers.
* `TauCeti.ClassFieldTheory.index_auxiliaryKummerIdeleClassSubgroup_mul_pow_card`:
  `[C_K : E_{S,T} Kˣ / Kˣ] · p ^ #T = p ^ (#S + r₁ + r₂)`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §6, the proof of the second inequality.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter VII, §6.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

variable {p : ℕ} [HasEnoughRootsOfUnity K p]

/-- **A principal idele in the auxiliary Kummer subgroup comes from a `p`-th power.** Let `S`
and `T` be disjoint, with `S` containing the places above `p` and generating the ideal class
group, and let the `S`-units surject onto the local unit `p`-th power classes at `T`. If the
principal idele of `a ∈ Kˣ` lies in `E_{S,T}`, then `a` is a `p`-th power in `K`. -/
private theorem mem_range_powMonoidHom_of_unitEmbedding_mem_auxiliaryKummerIdeleSubgroup
    (hp : p.Prime) {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hsurj : Function.Surjective
      (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST p))
    {a : Kˣ} (ha : IdeleGroup.unitEmbedding (𝓞 K) K a ∈ auxiliaryKummerIdeleSubgroup S T p) :
    a ∈ (powMonoidHom p : Kˣ →* Kˣ).range := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hmem := (mem_auxiliaryKummerIdeleSubgroup_iff S T p _).1 ha
  set Δ := Subgroup.zpowers a
  -- `Δ` has at most `p` classes modulo `p`-th powers, since `aᵖ` is a `p`-th power.
  have hdvd : (powMonoidHom p : Kˣ →* Kˣ).range.relIndex Δ ∣ p := by
    have h := Subgroup.relIndex_dvd_of_le_left Δ
      (Subgroup.zpowers_le.2 ⟨a, (zpow_natCast a p).symm⟩ :
        Subgroup.zpowers (a ^ (p : ℤ)) ≤ (powMonoidHom p : Kˣ →* Kˣ).range)
    rw [Subgroup.relIndex_zpowers_zpow, Int.gcd_natCast_natCast] at h
    exact h.trans (Nat.gcd_dvd_left _ _)
  have : (powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ :=
    ⟨fun h ↦ hp.ne_zero (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))⟩
  -- Every element of `Δ` is a local `p`-th power wherever `a` is one.
  have hpow {M : Type} [CommMonoid M] (f : Kˣ →* Mˣ)
      (hf : f a ∈ (powMonoidHom p : Mˣ →* Mˣ).range) (b : Kˣ) (hb : b ∈ Δ) :
      f b ∈ (powMonoidHom p : Mˣ →* Mˣ).range :=
    Subgroup.zpowers_le.2 (Subgroup.mem_comap.2 hf) hb
  have hroots (b : Kˣ) (_ : b ∈ Δ) : ∃ x : AlgebraicClosure K, x ^ p = algebraMap K _ b :=
    IsAlgClosed.exists_pow_nat_eq _ hp.pos
  have hdeg := finrank_kummerField hroots
  have : IsCyclic Gal(kummerField (AlgebraicClosure K) p Δ/K) :=
    isCyclic_of_card_dvd_prime (p := p) (by rwa [IsGalois.card_aut_eq_finrank, hdeg])
  -- Every idele class is a norm from `K(a^{1/p})`, so this cyclic extension is trivial.
  have hnorm := ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit
    (E := AlgebraicClosure K) S T (Finset.disjoint_coe.1 hST) hcl hpS
    (Subgroup.zpowers_le.2 <|
      (unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_one_iff S T a).1 <|
        auxiliaryKummerIdeleSubgroup_le_one S T p ha)
    (fun v hv b hb ↦ by
      obtain ⟨c, hc⟩ := hpow _ (HeightOneSpectrum.ideleFiniteCoord_unitEmbedding v a ▸ hmem.1 v hv)
        b hb
      exact ⟨c, by simpa using congrArg Units.val hc⟩)
    (fun w b hb ↦ by
      obtain ⟨c, hc⟩ := hpow _
        (InfinitePlace.ideleInfiniteCoord_unitEmbedding (R := 𝓞 K) w a ▸ hmem.2.1 w) b hb
      exact ⟨c, by simpa using congrArg Units.val hc⟩)
    (hdeg ▸ hdvd) (Set.exists_mem_unit_of_unitLocalPowerClassMap_surjective _ _ _ hsurj)
  have h1 := finrank_eq_one_of_surjective_ideleClassNormMap K _ hnorm
  rw [hdeg, Subgroup.relIndex_eq_one] at h1
  exact h1 (Subgroup.mem_zpowers a)

/-- **The principal ideles in the auxiliary Kummer subgroup.** Let `S` and `T` be disjoint, with
`S` containing the places above `p` and generating the ideal class group, and let the `S`-units
surject onto the local unit `p`-th power classes at `T`. Then the principal idele of `a ∈ Kˣ`
lies in `E_{S,T}` exactly when `a` is an `(S ∪ T)`-unit and a `p`-th power in `K`. -/
theorem unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_iff
    (hp : p.Prime) {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hsurj : Function.Surjective
      (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST p))
    (a : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K a ∈ auxiliaryKummerIdeleSubgroup S T p ↔
      a ∈ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K ∧
        a ∈ (powMonoidHom p : Kˣ →* Kˣ).range := by
  constructor
  · intro ha
    refine ⟨(unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_one_iff S T a).1
      (auxiliaryKummerIdeleSubgroup_le_one S T p ha), ?_⟩
    exact mem_range_powMonoidHom_of_unitEmbedding_mem_auxiliaryKummerIdeleSubgroup
      hp hST hcl hpS hsurj ha
  rintro ⟨hunit, b, rfl⟩
  rw [mem_auxiliaryKummerIdeleSubgroup_iff]
  refine ⟨fun v _ ↦ ⟨Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b, ?_⟩,
    fun w ↦ ⟨Units.map (algebraMap K w.Completion).toMonoidHom b, ?_⟩,
    ((mem_auxiliaryKummerIdeleSubgroup_one_iff S T _).1 <|
      (unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_one_iff S T (b ^ p)).2 hunit)⟩
  · simp [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding]
  · simp [InfinitePlace.ideleInfiniteCoord_unitEmbedding]

/-- **The index of the auxiliary Kummer idele classes.** Let `K` contain the `p`-th roots of
unity, and let `S` and `T` be disjoint finite sets of finite places, with `S` containing the
places above `p` and generating the ideal class group. If the `S`-units surject onto the local
unit `p`-th power classes at `T`, then `[C_K : E_{S,T} Kˣ / Kˣ] · p ^ #T = p ^ (#S + r₁ + r₂)`,
where `r₁ + r₂` is the number of infinite places of `K`. -/
theorem index_auxiliaryKummerIdeleClassSubgroup_mul_pow_card
    (hp : p.Prime) {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hsurj : Function.Surjective
      (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST p)) :
    (auxiliaryKummerIdeleClassSubgroup S T p).index * p ^ T.card =
      p ^ (S.card + Fintype.card (InfinitePlace K)) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hclST : Subgroup.closure (HeightOneSpectrum.classGroupMk (R := 𝓞 K) ''
      ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) = ⊤ :=
    top_unique (hcl ▸ Subgroup.closure_mono (Set.image_mono Set.subset_union_left))
  have h := index_auxiliaryKummerIdeleClassSubgroup_mul_relIndex S T p hclST
  -- The `(S ∪ T)`-units in `E_{S,T}` are the `p`-th powers among them.
  set U := ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K
  have hinf : (auxiliaryKummerIdeleSubgroup S T p).comap (IdeleGroup.unitEmbedding (𝓞 K) K) ⊓ U =
      (powMonoidHom p : Kˣ →* Kˣ).range ⊓ U := by
    ext a
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_comap,
      unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_iff hp hST hcl hpS hsurj]
    tauto
  have hU : ((auxiliaryKummerIdeleSubgroup S T p).comap
      (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex U =
      p ^ (S.card + T.card + Fintype.card (InfinitePlace K)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right,
      relIndex_range_powMonoidHom_sUnits_numberField, ← Finset.coe_union, Nat.card_coe_set_eq,
      Set.ncard_coe_finset, Finset.card_union_of_disjoint (Finset.disjoint_coe.1 hST)]
    ring_nf
  rw [hU, relIndex_auxiliaryKummerIdeleSubgroup_eq_pow S T p hpS] at h
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos (S.card + Fintype.card (InfinitePlace K)))
  rw [mul_assoc, ← pow_add, ← pow_add]
  convert h using 2 <;> ring

end TauCeti.ClassFieldTheory
