/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
import TauCeti.NumberTheory.NumberField.Kummer.SUnitRadical

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
* `TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_le_of_finrank_prime`: the Kummer case
  of the second fundamental inequality, `[C_K : N_{L/K}(C_L)] ≤ p`.

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

/-! ### The Kummer case of the second fundamental inequality -/

/-- **The Kummer case of the second fundamental inequality.** Let `L/K` be a Galois extension of
number fields of prime degree `p`, and suppose that `K` contains the `p`-th roots of unity. Then
the idele-class norm group has index at most `p`:
`[C_K : N_{L/K}(C_L)] ≤ p`. -/
theorem index_range_ideleClassNormMap_le_of_finrank_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity K p]
    (hfin : Module.finrank K L = p) :
    (GlobalNumberFields.ideleClassNormMap K L).range.index ≤ p := by
  classical
  -- Choose a finite set `S` containing the places above `p` and the ramified places of `L/K`,
  -- whose classes generate the class group. Kummer theory embeds `L` into `M = K(U_S^{1/p})`.
  -- The auxiliary places theorem supplies `T` with `p ^ #T = [M : L]` and an inclusion
  -- `E_{S,T} ⊆ N_{L/K}(C_L)`. The index formula for `E_{S,T}`, together with
  -- `[M : K] = p ^ (#S + r₁ + r₂)`, then cancels the factor `p ^ #T` and gives the bound.
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let F := ι.fieldRange
  have hFfin : Module.finrank K F = p :=
    (LinearEquiv.finrank_eq ι.equivFieldRange.symm.toLinearEquiv).trans hfin
  have : NumberField F :=
    have : FiniteDimensional K F := ι.equivFieldRange.toLinearEquiv.finiteDimensional
    .of_module_finite K F
  have : IsGalois K F := IsGalois.of_algEquiv ι.equivFieldRange
  have : Fact (Nat.card Gal(F/K)).Prime :=
    ⟨(IsGalois.card_aut_eq_finrank K F).trans hFfin |>.symm ▸ Fact.out⟩
  have : IsCyclic Gal(F/K) := isCyclic_of_prime_card rfl
  obtain ⟨S₀, hS₀fin, hS₀⟩ :=
    ClassGroup.exists_finite_closure_classGroupMk_image_eq_top (R := NumberField.RingOfIntegers K)
  have hp0 : Ideal.span ({(p : NumberField.RingOfIntegers K)} :
      Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    hS₀fin.toFinset ∪ TauCeti.NumberField.ramifiedSupport K F ∪
      (Ideal.finite_factors hp0).toFinset
  have hS₀S : S₀ ⊆ (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (hS₀fin.mem_toFinset.mpr hv))
  have hS : Subgroup.closure (HeightOneSpectrum.classGroupMk ''
      (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))) = ⊤ :=
    top_unique (hS₀ ▸ Subgroup.closure_mono (Set.image_mono hS₀S))
  have hpS (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
      (hv : (p : NumberField.RingOfIntegers K) ∈ v.asIdeal) : v ∈ S := by
    refine Finset.mem_union_right _ ((Ideal.finite_factors hp0).mem_toFinset.mpr ?_)
    exact Ideal.dvd_span_singleton.mpr hv
  have hram (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (hv : v ∉ (S : Set _)) :
      ∃ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
        w.asIdeal.LiesOver v.asIdeal ∧
          Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) w.asIdeal := by
    obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers F) v
    have hwv : w.asIdeal.LiesOver v.asIdeal := hw ▸ inferInstance
    refine ⟨w, hwv, TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v ?_ w.asIdeal⟩
    exact fun hvram ↦ hv (Finset.mem_union_left _ (Finset.mem_union_right _ hvram))
  have hFM : F ≤ kummerField (SeparableClosure K) p
      ((S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))).unit K) :=
    TauCeti.NumberField.le_kummerField_sUnits_of_isCyclic hS (hFfin ▸ dvd_rfl) hram
  let M := kummerField (SeparableClosure K) p
    ((S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))).unit K)
  let F' : IntermediateField K M := F.comap M.val
  have hFM' : F ≤ M.val.fieldRange := by
    intro x hx
    exact ⟨⟨x, hFM hx⟩, rfl⟩
  have hmap : F'.map M.val = F := IntermediateField.map_comap_eq_self hFM'
  let eFM : F' ≃ₐ[K] F :=
    (IntermediateField.equivMap F' M.val).trans (IntermediateField.equivOfEq hmap)
  have hF'fin : Module.finrank K F' = p := by
    rw [← hFfin]
    exact LinearEquiv.finrank_eq eFM.toLinearEquiv
  have : NumberField F' := NumberField.of_module_finite K F'
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K p
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))).unit K,
      ∃ x : SeparableClosure K, x ^ p = algebraMap K (SeparableClosure K) (a : K) := by
    intro a _
    exact IsSepClosed.exists_pow_nat_eq _ p
  obtain ⟨T, hST, hcard, hsurj, hnorm⟩ :=
    exists_auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap
      (E := SeparableClosure K) (Fact.out : p.Prime) S hpS hζ.toInteger_isPrimitiveRoot
      hroots F'
  have haux := index_auxiliaryKummerIdeleClassSubgroup_mul_pow_card
    (K := K) (Fact.out : p.Prime) hST hS hpS hsurj
  have hMfin : Module.finrank K M =
      p ^ (Fintype.card (InfinitePlace K) + S.card) := by
    rw [finrank_kummerField hroots, relIndex_range_powMonoidHom_sUnits_numberField,
      Nat.card_coe_set_eq, Set.ncard_coe_finset]
  let _ : Module.Free F' M := Module.Free.of_divisionRing F' M
  let _ : Module.Finite F' M := Module.Finite.of_restrictScalars_finite K F' M
  have hauxIndex : (auxiliaryKummerIdeleClassSubgroup (K := K) S T p).index = p := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos T.card)
    rw [haux, add_comm S.card, ← hMfin, ← Module.finrank_mul_finrank K F' M,
      hF'fin, ← hcard]
  have hdvd : (GlobalNumberFields.ideleClassNormMap K F').range.index ∣ p := by
    rw [← hauxIndex]
    exact Subgroup.index_dvd_of_le hnorm
  have hFle : (GlobalNumberFields.ideleClassNormMap K F).range.index ≤ p :=
    (congrArg Subgroup.index
      (GlobalNumberFields.range_ideleClassNormMap_eq_of_algEquiv eFM)).symm.trans_le
      (Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd)
  exact (congrArg Subgroup.index
    (GlobalNumberFields.range_ideleClassNormMap_eq_of_algEquiv ι.equivFieldRange)).trans_le hFle

end TauCeti.ClassFieldTheory
