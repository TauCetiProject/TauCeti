/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Basic

/-!
# Decomposition-group orbits on cosets and the primes of a fixed field

Let `M / K` be a Galois extension of number fields with group `G`, let `H` be a subgroup of `G`
with fixed field `E = M ^ H`, and let `Q` be a prime of `𝓞 M` above a prime `p` of `𝓞 K`, with
decomposition group `D`. The double coset law of `TauCeti/NumberTheory/RamificationInertia/
DoubleCoset/Basic.lean` indexes the primes of `𝓞 E` above `p` by `H \ G / D`. This file reads
the same law on the left cosets `G ⧸ H`, where `D` acts by translation: the coset `τ H` is
attached to the prime `τ⁻¹ Q ∩ 𝓞 E` (`Ideal.primesOverOfCoset`), two cosets are attached to the
same prime exactly when they lie in one `D`-orbit, every prime arises, and the `D`-orbit of `τ H`
has `e · f` elements, where `e` and `f` are the ramification index and the residue degree of the
attached prime over `p`. Altogether, the multiset of the sizes of the `D`-orbits on `G ⧸ H` is
the multiset of the local degrees `e · f` over the primes of `𝓞 E` above `p`.

This is the form of the double coset law that Dedekind's theorem uses: when `E = K(α)` for a root
`α` of an irreducible polynomial, `G ⧸ H` is the set of roots, and the orbit sizes of a Frobenius
on the roots become the residue degrees of the primes of `E` above `p`.

## Main definitions

* `Ideal.primesOverOfCoset`: the prime `τ⁻¹ Q ∩ 𝓞 (M ^ H)` attached to the coset `τ H`.

## Main results

* `Ideal.primesOverOfCoset_eq_iff`: the fibres of `primesOverOfCoset` are the orbits of the
  decomposition group of `Q`.
* `Ideal.primesOverOfCoset_surjective`: every prime of `𝓞 (M ^ H)` above `p` is attached to a
  coset.
* `Ideal.card_orbit_stabilizer_coset`: the orbit of `τ H` under the decomposition group has
  `e · f` elements, for the prime attached to `τ H`.
* `Ideal.map_card_orbit_stabilizer_eq_map_ramificationIdx_mul_inertiaDeg`: the multiset of orbit
  sizes is the multiset of local degrees over the primes of `𝓞 (M ^ H)` above `p`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open IntermediateField MulAction NumberField

open scoped NumberField Pointwise

namespace Ideal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

variable (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p]
  (H : Subgroup (M ≃ₐ[K] M))

/-- The prime of the fixed field `M ^ H` above `p` attached to a coset `τ H`: the contraction
`τ⁻¹ Q ∩ 𝓞 (M ^ H)`. It does not depend on the representative `τ`, because `H` fixes `M ^ H`
pointwise and so does not move contractions to it. -/
noncomputable def primesOverOfCoset : (M ≃ₐ[K] M) ⧸ H → p.primesOver (𝓞 ↥(fixedField H)) :=
  _root_.Quotient.lift (fun τ => ⟨(τ⁻¹ • Q).under (𝓞 ↥(fixedField H)), inferInstance,
      ⟨by rw [under_under]; exact (inferInstance : (τ⁻¹ • Q).LiesOver p).over⟩⟩) fun τ τ' h => by
    apply Subtype.ext
    change (τ⁻¹ • Q).under _ = (τ'⁻¹ • Q).under _
    rw [under_fixedField_eq_iff_mem_orbit]
    refine ⟨⟨τ⁻¹ * τ', QuotientGroup.leftRel_apply.mp h⟩, ?_⟩
    beta_reduce
    rw [Subgroup.smul_def, smul_smul]
    congr 1
    group

/-- The prime attached to the coset of `τ` is the contraction of `τ⁻¹ Q`. -/
@[simp]
theorem coe_primesOverOfCoset_mk (τ : M ≃ₐ[K] M) :
    (primesOverOfCoset p Q H (τ : (M ≃ₐ[K] M) ⧸ H) : Ideal (𝓞 ↥(fixedField H))) =
      (τ⁻¹ • Q).under (𝓞 ↥(fixedField H)) :=
  (rfl)

/-- **The fibres are the orbits of the decomposition group.** Two cosets are attached to the
same prime of `M ^ H` exactly when one is a translate of the other by the decomposition group of
`Q`. -/
theorem primesOverOfCoset_eq_iff (x y : (M ≃ₐ[K] M) ⧸ H) :
    primesOverOfCoset p Q H x = primesOverOfCoset p Q H y ↔
      x ∈ orbit (stabilizer (M ≃ₐ[K] M) Q) y := by
  induction x using QuotientGroup.induction_on with | H τ => ?_
  induction y using QuotientGroup.induction_on with | H τ' => ?_
  rw [Subtype.ext_iff, coe_primesOverOfCoset_mk, coe_primesOverOfCoset_mk,
    under_fixedField_eq_iff_mem_orbit, mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨h, hh⟩
    rw [Subgroup.smul_def, smul_smul] at hh
    refine ⟨⟨τ * h * τ'⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_assoc, mul_smul, hh, smul_smul, mul_inv_cancel, one_smul]
    · rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul,
        Subgroup.coe_mk, show (τ * (h : M ≃ₐ[K] M) * τ'⁻¹ * τ')⁻¹ * τ = (h : M ≃ₐ[K] M)⁻¹ by
          group]
      exact H.inv_mem h.2
  · rintro ⟨d, hd⟩
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq] at hd
    have hmem : τ⁻¹ * d * τ' ∈ H := by
      have := H.inv_mem hd
      simpa [mul_inv_rev, mul_assoc] using this
    refine ⟨⟨τ⁻¹ * d * τ', hmem⟩, ?_⟩
    rw [Subgroup.smul_def, smul_smul, show τ⁻¹ * (d : M ≃ₐ[K] M) * τ' * τ'⁻¹ = τ⁻¹ * d by group,
      mul_smul, mem_stabilizer_iff.mp d.2]

/-- **Every prime of the fixed field above `p` is attached to a coset.** -/
theorem primesOverOfCoset_surjective [IsGalois K M] :
    Function.Surjective (primesOverOfCoset p Q H) := by
  rintro ⟨𝔮, h𝔮, h𝔮p⟩
  obtain ⟨σ, hσ⟩ := exists_smul_under_fixedField_eq p Q H 𝔮
  exact ⟨((σ⁻¹ : M ≃ₐ[K] M) : (M ≃ₐ[K] M) ⧸ H),
    Subtype.ext (by rw [coe_primesOverOfCoset_mk, inv_inv]; exact hσ)⟩

omit [NumberField K] [NumberField M] in
/-- The stabilizer in `Gal(M/K)` of the coset `τ H` is the conjugate `τ H τ⁻¹`. -/
theorem stabilizer_coset_eq_map_conj (τ : M ≃ₐ[K] M) :
    stabilizer (M ≃ₐ[K] M) (τ : (M ≃ₐ[K] M) ⧸ H) = H.map (MulAut.conj τ).toMonoidHom := by
  rw [show (τ : (M ≃ₐ[K] M) ⧸ H) = τ • ((1 : M ≃ₐ[K] M) : (M ≃ₐ[K] M) ⧸ H) by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one],
    stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient]

/-- **Orbit sizes are local degrees.** The orbit of the coset `τ H` under the decomposition group
of `Q` has as many elements as the ramification index times the residue degree of the prime
`τ⁻¹ Q ∩ 𝓞 (M ^ H)` attached to it. -/
theorem card_orbit_stabilizer_coset [IsGalois K M] (τ : M ≃ₐ[K] M) :
    Nat.card (orbit (stabilizer (M ≃ₐ[K] M) Q) (τ : (M ≃ₐ[K] M) ⧸ H)) =
      ((τ⁻¹ • Q).under (𝓞 ↥(fixedField H))).ramificationIdx (𝓞 K) *
        ((τ⁻¹ • Q).under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) := by
  rw [ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex (τ⁻¹ • Q) H,
    stabilizer_smul_eq_stabilizer_map_conj, ← Subgroup.relIndex_comap,
    Subgroup.comap_equiv_eq_map_symm', Nat.card_congr (orbitEquivQuotientStabilizer _ _),
    ← Subgroup.index_eq_card, Subgroup.relIndex]
  congr 1
  ext d
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.subgroup_smul_def,
    ← mem_stabilizer_iff, stabilizer_coset_eq_map_conj]
  rfl

open scoped Classical in
/-- **The multiset of orbit sizes is the multiset of local degrees.** The sizes of the orbits of
the decomposition group of `Q` on `Gal(M/K) ⧸ H` are, as a multiset, the products `e · f` of
the ramification index and the residue degree over the primes of `𝓞 (M ^ H)` above `p`. -/
theorem map_card_orbit_stabilizer_eq_map_ramificationIdx_mul_inertiaDeg [IsGalois K M]
    [p.IsMaximal] :
    (Finset.univ : Finset (orbitRel.Quotient (stabilizer (M ≃ₐ[K] M) Q)
        ((M ≃ₐ[K] M) ⧸ H))).val.map (fun ω => Nat.card ω.orbit) =
      (Finset.univ : Finset (p.primesOver (𝓞 ↥(fixedField H)))).val.map
        (fun 𝔮 : p.primesOver (𝓞 ↥(fixedField H)) =>
          𝔮.1.ramificationIdx (𝓞 K) * 𝔮.1.inertiaDeg (𝓞 K)) := by
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ Finset.univ.nodup Finset.univ.nodup
    (fun ω _ => primesOverOfCoset p Q H ω.out) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro ω _ ω' _ h
    rw [primesOverOfCoset_eq_iff, ← orbitRel_apply] at h
    exact _root_.Quotient.out_equiv_out.mp h
  · intro 𝔮 _
    obtain ⟨x, hx⟩ := primesOverOfCoset_surjective p Q H 𝔮
    refine ⟨_root_.Quotient.mk'' x, Finset.mem_univ _, ?_⟩
    rw [← hx, primesOverOfCoset_eq_iff, ← orbitRel_apply]
    exact _root_.Quotient.mk_out' x
  · intro ω _
    rw [orbitRel.Quotient.orbit_eq_orbit_out ω _root_.Quotient.out_eq']
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective ω.out
    rw [← hτ, card_orbit_stabilizer_coset, coe_primesOverOfCoset_mk]

end Ideal
