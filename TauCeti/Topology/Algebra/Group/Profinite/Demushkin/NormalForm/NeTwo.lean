/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.OddPrime
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.QInvariant
public import TauCeti.Topology.Algebra.Group.Profinite.Free.BracketSpan
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ElementaryAutomorphism

/-!
# Labute's normal form for `q ≠ 2`

Let `F = freeProP p (Fin n)` be the free pro-`p` group on `n` generators and let `r ∈ Φ(F)` be a
relator presenting a Demushkin group `G = ⟨x₁, …, x_n ∣ r⟩` with `q`-invariant `q = q(G)`. Labute's
Theorem 3 says that for `q ≠ 2` a continuous automorphism of `F` carries `r` to the normal-form word
`x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, so that `G` is presented by that word. The case `q = p` at
an odd prime is proved in `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.OddPrime`,
where the basis-modification map `δ_ρ` is onto in every degree. This file proves the remaining
cases `q ≠ p`, that is `q = 0` and `q = p^f` with `f ≥ 2`, for every prime `p` including `p = 2`,
and assembles the theorem for every `q ≠ 2`.

For `q ≠ p` every exponent sum of `r` is divisible by `p ^ 2`, so the class of `r` in `gr_1(F)` has
no `p`-power part and the basis-modification map `δ_ρ` is no longer onto in every degree: the
successive approximation cannot change the exponent vector of the relator, and has to be run with
that vector held fixed. The normal form is therefore first proved for a relator whose exponent
vector is already `q e₁`, with `p ^ 2 ∣ q` and nondegenerate degree-one form. The elementary
automorphisms of `TauCeti.Topology.Algebra.Group.Profinite.Free.ElementaryAutomorphism` carry the
exponent vector of any relator presenting a Demushkin group with `q(G) ≠ p` to `q(G) e₁`, which
gives the theorem for `q(G) ≠ p`; together with the case `q = p` this is Labute's Theorem 3 for
every `q ≠ 2`. The normal form is the input to the uniqueness theorem of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Uniqueness`: two Demushkin groups
with the same rank and the same `q`-invariant `q ≠ 2` are topologically isomorphic.

## Main results

* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_toAdd_exponentSum_eq`:
  a relator with nondegenerate degree-one form and exponent vector `q e₁`, `p ^ 2 ∣ q`, is carried
  to `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` by a continuous automorphism of `F`.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne`: a
  relator in `Φ(F)` presenting a Demushkin group with `q(G) ≠ p` is carried to
  `x₁^{q(G)} (x₁, x₂) ⋯ (x_{n-1}, x_n)`.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne_two`:
  **Labute's Theorem 3 for `q ≠ 2`**, the same for every `q(G) ≠ 2`.
* `TauCeti.freeProP.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two`
  and its intrinsic form
  `IsDemushkin.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two`:
  a Demushkin group with `q(G) ≠ 2` is topologically isomorphic to
  `⟨x₁, …, x_n ∣ x₁^{q(G)} (x₁, x₂) ⋯ (x_{n-1}, x_n)⟩` on `n = demushkinRank hG` generators.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Proposition 5 and Theorem 3.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
-/

public section

namespace TauCeti

universe u v

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the coordinate
-- hypotheses below are stated over the module structure of `ZMod p` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

namespace freeProP

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **Labute's normal form for a relator with exponent vector `q e₁`, `p ^ 2 ∣ q`.** Let `F` be the
free pro-`p` group on `n` generators and let `r ∈ λ_1(F)` be a relator whose class in `gr_1(F)` has
nondegenerate degree-one form, and whose exponent sums are `q` at `x₁` and `0` at the other
generators, for some `q` divisible by `p ^ 2`. Then a continuous automorphism of `F` carries `r` to
`x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_toAdd_exponentSum_eq
    (r : pLowerCentralSeries p (freeProP p (Fin n)) 1)
    (hnd : (degreeOneForm (gradedMk p (freeProP p (Fin n)) 1 r)).Nondegenerate)
    {q : ℕ} (hq : p ^ 2 ∣ q)
    (hv : ∀ k : Fin n, (exponentSum p (Fin n) (r : freeProP p (Fin n))).toAdd k =
      if (k : ℕ) = 0 then (q : ℤ_[p]) else 0) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      e r = demushkinWordNeTwo q n (freeProPGen p n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨ContinuousMulEquiv.refl _, Subsingleton.elim _ _⟩
  have hpq : p ∣ q := (dvd_pow_self p two_ne_zero).trans hq
  have hq' : (p : ℤ_[p]) ^ 2 ∣ (q : ℤ_[p]) := by
    have h := Nat.cast_dvd_cast (α := ℤ_[p]) hq
    rwa [Nat.cast_pow] at h
  -- The `p`-power coordinates of the class of `r` vanish, so its degree-one form is alternating.
  have hc : ∀ k, (degreeOneBasis p (Fin n)).repr (gradedMk p (freeProP p (Fin n)) 1 r)
      (Sum.inl k) = 0 := by
    intro k
    rw [degreeOneBasis_repr_gradedMk_inl_eq_zero_iff, hv]
    split_ifs
    · exact hq'
    · exact dvd_zero _
  -- The normal form modulo `λ_2(F)` by an automorphism `e₁` fixing `x₁`.
  obtain ⟨-, e₁, he₁0, he₁⟩ :=
    exists_continuousMulEquiv_freeProPGen_zero_eq_inv_mul_demushkinWordNeTwo_mem r hnd
      (isAlt_degreeOneForm_of_repr_inl_eq_zero _ hc) hpq hv
  set f : freeProP p (Fin n) →ₜ* freeProP p (Fin n) :=
    (e₁ : freeProP p (Fin n) →ₜ* freeProP p (Fin n)) with hf
  have hmem : f r ∈ pLowerCentralSeries p (freeProP p (Fin n)) 1 :=
    f.toMonoidHom.map_pLowerCentralSeries_le f.continuous 1 ⟨r, r.2, rfl⟩
  -- `e₁ r` and the normal-form word have the same class in `gr_1(F)`.
  have hclass : gradedMk p (freeProP p (Fin n)) 1 ⟨f r, hmem⟩ =
      gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo q n (freeProPGen p n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hpq n _⟩ := by
    rw [gradedMk_eq_gradedMk_iff]
    exact QuotientGroup.eq.mpr he₁
  -- They have the same exponent vector `q e₁`, because `e₁` fixes `x₁`.
  have hrw : exponentSum p (Fin n) (f r) =
      exponentSum p (Fin n) (demushkinWordNeTwo q n (freeProPGen p n)) := by
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_exponentSum_demushkinWordNeTwo, hf, toAdd_exponentSum_apply_eq_sum_smul,
      Finset.sum_eq_single ⟨0, hn⟩ (fun k _ hk ↦ by
        rw [hv, ite_eq_right fun h ↦ hk (Fin.ext h), zero_smul])
        (fun h ↦ (h (Finset.mem_univ _)).elim),
      hv, ite_eq_left rfl, ContinuousMonoidHom.coe_coe, ← freeProPGen_of_lt p hn, he₁0]
  -- The class of `e₁ r` has derivatives spanning `gr_0(F)` and no `p`-power part.
  have hr' : gradedMk p (freeProP p (Fin n)) 1 ⟨f r, hmem⟩ =
      gradedMap p f.toMonoidHom f.continuous 1 (gradedMk p (freeProP p (Fin n)) 1 r) := by
    rw [gradedMap_gradedMk]
    rfl
  have hρ : Submodule.span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p (Fin n) i
      (gradedMk p (freeProP p (Fin n)) 1 ⟨f r, hmem⟩)) = ⊤ := by
    rw [span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm, hr']
    exact (nondegenerate_degreeOneForm_gradedMap_iff e₁ _).2 hnd
  have hc' : ∀ i, (degreeOneBasis p (Fin n)).repr (gradedMk p (freeProP p (Fin n)) 1 ⟨f r, hmem⟩)
      (Sum.inl i) = 0 := by
    intro i
    rw [degreeOneBasis_repr_gradedMk_inl_eq_zero_iff, hrw, toAdd_exponentSum_demushkinWordNeTwo,
      Pi.smul_apply, smul_eq_mul]
    exact hq'.mul_right _
  -- The deviations in the closed commutator subgroup are absorbed by corrections lying in the
  -- commutator subgroup at `x₁`, the only generator carrying a nonzero exponent.
  have hspan : ∀ m (hm : 1 ≤ m), ∀ z : pLowerCentralSeries p (freeProP p (Fin n)) (m + 1),
      (z : freeProP p (Fin n)) ∈ (commutator (freeProP p (Fin n))).topologicalClosure →
      ∃ ω : Fin n → pLowerCentralSeries p (freeProP p (Fin n)) m,
        (∀ i, (exponentSum p (Fin n) (f r)).toAdd i ≠ 0 →
          (ω i : freeProP p (Fin n)) ∈ (commutator (freeProP p (Fin n))).topologicalClosure) ∧
        basisModificationDelta p (Fin n) hm (gradedMk p (freeProP p (Fin n)) 1 ⟨f r, hmem⟩)
          (fun i ↦ gradedMk p (freeProP p (Fin n)) m (ω i)) =
            gradedMk p (freeProP p (Fin n)) (m + 1) z := by
    intro m hm z hz
    obtain ⟨ω, hω₀, hω⟩ := exists_apply_mem_commutator_basisModificationDelta_eq_of_mem_range hm hρ
      hc' ⟨0, hn⟩ (gradedMk_mem_range_basisModificationDelta_of_mem_topologicalClosure_commutator
        hm hρ hc' z hz)
    refine ⟨ω, fun i hi ↦ ?_, hω⟩
    obtain rfl : i = ⟨0, hn⟩ := by
      by_contra h
      apply hi
      rw [hrw, toAdd_exponentSum_demushkinWordNeTwo, Pi.smul_apply,
        toAdd_exponentSum_freeProPGen_apply, ite_eq_right fun h' ↦ h (Fin.ext h'), smul_zero]
    exact Subgroup.le_topologicalClosure _ hω₀
  obtain ⟨e₂, he₂⟩ := exists_continuousMulEquiv_apply_eq_of_exponentSum_eq ⟨f r, hmem⟩
    ⟨demushkinWordNeTwo q n (freeProPGen p n),
      demushkinWordNeTwo_mem_pLowerCentralSeries_one hpq n _⟩ hclass hrw hspan
  exact ⟨e₁.trans e₂, he₂⟩

/-- **Labute's normal form for `q ≠ p`** (Labute, Theorem 3, the cases `q = 0` and `q = p^f` with
`f ≥ 2`). Let `r ∈ Φ(F)` be a relator of the free pro-`p` group on `n` generators presenting a
Demushkin group `G = ⟨x₁, …, x_n ∣ r⟩` with `q`-invariant `q(G) ≠ p`. Then a continuous
automorphism of `F` carries `r` to `x₁^{q(G)} (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne
    {r : freeProP p (Fin n)} (hr : r ∈ proPFrattini p (freeProP p (Fin n)))
    (hG : IsDemushkin p (presentedProP p (Fin n) {r})) (hq : demushkinQ hG ≠ p) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      e r = demushkinWordNeTwo (demushkinQ hG) n (freeProPGen p n) := by
  have hn : 0 < n := by simpa using hG.card_pos_presentedProP
  have hr₁ : r ∈ pLowerCentralSeries p (freeProP p (Fin n)) 1 :=
    (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr
  have hpr : ∀ x, (p : ℤ_[p]) ∣ (exponentSum p (Fin n) r).toAdd x :=
    dvd_exponentSum_of_mem_proPFrattini p (Fin n) hr
  -- `q(G) ≠ p` says that every exponent sum of `r` is divisible by `p ^ 2`.
  have hsq : ∀ x, (p : ℤ_[p]) ^ 2 ∣ (exponentSum p (Fin n) r).toAdd x := fun x ↦
    by_contra fun hx ↦ hq ((demushkinQ_presentedProP_eq_iff_exists_not_dvd hG hpr).2 ⟨x, hx⟩)
  -- An automorphism `e₁` carries the exponent vector of `r` to `q₀ e₁`, where `q₀` is a coordinate
  -- of that vector dividing all the others.
  obtain ⟨x₁, e₁, hx₁, he₁⟩ := exists_continuousMulEquiv_toAdd_exponentSum_eq_single r ⟨0, hn⟩
  obtain ⟨w, hw, hv⟩ := exists_eq_smul_of_forall_dvd hx₁
  -- The `q`-invariant is `q₀` up to a unit `u` of `ℤ_p`, and it is divisible by `p ^ 2`.
  obtain ⟨u, hu, hq2⟩ : ∃ u : ℤ_[p]ˣ,
      (u : ℤ_[p]) * (exponentSum p (Fin n) r).toAdd x₁ = (demushkinQ hG : ℤ_[p]) ∧
        p ^ 2 ∣ demushkinQ hG := by
    by_cases hq0 : (exponentSum p (Fin n) r).toAdd x₁ = 0
    · rw [(demushkinQ_presentedProP_eq_zero_iff hw hv hG (hpr x₁)).2 hq0, hq0]
      exact ⟨1, by rw [mul_zero, Nat.cast_zero], dvd_zero _⟩
    · rw [demushkinQ_presentedProP_eq_pow_valuation hw hv hG (hpr x₁) hq0]
      refine ⟨(PadicInt.unitCoeff hq0)⁻¹, ?_, pow_dvd_pow p ?_⟩
      · rw [Nat.cast_pow, Units.inv_mul_eq_iff_eq_mul]
        exact PadicInt.unitCoeff_spec hq0
      · rw [← PadicInt.mem_span_pow_iff_le_valuation _ hq0, Ideal.mem_span_singleton]
        exact hsq x₁
  -- The dilation `x₁ ↦ x₁ ^ u` brings the exponent vector to `q(G) e₁`.
  set e₁₂ : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n) := e₁.trans (dilation ⟨0, hn⟩ u) with he₁₂
  have hmem : e₁₂ r ∈ pLowerCentralSeries p (freeProP p (Fin n)) 1 :=
    (e₁₂ : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom.map_pLowerCentralSeries_le
      (e₁₂ : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1 ⟨r, hr₁, rfl⟩
  have hv' : ∀ k : Fin n, (exponentSum p (Fin n) (e₁₂ r)).toAdd k =
      if (k : ℕ) = 0 then ((demushkinQ hG : ℕ) : ℤ_[p]) else 0 := by
    intro k
    rw [he₁₂, ContinuousMulEquiv.trans_apply, toAdd_exponentSum_dilation, he₁]
    by_cases hk : (k : ℕ) = 0
    · obtain rfl : k = ⟨0, hn⟩ := Fin.ext hk
      rw [Function.update_self, Pi.single_eq_same, hu, ite_eq_left rfl]
    · have hk' : k ≠ ⟨0, hn⟩ := fun h ↦ hk (congrArg Fin.val h)
      rw [Function.update_of_ne hk', Pi.single_eq_of_ne hk', ite_eq_right hk]
  -- The class of `e₁₂ r` still has nondegenerate degree-one form.
  have hnd : (degreeOneForm (gradedMk p (freeProP p (Fin n)) 1 ⟨e₁₂ r, hmem⟩)).Nondegenerate := by
    have h : gradedMk p (freeProP p (Fin n)) 1 ⟨e₁₂ r, hmem⟩ =
        gradedMap p (e₁₂ : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
          (e₁₂ : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1
          (gradedMk p (freeProP p (Fin n)) 1 ⟨r, hr₁⟩) := by
      rw [gradedMap_gradedMk]
      rfl
    rw [h]
    exact (nondegenerate_degreeOneForm_gradedMap_iff e₁₂ _).2
      (hG.nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _))
  obtain ⟨e₃, he₃⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_toAdd_exponentSum_eq ⟨e₁₂ r, hmem⟩
      hnd hq2 hv'
  exact ⟨e₁₂.trans e₃, he₃⟩

/-- **Labute's normal form for `q ≠ 2`** (Labute, Theorem 3, the case `q ≠ 2`). Let `r ∈ Φ(F)` be
a relator of the free pro-`p` group on `n` generators presenting a Demushkin group
`G = ⟨x₁, …, x_n ∣ r⟩` with `q`-invariant `q(G) ≠ 2`. Then a continuous automorphism of `F`
carries `r` to `x₁^{q(G)} (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne_two
    {r : freeProP p (Fin n)} (hr : r ∈ proPFrattini p (freeProP p (Fin n)))
    (hG : IsDemushkin p (presentedProP p (Fin n) {r})) (hq : demushkinQ hG ≠ 2) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      e r = demushkinWordNeTwo (demushkinQ hG) n (freeProPGen p n) := by
  by_cases hqp : demushkinQ hG = p
  · -- For `q(G) = p` the prime is odd, and the relator has a nonzero `p`-power part.
    have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two fun h ↦ hq (hqp.trans h)
    rw [hqp]
    exact exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_odd hp _
      (hG.nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _))
      ((demushkinQ_presentedProP_eq_iff_exists_degreeOneBasis_repr_inl_ne_zero hr hG).1 hqp)
  · exact exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne hr hG hqp

/-- **Labute's normal form for a one-relator Demushkin group with `q ≠ 2`.** Let `r ∈ Φ(F)` be a
relator of the free pro-`p` group on `n` generators presenting a Demushkin group with
`q`-invariant `q(G) ≠ 2`. Then `⟨x₁, …, x_n ∣ r⟩` is topologically isomorphic to
`⟨x₁, …, x_n ∣ x₁^{q(G)} (x₁, x₂) ⋯ (x_{n-1}, x_n)⟩`. -/
theorem exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two
    {r : freeProP p (Fin n)} (hr : r ∈ proPFrattini p (freeProP p (Fin n)))
    (hG : IsDemushkin p (presentedProP p (Fin n) {r})) (hq : demushkinQ hG ≠ 2) :
    Nonempty (presentedProP p (Fin n) {r} ≃ₜ*
      presentedProP p (Fin n) {demushkinWordNeTwo (demushkinQ hG) n (freeProPGen p n)}) := by
  obtain ⟨e, he⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_demushkinQ_ne_two hr hG hq
  exact ⟨presentedProP.congrSingleton e he⟩

end freeProP

/-- **Labute's normal form for a Demushkin group with `q ≠ 2`, intrinsic form** (Labute,
Theorem 3, the case `q ≠ 2`). A Demushkin group `G` with `q`-invariant `q(G) ≠ 2` is topologically
isomorphic to `⟨x₁, …, x_n ∣ x₁^{q(G)} (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` on `n = demushkinRank hG`
generators. -/
theorem IsDemushkin.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsDemushkin p G) (hq : demushkinQ hG ≠ 2) :
    Nonempty (G ≃ₜ* presentedProP p (Fin (demushkinRank hG))
      {demushkinWordNeTwo (demushkinQ hG) (demushkinRank hG)
        (freeProPGen p (demushkinRank hG))}) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin
  have : Nonempty (Fin (demushkinRank hG)) := ⟨⟨0, hG.demushkinRank_pos⟩⟩
  have hG' : IsDemushkin p (presentedProP p (Fin (demushkinRank hG)) {r}) :=
    isDemushkin_of_nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _)
      (hG.nondegenerate_degreeOneForm hr e)
  have hqq : demushkinQ hG' = demushkinQ hG := demushkinQ_congr hG' hG e
  obtain ⟨e'⟩ :=
    freeProP.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two hr hG'
      (hqq ▸ hq)
  rw [hqq] at e'
  exact ⟨e.symm.trans e'⟩

end TauCeti
