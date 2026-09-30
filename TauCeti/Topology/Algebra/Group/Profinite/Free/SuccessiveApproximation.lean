/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Comparison
import TauCeti.Algebra.Group.Subgroup.Congruence

/-!
# Successive approximation of a relator by basis modifications

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with lower
`p`-series `λ_k = λ_k(F)`, and let `r, w ∈ λ_1(F)` be two relators with the same class
`ρ ∈ gr_1(F)`, that is `r ≡ w mod λ_2(F)`. The basis modification `θ_w : x_i ↦ x_i * w_i` by a
family `w : X → λ_m(F)` moves `r` inside its coset modulo `λ_{m+1}(F)` by the class
`δ_ρ(ω) ∈ gr_{m+1}(F)` of `TauCeti.freeProP.basisModificationDelta`, and it leaves the class `ρ`
unchanged. So a congruence `r ≡ w mod λ_{m+1}` improves to a congruence modulo `λ_{m+2}` by one
basis modification at level `m` as soon as the class of the deviation `r⁻¹ * w` in `gr_{m+1}(F)`
lies in the image of `δ_ρ` (`TauCeti.freeProP.inv_basisModification_mul_mem_pLowerCentralSeries`),
and finitely many modifications carry `r` to `w` modulo any term of the series.

The limit is taken by
`TauCeti.IsProP.exists_continuousMulEquiv_apply_eq_of_forall_exists_surjective` of
`TauCeti.Topology.Algebra.Group.Profinite.ProP.Comparison`, which holds in any topologically
finitely generated pro-`p` group: the finite approximations are surjective endomorphisms of `F` by
Burnside's criterion (`TauCeti.IsProP.surjective_of_forall_inv_mul_mem_pLowerCentralSeries_one`),
and the levelwise comparison schema assembles them into a continuous automorphism `e` of `F` with
`e r = w`.

Two successive-approximation theorems follow, according to the span statement available for `ρ`.

* When `δ_ρ` is onto `gr_{m+1}(F)` for every `m ≥ 1`, every deviation is absorbed
  (`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top`).
  This hypothesis is established for the relators `x₁^p (x₁, x₂) (x₃, x₄) ⋯` at odd `p`
  (`TauCeti.freeProP.range_basisModificationDelta_eq_top_of_odd`).
* When `ρ` has no `p`-power part, `Im δ_ρ` misses the classes `π^{m+1} ξ_i` of the `p`-powers of
  the generators, so `δ_ρ` is not onto `gr_{m+1}(F)`. The **relative** theorem
  (`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_exponentSum_eq`) works with a span
  statement for the classes of the elements of the closed commutator subgroup
  `K = closure [F, F]`: it assumes that `r` and `w` have the same exponent vector
  `v = exponentSum r`, and that every deviation in `λ_{m+1}(F) ∩ K` is `δ_ρ` of a level-`m`
  correction `ω` with `ω_i ∈ K` at every generator `i` with `v_i ≠ 0`. This guarantees absorption
  for the deviations lying in `K`, and such a correction preserves the exponent vector of the
  relator (`TauCeti.freeProP.exponentSum_basisModification`), which keeps the deviation in `K` at
  every level. The intended application is to the relators
  `x₁^q (x₁, x₂) (x₃, x₄) ⋯` with `q = 0` or `q = p^f`, `f ≥ 2`, whose `p`-power part `x₁^q` lies
  in `λ_2(F)`; this file does not establish the hypothesis on the corrections for them, and the
  theorem is conditional on it.
  For `q = 0` the relator lies in `K`, the exponent vector vanishes and the constraint on `ω` is
  empty, so the hypothesis reduces to `Im δ_ρ` containing every class of an element of
  `λ_{m+1}(F) ∩ K`.

This is the successive-approximation argument of Labute's classification of Demushkin groups: span
statements for `δ_ρ`, such as those of
`TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification`, supply the hypotheses, and the
conclusions bring a relator congruent to a normal-form word modulo `λ_2(F)` to that word exactly.

## Main results

* `TauCeti.freeProP.inv_basisModification_mul_mem_pLowerCentralSeries`: one step of the
  approximation, a basis modification absorbing the class of the deviation.
* `TauCeti.freeProP.exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries` and its
  relative form `…_of_exponentSum_eq`: the finite approximations, one basis modification per
  level, in the two settings.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top`
  is **the successive-approximation theorem**: a continuous automorphism of `F` carries `r` to `w`
  when `δ_ρ` is onto in every degree.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_exponentSum_eq` is **the relative
  successive-approximation theorem**: a continuous automorphism of `F` carries `r` to `w` when the
  two relators have the same exponent vector and `δ_ρ` absorbs the deviations in the closed
  commutator subgroup by corrections preserving that vector.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5 and the proof of Theorem 3.
-/

public section

namespace TauCeti.freeProP

open Subgroup

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Finite X] [LinearOrder X]

/-! ### One step of the approximation -/

/-- **One step of the successive approximation.** Let `s ∈ λ_1(F)` and `w ∈ F` with
`s⁻¹ * w ∈ λ_{m+1}(F)`, `m ≥ 1`, and let `ω : X → λ_m(F)` be a family whose classes satisfy
`δ_σ(⟦ω⟧) = ` the class of `s⁻¹ * w` in `gr_{m+1}(F)`, where `σ ∈ gr_1(F)` is the class of `s`. Then
the basis modification `θ_ω` improves the congruence by one level: `(θ_ω s)⁻¹ * w ∈ λ_{m+2}(F)`. -/
theorem inv_basisModification_mul_mem_pLowerCentralSeries {m : ℕ} (hm : 1 ≤ m)
    (s : pLowerCentralSeries p (freeProP p X) 1) (w : freeProP p X)
    (hs : (s : freeProP p X)⁻¹ * w ∈ pLowerCentralSeries p (freeProP p X) (m + 1))
    (ω : X → pLowerCentralSeries p (freeProP p X) m)
    (hω : basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 s)
        (fun i ↦ gradedMk p (freeProP p X) m (ω i)) =
      gradedMk p (freeProP p X) (m + 1) ⟨(s : freeProP p X)⁻¹ * w, hs⟩) :
    (basisModification ω s)⁻¹ * w ∈ pLowerCentralSeries p (freeProP p X) (m + 2) := by
  have key := gradedMk_inv_mul_basisModification hm ω s
  rw [hω] at key
  have h : ((s : freeProP p X)⁻¹ * basisModification ω s)⁻¹ * ((s : freeProP p X)⁻¹ * w) ∈
      pLowerCentralSeries p (freeProP p X) (m + 2) :=
    QuotientGroup.eq.mp (gradedMk_eq_gradedMk_iff.mp key)
  rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at h

/-! ### The finite approximations -/

/-- **Finite successive approximation.** Let `r, w ∈ λ_1(F)` have the same class `ρ ∈ gr_1(F)`,
and suppose `δ_ρ` is onto `gr_{m+1}(F)` for `1 ≤ m ≤ k`. Then there is a continuous endomorphism
`φ` of `F`, congruent to the identity modulo `λ_1(F)`, with `φ r ≡ w mod λ_{k+2}(F)`. -/
theorem exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w) (k : ℕ)
    (hspan : ∀ m (hm : 1 ≤ m), m ≤ k →
      LinearMap.range (basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)) = ⊤) :
    ∃ φ : freeProP p X →ₜ* freeProP p X,
      (∀ g, g⁻¹ * φ g ∈ pLowerCentralSeries p (freeProP p X) 1) ∧
        (φ r)⁻¹ * w ∈ pLowerCentralSeries p (freeProP p X) (k + 2) := by
  induction k with
  | zero =>
    refine ⟨ContinuousMonoidHom.id _, fun g ↦ ?_, ?_⟩
    · simp
    · simpa using QuotientGroup.eq.mp (gradedMk_eq_gradedMk_iff.mp h)
  | succ k ih =>
    obtain ⟨φ, hφ, hr⟩ := ih fun m hm hmk ↦ hspan m hm (hmk.trans k.le_succ)
    -- `φ r` is again a relator with class `ρ`: `φ` is congruent to the identity modulo `λ_2` on
    -- `λ_1`.
    have hφr : φ r ∈ pLowerCentralSeries p (freeProP p X) 1 :=
      φ.toMonoidHom.map_pLowerCentralSeries_le φ.continuous 1 ⟨r, r.2, rfl⟩
    have hρ : gradedMk p (freeProP p X) 1 ⟨φ r, hφr⟩ = gradedMk p (freeProP p X) 1 r := by
      rw [gradedMk_eq_gradedMk_iff]
      exact (QuotientGroup.eq.mpr
        (inv_mul_apply_mem_pLowerCentralSeries φ.toMonoidHom φ.continuous hφ r.2)).symm
    -- The class in `gr_{k+2}(F)` of the deviation `(φ r)⁻¹ * w` is `δ_ρ(v)` for some `v`; lift the
    -- `v_i` to `w_i ∈ λ_{k+1}(F)` and modify the basis by them.
    obtain ⟨v, hv⟩ := LinearMap.range_eq_top.mp (hspan (k + 1) (by omega) le_rfl)
      (gradedMk p (freeProP p X) (k + 1 + 1) ⟨(φ r)⁻¹ * w, hr⟩)
    choose ω hω using fun i ↦ gradedMk_surjective (k + 1) (v i)
    refine ⟨(basisModification ω).comp φ, fun g ↦ ?_, ?_⟩
    · rw [ContinuousMonoidHom.coe_comp, Function.comp_apply]
      exact inv_mul_apply_apply_mem (fun g ↦ pLowerCentralSeries_antitone (by omega)
        (inv_mul_basisModification_mem_pLowerCentralSeries ω g)) hφ g
    · rw [ContinuousMonoidHom.coe_comp, Function.comp_apply]
      refine inv_basisModification_mul_mem_pLowerCentralSeries le_add_self ⟨φ r, hφr⟩ w hr ω ?_
      rw [hρ, funext hω, hv]

/-- **Finite successive approximation, relative form.** Let `r, w ∈ λ_1(F)` have the same class
`ρ ∈ gr_1(F)` and the same exponent vector `v = exponentSum r`, and suppose that for `1 ≤ m ≤ k`
every element of `λ_{m+1}(F)` lying in the closed commutator subgroup `K` has class `δ_ρ(⟦ω⟧)` for a
family `ω : X → λ_m(F)` with `ω_i ∈ K` at every generator `i` with `v_i ≠ 0`. Then there is a
continuous endomorphism `φ` of `F`, congruent to the identity modulo `λ_1(F)`, preserving the
exponent vector of `r`, with `φ r ≡ w mod λ_{k+2}(F)`. -/
theorem exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries_of_exponentSum_eq
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w)
    (hrw : exponentSum p X r = exponentSum p X w) (k : ℕ)
    (hspan : ∀ m (hm : 1 ≤ m), m ≤ k → ∀ z : pLowerCentralSeries p (freeProP p X) (m + 1),
      (z : freeProP p X) ∈ (commutator (freeProP p X)).topologicalClosure →
      ∃ ω : X → pLowerCentralSeries p (freeProP p X) m,
        (∀ i, (exponentSum p X r).toAdd i ≠ 0 →
          (ω i : freeProP p X) ∈ (commutator (freeProP p X)).topologicalClosure) ∧
        basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)
          (fun i ↦ gradedMk p (freeProP p X) m (ω i)) = gradedMk p (freeProP p X) (m + 1) z) :
    ∃ φ : freeProP p X →ₜ* freeProP p X,
      (∀ g, g⁻¹ * φ g ∈ pLowerCentralSeries p (freeProP p X) 1) ∧
        exponentSum p X (φ r) = exponentSum p X r ∧
        (φ r)⁻¹ * w ∈ pLowerCentralSeries p (freeProP p X) (k + 2) := by
  induction k with
  | zero =>
    refine ⟨ContinuousMonoidHom.id _, fun g ↦ ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using QuotientGroup.eq.mp (gradedMk_eq_gradedMk_iff.mp h)
  | succ k ih =>
    obtain ⟨φ, hφ, hφe, hr⟩ := ih fun m hm hmk ↦ hspan m hm (hmk.trans k.le_succ)
    -- `φ r` is again a relator with class `ρ`: `φ` is congruent to the identity modulo `λ_2` on
    -- `λ_1`.
    have hφr : φ r ∈ pLowerCentralSeries p (freeProP p X) 1 :=
      φ.toMonoidHom.map_pLowerCentralSeries_le φ.continuous 1 ⟨r, r.2, rfl⟩
    have hρ : gradedMk p (freeProP p X) 1 ⟨φ r, hφr⟩ = gradedMk p (freeProP p X) 1 r := by
      rw [gradedMk_eq_gradedMk_iff]
      exact (QuotientGroup.eq.mpr
        (inv_mul_apply_mem_pLowerCentralSeries φ.toMonoidHom φ.continuous hφ r.2)).symm
    -- The deviation `(φ r)⁻¹ * w` lies in the closed commutator subgroup, because `φ r` and `w`
    -- have the same exponent vector; the hypothesis absorbs it by a correction preserving that
    -- vector.
    have hz : (φ r)⁻¹ * w ∈ (commutator (freeProP p X)).topologicalClosure := by
      rw [← exponentSum_eq_one_iff, map_mul, map_inv, hφe, hrw, inv_mul_cancel]
    obtain ⟨ω, hωK, hω⟩ := hspan (k + 1) (by omega) le_rfl ⟨(φ r)⁻¹ * w, hr⟩ hz
    refine ⟨(basisModification ω).comp φ, fun g ↦ ?_, ?_, ?_⟩
    · rw [ContinuousMonoidHom.coe_comp, Function.comp_apply]
      exact inv_mul_apply_apply_mem (fun g ↦ pLowerCentralSeries_antitone (by omega)
        (inv_mul_basisModification_mem_pLowerCentralSeries ω g)) hφ g
    · rw [ContinuousMonoidHom.coe_comp, Function.comp_apply,
        exponentSum_basisModification ω fun i hi ↦ hωK i (hφe ▸ hi), hφe]
    · rw [ContinuousMonoidHom.coe_comp, Function.comp_apply]
      refine inv_basisModification_mul_mem_pLowerCentralSeries le_add_self ⟨φ r, hφr⟩ w hr ω ?_
      rw [hρ]
      exact hω

/-! ### The limit -/

/-- **The successive-approximation theorem.** Let `r, w ∈ λ_1(F)` be relators of the free pro-`p`
group `F` on a finite linearly ordered type with the same class `ρ ∈ gr_1(F)`, and suppose the
basis-modification map `δ_ρ` is onto `gr_{m+1}(F)` for every `m ≥ 1`. Then a continuous
automorphism of `F` carries `r` to `w`. -/
theorem exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w)
    (hspan : ∀ m (hm : 1 ≤ m),
      LinearMap.range (basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)) = ⊤) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X, e r = w := by
  refine (isProP_freeProP p X).exists_continuousMulEquiv_apply_eq_of_forall_exists_surjective
    (isTopologicallyFinitelyGenerated_freeProP p X) Fact.out (r : freeProP p X) w fun k ↦ ?_
  obtain ⟨φ, hφ, hr⟩ :=
    exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries r w h k fun m hm _ ↦ hspan m hm
  exact ⟨φ, (isProP_freeProP p X).surjective_of_forall_inv_mul_mem_pLowerCentralSeries_one
    (φ := φ.toMonoidHom) φ.continuous hφ, pLowerCentralSeries_antitone (by omega) hr⟩

/-- **The relative successive-approximation theorem.** Let `r, w ∈ λ_1(F)` be relators of the
free pro-`p` group `F` on a finite linearly ordered type with the same class `ρ ∈ gr_1(F)` and the
same exponent vector `v = exponentSum r`, and suppose that for every `m ≥ 1` each element of
`λ_{m+1}(F)` lying in the closed commutator subgroup `K` has class `δ_ρ(⟦ω⟧)` for a family
`ω : X → λ_m(F)` with `ω_i ∈ K` at every generator `i` with `v_i ≠ 0`. Then a continuous
automorphism of `F` carries `r` to `w`.

This is the form of the argument for a relator whose `p`-power part lies in `λ_2(F)`: there `Im δ_ρ`
misses the classes `π^{m+1} ξ_i`, so `δ_ρ` is not onto. The hypothesis on the corrections is the
constrained form of the span statement `Im δ_ρ ⊇ ` (classes of `λ_{m+1}(F) ∩ K`); it guarantees
absorption for the deviations lying in `K`, and the exponent-vector hypotheses keep the deviations
there along the approximation. It is assumed here, not established. -/
theorem exists_continuousMulEquiv_apply_eq_of_exponentSum_eq
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w)
    (hrw : exponentSum p X r = exponentSum p X w)
    (hspan : ∀ m (hm : 1 ≤ m), ∀ z : pLowerCentralSeries p (freeProP p X) (m + 1),
      (z : freeProP p X) ∈ (commutator (freeProP p X)).topologicalClosure →
      ∃ ω : X → pLowerCentralSeries p (freeProP p X) m,
        (∀ i, (exponentSum p X r).toAdd i ≠ 0 →
          (ω i : freeProP p X) ∈ (commutator (freeProP p X)).topologicalClosure) ∧
        basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)
          (fun i ↦ gradedMk p (freeProP p X) m (ω i)) = gradedMk p (freeProP p X) (m + 1) z) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X, e r = w := by
  refine (isProP_freeProP p X).exists_continuousMulEquiv_apply_eq_of_forall_exists_surjective
    (isTopologicallyFinitelyGenerated_freeProP p X) Fact.out (r : freeProP p X) w fun k ↦ ?_
  obtain ⟨φ, hφ, -, hr⟩ :=
    exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries_of_exponentSum_eq r w h hrw k
      fun m hm _ ↦ hspan m hm
  exact ⟨φ, (isProP_freeProP p X).surjective_of_forall_inv_mul_mem_pLowerCentralSeries_one
    (φ := φ.toMonoidHom) φ.continuous hφ, pLowerCentralSeries_antitone (by omega) hr⟩

end TauCeti.freeProP
