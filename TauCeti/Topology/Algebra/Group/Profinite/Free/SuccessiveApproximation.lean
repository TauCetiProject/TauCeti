/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Comparison
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside

/-!
# Successive approximation of a relator by basis modifications

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with lower
`p`-series `λ_k = λ_k(F)`, and let `r, w ∈ λ_1(F)` be two relators with the same class
`ρ ∈ gr_1(F)`, that is `r ≡ w mod λ_2(F)`. The basis modification `θ_w : x_i ↦ x_i * w_i` by a
family `w : X → λ_m(F)` moves `r` inside its coset modulo `λ_{m+1}(F)` by the class
`δ_ρ(ω) ∈ gr_{m+1}(F)` of `TauCeti.freeProP.basisModificationDelta`, and it leaves the class `ρ`
unchanged. So when `δ_ρ` is onto `gr_{m+1}(F)` for every `m ≥ 1`, a congruence `r ≡ w mod λ_{m+1}`
improves to a congruence modulo `λ_{m+2}` by one basis modification at level `m`, and finitely
many modifications carry `r` to `w` modulo any term of the series
(`TauCeti.freeProP.exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries`).

The limit is taken through the levelwise comparison schema
`TauCeti.PLowerCentralSeriesComparison`: the level-`k` comparison data are the surjective
endomorphisms of the finite group `F ⧸ λ_k` carrying the class of `r` to the class of `w`, the
finite approximations show that each level is nonempty, and descent along the series
(`ContinuousMonoidHom.pLowerCentralSeriesDesc`) bonds the levels. The schema produces a continuous
automorphism `e` of `F` with `e r = w`, which is
`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top`.

This is the successive-approximation argument of Labute's classification of Demushkin groups: the
span statements of `TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification` supply the
hypothesis on `δ_ρ`, and the conclusion brings a relator congruent to a normal-form word modulo
`λ_2(F)` to that word exactly.

## Main results

* `TauCeti.freeProP.exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries`: the finite
  approximations, one basis modification per level.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top`
  is **the successive-approximation theorem**: a continuous automorphism of `F` carries `r` to `w`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5 and the proof of Theorem 3.
-/

public section

namespace TauCeti.freeProP

open Subgroup

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Finite X] [LinearOrder X]

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
    · have h2 : (φ g)⁻¹ * basisModification ω (φ g) ∈ pLowerCentralSeries p (freeProP p X) 1 :=
        pLowerCentralSeries_antitone (by omega)
          (inv_mul_basisModification_mem_pLowerCentralSeries ω (φ g))
      have := mul_mem (hφ g) h2
      rwa [mul_assoc, mul_inv_cancel_left] at this
    · have key := gradedMk_inv_mul_basisModification (le_add_self : 1 ≤ k + 1) ω ⟨φ r, hφr⟩
      have hωv : (fun i ↦ gradedMk p (freeProP p X) (k + 1) (ω i)) = v := funext hω
      rw [hρ, hωv, hv] at key
      have h3 : ((φ r)⁻¹ * basisModification ω (φ r))⁻¹ * ((φ r)⁻¹ * w) ∈
          pLowerCentralSeries p (freeProP p X) (k + 1 + 1 + 1) :=
        QuotientGroup.eq.mp (gradedMk_eq_gradedMk_iff.mp key)
      rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at h3

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
  have hp : p.Prime := Fact.out
  have hfg := isTopologicallyFinitelyGenerated_freeProP p X
  have hP := isProP_freeProP p X
  have : ∀ k, DiscreteTopology (freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k) :=
    fun k ↦ QuotientGroup.discreteTopology (hfg.isOpen_pLowerCentralSeries hp k)
  -- The level-`k` comparison data: surjective endomorphisms of `F ⧸ λ_k` carrying `r` to `w`.
  let S (k : ℕ) : Type u :=
    {ψ : freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k →ₜ*
        freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) k //
      Function.Surjective ψ ∧ ψ (r : freeProP p X) = (w : freeProP p X)}
  have : ∀ k, Finite (S k) := fun k ↦ by
    have := hfg.finite_quotient_pLowerCentralSeries hp k
    exact Finite.of_injective (fun s : S k ↦ ⇑s.1)
      (DFunLike.coe_injective.comp Subtype.val_injective)
  -- Each level is nonempty, by the finite approximations: a basis modification congruent to the
  -- identity modulo `Φ(F)` is surjective, so it induces a surjection of `F ⧸ λ_k`.
  have : ∀ k, Nonempty (S k) := fun k ↦ by
    obtain ⟨φ, hφ, hr⟩ :=
      exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries r w h k
        fun m hm _ ↦ hspan m hm
    rw [pLowerCentralSeries_one_eq_proPFrattini hp] at hφ
    have hsurj : Function.Surjective φ :=
      hP.surjective_of_forall_inv_mul_mem_proPFrattini (φ := φ.toMonoidHom) φ.continuous hφ
    have hle : pLowerCentralSeries p (freeProP p X) k ≤
        (pLowerCentralSeries p (freeProP p X) k).comap φ.toMonoidHom :=
      Subgroup.map_le_iff_le_comap.mp (φ.toMonoidHom.map_pLowerCentralSeries_le φ.continuous k)
    refine ⟨⟨⟨QuotientGroup.map _ _ φ.toMonoidHom hle, continuous_of_discreteTopology⟩,
      QuotientGroup.map_surjective_of_surjective _ _ _ (QuotientGroup.mk_surjective.comp hsurj) hle,
      ?_⟩⟩
    rw [ContinuousMonoidHom.coe_mk, QuotientGroup.map_mk]
    exact QuotientGroup.eq.mpr (pLowerCentralSeries_antitone (by omega : k ≤ k + 2) hr)
  let C : PLowerCentralSeriesComparison p (freeProP p X) (freeProP p X) S :=
    { map := fun _ s ↦ s.1
      map_surjective := fun _ s ↦ s.2.1
      bond := fun _ s ↦ ⟨s.1.pLowerCentralSeriesDesc, s.1.pLowerCentralSeriesDesc_surjective s.2.1,
        by rw [ContinuousMonoidHom.pLowerCentralSeriesDesc_mk, s.2.2, QuotientGroup.mapOfLE_mk]⟩
      commutes := fun _ s x ↦ (s.1.pLowerCentralSeriesDesc_mapOfLE x).symm }
  obtain ⟨_, e, -, -, he, -⟩ := C.exists_continuousMulEquiv_preserving hP hfg hp
    (fun _ : Unit ↦ (r : freeProP p X)) (fun _ ↦ (w : freeProP p X))
    (1 : freeProP p X →ₜ* freeProP p X) 1 (fun _ s _ ↦ s.2.2)
    (fun _ ↦ ⟨0, fun _ _ _ _ ↦ by simp⟩)
  exact ⟨e, he ()⟩

end TauCeti.freeProP
