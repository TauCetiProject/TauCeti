/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.NoetherianType.HuberStandard
import TauCeti.RingTheory.Huber.NoetherianType.Quotient
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.Huber.Padic.TateAlgebra
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Examples: Huber's standing class and its separation from noetherian type

All three alternatives of `TauCeti.Huber.IsHuberStandard` (Huber 1996, (1.1.1)) are exercised,
together with quotient stability and the strict separation from `TauCeti.Huber.IsNoetherianType`:

* The Tate algebra `ℚ_p⟨T₁, …, Tₙ⟩` and its quotients belong to Huber's standing class via the
  strongly noetherian Tate alternative.
* The ring of `p`-adic integers `ℤ_[p]` and its quotients belong to Huber's standing class via the
  finite-type-over-a-noetherian-ring-of-definition alternative, although `ℤ_[p]` is neither Tate nor
  discrete.
* The polynomial ring `ℤ[X₀, X₁, …]` with the discrete topology is not noetherian, yet belongs to
  Huber's standing class via the discrete alternative.
* The product `ℤ_[p] × ℤ[X₀, X₁, …]` of `p`-adic `ℤ_[p]` with discrete `ℤ[X₀, X₁, …]` is a
  complete Hausdorff Huber ring of noetherian type — with `ℤ_[p] × ℤ` as an open noetherian ring of
  definition and `((p, 0))` as an ideal of definition — that does **not** belong to Huber's
  standing class. Since both factors belong to `IsHuberStandard`, this also shows that Huber's
  standing class is not closed under binary products of topological rings.

## References

* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, (1.1.1).
-/

open IsLocalRing MvPolynomial Topology TauCeti.Huber

section Examples

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Every quotient of `ℚ_p⟨T₁, …, Tₙ⟩` is in Huber's standing class. -/
example (J : Ideal (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ))) :
    IsHuberStandard
      ((MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ)) ⧸ J) :=
  inferInstance

/-- `ℤ_[p]` is in Huber's standing class via `(ℤ_[p], (p))`, and so is every quotient `ℤ_[p] ⧸ J`,
although `ℤ_[p]` is not a Tate ring. -/
example (J : Ideal ℤ_[p]) : ¬ IsTateRing ℤ_[p] ∧ IsHuberStandard (ℤ_[p] ⧸ J) := by
  have : IsHuberStandard ℤ_[p] := .of_isAdic PadicInt.isAdic_maximalIdeal
  exact ⟨PadicInt.not_isTateRing, inferInstance⟩

end Examples

/-- Discrete `ℤ[X₀, X₁, …]` is in Huber's standing class even though it is not noetherian. -/
example :
    letI : TopologicalSpace (MvPolynomial ℕ ℤ) := ⊥
    letI : DiscreteTopology (MvPolynomial ℕ ℤ) := ⟨rfl⟩
    letI : IsTopologicalRing (MvPolynomial ℕ ℤ) := inferInstance
    ¬ IsNoetherianRing (MvPolynomial ℕ ℤ) ∧ IsHuberStandard (MvPolynomial ℕ ℤ) := by
  let _ : TopologicalSpace (MvPolynomial ℕ ℤ) := ⊥
  have _ : DiscreteTopology (MvPolynomial ℕ ℤ) := ⟨rfl⟩
  exact ⟨MvPolynomial.not_isNoetherianRing ℕ ℤ, inferInstance⟩

/-- **Complete Hausdorff separation of `IsNoetherianType` and `IsHuberStandard`**: the product
`ℤ_[p] × ℤ[X₀, X₁, …]` (with discrete second factor) is a complete Hausdorff Huber ring of
noetherian type that is not in Huber's standing class, while both factors are in `IsHuberStandard`.
-/
example (p : ℕ) [Fact p.Prime] :
    letI : UniformSpace (MvPolynomial ℕ ℤ) := ⊥
    letI : DiscreteTopology (MvPolynomial ℕ ℤ) := DiscreteUniformity.instDiscreteTopology (X := _)
    letI : IsTopologicalRing (MvPolynomial ℕ ℤ) := inferInstance
    ∃ (_ : IsHuberRing (ℤ_[p] × MvPolynomial ℕ ℤ)),
      CompleteSpace (ℤ_[p] × MvPolynomial ℕ ℤ) ∧
      T2Space (ℤ_[p] × MvPolynomial ℕ ℤ) ∧
      IsHuberStandard ℤ_[p] ∧
      IsHuberStandard (MvPolynomial ℕ ℤ) ∧
      IsNoetherianType (ℤ_[p] × MvPolynomial ℕ ℤ) ∧
      ¬ IsHuberStandard (ℤ_[p] × MvPolynomial ℕ ℤ) := by
  let B := MvPolynomial ℕ ℤ
  let _ : UniformSpace B := ⊥
  have _ : DiscreteUniformity B := ⟨rfl⟩
  have _ : DiscreteTopology B := inferInstance
  let A₀ : Subring (ℤ_[p] × B) := (⊤ : Subring ℤ_[p]).prod (⊥ : Subring B)
  let π : A₀ := ⟨((p : ℤ_[p]), 0), ⟨trivial, (⊥ : Subring B).zero_mem⟩⟩
  have hpow (n : ℕ) :
      ((Ideal.span {π} ^ (n + 1) : Ideal A₀) : Set A₀) =
        Subtype.val ⁻¹'
          (((maximalIdeal ℤ_[p] ^ (n + 1) : Ideal ℤ_[p]) : Set ℤ_[p]) ×ˢ ({0} : Set B)) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, _root_.PadicInt.maximalIdeal_eq_span_p]
    have hπ : (π ^ (n + 1)).1 = ((p : ℤ_[p]) ^ (n + 1), (0 : B)) := by
      ext <;> simp [π, zero_pow (Nat.succ_ne_zero n)]
    refine ⟨fun ⟨c, hc⟩ ↦ ⟨⟨c.1.1, by simp [hc, Subring.coe_mul, hπ]⟩,
      by simp [hc, Subring.coe_mul, hπ]⟩, fun ⟨⟨q, hq⟩, hu2⟩ ↦ ?_⟩
    exact ⟨⟨(q, 0), ⟨trivial, (⊥ : Subring B).zero_mem⟩⟩, Subtype.ext <| Prod.ext
      (by simp [Subring.coe_mul, hπ, hq]) (by simp [Subring.coe_mul, hπ, hu2])⟩
  have hadic : IsAdic (Ideal.span {π}) := by
    rw [isAdic_iff]
    refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
    · rcases n with _ | n
      · simp
      · rw [hpow n]
        exact ((IsLocalRing.isOpen_maximalIdeal_pow ℤ_[p] _).prod
          (isOpen_discrete ({0} : Set B))).preimage continuous_subtype_val
    · rw [nhds_subtype_eq_comap, Filter.mem_comap] at hs
      obtain ⟨t, ht, hts⟩ := hs
      rw [nhds_prod_eq, Filter.mem_prod_iff] at ht
      obtain ⟨U, hU, V, hV, hUV⟩ := ht
      obtain ⟨m, hm⟩ := (isAdic_iff.mp (PadicInt.isAdic_maximalIdeal (p := p))).2 U hU
      refine ⟨m + 1, fun u hu ↦ hts (hUV ?_)⟩
      rw [hpow m] at hu
      exact ⟨hm (Ideal.pow_le_pow_right m.le_succ hu.1),
        Set.mem_singleton_iff.mp hu.2 ▸ mem_of_mem_nhds hV⟩
  have htop : IsNoetherianRing (⊤ : Subring ℤ_[p]) :=
    isNoetherianRing_of_ringEquiv ℤ_[p] Subring.topEquiv.symm
  have hbot : IsNoetherianRing (⊥ : Subring B) :=
    Subring.closure_empty (R := B) ▸ is_noetherian_subring_closure (∅ : Set B) Set.finite_empty
  have hA₀noeth : IsNoetherianRing A₀ :=
    isNoetherianRing_of_ringEquiv ((⊤ : Subring ℤ_[p]) × (⊥ : Subring B))
      (Subring.prodEquiv _ _).symm
  have hA₀open : IsOpen (A₀ : Set (ℤ_[p] × B)) :=
    Subring.coe_prod (⊤ : Subring ℤ_[p]) (⊥ : Subring B) ▸
      isOpen_univ.prod (isOpen_discrete _)
  let P : PairOfDefinition (ℤ_[p] × B) :=
    ⟨A₀, hA₀open, Ideal.span {π}, Submodule.fg_span_singleton _, hadic⟩
  have : IsHuberRing (ℤ_[p] × B) := ⟨⟨P⟩⟩
  refine ⟨inferInstance, inferInstance, inferInstance, .of_isAdic PadicInt.isAdic_maximalIdeal,
    inferInstance, .of_pairOfDefinition P hA₀noeth, fun hstd ↦ hstd.elim ?_ ?_ ?_⟩
  · intro Q _ _
    have := Algebra.FiniteType.isNoetherianRing Q.ringOfDefinition (ℤ_[p] × B)
    have hB : IsNoetherianRing B :=
      isNoetherianRing_of_surjective (ℤ_[p] × B) B (RingHom.snd ℤ_[p] B) Prod.snd_surjective
    exact MvPolynomial.not_isNoetherianRing ℕ ℤ hB
  · intro hTate _
    exact PadicInt.not_isTateRing
      (IsTateRing.of_continuous (A := ℤ_[p] × B) continuous_fst (φ := RingHom.fst ℤ_[p] B))
  · intro hDisc
    have h0 : IsOpen ({(0 : ℤ_[p])} : Set ℤ_[p]) := by
      have heq : (fun x : ℤ_[p] ↦ (x, (0 : B))) ⁻¹' ({(0 : ℤ_[p] × B)} : Set _) = {0} := by
        ext x; simp [Prod.ext_iff]
      exact heq ▸ (@isOpen_discrete _ _ hDisc _).preimage (Continuous.prodMk_left 0)
    have hnilp : IsTopologicallyNilpotent (p : ℤ_[p]) :=
      PadicInt.isTopologicallyNilpotent_iff_dvd.mpr dvd_rfl
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (hnilp (h0.mem_nhds rfl))
    exact pow_ne_zero n (NeZero.ne (p : ℤ_[p])) (hn n le_rfl)
