/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Powerful
import Mathlib.Topology.Separation.Connected
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Product
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# Uniform pro-`p` groups and constant lower `p`-series indices

This file defines uniform pro-`p` groups (`TauCeti.IsUniform`) and their dimension
(`TauCeti.uniformDimension`), proves the equivalence between torsion-freeness and constancy of the
successive lower `p`-series indices (Dixon–du Sautoy–Mann–Segal, Chapter 4), establishes the
basic closure properties of uniformity and dimension, and verifies concrete examples.

A topological group `U` is **uniform** (relative to `p`) when it is pro-`p`, topologically
finitely generated, torsion-free (`∀ g : U, IsOfFinOrder g → g = 1`), and powerful (with the
fourth-power commutator condition `⁅⊤, ⊤⁆ ≤ U ^ 4` at `p = 2`). Its **dimension** is defined as

  `uniformDimension p U = Nat.log p (closedPowerSubgroup U p).index`.

For a profinite pro-`p` group `U` and prime `p`, torsion-freeness is equivalent to having no
nontrivial element of order `p` (`TauCeti.IsProP.forall_isOfFinOrder_eq_one_iff`). For a
topologically finitely generated profinite pro-`p` group `U`, uniformity is equivalent to:

* `IsPowerful p U` together with bijectivity of every graded `p`-power map
  `gr_k(U) → gr_{k+1}(U)`
  (`TauCeti.IsProP.isUniform_iff_isPowerful_and_forall_gradedPow_bijective`), and equivalently to
* `IsPowerful p U` together with constancy of the successive lower `p`-series indices
  `[λ_k : λ_{k+1}] = [U : λ_1]`
  (`TauCeti.IsProP.isUniform_iff_isPowerful_and_relIndex_pLowerCentralSeries_eq`).

For a uniform profinite pro-`p` group `U`, `uniformDimension p U` equals the minimal number of
topological generators (`TauCeti.IsUniform.uniformDimension_eq_topologicalGeneratorRankNat`), is
uniquely determined by `[U : λ_1] = p ^ d`
(`TauCeti.IsUniform.index_pLowerCentralSeries_one_eq_pow_iff`), and governs every successive index
and term index along the lower `p`-series:

* `[λ_k : λ_{k+1}] = |gr_k(U)| = p ^ d`,
* `[U : λ_k] = [U : U ^ (p ^ k)] = p ^ (k * d)`.

Uniformity is invariant under topological group isomorphism, holds for every trivial group (of
dimension `0`), is preserved and reflected by binary and finite indexed products (with additive
`uniformDimension`), and passes to the canonical power subgroups `closedPowerSubgroup U (p ^ n)`
with the same dimension. Concrete verifications show that `Multiplicative ℤ_[p]` is uniform of
dimension `1`, `Multiplicative (X → ℤ_[p])` is uniform of dimension `Nat.card X`, and
`Multiplicative (ZMod p)` is powerful but not uniform, with lower `p`-series indices `p` at `k = 0`
and `1` at `k ≥ 1`.

## Main definitions

* `TauCeti.IsUniform`: uniformity of a topological group relative to `p` (pro-`p`, topologically
  finitely generated, torsion-free, and powerful).
* `TauCeti.uniformDimension`: `Nat.log p (closedPowerSubgroup G p).index`.

## Main results

* `TauCeti.IsProP.forall_isOfFinOrder_eq_one_iff`: a profinite pro-`p` group is torsion-free if and
  only if it has no nontrivial element of order `p`.
* `TauCeti.IsProP.isUniform_iff_isPowerful_and_forall_gradedPow_bijective`,
  `TauCeti.IsProP.isUniform_iff_isPowerful_and_relIndex_pLowerCentralSeries_eq`: DDMS Theorem 4.5,
  equivalence of torsion-freeness and constant lower `p`-series indices for t.f.g. powerful pro-`p`
  groups.
* `TauCeti.IsUniform.uniformDimension_eq_topologicalGeneratorRankNat`,
  `TauCeti.IsUniform.index_pLowerCentralSeries_one`,
  `TauCeti.IsUniform.index_pLowerCentralSeries_one_eq_pow_iff`,
  `TauCeti.IsUniform.relIndex_pLowerCentralSeries`, `TauCeti.IsUniform.natCard_gradedPiece`,
  `TauCeti.IsUniform.index_pLowerCentralSeries`: dimension identification and constant indices.
* `TauCeti.isUniform_congr`, `TauCeti.uniformDimension_congr`, `TauCeti.isUniform_of_subsingleton`,
  `TauCeti.uniformDimension_of_subsingleton`, `TauCeti.isUniform_prod_iff`,
  `TauCeti.uniformDimension_prod`, `TauCeti.isUniform_pi_iff`, `TauCeti.uniformDimension_pi`,
  `TauCeti.IsUniform.closedPowerSubgroup_pow`,
  `TauCeti.IsUniform.uniformDimension_closedPowerSubgroup_pow`: closure API.
* `TauCeti.isUniform_multiplicative_padicInt`, `TauCeti.uniformDimension_multiplicative_padicInt`,
  `TauCeti.isUniform_multiplicative_pi_padicInt`,
  `TauCeti.uniformDimension_multiplicative_pi_padicInt`, `TauCeti.isPowerful_multiplicative_zmod`,
  `TauCeti.not_isUniform_multiplicative_zmod`,
  `TauCeti.relIndex_pLowerCentralSeries_multiplicative_zmod_zero`,
  `TauCeti.relIndex_pLowerCentralSeries_multiplicative_zmod_succ`: concrete examples.

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, 2nd ed.,
  Cambridge University Press, 1999, Chapter 4, Theorem 4.5.
* K. Ardakov and K. A. Brown, *Ring-theoretic properties of Iwasawa algebras: a survey*,
  Documenta Math. Extra Vol. Coates (2006), Section 2.3.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

/-! ### Definitions and basic properties -/

section Defs

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group `G` is **uniform** relative to `p` if it is pro-`p`, topologically finitely
generated, torsion-free, and powerful (with the fourth-power commutator condition at `p = 2`). -/
def IsUniform : Prop :=
  IsProP p G ∧ IsTopologicallyFinitelyGenerated G ∧
    (∀ g : G, IsOfFinOrder g → g = 1) ∧ IsPowerful p G

/-- The **dimension** of a uniform pro-`p` group: `Nat.log p [G : G^p]`. -/
noncomputable def uniformDimension : ℕ :=
  Nat.log p (closedPowerSubgroup G p).index

/-- The unfolding characterization of `TauCeti.IsUniform`. -/
theorem isUniform_iff :
    IsUniform p G ↔
      IsProP p G ∧ IsTopologicallyFinitelyGenerated G ∧
        (∀ g : G, IsOfFinOrder g → g = 1) ∧ IsPowerful p G :=
  Iff.rfl

/-- The defining equation of `TauCeti.uniformDimension`. -/
theorem uniformDimension_def :
    uniformDimension p G = Nat.log p (closedPowerSubgroup G p).index := by
  rw [uniformDimension]

variable {p G}

namespace IsUniform

/-- A uniform group is pro-`p`. -/
theorem isProP (hG : IsUniform p G) : IsProP p G := hG.1

/-- A uniform group is topologically finitely generated. -/
theorem isTopologicallyFinitelyGenerated (hG : IsUniform p G) :
    IsTopologicallyFinitelyGenerated G := hG.2.1

/-- Every element of finite order in a uniform group is trivial. -/
theorem eq_one_of_isOfFinOrder (hG : IsUniform p G) {g : G} (hg : IsOfFinOrder g) : g = 1 :=
  hG.2.2.1 g hg

/-- A uniform group is multiplicatively torsion-free. -/
theorem isMulTorsionFree (hG : IsUniform p G) : IsMulTorsionFree G :=
  isMulTorsionFree_iff_not_isOfFinOrder.mpr fun _ hne hfin ↦ hne (hG.eq_one_of_isOfFinOrder hfin)

/-- A uniform group is powerful. -/
theorem isPowerful (hG : IsUniform p G) : IsPowerful p G := hG.2.2.2

/-- For positive `p`, a uniform group has no nontrivial element of order dividing `p`. -/
theorem eq_one_of_pow_prime_eq_one (hG : IsUniform p G) (hp : 0 < p) {g : G} (hg : g ^ p = 1) :
    g = 1 :=
  hG.eq_one_of_isOfFinOrder (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp, hg⟩)

/-- Uniformity transfers along a topological group isomorphism. -/
theorem of_equiv {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hG : IsUniform p G) (e : G ≃ₜ* H) : IsUniform p H := by
  refine ⟨hG.isProP.of_equiv e, (isTopologicallyFinitelyGenerated_congr e).mp
    hG.isTopologicallyFinitelyGenerated, fun h hh ↦ ?_, hG.isPowerful.of_equiv e⟩
  have hfin : IsOfFinOrder (e.symm h) := e.symm.toMulEquiv.toMonoidHom.isOfFinOrder hh
  simpa using congrArg e (hG.eq_one_of_isOfFinOrder hfin)

end IsUniform

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Uniformity is invariant under topological group isomorphism. -/
theorem isUniform_congr (e : G ≃ₜ* H) : IsUniform p G ↔ IsUniform p H :=
  ⟨fun h ↦ h.of_equiv e, fun h ↦ h.of_equiv e.symm⟩

/-- Topological group isomorphisms preserve `TauCeti.uniformDimension`. -/
theorem uniformDimension_congr (e : G ≃ₜ* H) : uniformDimension p G = uniformDimension p H := by
  rw [uniformDimension_def, uniformDimension_def, closedPowerSubgroup_index_congr e p]

variable (p G)

/-- Every trivial topological group is uniform. -/
theorem isUniform_of_subsingleton [Subsingleton G] : IsUniform p G := by
  have hpg : IsPGroup p G := fun g ↦ ⟨0, Subsingleton.elim _ _⟩
  refine ⟨hpg.isProP, isTopologicallyFinitelyGenerated_of_fg, fun g _ ↦ Subsingleton.elim g 1, ?_⟩
  rw [isPowerful_iff, Subgroup.commutator_le]
  intro a _ b _
  rw [Subsingleton.elim ⁅a, b⁆ 1]
  exact one_mem _

/-- The dimension of a trivial topological group is `0`. -/
@[simp]
theorem uniformDimension_of_subsingleton [Subsingleton G] : uniformDimension p G = 0 := by
  have : Subsingleton (G ⧸ closedPowerSubgroup G p) :=
    ⟨fun x y ↦ QuotientGroup.induction_on x fun a ↦ QuotientGroup.induction_on y fun b ↦
      congrArg _ (Subsingleton.elim a b)⟩
  rw [uniformDimension_def, Subgroup.index_eq_card, Nat.card_unique, Nat.log_one_right]

/-- The cardinality of the `k`-th graded piece `gr_k(G)` is the relative index `[λ_k : λ_{k+1}]`.
-/
theorem natCard_gradedPiece_eq_relIndex (k : ℕ) :
    Nat.card (gradedPiece p G k) =
      (pLowerCentralSeries p G (k + 1)).relIndex (pLowerCentralSeries p G k) :=
  (Nat.card_congr Additive.toMul).trans (Subgroup.index_eq_card _).symm

end Defs

/-! ### Torsion in profinite pro-`p` groups -/

section Torsion

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Every finite-order element of a profinite pro-`p` group has `p`-power order. -/
theorem IsProP.exists_pow_pow_eq_one_of_isOfFinOrder (hG : IsProP p G) {g : G}
    (hg : IsOfFinOrder g) : ∃ n : ℕ, g ^ p ^ n = 1 := by
  set H := Subgroup.zpowers g
  have : Finite H := hg.finite_zpowers
  have : DiscreteTopology H := Finite.instDiscreteTopology
  have hH : IsPGroup p H := isProP_iff_isPGroup.mp (hG.subgroup H)
  obtain ⟨n, hn⟩ := hH ⟨g, Subgroup.mem_zpowers g⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

/-- A profinite pro-`p` group is torsion-free if and only if it has no nontrivial element of order
`p`. -/
theorem IsProP.forall_isOfFinOrder_eq_one_iff [hp : Fact p.Prime] (hG : IsProP p G) :
    (∀ g : G, IsOfFinOrder g → g = 1) ↔ (∀ g : G, g ^ p = 1 → g = 1) := by
  refine ⟨fun h g hg ↦ h g (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.out.pos, hg⟩), fun h g hg ↦ ?_⟩
  obtain ⟨n, hn⟩ := hG.exists_pow_pow_eq_one_of_isOfFinOrder hg
  induction n with
  | zero => simpa using hn
  | succ n ih =>
    rw [pow_succ, pow_mul] at hn
    exact ih (h _ hn)

end Torsion

/-! ### Constant lower `p`-series indices (DDMS Chapter 4) -/

section ConstantIndex

variable {p : ℕ} [hp : Fact p.Prime] {U : Type*} [Group U] [TopologicalSpace U]
  [IsTopologicalGroup U] [CompactSpace U] [TotallyDisconnectedSpace U]

/-- If every graded `p`-power map `gr_k(U) → gr_{k+1}(U)` is injective in a profinite pro-`p` group
`U`, then `U` has no nontrivial element of order `p`. -/
theorem IsProP.eq_one_of_pow_prime_eq_one_of_gradedPow_injective (hU : IsProP p U)
    (hinj : ∀ k, Function.Injective (gradedPow p U k)) {g : U} (hg : g ^ p = 1) : g = 1 := by
  suffices hall : ∀ k, g ∈ pLowerCentralSeries p U k by
    have hbot : g ∈ (⊥ : Subgroup U) := by
      rw [← hU.iInf_pLowerCentralSeries_eq_bot hp.out]
      exact Subgroup.mem_iInf.mpr hall
    exact Subgroup.mem_bot.mp hbot
  intro k
  induction k with
  | zero => exact mem_pLowerCentralSeries_zero p g
  | succ k ih =>
    have hzero : gradedPow p U k (gradedMk p U k ⟨g, ih⟩) = gradedPow p U k (gradedMk p U k 1) := by
      rw [gradedPow_gradedMk, gradedPow_gradedMk]
      congr 1
      exact Subtype.ext (by simpa using hg)
    have hmk : gradedMk p U k ⟨g, ih⟩ = 0 := by
      rw [← gradedMk_one (p := p) (G := U) k]
      exact hinj k hzero
    exact gradedMk_eq_zero_iff.mp hmk

/-- Single refinement step for DDMS Theorem 4.5: given `a` with `a ^ p ∈ λ_{k + j + 2}`, there is
`y ∈ λ_{k + j + 1}` such that `(a * y) ^ p ∈ λ_{k + (j + 1) + 2}`. -/
private theorem exists_mul_pow_mem_succ (hpow : IsPowerful p U) (hU : IsProP p U)
    (hfg : IsTopologicallyFinitelyGenerated U) (k j : ℕ) {a : U}
    (ha : a ^ p ∈ pLowerCentralSeries p U (k + j + 2)) :
    ∃ y ∈ pLowerCentralSeries p U (k + j + 1),
      (a * y) ^ p ∈ pLowerCentralSeries p U (k + (j + 1) + 2) := by
  obtain ⟨w, hw⟩ := hpow.gradedPow_surjective hU hfg (k + j + 1)
    (gradedMk p U (k + j + 2) ⟨(a ^ p)⁻¹, inv_mem ha⟩)
  obtain ⟨y, rfl⟩ := gradedMk_surjective (k + j + 1) w
  rw [gradedPow_gradedMk, gradedMk_eq_gradedMk_iff] at hw
  refine ⟨y, y.2, ?_⟩
  have hidx : k + (j + 1) + 2 = (k + j + 1) + 2 := by omega
  rw [hidx, ← QuotientGroup.eq_one_iff]
  have hmul := hpow.mk_mul_pow_prime_eq hU hfg (k + j + 1) (a := a) y.2
  rw [hmul, QuotientGroup.mk_mul, hw, QuotientGroup.mk_inv, mul_inv_cancel]

/-- Core kernel lemma for DDMS Theorem 4.5: in a topologically finitely generated powerful pro-`p`
group with no element of order `p`, if `x ^ p ∈ λ_{k+2}` then `x ∈ λ_{k+1}`. -/
private theorem mem_pLowerCentralSeries_succ_of_pow_mem (hpow : IsPowerful p U) (hU : IsProP p U)
    (hfg : IsTopologicallyFinitelyGenerated U) (htors : ∀ g : U, g ^ p = 1 → g = 1) (k : ℕ)
    {x : U} (hx : x ^ p ∈ pLowerCentralSeries p U (k + 2)) :
    x ∈ pLowerCentralSeries p U (k + 1) := by
  -- Iteratively refine `x` by elements of `λ_{k + j + 1}` so that `(seq j)^p ∈ λ_{k + j + 2}`.
  let step : ∀ (j : ℕ), {a : U // a ^ p ∈ pLowerCentralSeries p U (k + j + 2)} →
      {b : U // b ^ p ∈ pLowerCentralSeries p U (k + (j + 1) + 2)} := fun j a ↦
    let h := exists_mul_pow_mem_succ hpow hU hfg k j a.2
    ⟨a.1 * h.choose, h.choose_spec.2⟩
  let seq : ∀ j : ℕ, {a : U // a ^ p ∈ pLowerCentralSeries p U (k + j + 2)} :=
    Nat.rec ⟨x, hx⟩ step
  have hstep : ∀ j, (seq j).1⁻¹ * (seq (j + 1)).1 ∈ pLowerCentralSeries p U (k + j + 1) := by
    intro j
    change (seq j).1⁻¹ * ((seq j).1 * (exists_mul_pow_mem_succ hpow hU hfg k j (seq j).2).choose) ∈
      _
    rw [inv_mul_cancel_left]
    exact (exists_mul_pow_mem_succ hpow hU hfg k j (seq j).2).choose_spec.1
  have hcompat : ∀ (n : ℕ) (g : U),
      (g : U ⧸ pLowerCentralSeries p U (n + 1)) = ((seq (n + 1)).1 : U ⧸ _) →
      (g : U ⧸ pLowerCentralSeries p U n) = ((seq n).1 : U ⧸ _) := by
    intro n g hg
    have hg' : (g : U ⧸ pLowerCentralSeries p U n) = ((seq (n + 1)).1 : U ⧸ _) :=
      QuotientGroup.eq.mpr (pLowerCentralSeries_antitone (Nat.le_succ n) (QuotientGroup.eq.mp hg))
    have hs : ((seq n).1 : U ⧸ pLowerCentralSeries p U n) = ((seq (n + 1)).1 : U ⧸ _) :=
      QuotientGroup.eq.mpr (pLowerCentralSeries_antitone (by omega) (hstep n))
    exact hg'.trans hs.symm
  obtain ⟨z, hz, -⟩ :=
    hU.existsUnique_forall_mk_eq_pLowerCentralSeries hp.out (fun n ↦ (seq n).1) hcompat
  have hzp : z ^ p = 1 := by
    suffices hall : ∀ n, z ^ p ∈ pLowerCentralSeries p U n by
      exact Subgroup.mem_bot.mp (hU.iInf_pLowerCentralSeries_eq_bot hp.out ▸
        Subgroup.mem_iInf.mpr hall)
    intro n
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hz n, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff]
    exact pLowerCentralSeries_antitone (by omega) (seq n).2
  have hz1 : z = 1 := htors z hzp
  have hseq_eq : ∀ j, ((seq j).1 : U ⧸ pLowerCentralSeries p U (k + 1)) = (x : U ⧸ _) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hs : ((seq j).1 : U ⧸ pLowerCentralSeries p U (k + 1)) = ((seq (j + 1)).1 : U ⧸ _) :=
        QuotientGroup.eq.mpr (pLowerCentralSeries_antitone (by omega) (hstep j))
      exact hs.symm.trans ih
  rw [← QuotientGroup.eq_one_iff, ← hseq_eq (k + 1), ← hz (k + 1), hz1, QuotientGroup.mk_one]

/-- **Injectivity of `gradedPow` in a torsion-free powerful pro-`p` group.** In a topologically
finitely generated powerful profinite pro-`p` group with no element of order `p`, every graded
`p`-power map `gr_k(U) → gr_{k+1}(U)` is injective. -/
theorem IsPowerful.gradedPow_injective_of_forall_pow_prime_eq_one (hpow : IsPowerful p U)
    (hU : IsProP p U) (hfg : IsTopologicallyFinitelyGenerated U)
    (htors : ∀ g : U, g ^ p = 1 → g = 1) (k : ℕ) :
    Function.Injective (gradedPow p U k) := by
  have hfun : gradedPow p U k = hpow.gradedPowAddMonoidHom k :=
    funext fun x ↦ (hpow.gradedPowAddMonoidHom_apply k x).symm
  rw [hfun, injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := gradedMk_surjective k a
  rw [IsPowerful.gradedPowAddMonoidHom_apply, gradedPow_gradedMk, gradedMk_eq_zero_iff] at ha
  exact gradedMk_eq_zero_iff.mpr (mem_pLowerCentralSeries_succ_of_pow_mem hpow hU hfg htors k ha)

/-- **DDMS Theorem 4.5 (graded form).** A topologically finitely generated profinite pro-`p` group
is uniform if and only if it is powerful and every graded `p`-power map `gr_k(U) → gr_{k+1}(U)` is
bijective. -/
theorem IsProP.isUniform_iff_isPowerful_and_forall_gradedPow_bijective (hU : IsProP p U)
    (hfg : IsTopologicallyFinitelyGenerated U) :
    IsUniform p U ↔ IsPowerful p U ∧ ∀ k, Function.Bijective (gradedPow p U k) := by
  constructor
  · intro hunif
    refine ⟨hunif.isPowerful, fun k ↦ ⟨?_, hunif.isPowerful.gradedPow_surjective hU hfg k⟩⟩
    exact hunif.isPowerful.gradedPow_injective_of_forall_pow_prime_eq_one hU hfg
      (fun _ hg ↦ hunif.eq_one_of_pow_prime_eq_one hp.out.pos hg) k
  · rintro ⟨hpow, hbij⟩
    refine ⟨hU, hfg, ?_, hpow⟩
    exact hU.forall_isOfFinOrder_eq_one_iff.mpr fun _ hg ↦
      hU.eq_one_of_pow_prime_eq_one_of_gradedPow_injective (fun k ↦ (hbij k).1) hg

/-- **DDMS Theorem 4.5 (constant-index form).** A topologically finitely generated profinite pro-`p`
group is uniform if and only if it is powerful and every successive lower `p`-series index
`[λ_k : λ_{k+1}]` equals `[U : λ_1]`. -/
theorem IsProP.isUniform_iff_isPowerful_and_relIndex_pLowerCentralSeries_eq (hU : IsProP p U)
    (hfg : IsTopologicallyFinitelyGenerated U) :
    IsUniform p U ↔
      IsPowerful p U ∧
        ∀ k, (pLowerCentralSeries p U (k + 1)).relIndex (pLowerCentralSeries p U k) =
          (pLowerCentralSeries p U 1).index := by
  rw [hU.isUniform_iff_isPowerful_and_forall_gradedPow_bijective hfg]
  refine and_congr_right fun hpow ↦ ⟨fun hbij k ↦ ?_, fun hconst k ↦ ?_⟩
  · rw [← natCard_gradedPiece_eq_relIndex]
    induction k with
    | zero =>
      rw [natCard_gradedPiece_eq_relIndex, pLowerCentralSeries_zero, Subgroup.relIndex_top_right]
    | succ k ih =>
      rw [← Nat.card_congr (Equiv.ofBijective _ (hbij k)), ih]
  · have : Finite (gradedPiece p U k) := hfg.finite_gradedPiece hp.out k
    exact (Nat.bijective_iff_surjective_and_card (gradedPow p U k)).mpr
      ⟨hpow.gradedPow_surjective hU hfg k, by
        rw [natCard_gradedPiece_eq_relIndex, natCard_gradedPiece_eq_relIndex, hconst k,
          hconst (k + 1)]⟩

namespace IsUniform

/-- In a uniform profinite pro-`p` group, every graded `p`-power map `gr_k(U) → gr_{k+1}(U)` is
bijective. -/
theorem gradedPow_bijective (hU : IsUniform p U) (k : ℕ) :
    Function.Bijective (gradedPow p U k) :=
  ((hU.isProP.isUniform_iff_isPowerful_and_forall_gradedPow_bijective
    hU.isTopologicallyFinitelyGenerated).mp hU).2 k

/-- In a uniform profinite pro-`p` group, `λ_k(U) = closedPowerSubgroup U (p ^ k)`. -/
theorem pLowerCentralSeries_eq_closedPowerSubgroup (hU : IsUniform p U) (k : ℕ) :
    pLowerCentralSeries p U k = closedPowerSubgroup U (p ^ k) :=
  hU.isPowerful.pLowerCentralSeries_eq_closedPowerSubgroup hU.isProP
    hU.isTopologicallyFinitelyGenerated k

/-- In a uniform profinite pro-`p` group, `uniformDimension p U` equals the minimal number of
topological generators. -/
theorem uniformDimension_eq_topologicalGeneratorRankNat (hU : IsUniform p U) :
    uniformDimension p U = topologicalGeneratorRankNat U hU.isTopologicallyFinitelyGenerated := by
  rw [uniformDimension_def, hU.isPowerful.index_closedPowerSubgroup_prime_eq_pow_rank hU.isProP
    hU.isTopologicallyFinitelyGenerated, Nat.log_pow hp.out.one_lt]

/-- In a uniform profinite pro-`p` group, `[U : U^p] = p ^ uniformDimension p U`. -/
theorem index_closedPowerSubgroup_prime (hU : IsUniform p U) :
    (closedPowerSubgroup U p).index = p ^ uniformDimension p U := by
  rw [hU.uniformDimension_eq_topologicalGeneratorRankNat,
    hU.isPowerful.index_closedPowerSubgroup_prime_eq_pow_rank hU.isProP
      hU.isTopologicallyFinitelyGenerated]

/-- In a uniform profinite pro-`p` group, `[U : λ_1] = p ^ uniformDimension p U`. -/
theorem index_pLowerCentralSeries_one (hU : IsUniform p U) :
    (pLowerCentralSeries p U 1).index = p ^ uniformDimension p U := by
  rw [hU.pLowerCentralSeries_eq_closedPowerSubgroup 1, pow_one, hU.index_closedPowerSubgroup_prime]

/-- `uniformDimension p U` is the unique natural number `d` with `[U : λ_1] = p ^ d`. -/
theorem index_pLowerCentralSeries_one_eq_pow_iff (hU : IsUniform p U) {d : ℕ} :
    (pLowerCentralSeries p U 1).index = p ^ d ↔ d = uniformDimension p U := by
  rw [hU.index_pLowerCentralSeries_one]
  exact ⟨fun h ↦ (Nat.pow_right_injective hp.out.two_le h).symm, fun h ↦ by rw [h]⟩

/-- Every successive lower `p`-series index `[λ_k : λ_{k+1}]` of a uniform profinite pro-`p` group
equals `p ^ uniformDimension p U`. -/
theorem relIndex_pLowerCentralSeries (hU : IsUniform p U) (k : ℕ) :
    (pLowerCentralSeries p U (k + 1)).relIndex (pLowerCentralSeries p U k) =
      p ^ uniformDimension p U := by
  rw [((hU.isProP.isUniform_iff_isPowerful_and_relIndex_pLowerCentralSeries_eq
    hU.isTopologicallyFinitelyGenerated).mp hU).2 k, hU.index_pLowerCentralSeries_one]

/-- Every graded piece `gr_k(U)` of a uniform profinite pro-`p` group has cardinality
`p ^ uniformDimension p U`. -/
theorem natCard_gradedPiece (hU : IsUniform p U) (k : ℕ) :
    Nat.card (gradedPiece p U k) = p ^ uniformDimension p U := by
  rw [natCard_gradedPiece_eq_relIndex, hU.relIndex_pLowerCentralSeries k]

/-- For every `k`, the `k`-th term `λ_k(U)` of a uniform profinite pro-`p` group has index
`p ^ (k * uniformDimension p U)`. -/
theorem index_pLowerCentralSeries (hU : IsUniform p U) (k : ℕ) :
    (pLowerCentralSeries p U k).index = p ^ (k * uniformDimension p U) := by
  induction k with
  | zero => rw [pLowerCentralSeries_zero, Subgroup.index_top, zero_mul, pow_zero]
  | succ k ih =>
    rw [← Subgroup.relIndex_mul_index (pLowerCentralSeries_succ_le k),
      hU.relIndex_pLowerCentralSeries k, ih, ← pow_add, add_mul, one_mul, add_comm]

/-- For every `k`, `closedPowerSubgroup U (p ^ k)` has index `p ^ (k * uniformDimension p U)`. -/
theorem index_closedPowerSubgroup_pow (hU : IsUniform p U) (k : ℕ) :
    (closedPowerSubgroup U (p ^ k)).index = p ^ (k * uniformDimension p U) := by
  rw [← hU.pLowerCentralSeries_eq_closedPowerSubgroup k, hU.index_pLowerCentralSeries k]

end IsUniform

end ConstantIndex

/-! ### Closure properties: products and canonical power subgroups -/

section Closure

section Products

variable {p : ℕ} {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A binary product of uniform groups is uniform. -/
theorem IsUniform.prod (hG : IsUniform p G) (hH : IsUniform p H) : IsUniform p (G × H) := by
  refine ⟨hG.isProP.prod hH.isProP,
    hG.isTopologicallyFinitelyGenerated.prod hH.isTopologicallyFinitelyGenerated, ?_,
    hG.isPowerful.prod hH.isPowerful⟩
  rintro ⟨g, h⟩ hgh
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hgh
  exact Prod.ext
    (hG.eq_one_of_isOfFinOrder (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Prod.fst hpow⟩))
    (hH.eq_one_of_isOfFinOrder (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Prod.snd hpow⟩))

/-- A binary product of topological groups is uniform if and only if both factors are. -/
theorem isUniform_prod_iff : IsUniform p (G × H) ↔ IsUniform p G ∧ IsUniform p H := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hG, hH⟩ ↦ hG.prod hH⟩
  · refine ⟨h.isProP.of_surjective (MonoidHom.fst G H) continuous_fst Prod.fst_surjective,
      (isTopologicallyFinitelyGenerated_prod_iff.mp h.isTopologicallyFinitelyGenerated).1,
      fun g hg ↦ ?_, (isPowerful_prod_iff.mp h.isPowerful).1⟩
    exact congrArg Prod.fst (h.eq_one_of_isOfFinOrder ((MonoidHom.inl G H).isOfFinOrder hg))
  · refine ⟨h.isProP.of_surjective (MonoidHom.snd G H) continuous_snd Prod.snd_surjective,
      (isTopologicallyFinitelyGenerated_prod_iff.mp h.isTopologicallyFinitelyGenerated).2,
      fun g hg ↦ ?_, (isPowerful_prod_iff.mp h.isPowerful).2⟩
    exact congrArg Prod.snd (h.eq_one_of_isOfFinOrder ((MonoidHom.inr G H).isOfFinOrder hg))

/-- `TauCeti.uniformDimension` is additive on binary products of uniform profinite pro-`p` groups.
-/
theorem uniformDimension_prod [hp : Fact p.Prime] [CompactSpace G] [TotallyDisconnectedSpace G]
    [CompactSpace H] [TotallyDisconnectedSpace H] (hG : IsUniform p G) (hH : IsUniform p H) :
    uniformDimension p (G × H) = uniformDimension p G + uniformDimension p H := by
  rw [uniformDimension_def, closedPowerSubgroup_prod, Subgroup.index_prod,
    hG.index_closedPowerSubgroup_prime, hH.index_closedPowerSubgroup_prime, ← pow_add,
    Nat.log_pow hp.out.one_lt]

/-- A finite product of uniform groups is uniform. -/
theorem IsUniform.pi {ι : Type*} [Finite ι] {F : ι → Type*} [∀ i, Group (F i)]
    [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalGroup (F i)]
    (hF : ∀ i, IsUniform p (F i)) : IsUniform p (∀ i, F i) := by
  refine ⟨IsProP.pi fun i ↦ (hF i).isProP,
    IsTopologicallyFinitelyGenerated.pi fun i ↦ (hF i).isTopologicallyFinitelyGenerated,
    fun f hf ↦ ?_, IsPowerful.pi fun i ↦ (hF i).isPowerful⟩
  funext i
  exact (hF i).eq_one_of_isOfFinOrder ((Pi.evalMonoidHom F i).isOfFinOrder hf)

/-- A finite product of topological groups is uniform if and only if each factor is. -/
theorem isUniform_pi_iff {ι : Type*} [Finite ι] {F : ι → Type*} [∀ i, Group (F i)]
    [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalGroup (F i)] :
    IsUniform p (∀ i, F i) ↔ ∀ i, IsUniform p (F i) := by
  classical
  refine ⟨fun h i ↦ ⟨h.isProP.of_surjective (Pi.evalMonoidHom F i) (continuous_apply i)
      (Function.surjective_eval i),
    (isTopologicallyFinitelyGenerated_pi_iff.mp h.isTopologicallyFinitelyGenerated) i,
    fun g hg ↦ ?_, (isPowerful_pi_iff.mp h.isPowerful) i⟩, IsUniform.pi⟩
  have h1 := congrFun (h.eq_one_of_isOfFinOrder ((MonoidHom.mulSingle F i).isOfFinOrder hg)) i
  simpa using h1

/-- Dependent version of `Subgroup.index_pi` for a finite family of groups. -/
private theorem index_pi_dependent {ι : Type*} [Fintype ι] {F : ι → Type*} [∀ i, Group (F i)]
    (H : ∀ i, Subgroup (F i)) : (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight fun x y ↦ ?_).trans (Setoid.piQuotientEquiv _).symm)
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_pi, Set.mem_univ, forall_true_left,
    Pi.mul_apply, Pi.inv_apply]
  exact forall_congr' fun i ↦ (QuotientGroup.leftRel_apply (s := H i)).symm

/-- `TauCeti.uniformDimension` is additive on finite products of uniform profinite pro-`p` groups.
-/
theorem uniformDimension_pi [hp : Fact p.Prime] {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, Group (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalGroup (F i)]
    [∀ i, CompactSpace (F i)] [∀ i, TotallyDisconnectedSpace (F i)]
    (hF : ∀ i, IsUniform p (F i)) :
    uniformDimension p (∀ i, F i) = ∑ i, uniformDimension p (F i) := by
  rw [uniformDimension_def, closedPowerSubgroup_pi, index_pi_dependent]
  simp_rw [fun i ↦ (hF i).index_closedPowerSubgroup_prime]
  rw [Finset.prod_pow_eq_pow_sum, Nat.log_pow hp.out.one_lt]

end Products

section PowerSubgroup

variable {p : ℕ} [hp : Fact p.Prime] {U : Type*} [Group U] [TopologicalSpace U]
  [IsTopologicalGroup U] [CompactSpace U] [TotallyDisconnectedSpace U]

/-- Every term `λ_n(U)` of the lower `p`-series of a uniform profinite pro-`p` group is uniform. -/
theorem IsUniform.pLowerCentralSeries (hU : IsUniform p U) (n : ℕ) :
    IsUniform p (TauCeti.pLowerCentralSeries p U n) := by
  refine ⟨hU.isProP.subgroup _,
    hU.isTopologicallyFinitelyGenerated.of_openSubgroup
      ⟨TauCeti.pLowerCentralSeries p U n,
        hU.isTopologicallyFinitelyGenerated.isOpen_pLowerCentralSeries hp.out n⟩,
    fun g hg ↦ Subtype.ext (hU.eq_one_of_isOfFinOrder
      ((TauCeti.pLowerCentralSeries p U n).subtype.isOfFinOrder hg)),
    hU.isPowerful.pLowerCentralSeries_isPowerful hU.isProP hU.isTopologicallyFinitelyGenerated n⟩

/-- Every canonical power subgroup `closedPowerSubgroup U (p ^ n)` of a uniform profinite pro-`p`
group is uniform. -/
theorem IsUniform.closedPowerSubgroup_pow (hU : IsUniform p U) (n : ℕ) :
    IsUniform p (closedPowerSubgroup U (p ^ n)) := by
  rw [← hU.pLowerCentralSeries_eq_closedPowerSubgroup n]
  exact hU.pLowerCentralSeries n

/-- Every term `λ_n(U)` of the lower `p`-series of a uniform profinite pro-`p` group has the same
`TauCeti.uniformDimension` as `U`. -/
theorem IsUniform.uniformDimension_pLowerCentralSeries (hU : IsUniform p U) (n : ℕ) :
    uniformDimension p (TauCeti.pLowerCentralSeries p U n) = uniformDimension p U := by
  set L := TauCeti.pLowerCentralSeries p U n
  have : CompactSpace L := isCompact_iff_compactSpace.mp (isClosed_pLowerCentralSeries n).isCompact
  have hL : IsUniform p L := hU.pLowerCentralSeries n
  have hmap := hU.isPowerful.map_subtype_pLowerCentralSeries_pLowerCentralSeries hU.isProP
    hU.isTopologicallyFinitelyGenerated n 1
  have hidx1 : (TauCeti.pLowerCentralSeries p U (n + 1)).index =
      (TauCeti.pLowerCentralSeries p L 1).index * L.index := by
    rw [← hmap, Subgroup.index_map_subtype]
  have hidx2 : (TauCeti.pLowerCentralSeries p U (n + 1)).index =
      (TauCeti.pLowerCentralSeries p U (n + 1)).relIndex L * L.index :=
    (Subgroup.relIndex_mul_index (pLowerCentralSeries_succ_le n)).symm
  have hLpos : 0 < L.index := by
    rw [hU.index_pLowerCentralSeries n]
    exact pow_pos hp.out.pos _
  have hEq : (TauCeti.pLowerCentralSeries p L 1).index =
      (TauCeti.pLowerCentralSeries p U (n + 1)).relIndex L :=
    Nat.eq_of_mul_eq_mul_right hLpos (hidx1.symm.trans hidx2)
  rw [hL.index_pLowerCentralSeries_one, hU.relIndex_pLowerCentralSeries n] at hEq
  exact Nat.pow_right_injective hp.out.two_le hEq

/-- Every canonical power subgroup `closedPowerSubgroup U (p ^ n)` of a uniform profinite pro-`p`
group has the same `TauCeti.uniformDimension` as `U`. -/
theorem IsUniform.uniformDimension_closedPowerSubgroup_pow (hU : IsUniform p U) (n : ℕ) :
    uniformDimension p (closedPowerSubgroup U (p ^ n)) = uniformDimension p U := by
  rw [← hU.pLowerCentralSeries_eq_closedPowerSubgroup n]
  exact hU.uniformDimension_pLowerCentralSeries n

end PowerSubgroup

end Closure

/-! ### Concrete examples -/

section Examples

variable (p : ℕ) [hp : Fact p.Prime]

/-- The closed `p ^ n`-th power subgroup of `Multiplicative ℤ_[p]` is the level `p ^ n ℤ_p`. -/
theorem closedPowerSubgroup_multiplicative_padicInt (n : ℕ) :
    closedPowerSubgroup (Multiplicative ℤ_[p]) (p ^ n) = (padicIntLevel p n).toSubgroup := by
  rw [closedPowerSubgroup_eq_range_powMonoidHom]
  ext x
  rw [MonoidHom.mem_range]
  change (∃ y, (powMonoidHom (p ^ n)) y = x) ↔ x ∈ padicIntLevel p n
  rw [mem_padicIntLevel_iff]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y.toAdd, ?_⟩
    simp [nsmul_eq_mul]
  · rintro ⟨z, hz⟩
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    apply Multiplicative.toAdd.injective
    simp [hz, nsmul_eq_mul]

/-- The additive group `Multiplicative ℤ_[p]` is uniform. -/
theorem isUniform_multiplicative_padicInt : IsUniform p (Multiplicative ℤ_[p]) := by
  refine ⟨isProP_multiplicative_padicInt p,
    isTopologicallyFinitelyGenerated_multiplicative_padicInt p, fun g hg ↦ ?_,
    isPowerful_of_isMulCommutative p⟩
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  have hmul : (n : ℤ_[p]) * g.toAdd = 0 := by
    have h := congrArg Multiplicative.toAdd hpow
    simpa [nsmul_eq_mul] using h
  have hzero : g.toAdd = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (Nat.cast_ne_zero.mpr hn.ne')
  exact Multiplicative.toAdd.injective (by simpa using hzero)

/-- `Multiplicative ℤ_[p]` has uniform dimension `1`. -/
@[simp]
theorem uniformDimension_multiplicative_padicInt :
    uniformDimension p (Multiplicative ℤ_[p]) = 1 := by
  have h1 := closedPowerSubgroup_multiplicative_padicInt p 1
  rw [pow_one] at h1
  rw [uniformDimension_def, h1, index_padicIntLevel, Nat.log_pow hp.out.one_lt]

/-- For every finite index type `X`, `Multiplicative (X → ℤ_[p])` is uniform. -/
theorem isUniform_multiplicative_pi_padicInt (X : Type*) [Finite X] :
    IsUniform p (Multiplicative (X → ℤ_[p])) :=
  (IsUniform.pi fun _ : X ↦ isUniform_multiplicative_padicInt p).of_equiv
    (ContinuousMulEquiv.piMultiplicative fun _ : X ↦ ℤ_[p]).symm

/-- For every finite index type `X`, `Multiplicative (X → ℤ_[p])` has uniform dimension
`Nat.card X` (in particular, `Multiplicative (Fin d → ℤ_[p])` has dimension `d`). -/
@[simp]
theorem uniformDimension_multiplicative_pi_padicInt (X : Type*) [Finite X] :
    uniformDimension p (Multiplicative (X → ℤ_[p])) = Nat.card X := by
  have := Fintype.ofFinite X
  rw [uniformDimension_congr (ContinuousMulEquiv.piMultiplicative fun _ : X ↦ ℤ_[p]),
    uniformDimension_pi fun _ : X ↦ isUniform_multiplicative_padicInt p]
  simp [Nat.card_eq_fintype_card]

/-- The cyclic group `Multiplicative (ZMod p)` is not uniform, as it has nontrivial `p`-torsion. -/
theorem not_isUniform_multiplicative_zmod : ¬ IsUniform p (Multiplicative (ZMod p)) := by
  intro hunif
  have hpow : (Multiplicative.ofAdd (1 : ZMod p)) ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    simp [nsmul_eq_mul]
  have h1 := hunif.eq_one_of_pow_prime_eq_one hp.out.pos hpow
  exact (one_ne_zero : (1 : ZMod p) ≠ 0) (by simpa using congrArg Multiplicative.toAdd h1)

end Examples

section ZModExamples

variable (p : ℕ)

/-- The cyclic group `Multiplicative (ZMod p)` is powerful (being abelian). -/
theorem isPowerful_multiplicative_zmod : IsPowerful p (Multiplicative (ZMod p)) :=
  isPowerful_of_isMulCommutative p

/-- In `Multiplicative (ZMod p)`, every term `λ_k` with `k ≥ 1` of the lower `p`-series is
trivial. -/
theorem pLowerCentralSeries_multiplicative_zmod_of_pos {k : ℕ} (hk : 0 < k) :
    pLowerCentralSeries p (Multiplicative (ZMod p)) k = ⊥ := by
  refine le_bot_iff.mp ((pLowerCentralSeries_antitone hk).trans ?_)
  rw [pLowerCentralSeries_eq_of_discreteTopology,
    Subgroup.top_pLowerCentralSeries_eq_range_powMonoidHom, pow_one,
    MonoidHom.range_eq_bot_iff.mpr]
  exact MonoidHom.ext fun x ↦ by
    apply Multiplicative.toAdd.injective
    simp [nsmul_eq_mul]

/-- In `Multiplicative (ZMod p)`, the zeroth lower `p`-series index `[λ_0 : λ_1]` equals `p`. -/
theorem relIndex_pLowerCentralSeries_multiplicative_zmod_zero :
    (pLowerCentralSeries p (Multiplicative (ZMod p)) 1).relIndex
      (pLowerCentralSeries p (Multiplicative (ZMod p)) 0) = p := by
  rw [pLowerCentralSeries_zero, Subgroup.relIndex_top_right,
    pLowerCentralSeries_multiplicative_zmod_of_pos p zero_lt_one, Subgroup.index_bot,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- In `Multiplicative (ZMod p)`, every subsequent lower `p`-series index `[λ_{k+1} : λ_{k+2}]`
equals `1`. -/
theorem relIndex_pLowerCentralSeries_multiplicative_zmod_succ (k : ℕ) :
    (pLowerCentralSeries p (Multiplicative (ZMod p)) (k + 2)).relIndex
      (pLowerCentralSeries p (Multiplicative (ZMod p)) (k + 1)) = 1 := by
  rw [pLowerCentralSeries_multiplicative_zmod_of_pos p (Nat.succ_pos _),
    pLowerCentralSeries_multiplicative_zmod_of_pos p (Nat.succ_pos _), Subgroup.relIndex_self]

end ZModExamples

end TauCeti
