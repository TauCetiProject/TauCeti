/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteCyclic

import Mathlib.Data.FunLike.Fintype

/-!
# Degree-one evaluation duality and Euler characteristic for groups of order two

Let `G` be a topological group of order two, `M` a topological `G`-module killed by `n ≠ 0`, and
`N ≃+ ZMod n` a `G`-module on which `1 ≠ g ∈ G` acts by `g • y = -y` (modeling `μₙ` over `ℝ`).

1. **Euler characteristic:** For discrete `G`, comparing `g - 1` and `1 + g` on `M` with `G`-maps
   `M → N` yields `|M| · |H¹(G, M)| = |H⁰(G, M)| · |H⁰(G, InternalHom G M N)|`, hence
   `|H¹(G, InternalHom G M N)| = |H¹(G, M)|` for finite discrete `M` over any topological `G`.
2. **Degree-one duality:** For discrete `G`, the norm on `N` vanishes, so `H²(G, N) ≃+ H⁰(G, N)`
   evaluates `(1, 1)` cup products as `(b g) (a g)`. Equal cardinalities give bijectivity of
   `dualityMap1 G M N` and of its composition with any injective `H²(G, N) →+ ZMod n`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Theorems 2.8 and 2.13.
* J.-P. Serre, *Local Fields*, Springer GTM 67 (1979), Chapter VIII, §4.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN

section EulerHelpers

variable {G : Type uG} [Group G] (M : Type uM) [AddCommGroup M] [DistribMulAction G M]

private def diffHom (g : G) : M →+ M where
  toFun m := g • m - m
  map_zero' := by simp
  map_add' _ _ := by simp only [smul_add]; abel

private def normHom (g : G) : M →+ M where
  toFun m := m + g • m
  map_zero' := by simp
  map_add' _ _ := by simp only [smul_add]; abel

variable {M}

private theorem ker_diffHom_eq_H0 {g : G} (hguniq : ∀ x : G, x ≠ 1 → x = g) :
    (diffHom M g).ker = H0 G M := by
  ext m
  simp only [AddMonoidHom.mem_ker, diffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, sub_eq_zero,
    FixedPoints.mem_addSubgroup]
  refine ⟨fun hm x => ?_, fun hm => hm g⟩
  rcases (eq_or_ne x 1).imp_right (hguniq x) with rfl | hx
  · exact one_smul G m
  · exact hx ▸ hm

private theorem range_diffHom_le_ker_normHom {g : G} (hgg : g * g = 1) :
    (diffHom M g).range ≤ (normHom M g).ker := by
  rintro _ ⟨m, rfl⟩
  simp only [AddMonoidHom.mem_ker, normHom, diffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    smul_sub, ← mul_smul, hgg, one_smul]
  abel

private theorem range_normHom_le_H0 {g : G} (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1) :
    (normHom M g).range ≤ H0 G M := by
  rw [← ker_diffHom_eq_H0 hguniq]
  rintro _ ⟨m, rfl⟩
  simp only [AddMonoidHom.mem_ker, diffHom, normHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    smul_add, ← mul_smul, hgg, one_smul]
  abel

private noncomputable def z1OfMemKerNorm [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace M] [IsTopologicalAddGroup M] {g : G} (hg1 : g ≠ 1)
    (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1) (m : (normHom M g).ker) : Z1 G M :=
  open scoped Classical in
  ⟨fun x => if x = 1 then 0 else m.val,
    mem_Z1_iff.mpr ⟨continuous_of_discreteTopology, fun x y => by
    rcases (eq_or_ne x 1).imp_right (hguniq x) with rfl | hx <;>
      rcases (eq_or_ne y 1).imp_right (hguniq y) with rfl | hy
    · simp
    · simp [hy, hg1]
    · simp [hx, hg1]
    · simp only [hx, hy, hgg, hg1, ↓reduceIte]
      exact ((add_comm (g • m.val) m.val).trans (AddMonoidHom.mem_ker.mp m.property)).symm⟩⟩

private theorem z1OfMemKerNorm_val_gen [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace M] [IsTopologicalAddGroup M] {g : G} (hg1 : g ≠ 1)
    (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1) (m : (normHom M g).ker) :
    (z1OfMemKerNorm hg1 hguniq hgg m).val g = m.val := by
  simp [z1OfMemKerNorm, hg1]

private def evalZ1AtGen [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {g : G} (hgg : g * g = 1) : Z1 G M →+ (normHom M g).ker where
  toFun f := ⟨f.val g, by
    have h := (mem_Z1_iff.mp f.property).2 g g
    rw [hgg, map_one_of_mem_Z1 f.property] at h
    exact (add_comm (f.val g) (g • f.val g)).trans h.symm⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem evalZ1AtGen_z1OfMemKerNorm [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace M] [IsTopologicalAddGroup M] {g : G} (hg1 : g ≠ 1)
    (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1) (m : (normHom M g).ker) :
    evalZ1AtGen hgg (z1OfMemKerNorm hg1 hguniq hgg m) = m :=
  Subtype.ext (z1OfMemKerNorm_val_gen hg1 hguniq hgg m)

private noncomputable def h1EquivKerNormQuot [TopologicalSpace G] [DiscreteTopology G]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M] {g : G} (hg1 : g ≠ 1)
    (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1) (hzpow : ∀ x : G, x ∈ Subgroup.zpowers g) :
    H1 G M ≃+ (normHom M g).ker ⧸ (diffHom M g).range.addSubgroupOf (normHom M g).ker := by
  let S := (diffHom M g).range.addSubgroupOf (normHom M g).ker
  let φ : Z1 G M →+ (normHom M g).ker ⧸ S := (QuotientAddGroup.mk' S).comp (evalZ1AtGen hgg)
  have hker : ∀ f : Z1 G M, φ f = 0 ↔ f ∈ (B1 G M).addSubgroupOf (Z1 G M) := fun f => by
    rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    exact (H1pi_eq_zero_iff_exists_smul_sub_eq g hzpow f).symm.trans
      (H1pi_eq_zero_iff.trans AddSubgroup.mem_addSubgroupOf.symm)
  refine AddEquiv.ofBijective
    (QuotientAddGroup.lift _ φ fun f hf => AddMonoidHom.mem_ker.mpr ((hker f).mpr hf)) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    induction x using QuotientAddGroup.induction_on with
    | _ f => exact (QuotientAddGroup.eq_zero_iff f).mpr ((hker f).mp hx)
  · intro q
    induction q using QuotientAddGroup.induction_on with
    | _ m =>
      refine ⟨(z1OfMemKerNorm hg1 hguniq hgg m : H1 G M), ?_⟩
      rw [QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        evalZ1AtGen_z1OfMemKerNorm]

private def h0InternalHomEquivQuotHom {N : Type uN} [AddCommGroup N] [DistribMulAction G N]
    {g : G} (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgN : ∀ y : N, g • y = -y) :
    H0 G (InternalHom G M N) ≃+ ((M ⧸ (normHom M g).range) →+ N) where
  toFun φ := QuotientAddGroup.lift (normHom M g).range φ.val.toAddMonoidHom <| by
    rintro _ ⟨m, rfl⟩
    have hfix := InternalHom.smul_eq_self_iff.mp
      ((FixedPoints.mem_addSubgroup G (InternalHom G M N) φ.val).mp φ.property g) m
    rw [hgN] at hfix
    exact (φ.val.toAddMonoidHom.map_add m (g • m)).trans (by rw [hfix, add_neg_cancel])
  invFun ψ := ⟨InternalHom.of G (ψ.comp (QuotientAddGroup.mk' (normHom M g).range)),
    (FixedPoints.mem_addSubgroup G (InternalHom G M N) _).mpr fun x => by
      rcases (eq_or_ne x 1).imp_right (hguniq x) with rfl | hx
      · exact one_smul G _
      · rw [hx]
        refine InternalHom.smul_eq_self_iff.mpr fun m => ?_
        rw [hgN]
        have hmk : (QuotientAddGroup.mk (m + g • m) : M ⧸ (normHom M g).range) = 0 :=
          (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨m, rfl⟩)
        exact eq_neg_of_add_eq_zero_right (by simp [← map_add, ← QuotientAddGroup.mk_add, hmk])⟩
  left_inv _ := Subtype.ext (InternalHom.ext (AddMonoidHom.ext fun _ => rfl))
  right_inv _ := AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun _ => rfl
  map_add' _ _ := AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun _ => rfl

private theorem subsingleton_H1_of_not_discreteTopology [TopologicalSpace G]
    (hG : Nat.card G = 2) (hndisc : ¬ DiscreteTopology G)
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] : Subsingleton (H1 G M) := by
  obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  suffices ∀ x : H1 G M, x = 0 from ⟨fun a b => (this a).trans (this b).symm⟩
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    suffices f = 0 by rw [this, QuotientAddGroup.mk_zero]
    ext y
    rcases (eq_or_ne y 1).imp_right (hguniq y) with rfl | hy
    · exact map_one_of_mem_Z1 f.property
    · rw [hy]
      by_contra hne
      have hfg : f.val g ≠ 0 := hne
      apply hndisc
      rw [discreteTopology_iff_isOpen_singleton]
      intro z
      convert (mem_Z1_iff.mp f.property).1.isOpen_preimage {f.val z} (isOpen_discrete _)
      ext u
      have hf1 : f.val 1 = 0 := map_one_of_mem_Z1 f.property
      rcases (eq_or_ne z 1).imp_right (hguniq z) with rfl | rfl <;>
        rcases (eq_or_ne u 1).imp_right (hguniq u) with rfl | rfl
      · simp
      · simp [hf1, hg1, hfg]
      · simp [hf1, hg1.symm, hfg.symm]
      · simp

end EulerHelpers

section EulerCharacteristic

variable {G : Type uG} [Group G]

/-- **Euler characteristic for a discrete group of order two**: for a `G`-module `M` killed by
`n ≠ 0` and `N ≃+ ZMod n` with inversion action `g • y = -y` (`g ≠ 1`),
`|M| * |H¹(G, M)| = |H⁰(G, M)| * |H⁰(G, InternalHom G M N)|` (`0 = 0` when `M` is infinite). -/
theorem natCard_mul_natCard_H1_of_natCard_eq_two [TopologicalSpace G] [DiscreteTopology G]
    (hG : Nat.card G = 2) {M : Type uM} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
    {N : Type uN} [AddCommGroup N] [DistribMulAction G N] {n : ℕ} [NeZero n]
    (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y) :
    Nat.card M * Nat.card (H1 G M) =
      Nat.card (H0 G M) * Nat.card (H0 G (InternalHom G M N)) := by
  obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  have hgg : g * g = 1 := by rw [← sq, ← hG]; exact pow_card_eq_one'
  have hzpow : ∀ x : G, x ∈ Subgroup.zpowers g := fun _ => mem_zpowers_of_prime_card hG hg1
  have hQ : ∀ q : M ⧸ (normHom M g).range, n • q = 0 := fun q =>
    QuotientAddGroup.induction_on q fun m => by
      rw [← QuotientAddGroup.mk_nsmul, hM m, QuotientAddGroup.mk_zero]
  have hcardH0' : Nat.card (H0 G (InternalHom G M N)) = Nat.card (M ⧸ (normHom M g).range) := by
    rw [Nat.card_congr (h0InternalHomEquivQuotHom hguniq (hN g hg1)).toEquiv,
      e.natCard_addMonoidHom_zmod hQ]
  rcases finite_or_infinite M with _ | _
  · have hcardM : Nat.card M = Nat.card (diffHom M g).range * Nat.card (H0 G M) := by
      rw [← ker_diffHom_eq_H0 hguniq,
        ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (diffHom M g)).toEquiv]
      exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    have hsub := range_diffHom_le_ker_normHom (M := M) hgg
    have hcardSub : Nat.card ((diffHom M g).range.addSubgroupOf (normHom M g).ker) =
        Nat.card (diffHom M g).range :=
      Nat.card_congr ⟨fun x => ⟨x.val.val, x.property⟩,
        fun y => ⟨⟨y.val, hsub y.property⟩, y.property⟩,
        fun _ => rfl, fun _ => rfl⟩
    have hcardKer :
        Nat.card (normHom M g).ker = Nat.card (H1 G M) * Nat.card (diffHom M g).range := by
      rw [Nat.card_congr (h1EquivKerNormQuot hg1 hguniq hgg hzpow).toEquiv, ← hcardSub]
      exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    have hcardQuot : Nat.card (M ⧸ (normHom M g).range) = Nat.card (normHom M g).ker := by
      have h₁ := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (normHom M g).range
      have h₂ := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (normHom M g).ker
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (normHom M g)).toEquiv,
        mul_comm] at h₂
      exact Nat.mul_right_cancel Nat.card_pos (h₁.symm.trans h₂)
    rw [hcardM, hcardH0', hcardQuot, hcardKer]
    ring
  · rw [Nat.card_eq_zero_of_infinite, zero_mul, hcardH0']
    symm
    by_contra hne
    have : Finite (H0 G M) := Nat.finite_of_card_ne_zero (left_ne_zero_of_mul hne)
    have hle := range_normHom_le_H0 (M := M) hguniq hgg
    have : Finite (normHom M g).range :=
      Finite.of_injective (AddSubgroup.inclusion hle) (AddSubgroup.inclusion_injective hle)
    have hM0 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (normHom M g).range
    rw [Nat.card_eq_zero_of_infinite] at hM0
    exact mul_ne_zero (right_ne_zero_of_mul hne) Nat.card_pos.ne' hM0.symm

/-- **First cohomology of the internal dual has the same cardinality** over a topological group of
order two when the non-identity element acts on `N ≃+ ZMod n` by inversion. -/
theorem natCard_H1_internalHom_eq_of_natCard_eq_two [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : Nat.card G = 2) {M : Type uM} [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    [Finite M] {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] {n : ℕ} [NeZero n]
    (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y) :
    Nat.card (H1 G (InternalHom G M N)) = Nat.card (H1 G M) := by
  by_cases hdisc : DiscreteTopology G
  · have : Finite N := Finite.of_equiv _ e.symm.toEquiv
    have h₁ := natCard_mul_natCard_H1_of_natCard_eq_two hG e hM hN
    have h₂ := natCard_mul_natCard_H1_of_natCard_eq_two hG e
      (InternalHom.nsmul_eq_zero_of_domain (G := G) (N := N) hM) hN
    have hcardH0'' :
        Nat.card (H0 G (InternalHom G (InternalHom G M N) N)) = Nat.card (H0 G M) :=
      (Nat.card_congr (Equiv.ofBijective _ (explicitCoeff0_bijective G M
        (InternalHom.eval_bijective_of_addEquiv_zmod e hM)))).symm
    rw [InternalHom.natCard_of_addEquiv_zmod e hM, hcardH0'',
      mul_comm (Nat.card (H0 G (InternalHom G M N)))] at h₂
    exact Nat.mul_left_cancel Nat.card_pos (h₂.trans h₁.symm)
  · have h1 := subsingleton_H1_of_not_discreteTopology hG hdisc (M := M)
    have h2 := subsingleton_H1_of_not_discreteTopology hG hdisc (M := InternalHom G M N)
    rw [Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩, Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩]

end EulerCharacteristic

section DegreeOneDuality

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

private noncomputable def cyclicTwoH2ToH0 [DiscreteTopology G] [Fintype G] {g : G}
    (hg1 : g ≠ 1) (hguniq : ∀ x : G, x ≠ 1 → x = g) (hzpow : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hgN : ∀ y : N, g • y = -y) : H2 G N ≃+ H0 G N := by
  have hnorm : (groupNorm G N).range.addSubgroupOf (H0 G N) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨y, hy⟩
    rw [groupNorm_apply, Fintype.sum_eq_add 1 g hg1.symm fun z hz => (hz.2 (hguniq z hz.1)).elim,
      one_smul, hgN y, add_neg_cancel] at hy
    exact AddSubgroup.mem_bot.mpr (Subtype.ext hy.symm)
  exact (explicitH2CyclicEquiv G N g hzpow).trans
    ((QuotientAddGroup.quotientAddEquivOfEq hnorm).trans QuotientAddGroup.quotientBot)

private theorem coe_cyclicTwoH2ToH0_dualityMap1_mk [DiscreteTopology G] [Fintype G]
    {g : G} (hg1 : g ≠ 1) (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1)
    (hzpow : ∀ x : G, x ∈ Subgroup.zpowers g) (hgN : ∀ y : N, g • y = -y)
    (a : Z1 G M) (b : Z1 G (InternalHom G M N)) :
    (cyclicTwoH2ToH0 hg1 hguniq hzpow hgN
        (dualityMap1 G M N (a : H1 G M) (b : H1 G (InternalHom G M N))) : N) =
      (b.val g).toAddMonoidHom (a.val g) := by
  rw [dualityMap1_mk, cyclicTwoH2ToH0, AddEquiv.trans_apply, explicitH2CyclicEquiv_mk]
  have hbot : ∀ (u : H0 G N) (hnorm : (groupNorm G N).range.addSubgroupOf (H0 G N) = ⊥),
      ((QuotientAddGroup.quotientBot
        (QuotientAddGroup.quotientAddEquivOfEq hnorm (QuotientAddGroup.mk u)) : H0 G N) : N) =
        u.val := fun u _ => by
    rw [QuotientAddGroup.quotientAddEquivOfEq_mk, ← QuotientAddGroup.quotientBot_symm_apply u,
      AddEquiv.apply_symm_apply]
  rw [AddEquiv.trans_apply, hbot]
  dsimp only
  rw [Fintype.sum_eq_add 1 g hg1.symm fun z hz => (hz.2 (hguniq z hz.1)).elim]
  have ha1 : a.val 1 = 0 := map_one_of_mem_Z1 a.property
  have hcoc := (mem_Z1_iff.mp a.property).2 g g
  rw [hgg, ha1] at hcoc
  simp only [AddMonoidHom.flip_apply, InternalHom.evalPairing_apply, ha1, map_zero,
    AddMonoidHom.zero_apply, zero_add, InternalHom.toAddMonoidHom_smul, homAction_apply,
    inv_eq_of_mul_eq_one_right hgg, eq_neg_of_add_eq_zero_left hcoc.symm, map_neg, hgN, neg_neg]

private theorem dualityMap1_injective_of_discrete [DiscreteTopology G]
    (hG : Nat.card G = 2) {n : ℕ} [NeZero n] (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y) : Function.Injective (dualityMap1 G M N) := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  have hgg : g * g = 1 := by rw [← sq, ← hG]; exact pow_card_eq_one'
  have hzpow : ∀ x : G, x ∈ Subgroup.zpowers g := fun _ => mem_zpowers_of_prime_card hG hg1
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    by_contra hne
    have hnotmem : a.val g ∉ (diffHom M g).range := fun ⟨m, hm⟩ =>
      hne ((H1pi_eq_zero_iff_exists_smul_sub_eq g hzpow a).mpr ⟨m, hm⟩)
    have hQ : ∀ q : M ⧸ (diffHom M g).range, n • q = 0 := fun q =>
      QuotientAddGroup.induction_on q fun m => by
        rw [← QuotientAddGroup.mk_nsmul, hM m, QuotientAddGroup.mk_zero]
    obtain ⟨f, hf⟩ := exists_addMonoidHom_zmod_apply_ne_zero hQ fun h0 =>
      hnotmem ((QuotientAddGroup.eq_zero_iff (a.val g)).mp h0)
    let ψ : M →+ N := e.symm.toAddMonoidHom.comp (f.comp (QuotientAddGroup.mk' _))
    have hψker : InternalHom.of G ψ ∈ (normHom (InternalHom G M N) g).ker := by
      rw [AddMonoidHom.mem_ker, normHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      ext m
      simp only [InternalHom.toAddMonoidHom_add, InternalHom.toAddMonoidHom_smul,
        InternalHom.toAddMonoidHom_zero, AddMonoidHom.add_apply, AddMonoidHom.zero_apply,
        homAction_apply, inv_eq_of_mul_eq_one_right hgg, hN g hg1]
      have hgm : ψ (g • m) = ψ m := by
        have hmk : (QuotientAddGroup.mk (g • m - m) : M ⧸ (diffHom M g).range) = 0 :=
          (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨m, rfl⟩)
        rw [← sub_eq_zero, ← map_sub]
        simp only [ψ, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, hmk, map_zero]
      rw [hgm, add_neg_cancel]
    let b := z1OfMemKerNorm hg1 hguniq hgg ⟨InternalHom.of G ψ, hψker⟩
    have heval := coe_cyclicTwoH2ToH0_dualityMap1_mk hg1 hguniq hgg hzpow (hN g hg1) a b
    rw [hx, AddMonoidHom.zero_apply, map_zero, AddSubgroup.coe_zero,
      z1OfMemKerNorm_val_gen] at heval
    exact hf ((AddEquiv.map_eq_zero_iff e.symm).mp heval.symm)

/-- **Postcomposing `dualityMap1` with any injective `H²(G, N) →+ ZMod n` is bijective** over a
topological group `G` of order two, for a finite discrete `G`-module `M` killed by `n ≠ 0` and
discrete `N ≃+ ZMod n` with inversion action `g • y = -y` (`g ≠ 1`). -/
theorem compHom_comp_dualityMap1_bijective_of_natCard_eq_two (hG : Nat.card G = 2)
    {n : ℕ} [NeZero n] (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y) {ι : H2 G N →+ ZMod n}
    (hι : Function.Injective ι) :
    Function.Bijective
      ((AddMonoidHom.compHom ι :
          (H1 G (InternalHom G M N) →+ H2 G N) →+ (H1 G (InternalHom G M N) →+ ZMod n)).comp
        (dualityMap1 G M N)) := by
  by_cases hdisc : DiscreteTopology G
  · have : Finite G := Nat.finite_of_card_ne_zero (by omega)
    have : Finite N := Finite.of_equiv _ e.symm.toEquiv
    have : Finite (Z1 G M) := Subtype.finite
    have : Finite (H1 G M) := Quotient.finite _
    have : Finite (Z1 G (InternalHom G M N)) := Subtype.finite
    have : Finite (H1 G (InternalHom G M N)) := Quotient.finite _
    have : Finite (H1 G (InternalHom G M N) →+ ZMod n) := DFunLike.finite _
    have hcompInj : Function.Injective
        (AddMonoidHom.compHom ι :
          (H1 G (InternalHom G M N) →+ H2 G N) →+ (H1 G (InternalHom G M N) →+ ZMod n)) :=
      fun _ _ hf => AddMonoidHom.ext fun y => hι (DFunLike.congr_fun hf y)
    have hM' : ∀ φ : InternalHom G M N, n • φ = 0 := InternalHom.nsmul_eq_zero_of_domain hM
    refine (hcompInj.comp
      (dualityMap1_injective_of_discrete hG e hM hN)).bijective_of_nat_card_le ?_
    rw [natCard_addMonoidHom_zmod (nsmul_H1_eq_zero (G := G) hM'),
      natCard_H1_internalHom_eq_of_natCard_eq_two hG e hM hN]
  · have := subsingleton_H1_of_not_discreteTopology hG hdisc (M := M)
    have := subsingleton_H1_of_not_discreteTopology hG hdisc (M := InternalHom G M N)
    exact ⟨fun x y _ => Subsingleton.elim x y,
      fun _ => ⟨0, AddMonoidHom.ext fun b => by simp [Subsingleton.elim b 0]⟩⟩

/-- **Degree-one evaluation duality for a topological group of order two**, for a finite discrete
`G`-module `M` killed by `n ≠ 0` and discrete `N ≃+ ZMod n` with inversion action `g • y = -y`
(`g ≠ 1`). -/
theorem dualityMap1_bijective_of_natCard_eq_two (hG : Nat.card G = 2)
    {n : ℕ} [NeZero n] (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y) : Function.Bijective (dualityMap1 G M N) := by
  by_cases hdisc : DiscreteTopology G
  · have : Finite G := Nat.finite_of_card_ne_zero (by omega)
    let _ : Fintype G := Fintype.ofFinite G
    obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
    have hzpow : ∀ x : G, x ∈ Subgroup.zpowers g := fun _ => mem_zpowers_of_prime_card hG hg1
    let eH2 := cyclicTwoH2ToH0 hg1 hguniq hzpow (hN g hg1)
    let ι : H2 G N →+ ZMod n := e.toAddMonoidHom.comp ((H0 G N).subtype.comp eH2.toAddMonoidHom)
    have hι : Function.Injective ι := e.injective.comp (Subtype.val_injective.comp eH2.injective)
    have hcompInj : Function.Injective
        (AddMonoidHom.compHom ι :
          (H1 G (InternalHom G M N) →+ H2 G N) →+ (H1 G (InternalHom G M N) →+ ZMod n)) :=
      fun _ _ hf => AddMonoidHom.ext fun y => hι (DFunLike.congr_fun hf y)
    have hbij := compHom_comp_dualityMap1_bijective_of_natCard_eq_two hG e hM hN hι
    exact ⟨dualityMap1_injective_of_discrete hG e hM hN,
      fun b => let ⟨a, ha⟩ := hbij.2 (AddMonoidHom.compHom ι b); ⟨a, hcompInj ha⟩⟩
  · have := subsingleton_H1_of_not_discreteTopology hG hdisc (M := M)
    have := subsingleton_H1_of_not_discreteTopology hG hdisc (M := InternalHom G M N)
    exact ⟨fun x y _ => Subsingleton.elim x y,
      fun _ => ⟨0, AddMonoidHom.ext fun b => by simp [Subsingleton.elim b 0]⟩⟩

end DegreeOneDuality

end TauCeti.ContCohomology
