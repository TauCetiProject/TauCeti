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

Let `G` be a topological group of order two, let `M` be a topological `G`-module killed by `n ≠ 0`,
and let `N` be a `G`-module additively isomorphic to `ZMod n` on which the non-identity element of
`G` acts by inversion (`g • y = -y`). This is the abstract group-theoretic situation of Galois
cohomology over `ℝ` with Kummer coefficients `μₙ`, where complex conjugation inverts `n`-th roots of
unity.

In this setting two phenomena hold in ordinary continuous cohomology without passing to Tate
cohomology:

1. **Euler characteristic.** When `G` is discrete, comparing the kernels and images of `g - 1` and
   `1 + g` on `M` with the `G`-equivariant homomorphisms `M → N` yields
   ```text
   |M| · |H¹(G, M)| = |H⁰(G, M)| · |H⁰(G, InternalHom G M N)|,
   ```
   for finite or infinite `M` (for infinite `M` both sides are `0`). Applying the same identity to a
   finite discrete `M` and its dual `InternalHom G M N` via double duality — and observing that when
   `G` is non-discrete every continuous `1`-cocycle into a discrete module is constant — gives
   `|H¹(G, InternalHom G M N)| = |H¹(G, M)|` without assuming `G` discrete.
2. **Perfect evaluation duality in degree one.** When `G` is discrete, the group norm on `N`
   vanishes (`y + (-y) = 0`), so the cyclic `H²` isomorphism embeds `H²(G, N)` injectively into `N`
   with image the `2`-torsion `H⁰(G, N)`. Evaluating a `(1, 1)` cup product along this embedding
   sends classes `[a] ∈ H¹(G, M)` and `[b] ∈ H¹(G, InternalHom G M N)` to `(b g) (a g)`. Additive
   functionals on `M ⧸ range (g - 1)` valued in `ZMod n` lift to `1`-cocycles of
   `InternalHom G M N` and detect every non-coboundary `a g`, proving injectivity of
   `dualityMap1 G M N`. Because `H¹` of a group of order two is `2`-torsion, homomorphisms from
   `H¹(G, InternalHom G M N)` into `H²(G, N)` match homomorphisms into `ZMod n`, so equal
   cardinalities upgrade injectivity to bijectivity of `dualityMap1 G M N` — and likewise after
   postcomposing with any injective homomorphism `H²(G, N) →+ ZMod n`. When `G` is non-discrete both
   `H¹` groups vanish, so bijectivity holds unconditionally for any topological group `G` of order
   two.

Both algebraic hypotheses are sharp. Without the inversion action `g • y = -y`, taking discrete `G`
of order two acting trivially on `M = N = ZMod 3` gives `|M| · |H¹(G, M)| = 3 · 1 = 3` whereas
`|H⁰(G, M)| · |H⁰(G, InternalHom G M N)| = 3 · 3 = 9`; acting trivially on `M = N = ZMod 4` makes
`dualityMap1` vanish on `H¹(G, ZMod 4) ≃ ZMod 2`. Likewise, degrees `0` and `2` do not satisfy
ordinary cohomology duality without replacing `H⁰` by Tate cohomology `Ĥ⁰`: for `G` acting trivially
on `M = ZMod 3` and by inversion on `N = ZMod 3`, `H⁰(G, M) = ZMod 3` while `H²(G, N) = 0`.

Companion statements for a subsingleton group `G` (the complex archimedean case, where `H¹` vanishes
and `|M|² · |H¹(G, M)| = |H⁰(G, M)| · |H⁰(G, InternalHom G M N)|`) are included at the end of the
file so downstream archimedean local duality can dispatch real and complex places uniformly.

## Main statements

* `TauCeti.ContCohomology.two_nsmul_H1_eq_zero_of_natCard_eq_two` and
  `TauCeti.ContCohomology.two_nsmul_H2_eq_zero_of_natCard_eq_two`: for `Nat.card G = 2`, both
  `H¹(G, M)` and `H²(G, M)` are `2`-torsion.
* `TauCeti.ContCohomology.natCard_mul_natCard_H1_of_natCard_eq_two`:
  `Nat.card M * Nat.card (H1 G M) = Nat.card (H0 G M) * Nat.card (H0 G (InternalHom G M N))`.
* `TauCeti.ContCohomology.natCard_H1_internalHom_eq_of_natCard_eq_two`:
  `Nat.card (H1 G (InternalHom G M N)) = Nat.card (H1 G M)`.
* `TauCeti.ContCohomology.dualityMap1_bijective_of_natCard_eq_two`: `dualityMap1 G M N` is
  bijective.
* `TauCeti.ContCohomology.bijective_compHom_dualityMap1_of_natCard_eq_two`: postcomposing
  `dualityMap1 G M N` with any injective `H2 G N →+ ZMod n` is bijective.
* `TauCeti.ContCohomology.natCard_sq_mul_natCard_H1_of_subsingleton`,
  `TauCeti.ContCohomology.dualityMap1_bijective_of_subsingleton`, and
  `TauCeti.ContCohomology.bijective_compHom_dualityMap1_of_subsingleton`: the trivial-group
  companions.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Theorem 2.8 and Theorem 2.13:
  Tate's local Euler characteristic and local duality at archimedean places.
* J.-P. Serre, *Local Fields*, Springer GTM 67 (1979), Chapter VIII, §4: cohomology of finite
  cyclic groups.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN

section TwoTorsion

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **First continuous cohomology of a group of order two is `2`-torsion.** No discreteness
hypothesis on `G` or `M` is required: for the unique non-identity element `g`, any `1`-cocycle `f`
satisfies `g • (-f g) - (-f g) = 2 • f g`. -/
theorem two_nsmul_H1_eq_zero_of_natCard_eq_two (hG : Nat.card G = 2) (x : H1 G M) :
    2 • x = 0 := by
  obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  have hgg : g * g = 1 :=
    ((eq_or_ne (g * g) 1).imp_right (hguniq _)).resolve_right fun h =>
      hg1 (mul_left_cancel (h.trans (mul_one g).symm))
  have hzpow : ∀ y : G, y ∈ Subgroup.zpowers g := fun y =>
    ((eq_or_ne y 1).imp_right (hguniq y)).elim
      (fun hy => hy ▸ ⟨0, zpow_zero g⟩) (fun hy => by rw [hy]; exact ⟨1, zpow_one g⟩)
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    rw [← QuotientAddGroup.mk_nsmul]
    refine (H1pi_eq_zero_iff_exists_smul_sub_eq g hzpow (2 • f)).mpr ⟨-f.val g, ?_⟩
    have hcoc := (mem_Z1_iff.mp f.property).2 g g
    rw [hgg, map_one_of_mem_Z1 f.property] at hcoc
    have hgf : g • f.val g = -f.val g := eq_neg_of_add_eq_zero_left hcoc.symm
    rw [AddSubgroup.coe_nsmul, two_nsmul, Pi.add_apply, smul_neg, hgf, neg_neg, sub_neg_eq_add]

/-- **Second continuous cohomology of a topological group of order two is `2`-torsion.** No
discreteness hypothesis on `G` or `M` is required: for any continuous `2`-cocycle `f` and the unique
non-identity element `g`, the continuous `1`-cochain `u ↦ f (u, 1) + f (u, g)` has coboundary
`2 • f`. -/
theorem two_nsmul_H2_eq_zero_of_natCard_eq_two [ContinuousMul G] (hG : Nat.card G = 2)
    (x : H2 G M) : 2 • x = 0 := by
  obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  have hgg : g * g = 1 :=
    ((eq_or_ne (g * g) 1).imp_right (hguniq _)).resolve_right fun h =>
      hg1 (mul_left_cancel (h.trans (mul_one g).symm))
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    obtain ⟨hfcont, hfcoc⟩ := mem_Z2_iff.mp f.property
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
      mem_B2_iff']
    refine ⟨fun u => f.val (u, 1) + f.val (u, g),
      (hfcont.comp (Continuous.prodMk_left 1)).add (hfcont.comp (Continuous.prodMk_left g)),
      fun u v => ?_⟩
    have h1 := hfcoc u v 1
    have hg := hfcoc u v g
    have hsum : f.val (u, v * 1) + f.val (u, v * g) = f.val (u, 1) + f.val (u, g) := by
      rcases (eq_or_ne v 1).imp_right (hguniq v) with rfl | hv
      · rw [one_mul, one_mul]
      · rw [hv, mul_one, hgg, add_comm]
    have hcomb := congr_arg₂ (· + ·) h1 hg
    rw [AddSubgroup.coe_nsmul, two_nsmul, Pi.add_apply, smul_add]
    symm
    exact eq_of_sub_eq_zero (by
      calc f.val (u, v) + f.val (u, v) -
            (u • f.val (v, 1) + u • f.val (v, g) - (f.val (u * v, 1) + f.val (u * v, g)) +
              (f.val (u, 1) + f.val (u, g)))
          = (f.val (u * v, 1) + f.val (u, v) + (f.val (u * v, g) + f.val (u, v))) -
              (u • f.val (v, 1) + f.val (u, v * 1) + (u • f.val (v, g) + f.val (u, v * g))) +
              (f.val (u, v * 1) + f.val (u, v * g) - (f.val (u, 1) + f.val (u, g))) := by abel
        _ = 0 := by rw [hcomb, hsum, sub_self, sub_self, add_zero])

end TwoTorsion

section EulerCharacteristic

variable {G : Type uG} [Group G]

private def diffHom (M : Type uM) [AddCommGroup M] [DistribMulAction G M] (g : G) : M →+ M where
  toFun m := g • m - m
  map_zero' := by simp
  map_add' x y := by simp only [smul_add]; abel

private def normHom (M : Type uM) [AddCommGroup M] [DistribMulAction G M] (g : G) : M →+ M where
  toFun m := m + g • m
  map_zero' := by simp
  map_add' x y := by simp only [smul_add]; abel

private theorem ker_diffHom_eq_H0 {M : Type uM} [AddCommGroup M] [DistribMulAction G M] {g : G}
    (hguniq : ∀ x : G, x ≠ 1 → x = g) : (diffHom M g).ker = H0 G M := by
  ext m
  simp only [AddMonoidHom.mem_ker, diffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, sub_eq_zero,
    FixedPoints.mem_addSubgroup]
  refine ⟨fun hm x => ?_, fun hm => hm g⟩
  rcases (eq_or_ne x 1).imp_right (hguniq x) with rfl | hx
  · exact one_smul G m
  · rw [hx]
    exact hm

private theorem range_diffHom_le_ker_normHom {M : Type uM} [AddCommGroup M] [DistribMulAction G M]
    {g : G} (hgg : g * g = 1) : (diffHom M g).range ≤ (normHom M g).ker := by
  rintro _ ⟨m, rfl⟩
  simp only [AddMonoidHom.mem_ker, normHom, diffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    smul_sub, ← mul_smul, hgg, one_smul]
  abel

private theorem range_normHom_le_H0 {M : Type uM} [AddCommGroup M] [DistribMulAction G M] {g : G}
    (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1) : (normHom M g).range ≤ H0 G M := by
  rw [← ker_diffHom_eq_H0 hguniq]
  rintro _ ⟨m, rfl⟩
  simp only [AddMonoidHom.mem_ker, diffHom, normHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    smul_add, ← mul_smul, hgg, one_smul]
  abel

private noncomputable def z1OfMemKerNorm [TopologicalSpace G] [DiscreteTopology G]
    {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] {g : G} (hg1 : g ≠ 1) (hguniq : ∀ x : G, x ≠ 1 → x = g)
    (hgg : g * g = 1) (m : (normHom M g).ker) : Z1 G M := by
  classical
  refine ⟨fun x => if x = 1 then 0 else m.1, mem_Z1_iff.mpr ⟨continuous_of_discreteTopology, ?_⟩⟩
  intro x y
  rcases (eq_or_ne x 1).imp_right (hguniq x) with rfl | hx <;>
    rcases (eq_or_ne y 1).imp_right (hguniq y) with rfl | hy
  · simp
  · simp [hy, hg1]
  · simp [hx, hg1]
  · simp only [hx, hy, hgg, ↓reduceIte, ite_eq_right_iff.mpr fun h => absurd h hg1]
    have hm0 : m.1 + g • m.1 = 0 := AddMonoidHom.mem_ker.mp m.2
    exact ((add_comm (g • m.1) m.1).trans hm0).symm

private def evalZ1AtGen [TopologicalSpace G]
    {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] {g : G} (hgg : g * g = 1) : Z1 G M →+ (normHom M g).ker where
  toFun f := ⟨f.val g, by
    have h := (mem_Z1_iff.mp f.property).2 g g
    rw [hgg, map_one_of_mem_Z1 f.property] at h
    exact (add_comm (f.val g) (g • f.val g)).trans h.symm⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private noncomputable def h1EquivKerNormQuot [TopologicalSpace G] [DiscreteTopology G]
    {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M] {g : G} (hg1 : g ≠ 1)
    (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1) :
    H1 G M ≃+ (normHom M g).ker ⧸ (diffHom M g).range.addSubgroupOf (normHom M g).ker := by
  let S := (diffHom M g).range.addSubgroupOf (normHom M g).ker
  let φ : Z1 G M →+ (normHom M g).ker ⧸ S :=
    (QuotientAddGroup.mk' S).comp (evalZ1AtGen hgg)
  have hzpow : ∀ x : G, x ∈ Subgroup.zpowers g := fun x =>
    ((eq_or_ne x 1).imp_right (hguniq x)).elim
      (fun hx => hx ▸ ⟨0, zpow_zero g⟩) (fun hx => by rw [hx]; exact ⟨1, zpow_one g⟩)
  have hker : ∀ f : Z1 G M, φ f = 0 ↔ f ∈ (B1 G M).addSubgroupOf (Z1 G M) := fun f => by
    rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    exact (H1pi_eq_zero_iff_exists_smul_sub_eq g hzpow f).symm.trans
      (H1pi_eq_zero_iff.trans AddSubgroup.mem_addSubgroupOf.symm)
  have hle : (B1 G M).addSubgroupOf (Z1 G M) ≤ φ.ker := fun f hf =>
    AddMonoidHom.mem_ker.mpr ((hker f).mpr hf)
  refine AddEquiv.ofBijective (QuotientAddGroup.lift _ φ hle) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    induction x using QuotientAddGroup.induction_on with
    | _ f => exact (QuotientAddGroup.eq_zero_iff f).mpr ((hker f).mp hx)
  · intro q
    induction q using QuotientAddGroup.induction_on with
    | _ m =>
      refine ⟨(z1OfMemKerNorm hg1 hguniq hgg m : H1 G M), ?_⟩
      rw [QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
      congr 1
      classical
      exact Subtype.ext (ite_eq_right_iff.mpr fun h => absurd h hg1)

private def h0InternalHomEquivQuotHom {M : Type uM} [AddCommGroup M] [DistribMulAction G M]
    {N : Type uN} [AddCommGroup N] [DistribMulAction G N] {g : G}
    (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgN : ∀ y : N, g • y = -y) :
    H0 G (InternalHom G M N) ≃+ ((M ⧸ (normHom M g).range) →+ N) where
  toFun φ := QuotientAddGroup.lift (normHom M g).range φ.1.toAddMonoidHom <| by
    rintro _ ⟨m, rfl⟩
    have hfix := InternalHom.smul_eq_self_iff.mp
      ((FixedPoints.mem_addSubgroup G (InternalHom G M N) φ.1).mp φ.2 g) m
    rw [hgN] at hfix
    exact (φ.1.toAddMonoidHom.map_add m (g • m)).trans (by rw [hfix, add_neg_cancel])
  invFun ψ := ⟨InternalHom.of G (ψ.comp (QuotientAddGroup.mk' (normHom M g).range)),
    (FixedPoints.mem_addSubgroup G (InternalHom G M N) _).mpr fun x => by
      rcases (eq_or_ne x 1).imp_right (hguniq x) with rfl | hx
      · exact one_smul G _
      · rw [hx]
        refine InternalHom.smul_eq_self_iff.mpr fun m => ?_
        rw [hgN]
        have hmk : (QuotientAddGroup.mk (m + g • m) : M ⧸ (normHom M g).range) = 0 := by
          rw [QuotientAddGroup.eq_zero_iff]
          exact AddMonoidHom.mem_range.mpr ⟨m, rfl⟩
        have hzero : ψ (QuotientAddGroup.mk m) + ψ (QuotientAddGroup.mk (g • m)) = 0 := by
          rw [← map_add, ← QuotientAddGroup.mk_add, hmk, map_zero]
        exact eq_neg_of_add_eq_zero_right hzero⟩
  left_inv φ := Subtype.ext (InternalHom.ext (AddMonoidHom.ext fun _ => rfl))
  right_inv ψ := AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun _ => rfl
  map_add' _ _ := AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun _ => rfl

/-- When a two-element group `G` does not carry the discrete topology, every continuous `1`-cocycle
from `G` into a discrete `G`-module `X` is constant, hence zero, so `H¹(G, X)` is trivial. -/
private theorem subsingleton_H1_of_not_discreteTopology [TopologicalSpace G] {g : G} (hg1 : g ≠ 1)
    (hguniq : ∀ x : G, x ≠ 1 → x = g) (hndisc : ¬ DiscreteTopology G)
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [DiscreteTopology X]
    [DistribMulAction G X] [ContinuousSMul G X] :
    Subsingleton (H1 G X) := by
  suffices ∀ x : H1 G X, x = 0 from ⟨fun a b => (this a).trans (this b).symm⟩
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
      have hf1 : f.val 1 = 0 := map_one_of_mem_Z1 f.property
      have hfcont : Continuous f.val := (mem_Z1_iff.mp f.property).1
      intro z
      rcases (eq_or_ne z 1).imp_right (hguniq z) with rfl | hz
      · convert hfcont.isOpen_preimage {0} (isOpen_discrete _)
        ext u
        rcases (eq_or_ne u 1).imp_right (hguniq u) with rfl | hu
        · simp [hf1]
        · simp [hu, hg1, hfg]
      · rw [hz]
        convert hfcont.isOpen_preimage {f.val g} (isOpen_discrete _)
        ext u
        rcases (eq_or_ne u 1).imp_right (hguniq u) with rfl | hu
        · simp [hf1, hg1.symm, hfg.symm]
        · simp [hu]

/-- **Euler characteristic for a discrete group of order two.** Let `G` be a discrete group with
`Nat.card G = 2`, let `M` be a topological `G`-module killed by `n ≠ 0`, and let `N` be an additive
group `N ≃+ ZMod n` on which the non-identity element of `G` acts by inversion. Then
```text
Nat.card M * Nat.card (H1 G M) = Nat.card (H0 G M) * Nat.card (H0 G (InternalHom G M N)).
```
When `M` is infinite, both sides are `0`. -/
theorem natCard_mul_natCard_H1_of_natCard_eq_two [TopologicalSpace G] [DiscreteTopology G]
    (hG : Nat.card G = 2) {M : Type uM} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
    {N : Type uN} [AddCommGroup N] [DistribMulAction G N] {n : ℕ} [NeZero n]
    (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y) :
    Nat.card M * Nat.card (H1 G M) =
      Nat.card (H0 G M) * Nat.card (H0 G (InternalHom G M N)) := by
  obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  have hgg : g * g = 1 :=
    ((eq_or_ne (g * g) 1).imp_right (hguniq _)).resolve_right fun h =>
      hg1 (mul_left_cancel (h.trans (mul_one g).symm))
  have hQ : ∀ q : M ⧸ (normHom M g).range, n • q = 0 := fun q =>
    QuotientAddGroup.induction_on q fun m => by
      rw [← QuotientAddGroup.mk_nsmul, hM m, QuotientAddGroup.mk_zero]
  have hcardH0' :
      Nat.card (H0 G (InternalHom G M N)) = Nat.card (M ⧸ (normHom M g).range) := by
    rw [Nat.card_congr (h0InternalHomEquivQuotHom hguniq (hN g hg1)).toEquiv,
      e.natCard_addMonoidHom_zmod hQ]
  rcases finite_or_infinite M with _ | _
  · have hcardM : Nat.card M = Nat.card (diffHom M g).range * Nat.card (H0 G M) := by
      rw [← ker_diffHom_eq_H0 hguniq,
        ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (diffHom M g)).toEquiv]
      exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    have hsub := range_diffHom_le_ker_normHom (M := M) hgg
    have hcardSub :
        Nat.card ((diffHom M g).range.addSubgroupOf (normHom M g).ker) =
          Nat.card (diffHom M g).range :=
      Nat.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun y => ⟨⟨y.1, hsub y.2⟩, y.2⟩,
        fun _ => rfl, fun _ => rfl⟩
    have hcardKer : Nat.card (normHom M g).ker =
        Nat.card (H1 G M) * Nat.card (diffHom M g).range := by
      rw [Nat.card_congr (h1EquivKerNormQuot hg1 hguniq hgg).toEquiv, ← hcardSub]
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
    have hQne : Nat.card (M ⧸ (normHom M g).range) ≠ 0 := right_ne_zero_of_mul hne
    have hle := range_normHom_le_H0 (M := M) hguniq hgg
    have : Finite (normHom M g).range :=
      Finite.of_injective (AddSubgroup.inclusion hle) (AddSubgroup.inclusion_injective hle)
    have hRne : Nat.card (normHom M g).range ≠ 0 := Nat.card_pos.ne'
    have hM0 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (normHom M g).range
    rw [Nat.card_eq_zero_of_infinite] at hM0
    exact mul_ne_zero hQne hRne hM0.symm

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
    have hM' : ∀ φ : InternalHom G M N, n • φ = 0 := InternalHom.nsmul_eq_zero_of_domain hM
    have h₁ := natCard_mul_natCard_H1_of_natCard_eq_two hG e hM hN
    have h₂ := natCard_mul_natCard_H1_of_natCard_eq_two hG e hM' hN
    have hcardM' : Nat.card (InternalHom G M N) = Nat.card M :=
      InternalHom.natCard_of_addEquiv_zmod e hM
    have hcardH0'' :
        Nat.card (H0 G (InternalHom G (InternalHom G M N) N)) = Nat.card (H0 G M) :=
      (Nat.card_congr (Equiv.ofBijective _ (explicitCoeff0_bijective G M
        (InternalHom.eval_bijective_of_addEquiv_zmod e hM)))).symm
    rw [hcardM', hcardH0'', mul_comm (Nat.card (H0 G (InternalHom G M N)))] at h₂
    exact Nat.mul_left_cancel Nat.card_pos (h₂.trans h₁.symm)
  · obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
    have h1 := subsingleton_H1_of_not_discreteTopology hg1 hguniq hdisc (X := M)
    have h2 := subsingleton_H1_of_not_discreteTopology hg1 hguniq hdisc (X := InternalHom G M N)
    rw [Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩, Nat.card_eq_one_iff_unique.mpr ⟨h1, ⟨0⟩⟩]

end EulerCharacteristic

section DegreeOneDuality

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem sum_univ_eq_add_of_unique_ne_one [Fintype G] {g : G} (hg1 : g ≠ 1)
    (hguniq : ∀ x : G, x ≠ 1 → x = g) {A : Type*} [AddCommMonoid A] (f : G → A) :
    ∑ x : G, f x = f 1 + f g := by
  classical
  have huniv : (Finset.univ : Finset G) = {1, g} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact (eq_or_ne x 1).imp_right (hguniq x)
  rw [huniv, Finset.sum_pair hg1.symm]

private noncomputable def cyclicTwoH2ToH0 [DiscreteTopology G] [Fintype G] {g : G}
    (hg1 : g ≠ 1) (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgN : ∀ y : N, g • y = -y) :
    H2 G N ≃+ H0 G N := by
  have hzpow : ∀ x : G, x ∈ Subgroup.zpowers g := fun x =>
    ((eq_or_ne x 1).imp_right (hguniq x)).elim
      (fun hx => hx ▸ ⟨0, zpow_zero g⟩) (fun hx => by rw [hx]; exact ⟨1, zpow_one g⟩)
  have hnorm : (groupNorm G N).range.addSubgroupOf (H0 G N) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨y, hy⟩
    rw [groupNorm_apply, sum_univ_eq_add_of_unique_ne_one hg1 hguniq, one_smul, hgN y,
      add_neg_cancel] at hy
    exact AddSubgroup.mem_bot.mpr (Subtype.ext hy.symm)
  exact (explicitH2CyclicEquiv G N g hzpow).trans
    ((QuotientAddGroup.quotientAddEquivOfEq hnorm).trans QuotientAddGroup.quotientBot)

private theorem coe_cyclicTwoH2ToH0_dualityMap1_mk [DiscreteTopology G] [Fintype G]
    {g : G} (hg1 : g ≠ 1) (hguniq : ∀ x : G, x ≠ 1 → x = g) (hgg : g * g = 1)
    (hgN : ∀ y : N, g • y = -y) (a : Z1 G M) (b : Z1 G (InternalHom G M N)) :
    (cyclicTwoH2ToH0 hg1 hguniq hgN
        (dualityMap1 G M N (a : H1 G M) (b : H1 G (InternalHom G M N))) : N) =
      (b.val g).toAddMonoidHom (a.val g) := by
  rw [dualityMap1_mk, cyclicTwoH2ToH0, AddEquiv.trans_apply, explicitH2CyclicEquiv_mk]
  have hbot : ∀ u : H0 G N,
      ∀ hnorm : (groupNorm G N).range.addSubgroupOf (H0 G N) = ⊥,
      ((QuotientAddGroup.quotientBot
        (QuotientAddGroup.quotientAddEquivOfEq hnorm (QuotientAddGroup.mk u)) : H0 G N) : N) =
        u.1 := by
    intro u hnorm
    rw [QuotientAddGroup.quotientAddEquivOfEq_mk, ← QuotientAddGroup.quotientBot_symm_apply u,
      AddEquiv.apply_symm_apply]
  rw [AddEquiv.trans_apply, hbot]
  dsimp only
  rw [sum_univ_eq_add_of_unique_ne_one hg1 hguniq]
  have ha1 : a.val 1 = 0 := map_one_of_mem_Z1 a.property
  have hcoc := (mem_Z1_iff.mp a.property).2 g g
  rw [hgg, ha1] at hcoc
  have hga : g • a.val g = -a.val g := eq_neg_of_add_eq_zero_left hcoc.symm
  simp only [AddMonoidHom.flip_apply, InternalHom.evalPairing_apply, ha1, map_zero,
    AddMonoidHom.zero_apply, zero_add, InternalHom.toAddMonoidHom_smul, homAction_apply,
    inv_eq_of_mul_eq_one_right hgg, hga, map_neg, hgN, neg_neg]

private theorem dualityMap1_injective_of_discrete [DiscreteTopology G]
    (hG : Nat.card G = 2) {n : ℕ} [NeZero n] (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y) :
    Function.Injective (dualityMap1 G M N) := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
  have hgg : g * g = 1 :=
    ((eq_or_ne (g * g) 1).imp_right (hguniq _)).resolve_right fun h =>
      hg1 (mul_left_cancel (h.trans (mul_one g).symm))
  have hzpow : ∀ x : G, x ∈ Subgroup.zpowers g := fun x =>
    ((eq_or_ne x 1).imp_right (hguniq x)).elim
      (fun hx => hx ▸ ⟨0, zpow_zero g⟩) (fun hx => by rw [hx]; exact ⟨1, zpow_one g⟩)
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    by_contra hne
    have hnotmem : a.val g ∉ (diffHom M g).range := fun ⟨m, hm⟩ =>
      hne ((H1pi_eq_zero_iff_exists_smul_sub_eq g hzpow a).mpr ⟨m, hm⟩)
    have hQ : ∀ q : M ⧸ (diffHom M g).range, n • q = 0 := fun q =>
      QuotientAddGroup.induction_on q fun m => by
        rw [← QuotientAddGroup.mk_nsmul, hM m, QuotientAddGroup.mk_zero]
    have hqne : (QuotientAddGroup.mk (a.val g) : M ⧸ (diffHom M g).range) ≠ 0 := fun h0 =>
      hnotmem ((QuotientAddGroup.eq_zero_iff (a.val g)).mp h0)
    obtain ⟨f, hf⟩ := exists_addMonoidHom_zmod_apply_ne_zero hQ hqne
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
    have hbval : b.val g = InternalHom.of G ψ := by
      classical
      exact ite_eq_right_iff.mpr fun h => absurd h hg1
    have hpair0 : dualityMap1 G M N (a : H1 G M) (b : H1 G (InternalHom G M N)) = 0 := by
      rw [hx, AddMonoidHom.zero_apply]
    have heval := coe_cyclicTwoH2ToH0_dualityMap1_mk hg1 hguniq hgg (hN g hg1) a b
    rw [hpair0, map_zero, AddSubgroup.coe_zero, hbval] at heval
    exact hf ((AddEquiv.map_eq_zero_iff e.symm).mp heval.symm)

/-- **Degree-one evaluation duality for a topological group of order two.** Let `G` be a topological
group with `Nat.card G = 2`, let `M` be a finite discrete `G`-module killed by `n ≠ 0`, and let `N`
be a discrete `G`-module `N ≃+ ZMod n` on which the non-identity element of `G` acts by inversion.
Then `dualityMap1 G M N : H¹(G, M) →+ (H¹(G, InternalHom G M N) →+ H²(G, N))` is bijective. -/
theorem dualityMap1_bijective_of_natCard_eq_two (hG : Nat.card G = 2)
    {n : ℕ} [NeZero n] (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y) :
    Function.Bijective (dualityMap1 G M N) := by
  by_cases hdisc : DiscreteTopology G
  · have : Finite G := Nat.finite_of_card_ne_zero (by omega)
    let _ : Fintype G := Fintype.ofFinite G
    have : Finite N := Finite.of_equiv _ e.symm.toEquiv
    obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
    let eH2 := cyclicTwoH2ToH0 hg1 hguniq (hN g hg1)
    let ι : H2 G N →+ ZMod n := e.toAddMonoidHom.comp ((H0 G N).subtype.comp eH2.toAddMonoidHom)
    have hιinj : Function.Injective ι :=
      e.injective.comp (Subtype.val_injective.comp eH2.injective)
    have hιrange : ∀ z : ZMod n, 2 • z = 0 → ∃ c : H2 G N, ι c = z := fun z hz => by
      have hy : e.symm z ∈ H0 G N := (FixedPoints.mem_addSubgroup G N _).mpr fun x => by
        rcases (eq_or_ne x 1).imp_right (hguniq x) with rfl | hx
        · exact one_smul G _
        · rw [hx, hN g hg1]
          have h2 : 2 • e.symm z = 0 := by rw [← map_nsmul, hz, map_zero]
          rw [two_nsmul] at h2
          exact (eq_neg_of_add_eq_zero_left h2).symm
      refine ⟨eH2.symm ⟨e.symm z, hy⟩, ?_⟩
      simp [ι]
    have hcompBij : Function.Bijective
        (AddMonoidHom.compHom ι :
          (H1 G (InternalHom G M N) →+ H2 G N) →+ (H1 G (InternalHom G M N) →+ ZMod n)) :=
      AddMonoidHom.compHom_bijective_of_forall_nsmul_eq_zero hιinj
        (two_nsmul_H1_eq_zero_of_natCard_eq_two hG) hιrange
    have : Finite (Z1 G M) := Subtype.finite
    have : Finite (H1 G M) := Quotient.finite _
    have : Finite (Z1 G (InternalHom G M N)) := Subtype.finite
    have : Finite (H1 G (InternalHom G M N)) := Quotient.finite _
    have : Finite (H1 G (InternalHom G M N) →+ ZMod n) := DFunLike.finite _
    have : Finite (H1 G (InternalHom G M N) →+ H2 G N) :=
      Finite.of_equiv _ (Equiv.ofBijective _ hcompBij).symm
    have hM' : ∀ φ : InternalHom G M N, n • φ = 0 := InternalHom.nsmul_eq_zero_of_domain hM
    refine (dualityMap1_injective_of_discrete hG e hM hN).bijective_of_nat_card_le ?_
    rw [Nat.card_congr (Equiv.ofBijective _ hcompBij),
      natCard_addMonoidHom_zmod (nsmul_H1_eq_zero (G := G) hM'),
      natCard_H1_internalHom_eq_of_natCard_eq_two hG e hM hN]
  · obtain ⟨g, hg1, hguniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
    have : Subsingleton (H1 G M) := subsingleton_H1_of_not_discreteTopology hg1 hguniq hdisc
    have : Subsingleton (H1 G (InternalHom G M N)) :=
      subsingleton_H1_of_not_discreteTopology hg1 hguniq hdisc
    exact ⟨fun x y _ => Subsingleton.elim x y, fun f =>
      ⟨0, AddMonoidHom.ext fun b => by simp [Subsingleton.elim b 0]⟩⟩

/-- **Postcomposing `dualityMap1` with any injective invariant `H²(G, N) →+ ZMod n` is bijective**
over a topological group of order two under the inversion action on `N ≃+ ZMod n`. -/
theorem bijective_compHom_dualityMap1_of_natCard_eq_two (hG : Nat.card G = 2)
    {n : ℕ} [NeZero n] (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0)
    (hN : ∀ g : G, g ≠ 1 → ∀ y : N, g • y = -y)
    {ι : H2 G N →+ ZMod n} (hι : Function.Injective ι) :
    Function.Bijective
      ((AddMonoidHom.compHom ι :
          (H1 G (InternalHom G M N) →+ H2 G N) →+ (H1 G (InternalHom G M N) →+ ZMod n)).comp
        (dualityMap1 G M N)) := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have : Finite (Z1 G M) := Subtype.finite
  have : Finite (H1 G M) := Quotient.finite _
  have : Finite (Z1 G (InternalHom G M N)) := Subtype.finite
  have : Finite (H1 G (InternalHom G M N)) := Quotient.finite _
  have : Finite (H1 G (InternalHom G M N) →+ ZMod n) := DFunLike.finite _
  have hbij1 := dualityMap1_bijective_of_natCard_eq_two hG e hM hN
  have hcompInj : Function.Injective
      (AddMonoidHom.compHom ι :
        (H1 G (InternalHom G M N) →+ H2 G N) →+ (H1 G (InternalHom G M N) →+ ZMod n)) :=
    fun f₁ f₂ hf => AddMonoidHom.ext fun y => hι (DFunLike.congr_fun hf y)
  have hM' : ∀ φ : InternalHom G M N, n • φ = 0 := InternalHom.nsmul_eq_zero_of_domain hM
  refine (hcompInj.comp hbij1.1).bijective_of_nat_card_le ?_
  rw [natCard_addMonoidHom_zmod (nsmul_H1_eq_zero (G := G) hM'),
    natCard_H1_internalHom_eq_of_natCard_eq_two hG e hM hN]

end DegreeOneDuality

section SubsingletonGroup

/-- **Euler characteristic for a trivial group.** When `G` is a subsingleton, `H¹(G, M)` is
trivial and every element of `M` and `InternalHom G M N` is invariant, so
`Nat.card M ^ 2 * Nat.card (H1 G M) = Nat.card (H0 G M) * Nat.card (H0 G (InternalHom G M N))`. -/
theorem natCard_sq_mul_natCard_H1_of_subsingleton {G : Type uG} [Group G] [TopologicalSpace G]
    [Subsingleton G] {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M] {N : Type uN} [AddCommGroup N]
    [DistribMulAction G N] {n : ℕ} [NeZero n] (e : N ≃+ ZMod n) (hM : ∀ m : M, n • m = 0) :
    Nat.card M ^ 2 * Nat.card (H1 G M) =
      Nat.card (H0 G M) * Nat.card (H0 G (InternalHom G M N)) := by
  have h1 : Nat.card (H1 G M) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨subsingleton_H1_of_subsingleton G M, ⟨0⟩⟩
  have hH0M : H0 G M = ⊤ :=
    H0_eq_top_of_smul_eq_self fun g m => by rw [Subsingleton.elim g 1, one_smul]
  have hH0M' : H0 G (InternalHom G M N) = ⊤ :=
    H0_eq_top_of_smul_eq_self fun g φ => by rw [Subsingleton.elim g 1, one_smul]
  rw [h1, mul_one, sq, hH0M, hH0M',
    Nat.card_congr (AddSubgroup.topEquiv (G := M)).toEquiv,
    Nat.card_congr (AddSubgroup.topEquiv (G := InternalHom G M N)).toEquiv,
    InternalHom.natCard_of_addEquiv_zmod e hM]

/-- **Degree-one evaluation duality for a trivial group**: both `H¹(G, M)` and
`H¹(G, InternalHom G M N)` vanish, so `dualityMap1 G M N` is bijective. -/
theorem dualityMap1_bijective_of_subsingleton {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (hG : Subsingleton G) {M : Type uM} [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    [Finite M] {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] :
    Function.Bijective (dualityMap1 G M N) := by
  have : Subsingleton G := hG
  have : Subsingleton (H1 G M) := subsingleton_H1_of_subsingleton G M
  have : Subsingleton (H1 G (InternalHom G M N)) := subsingleton_H1_of_subsingleton G _
  exact ⟨fun x y _ => Subsingleton.elim x y, fun f =>
    ⟨0, AddMonoidHom.ext fun b => by simp [Subsingleton.elim b 0]⟩⟩

/-- **Postcomposing `dualityMap1` with any homomorphism out of `H²(G, N)` is bijective** when `G`
is a subsingleton, since both `H¹` groups vanish. -/
theorem bijective_compHom_dualityMap1_of_subsingleton {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (hG : Subsingleton G) {M : Type uM} [AddCommGroup M]
    [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    [Finite M] {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] {P : Type*} [AddCommMonoid P]
    (ι : H2 G N →+ P) :
    Function.Bijective
      ((AddMonoidHom.compHom ι :
          (H1 G (InternalHom G M N) →+ H2 G N) →+ (H1 G (InternalHom G M N) →+ P)).comp
        (dualityMap1 G M N)) := by
  have : Subsingleton G := hG
  have : Subsingleton (H1 G M) := subsingleton_H1_of_subsingleton G M
  have : Subsingleton (H1 G (InternalHom G M N)) := subsingleton_H1_of_subsingleton G _
  exact ⟨fun x y _ => Subsingleton.elim x y, fun f =>
    ⟨0, AddMonoidHom.ext fun b => by simp [Subsingleton.elim b 0]⟩⟩

end SubsingletonGroup

end TauCeti.ContCohomology
