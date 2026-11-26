/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import TauCeti.RingTheory.IntegralOrder.LeftOrder
import Mathlib.RingTheory.Ideal.Maximal
-- `ContinuousMap.isUltrametricDist`: the supremum norm on `C(X, k)` is ultrametric.
import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# Ultrametric Stone–Weierstrass theorem for modules and subalgebras

Let `X` be a compact topological space and `k` a normed field whose metric is ultrametric
(`IsUltrametricDist k`). Neither completeness of `k`, nontriviality of the norm on `k`,
Hausdorffness of `X`, nor nonemptiness of `X` is required.

For a `k`-submodule `N` of `C(X, k)`, its **multiplier subalgebra** `N.leftOrder` consists of
all `u : C(X, k)` such that `u * d ∈ N` for every `d ∈ N`. The localization form of the ultrametric
Stone–Weierstrass theorem (Kaplansky–Prolla) states that a continuous map `φ : C(X, k)` lies in the
uniform closure `N.topologicalClosure` whenever, for every `a : X`, there exists `d ∈ N` agreeing
with `φ` on the fiber
`{x : X | ∀ u ∈ N.leftOrder, u x = u a}`
(`ContinuousMap.mem_topologicalClosure_of_eq_on_multiplier_fibers`).

As immediate corollaries we obtain:
* the submodule density theorem when `N.leftOrder` separates points and `N` vanishes
  nowhere
  (`ContinuousMap.submodule_topologicalClosure_eq_top_of_separatesPoints_ultrametric`), and
* Kaplansky's ultrametric Stone–Weierstrass theorem for subalgebras: every point-separating
  subalgebra `A : Subalgebra k C(X, k)` is dense in `C(X, k)`
  (`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints_ultrametric`).

## Proof overview

Assuming `φ` stays at distance strictly greater than `ε > 0` from `N`, let `B` be the subring of
multipliers of norm at most `1`. The multipliers `w ∈ B` for which `w * φ` lies within `ε` of `N`
form a proper ideal of `B`, hence are contained in a maximal ideal `m`. On the closed set
`Z = {x : X | ∀ f ∈ mᶜ, 1 ≤ ‖f x‖}`, compactness shows that any bound `‖g x‖ ≤ r` on `Z` yields
`f ∈ mᶜ` with `‖f * g‖ ≤ r` everywhere. Using this, every multiplier is constant on `Z`; thus some
`d ∈ N` agrees with `φ` on `Z`, and multiplying `φ - d` by a suitable `f ∈ mᶜ` puts `f * φ` within
`ε` of `N`, contradicting `f ∉ m`.

## References

* I. Kaplansky, *The Weierstrass theorem in fields with valuations*, Proc. Amer. Math. Soc. 1
  (1950), 356–357.
* J. B. Prolla, *Approximation of Vector Valued Functions*, North-Holland (1977).
* Adapted from the formalization by L. Alpöge and L. Sernau of `New.stoneWeierstrass_ultrametric`
  in `src/Lib/GaloisRep/WeightCongruence.lean` of the `riemann-hypothesis` repository,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

open Filter Metric Set Topology

namespace ContinuousMap

section UltrametricStoneWeierstrass

variable {X k : Type*} [TopologicalSpace X] [CompactSpace X] [NormedField k] [IsUltrametricDist k]

/-- The subring of multipliers of `N` with supremum norm at most `1`. -/
private def boundedMultipliers (N : Submodule k C(X, k)) : Subring C(X, k) :=
  N.leftOrder.toSubring ⊓
    ⨅ x : X, (Subring.unitClosedBall k).comap (ContinuousMap.evalAlgHom k k x).toRingHom

private lemma mem_boundedMultipliers {N : Submodule k C(X, k)} {u : C(X, k)} :
    u ∈ boundedMultipliers N ↔ u ∈ N.leftOrder ∧ ‖u‖ ≤ 1 := by
  rw [boundedMultipliers, Subring.mem_inf, Subalgebra.mem_toSubring,
    ContinuousMap.norm_le _ zero_le_one, Subring.mem_iInf]
  exact and_congr_right fun _ ↦ forall_congr' fun _ ↦ Subring.mem_unitClosedBall

private lemma exists_maximal_ideal_of_far (N : Submodule k C(X, k)) (φ : C(X, k)) {ε : ℝ}
    (hε : 0 ≤ ε) (h_far : ∀ g ∈ N, ε < ‖φ - g‖) :
    ∃ m : Ideal (boundedMultipliers N), m.IsMaximal ∧
      ∀ w : boundedMultipliers N, ∀ g ∈ N, ‖(w : C(X, k)) * φ - g‖ ≤ ε → w ∈ m := by
  let B := boundedMultipliers N
  let N' : Submodule B C(X, k) :=
    { N.toAddSubmonoid with
      smul_mem' := fun c d hd ↦
        Submodule.mem_leftOrder_iff.1 (mem_boundedMultipliers.1 c.property).1 d hd }
  obtain ⟨ball, hball⟩ : ∃ ball : Submodule B C(X, k), ∀ f, f ∈ ball ↔ ‖f‖ ≤ ε := by
    rcases hε.eq_or_lt with rfl | hpos
    · exact ⟨⊥, fun f ↦ by rw [Submodule.mem_bot, norm_le_zero_iff]⟩
    · refine ⟨{ (IsUltrametricDist.closedBall_openAddSubgroup C(X, k) hpos :
          AddSubgroup C(X, k)) with smul_mem' := ?_ }, fun _ ↦ mem_closedBall_zero_iff⟩
      intro c f hf
      apply mem_closedBall_zero_iff.2
      rw [Subring.smul_def, smul_eq_mul]
      have hc := (mem_boundedMultipliers.1 c.property).2
      exact (norm_mul_le (c : C(X, k)) f).trans
        ((mul_le_of_le_one_left (norm_nonneg f) hc).trans (mem_closedBall_zero_iff.1 hf))
  let I : Ideal B := (N' ⊔ ball).comap (LinearMap.toSpanSingleton B C(X, k) φ)
  have hI_ne_top : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : B) ∈ I := htop.symm ▸ Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul, Submodule.mem_sup] at h1
    rcases h1 with ⟨g, hg, r, hr, hgr⟩
    have hsub : φ - g = r := sub_eq_of_eq_add' hgr.symm
    exact (h_far g hg).not_ge (hsub ▸ (hball r).1 hr)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI_ne_top
  refine ⟨m, hm, fun w g hg hle ↦ hIm ?_⟩
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_sup]
  exact ⟨g, hg, (w : C(X, k)) * φ - g, (hball _).2 hle,
    add_sub_cancel g ((w : C(X, k)) * φ)⟩

/-- The closed set of points where every multiplier outside the prime ideal `m` has norm at
least `1`. -/
private def zeroSet {N : Submodule k C(X, k)} (m : Ideal (boundedMultipliers N)) [m.IsPrime] :
    Set X :=
  {x | ∀ f : m.primeCompl, 1 ≤ ‖(f : C(X, k)) x‖}

omit [CompactSpace X] in
private lemma isClosed_zeroSet {N : Submodule k C(X, k)} (m : Ideal (boundedMultipliers N))
    [m.IsPrime] : IsClosed (zeroSet m) := by
  rw [zeroSet, Set.ofPred_forall]
  exact isClosed_iInter fun f : m.primeCompl ↦
    isClosed_le continuous_const (f : C(X, k)).continuous.norm

private lemma exists_mul_norm_le_of_le_on_zeroSet {N : Submodule k C(X, k)}
    {m : Ideal (boundedMultipliers N)} [m.IsPrime] (g : C(X, k)) {r : ℝ} (hr : 0 < r)
    (hg : ∀ x ∈ zeroSet m, ‖g x‖ ≤ r) :
    ∃ f : m.primeCompl, ‖(f : C(X, k)) * g‖ ≤ r := by
  let P := m.primeCompl
  let U (f : P) : Set X := ((f : C(X, k)) * g) ⁻¹' closedBall 0 r
  have h_cover (x : X) : ∃ f : P, x ∈ U f := by
    by_cases hx : x ∈ zeroSet m
    · exact ⟨1, by simpa [U] using hg x hx⟩
    · simp only [zeroSet, mem_ofPred_eq, not_forall, not_le] at hx
      obtain ⟨f, hf⟩ := hx
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < r / (‖g x‖ + 1)) hf
      refine ⟨f ^ n, ?_⟩
      simp only [U, mem_preimage, mem_closedBall_zero_iff, ContinuousMap.mul_apply,
        SubmonoidClass.coe_pow, ContinuousMap.coe_pow, Pi.pow_apply, norm_mul, norm_pow]
      calc
        ‖(f : C(X, k)) x‖ ^ n * ‖g x‖ ≤ r / (‖g x‖ + 1) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
        _ ≤ r := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg (g x)]
  have h_mono (e f : P) : U f ⊆ U (e * f) := fun x hx ↦ by
    simp only [U, mem_preimage, mem_closedBall_zero_iff, Submonoid.coe_mul, Subring.coe_mul,
      ContinuousMap.coe_mul, Pi.mul_apply, mul_assoc]
    rw [norm_mul]
    have he : ‖(e : C(X, k)) x‖ ≤ 1 :=
      (norm_coe_le_norm _ x).trans (mem_boundedMultipliers.1 e.val.property).2
    have hfx : ‖(f : C(X, k)) x * g x‖ ≤ r := by simpa [U] using hx
    exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hfx
  have h_open (f : P) : IsOpen (U f) :=
    (IsUltrametricDist.isOpen_closedBall 0 hr.ne').preimage ((f : C(X, k)) * g).continuous
  have h_dir : Directed (· ⊆ ·) U := fun e f ↦
    ⟨e * f, by simpa [mul_comm] using h_mono f e, h_mono e f⟩
  have : Nonempty P := ⟨1⟩
  obtain ⟨f, hf⟩ := isCompact_univ.elim_directed_cover U h_open
    (fun x _ ↦ mem_iUnion.2 (h_cover x)) h_dir
  refine ⟨f, (ContinuousMap.norm_le _ hr.le).2 fun x ↦ ?_⟩
  simpa [U] using hf (mem_univ x)

omit [CompactSpace X] in
private lemma mem_ideal_of_apply_eq_zero {N : Submodule k C(X, k)}
    {m : Ideal (boundedMultipliers N)} [m.IsPrime] {w : boundedMultipliers N}
    {x : X} (hx : x ∈ zeroSet m) (hw : (w : C(X, k)) x = 0) : w ∈ m := by
  by_contra h
  have hnorm := hx ⟨w, h⟩
  rw [hw, norm_zero] at hnorm
  exact not_le_of_gt zero_lt_one hnorm

private lemma eq_on_zeroSet_of_mem_multiplier {N : Submodule k C(X, k)}
    {m : Ideal (boundedMultipliers N)} [m.IsPrime] {u : C(X, k)}
    (hu : u ∈ N.leftOrder) {x a : X} (hx : x ∈ zeroSet m) (ha : a ∈ zeroSet m) :
    u x = u a := by
  let v : C(X, k) := u - ContinuousMap.const X (u a)
  obtain ⟨y, hy, h_max⟩ :=
    (isClosed_zeroSet m).isCompact.exists_isMaxOn ⟨x, hx⟩ v.continuous.norm.continuousOn
  refine eq_of_norm_sub_le_zero ((h_max hx).trans (not_lt.1 fun h_pos ↦ ?_))
  obtain ⟨f, hf⟩ := exists_mul_norm_le_of_le_on_zeroSet (m := m) v h_pos h_max
  have hv_mult : v ∈ N.leftOrder :=
    N.leftOrder.sub_mem hu (N.leftOrder.algebraMap_mem (u a))
  have hw_norm : ‖(v y)⁻¹ • ((f : C(X, k)) * v)‖ ≤ 1 := by
    rw [norm_smul, norm_inv]
    exact (mul_le_mul_of_nonneg_left hf (inv_nonneg.2 (norm_nonneg _))).trans
      (by rw [inv_mul_cancel₀ h_pos.ne'])
  let w : boundedMultipliers N :=
    ⟨(v y)⁻¹ • ((f : C(X, k)) * v),
      mem_boundedMultipliers.2
        ⟨N.leftOrder.smul_mem
          (N.leftOrder.mul_mem (mem_boundedMultipliers.1 f.val.property).1 hv_mult) _, hw_norm⟩⟩
  have hw_mem : w ∈ m := mem_ideal_of_apply_eq_zero ha (by
    simp only [w, v, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.sub_apply, ContinuousMap.const_apply, sub_self, mul_zero, smul_zero])
  have hdiff_mem : f.val - w ∈ m := mem_ideal_of_apply_eq_zero hy (by
    have hvne : v y ≠ 0 := norm_pos_iff.1 h_pos
    simp only [w, AddSubgroupClass.coe_sub, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul]
    rw [mul_comm ((f : C(X, k)) y), ← mul_assoc, inv_mul_cancel₀ hvne, one_mul, sub_self])
  exact f.property ((m.sub_mem_iff_left hw_mem).mp hdiff_mem)

/-- **Ultrametric Stone–Weierstrass theorem for modules (epsilon form).** Let `X` be a compact
space, `k` an ultrametric normed field, `N` a `k`-submodule of `C(X, k)`, and `φ : C(X, k)`. If
for every `a : X` there exists `d ∈ N` agreeing with `φ` on the fiber where all multipliers of `N`
take the same value as at `a`, then `φ` can be approximated arbitrarily closely in supremum norm by
elements of `N`. -/
theorem exists_mem_norm_sub_le_of_eq_on_multiplier_fibers (N : Submodule k C(X, k)) (φ : C(X, k))
    (h_fiber : ∀ a : X, ∃ d ∈ N, ∀ x : X, (∀ u ∈ N.leftOrder, u x = u a) → φ x = d x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ N, ‖φ - g‖ ≤ ε := by
  by_contra! h_far
  obtain ⟨m, hm, h_near⟩ := exists_maximal_ideal_of_far N φ hε.le h_far
  have : m.IsMaximal := hm
  have hd_exists : ∃ d ∈ N, ∀ x ∈ zeroSet m, ‖(φ - d) x‖ ≤ ε := by
    by_cases hZ : (zeroSet m).Nonempty
    · obtain ⟨a, ha⟩ := hZ
      obtain ⟨d, hd, hφd⟩ := h_fiber a
      refine ⟨d, hd, fun x hx ↦ ?_⟩
      have hxa : φ x = d x :=
        hφd x fun u hu ↦ eq_on_zeroSet_of_mem_multiplier (m := m) hu hx ha
      rw [ContinuousMap.sub_apply, hxa, sub_self, norm_zero]
      exact hε.le
    · exact ⟨0, N.zero_mem, fun x hx ↦ (hZ ⟨x, hx⟩).elim⟩
  obtain ⟨d, hd, h_bound⟩ := hd_exists
  obtain ⟨f, hf⟩ := exists_mul_norm_le_of_le_on_zeroSet (m := m) (φ - d) hε h_bound
  have h_near_f : ‖(f : C(X, k)) * φ - (f : C(X, k)) * d‖ ≤ ε := by rwa [← mul_sub]
  exact f.property (h_near f.val ((f : C(X, k)) * d)
    (Submodule.mem_leftOrder_iff.1 (mem_boundedMultipliers.1 f.val.property).1 d hd) h_near_f)

/-- **Ultrametric Stone–Weierstrass theorem for modules (closure form).** If `φ : C(X, k)` agrees
with some element of `N` on every multiplier fiber of `N`, then `φ ∈ N.topologicalClosure`. -/
theorem mem_topologicalClosure_of_eq_on_multiplier_fibers (N : Submodule k C(X, k)) (φ : C(X, k))
    (h_fiber : ∀ a : X, ∃ d ∈ N, ∀ x : X, (∀ u ∈ N.leftOrder, u x = u a) → φ x = d x) :
    φ ∈ N.topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, hle⟩ :=
    exists_mem_norm_sub_le_of_eq_on_multiplier_fibers N φ h_fiber (half_pos hε)
  refine ⟨g, hg, ?_⟩
  rw [dist_eq_norm]
  exact hle.trans_lt (half_lt_self hε)

/-- **Ultrametric Stone–Weierstrass theorem for modules with a subalgebra of multipliers.** If a
subalgebra `A : Subalgebra k C(X, k)` stabilizes `N` and `φ` agrees with some element of `N` on
every fiber of `A`, then `φ ∈ N.topologicalClosure`. -/
theorem mem_topologicalClosure_of_eq_on_subalgebra_fibers (N : Submodule k C(X, k))
    (A : Subalgebra k C(X, k)) (hAN : A ≤ N.leftOrder) (φ : C(X, k))
    (h_fiber : ∀ a : X, ∃ d ∈ N, ∀ x : X, (∀ u ∈ A, u x = u a) → φ x = d x) :
    φ ∈ N.topologicalClosure :=
  mem_topologicalClosure_of_eq_on_multiplier_fibers N φ fun a ↦
    let ⟨d, hd, hφd⟩ := h_fiber a
    ⟨d, hd, fun x hx ↦ hφd x fun u hu ↦ hx u (hAN hu)⟩

/-- **Density of a submodule whose multipliers separate points.** If `N.leftOrder`
separates points of `X` and `N` vanishes nowhere on `X`, then `N` is dense in `C(X, k)`. -/
theorem submodule_topologicalClosure_eq_top_of_separatesPoints_ultrametric (N : Submodule k C(X, k))
    (hsep : N.leftOrder.SeparatesPoints) (hvan : ∀ a : X, ∃ d ∈ N, d a ≠ 0) :
    N.topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  refine mem_topologicalClosure_of_eq_on_multiplier_fibers N φ fun a ↦ ?_
  obtain ⟨d₀, hd₀, hda⟩ := hvan a
  refine ⟨(φ a * (d₀ a)⁻¹) • d₀, N.smul_mem _ hd₀, fun x hx ↦ ?_⟩
  have hxa : x = a := by
    by_contra hne
    obtain ⟨_, ⟨u, hu, rfl⟩, hux⟩ := hsep hne
    exact hux (hx u hu)
  subst hxa
  rw [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hda, mul_one]

/-- **Kaplansky's ultrametric Stone–Weierstrass theorem for subalgebras.** Every point-separating
`k`-subalgebra `A` of `C(X, k)` over an ultrametric normed field `k` is dense in `C(X, k)`. -/
theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints_ultrametric
    (A : Subalgebra k C(X, k)) (hsep : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := by
  have h := submodule_topologicalClosure_eq_top_of_separatesPoints_ultrametric
    (Subalgebra.toSubmodule A) (by rwa [Subalgebra.leftOrder_toSubmodule])
    fun _ ↦ ⟨1, A.one_mem, by simp⟩
  rw [← SetLike.coe_set_eq, Subalgebra.topologicalClosure_coe, Algebra.coe_top]
  simpa [← SetLike.coe_set_eq, Submodule.topologicalClosure_coe] using h

/-- **Kaplansky's ultrametric Stone–Weierstrass theorem (epsilon form).** For a point-separating
subalgebra `A` of `C(X, k)` over an ultrametric normed field `k`, every `φ : C(X, k)` can be
approximated within any `ε > 0` by an element of `A`. -/
theorem exists_mem_subalgebra_norm_sub_lt_of_separatesPoints_ultrametric
    (A : Subalgebra k C(X, k)) (hsep : A.SeparatesPoints) (φ : C(X, k)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ A, ‖φ - g‖ < ε := by
  have hcl : φ ∈ closure (A : Set C(X, k)) := by
    rw [← Subalgebra.topologicalClosure_coe,
      subalgebra_topologicalClosure_eq_top_of_separatesPoints_ultrametric A hsep,
      Algebra.coe_top]
    exact mem_univ φ
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.1 hcl ε hε
  exact ⟨g, hg, by rwa [← dist_eq_norm]⟩

end UltrametricStoneWeierstrass

end ContinuousMap
