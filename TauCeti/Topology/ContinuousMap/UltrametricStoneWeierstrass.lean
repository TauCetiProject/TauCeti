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
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Ultrametric Stone–Weierstrass theorem for modules and subalgebras

Let `X` be a compact topological space and `k` a normed field whose metric is ultrametric
(`IsUltrametricDist k`). Neither completeness of `k`, nontriviality of the norm on `k`,
Hausdorffness of `X`, nor nonemptiness of `X` is required.

For a `k`-submodule `N` of `C(X, k)`, its **multiplier subalgebra**
`ContinuousMap.multiplierSubalgebra N` consists of all `u : C(X, k)` such that `u * d ∈ N` for
every `d ∈ N`. The localization form of the ultrametric Stone–Weierstrass theorem (Kaplansky–Prolla)
states that a continuous map `φ : C(X, k)` lies in the uniform closure `N.topologicalClosure`
whenever, for every `a : X`, there exists `d ∈ N` agreeing with `φ` on the fiber
`{x : X | ∀ u ∈ multiplierSubalgebra N, u x = u a}`
(`ContinuousMap.mem_topologicalClosure_of_eq_on_multiplier_fibers`).

As immediate corollaries we obtain:
* the submodule density theorem when `multiplierSubalgebra N` separates points and `N` vanishes
  nowhere (`ContinuousMap.submodule_topologicalClosure_eq_top_of_separatesPoints`), and
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
-/

public section

open Filter Metric Set Topology

namespace ContinuousMap

section MultiplierSubalgebra

variable {X k : Type*} [TopologicalSpace X] [CommSemiring k] [TopologicalSpace k]
  [IsTopologicalSemiring k]

/-- The **multiplier subalgebra** of a `k`-submodule `N` of `C(X, k)`: the subalgebra of
continuous functions `u : C(X, k)` stabilizing `N` under pointwise multiplication. -/
def multiplierSubalgebra (N : Submodule k C(X, k)) : Subalgebra k C(X, k) where
  carrier := {u | ∀ d ∈ N, u * d ∈ N}
  mul_mem' {u v} hu hv d hd := by
    rw [mul_assoc]
    exact hu _ (hv d hd)
  one_mem' d hd := by simpa using hd
  add_mem' {u v} hu hv d hd := by
    rw [add_mul]
    exact N.add_mem (hu d hd) (hv d hd)
  zero_mem' d _ := by simp
  algebraMap_mem' c d hd := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact N.smul_mem c hd

/-- Membership in `multiplierSubalgebra N` means stabilizing `N` under multiplication. -/
@[simp]
theorem mem_multiplierSubalgebra {N : Submodule k C(X, k)} {u : C(X, k)} :
    u ∈ multiplierSubalgebra N ↔ ∀ d ∈ N, u * d ∈ N :=
  Iff.rfl

end MultiplierSubalgebra

section UltrametricStoneWeierstrass

variable {X k : Type*} [TopologicalSpace X] [CompactSpace X] [NormedField k] [IsUltrametricDist k]

private lemma norm_add_le_max_continuousMap (f g : C(X, k)) :
    ‖f + g‖ ≤ max ‖f‖ ‖g‖ := by
  rw [ContinuousMap.norm_le _ (le_max_of_le_left (norm_nonneg f))]
  intro x
  calc
    ‖(f + g) x‖ = ‖f x + g x‖ := rfl
    _ ≤ max ‖f x‖ ‖g x‖ := IsUltrametricDist.norm_add_le_max (f x) (g x)
    _ ≤ max ‖f‖ ‖g‖ := max_le_max (norm_coe_le_norm f x) (norm_coe_le_norm g x)

/-- The subring of multipliers of `N` with supremum norm at most `1`. -/
private def boundedMultipliers (N : Submodule k C(X, k)) : Subring C(X, k) where
  carrier := {u | u ∈ multiplierSubalgebra N ∧ ‖u‖ ≤ 1}
  mul_mem' {u v} hu hv :=
    ⟨(multiplierSubalgebra N).mul_mem hu.1 hv.1,
      (norm_mul_le u v).trans ((mul_le_of_le_one_left (norm_nonneg v) hu.2).trans hv.2)⟩
  one_mem' :=
    ⟨(multiplierSubalgebra N).one_mem, (ContinuousMap.norm_le _ zero_le_one).2 fun _ ↦ by simp⟩
  add_mem' {u v} hu hv :=
    ⟨(multiplierSubalgebra N).add_mem hu.1 hv.1,
      (norm_add_le_max_continuousMap u v).trans (max_le hu.2 hv.2)⟩
  zero_mem' := ⟨(multiplierSubalgebra N).zero_mem, by simp⟩
  neg_mem' {u} hu := ⟨(multiplierSubalgebra N).neg_mem hu.1, by simpa using hu.2⟩

private lemma exists_maximal_ideal_of_far (N : Submodule k C(X, k)) (φ : C(X, k)) {ε : ℝ}
    (hε : 0 < ε) (h_far : ∀ g ∈ N, ε < ‖φ - g‖) :
    ∃ m : Ideal (boundedMultipliers N), m.IsMaximal ∧
      ∀ w : boundedMultipliers N, ∀ g ∈ N, ‖(w : C(X, k)) * φ - g‖ ≤ ε → w ∈ m := by
  let B := boundedMultipliers N
  let N' : Submodule B C(X, k) :=
    { N.toAddSubmonoid with smul_mem' := fun c _ hd ↦ c.2.1 _ hd }
  let ball : Submodule B C(X, k) :=
    { carrier := {f | ‖f‖ ≤ ε}
      add_mem' := fun {f g} hf hg ↦ (norm_add_le_max_continuousMap f g).trans (max_le hf hg)
      zero_mem' := by simpa using hε.le
      smul_mem' := fun c f hf ↦ by
        change ‖(c : C(X, k)) * f‖ ≤ ε
        exact (norm_mul_le (c : C(X, k)) f).trans
          ((mul_le_of_le_one_left (norm_nonneg f) c.2.2).trans hf) }
  let I : Ideal B := (N' ⊔ ball).comap (LinearMap.toSpanSingleton B C(X, k) φ)
  have hI_ne_top : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : B) ∈ I := htop.symm ▸ Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul, Submodule.mem_sup] at h1
    rcases h1 with ⟨g, hg, r, hr, hgr⟩
    have hsub : φ - g = r := sub_eq_of_eq_add' hgr.symm
    exact (h_far g hg).not_ge (hsub ▸ hr)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI_ne_top
  refine ⟨m, hm, fun w g hg hle ↦ hIm ?_⟩
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_sup]
  exact ⟨g, hg, (w : C(X, k)) * φ - g, hle, add_sub_cancel g ((w : C(X, k)) * φ)⟩

private lemma exists_mul_norm_le_of_le_on_zeroSet {N : Submodule k C(X, k)}
    {m : Ideal (boundedMultipliers N)} [m.IsPrime] (g : C(X, k)) {r : ℝ} (hr : 0 < r)
    (hg : ∀ x : X, (∀ f : m.primeCompl, 1 ≤ ‖(f : C(X, k)) x‖) → ‖g x‖ ≤ r) :
    ∃ f : m.primeCompl, ‖(f : C(X, k)) * g‖ ≤ r := by
  let P := m.primeCompl
  let U (f : P) : Set X := ((f : C(X, k)) * g) ⁻¹' closedBall 0 r
  have h_cover (x : X) : ∃ f : P, x ∈ U f := by
    by_cases hx : ∀ f : P, 1 ≤ ‖(f : C(X, k)) x‖
    · exact ⟨1, by simpa [U] using hg x hx⟩
    · push Not at hx
      obtain ⟨f, hf⟩ := hx
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < r / (‖g x‖ + 1) by positivity) hf
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
    have he : ‖(e : C(X, k)) x‖ ≤ 1 := (norm_coe_le_norm (e : C(X, k)) x).trans e.1.2.2
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

private lemma eq_on_zeroSet_of_mem_multiplier {N : Submodule k C(X, k)}
    {m : Ideal (boundedMultipliers N)} [m.IsMaximal] {u : C(X, k)}
    (hu : u ∈ multiplierSubalgebra N) {x a : X}
    (hx : ∀ f : m.primeCompl, 1 ≤ ‖(f : C(X, k)) x‖)
    (ha : ∀ f : m.primeCompl, 1 ≤ ‖(f : C(X, k)) a‖) :
    u x = u a := by
  let Z : Set X := {y | ∀ f : m.primeCompl, 1 ≤ ‖(f : C(X, k)) y‖}
  let v : C(X, k) := u - ContinuousMap.const X (u a)
  have hZ_closed : IsClosed Z := by
    have hZ_eq : Z = ⋂ f : m.primeCompl, {y | (1 : ℝ) ≤ ‖(f : C(X, k)) y‖} := by
      ext y
      simp [Z]
    rw [hZ_eq]
    exact isClosed_iInter fun f : m.primeCompl ↦
      isClosed_le continuous_const (f : C(X, k)).continuous.norm
  obtain ⟨y, hy, h_max⟩ := hZ_closed.isCompact.exists_isMaxOn ⟨x, hx⟩ v.continuous.norm.continuousOn
  refine eq_of_norm_sub_le_zero ((h_max hx).trans (not_lt.1 fun h_pos ↦ ?_))
  obtain ⟨f, hf⟩ := exists_mul_norm_le_of_le_on_zeroSet (m := m) v h_pos h_max
  have hv_mult : v ∈ multiplierSubalgebra N :=
    (multiplierSubalgebra N).sub_mem hu ((multiplierSubalgebra N).algebraMap_mem (u a))
  have hw_norm : ‖(v y)⁻¹ • ((f : C(X, k)) * v)‖ ≤ 1 := by
    rw [norm_smul, norm_inv]
    exact (mul_le_mul_of_nonneg_left hf (inv_nonneg.2 (norm_nonneg _))).trans
      (by rw [inv_mul_cancel₀ h_pos.ne'])
  let w : boundedMultipliers N :=
    ⟨(v y)⁻¹ • ((f : C(X, k)) * v),
      (multiplierSubalgebra N).smul_mem ((multiplierSubalgebra N).mul_mem f.1.2.1 hv_mult) _,
      hw_norm⟩
  have hw_mem : w ∈ m := by
    by_contra hw
    have h1 := ha ⟨w, hw⟩
    simp [w, v] at h1
    linarith
  have hdiff_mem : f.1 - w ∈ m := by
    by_contra hdw
    have h1 := hy ⟨f.1 - w, hdw⟩
    have hvne : v y ≠ 0 := norm_pos_iff.1 h_pos
    have hval : ((f.1 - w : boundedMultipliers N) : C(X, k)) y = 0 := by
      change (f : C(X, k)) y - (v y)⁻¹ * ((f : C(X, k)) y * v y) = 0
      rw [mul_comm ((f : C(X, k)) y), ← mul_assoc, inv_mul_cancel₀ hvne, one_mul, sub_self]
    rw [hval, norm_zero] at h1
    linarith
  exact f.2 ((m.sub_mem_iff_left hw_mem).mp hdiff_mem)

/-- **Ultrametric Stone–Weierstrass theorem for modules (epsilon form).** Let `X` be a compact
space, `k` an ultrametric normed field, `N` a `k`-submodule of `C(X, k)`, and `φ : C(X, k)`. If
for every `a : X` there exists `d ∈ N` agreeing with `φ` on the fiber where all multipliers of `N`
take the same value as at `a`, then `φ` can be approximated arbitrarily closely in supremum norm by
elements of `N`. -/
theorem exists_mem_norm_sub_le_of_eq_on_multiplier_fibers (N : Submodule k C(X, k)) (φ : C(X, k))
    (h_fiber : ∀ a : X, ∃ d ∈ N, ∀ x : X, (∀ u ∈ multiplierSubalgebra N, u x = u a) → φ x = d x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ N, ‖φ - g‖ ≤ ε := by
  by_contra! h_far
  obtain ⟨m, hm, h_near⟩ := exists_maximal_ideal_of_far N φ hε h_far
  have : m.IsMaximal := hm
  let Z : Set X := {x | ∀ f : m.primeCompl, 1 ≤ ‖(f : C(X, k)) x‖}
  have hd_exists : ∃ d ∈ N, ∀ x ∈ Z, ‖(φ - d) x‖ ≤ ε := by
    by_cases hZ : Z.Nonempty
    · obtain ⟨a, ha⟩ := hZ
      obtain ⟨d, hd, hφd⟩ := h_fiber a
      refine ⟨d, hd, fun x hx ↦ ?_⟩
      have hxa : φ x = d x :=
        hφd x fun u hu ↦ eq_on_zeroSet_of_mem_multiplier (m := m) hu hx ha
      change ‖φ x - d x‖ ≤ ε
      rw [hxa, sub_self, norm_zero]
      exact hε.le
    · exact ⟨0, N.zero_mem, fun x hx ↦ (hZ ⟨x, hx⟩).elim⟩
  obtain ⟨d, hd, h_bound⟩ := hd_exists
  obtain ⟨f, hf⟩ := exists_mul_norm_le_of_le_on_zeroSet (m := m) (φ - d) hε h_bound
  have h_near_f : ‖(f : C(X, k)) * φ - (f : C(X, k)) * d‖ ≤ ε := by rwa [← mul_sub]
  exact f.2 (h_near f.1 ((f : C(X, k)) * d) (f.1.2.1 d hd) h_near_f)

/-- **Ultrametric Stone–Weierstrass theorem for modules (closure form).** If `φ : C(X, k)` agrees
with some element of `N` on every multiplier fiber of `N`, then `φ ∈ N.topologicalClosure`. -/
theorem mem_topologicalClosure_of_eq_on_multiplier_fibers (N : Submodule k C(X, k)) (φ : C(X, k))
    (h_fiber : ∀ a : X, ∃ d ∈ N, ∀ x : X, (∀ u ∈ multiplierSubalgebra N, u x = u a) → φ x = d x) :
    φ ∈ N.topologicalClosure := by
  change φ ∈ closure (N : Set C(X, k))
  rw [Metric.mem_closure_iff]
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
    (A : Subalgebra k C(X, k)) (hAN : ∀ u ∈ A, ∀ d ∈ N, u * d ∈ N) (φ : C(X, k))
    (h_fiber : ∀ a : X, ∃ d ∈ N, ∀ x : X, (∀ u ∈ A, u x = u a) → φ x = d x) :
    φ ∈ N.topologicalClosure :=
  mem_topologicalClosure_of_eq_on_multiplier_fibers N φ fun a ↦
    let ⟨d, hd, hφd⟩ := h_fiber a
    ⟨d, hd, fun x hx ↦ hφd x fun u hu ↦ hx u (hAN u hu)⟩

/-- **Density of a submodule whose multipliers separate points.** If `multiplierSubalgebra N`
separates points of `X` and `N` vanishes nowhere on `X`, then `N` is dense in `C(X, k)`. -/
theorem submodule_topologicalClosure_eq_top_of_separatesPoints (N : Submodule k C(X, k))
    (hsep : (multiplierSubalgebra N).SeparatesPoints) (hvan : ∀ a : X, ∃ d ∈ N, d a ≠ 0) :
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
  change φ x = φ x * (d₀ x)⁻¹ * d₀ x
  rw [mul_assoc, inv_mul_cancel₀ hda, mul_one]

/-- **Kaplansky's ultrametric Stone–Weierstrass theorem for subalgebras.** Every point-separating
`k`-subalgebra `A` of `C(X, k)` over an ultrametric normed field `k` is dense in `C(X, k)`. -/
theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints_ultrametric
    (A : Subalgebra k C(X, k)) (hsep : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  change φ ∈ (Subalgebra.toSubmodule A).topologicalClosure
  refine mem_topologicalClosure_of_eq_on_subalgebra_fibers (Subalgebra.toSubmodule A) A
    (fun u hu d hd ↦ A.mul_mem hu hd) φ fun a ↦ ?_
  refine ⟨algebraMap k C(X, k) (φ a), A.algebraMap_mem (φ a), fun x hx ↦ ?_⟩
  have hxa : x = a := by
    by_contra hne
    obtain ⟨_, ⟨u, hu, rfl⟩, hux⟩ := hsep hne
    exact hux (hx u hu)
  subst hxa
  simp

/-- **Kaplansky's ultrametric Stone–Weierstrass theorem (epsilon form).** For a point-separating
subalgebra `A` of `C(X, k)` over an ultrametric normed field `k`, every `φ : C(X, k)` can be
approximated within any `ε > 0` by an element of `A`. -/
theorem exists_mem_subalgebra_norm_sub_lt_of_separatesPoints_ultrametric
    (A : Subalgebra k C(X, k)) (hsep : A.SeparatesPoints) (φ : C(X, k)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ A, ‖φ - g‖ < ε := by
  have hcl : φ ∈ closure (A : Set C(X, k)) := by
    have htop := subalgebra_topologicalClosure_eq_top_of_separatesPoints_ultrametric A hsep
    have hmem : φ ∈ A.topologicalClosure := by
      rw [htop]
      trivial
    exact hmem
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.1 hcl ε hε
  exact ⟨g, hg, by rwa [← dist_eq_norm]⟩

end UltrametricStoneWeierstrass

end ContinuousMap
