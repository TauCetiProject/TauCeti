/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Diagonal
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Eigenbasis
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralCutoff
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.InvSqrtAdd

/-!
# Functional calculus and the bounded transform for compact resolvent

Let `A` be a self-adjoint partial linear map with compact resolvent on a complex Hilbert space `H`.
By `IsSelfAdjoint.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent`, `A` admits a
Hilbert basis `b` of eigenvectors with real eigenvalues `λᵢ` whose absolute values satisfy the
Northcott property (`LinearPMap.HasCompactResolvent.northcott_norm_of_orthonormal`). Consequently
the index type is countable and `H` is automatically separable
(`IsSelfAdjoint.separableSpace_of_hasCompactResolvent`). Conversely, a real diagonal operator
`b.diagonalPMap λ` has compact resolvent if and only if `|λᵢ|` is Northcott
(`HilbertBasis.hasCompactResolvent_diagonalPMap_iff`).

Because `b.diagonalPMap (f ∘ λ)` is independent of the choice of eigenbasis
(`LinearPMap.IsFormalAdjoint.diagonalPMap_eq_diagonalPMap`), any function `f : ℝ → ℂ` defines a
closed partial operator `A.eigenCalculus hA h f`, and any bounded `f : ℝ → ℂ` defines a bounded
operator `A.boundedEigenCalculus hA h f hf`. This bounded functional calculus is a unital
`*`-homomorphism in `f`, respects unitary conjugation, sends functions vanishing at infinity to
compact operators, and turns anticommutation with `A` into commutation (for even `f`) or
anticommutation (for odd `f`).

Taking `f(t) = t / √(1 + t²)` yields the **bounded transform** (or Woronowicz–Baaj–Julg transform)
`F_A = A.boundedTransform hA h`, formally `A (1 + A²)⁻¹/²`. It is a self-adjoint contraction with
`1 - F_A² = (1 + A²)⁻¹` compact. Whenever a bounded operator `T` preserves the domain of `A` and
has bounded commutator `[A, T] = C` on `D(A)`, the Baaj–Julg integral identity expresses `[F_A, T]`
as a norm-convergent Bochner integral of compact operators over `(0, ∞)`, proving that `[F_A, T]`
is compact (`LinearPMap.isCompactOperator_commutator_boundedTransform`) with operator norm bound
`‖[F_A, T]‖ ≤ (5 / 4) ‖C‖` (`LinearPMap.norm_commutator_boundedTransform_le`).

## Main definitions

* `LinearPMap.eigenCalculus`: the unbounded eigenbasis functional calculus `f(A)`.
* `LinearPMap.boundedEigenCalculus`: the bounded eigenbasis functional calculus `f(A)` for bounded
  `f : ℝ → ℂ`.
* `LinearPMap.boundedTransform`: the bounded transform `F_A = A (1 + A²)⁻¹/²`.

## Main results

* `HilbertBasis.hasCompactResolvent_diagonalPMap_iff`: a real diagonal operator has compact
  resolvent iff `|λᵢ|` is Northcott (Reed–Simon XIII.64).
* `IsSelfAdjoint.separableSpace_of_hasCompactResolvent`: a complex Hilbert space admitting a
  self-adjoint operator with compact resolvent is separable.
* `LinearPMap.boundedEigenCalculus_eq_diagonal`,
  `LinearPMap.isCompactOperator_boundedEigenCalculus`,
  `LinearPMap.boundedEigenCalculus_unitaryConj`,
  `LinearPMap.mul_boundedEigenCalculus_of_anticommute`: key properties of the bounded functional
  calculus.
* `LinearPMap.isSelfAdjoint_boundedTransform`, `LinearPMap.norm_boundedTransform_le_one`,
  `LinearPMap.one_sub_boundedTransform_mul_self`,
  `LinearPMap.isCompactOperator_boundedTransform_mul_self_sub_one`: basic properties of `F_A`.
* `LinearPMap.isCompactOperator_commutator_boundedTransform`,
  `LinearPMap.norm_commutator_boundedTransform_le`: the Baaj–Julg commutator theorem.

## References

* S. Baaj and P. Julg, *Théorie bivariante de Kasparov et opérateurs non bornés dans les
  C*-modules hilbertiens*, C. R. Acad. Sci. Paris Sér. I Math. 296 (1983), 875–878.
* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §2.
* N. Higson and J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), Chapter 10.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProductSpace lp

/-! ### Compact resolvent for diagonal operators and automatic separability -/

section DiagonalCriterion

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Reed–Simon criterion for diagonal operators.** A diagonal partial linear map with real
entries `lam : ι → ℝ` in a Hilbert basis has compact resolvent if and only if `i ↦ |lam i|` is
Northcott (only finitely many entries lie in any bounded interval). -/
theorem HilbertBasis.hasCompactResolvent_diagonalPMap_iff (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) :
    (b.diagonalPMap fun i ↦ (lam i : ℂ)).HasCompactResolvent ↔ Northcott fun i ↦ |lam i| := by
  set A := b.diagonalPMap fun i ↦ (lam i : ℂ)
  have hA : IsSelfAdjoint A := b.isSelfAdjoint_diagonalPMap (by ext i; simp)
  have hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i := fun i ↦
    ⟨b.self_mem_diagonalPMap_domain _ i, b.diagonalPMap_apply_self _ i⟩
  constructor
  · intro h
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      h.northcott_norm_of_orthonormal b.orthonormal hb
  · intro hN
    rw [hA.hasCompactResolvent_iff_isCompactOperator_resolvent (z := Complex.I) (by simp)]
    have hnorm (i : ι) : 1 ≤ ‖Complex.I - (lam i : ℂ)‖ := by
      simpa using Complex.abs_im_le_norm (Complex.I - (lam i : ℂ))
    let m : ℓ^∞(ι, ℂ) := ⟨fun i ↦ (Complex.I - (lam i : ℂ))⁻¹, memℓp_infty ⟨1, by
      rintro _ ⟨i, rfl⟩
      dsimp only
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (hnorm i)⟩⟩
    have hR : A.resolvent Complex.I = b.diagonal m := by
      refine b.ext_inner_apply b fun i j ↦ ?_
      rw [LinearPMap.resolvent_apply_of_apply_eq_smul hA.I_mem_resolventSet
        ⟨b j, (hb j).1⟩ (hb j).2, b.diagonal_apply_self]
    rw [hR, b.isCompactOperator_diagonal_iff, tendsto_zero_iff_norm_tendsto_zero,
      Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_cofinite]
    refine (hN.finite_le ε⁻¹).subset fun i hi ↦ ?_
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _),
      not_lt] at hi
    have hne : Complex.I - (lam i : ℂ) ≠ 0 := by
      intro h0
      have := hnorm i
      rw [h0, norm_zero] at this
      linarith
    have hre : |lam i| ≤ ‖Complex.I - (lam i : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (Complex.I - (lam i : ℂ))
    have hinv : ‖Complex.I - (lam i : ℂ)‖ ≤ ε⁻¹ := by
      change ε ≤ ‖(Complex.I - (lam i : ℂ))⁻¹‖ at hi
      rw [norm_inv] at hi
      exact (le_inv_comm₀ hε (norm_pos_iff.2 hne)).1 hi
    exact hre.trans hinv

end DiagonalCriterion

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- A complex Hilbert space carrying a self-adjoint operator with compact resolvent is
automatically separable: the eigenbasis index type is a countable union of finite sublevel sets
of `|λᵢ|`. -/
theorem _root_.IsSelfAdjoint.separableSpace_of_hasCompactResolvent (hA : IsSelfAdjoint A)
    (h : A.HasCompactResolvent) : TopologicalSpace.SeparableSpace H := by
  obtain ⟨κ, b, lam, hb⟩ := hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h
  have hN : Northcott fun k ↦ |lam k| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      h.northcott_norm_of_orthonormal b.orthonormal hb
  have : Countable κ := by
    rw [← Set.countable_univ_iff]
    have huniv : (Set.univ : Set κ) = ⋃ n : ℕ, {k | |lam k| ≤ (n : ℝ)} := by
      ext k
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact exists_nat_ge |lam k|
    rw [huniv]
    exact Set.countable_iUnion fun n ↦ (hN.finite_le (n : ℝ)).countable
  exact b.separableSpace

/-! ### Eigenbasis functional calculus -/

section EigenCalculus

variable (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

private def chosenIndex (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) : Type :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h).choose

private def chosenBasis (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    HilbertBasis (chosenIndex hA h) ℂ H :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h).choose_spec.choose

private def chosenEigval (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    chosenIndex hA h → ℝ :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent
    h).choose_spec.choose_spec.choose

private theorem chosenBasis_spec (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (k : chosenIndex hA h) :
    ∃ hk : chosenBasis hA h k ∈ A.domain,
      A ⟨chosenBasis hA h k, hk⟩ = (chosenEigval hA h k : ℂ) • chosenBasis hA h k :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent
    h).choose_spec.choose_spec.choose_spec k

/-- **Unbounded eigenbasis functional calculus.** For a self-adjoint operator `A` with compact
resolvent and any function `f : ℝ → ℂ`, `A.eigenCalculus hA h f` is the diagonal partial linear
map acting by multiplication by `f (λᵢ)` in any orthonormal eigenbasis of `A`. It does not depend
on the choice of eigenbasis (`LinearPMap.eigenCalculus_eq_diagonalPMap`). -/
def eigenCalculus (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (f : ℝ → ℂ) : H →ₗ.[ℂ] H :=
  (chosenBasis hA h).diagonalPMap fun k ↦ f (chosenEigval hA h k)

/-- Characterization of `eigenCalculus` in any orthonormal eigenbasis of `A`. -/
theorem eigenCalculus_eq_diagonalPMap {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i) (f : ℝ → ℂ) :
    A.eigenCalculus hA h f = b.diagonalPMap fun i ↦ f (lam i) :=
  hA.isFormalAdjoint.diagonalPMap_eq_diagonalPMap (chosenBasis_spec hA h) hb f

/-- Applying the eigenbasis functional calculus to the identity function recovers `A`. -/
@[simp]
theorem eigenCalculus_id : A.eigenCalculus hA h (fun t ↦ (t : ℂ)) = A :=
  (hA.eq_diagonalPMap (chosenBasis_spec hA h)).symm

/-- Every operator in the eigenbasis functional calculus is closed. -/
theorem isClosed_eigenCalculus (f : ℝ → ℂ) : (A.eigenCalculus hA h f).IsClosed :=
  (chosenBasis hA h).isClosed_diagonalPMap _

/-- The adjoint of `f(A)` is `(star f)(A)`. -/
@[simp]
theorem adjoint_eigenCalculus (f : ℝ → ℂ) :
    (A.eigenCalculus hA h f)† = A.eigenCalculus hA h (star f) :=
  (chosenBasis hA h).adjoint_diagonalPMap _

/-- A real-valued function of `A` is self-adjoint. -/
theorem isSelfAdjoint_eigenCalculus {f : ℝ → ℂ} (hf : ∀ t, star (f t) = f t) :
    IsSelfAdjoint (A.eigenCalculus hA h f) :=
  (chosenBasis hA h).isSelfAdjoint_diagonalPMap (funext fun _ ↦ hf _)

/-- On an eigenvector of `A` with real eigenvalue `r`, `f(A)` is defined and acts as scalar
multiplication by `f r`. -/
theorem eigenCalculus_apply_of_apply_eq_smul (f : ℝ → ℂ) (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) :
    ∃ hmem : (x : H) ∈ (A.eigenCalculus hA h f).domain,
      A.eigenCalculus hA h f ⟨x, hmem⟩ = f r • (x : H) := by
  have hgraph : ((x : H), f r • (x : H)) ∈ (A.eigenCalculus hA h f).graph := by
    rw [eigenCalculus, HilbertBasis.mem_graph_diagonalPMap_iff]
    intro k
    rw [inner_smul_right]
    by_cases hkr : chosenEigval hA h k = r
    · rw [hkr]
    · obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
      have horth := hA.isFormalAdjoint.inner_eq_zero_of_apply_eq_smul
        (x := ⟨chosenBasis hA h k, hk⟩) (y := x) hAk hx (Complex.ofReal_injective.ne hkr)
      simp [horth]
  obtain ⟨u, hu, hfu⟩ := (mem_graph_iff _).1 hgraph
  dsimp only at hu hfu
  have hmem : (x : H) ∈ (A.eigenCalculus hA h f).domain := hu ▸ u.2
  refine ⟨hmem, ?_⟩
  have hu' : u = ⟨x, hmem⟩ := Subtype.ext hu
  rwa [← hu']

private def boundedFamily {ι : Type*} (lam : ι → ℝ) (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    ℓ^∞(ι, ℂ) :=
  ⟨fun i ↦ f (lam i), memℓp_infty <| by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC (lam i)⟩⟩

/-- **Bounded eigenbasis functional calculus.** For a self-adjoint operator `A` with compact
resolvent and a bounded function `f : ℝ → ℂ`, `A.boundedEigenCalculus hA h f hf` is the bounded
diagonal operator acting by multiplication by `f (λᵢ)` in any orthonormal eigenbasis of `A`. -/
def boundedEigenCalculus (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) : H →L[ℂ] H :=
  (chosenBasis hA h).diagonal (boundedFamily (chosenEigval hA h) f hf)

/-- Viewed as an everywhere-defined partial linear map, `boundedEigenCalculus` coincides with
`eigenCalculus`. -/
theorem boundedEigenCalculus_toPMap (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    ((A.boundedEigenCalculus hA h f hf : H →ₗ[ℂ] H).toPMap ⊤) = A.eigenCalculus hA h f :=
  ((chosenBasis hA h).diagonalPMap_eq_toPMap _).symm

/-- Characterization of `boundedEigenCalculus` in any orthonormal eigenbasis of `A`. -/
theorem boundedEigenCalculus_eq_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (m : ℓ^∞(ι, ℂ)) (hm : ∀ i, m i = f (lam i)) :
    A.boundedEigenCalculus hA h f hf = b.diagonal m := by
  have hPMap : ((A.boundedEigenCalculus hA h f hf : H →ₗ[ℂ] H).toPMap ⊤) =
      ((b.diagonal m : H →ₗ[ℂ] H).toPMap ⊤) := by
    rw [boundedEigenCalculus_toPMap, eigenCalculus_eq_diagonalPMap hA h b hb f,
      ← b.diagonalPMap_eq_toPMap m]
    congr 1
    exact funext fun i ↦ (hm i).symm
  ext x
  have hEq := (LinearPMap.ext_iff.1 hPMap).2
  exact @hEq x Submodule.mem_top Submodule.mem_top

/-- `boundedEigenCalculus` depends only on the function `f`. -/
theorem boundedEigenCalculus_congr {f g : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hg : ∃ C, ∀ t, ‖g t‖ ≤ C) (hfg : ∀ t, f t = g t) :
    A.boundedEigenCalculus hA h f hf = A.boundedEigenCalculus hA h g hg := by
  rw [boundedEigenCalculus, boundedEigenCalculus]
  congr 1
  ext k
  exact hfg _

/-- On an eigenvector of `A` with real eigenvalue `r`, `boundedEigenCalculus` acts as scalar
multiplication by `f r`. -/
theorem boundedEigenCalculus_apply_of_apply_eq_smul {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (x : A.domain) {r : ℝ} (hx : A x = (r : ℂ) • (x : H)) :
    A.boundedEigenCalculus hA h f hf x = f r • (x : H) := by
  obtain ⟨hmem, hfx⟩ := A.eigenCalculus_apply_of_apply_eq_smul hA h f x hx
  have hgraph : ((x : H), f r • (x : H)) ∈
      ((A.boundedEigenCalculus hA h f hf : H →ₗ[ℂ] H).toPMap ⊤).graph := by
    rw [A.boundedEigenCalculus_toPMap hA h f hf, ← hfx]
    exact (A.eigenCalculus hA h f).mem_graph ⟨x, hmem⟩
  obtain ⟨u, hu, hfu⟩ := (mem_graph_iff _).1 hgraph
  dsimp only at hu hfu
  rw [← hfu, ← hu]
  rfl

/-- `0(A) = 0`. -/
@[simp]
theorem boundedEigenCalculus_zero (h0 : ∃ C, ∀ _ : ℝ, ‖(0 : ℂ)‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun _ ↦ 0) h0 = 0 := by
  rw [boundedEigenCalculus_eq_diagonal hA h (chosenBasis hA h) (chosenBasis_spec hA h) _ _ 0
    (fun _ ↦ rfl), _root_.map_zero]

/-- `1(A) = 1`. -/
@[simp]
theorem boundedEigenCalculus_one (h1 : ∃ C, ∀ _ : ℝ, ‖(1 : ℂ)‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun _ ↦ 1) h1 = 1 := by
  rw [boundedEigenCalculus_eq_diagonal hA h (chosenBasis hA h) (chosenBasis_spec hA h) _ _ 1
    (fun _ ↦ rfl), _root_.map_one]

/-- `(f + g)(A) = f(A) + g(A)`. -/
theorem boundedEigenCalculus_add {f g : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hg : ∃ C, ∀ t, ‖g t‖ ≤ C) (hfg : ∃ C, ∀ t, ‖f t + g t‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ f t + g t) hfg =
      A.boundedEigenCalculus hA h f hf + A.boundedEigenCalculus hA h g hg := by
  rw [boundedEigenCalculus, boundedEigenCalculus, boundedEigenCalculus, ← _root_.map_add]
  congr 1

/-- `(c • f)(A) = c • f(A)`. -/
theorem boundedEigenCalculus_smul (c : ℂ) {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hcf : ∃ C, ∀ t, ‖c * f t‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ c * f t) hcf =
      c • A.boundedEigenCalculus hA h f hf := by
  rw [boundedEigenCalculus, boundedEigenCalculus, ← _root_.map_smul]
  congr 1

/-- `(f * g)(A) = f(A) * g(A)`. -/
theorem boundedEigenCalculus_mul {f g : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hg : ∃ C, ∀ t, ‖g t‖ ≤ C) (hfg : ∃ C, ∀ t, ‖f t * g t‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ f t * g t) hfg =
      A.boundedEigenCalculus hA h f hf * A.boundedEigenCalculus hA h g hg := by
  rw [boundedEigenCalculus, boundedEigenCalculus, boundedEigenCalculus, ← _root_.map_mul]
  congr 1

/-- `star (f(A)) = (star f)(A)`. -/
theorem star_boundedEigenCalculus {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hfs : ∃ C, ∀ t, ‖star (f t)‖ ≤ C) :
    star (A.boundedEigenCalculus hA h f hf) =
      A.boundedEigenCalculus hA h (fun t ↦ star (f t)) hfs := by
  rw [boundedEigenCalculus, boundedEigenCalculus, HilbertBasis.star_diagonal]
  congr 1

/-- A bounded real-valued function of `A` is a self-adjoint bounded operator. -/
theorem isSelfAdjoint_boundedEigenCalculus {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hreal : ∀ t, star (f t) = f t) : IsSelfAdjoint (A.boundedEigenCalculus hA h f hf) := by
  refine (chosenBasis hA h).isSelfAdjoint_diagonal ?_
  ext k
  exact hreal _

/-- Operator norm bound: if `‖f t‖ ≤ C` for all `t` with `0 ≤ C`, then `‖f(A)‖ ≤ C`. -/
theorem norm_boundedEigenCalculus_le {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) {C : ℝ}
    (hC₀ : 0 ≤ C) (hC : ∀ t, ‖f t‖ ≤ C) : ‖A.boundedEigenCalculus hA h f hf‖ ≤ C := by
  rw [boundedEigenCalculus, HilbertBasis.norm_diagonal]
  exact lp.norm_le_of_forall_le hC₀ fun k ↦ hC _

/-- If `f : ℝ → ℂ` vanishes at infinity (`cocompact ℝ`), then `f(A)` is a compact operator. -/
theorem isCompactOperator_boundedEigenCalculus {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hlim : Tendsto f (cocompact ℝ) (𝓝 0)) :
    IsCompactOperator (A.boundedEigenCalculus hA h f hf) := by
  rw [boundedEigenCalculus, HilbertBasis.isCompactOperator_diagonal_iff]
  have hN : Northcott fun k ↦ |chosenEigval hA h k| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      h.northcott_norm_of_orthonormal (chosenBasis hA h).orthonormal (chosenBasis_spec hA h)
  have htend : Tendsto (chosenEigval hA h) cofinite (cocompact ℝ) := by
    rw [Filter.hasBasis_cocompact.tendsto_right_iff]
    intro s hs
    rw [Filter.eventually_cofinite]
    obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall (0 : ℝ)
    refine (hN.finite_le R).subset fun k hk ↦ ?_
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_not] at hk
    have hk' := hR hk
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hk'
    exact hk'
  exact hlim.comp htend

/-- The bounded functional calculus applied to `t ↦ (1 + t²)⁻¹` equals `A.invOneAddSq`. -/
theorem boundedEigenCalculus_invOneAddSq
    (hf : ∃ C, ∀ t : ℝ, ‖(((1 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ (((1 + t ^ 2)⁻¹ : ℝ) : ℂ)) hf = A.invOneAddSq := by
  refine (chosenBasis hA h).ext_inner_apply (chosenBasis hA h) fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hj⟩ hAj,
    invOneAddSq_apply_of_apply_eq_smul hA.I_mem_resolventSet hA.neg_I_mem_resolventSet ⟨_, hj⟩ hAj]
  push_cast
  rfl

/-- Unitary conjugation commutes with the bounded eigenbasis functional calculus. -/
theorem boundedEigenCalculus_unitaryConj {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') (f : ℝ → ℂ)
    (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    (unitaryConj U A).boundedEigenCalculus (isSelfAdjoint_unitaryConj hA)
      ((hasCompactResolvent_unitaryConj_iff U).2 h) f hf =
      U.conjStarAlgEquiv (A.boundedEigenCalculus hA h f hf) := by
  set b := chosenBasis hA h
  set lam := chosenEigval hA h
  have hb' : ∀ k, ∃ hk : b.mapₗᵢ U k ∈ (unitaryConj U A).domain,
      unitaryConj U A ⟨b.mapₗᵢ U k, hk⟩ = (lam k : ℂ) • b.mapₗᵢ U k := fun k ↦ by
    obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
    refine ⟨by rw [HilbertBasis.mapₗᵢ_apply]; exact map_mem_unitaryConj_domain U A ⟨b k, hk⟩, ?_⟩
    simp only [HilbertBasis.mapₗᵢ_apply]
    rw [unitaryConj_apply_map U A ⟨b k, hk⟩, hAk, _root_.map_smul]
  refine (b.mapₗᵢ U).ext_inner_apply (b.mapₗᵢ U) fun i j ↦ ?_
  obtain ⟨hj', hAj'⟩ := hb' j
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  rw [boundedEigenCalculus_apply_of_apply_eq_smul _ _ hf ⟨_, hj'⟩ hAj',
    LinearIsometryEquiv.conjStarAlgEquiv_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, HilbertBasis.mapₗᵢ_apply]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    HilbertBasis.mapₗᵢ_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨b j, hj⟩ hAj, _root_.map_smul]

/-- **Anticommutation with odd functions.** If a bounded operator `γ` preserves the domain of `A`
and anticommutes with `A` on `D(A)`, then `γ` anticommutes with `f(A)` for every bounded odd
function `f`. -/
theorem mul_boundedEigenCalculus_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.2⟩)
    {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (hodd : ∀ t, f (-t) = -f t) :
    γ * A.boundedEigenCalculus hA h f hf = -(A.boundedEigenCalculus hA h f hf * γ) := by
  set b := chosenBasis hA h
  refine b.ext_inner_apply b fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  have hγeig : A ⟨γ (b j), hγdom (b j) hj⟩ = ((-chosenEigval hA h j : ℝ) : ℂ) • γ (b j) := by
    have h1 := hγA ⟨b j, hj⟩
    rw [hAj, _root_.map_smul] at h1
    rw [← neg_neg (A ⟨γ (b j), hγdom (b j) hj⟩), ← h1]
    simp only [Complex.ofReal_neg, neg_smul]
    rfl
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, _root_.neg_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨b j, hj⟩ hAj,
    boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨γ (b j), hγdom (b j) hj⟩ hγeig,
    hodd, _root_.map_smul, neg_smul, neg_neg]

/-- **Commutation with even functions.** If a bounded operator `γ` preserves the domain of `A` and
anticommutes with `A` on `D(A)`, then `γ` commutes with `f(A)` for every bounded even function
`f`. -/
theorem commute_boundedEigenCalculus_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.2⟩)
    {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (heven : ∀ t, f (-t) = f t) :
    Commute γ (A.boundedEigenCalculus hA h f hf) := by
  set b := chosenBasis hA h
  refine b.ext_inner_apply b fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  have hγeig : A ⟨γ (b j), hγdom (b j) hj⟩ = ((-chosenEigval hA h j : ℝ) : ℂ) • γ (b j) := by
    have h1 := hγA ⟨b j, hj⟩
    rw [hAj, _root_.map_smul] at h1
    rw [← neg_neg (A ⟨γ (b j), hγdom (b j) hj⟩), ← h1]
    simp only [Complex.ofReal_neg, neg_smul]
    rfl
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨b j, hj⟩ hAj,
    boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨γ (b j), hγdom (b j) hj⟩ hγeig,
    heven, _root_.map_smul]

end EigenCalculus

/-! ### The bounded transform `A (1 + A²)⁻¹/²` -/

section BoundedTransform

private theorem norm_div_sqrt_one_add_sq_le_one (t : ℝ) :
    ‖((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    div_le_one (Real.sqrt_pos.2 (by positivity))]
  calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
    _ ≤ Real.sqrt (1 + t ^ 2) := Real.sqrt_le_sqrt (by linarith)

/-- The **bounded transform** (or Woronowicz–Baaj–Julg transform) `F_A = A (1 + A²)⁻¹/²` of a
self-adjoint operator `A` with compact resolvent, defined via the bounded eigenbasis functional
calculus of `t ↦ t / √(1 + t²)`. -/
def boundedTransform (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    H →L[ℂ] H :=
  A.boundedEigenCalculus hA h (fun t ↦ ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ))
    ⟨1, norm_div_sqrt_one_add_sq_le_one⟩

variable (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

/-- In any orthonormal eigenbasis of `A`, the bounded transform acts diagonally by
`λᵢ / √(1 + λᵢ²)`. -/
theorem boundedTransform_eq_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    (m : ℓ^∞(ι, ℂ)) (hm : ∀ i, m i = ((lam i / Real.sqrt (1 + lam i ^ 2) : ℝ) : ℂ)) :
    A.boundedTransform hA h = b.diagonal m :=
  A.boundedEigenCalculus_eq_diagonal hA h b hb _ _ m hm

/-- On an eigenvector of `A` with real eigenvalue `r`, the bounded transform multiplies by
`r / √(1 + r²)`. -/
theorem boundedTransform_apply_of_apply_eq_smul (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) :
    A.boundedTransform hA h x = ((r / Real.sqrt (1 + r ^ 2) : ℝ) : ℂ) • (x : H) :=
  A.boundedEigenCalculus_apply_of_apply_eq_smul hA h _ x hx

/-- The bounded transform is self-adjoint. -/
theorem isSelfAdjoint_boundedTransform : IsSelfAdjoint (A.boundedTransform hA h) :=
  A.isSelfAdjoint_boundedEigenCalculus hA h _ fun _ ↦ by simp

/-- The star of the bounded transform is itself. -/
@[simp]
theorem star_boundedTransform : star (A.boundedTransform hA h) = A.boundedTransform hA h :=
  (A.isSelfAdjoint_boundedTransform hA h).star_eq

/-- The bounded transform is a contraction: `‖A (1 + A²)⁻¹/²‖ ≤ 1`. -/
theorem norm_boundedTransform_le_one : ‖A.boundedTransform hA h‖ ≤ 1 :=
  A.norm_boundedEigenCalculus_le hA h _ zero_le_one norm_div_sqrt_one_add_sq_le_one

private theorem inv_one_add_sq_add_boundedTransform_sq (t : ℝ) :
    (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) +
      ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) = 1 := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hid : (1 + t ^ 2)⁻¹ + (t / Real.sqrt (1 + t ^ 2)) * (t / Real.sqrt (1 + t ^ 2)) = 1 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hpos.le, ← sq]
    field_simp
  exact_mod_cast hid

/-- **`1 - F_A² = (1 + A²)⁻¹`.** -/
theorem one_sub_boundedTransform_mul_self :
    1 - A.boundedTransform hA h * A.boundedTransform hA h = A.invOneAddSq := by
  have hinv_bdd : ∃ C, ∀ t : ℝ, ‖(((1 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ C :=
    ⟨1, fun t ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity)]
      exact inv_le_one_of_one_le₀ (by nlinarith)⟩
  have hsq_bdd : ∃ C, ∀ t : ℝ,
      ‖((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖ ≤ C :=
    ⟨1, fun t ↦ by
      rw [norm_mul]
      calc ‖((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖ * ‖((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖
          ≤ 1 * 1 := mul_le_mul (norm_div_sqrt_one_add_sq_le_one t)
            (norm_div_sqrt_one_add_sq_le_one t) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1⟩
  have hsum_bdd : ∃ C, ∀ t : ℝ, ‖(((1 + t ^ 2)⁻¹ : ℝ) : ℂ) +
      ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)‖ ≤ C :=
    ⟨1, fun t ↦ by rw [inv_one_add_sq_add_boundedTransform_sq]; simp⟩
  have h1 : (1 : H →L[ℂ] H) = A.boundedEigenCalculus hA h (fun _ ↦ 1) ⟨1, fun _ ↦ by simp⟩ :=
    (A.boundedEigenCalculus_one hA h _).symm
  have hmul : A.boundedTransform hA h * A.boundedTransform hA h =
      A.boundedEigenCalculus hA h
        (fun t ↦ ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) * ((t / Real.sqrt (1 + t ^ 2) : ℝ) : ℂ))
        hsq_bdd :=
    (A.boundedEigenCalculus_mul hA h _ _ hsq_bdd).symm
  rw [← A.boundedEigenCalculus_invOneAddSq hA h hinv_bdd, sub_eq_iff_eq_add, hmul,
    ← A.boundedEigenCalculus_add hA h hinv_bdd hsq_bdd hsum_bdd, h1]
  exact A.boundedEigenCalculus_congr hA h _ _ fun t ↦
    (inv_one_add_sq_add_boundedTransform_sq t).symm

/-- **`F_A² - 1 = -(1 + A²)⁻¹`.** -/
theorem boundedTransform_mul_self_sub_one :
    A.boundedTransform hA h * A.boundedTransform hA h - 1 = -A.invOneAddSq := by
  rw [← neg_sub, one_sub_boundedTransform_mul_self]

/-- The defect `F_A² - 1` of the bounded transform is compact. -/
theorem isCompactOperator_boundedTransform_mul_self_sub_one :
    IsCompactOperator ⇑(A.boundedTransform hA h * A.boundedTransform hA h - 1) := by
  rw [boundedTransform_mul_self_sub_one, FunLike.coe_neg]
  exact (h.isCompactOperator_invOneAddSq hA.I_mem_resolventSet).neg

/-- Unitary conjugation commutes with the bounded transform. -/
theorem boundedTransform_unitaryConj {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') :
    (unitaryConj U A).boundedTransform (isSelfAdjoint_unitaryConj hA)
      ((hasCompactResolvent_unitaryConj_iff U).2 h) =
      U.conjStarAlgEquiv (A.boundedTransform hA h) :=
  A.boundedEigenCalculus_unitaryConj hA h U _ _

/-- Any bounded operator preserving `D(A)` and anticommuting with `A` anticommutes with `F_A`. -/
theorem mul_boundedTransform_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.2⟩) :
    γ * A.boundedTransform hA h = -(A.boundedTransform hA h * γ) :=
  A.mul_boundedEigenCalculus_of_anticommute hA h hγdom hγA _ fun t ↦ by
    simp [neg_div]

/-! ### The Baaj–Julg commutator theorem -/

private theorem norm_inv_one_add_max_add_sq_le (r t : ℝ) :
    ‖(((1 + max r 0 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ (1 + max r 0)⁻¹ := by
  have ha : 0 < 1 + max r 0 := by linarith [le_max_right r 0]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity)]
  exact inv_anti₀ ha (by linarith [sq_nonneg t])

private theorem norm_div_one_add_max_add_sq_le (r t : ℝ) :
    ‖((t / (1 + max r 0 + t ^ 2) : ℝ) : ℂ)‖ ≤ (2 * Real.sqrt (1 + max r 0))⁻¹ := by
  have ha : 0 < 1 + max r 0 := by linarith [le_max_right r 0]
  have hd : 0 < 1 + max r 0 + t ^ 2 := by positivity
  have h2 : 0 < 2 * Real.sqrt (1 + max r 0) := by positivity
  have hsq : 2 * Real.sqrt (1 + max r 0) * |t| ≤ 1 + max r 0 + t ^ 2 := by
    have h1 : Real.sqrt (1 + max r 0) ^ 2 = 1 + max r 0 := Real.sq_sqrt ha.le
    nlinarith [sq_abs t, sq_nonneg (Real.sqrt (1 + max r 0) - |t|)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hd, div_le_iff₀ hd,
    ← mul_le_mul_iff_right₀ h2, ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul]
  exact hsq

private theorem norm_div_one_add_max_sub_le (r₁ r₂ t : ℝ) :
    ‖((t / (1 + max r₁ 0 + t ^ 2) : ℝ) : ℂ) +
      (-1 : ℂ) * ((t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ)‖ ≤ |r₁ - r₂| := by
  have hd1 : 0 < 1 + max r₁ 0 + t ^ 2 := by linarith [le_max_right r₁ 0, sq_nonneg t]
  have hd2 : 0 < 1 + max r₂ 0 + t ^ 2 := by linarith [le_max_right r₂ 0, sq_nonneg t]
  have hdiff : ((t / (1 + max r₁ 0 + t ^ 2) : ℝ) : ℂ) +
      (-1 : ℂ) * ((t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ) =
      (((t * (max r₂ 0 - max r₁ 0)) /
        ((1 + max r₁ 0 + t ^ 2) * (1 + max r₂ 0 + t ^ 2)) : ℝ) : ℂ) := by
    have hid : t / (1 + max r₁ 0 + t ^ 2) - t / (1 + max r₂ 0 + t ^ 2) =
        (t * (max r₂ 0 - max r₁ 0)) / ((1 + max r₁ 0 + t ^ 2) * (1 + max r₂ 0 + t ^ 2)) := by
      field_simp
      ring
    have hC : ((t / (1 + max r₁ 0 + t ^ 2) : ℝ) : ℂ) +
        (-1 : ℂ) * ((t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ) =
        ((t / (1 + max r₁ 0 + t ^ 2) - t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hC, hid]
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (mul_pos hd1 hd2), div_le_iff₀ (mul_pos hd1 hd2)]
  have ht_le : |t| ≤ 1 + max r₁ 0 + t ^ 2 := by
    have := sq_nonneg (|t| - 1)
    nlinarith [sq_abs t, le_max_right r₁ 0]
  have h1_le : 1 ≤ 1 + max r₂ 0 + t ^ 2 := by nlinarith [le_max_right r₂ 0]
  have hmax : |max r₂ 0 - max r₁ 0| ≤ |r₁ - r₂| := by
    rw [abs_sub_comm]
    exact abs_max_sub_max_le_abs r₁ r₂ 0
  calc |t| * |max r₂ 0 - max r₁ 0|
      ≤ (1 + max r₁ 0 + t ^ 2) * |r₁ - r₂| :=
        mul_le_mul ht_le hmax (abs_nonneg _) hd1.le
    _ = |r₁ - r₂| * ((1 + max r₁ 0 + t ^ 2) * 1) := by ring
    _ ≤ |r₁ - r₂| * ((1 + max r₁ 0 + t ^ 2) * (1 + max r₂ 0 + t ^ 2)) := by gcongr

private def bjRes (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) (r : ℝ) : H →L[ℂ] H :=
  A.boundedEigenCalculus hA h (fun t ↦ (((1 + max r 0 + t ^ 2)⁻¹ : ℝ) : ℂ))
    ⟨(1 + max r 0)⁻¹, norm_inv_one_add_max_add_sq_le r⟩

private def bjMulRes (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) (r : ℝ) : H →L[ℂ] H :=
  A.boundedEigenCalculus hA h (fun t ↦ ((t / (1 + max r 0 + t ^ 2) : ℝ) : ℂ))
    ⟨(2 * Real.sqrt (1 + max r 0))⁻¹, norm_div_one_add_max_add_sq_le r⟩

private theorem norm_bjRes_le (r : ℝ) : ‖bjRes hA h r‖ ≤ (1 + max r 0)⁻¹ :=
  A.norm_boundedEigenCalculus_le hA h _ (by have := le_max_right r 0; positivity)
    (norm_inv_one_add_max_add_sq_le r)

private theorem norm_bjMulRes_le (r : ℝ) :
    ‖bjMulRes hA h r‖ ≤ (2 * Real.sqrt (1 + max r 0))⁻¹ :=
  A.norm_boundedEigenCalculus_le hA h _ (by have := le_max_right r 0; positivity)
    (norm_div_one_add_max_add_sq_le r)

private theorem isSelfAdjoint_bjRes (r : ℝ) : IsSelfAdjoint (bjRes hA h r) :=
  A.isSelfAdjoint_boundedEigenCalculus hA h _ fun _ ↦ by simp

private theorem isSelfAdjoint_bjMulRes (r : ℝ) : IsSelfAdjoint (bjMulRes hA h r) :=
  A.isSelfAdjoint_boundedEigenCalculus hA h _ fun _ ↦ by simp

private theorem bjRes_apply_chosenBasis {r : ℝ} (hr : 0 ≤ r) (k : chosenIndex hA h) :
    bjRes hA h r (chosenBasis hA h k) =
      (((1 + r + chosenEigval hA h k ^ 2)⁻¹ : ℝ) : ℂ) • chosenBasis hA h k := by
  obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
  have h1 := A.boundedEigenCalculus_apply_of_apply_eq_smul hA h
    ⟨(1 + max r 0)⁻¹, norm_inv_one_add_max_add_sq_le r⟩ ⟨chosenBasis hA h k, hk⟩ hAk
  simpa only [bjRes, max_eq_left hr] using h1

private theorem bjMulRes_apply_chosenBasis {r : ℝ} (hr : 0 ≤ r) (k : chosenIndex hA h) :
    bjMulRes hA h r (chosenBasis hA h k) =
      ((chosenEigval hA h k / (1 + r + chosenEigval hA h k ^ 2) : ℝ) : ℂ) • chosenBasis hA h k := by
  obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
  have h1 := A.boundedEigenCalculus_apply_of_apply_eq_smul hA h
    ⟨(2 * Real.sqrt (1 + max r 0))⁻¹, norm_div_one_add_max_add_sq_le r⟩
    ⟨chosenBasis hA h k, hk⟩ hAk
  simpa only [bjMulRes, max_eq_left hr] using h1

private theorem isCompactOperator_bjMulRes (r : ℝ) : IsCompactOperator (bjMulRes hA h r) := by
  refine A.isCompactOperator_boundedEigenCalculus hA h _ ?_
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.Eventually, Filter.mem_cocompact]
  refine ⟨Metric.closedBall 0 ε⁻¹, isCompact_closedBall 0 ε⁻¹, fun t ht ↦ ?_⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
  have ha : 0 < 1 + max r 0 := by linarith [le_max_right r 0]
  have hd : 0 < 1 + max r 0 + t ^ 2 := by positivity
  have ht0 : 0 < |t| := (inv_pos.2 hε).trans ht
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  rw [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_of_pos hd]
  calc |t| / (1 + max r 0 + t ^ 2)
      < |t| / (t ^ 2) := by
        gcongr
        linarith
    _ = |t|⁻¹ := by rw [← sq_abs t, sq, div_mul_cancel_left₀ ht0.ne']
    _ < ε := (inv_lt_comm₀ ht0 hε).2 ht

private theorem continuous_bjMulRes : Continuous (bjMulRes hA h) := by
  refine LipschitzWith.continuous (K := 1) fun r₁ r₂ ↦ ?_
  rw [ENNReal.coe_one, one_mul, edist_dist, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg,
    dist_eq_norm, Real.dist_eq]
  have hneg : ∃ C, ∀ t : ℝ, ‖(-1 : ℂ) * ((t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ)‖ ≤ C :=
    ⟨(2 * Real.sqrt (1 + max r₂ 0))⁻¹, fun t ↦ by
      simpa using norm_div_one_add_max_add_sq_le r₂ t⟩
  have hsub : bjMulRes hA h r₁ - bjMulRes hA h r₂ =
      A.boundedEigenCalculus hA h
        (fun t ↦ ((t / (1 + max r₁ 0 + t ^ 2) : ℝ) : ℂ) +
          (-1 : ℂ) * ((t / (1 + max r₂ 0 + t ^ 2) : ℝ) : ℂ))
        ⟨|r₁ - r₂|, norm_div_one_add_max_sub_le r₁ r₂⟩ := by
    rw [bjMulRes, bjMulRes, sub_eq_add_neg, ← neg_one_smul ℂ,
      ← A.boundedEigenCalculus_smul hA h (-1) _ hneg,
      ← A.boundedEigenCalculus_add hA h _ hneg ⟨|r₁ - r₂|, norm_div_one_add_max_sub_le r₁ r₂⟩]
  rw [hsub]
  exact A.norm_boundedEigenCalculus_le hA h _ (abs_nonneg _) (norm_div_one_add_max_sub_le r₁ r₂)

private theorem inner_commutator_chosenBasis {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.2⟩ - T (A x) = C x)
    (i j : chosenIndex hA h) :
    ⟪chosenBasis hA h i, C (chosenBasis hA h j)⟫_ℂ =
      ((chosenEigval hA h i - chosenEigval hA h j : ℝ) : ℂ) *
        ⟪chosenBasis hA h i, T (chosenBasis hA h j)⟫_ℂ := by
  obtain ⟨hi, hAi⟩ := chosenBasis_spec hA h i
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  rw [← hC ⟨chosenBasis hA h j, hj⟩, inner_sub_right, hAj, _root_.map_smul, inner_smul_right,
    ← hA.isFormalAdjoint ⟨chosenBasis hA h i, hi⟩ ⟨T (chosenBasis hA h j), hTdom _ hj⟩,
    hAi, inner_smul_left]
  simp only [Complex.conj_ofReal, Complex.ofReal_sub]
  ring

private theorem inner_bjMulRes_commutator_chosenBasis (T : H →L[ℂ] H) {r : ℝ} (hr : 0 ≤ r)
    (i j : chosenIndex hA h) :
    ⟪chosenBasis hA h i, (bjMulRes hA h r * T - T * bjMulRes hA h r) (chosenBasis hA h j)⟫_ℂ =
      ((chosenEigval hA h i / (1 + r + chosenEigval hA h i ^ 2) -
        chosenEigval hA h j / (1 + r + chosenEigval hA h j ^ 2) : ℝ) : ℂ) *
        ⟪chosenBasis hA h i, T (chosenBasis hA h j)⟫_ℂ := by
  have hQ_adj : (bjMulRes hA h r).adjoint = bjMulRes hA h r :=
    (ContinuousLinearMap.star_eq_adjoint _).symm.trans (isSelfAdjoint_bjMulRes hA h r).star_eq
  simp only [_root_.sub_apply, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, inner_sub_right]
  rw [← ContinuousLinearMap.adjoint_inner_left (bjMulRes hA h r), hQ_adj,
    bjMulRes_apply_chosenBasis hA h hr i, bjMulRes_apply_chosenBasis hA h hr j,
    inner_smul_left, _root_.map_smul, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.ofReal_sub]
  ring

private theorem bjMulRes_commutator {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.2⟩ - T (A x) = C x) {r : ℝ} (hr : 0 ≤ r) :
    bjMulRes hA h r * T - T * bjMulRes hA h r =
      ((1 + r : ℝ) : ℂ) • (bjRes hA h r * C * bjRes hA h r) -
        bjMulRes hA h r * C * bjMulRes hA h r := by
  set b := chosenBasis hA h
  set lam := chosenEigval hA h
  have hQ_adj : (bjMulRes hA h r).adjoint = bjMulRes hA h r :=
    (ContinuousLinearMap.star_eq_adjoint _).symm.trans (isSelfAdjoint_bjMulRes hA h r).star_eq
  have hR_adj : (bjRes hA h r).adjoint = bjRes hA h r :=
    (ContinuousLinearMap.star_eq_adjoint _).symm.trans (isSelfAdjoint_bjRes hA h r).star_eq
  refine b.ext_inner_apply b fun i j ↦ ?_
  have hR1 : ⟪b i, (bjRes hA h r * C * bjRes hA h r) (b j)⟫_ℂ =
      (((1 + r + lam i ^ 2)⁻¹ * (1 + r + lam j ^ 2)⁻¹ : ℝ) : ℂ) * ⟪b i, C (b j)⟫_ℂ := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left (bjRes hA h r), hR_adj,
      bjRes_apply_chosenBasis hA h hr i, bjRes_apply_chosenBasis hA h hr j,
      inner_smul_left, _root_.map_smul, inner_smul_right]
    simp only [Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have hR2 : ⟪b i, (bjMulRes hA h r * C * bjMulRes hA h r) (b j)⟫_ℂ =
      (((lam i / (1 + r + lam i ^ 2)) * (lam j / (1 + r + lam j ^ 2)) : ℝ) : ℂ) *
        ⟪b i, C (b j)⟫_ℂ := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left (bjMulRes hA h r), hQ_adj,
      bjMulRes_apply_chosenBasis hA h hr i, bjMulRes_apply_chosenBasis hA h hr j,
      inner_smul_left, _root_.map_smul, inner_smul_right]
    simp only [Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have hCij : ⟪b i, C (b j)⟫_ℂ = ((lam i - lam j : ℝ) : ℂ) * ⟪b i, T (b j)⟫_ℂ :=
    inner_commutator_chosenBasis hA h hTdom hC i j
  rw [inner_bjMulRes_commutator_chosenBasis hA h T hr i j]
  simp only [_root_.sub_apply, _root_.smul_apply, inner_sub_right, inner_smul_right, hR1, hR2, hCij]
  have hd₁ : (1 : ℝ) + r + lam i ^ 2 ≠ 0 := by positivity
  have hd₂ : (1 : ℝ) + r + lam j ^ 2 ≠ 0 := by positivity
  have hid : lam i / (1 + r + lam i ^ 2) - lam j / (1 + r + lam j ^ 2) =
      (1 + r) * ((1 + r + lam i ^ 2)⁻¹ * (1 + r + lam j ^ 2)⁻¹) * (lam i - lam j) -
        (lam i / (1 + r + lam i ^ 2)) * (lam j / (1 + r + lam j ^ 2)) * (lam i - lam j) := by
    field_simp
    ring
  have hidC : ((lam i / (1 + r + lam i ^ 2) - lam j / (1 + r + lam j ^ 2) : ℝ) : ℂ) =
      ((1 + r : ℝ) : ℂ) * (((1 + r + lam i ^ 2)⁻¹ * (1 + r + lam j ^ 2)⁻¹ : ℝ) : ℂ) *
          ((lam i - lam j : ℝ) : ℂ) -
        (((lam i / (1 + r + lam i ^ 2)) * (lam j / (1 + r + lam j ^ 2)) : ℝ) : ℂ) *
          ((lam i - lam j : ℝ) : ℂ) := by
    exact_mod_cast hid
  rw [hidC]
  ring

private theorem norm_bjMulRes_commutator_le {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.2⟩ - T (A x) = C x) {r : ℝ} (hr : 0 ≤ r) :
    ‖bjMulRes hA h r * T - T * bjMulRes hA h r‖ ≤ (5 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := by
  rw [bjMulRes_commutator hA h hTdom hC hr]
  have h1r : 0 < 1 + r := by linarith
  have hR : ‖bjRes hA h r‖ ≤ (1 + r)⁻¹ := by simpa [max_eq_left hr] using norm_bjRes_le hA h r
  have hQ : ‖bjMulRes hA h r‖ ≤ (2 * Real.sqrt (1 + r))⁻¹ := by
    simpa [max_eq_left hr] using norm_bjMulRes_le hA h r
  have hterm1 : ‖((1 + r : ℝ) : ℂ) • (bjRes hA h r * C * bjRes hA h r)‖ ≤
      ‖C‖ * (1 + r)⁻¹ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1r]
    calc (1 + r) * ‖bjRes hA h r * C * bjRes hA h r‖
        ≤ (1 + r) * (‖bjRes hA h r‖ * ‖C‖ * ‖bjRes hA h r‖) := by
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (1 + r) * ((1 + r)⁻¹ * ‖C‖ * (1 + r)⁻¹) := by gcongr
      _ = ‖C‖ * (1 + r)⁻¹ := by field_simp
  have hterm2 : ‖bjMulRes hA h r * C * bjMulRes hA h r‖ ≤ (1 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := by
    calc ‖bjMulRes hA h r * C * bjMulRes hA h r‖
        ≤ ‖bjMulRes hA h r‖ * ‖C‖ * ‖bjMulRes hA h r‖ :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (2 * Real.sqrt (1 + r))⁻¹ * ‖C‖ * (2 * Real.sqrt (1 + r))⁻¹ := by gcongr
      _ = (1 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := by
          have hsq : Real.sqrt (1 + r) ^ 2 = 1 + r := Real.sq_sqrt h1r.le
          have hs0 : Real.sqrt (1 + r) ≠ 0 := (Real.sqrt_pos.2 h1r).ne'
          field_simp
          rw [hsq]
          ring
  calc ‖((1 + r : ℝ) : ℂ) • (bjRes hA h r * C * bjRes hA h r) -
          bjMulRes hA h r * C * bjMulRes hA h r‖
      ≤ ‖((1 + r : ℝ) : ℂ) • (bjRes hA h r * C * bjRes hA h r)‖ +
          ‖bjMulRes hA h r * C * bjMulRes hA h r‖ := norm_sub_le _ _
    _ ≤ ‖C‖ * (1 + r)⁻¹ + (1 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := add_le_add hterm1 hterm2
    _ = (5 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹ := by ring

private def bjIntegrand (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) (T : H →L[ℂ] H)
    (r : ℝ) : H →L[ℂ] H :=
  (Real.pi⁻¹ * (Real.sqrt r)⁻¹ : ℝ) • (bjMulRes hA h r * T - T * bjMulRes hA h r)

private theorem continuousOn_bjIntegrand (T : H →L[ℂ] H) :
    ContinuousOn (bjIntegrand hA h T) (Ioi 0) := by
  have hscalar : ContinuousOn (fun r : ℝ ↦ Real.pi⁻¹ * (Real.sqrt r)⁻¹) (Ioi 0) :=
    continuousOn_const.mul <|
      ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun _ hr ↦ (Real.sqrt_pos.2 hr).ne'
  have hop : ContinuousOn (fun r : ℝ ↦ bjMulRes hA h r * T - T * bjMulRes hA h r) (Ioi 0) :=
    (((continuous_bjMulRes hA h).mul continuous_const).sub
      (continuous_const.mul (continuous_bjMulRes hA h))).continuousOn
  exact hscalar.smul hop

private theorem integrableOn_bjIntegrand {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.2⟩ - T (A x) = C x) :
    IntegrableOn (bjIntegrand hA h T) (Ioi 0) := by
  have hdom : IntegrableOn
      (fun r : ℝ ↦ (5 / 4 * Real.pi⁻¹ * ‖C‖) * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹)) (Ioi 0) :=
    (TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add zero_lt_one).const_mul _
  refine hdom.mono' ((continuousOn_bjIntegrand hA h T).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : 0 < r)
  rw [bjIntegrand, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.pi⁻¹ * (Real.sqrt r)⁻¹ * ‖bjMulRes hA h r * T - T * bjMulRes hA h r‖
      ≤ Real.pi⁻¹ * (Real.sqrt r)⁻¹ * ((5 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹) := by
        gcongr
        exact norm_bjMulRes_commutator_le hA h hTdom hC hr.le
    _ = 5 / 4 * Real.pi⁻¹ * ‖C‖ * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹) := by ring

private theorem inner_bjIntegrand_chosenBasis (T : H →L[ℂ] H) (i j : chosenIndex hA h)
    {r : ℝ} (hr : 0 < r) :
    ⟪chosenBasis hA h i, bjIntegrand hA h T r (chosenBasis hA h j)⟫_ℂ =
      ((Real.pi⁻¹ * (chosenEigval hA h i * ((Real.sqrt r)⁻¹ * (1 + chosenEigval hA h i ^ 2 + r)⁻¹)
        - chosenEigval hA h j * ((Real.sqrt r)⁻¹ * (1 + chosenEigval hA h j ^ 2 + r)⁻¹)) : ℝ) : ℂ) *
        ⟪chosenBasis hA h i, T (chosenBasis hA h j)⟫_ℂ := by
  rw [bjIntegrand, _root_.smul_apply, ← Complex.coe_smul, inner_smul_right,
    inner_bjMulRes_commutator_chosenBasis hA h T hr.le i j]
  have heq₁ : 1 + r + chosenEigval hA h i ^ 2 = 1 + chosenEigval hA h i ^ 2 + r := by ring
  have heq₂ : 1 + r + chosenEigval hA h j ^ 2 = 1 + chosenEigval hA h j ^ 2 + r := by ring
  rw [heq₁, heq₂, div_eq_mul_inv, div_eq_mul_inv]
  push_cast
  ring

private theorem commutator_boundedTransform_eq_integral {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.2⟩ - T (A x) = C x) :
    A.boundedTransform hA h * T - T * A.boundedTransform hA h =
      ∫ r in Ioi (0 : ℝ), bjIntegrand hA h T r := by
  set b := chosenBasis hA h
  set lam := chosenEigval hA h
  have hint := integrableOn_bjIntegrand hA h hTdom hC
  have hF_adj : (A.boundedTransform hA h).adjoint = A.boundedTransform hA h :=
    (ContinuousLinearMap.star_eq_adjoint _).symm.trans (A.star_boundedTransform hA h)
  refine b.ext_inner_apply b fun i j ↦ ?_
  obtain ⟨hi, hAi⟩ := chosenBasis_spec hA h i
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  have hLHS : ⟪b i, (A.boundedTransform hA h * T - T * A.boundedTransform hA h) (b j)⟫_ℂ =
      ((lam i / Real.sqrt (1 + lam i ^ 2) - lam j / Real.sqrt (1 + lam j ^ 2) : ℝ) : ℂ) *
        ⟪b i, T (b j)⟫_ℂ := by
    simp only [_root_.sub_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, inner_sub_right]
    rw [← ContinuousLinearMap.adjoint_inner_left (A.boundedTransform hA h), hF_adj,
      A.boundedTransform_apply_of_apply_eq_smul hA h ⟨b i, hi⟩ hAi,
      A.boundedTransform_apply_of_apply_eq_smul hA h ⟨b j, hj⟩ hAj,
      inner_smul_left, _root_.map_smul, inner_smul_right]
    simp only [Complex.conj_ofReal, Complex.ofReal_sub]
    ring
  let L : (H →L[ℂ] H) →L[ℂ] ℂ := (innerSL ℂ (b i)).comp (ContinuousLinearMap.apply ℂ H (b j))
  have hL_comm : ⟪b i, (∫ r in Ioi (0 : ℝ), bjIntegrand hA h T r) (b j)⟫_ℂ =
      ∫ r in Ioi (0 : ℝ), ⟪b i, bjIntegrand hA h T r (b j)⟫_ℂ :=
    (L.integral_comp_comm hint).symm
  rw [hLHS, hL_comm,
    setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ inner_bjIntegrand_chosenBasis hA h T i j hr,
    integral_mul_const]
  have hint_i := (TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add (a := 1 + lam i ^ 2)
    (by positivity)).const_mul (lam i)
  have hint_j := (TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add (a := 1 + lam j ^ 2)
    (by positivity)).const_mul (lam j)
  have hreal_int :
      (∫ r in Ioi (0 : ℝ), ((Real.pi⁻¹ * (lam i * ((Real.sqrt r)⁻¹ * (1 + lam i ^ 2 + r)⁻¹) -
        lam j * ((Real.sqrt r)⁻¹ * (1 + lam j ^ 2 + r)⁻¹)) : ℝ) : ℂ)) =
      (((∫ r in Ioi (0 : ℝ), Real.pi⁻¹ * (lam i * ((Real.sqrt r)⁻¹ * (1 + lam i ^ 2 + r)⁻¹) -
        lam j * ((Real.sqrt r)⁻¹ * (1 + lam j ^ 2 + r)⁻¹))) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm ((hint_i.sub hint_j).const_mul Real.pi⁻¹)
  rw [hreal_int, integral_const_mul, integral_sub hint_i hint_j, integral_const_mul,
    integral_const_mul,
    TauCeti.integral_Ioi_inv_sqrt_mul_inv_add (by positivity),
    TauCeti.integral_Ioi_inv_sqrt_mul_inv_add (by positivity)]
  congr 1
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  exact_mod_cast (by field_simp :
    lam i / Real.sqrt (1 + lam i ^ 2) - lam j / Real.sqrt (1 + lam j ^ 2) =
      Real.pi⁻¹ * (lam i * (Real.pi / Real.sqrt (1 + lam i ^ 2)) -
        lam j * (Real.pi / Real.sqrt (1 + lam j ^ 2))))

/-- **Baaj–Julg compactness theorem.** If a bounded operator `T` preserves the domain of `A` and
has bounded commutator `[A, T]` on `D(A)`, then `[F_A, T]` is a compact operator. -/
theorem isCompactOperator_commutator_boundedTransform {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.2⟩ - T (A x) = C x) :
    IsCompactOperator ⇑(A.boundedTransform hA h * T - T * A.boundedTransform hA h) := by
  rw [commutator_boundedTransform_eq_integral hA h hTdom hC]
  -- Every value of the integrand lies in the closed subspace of compact operators;
  -- separate by Hahn–Banach to conclude the Bochner integral stays in the subspace.
  let K : Submodule ℂ (H →L[ℂ] H) := compactOperator (RingHom.id ℂ) H H
  have hKcl : _root_.IsClosed (K : Set (H →L[ℂ] H)) := isClosed_setOfPred_isCompactOperator
  have hmem (r : ℝ) : bjIntegrand hA h T r ∈ K := by
    have hQ := isCompactOperator_bjMulRes hA h r
    have hcomm : IsCompactOperator ⇑(bjMulRes hA h r * T - T * bjMulRes hA h r) := by
      rw [FunLike.coe_sub]
      exact (hQ.mul_right T).sub (hQ.mul_left T)
    change IsCompactOperator ⇑(((Real.pi⁻¹ * (Real.sqrt r)⁻¹ : ℝ) : ℂ) •
      (bjMulRes hA h r * T - T * bjMulRes hA h r))
    rw [FunLike.coe_smul]
    exact hcomm.smul _
  change (∫ r in Ioi (0 : ℝ), bjIntegrand hA h T r) ∈ (K : Set (H →L[ℂ] H))
  by_contra hnot
  obtain ⟨l, u, hlK, hlI⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (K.restrictScalars ℝ).convex hKcl hnot
  have hl_zero (y : H →L[ℂ] H) (hy : y ∈ K) : l y = 0 := by
    by_contra hly
    have hlt := hlK _ (K.smul_mem (((u + 1 : ℝ) : ℂ) * (l y)⁻¹) hy)
    rw [_root_.map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hly, mul_one,
      RCLike.re_to_complex, Complex.ofReal_re] at hlt
    linarith
  have hu : 0 < u := by simpa using hlK 0 K.zero_mem
  have hlI0 : l (∫ r in Ioi (0 : ℝ), bjIntegrand hA h T r) = 0 := by
    rw [← l.integral_comp_comm (integrableOn_bjIntegrand hA h hTdom hC)]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun r ↦ hl_zero _ (hmem r)), integral_zero]
  rw [hlI0, _root_.map_zero] at hlI
  linarith

/-- **Baaj–Julg norm estimate.** If a bounded operator `T` preserves the domain of `A` and
`[A, T] = C` on `D(A)` for a bounded operator `C`, then `‖[F_A, T]‖ ≤ (5 / 4) ‖C‖`. -/
theorem norm_commutator_boundedTransform_le {T C : H →L[ℂ] H}
    (hTdom : ∀ x ∈ A.domain, T x ∈ A.domain)
    (hC : ∀ x : A.domain, A ⟨T x, hTdom x x.2⟩ - T (A x) = C x) :
    ‖A.boundedTransform hA h * T - T * A.boundedTransform hA h‖ ≤ 5 / 4 * ‖C‖ := by
  rw [commutator_boundedTransform_eq_integral hA h hTdom hC]
  have hint := integrableOn_bjIntegrand hA h hTdom hC
  have hdom : IntegrableOn
      (fun r : ℝ ↦ (5 / 4 * Real.pi⁻¹ * ‖C‖) * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹)) (Ioi 0) :=
    (TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add zero_lt_one).const_mul _
  calc ‖∫ r in Ioi (0 : ℝ), bjIntegrand hA h T r‖
      ≤ ∫ r in Ioi (0 : ℝ), ‖bjIntegrand hA h T r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioi (0 : ℝ), (5 / 4 * Real.pi⁻¹ * ‖C‖) * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹) := by
        refine setIntegral_mono_on hint.norm hdom measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        rw [bjIntegrand, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc Real.pi⁻¹ * (Real.sqrt r)⁻¹ * ‖bjMulRes hA h r * T - T * bjMulRes hA h r‖
            ≤ Real.pi⁻¹ * (Real.sqrt r)⁻¹ * ((5 / 4 : ℝ) * ‖C‖ * (1 + r)⁻¹) := by
              gcongr
              exact norm_bjMulRes_commutator_le hA h hTdom hC hr.le
          _ = 5 / 4 * Real.pi⁻¹ * ‖C‖ * ((Real.sqrt r)⁻¹ * (1 + r)⁻¹) := by ring
    _ = 5 / 4 * Real.pi⁻¹ * ‖C‖ * (Real.pi / Real.sqrt 1) := by
        rw [integral_const_mul, TauCeti.integral_Ioi_inv_sqrt_mul_inv_add zero_lt_one]
    _ = 5 / 4 * ‖C‖ := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        rw [Real.sqrt_one, div_one]
        field_simp

end BoundedTransform

end LinearPMap
