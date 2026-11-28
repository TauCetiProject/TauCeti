/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Noncompact
import TauCeti.Geometry.Manifold.ModelTransport.Finrank

/-!
# Fundamental classes on manifolds

This module develops manifold consequences of `TauCeti.IsFundamentalClass` (defined in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass.Basic`), without importing
the integral `HomologicalOrientation` layer (comparisons with `HomologicalOrientation` live in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass.Integral`).

On an `n`-manifold with nontrivial coefficients, a fundamental class has nonzero local images and
`0` is not fundamental; over a commutative ring with faithful coefficients, `r • μ` is fundamental
iff `r` is a unit, and over a division ring on a compact connected manifold every nonzero
top-dimensional class is fundamental. On a compact connected `n`-manifold over a
Dedekind-finite ring `K`, a fundamental class determines the normalized rank-one equivalence
`TauCeti.IsFundamentalClass.linearEquivOfLinearEquiv` (and
`TauCeti.IsFundamentalClass.linearEquiv`), and every top-dimensional class is a unique multiple of
a fundamental class (`TauCeti.IsFundamentalClass.existsUnique_eq_smul`).

## Main results

* `TauCeti.IsFundamentalClass.singularHomologyToLocalHomology_ne_zero`: local images of a
  fundamental class are nonzero.
* `TauCeti.not_isFundamentalClass_zero`: `0` is not a fundamental class.
* `TauCeti.IsFundamentalClass.isFundamentalClass_smul_iff`: `r • μ` is fundamental iff `IsUnit r`.
* `TauCeti.isFundamentalClass_iff_ne_zero`: over a division ring, `μ` is fundamental iff `μ ≠ 0`.
* `TauCeti.IsFundamentalClass.exists_linearEquiv_isUnit`,
  `TauCeti.IsFundamentalClass.linearEquivOfLinearEquiv`,
  `TauCeti.IsFundamentalClass.linearEquiv`: top homology of a compact connected manifold with a
  fundamental class is free of rank one.
* `TauCeti.IsFundamentalClass.existsUnique_eq_smul`: on a connected manifold, with coefficients in
  a Dedekind-finite ring `K`, every top-dimensional class is `c • μ` for a unique `c : K`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, p.236 and Theorem 3.26.
-/

public section

noncomputable section

open CategoryTheory Module Set

universe w v u

namespace TauCeti

section Manifold

variable {M E : Type w} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)

include hn in
/-- **A fundamental class has nonzero local images** in the top degree `n` of an `n`-manifold with
nontrivial coefficients: the local homology `Hₙ(M, M ∖ {x}; N)` at a point is then a nontrivial
copy of the coefficients, which `0` does not generate. -/
theorem IsFundamentalClass.singularHomologyToLocalHomology_ne_zero [T1Space M] {R : Type u}
    [Ring R] {N : ModuleCat.{w} R} [Nontrivial N]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) (x : M) : singularHomologyToLocalHomology N x n μ ≠ 0 := by
  subst hn
  have : Nontrivial (localHomology N ({x} : Set M) (finrank ℝ E) : ModuleCat.{w} R) :=
    (singularHomologyComplSingletonFinrankIso N (chartAt E x)
      (mem_chart_source E x)).toLinearEquiv.toEquiv.nontrivial
  intro h
  have hx := (isFundamentalClass_iff μ).1 hμ x
  rw [h, Submodule.span_singleton_eq_bot.2 rfl] at hx
  exact bot_ne_top hx

include hn in
/-- **The zero class is not fundamental** in the top degree `n` of a nonempty `n`-manifold with
nontrivial coefficients: the local homology `Hₙ(M, M ∖ {x}; N)` at a point is then a nontrivial
copy of the coefficients, which `0 ∈ Hₙ(M; N)` does not generate. -/
theorem not_isFundamentalClass_zero [T1Space M] [Nonempty M] {R : Type u} [Ring R]
    (N : ModuleCat.{w} R) [Nontrivial N] :
    ¬ IsFundamentalClass (0 : ((TopCat.toSSet.obj (TopCat.of M)).homology N n :
      ModuleCat.{w} R)) := fun h ↦
  h.singularHomologyToLocalHomology_ne_zero hn (Classical.arbitrary M) (map_zero _)

include hn in
/-- **Multiples of a fundamental class.** On a nonempty `n`-manifold, with faithful coefficients
`N` over a commutative ring `R`, a multiple `r • μ` of a fundamental class `μ ∈ Hₙ(M; N)` is a
fundamental class exactly when `r` is a unit. -/
theorem IsFundamentalClass.isFundamentalClass_smul_iff [T1Space M] [Nonempty M] {R : Type u}
    [CommRing R] {N : ModuleCat.{w} R} [FaithfulSMul R N]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology N n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) (r : R) : IsFundamentalClass (r • μ) ↔ IsUnit r := by
  refine ⟨fun h ↦ ?_, fun hr ↦ (isFundamentalClass_smul_iff_of_isUnit hr).2 hμ⟩
  subst hn
  obtain ⟨x⟩ := ‹Nonempty M›
  have hv := (isFundamentalClass_iff μ).1 hμ x
  have hrv := (isFundamentalClass_iff _).1 h x
  rw [map_smul] at hrv
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1
    (hrv.symm ▸ Submodule.mem_top : singularHomologyToLocalHomology N x _ μ ∈ _)
  let e := (singularHomologyComplSingletonFinrankIso N (chartAt E x)
    (mem_chart_source E x)).toLinearEquiv
  exact IsUnit.of_mul_eq_one_right s
    (e.eq_one_of_smul_eq_self_of_span_singleton_eq_top hv (by rw [mul_smul, hs]))

include hn in
/-- **Fundamental classes over a division ring.** On a nonempty compact connected `n`-manifold, a
class of `Hₙ(M; K)` is a fundamental class exactly when it is nonzero: its image at each point is
then a nonzero element of the one-dimensional local homology. -/
theorem isFundamentalClass_iff_ne_zero [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {K : Type w} [DivisionRing K]
    (μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)) :
    IsFundamentalClass μ ↔ μ ≠ 0 := by
  have : Nonempty M := ConnectedSpace.toNonempty
  refine ⟨fun h hμ ↦ not_isFundamentalClass_zero hn (ModuleCat.of K K) (hμ ▸ h), fun hμ ↦ ?_⟩
  subst hn
  rw [isFundamentalClass_iff_isUnit_of_linearEquiv fun x ↦
    (singularHomologyComplSingletonFinrankIso (ModuleCat.of K K) (chartAt E x)
      (mem_chart_source E x)).toLinearEquiv]
  refine fun x ↦ isUnit_iff_ne_zero.2 ((LinearEquiv.map_ne_zero_iff _).2 ?_)
  rw [← map_zero (singularHomologyToLocalHomology (ModuleCat.of K K) x _)]
  exact (singularHomologyToLocalHomology_injective _ rfl x).ne hμ

end Manifold

section RankOne

variable {M : Type w} {E : Type v} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)

include hn in
/-- **The top homology of a manifold with a fundamental class is free of rank one.** On a compact
connected `n`-manifold, with coefficients `R ≃ₗ[k] k` over a Dedekind-finite ring `k` (for instance
a commutative ring or a domain), if `μ ∈ Hₙ(M; R)` is a fundamental class then `Hₙ(M; R)` is
isomorphic to `k` by an equivalence sending `μ` to a unit: restriction to the local homology at a
point is injective (`TauCeti.singularHomologyToLocalHomology_injective`), surjective since its
image contains the generator given by `μ`, and carries `μ` to a generator. -/
theorem IsFundamentalClass.exists_linearEquiv_isUnit [T2Space M] [CompactSpace M]
    [ConnectedSpace M] {k : Type w} [Ring k] [IsDedekindFiniteMonoid k] {R : ModuleCat.{w} k}
    (eR : R ≃ₗ[k] k) {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k)}
    (hμ : IsFundamentalClass μ) :
    ∃ e : ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k) ≃ₗ[k] k,
      IsUnit (e μ) := by
  let _ : ChartedSpace (ULift.{w} (Fin n) → ℝ) M := ChartedSpace.uliftFin M hn
  have hE' := finrank_ulift_fin_arrow.{w} ℝ n
  obtain ⟨x⟩ : Nonempty M := ConnectedSpace.toNonempty
  have hsurj : Function.Surjective (singularHomologyToLocalHomology R x n) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (isFundamentalClass_iff μ).1 hμ x,
      Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_range_self _ μ
  let eL := localHomologySingletonLinearEquiv R hE' eR x
  refine ⟨(LinearEquiv.ofBijective _
    ⟨singularHomologyToLocalHomology_injective R hE' x, hsurj⟩).trans eL, ?_⟩
  -- The image of `μ` generates the local homology, so its coordinate is a unit.
  exact eL.span_singleton_eq_top_iff_isUnit.1 ((isFundamentalClass_iff μ).1 hμ x)

/-- **Normalized rank-one equivalence from a fundamental class.** On a compact connected
`n`-manifold, with coefficients `eR : R ≃ₗ[k] k` over a Dedekind-finite ring `k`, a fundamental
class `μ ∈ Hₙ(M; R)` determines the `k`-linear equivalence `k ≃ₗ[k] Hₙ(M; R)` sending
`r ↦ r • μ`. -/
def IsFundamentalClass.linearEquivOfLinearEquiv [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {k : Type w} [Ring k] [IsDedekindFiniteMonoid k] {R : ModuleCat.{w} k} (eR : R ≃ₗ[k] k)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k)}
    (hμ : IsFundamentalClass μ) :
    k ≃ₗ[k] ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k) :=
  let h := hμ.exists_linearEquiv_isUnit hn eR
  let u := h.choose_spec.unit
  (u.mulRightLinearEquiv k).trans h.choose.symm

@[simp]
theorem IsFundamentalClass.linearEquivOfLinearEquiv_apply [T2Space M] [CompactSpace M]
    [ConnectedSpace M] {k : Type w} [Ring k] [IsDedekindFiniteMonoid k] {R : ModuleCat.{w} k}
    (eR : R ≃ₗ[k] k) {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology R n : ModuleCat.{w} k)}
    (hμ : IsFundamentalClass μ) (r : k) :
    hμ.linearEquivOfLinearEquiv hn eR r = r • μ := by
  simp only [linearEquivOfLinearEquiv, LinearEquiv.trans_apply, Units.mulRightLinearEquiv_apply,
    IsUnit.unit_spec, ← smul_eq_mul, map_smul, LinearEquiv.symm_apply_apply]

/-- **Normalized rank-one equivalence from a fundamental class** for ring coefficients `R`. -/
def IsFundamentalClass.linearEquiv [T2Space M] [CompactSpace M] [ConnectedSpace M] {R : Type w}
    [Ring R] [IsDedekindFiniteMonoid R]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) :
    R ≃ₗ[R] ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R) :=
  hμ.linearEquivOfLinearEquiv hn (LinearEquiv.refl R R)

@[simp]
theorem IsFundamentalClass.linearEquiv_apply [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {R : Type w} [Ring R] [IsDedekindFiniteMonoid R]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of R R) n : ModuleCat.{w} R)}
    (hμ : IsFundamentalClass μ) (r : R) :
    hμ.linearEquiv hn r = r • μ :=
  hμ.linearEquivOfLinearEquiv_apply hn (LinearEquiv.refl R R) r

end RankOne

section Connected

variable {M E : Type w} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {n : ℕ} (hn : finrank ℝ E = n)

include hn in
/-- **Top-dimensional classes are multiples of a fundamental class.** On a connected
`n`-manifold, with coefficients in a Dedekind-finite ring `K` (for instance a commutative ring),
every class `γ` of `Hₙ(M; K)` is `c • μ` for exactly one `c : K`, where `μ` is a fundamental
class. For a map `f` from a compact manifold with fundamental class `μ'`, the coefficient of
`f_* μ'` is the degree of `f` with coefficients in `K`. -/
theorem IsFundamentalClass.existsUnique_eq_smul [T2Space M] [ConnectedSpace M]
    {K : Type w} [Ring K] [IsDedekindFiniteMonoid K]
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)}
    (hμ : IsFundamentalClass μ)
    (γ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)) :
    ∃! c : K, γ = c • μ := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · -- Over the zero ring the homology is trivial.
    have := Module.subsingleton K
      ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of K K) n : ModuleCat.{w} K)
    exact ⟨0, Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  -- The fundamental class is nonzero, so `Hₙ(M; K) ≠ 0` and the connected manifold is compact.
  have : T1Space M := ChartedSpace.t1Space E M
  have : Nonempty M := ConnectedSpace.toNonempty
  have : CompactSpace M := compactSpace_of_nontrivial_singularHomology (ModuleCat.of K K) hn le_rfl
    (h := ⟨⟨μ, 0, fun h0 ↦ not_isFundamentalClass_zero hn (ModuleCat.of K K) (h0 ▸ hμ)⟩⟩)
  obtain ⟨e, u, hu⟩ := hμ.exists_linearEquiv_isUnit hn (LinearEquiv.refl K K)
  -- In the coordinate `e`, the equation `γ = c • μ` reads `e γ = c * u` for the unit `u = e μ`.
  have key (c : K) : γ = c • μ ↔ c = e γ * ↑u⁻¹ := by
    rw [← e.injective.eq_iff, map_smul, smul_eq_mul, ← hu, eq_comm, Units.eq_mul_inv_iff_mul_eq]
  exact ⟨e γ * ↑u⁻¹, (key _).2 rfl, fun c hc ↦ (key c).1 hc⟩

end Connected

end TauCeti
