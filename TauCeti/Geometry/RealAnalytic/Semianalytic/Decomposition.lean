/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Geometry.RealAlgebraic.SignInvariant
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
public import TauCeti.Topology.ClusterSet
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.SingularDirection
import TauCeti.Analysis.Analytic.Submanifold.Transport
import TauCeti.Data.Set.Lattice
import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
import TauCeti.Geometry.RealAlgebraic.Stack.Frontier.Lifting
import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
import TauCeti.Geometry.RealAnalytic.Projection
import TauCeti.Geometry.RealAnalytic.Semianalytic.Stack
import TauCeti.Topology.ContinuousOn.Extension

/-!
# Local normal decomposition of real analytic germs and semianalytic sets

Given finitely many real functions analytic at a point `x₀` of a finite-dimensional real normed
space and a prescribed neighborhood `V` of `x₀`, there exists an open semianalytic neighborhood
`U ⊆ V` of `x₀` partitioned into finitely many pairwise disjoint connected semianalytic sets on
each of which every function of the family has constant sign
(`TauCeti.exists_isConnected_partition_signInvariant`).
In coordinate space `Fin n → ℝ`, every piece of the partition is also a real analytic submanifold of
some dimension `d ≤ n` (`TauCeti.exists_isAnalyticSubmanifold_partition_signInvariant`), so in any
finite-dimensional normed space each piece is locally closed.

In coordinate space the partition moreover satisfies both parts of the frontier condition: if a
piece `B` meets the closure of a piece `C`, then `B ⊆ closure C`, and if in addition `B ≠ C`, then
the dimension of `B` is strictly smaller than that of `C`. Since the pieces cover `U`, the trace
`U ∩ closure C` of the closure of a piece is the union of the pieces it contains. Every piece also
has preconnected approach regions (`TauCeti.IsPreconnectedApproachAt`) at every point of `U`: the
piece is locally connected near each of its frontier points in `U`.

Applying this decomposition to the analytic functions appearing in local sign-condition descriptions
of semianalytic germs yields simultaneous local partitions compatible with any finite family of
germs semianalytic at `x₀` (`TauCeti.exists_isAnalyticSubmanifold_partition_subset_or_disjoint`,
`TauCeti.exists_isConnected_partition_subset_or_disjoint`), and in particular writes the trace
`s ∩ U` of a germ semianalytic at `x₀` on an arbitrarily small open semianalytic neighborhood `U`
as a finite disjoint union of connected semianalytic pieces
(`TauCeti.SemianalyticAt.exists_isAnalyticSubmanifold_partition_inter`,
`TauCeti.SemianalyticAt.exists_isConnected_partition_inter`).

The proof inducts on the ambient dimension `n`, following the same projection-and-lifting scheme as
the semialgebraic CAD construction `TauCeti.exists_isCAD_signInvariant`: after discarding the germs
vanishing near `x₀` and applying a continuous linear change of coordinates
(`TauCeti.exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top`) to put the remaining
germs into simultaneous Weierstrass general position along the `0`-th coordinate, the real
Weierstrass preparation theorem (`AnalyticAt.exists_weierstrassPreparation_real`) replaces each germ
on a cylindrical slab `(t₀ - ε, t₀ + ε) × B₀` up to a constant unit sign by a shifted Weierstrass
polynomial. Adjoining the two slab-boundary linear factors `X - C (t₀ ∓ ε)` to that polynomial
family, taking its analytic Collins projection on the base
(`TauCeti.exists_analyticOnNhd_projection_delineation`), decomposing the base by the induction
hypothesis inside a closed ball contained in `B₀`, lifting along the resulting delineations
(`TauCeti.Delineation.isSemianalytic_of_mem_stackCells`,
`TauCeti.Delineation.exists_isAnalyticSubmanifold_of_mem_stackCells`), and selecting the stack cells
contained in the open slab produces a partition of the slab whose pushforward under the linear
equivalence partitions an open semianalytic neighborhood of `x₀`. The frontier condition and the
preconnected approach regions are carried through the same induction: the members of the lifted
polynomial family are monic of constant degree, so over a base piece `B ⊆ closure C` the roots of
the delineation over `C` converge to roots of the delineation over `B`
(`TauCeti.Delineation.exists_root_tendsto_of_subset_closure`), and the stack frontier lemmas
(`TauCeti.subset_closure_of_mem_biUnion_stackCells`, `TauCeti.dim_lt_of_mem_biUnion_stackCells`,
`TauCeti.isPreconnectedApproachAt_of_mem_biUnion_stackCells`) lift both properties from the base.

## Main results

* `TauCeti.exists_isAnalyticSubmanifold_partition_signInvariant`: local partition of an open
  semianalytic neighborhood in `Fin n → ℝ` into finitely many connected semianalytic real analytic
  submanifolds on which finitely many analytic germs are sign-invariant, satisfying the frontier
  condition.
* `TauCeti.exists_isAnalyticSubmanifold_partition_subset_or_disjoint`: the same for a partition
  compatible with finitely many semianalytic germs.
* `TauCeti.SemianalyticAt.exists_isAnalyticSubmanifold_partition_inter`: a local analytic
  submanifold partition of a single semianalytic germ in `Fin n → ℝ`.
* `TauCeti.exists_isConnected_partition_signInvariant`,
  `TauCeti.exists_isConnected_partition_subset_or_disjoint`,
  `TauCeti.SemianalyticAt.exists_isConnected_partition_inter`: coordinate-free versions in any
  finite-dimensional real normed space.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, §15–17.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1–2.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
* G. E. Collins, *Quantifier elimination for real closed fields by cylindrical algebraic
  decomposition*, Lecture Notes in Computer Science 33 (1975), 134–183.
* S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Section 5.1 and Chapters 10–11.
* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), 242–268 (analytic delineability and lifting).
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

/-! ### Auxiliary polynomial and stack lemmas for a cylindrical slab -/

section SlabHelpers

variable {n : ℕ} {ι₁ : Type*} {d : ι₁ → ℕ}

/-- Family of univariate polynomials over `Fin n → ℝ` pairing shifted Weierstrass polynomials
`(monicOfCoeff (c j · z)).comp (X - C t₀)` with the two slab-boundary factors `X - C (t₀ ∓ ε)`. -/
private noncomputable def slabPoly (c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ) (t₀ ε : ℝ) :
    (ι₁ ⊕ Bool) → (Fin n → ℝ) → ℝ[X]
  | .inl j, z => (TauCeti.Polynomial.monicOfCoeff (fun k ↦ c j k z)).comp (X - C t₀)
  | .inr false, _ => X - C (t₀ - ε)
  | .inr true, _ => X - C (t₀ + ε)

private theorem analyticOnNhd_coeff_slabPoly {c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ}
    {B₀ : Set (Fin n → ℝ)} (hc : ∀ j k, AnalyticOnNhd ℝ (c j k) B₀) (t₀ ε : ℝ)
    (a : ι₁ ⊕ Bool) (m : ℕ) :
    AnalyticOnNhd ℝ (fun z ↦ (slabPoly c t₀ ε a z).coeff m) B₀ := by
  rcases a with j | (_ | _)
  · have hcoeff (z : Fin n → ℝ) :
        (slabPoly c t₀ ε (.inl j) z).coeff m =
          ((X - C t₀ : ℝ[X]) ^ d j).coeff m +
            ∑ k : Fin (d j), c j k z * ((X - C t₀ : ℝ[X]) ^ (k : ℕ)).coeff m := by
      conv_lhs =>
        rw [slabPoly, (TauCeti.Polynomial.monicOfCoeff fun k ↦ c j k z).as_sum_range_C_mul_X_pow,
          TauCeti.Polynomial.natDegree_monicOfCoeff, Finset.sum_range_succ,
          ← Fin.sum_univ_eq_sum_range]
      simp [add_comm]
    simp_rw [hcoeff]
    exact analyticOnNhd_const.add <|
      Finset.analyticOnNhd_fun_sum Finset.univ fun k _ ↦ (hc j k).mul analyticOnNhd_const
  · exact analyticOnNhd_const
  · exact analyticOnNhd_const

private theorem monic_slabPoly (c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ) (t₀ ε : ℝ)
    (a : ι₁ ⊕ Bool) (z : Fin n → ℝ) : (slabPoly c t₀ ε a z).Monic := by
  rcases a with j | (_ | _)
  · exact (TauCeti.Polynomial.monic_monicOfCoeff _).comp_X_sub_C t₀
  · exact monic_X_sub_C _
  · exact monic_X_sub_C _

private theorem natDegree_slabPoly (c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ) (t₀ ε : ℝ)
    (a : ι₁ ⊕ Bool) (z : Fin n → ℝ) :
    (slabPoly c t₀ ε a z).natDegree = Sum.elim d (fun _ ↦ 1) a := by
  rcases a with j | (_ | _)
  · rw [slabPoly, natDegree_comp, TauCeti.Polynomial.natDegree_monicOfCoeff, natDegree_X_sub_C,
      mul_one, Sum.elim_inl]
  · exact natDegree_X_sub_C _
  · exact natDegree_X_sub_C _

/-- **Frontier root matching for slab delineations.** The members of `slabPoly c t₀ ε` are monic
of constant degree with continuous coefficients on `B₀`, so the roots of a delineation over `C`
converge, along `C`, to roots of a delineation over a connected `B ⊆ B₀ ∩ closure C` at which `C`
has preconnected approach regions. -/
private theorem exists_slabPoly_root_tendsto {B₀ B C : Set (Fin n → ℝ)}
    {c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ} {t₀ ε : ℝ}
    (hc : ∀ j k, AnalyticOnNhd ℝ (c j k) B₀)
    (D_C : Delineation fun a (y : C) ↦ slabPoly c t₀ ε a y)
    (D_B : Delineation fun a (x : B) ↦ slabPoly c t₀ ε a x)
    (hBB₀ : B ⊆ B₀) (hBC : B ⊆ closure C) (hB : IsConnected B)
    (hconn : ∀ x ∈ B, IsPreconnectedApproachAt C x) :
    ∃ σ : Fin D_C.count → Fin D_B.count,
      ∀ i (x : B), Tendsto (D_C.root i) (comap Subtype.val (𝓝 x.val)) (𝓝 (D_B.root (σ i) x)) := by
  obtain ⟨σ, -, hσ⟩ := D_C.exists_root_tendsto_of_subset_closure D_B hBC hB hconn fun i ↦ by
    obtain ⟨a, ha⟩ := D_C.exists_multiplicity_pos i
    exact ⟨a, ha, fun x _ ↦ (monic_slabPoly c t₀ ε a x).ne_zero,
      fun x hx m _ ↦ (analyticOnNhd_coeff_slabPoly hc t₀ ε a m x (hBB₀ hx)).continuousAt.tendsto
        |>.mono_left nhdsWithin_le_nhds,
      fun x _ ↦ .of_forall fun y ↦ by rw [natDegree_slabPoly, natDegree_slabPoly]⟩
  exact ⟨σ, hσ⟩

/-- Because `X - C (t₀ - ε)` and `X - C (t₀ + ε)` belong to `slabPoly c t₀ ε`, every ambient cell of
a delineation of `slabPoly c t₀ ε` lies either inside or outside the open slab
`{y | y 0 ∈ Ioo (t₀ - ε) (t₀ + ε)}`. -/
private theorem subset_or_disjoint_slab_of_mem_stackCells {S : Set (Fin n → ℝ)}
    {c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ} {t₀ ε : ℝ}
    (D : Delineation fun a (x : S) ↦ slabPoly c t₀ ε a x)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root) :
    E ⊆ {y | y 0 ∈ Ioo (t₀ - ε) (t₀ + ε)} ∨ Disjoint E {y | y 0 ∈ Ioo (t₀ - ε) (t₀ + ε)} := by
  have hslab : {y : Fin (n + 1) → ℝ | y 0 ∈ Ioo (t₀ - ε) (t₀ + ε)} =
      {y | (fun σ : Bool → SignType ↦ σ false = 1 ∧ σ true = -1) fun b ↦
        SignType.sign ((slabPoly c t₀ ε (.inr b) (Fin.tail y)).eval (y 0))} := by
    ext y
    simp only [mem_ofPred_eq, mem_Ioo, slabPoly, eval_sub, eval_X, eval_C,
      sign_eq_one_iff, sign_eq_neg_one_iff, sub_pos, sub_neg]
  rw [hslab]
  exact subset_or_disjoint_setOf_sign
    (f := fun b (y : Fin (n + 1) → ℝ) ↦ (slabPoly c t₀ ε (.inr b) (Fin.tail y)).eval (y 0))
    (fun b ↦ D.signInvariant_eval_of_mem_stackCells (.inr b) hE)
    (fun σ : Bool → SignType ↦ σ false = 1 ∧ σ true = -1)

/-- Simultaneous real Weierstrass preparation on an open cylindrical slab `(t₀ - ε, t₀ + ε) × B₀`:
each germ `g j` with finite `0`-th coordinate analytic order has the sign of its shifted Weierstrass
polynomial times a constant sign `u₀ j`. -/
private theorem exists_slab_weierstrass_sign [Finite ι₁]
    {g : ι₁ → (Fin (n + 1) → ℝ) → ℝ} {y₀ : Fin (n + 1) → ℝ} {V₂ : Set (Fin (n + 1) → ℝ)}
    (hg : ∀ j, AnalyticAt ℝ (g j) y₀)
    (hord : ∀ j, analyticOrderAt (fun t ↦ g j (Fin.cons t (Fin.tail y₀))) (y₀ 0) ≠ ⊤)
    (hV₂ : V₂ ∈ 𝓝 y₀) :
    ∃ (d : ι₁ → ℕ) (c : ∀ j, Fin (d j) → (Fin n → ℝ) → ℝ) (u₀ : ι₁ → SignType)
      (B₀ : Set (Fin n → ℝ)) (ε : ℝ),
      IsOpen B₀ ∧ Fin.tail y₀ ∈ B₀ ∧ 0 < ε ∧ (∀ j k, AnalyticOnNhd ℝ (c j k) B₀) ∧
      ∀ y : Fin (n + 1) → ℝ, Fin.tail y ∈ B₀ → y 0 ∈ Ioo (y₀ 0 - ε) (y₀ 0 + ε) →
        y ∈ V₂ ∧ ∀ j, SignType.sign (g j y) =
          SignType.sign ((slabPoly c (y₀ 0) ε (.inl j) (Fin.tail y)).eval (y 0)) * u₀ j := by
  classical
  cases nonempty_fintype ι₁
  set z₀ := Fin.tail y₀
  set t₀ := y₀ 0 with ht₀
  let e : (Fin n → ℝ) × ℝ → Fin (n + 1) → ℝ := fun p ↦ Fin.cons p.2 p.1
  have he₀ : e (z₀, t₀) = y₀ := Fin.cons_self_tail y₀
  have he_an (p : (Fin n → ℝ) × ℝ) : AnalyticAt ℝ e p :=
    AnalyticAt.pi fun m ↦ Fin.cases analyticAt_snd
      (fun k ↦ ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) k).comp
        (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)).analyticAt p) m
  have hg' (j : ι₁) : AnalyticAt ℝ (g j ∘ e) (z₀, t₀) := (hg j).comp_of_eq (he_an _) he₀
  choose d hd using fun j ↦ ENat.ne_top_iff_exists.1 (hord j)
  choose c u hc _ hu hu0 hfac using fun j ↦ (hg' j).exists_weierstrassPreparation_real (hd j).symm
  -- Combine coefficient analyticity, inclusion in `V₂`, factorization, and unit sign constancy.
  have hunit (j : ι₁) : ∀ᶠ p in 𝓝 (z₀, t₀), SignType.sign (u j p) = SignType.sign (u j (z₀, t₀)) :=
    ((continuousAt_sign_of_ne_zero (hu0 j)).comp (hu j).continuousAt)
      ((isOpen_discrete _).mem_nhds (mem_singleton _))
  have hprod : ∀ᶠ p in 𝓝 (z₀, t₀), e p ∈ V₂ ∧ ∀ j,
      SignType.sign (g j (e p)) =
        SignType.sign ((TauCeti.Polynomial.monicOfCoeff (fun k ↦ c j k p.1)).eval (p.2 - t₀)) *
          SignType.sign (u j (z₀, t₀)) := by
    have heV : e ⁻¹' V₂ ∈ 𝓝 (z₀, t₀) := (he_an _).continuousAt.preimage_mem_nhds (he₀ ▸ hV₂)
    filter_upwards [heV, eventually_all.2 hfac, eventually_all.2 hunit] with p hpV hpf hpu
    refine ⟨hpV, fun j ↦ ?_⟩
    rw [← Function.comp_apply (f := g j), hpf j, sign_mul, hpu j]
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hprod
  have hc_nhds : ∀ᶠ z in 𝓝 z₀, ∀ j k, AnalyticAt ℝ (c j k) z :=
    eventually_all.2 fun j ↦ eventually_all.2 fun k ↦ (hc j k).eventually_analyticAt
  obtain ⟨B₀, hB₀sub, hB₀o, hz₀B₀⟩ :=
    eventually_nhds_iff.1 (inter_mem (Metric.ball_mem_nhds z₀ hδ) hc_nhds)
  refine ⟨d, c, fun j ↦ SignType.sign (u j (z₀, t₀)), B₀, δ, hB₀o, hz₀B₀, hδ,
    fun j k z hz ↦ (hB₀sub z hz).2 j k, fun y hyB hyI ↦ ?_⟩
  have hdist : dist (Fin.tail y, y 0) (z₀, t₀) < δ := by
    rw [Prod.dist_eq]
    refine max_lt (hB₀sub _ hyB).1 ?_
    rw [ht₀, Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [hyI.2], by linarith [hyI.1]⟩
  obtain ⟨hyV, hysign⟩ := hball hdist
  have hey : e (Fin.tail y, y 0) = y := Fin.cons_self_tail y
  rw [hey] at hyV hysign
  refine ⟨hyV, fun j ↦ ?_⟩
  simpa [slabPoly, Polynomial.eval_comp] using hysign j

/-- Lifting a base partition `𝒟` of `U'` satisfying the frontier condition along delineations
`Θ S` of `slabPoly c t₀ ε` gives a cell family `⋃ S ∈ 𝒟, stackCells S (Θ S).2` satisfying both
parts of the frontier condition, whose cells have preconnected approach regions at every point
over `U'`, provided the base cells have preconnected approach regions at every point of `U'`. -/
private theorem frontierCondition_biUnion_slabPoly_stackCells {B₀ U' : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ} {t₀ ε : ℝ}
    (hc : ∀ j k, AnalyticOnNhd ℝ (c j k) B₀) (h𝒟cov : ⋃₀ 𝒟 = U') (hU'B₀ : U' ⊆ B₀)
    (h𝒟cell : ∀ S ∈ 𝒟, IsConnected S ∧ ∃ e, IsAnalyticSubmanifold e S)
    (h𝒟front : ∀ S ∈ 𝒟, ∀ T ∈ 𝒟, (S ∩ closure T).Nonempty → S ⊆ closure T)
    (h𝒟dim : ∀ S ∈ 𝒟, ∀ T ∈ 𝒟, S ⊆ closure T → S ≠ T →
      ∀ e e', IsAnalyticSubmanifold e S → IsAnalyticSubmanifold e' T → e < e')
    (h𝒟conn : ∀ S ∈ 𝒟, ∀ x ∈ U', IsPreconnectedApproachAt S x)
    {Θ : ∀ S : Set (Fin n → ℝ), Σ k, Fin k → S → ℝ}
    (hΘ : ∀ S ∈ 𝒟, ∃ D : Delineation (fun a (x : S) ↦ slabPoly c t₀ ε a x),
      Θ S = ⟨D.count, D.root⟩)
    (hcont : ∀ S ∈ 𝒟, ∀ i, Continuous ((Θ S).2 i))
    (hmono : ∀ S ∈ 𝒟, ∀ y : S, StrictMono fun i ↦ (Θ S).2 i y) :
    let ℰ := ⋃ S ∈ 𝒟, stackCells S (Θ S).2
    (∀ E' ∈ ℰ, ∀ E ∈ ℰ, (E' ∩ closure E).Nonempty → E' ⊆ closure E) ∧
    (∀ E' ∈ ℰ, ∀ E ∈ ℰ, E' ⊆ closure E → E' ≠ E →
      ∀ e' e, IsAnalyticSubmanifold e' E' → IsAnalyticSubmanifold e E → e' < e) ∧
    ∀ E ∈ ℰ, ∀ v : Fin (n + 1) → ℝ, Fin.tail v ∈ U' → IsPreconnectedApproachAt E v := by
  intro ℰ
  have hsub (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : S ⊆ U' := h𝒟cov ▸ subset_sUnion_of_mem hS
  have hmatch : ∀ B ∈ 𝒟, ∀ C ∈ 𝒟, B ⊆ closure C → B ≠ C →
      ∃ σ : Fin (Θ C).1 → Fin (Θ B).1, ∀ i (x : B),
        Tendsto ((Θ C).2 i) (comap Subtype.val (𝓝 x.val)) (𝓝 ((Θ B).2 (σ i) x)) := by
    intro B hB C hC hBC _
    obtain ⟨D_B, hDB⟩ := hΘ B hB
    obtain ⟨D_C, hDC⟩ := hΘ C hC
    rw [hDB, hDC]
    exact exists_slabPoly_root_tendsto hc D_C D_B ((hsub B hB).trans hU'B₀) hBC (h𝒟cell B hB).1
      fun x hx ↦ h𝒟conn C hC x (hsub B hB hx)
  -- Fix a dimension for every base cell, to state the dimension drop in the base.
  choose dim hdim using fun S : Set (Fin n → ℝ) ↦ (em (S ∈ 𝒟)).elim
    (fun hS ↦ (h𝒟cell S hS).2.imp fun _ he _ ↦ he) fun hS ↦ ⟨0, fun h ↦ (hS h).elim⟩
  have hroot : ∀ S ∈ 𝒟, ∀ i, ∃ r : (Fin n → ℝ) → ℝ,
      (∀ y : S, r y = (Θ S).2 i y) ∧ AnalyticOnSubmanifold (dim S) r S := fun S hS ↦ by
    obtain ⟨D, hD⟩ := hΘ S hS
    rw [hD]
    intro i
    obtain ⟨r, -, hr⟩ := (D.continuous_root i).exists_continuousOn_eq
    exact ⟨r, hr, D.analyticOnSubmanifold_root (hdim S hS) (fun a m ↦
      ((analyticOnNhd_coeff_slabPoly hc t₀ ε a m).mono
        ((hsub S hS).trans hU'B₀)).analyticOnSubmanifold (hdim S hS)) i hr⟩
  refine ⟨fun E' hE' E hE hne ↦ subset_closure_of_mem_biUnion_stackCells
      (k := fun S ↦ (Θ S).1) (θ := fun S ↦ (Θ S).2) h𝒟front hcont hmono hmatch hE' hE hne,
    fun E' hE' E hE hsubE hne e' e hE'sub hEsub ↦ dim_lt_of_mem_biUnion_stackCells
      (k := fun S ↦ (Θ S).1) (θ := fun S ↦ (Θ S).2) (d := dim) hdim h𝒟front
      (fun B hB C hC hBC hBC' ↦ h𝒟dim B hB C hC hBC hBC' _ _ (hdim B hB) (hdim C hC)) hroot hmono
      hmatch hE' hE hE'sub hEsub hsubE hne,
    fun E hE v hv ↦ isPreconnectedApproachAt_of_mem_biUnion_stackCells
      (k := fun S ↦ (Θ S).1) (θ := fun S ↦ (Θ S).2) h𝒟cov h𝒟front
      (fun S hS x hx ↦ h𝒟conn S hS x hx.1) hcont hmono hmatch hE hv⟩

/-- Lifting a base partition `𝒟` of `U'` inside `B₀` along delineations `Θ S` of `slabPoly c t₀ ε`
and keeping the stack cells contained in `H = {y | y 0 ∈ Ioo (t₀ - ε) (t₀ + ε)}` partitions the
open slab `(Fin.tail ⁻¹' U') ∩ H` into connected semianalytic real analytic submanifolds on which
each shifted Weierstrass polynomial is sign-invariant. If the base partition satisfies the frontier
condition and its cells have preconnected approach regions at all points of `U'`, the same holds
for the partition of the slab. -/
private theorem lift_slab_partition [Finite ι₁] {B₀ U' : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ} {t₀ ε : ℝ}
    (hc : ∀ j k, AnalyticOnNhd ℝ (c j k) B₀) (h𝒟fin : 𝒟.Finite) (h𝒟disj : 𝒟.PairwiseDisjoint id)
    (h𝒟cov : ⋃₀ 𝒟 = U') (hclos : ∀ S ∈ 𝒟, closure S ⊆ B₀)
    (h𝒟cell : ∀ S ∈ 𝒟, IsConnected S ∧ IsSemianalytic S ∧ ∃ e ≤ n, IsAnalyticSubmanifold e S)
    (h𝒟front : ∀ S ∈ 𝒟, ∀ T ∈ 𝒟, (S ∩ closure T).Nonempty → S ⊆ closure T)
    (h𝒟dim : ∀ S ∈ 𝒟, ∀ T ∈ 𝒟, S ⊆ closure T → S ≠ T →
      ∀ e e', IsAnalyticSubmanifold e S → IsAnalyticSubmanifold e' T → e < e')
    (h𝒟conn : ∀ S ∈ 𝒟, ∀ x ∈ U', IsPreconnectedApproachAt S x)
    (hdelin : ∀ S ∈ 𝒟, Nonempty (Delineation fun a (x : S) ↦ slabPoly c t₀ ε a x)) :
    let H : Set (Fin (n + 1) → ℝ) := {y | y 0 ∈ Ioo (t₀ - ε) (t₀ + ε)}
    ∃ 𝒞₀ : Set (Set (Fin (n + 1) → ℝ)),
      𝒞₀.Finite ∧ 𝒞₀.PairwiseDisjoint id ∧ ⋃₀ 𝒞₀ = (Fin.tail ⁻¹' U') ∩ H ∧
      (∀ E ∈ 𝒞₀, IsConnected E ∧ IsSemianalytic E ∧ (∃ d' ≤ n + 1, IsAnalyticSubmanifold d' E) ∧
        (∀ j : ι₁, SignInvariant (fun y ↦ (slabPoly c t₀ ε (.inl j) (Fin.tail y)).eval (y 0)) E) ∧
        ∀ v ∈ (Fin.tail ⁻¹' U') ∩ H, IsPreconnectedApproachAt E v) ∧
      (∀ E' ∈ 𝒞₀, ∀ E ∈ 𝒞₀, (E' ∩ closure E).Nonempty → E' ⊆ closure E) ∧
      ∀ E' ∈ 𝒞₀, ∀ E ∈ 𝒞₀, E' ⊆ closure E → E' ≠ E →
        ∀ e' e, IsAnalyticSubmanifold e' E' → IsAnalyticSubmanifold e E → e' < e := by
  intro H
  -- Package chosen delineations as one family indexed by all sets, as the stack lifting lemmas
  -- expect; off `𝒟` it is the empty stack.
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ∀ S : Set (Fin n → ℝ), Σ k, Fin k → S → ℝ, ∀ S ∈ 𝒟,
      ∃ D : Delineation (fun a (x : S) ↦ slabPoly c t₀ ε a x), Θ S = ⟨D.count, D.root⟩ :=
    open Classical in
    ⟨fun S ↦ if hS : S ∈ 𝒟 then ⟨_, (Classical.choice (hdelin S hS)).root⟩ else ⟨0, Fin.elim0⟩,
      fun S hS ↦ ⟨Classical.choice (hdelin S hS), by simp only [hS, ↓reduceDIte]⟩⟩
  have hU'B₀ : U' ⊆ B₀ := h𝒟cov ▸ sUnion_subset fun S hS ↦ subset_closure.trans (hclos S hS)
  have hΘroot : ∀ S ∈ 𝒟,
      (∀ i, Continuous ((Θ S).2 i)) ∧ ∀ y : S, StrictMono fun i ↦ (Θ S).2 i y := fun S hS ↦ by
    obtain ⟨D, hD⟩ := hΘ S hS
    rw [hD]
    exact ⟨D.continuous_root, D.strictMono_root⟩
  have hmono : ∀ S ∈ 𝒟, ∀ y : S, StrictMono fun i ↦ (Θ S).2 i y := fun S hS ↦ (hΘroot S hS).2
  obtain ⟨hfront, hdim, hconn⟩ := frontierCondition_biUnion_slabPoly_stackCells hc h𝒟cov hU'B₀
    (fun S hS ↦ ⟨(h𝒟cell S hS).1, (h𝒟cell S hS).2.2.imp fun _ h ↦ h.2⟩) h𝒟front h𝒟dim h𝒟conn hΘ
    (fun S hS ↦ (hΘroot S hS).1) hmono
  let ℰ := ⋃ S ∈ 𝒟, stackCells S (Θ S).2
  -- Each stack cell lies inside or outside the slab and has the expected cell properties.
  have hcell : ∀ E ∈ ℰ, (E ⊆ H ∨ Disjoint E H) ∧ IsConnected E ∧ IsSemianalytic E ∧
      (∃ d' ≤ n + 1, IsAnalyticSubmanifold d' E) ∧
      ∀ j : ι₁, SignInvariant (fun y ↦ (slabPoly c t₀ ε (.inl j) (Fin.tail y)).eval (y 0)) E := by
    intro E hE
    obtain ⟨S, hS, hES⟩ := mem_iUnion₂.1 hE
    obtain ⟨D, hD⟩ := hΘ S hS
    rw [hD] at hES
    obtain ⟨hSc, hSsa, e, hen, hSsub⟩ := h𝒟cell S hS
    have hSB₀ : S ⊆ B₀ := subset_closure.trans (hclos S hS)
    obtain ⟨d', hd'e, hEsub⟩ := D.exists_isAnalyticSubmanifold_of_mem_stackCells hSsub
      (fun a m ↦ ((analyticOnNhd_coeff_slabPoly hc t₀ ε a m).mono hSB₀).analyticOnSubmanifold hSsub)
      hES
    exact ⟨subset_or_disjoint_slab_of_mem_stackCells D hES,
      isConnected_of_mem_stackCells hSc D.continuous_root D.strictMono_root hES,
      D.isSemianalytic_of_mem_stackCells hSsa
        (fun x hx ↦ ⟨Sum.elim d (fun _ ↦ 1),
          fun a m _ ↦ analyticOnNhd_coeff_slabPoly hc t₀ ε a m x (hclos S hS hx),
          fun a ↦ .of_forall fun z ↦ (natDegree_slabPoly c t₀ ε a z).le⟩) hES,
      ⟨d', by omega, hEsub⟩, fun j ↦ D.signInvariant_eval_of_mem_stackCells (.inl j) hES⟩
  refine ⟨{E ∈ ℰ | E ⊆ H}, (h𝒟fin.biUnion fun S _ ↦ finite_stackCells S _).subset (sep_subset _ _),
    (pairwiseDisjoint_biUnion_stackCells h𝒟disj fun S hS y ↦ (hmono S hS y).injective).subset
      (sep_subset _ _), ?_, fun E hE ↦ ⟨(hcell E hE.1).2.1, (hcell E hE.1).2.2.1,
        (hcell E hE.1).2.2.2.1, (hcell E hE.1).2.2.2.2, fun v hv ↦ hconn E hE.1 v hv.1⟩,
    fun E' hE' E hE ↦ hfront E' hE'.1 E hE.1, fun E' hE' E hE ↦ hdim E' hE'.1 E hE.1⟩
  rw [sUnion_sep_subset_eq_inter fun E hE ↦ (hcell E hE).1,
    sUnion_biUnion_stackCells fun S hS y ↦ (hmono S hS y).monotone, h𝒟cov, inter_comm]

/-- Pushing forward a finite partition `𝒞₀` of an open set `W` along a continuous linear equivalence
`L` of `Fin n → ℝ` preserves both parts of the frontier condition and preconnected approach regions
at the points of `W`. -/
private theorem frontierCondition_image_continuousLinearEquiv {n : ℕ}
    (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) {W : Set (Fin n → ℝ)} {𝒞₀ : Set (Set (Fin n → ℝ))}
    (h₁ : ∀ B ∈ 𝒞₀, ∀ C ∈ 𝒞₀, (B ∩ closure C).Nonempty → B ⊆ closure C)
    (h₂ : ∀ B ∈ 𝒞₀, ∀ C ∈ 𝒞₀, B ⊆ closure C → B ≠ C →
      ∀ d e, IsAnalyticSubmanifold d B → IsAnalyticSubmanifold e C → d < e)
    (h₃ : ∀ C ∈ 𝒞₀, ∀ x ∈ W, IsPreconnectedApproachAt C x) :
    (∀ B ∈ image L '' 𝒞₀, ∀ C ∈ image L '' 𝒞₀, (B ∩ closure C).Nonempty → B ⊆ closure C) ∧
    (∀ B ∈ image L '' 𝒞₀, ∀ C ∈ image L '' 𝒞₀, B ⊆ closure C → B ≠ C →
      ∀ d e, IsAnalyticSubmanifold d B → IsAnalyticSubmanifold e C → d < e) ∧
    ∀ C ∈ image L '' 𝒞₀, ∀ x ∈ L '' W, IsPreconnectedApproachAt C x := by
  have hcl (C : Set (Fin n → ℝ)) : closure (L '' C) = L '' closure C :=
    (L.toHomeomorph.image_closure C).symm
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ hne
    rw [hcl, ← image_inter L.injective, image_nonempty] at hne
    rw [hcl]
    exact image_mono (h₁ B hB C hC hne)
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ hsub hne d e hBd hCe
    rw [hcl, image_subset_image_iff L.injective] at hsub
    rw [isAnalyticSubmanifold_image_continuousLinearEquiv_iff] at hBd hCe
    exact h₂ B hB C hC hsub (fun h ↦ hne (h ▸ rfl)) d e hBd hCe
  · rintro _ ⟨C, hC, rfl⟩ _ ⟨x, hx, rfl⟩
    exact (h₃ C hC x hx).image L.continuous.continuousAt L.continuous.continuousOn
      L.symm.continuous.continuousAt (L.symm_apply_apply x) fun y _ ↦ L.symm_apply_apply y

/-- Pushing forward a finite partition `𝒞₀` of an open set `W` containing `e.symm x₀` along a
continuous linear equivalence `e : E₁ ≃L[ℝ] E₂` produces a partition of the open semianalytic
neighborhood `e '' W` of `x₀` into connected semianalytic pieces carrying any extra property `Q`. -/
private theorem image_continuousLinearEquiv_partition {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {Q : Set E₂ → Prop} (e : E₁ ≃L[ℝ] E₂) {x₀ : E₂} {V : Set E₂} {W : Set E₁}
    {𝒞₀ : Set (Set E₁)} (hWo : IsOpen W) (hy₀W : e.symm x₀ ∈ W) (hWV : e '' W ⊆ V)
    (h𝒞₀fin : 𝒞₀.Finite) (h𝒞₀disj : 𝒞₀.PairwiseDisjoint id) (h𝒞₀cov : ⋃₀ 𝒞₀ = W)
    (h𝒞₀cell : ∀ E ∈ 𝒞₀, IsConnected E ∧ IsSemianalytic E ∧ Q (e '' E)) :
    IsOpen (e '' W) ∧ x₀ ∈ e '' W ∧ e '' W ⊆ V ∧ IsSemianalytic (e '' W) ∧
      (image e '' 𝒞₀).Finite ∧ (image e '' 𝒞₀).PairwiseDisjoint id ∧ ⋃₀ (image e '' 𝒞₀) = e '' W ∧
      ∀ C ∈ image e '' 𝒞₀, IsConnected C ∧ IsSemianalytic C ∧ Q C := by
  have h𝒞cov : ⋃₀ (image e '' 𝒞₀) = e '' W := by rw [← image_sUnion, h𝒞₀cov]
  have h𝒞cell : ∀ C ∈ image e '' 𝒞₀, IsConnected C ∧ IsSemianalytic C ∧ Q C := by
    rintro _ ⟨E, hE, rfl⟩
    obtain ⟨hEc, hEsa, hEQ⟩ := h𝒞₀cell E hE
    refine ⟨hEc.image e e.continuous.continuousOn, ?_, hEQ⟩
    rw [e.image_eq_preimage_symm]
    exact hEsa.preimage fun x _ ↦ e.symm.analyticAt x
  refine ⟨e.toHomeomorph.isOpenMap W hWo, ⟨e.symm x₀, hy₀W, e.apply_symm_apply x₀⟩,
    hWV, ?_, h𝒞₀fin.image _, ?_, h𝒞cov, h𝒞cell⟩
  · rw [← h𝒞cov, sUnion_eq_biUnion]
    exact IsSemianalytic.biUnion (h𝒞₀fin.image _) fun C hC ↦ (h𝒞cell C hC).2.1
  · rintro _ ⟨E₁, hE₁, rfl⟩ _ ⟨E₂, hE₂, rfl⟩ hne
    exact (disjoint_image_iff e.injective).2 (h𝒞₀disj hE₁ hE₂ fun h ↦ hne (h ▸ rfl))

/-- Sign invariance of a family `f` on the pushforward `L '' E` of a slab cell `E`, separating the
germs vanishing on `V₁` from the Weierstrass-prepared germs. -/
private theorem signInvariant_image_of_slab {n : ℕ} {ι : Type*}
    {f : ι → (Fin (n + 1) → ℝ) → ℝ} {x₀ : Fin (n + 1) → ℝ} {V₁ : Set (Fin (n + 1) → ℝ)}
    (hV₁zero : ∀ x ∈ V₁, ∀ i, f i =ᶠ[𝓝 x₀] 0 → f i x = 0)
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) {E : Set (Fin (n + 1) → ℝ)}
    {p : {i : ι // ¬ f i =ᶠ[𝓝 x₀] 0} → (Fin (n + 1) → ℝ) → ℝ}
    {u₀ : {i : ι // ¬ f i =ᶠ[𝓝 x₀] 0} → SignType}
    (hEV₁ : ∀ y ∈ E, L y ∈ V₁)
    (hsign : ∀ y ∈ E, ∀ j, SignType.sign (f j.val (L y)) = SignType.sign (p j y) * u₀ j)
    (hEsign : ∀ j, SignInvariant (p j) E) (i : ι) :
    SignInvariant (f i) (L '' E) := by
  by_cases hi : f i =ᶠ[𝓝 x₀] 0
  · exact (signInvariant_const 0).congr fun x ⟨y, hyE, hxy⟩ ↦
      hxy ▸ (hV₁zero (L y) (hEV₁ y hyE) i hi).symm
  · rw [signInvariant_image, signInvariant_def]
    intro y₁ hy₁ y₂ hy₂
    rw [Function.comp_apply, Function.comp_apply, hsign y₁ hy₁ ⟨i, hi⟩, hsign y₂ hy₂ ⟨i, hi⟩,
      signInvariant_def.1 (hEsign ⟨i, hi⟩) y₁ hy₁ y₂ hy₂]

end SlabHelpers

/-! ### Local sign-invariant decomposition in coordinate space `Fin n → ℝ` -/

/-- **Local normal decomposition of real analytic germs in `Fin n → ℝ`.** Given a finite family of
functions `f i` analytic at `x₀ : Fin n → ℝ` and a neighborhood `V` of `x₀`, there exists an open
semianalytic neighborhood `U ⊆ V` of `x₀` partitioned into finitely many pairwise disjoint connected
semianalytic sets `C ∈ 𝒞`, each a real analytic submanifold of some dimension `d ≤ n`, on which
every `f i` is sign-invariant. The partition satisfies the frontier condition: a piece `B` meeting
the closure of a piece `C` lies in it, and then has strictly smaller dimension unless `B = C`.
Every piece has preconnected approach regions at every point of `U`. -/
theorem exists_isAnalyticSubmanifold_partition_signInvariant.{u} {n : ℕ} {ι : Type u} [Finite ι]
    {f : ι → (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      (∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ (∃ d ≤ n, IsAnalyticSubmanifold d C) ∧
        ∀ i, SignInvariant (f i) C) ∧
      (∀ B ∈ 𝒞, ∀ C ∈ 𝒞, (B ∩ closure C).Nonempty → B ⊆ closure C) ∧
      (∀ B ∈ 𝒞, ∀ C ∈ 𝒞, B ⊆ closure C → B ≠ C →
        ∀ d e, IsAnalyticSubmanifold d B → IsAnalyticSubmanifold e C → d < e) ∧
      ∀ C ∈ 𝒞, ∀ x ∈ U, IsPreconnectedApproachAt C x := by
  induction n generalizing ι with
  | zero =>
    have hVuniv : univ ⊆ V := fun y _ ↦ Subsingleton.elim y x₀ ▸ mem_of_mem_nhds hV
    refine ⟨univ, {univ}, isOpen_univ, mem_univ x₀, hVuniv, isSemianalytic_univ,
      finite_singleton univ, pairwiseDisjoint_singleton univ id, sUnion_singleton univ, ?_, ?_,
      ?_, ?_⟩
    · rintro _ rfl
      exact ⟨isConnected_univ, isSemianalytic_univ,
        ⟨0, le_rfl, isOpen_univ.isAnalyticSubmanifold univ_nonempty⟩,
        fun _ ↦ subsingleton_of_subsingleton.signInvariant⟩
    · rintro _ rfl _ rfl -
      exact subset_closure
    · rintro _ rfl _ rfl _ h
      exact (h rfl).elim
    · rintro _ rfl x -
      exact isPreconnectedApproachAt_def.2 fun s hs ↦
        ⟨s, hs, subset_rfl, subsingleton_of_subsingleton.isPreconnected⟩
  | succ n ih =>
    -- Stage 1: Shrink `V` to an open `V₁` where every germ locally zero at `x₀` vanishes.
    have hzero : ∀ᶠ x in 𝓝 x₀, ∀ i, f i =ᶠ[𝓝 x₀] 0 → f i x = 0 :=
      eventually_all.2 fun i ↦ by
        by_cases hi : f i =ᶠ[𝓝 x₀] 0
        exacts [hi.mono fun _ hx _ ↦ hx, .of_forall fun _ h ↦ (hi h).elim]
    obtain ⟨V₁, hV₁sub, hV₁o, hx₀V₁⟩ := eventually_nhds_iff.1 (inter_mem hV hzero)
    let ι₁ := {i : ι // ¬ f i =ᶠ[𝓝 x₀] 0}
    -- Stage 2: Put non-locally-zero germs in Weierstrass general position and prepare on a slab.
    obtain ⟨L, hord⟩ := exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top
      (f := fun j : ι₁ ↦ f j.val) (fun j ↦ hf j.val) (fun j ↦ j.property)
    set y₀ := L.symm x₀
    obtain ⟨d, c, u₀, B₀, ε, hB₀o, hz₀B₀, hε, hc, hslab⟩ := exists_slab_weierstrass_sign
      (g := fun j : ι₁ ↦ f j.val ∘ L) (fun j ↦ (hf j.val).comp_of_eq (L.analyticAt y₀)
        (L.apply_symm_apply x₀)) hord
      ((hV₁o.preimage L.continuous).mem_nhds (by simpa [y₀] using hx₀V₁))
    -- Stage 3: Project the augmented slab polynomial family onto `B₀` and decompose inside a ball.
    obtain ⟨g, hg_an, hg_delin⟩ := exists_analyticOnNhd_projection_delineation
      (F := slabPoly c (y₀ 0) ε) (d := Sum.elim d (fun _ ↦ 1))
      (fun a m _ ↦ analyticOnNhd_coeff_slabPoly hc (y₀ 0) ε a m)
      (fun a z _ ↦ (natDegree_slabPoly c (y₀ 0) ε a z).le)
    obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.1 hB₀o (Fin.tail y₀) hz₀B₀
    obtain ⟨U', 𝒟, hU'o, hz₀U', hU'ball, _, h𝒟fin, h𝒟disj, h𝒟cov, h𝒟cell, h𝒟front, h𝒟dim,
        h𝒟conn⟩ :=
      ih (f := fun a : ULift.{u} g ↦ a.down.val) (fun a ↦ hg_an a.down.val a.down.property _ hz₀B₀)
        (Metric.ball_mem_nhds (Fin.tail y₀) (half_pos hr₀))
    -- Stage 4: Delineate `slabPoly` over each base cell and lift to a partition of the slab `W`.
    have hclos (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : closure S ⊆ B₀ :=
      (closure_mono ((subset_sUnion_of_mem hS).trans (h𝒟cov ▸ hU'ball))).trans <|
        Metric.closure_ball_subset_closedBall.trans <|
          (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball₀
    have hdelin (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) :
        Nonempty (Delineation fun a (x : S) ↦ slabPoly c (y₀ 0) ε a x) :=
      hg_delin S (subset_closure.trans (hclos S hS)) (h𝒟cell S hS).1.isPreconnected
        fun a ha x hx y hy ↦ by
          rw [← sign_eq_zero_iff (a := a x), ← sign_eq_zero_iff (a := a y),
            signInvariant_def.1 ((h𝒟cell S hS).2.2.2 (ULift.up ⟨a, ha⟩)) x hx y hy]
    obtain ⟨𝒞₀, h𝒞₀fin, h𝒞₀disj, h𝒞₀cov, h𝒞₀cell, h𝒞₀front, h𝒞₀dim⟩ :=
      lift_slab_partition hc h𝒟fin h𝒟disj h𝒟cov hclos
        (fun S hS ↦ ⟨(h𝒟cell S hS).1, (h𝒟cell S hS).2.1, (h𝒟cell S hS).2.2.1⟩) h𝒟front h𝒟dim
        h𝒟conn hdelin
    -- Stage 5: Push forward the slab partition along `L` and verify sign invariance on each cell.
    set W := (Fin.tail ⁻¹' U') ∩ {y : Fin (n + 1) → ℝ | y 0 ∈ Ioo (y₀ 0 - ε) (y₀ 0 + ε)}
    have hWB₀ (y : Fin (n + 1) → ℝ) (hy : y ∈ W) : Fin.tail y ∈ B₀ :=
      hball₀ ((Metric.ball_subset_ball (half_lt_self hr₀).le) (hU'ball hy.1))
    obtain ⟨hUo, hx₀U, hUV, hUsa, h𝒞fin, h𝒞disj, h𝒞cov, h𝒞cell⟩ :=
      image_continuousLinearEquiv_partition (V := V)
        (Q := fun C ↦ (∃ d' ≤ n + 1, IsAnalyticSubmanifold d' C) ∧ ∀ i, SignInvariant (f i) C) L
        ((hU'o.preimage (continuous_pi fun k ↦ continuous_apply k.succ)).inter
          ((isOpen_Ioo).preimage (continuous_apply 0)))
        ⟨hz₀U', by simp [y₀, hε]⟩
        (fun _ ⟨y, hyW, hxy⟩ ↦ hxy ▸ (hV₁sub _ (hslab y (hWB₀ y hyW) hyW.2).1).1)
        h𝒞₀fin h𝒞₀disj h𝒞₀cov fun E hE ↦ by
          obtain ⟨hEc, hEsa, ⟨d', hd', hEsub⟩, hEsign, -⟩ := h𝒞₀cell E hE
          have hEW : E ⊆ W := h𝒞₀cov ▸ subset_sUnion_of_mem hE
          exact ⟨hEc, hEsa, ⟨d', hd', hEsub.image_continuousLinearEquiv L⟩,
            signInvariant_image_of_slab (fun x hx ↦ (hV₁sub x hx).2) L
              (fun y hy ↦ (hslab y (hWB₀ y (hEW hy)) (hEW hy).2).1)
              (fun y hy j ↦ (hslab y (hWB₀ y (hEW hy)) (hEW hy).2).2 j) hEsign⟩
    obtain ⟨h𝒞front, h𝒞dim, h𝒞conn⟩ :=
      frontierCondition_image_continuousLinearEquiv L h𝒞₀front h𝒞₀dim
        fun E hE ↦ (h𝒞₀cell E hE).2.2.2.2
    exact ⟨_, _, hUo, hx₀U, hUV, hUsa, h𝒞fin, h𝒞disj, h𝒞cov, h𝒞cell, h𝒞front, h𝒞dim, h𝒞conn⟩

/-- **Simultaneous local normal decomposition for semianalytic germs in `Fin n → ℝ`.**
Given finitely many sets `s i` semianalytic at `x₀ : Fin n → ℝ` and a neighborhood `V` of `x₀`,
there exists an open semianalytic neighborhood `U ⊆ V` of `x₀` partitioned into finitely many
pairwise disjoint connected semianalytic real analytic submanifolds, each lying either inside or
outside every `s i`. The partition satisfies the frontier condition: a piece `B` meeting the
closure of a piece `C` lies in it, and then has strictly smaller dimension unless `B = C`. Every
piece has preconnected approach regions at every point of `U`. -/
theorem exists_isAnalyticSubmanifold_partition_subset_or_disjoint {n : ℕ} {ι : Type*} [Finite ι]
    {s : ι → Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hs : ∀ i, SemianalyticAt (s i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      (∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ (∃ d ≤ n, IsAnalyticSubmanifold d C) ∧
        ∀ i, C ⊆ s i ∨ Disjoint C (s i)) ∧
      (∀ B ∈ 𝒞, ∀ C ∈ 𝒞, (B ∩ closure C).Nonempty → B ⊆ closure C) ∧
      (∀ B ∈ 𝒞, ∀ C ∈ 𝒞, B ⊆ closure C → B ≠ C →
        ∀ d e, IsAnalyticSubmanifold d B → IsAnalyticSubmanifold e C → d < e) ∧
      ∀ C ∈ 𝒞, ∀ x ∈ U, IsPreconnectedApproachAt C x := by
  classical
  cases nonempty_fintype ι
  choose W hW t ht hst using fun i ↦ semianalyticAt_def.1 (hs i)
  choose m f hf Φ ht_eq using fun i ↦ (ht i).exists_eq_setOf_sign
  have hfx (p : Σ i, Fin (m i)) : AnalyticAt ℝ (f p.1 p.2) x₀ :=
    hf p.1 p.2 x₀ (mem_of_mem_nhds (hW p.1))
  obtain ⟨U, 𝒞, hUo, hx₀U, hUW, hUsa, h𝒞fin, h𝒞disj, h𝒞cov, h𝒞cell, h𝒞front⟩ :=
    exists_isAnalyticSubmanifold_partition_signInvariant (f := fun p : Σ i, Fin (m i) ↦ f p.1 p.2)
      hfx (inter_mem hV (iInter_mem.2 hW))
  refine ⟨U, 𝒞, hUo, hx₀U, hUW.trans inter_subset_left, hUsa, h𝒞fin, h𝒞disj, h𝒞cov,
    fun C hC ↦ ?_, h𝒞front⟩
  obtain ⟨hCc, hCsa, hCsub, hCsign⟩ := h𝒞cell C hC
  refine ⟨hCc, hCsa, hCsub, fun i ↦ ?_⟩
  have hCU : C ⊆ W i := fun y hy ↦ mem_iInter.1 (hUW (h𝒞cov ▸ mem_sUnion.2 ⟨C, hC, hy⟩)).2 i
  -- On `C ⊆ W i`, `s i` agrees with `{y | Φ i fun k ↦ sign (f i k y)}`.
  rcases subset_or_disjoint_setOf_sign (t := C) (f := fun k ↦ f i k)
      (fun k ↦ hCsign ⟨i, k⟩) (Φ i) with hsub | hdisj
  · refine .inl fun y hyC ↦ ?_
    have hmem := Set.ext_iff.1 (hst i) y
    exact (hmem.2 ⟨ht_eq i ▸ hsub hyC, hCU hyC⟩).1
  · refine .inr (disjoint_left.2 fun y hyC hys ↦ disjoint_left.1 hdisj hyC ?_)
    have hmem := Set.ext_iff.1 (hst i) y
    exact ht_eq i ▸ (hmem.1 ⟨hys, hCU hyC⟩).1

/-- **Local connected analytic submanifold partition of a semianalytic germ in `Fin n → ℝ`.** If `s`
is semianalytic at `x₀ : Fin n → ℝ` and `V ∈ 𝓝 x₀`, there is an open semianalytic neighborhood
`U ⊆ V` of `x₀` such that `s ∩ U` is globally semianalytic and partitioned into finitely many
pairwise disjoint connected semianalytic real analytic submanifolds. -/
theorem SemianalyticAt.exists_isAnalyticSubmanifold_partition_inter {n : ℕ}
    {s V : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} (hs : SemianalyticAt s x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧ IsSemianalytic (s ∩ U) ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = s ∩ U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ ∃ d ≤ n, IsAnalyticSubmanifold d C := by
  obtain ⟨U, 𝒟, hUo, hx₀U, hUV, hUsa, h𝒟fin, h𝒟disj, h𝒟cov, h𝒟cell, -⟩ :=
    exists_isAnalyticSubmanifold_partition_subset_or_disjoint (fun _ : Unit ↦ hs) hV
  have h𝒞fin : {C ∈ 𝒟 | C ⊆ s}.Finite := h𝒟fin.subset (sep_subset _ _)
  have h𝒞cov : ⋃₀ {C ∈ 𝒟 | C ⊆ s} = s ∩ U := by
    rw [sUnion_sep_subset_eq_inter fun C hC ↦ (h𝒟cell C hC).2.2.2 (), h𝒟cov]
  have hsUsa : IsSemianalytic (s ∩ U) := by
    rw [← h𝒞cov, sUnion_eq_biUnion]
    exact .biUnion h𝒞fin fun C hC ↦ (h𝒟cell C hC.1).2.1
  exact ⟨U, {C ∈ 𝒟 | C ⊆ s}, hUo, hx₀U, hUV, hUsa, hsUsa, h𝒞fin, h𝒟disj.subset (sep_subset _ _),
    h𝒞cov, fun C hC ↦ ⟨(h𝒟cell C hC.1).1, (h𝒟cell C hC.1).2.1, (h𝒟cell C hC.1).2.2.1⟩⟩

/-! ### Coordinate-free local decompositions in finite-dimensional real normed spaces -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local sign-invariant decomposition of real analytic germs.** Given finitely many real
functions `f i` analytic at a point `x₀` of a finite-dimensional real normed space `E` and a
neighborhood `V` of `x₀`, there exists an open semianalytic neighborhood `U ⊆ V` of `x₀` partitioned
into finitely many pairwise disjoint connected, semianalytic, locally closed sets on each of which
every `f i` is sign-invariant. -/
theorem exists_isConnected_partition_signInvariant {ι : Type*} [Finite ι]
    {f : ι → E → ℝ} {x₀ : E} {V : Set E}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set E) (𝒞 : Set (Set E)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ IsLocallyClosed C ∧
        ∀ i, SignInvariant (f i) C := by
  let φ : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  obtain ⟨U₀, 𝒞₀, hU₀o, hx₀U₀, hU₀V, _, h𝒞₀fin, h𝒞₀disj, h𝒞₀cov, h𝒞₀cell, -⟩ :=
    exists_isAnalyticSubmanifold_partition_signInvariant (f := fun i ↦ f i ∘ φ.symm)
      (fun i ↦ (hf i).comp_of_eq (φ.symm.analyticAt (φ x₀)) (φ.symm_apply_apply x₀))
      (φ.toHomeomorph.symm.continuous.continuousAt.preimage_mem_nhds
        (by simpa [φ.symm_apply_apply] using hV))
  refine ⟨_, _, image_continuousLinearEquiv_partition φ.symm hU₀o hx₀U₀ (image_subset_iff.2 hU₀V)
    h𝒞₀fin h𝒞₀disj h𝒞₀cov fun C₀ hC₀ ↦ ?_⟩
  obtain ⟨hCc, hCsa, ⟨_, _, hCsub⟩, hCsign⟩ := h𝒞₀cell C₀ hC₀
  exact ⟨hCc, hCsa,
    (φ.symm.image_eq_preimage_symm C₀).symm ▸ hCsub.isLocallyClosed.preimage φ.continuous,
    fun i ↦ signInvariant_image.2 (hCsign i)⟩

/-- **Simultaneous local connected partition for semianalytic germs.** Given finitely many sets
`s i` semianalytic at a point `x₀` of a finite-dimensional real normed space `E` and `V ∈ 𝓝 x₀`,
there exists an open semianalytic neighborhood `U ⊆ V` of `x₀` partitioned into finitely many
pairwise disjoint connected, semianalytic, locally closed sets, each lying inside or outside every
`s i`. -/
theorem exists_isConnected_partition_subset_or_disjoint {ι : Type*} [Finite ι]
    {s : ι → Set E} {x₀ : E} {V : Set E}
    (hs : ∀ i, SemianalyticAt (s i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set E) (𝒞 : Set (Set E)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ IsLocallyClosed C ∧
        ∀ i, C ⊆ s i ∨ Disjoint C (s i) := by
  let φ : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv
  have hs' (i : ι) : SemianalyticAt (φ.symm ⁻¹' s i) (φ x₀) :=
    (φ.symm_apply_apply x₀ ▸ hs i).preimage (φ.symm.analyticAt (φ x₀))
  obtain ⟨U₀, 𝒞₀, hU₀o, hx₀U₀, hU₀V, _, h𝒞₀fin, h𝒞₀disj, h𝒞₀cov, h𝒞₀cell, -⟩ :=
    exists_isAnalyticSubmanifold_partition_subset_or_disjoint hs'
      (φ.toHomeomorph.symm.continuous.continuousAt.preimage_mem_nhds
        (by simpa [φ.symm_apply_apply] using hV))
  refine ⟨_, _, image_continuousLinearEquiv_partition φ.symm hU₀o hx₀U₀ (image_subset_iff.2 hU₀V)
    h𝒞₀fin h𝒞₀disj h𝒞₀cov fun C₀ hC₀ ↦ ?_⟩
  obtain ⟨hCc, hCsa, ⟨_, _, hCsub⟩, hCcompat⟩ := h𝒞₀cell C₀ hC₀
  refine ⟨hCc, hCsa,
    (φ.symm.image_eq_preimage_symm C₀).symm ▸ hCsub.isLocallyClosed.preimage φ.continuous,
    fun i ↦ ?_⟩
  rcases hCcompat i with hsub | hdisj
  · exact .inl (image_subset_iff.2 hsub)
  · exact .inr (disjoint_left.2 fun _ ⟨y, hy, hxy⟩ hys ↦
      disjoint_left.1 hdisj hy (by simpa [mem_preimage, hxy] using hys))

/-- **Local connected partition of a semianalytic germ.** If `s` is semianalytic at a point `x₀` of
a finite-dimensional real normed space `E` and `V ∈ 𝓝 x₀`, there exists an open semianalytic
neighborhood `U ⊆ V` of `x₀` such that `s ∩ U` is globally semianalytic and partitioned into
finitely many pairwise disjoint connected, semianalytic, locally closed sets. -/
theorem SemianalyticAt.exists_isConnected_partition_inter {s V : Set E} {x₀ : E}
    (hs : SemianalyticAt s x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set E) (𝒞 : Set (Set E)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧ IsSemianalytic (s ∩ U) ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = s ∩ U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ IsLocallyClosed C := by
  obtain ⟨U, 𝒟, hUo, hx₀U, hUV, hUsa, h𝒟fin, h𝒟disj, h𝒟cov, h𝒟cell⟩ :=
    exists_isConnected_partition_subset_or_disjoint (fun _ : Unit ↦ hs) hV
  have h𝒞fin : {C ∈ 𝒟 | C ⊆ s}.Finite := h𝒟fin.subset (sep_subset _ _)
  have h𝒞cov : ⋃₀ {C ∈ 𝒟 | C ⊆ s} = s ∩ U := by
    rw [sUnion_sep_subset_eq_inter fun C hC ↦ (h𝒟cell C hC).2.2.2 (), h𝒟cov]
  have hsUsa : IsSemianalytic (s ∩ U) := by
    rw [← h𝒞cov, sUnion_eq_biUnion]
    exact .biUnion h𝒞fin fun C hC ↦ (h𝒟cell C hC.1).2.1
  exact ⟨U, {C ∈ 𝒟 | C ⊆ s}, hUo, hx₀U, hUV, hUsa, hsUsa, h𝒞fin, h𝒟disj.subset (sep_subset _ _),
    h𝒞cov, fun C hC ↦ ⟨(h𝒟cell C hC.1).1, (h𝒟cell C hC.1).2.1, (h𝒟cell C hC.1).2.2.1⟩⟩

end FiniteDimensional

end TauCeti
