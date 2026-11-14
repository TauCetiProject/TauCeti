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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Analytic.Complexification.Weierstrass
import TauCeti.Analysis.Analytic.SingularDirection
import TauCeti.Analysis.Analytic.Submanifold.Transport
import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
import TauCeti.Geometry.RealAnalytic.Projection
import TauCeti.Geometry.RealAnalytic.Semianalytic.Stack

/-!
# Local sign-invariant decomposition of real analytic germs and semianalytic sets

Given finitely many real functions analytic at a point `x₀` of a finite-dimensional real normed
space and a prescribed neighborhood `V` of `x₀`, there exists an open semianalytic neighborhood
`U ⊆ V` of `x₀` partitioned into finitely many pairwise disjoint connected semianalytic sets on
each of which every function of the family has constant sign
(`TauCeti.exists_isConnected_partition_signInvariant`).
In coordinate space `Fin n → ℝ`, every piece of the partition is also a real analytic submanifold of
some dimension `d ≤ n` (`TauCeti.exists_isAnalyticSubmanifold_partition_signInvariant`), so in any
finite-dimensional normed space each piece is locally closed.

Applying this decomposition to the analytic functions appearing in local sign-condition descriptions
of semianalytic germs yields simultaneous local partitions compatible with any finite family of
germs semianalytic at `x₀` (`TauCeti.SemianalyticAt.exists_isAnalyticSubmanifold_partition`,
`TauCeti.SemianalyticAt.exists_isConnected_partition`), and in particular writes the trace `s ∩ U`
of a germ semianalytic at `x₀` on an arbitrarily small open semianalytic neighborhood `U` as a
finite disjoint union of connected semianalytic pieces
(`TauCeti.SemianalyticAt.exists_isAnalyticSubmanifold_partition_inter`,
`TauCeti.SemianalyticAt.exists_isConnected_partition_inter`).

The proof inducts on the ambient dimension `n`: after discarding the germs vanishing near `x₀` and
applying a continuous linear change of coordinates to put the remaining germs into simultaneous
Weierstrass general position along the `0`-th coordinate, the real Weierstrass preparation theorem
replaces each germ on a cylindrical slab `(t₀ - ε, t₀ + ε) × B₀` up to a constant unit sign by a
shifted Weierstrass polynomial. Adjoining the two slab-boundary linear factors `X - C (t₀ ∓ ε)` to
that polynomial family, taking its analytic Collins projection on the base, decomposing the base by
the induction hypothesis inside a closed ball contained in `B₀`, and selecting the stack cells
contained in the open slab produces a partition of the slab whose pushforward under the linear
equivalence partitions an open semianalytic neighborhood of `x₀`.

## Main results

* `TauCeti.exists_isAnalyticSubmanifold_partition_signInvariant`: local partition of an open
  semianalytic neighborhood in `Fin n → ℝ` into finitely many connected semianalytic real analytic
  submanifolds on which finitely many analytic germs are sign-invariant.
* `TauCeti.SemianalyticAt.exists_isAnalyticSubmanifold_partition`,
  `TauCeti.SemianalyticAt.exists_isAnalyticSubmanifold_partition_inter`: compatible local analytic
  submanifold partitions for finite families of semianalytic germs and for a single semianalytic
  germ in `Fin n → ℝ`.
* `TauCeti.exists_isConnected_partition_signInvariant`,
  `TauCeti.SemianalyticAt.exists_isConnected_partition`,
  `TauCeti.SemianalyticAt.exists_isConnected_partition_inter`: coordinate-free versions in any
  finite-dimensional real normed space.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, §15–17.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1–2.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
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

private theorem natDegree_slabPoly_le (c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ) (t₀ ε : ℝ)
    (a : ι₁ ⊕ Bool) (z : Fin n → ℝ) :
    (slabPoly c t₀ ε a z).natDegree ≤ Sum.elim d (fun _ ↦ 1) a := by
  rcases a with j | (_ | _)
  · exact Polynomial.natDegree_comp_le.trans <| by
      rw [TauCeti.Polynomial.natDegree_monicOfCoeff, natDegree_X_sub_C, mul_one]; rfl
  · exact (natDegree_X_sub_C _).le
  · exact (natDegree_X_sub_C _).le

/-- Every member of a delineated polynomial family is sign-invariant along
`y ↦ (F k (tail y)).eval (y 0)` on each ambient stack cell. -/
private theorem signInvariant_eval_of_mem_stackCells {κ : Type*} {S : Set (Fin n → ℝ)}
    {F : κ → (Fin n → ℝ) → ℝ[X]} (D : Delineation fun k (x : S) ↦ F k x) (k : κ)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root) :
    SignInvariant (fun y : Fin (n + 1) → ℝ ↦ (F k (Fin.tail y)).eval (y 0)) E := by
  have hcomp : (fun y : Fin (n + 1) → ℝ ↦ (F k (Fin.tail y)).eval (y 0)) ∘ cylinder S =
      fun z : S × ℝ ↦ (F k z.1.1).eval z.2 := by
    ext z
    simp [cylinder_def]
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rw [signInvariant_image, hcomp]
  exacts [D.signInvariant_sectionSet k i, D.signInvariant_sectorSet k j]

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
    (fun b ↦ signInvariant_eval_of_mem_stackCells D (.inr b) hE)
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
  set t₀ := y₀ 0
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
    change SignType.sign ((g j ∘ e) p) = _
    rw [hpf j, sign_mul, hpu j]
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
    change dist (y 0) (y₀ 0) < δ
    rw [Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [hyI.2], by linarith [hyI.1]⟩
  obtain ⟨hyV, hysign⟩ := hball hdist
  have hey : e (Fin.tail y, y 0) = y := Fin.cons_self_tail y
  rw [hey] at hyV hysign
  refine ⟨hyV, fun j ↦ ?_⟩
  simpa [slabPoly, Polynomial.eval_comp] using hysign j

/-- Lifting a base partition `𝒟` of `U'` inside `B₀` along delineations of `slabPoly c t₀ ε` and
keeping the stack cells contained in `H = {y | y 0 ∈ Ioo (t₀ - ε) (t₀ + ε)}` partitions the open
slab `(Fin.tail ⁻¹' U') ∩ H` into connected semianalytic real analytic submanifolds on which each
shifted Weierstrass polynomial is sign-invariant. -/
private theorem lift_slab_partition [Finite ι₁] {B₀ U' : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {c : ∀ j : ι₁, Fin (d j) → (Fin n → ℝ) → ℝ} {t₀ ε : ℝ}
    (hc : ∀ j k, AnalyticOnNhd ℝ (c j k) B₀) (h𝒟fin : 𝒟.Finite) (h𝒟disj : 𝒟.PairwiseDisjoint id)
    (h𝒟cov : ⋃₀ 𝒟 = U') (hclos : ∀ S ∈ 𝒟, closure S ⊆ B₀)
    (h𝒟cell : ∀ S ∈ 𝒟, IsConnected S ∧ IsSemianalytic S ∧ ∃ e ≤ n, IsAnalyticSubmanifold e S)
    (D : ∀ S : 𝒟, Delineation fun a (x : S.1) ↦ slabPoly c t₀ ε a x) :
    let H : Set (Fin (n + 1) → ℝ) := {y | y 0 ∈ Ioo (t₀ - ε) (t₀ + ε)}
    ∃ 𝒞₀ : Set (Set (Fin (n + 1) → ℝ)),
      𝒞₀.Finite ∧ 𝒞₀.PairwiseDisjoint id ∧ ⋃₀ 𝒞₀ = (Fin.tail ⁻¹' U') ∩ H ∧
      ∀ E ∈ 𝒞₀, IsConnected E ∧ IsSemianalytic E ∧ (∃ d' ≤ n + 1, IsAnalyticSubmanifold d' E) ∧
        ∀ j : ι₁, SignInvariant (fun y ↦ (slabPoly c t₀ ε (.inl j) (Fin.tail y)).eval (y 0)) E := by
  intro H
  have := h𝒟fin.to_subtype
  let 𝒞₀ : Set (Set (Fin (n + 1) → ℝ)) :=
    ⋃ S : 𝒟, {E ∈ stackCells S.1 (D S).root | E ⊆ H}
  refine ⟨𝒞₀, finite_iUnion fun S ↦ (finite_stackCells S.1 _).subset (sep_subset _ _),
    ?_, ?_, ?_⟩
  · -- Cells over the same base cell are disjoint in the stack; cells over distinct bases have
    -- disjoint `Fin.tail` projections.
    rintro E₁ hE₁ E₂ hE₂ hne
    obtain ⟨S₁, hE₁S, -⟩ := mem_iUnion.1 hE₁
    obtain ⟨S₂, hE₂S, -⟩ := mem_iUnion.1 hE₂
    rcases eq_or_ne S₁ S₂ with rfl | hSne
    · exact pairwiseDisjoint_stackCells (fun x ↦ ((D S₁).strictMono_root x).injective)
        hE₁S hE₂S hne
    · refine Disjoint.mono
        (subset_sUnion_of_mem hE₁S |>.trans (sUnion_stackCells fun x ↦
          ((D S₁).strictMono_root x).monotone).subset)
        (subset_sUnion_of_mem hE₂S |>.trans (sUnion_stackCells fun x ↦
          ((D S₂).strictMono_root x).monotone).subset)
        ((h𝒟disj S₁.2 S₂.2 (Subtype.coe_ne_coe.2 hSne)).preimage Fin.tail)
  · -- The kept stack cells cover `(Fin.tail ⁻¹' U') ∩ H`.
    ext y
    simp only [𝒞₀, mem_sUnion, mem_iUnion, mem_sep_iff, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨E, ⟨S, hES, hEH⟩, hyE⟩
      have hyS : Fin.tail y ∈ S.1 :=
        (sUnion_stackCells fun x ↦ ((D S).strictMono_root x).monotone).subset
          (mem_sUnion.2 ⟨E, hES, hyE⟩)
      exact ⟨h𝒟cov ▸ mem_sUnion.2 ⟨S.1, S.2, hyS⟩, hEH hyE⟩
    · rintro ⟨hyU', hyH⟩
      obtain ⟨S, hS𝒟, hyS⟩ := mem_sUnion.1 (h𝒟cov.symm ▸ hyU')
      let S' : 𝒟 := ⟨S, hS𝒟⟩
      obtain ⟨E, hES, hyE⟩ := mem_sUnion.1 <|
        (sUnion_stackCells (C := S'.1) (fun x ↦ ((D S').strictMono_root x).monotone)).symm ▸
          (show y ∈ Fin.tail ⁻¹' S'.1 from hyS)
      have hEH : E ⊆ H := (subset_or_disjoint_slab_of_mem_stackCells (D S') hES).resolve_right
        fun hd ↦ disjoint_left.1 hd hyE hyH
      exact ⟨E, ⟨S', hES, hEH⟩, hyE⟩
  · -- Each kept stack cell is connected, semianalytic, an analytic submanifold, and sign-invariant.
    intro E hE
    obtain ⟨S, hES, -⟩ := mem_iUnion.1 hE
    obtain ⟨hSc, hSsa, e, hen, hSsub⟩ := h𝒟cell S.1 S.2
    have hSB₀ : S.1 ⊆ B₀ := subset_closure.trans (hclos S.1 S.2)
    have hEconn : IsConnected E :=
      isConnected_of_mem_stackCells hSc (D S).continuous_root (D S).strictMono_root hES
    have hEsa : IsSemianalytic E :=
      (D S).isSemianalytic_of_mem_stackCells hSsa
        (fun x hx ↦ ⟨Sum.elim d (fun _ ↦ 1),
          fun a m _ ↦ analyticOnNhd_coeff_slabPoly hc t₀ ε a m x (hclos S.1 S.2 hx),
          fun a ↦ .of_forall (natDegree_slabPoly_le c t₀ ε a)⟩) hES
    obtain ⟨d', hd'e, hEsub⟩ := (D S).exists_isAnalyticSubmanifold_of_mem_stackCells hSsub
      (fun a m ↦ ((analyticOnNhd_coeff_slabPoly hc t₀ ε a m).mono hSB₀).analyticOnSubmanifold hSsub)
      hES
    exact ⟨hEconn, hEsa, ⟨d', by omega, hEsub⟩,
      fun j ↦ signInvariant_eval_of_mem_stackCells (D S) (.inl j) hES⟩

/-- Pushing forward a finite partition `𝒞₀` of an open set `W` containing `L.symm x₀` along a
continuous linear equivalence `L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)` produces a partition of the open
semianalytic neighborhood `L '' W` of `x₀` into connected semianalytic real analytic
submanifolds. -/
private theorem image_continuousLinearEquiv_partition {m : ℕ} {P : Set (Fin m → ℝ) → Prop}
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) {x₀ : Fin m → ℝ} {V W : Set (Fin m → ℝ)}
    {𝒞₀ : Set (Set (Fin m → ℝ))} (hWo : IsOpen W) (hy₀W : L.symm x₀ ∈ W) (hWV : L '' W ⊆ V)
    (h𝒞₀fin : 𝒞₀.Finite) (h𝒞₀disj : 𝒞₀.PairwiseDisjoint id) (h𝒞₀cov : ⋃₀ 𝒞₀ = W)
    (h𝒞₀cell : ∀ E ∈ 𝒞₀, IsConnected E ∧ IsSemianalytic E ∧
      (∃ d' ≤ m, IsAnalyticSubmanifold d' E) ∧ P (L '' E)) :
    ∃ (U : Set (Fin m → ℝ)) (𝒞 : Set (Set (Fin m → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ (∃ d' ≤ m, IsAnalyticSubmanifold d' C) ∧ P C := by
  let 𝒞 : Set (Set (Fin m → ℝ)) := image L '' 𝒞₀
  have h𝒞cov : ⋃₀ 𝒞 = L '' W := by rw [← image_sUnion, h𝒞₀cov]
  have h𝒞sa : ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧
      (∃ d' ≤ m, IsAnalyticSubmanifold d' C) ∧ P C := by
    rintro _ ⟨E, hE, rfl⟩
    obtain ⟨hEc, hEsa, ⟨d', hd', hEsub⟩, hEP⟩ := h𝒞₀cell E hE
    refine ⟨hEc.image L L.continuous.continuousOn, ?_,
      ⟨d', hd', hEsub.image_continuousLinearEquiv L⟩, hEP⟩
    rw [L.image_eq_preimage_symm]
    exact hEsa.preimage fun x _ ↦ L.symm.analyticAt x
  refine ⟨L '' W, 𝒞, L.toHomeomorph.isOpenMap W hWo, ⟨L.symm x₀, hy₀W, L.apply_symm_apply x₀⟩,
    hWV, ?_, h𝒞₀fin.image _, ?_, h𝒞cov, h𝒞sa⟩
  · rw [← h𝒞cov, sUnion_eq_biUnion]
    exact IsSemianalytic.biUnion (h𝒞₀fin.image _) fun C hC ↦ (h𝒞sa C hC).2.1
  · rintro _ ⟨E₁, hE₁, rfl⟩ _ ⟨E₂, hE₂, rfl⟩ hne
    exact (disjoint_image_iff L.injective).2 (h𝒞₀disj hE₁ hE₂ fun h ↦ hne (h ▸ rfl))

end SlabHelpers

/-! ### Local sign-invariant decomposition in coordinate space `Fin n → ℝ` -/

/-- **Local sign-invariant decomposition of real analytic germs in `Fin n → ℝ`.** Given a finite
family of functions `f i` analytic at `x₀ : Fin n → ℝ` and a neighborhood `V` of `x₀`, there exists
an open semianalytic neighborhood `U ⊆ V` of `x₀` partitioned into finitely many pairwise disjoint
connected semianalytic sets `C ∈ 𝒞`, each a real analytic submanifold of some dimension `d ≤ n`, on
which every `f i` is sign-invariant. -/
theorem exists_isAnalyticSubmanifold_partition_signInvariant.{u} {n : ℕ} {ι : Type u} [Finite ι]
    {f : ι → (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ (∃ d ≤ n, IsAnalyticSubmanifold d C) ∧
        ∀ i, SignInvariant (f i) C := by
  induction n generalizing ι with
  | zero =>
    have hVuniv : univ ⊆ V := fun y _ ↦ Subsingleton.elim y x₀ ▸ mem_of_mem_nhds hV
    refine ⟨univ, {univ}, isOpen_univ, mem_univ x₀, hVuniv, isSemianalytic_univ,
      finite_singleton univ, pairwiseDisjoint_singleton univ id, sUnion_singleton univ, ?_⟩
    rintro _ rfl
    exact ⟨isConnected_univ, isSemianalytic_univ,
      ⟨0, le_rfl, isOpen_univ.isAnalyticSubmanifold univ_nonempty⟩,
      fun _ ↦ subsingleton_of_subsingleton.signInvariant⟩
  | succ n ih =>
    -- Shrink `V` to an open `V₁` where every germ locally zero at `x₀` vanishes identically.
    have hzero : ∀ᶠ x in 𝓝 x₀, ∀ i, f i =ᶠ[𝓝 x₀] 0 → f i x = 0 :=
      eventually_all.2 fun i ↦ by
        by_cases hi : f i =ᶠ[𝓝 x₀] 0
        exacts [hi.mono fun _ hx _ ↦ hx, .of_forall fun _ h ↦ (hi h).elim]
    obtain ⟨V₁, hV₁sub, hV₁o, hx₀V₁⟩ := eventually_nhds_iff.1 (inter_mem hV hzero)
    let ι₁ := {i : ι // ¬ f i =ᶠ[𝓝 x₀] 0}
    -- Put the non-locally-zero germs into simultaneous Weierstrass general position via `L`.
    obtain ⟨L, hord⟩ := exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top
      (f := fun j : ι₁ ↦ f j.1) (fun j ↦ hf j.1) (fun j ↦ j.2)
    set y₀ := L.symm x₀
    obtain ⟨d, c, u₀, B₀, ε, hB₀o, hz₀B₀, hε, hc, hslab⟩ := exists_slab_weierstrass_sign
      (g := fun j : ι₁ ↦ f j.1 ∘ L) (fun j ↦ (hf j.1).comp_of_eq (L.analyticAt y₀)
        (L.apply_symm_apply x₀)) hord
      ((hV₁o.preimage L.continuous).mem_nhds (by simpa [y₀] using hx₀V₁))
    -- Project the augmented slab polynomial family onto `B₀` and decompose inside a closed ball.
    obtain ⟨g, hg_an, hg_delin⟩ := exists_analyticOnNhd_projection_delineation
      (F := slabPoly c (y₀ 0) ε) (d := Sum.elim d (fun _ ↦ 1))
      (fun a m _ ↦ analyticOnNhd_coeff_slabPoly hc (y₀ 0) ε a m)
      (fun a z _ ↦ natDegree_slabPoly_le c (y₀ 0) ε a z)
    obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.1 hB₀o (Fin.tail y₀) hz₀B₀
    obtain ⟨U', 𝒟, hU'o, hz₀U', hU'ball, _, h𝒟fin, h𝒟disj, h𝒟cov, h𝒟cell⟩ :=
      ih (f := fun a : ULift.{u} g ↦ a.down.1) (fun a ↦ hg_an a.down.1 a.down.2 _ hz₀B₀)
        (Metric.ball_mem_nhds (Fin.tail y₀) (half_pos hr₀))
    have hclos (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : closure S ⊆ B₀ :=
      (closure_mono ((subset_sUnion_of_mem hS).trans (h𝒟cov ▸ hU'ball))).trans <|
        Metric.closure_ball_subset_closedBall.trans <|
          (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball₀
    have hdelin (S : 𝒟) : Nonempty (Delineation fun a (x : S.1) ↦ slabPoly c (y₀ 0) ε a x) :=
      hg_delin S.1 (subset_closure.trans (hclos S.1 S.2)) (h𝒟cell S.1 S.2).1.isPreconnected
        fun a ha x hx y hy ↦ by
          rw [← sign_eq_zero_iff (a := a x), ← sign_eq_zero_iff (a := a y),
            signInvariant_def.1 ((h𝒟cell S.1 S.2).2.2.2 (ULift.up ⟨a, ha⟩)) x hx y hy]
    let D (S : 𝒟) := Classical.choice (hdelin S)
    obtain ⟨𝒞₀, h𝒞₀fin, h𝒞₀disj, h𝒞₀cov, h𝒞₀cell⟩ := lift_slab_partition hc h𝒟fin h𝒟disj h𝒟cov
      hclos (fun S hS ↦ ⟨(h𝒟cell S hS).1, (h𝒟cell S hS).2.1, (h𝒟cell S hS).2.2.1⟩) D
    set W := (Fin.tail ⁻¹' U') ∩ {y : Fin (n + 1) → ℝ | y 0 ∈ Ioo (y₀ 0 - ε) (y₀ 0 + ε)}
    have hWB₀ (y : Fin (n + 1) → ℝ) (hy : y ∈ W) : Fin.tail y ∈ B₀ :=
      hball₀ ((Metric.ball_subset_ball (half_lt_self hr₀).le) (hU'ball hy.1))
    refine image_continuousLinearEquiv_partition L
      ((hU'o.preimage (continuous_pi fun k ↦ continuous_apply k.succ)).inter
        ((isOpen_Ioo).preimage (continuous_apply 0)))
      ⟨hz₀U', by simp [y₀, hε]⟩
      (fun _ ⟨y, hyW, hxy⟩ ↦ hxy ▸ (hV₁sub _ (hslab y (hWB₀ y hyW) hyW.2).1).1)
      h𝒞₀fin h𝒞₀disj h𝒞₀cov fun E hE ↦ ?_
    obtain ⟨hEc, hEsa, hEsub, hEsign⟩ := h𝒞₀cell E hE
    have hEW : E ⊆ W := h𝒞₀cov ▸ subset_sUnion_of_mem hE
    refine ⟨hEc, hEsa, hEsub, fun i ↦ ?_⟩
    by_cases hi : f i =ᶠ[𝓝 x₀] 0
    · exact (signInvariant_const 0).congr fun x ⟨y, hyE, hxy⟩ ↦
        hxy ▸ ((hV₁sub _ (hslab y (hWB₀ y (hEW hyE)) (hEW hyE).2).1).2 i hi).symm
    · rw [signInvariant_image, signInvariant_def]
      intro y₁ hy₁ y₂ hy₂
      change SignType.sign ((f i ∘ L) y₁) = SignType.sign ((f i ∘ L) y₂)
      rw [(hslab y₁ (hWB₀ y₁ (hEW hy₁)) (hEW hy₁).2).2 ⟨i, hi⟩,
        (hslab y₂ (hWB₀ y₂ (hEW hy₂)) (hEW hy₂).2).2 ⟨i, hi⟩,
        signInvariant_def.1 (hEsign ⟨i, hi⟩) y₁ hy₁ y₂ hy₂]

/-- **Simultaneous local analytic submanifold partition for semianalytic germs in `Fin n → ℝ`.**
Given finitely many sets `s i` semianalytic at `x₀ : Fin n → ℝ` and a neighborhood `V` of `x₀`,
there exists an open semianalytic neighborhood `U ⊆ V` of `x₀` partitioned into finitely many
pairwise disjoint connected semianalytic real analytic submanifolds, each lying either inside or
outside every `s i`. -/
theorem SemianalyticAt.exists_isAnalyticSubmanifold_partition {n : ℕ} {ι : Type*} [Finite ι]
    {s : ι → Set (Fin n → ℝ)} {x₀ : Fin n → ℝ} {V : Set (Fin n → ℝ)}
    (hs : ∀ i, SemianalyticAt (s i) x₀) (hV : V ∈ 𝓝 x₀) :
    ∃ (U : Set (Fin n → ℝ)) (𝒞 : Set (Set (Fin n → ℝ))),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ (∃ d ≤ n, IsAnalyticSubmanifold d C) ∧
        ∀ i, C ⊆ s i ∨ Disjoint C (s i) := by
  classical
  cases nonempty_fintype ι
  choose W hW t ht hst using fun i ↦ semianalyticAt_def.1 (hs i)
  choose m f hf Φ ht_eq using fun i ↦ (ht i).exists_eq_setOf_sign
  have hfx (p : Σ i, Fin (m i)) : AnalyticAt ℝ (f p.1 p.2) x₀ :=
    hf p.1 p.2 x₀ (mem_of_mem_nhds (hW p.1))
  obtain ⟨U, 𝒞, hUo, hx₀U, hUW, hUsa, h𝒞fin, h𝒞disj, h𝒞cov, h𝒞cell⟩ :=
    exists_isAnalyticSubmanifold_partition_signInvariant (f := fun p : Σ i, Fin (m i) ↦ f p.1 p.2)
      hfx (inter_mem hV (iInter_mem.2 hW))
  refine ⟨U, 𝒞, hUo, hx₀U, hUW.trans inter_subset_left, hUsa, h𝒞fin, h𝒞disj, h𝒞cov, fun C hC ↦ ?_⟩
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

private theorem filter_subset_partition {X : Type*} {s U : Set X} {𝒟 : Set (Set X)}
    (h𝒟fin : 𝒟.Finite) (h𝒟disj : 𝒟.PairwiseDisjoint id) (h𝒟cov : ⋃₀ 𝒟 = U)
    (hcompat : ∀ C ∈ 𝒟, C ⊆ s ∨ Disjoint C s) :
    {C ∈ 𝒟 | C ⊆ s}.Finite ∧ {C ∈ 𝒟 | C ⊆ s}.PairwiseDisjoint id ∧
      ⋃₀ {C ∈ 𝒟 | C ⊆ s} = s ∩ U := by
  refine ⟨h𝒟fin.subset (sep_subset _ _), h𝒟disj.subset (sep_subset _ _), ?_⟩
  ext y
  simp only [mem_sUnion, mem_sep_iff, mem_inter_iff]
  refine ⟨fun ⟨C, ⟨hC𝒟, hCs⟩, hyC⟩ ↦ ⟨hCs hyC, h𝒟cov ▸ mem_sUnion.2 ⟨C, hC𝒟, hyC⟩⟩, ?_⟩
  rintro ⟨hys, hyU⟩
  obtain ⟨C, hC𝒟, hyC⟩ := mem_sUnion.1 (h𝒟cov.symm ▸ hyU)
  exact ⟨C, ⟨hC𝒟, (hcompat C hC𝒟).resolve_right fun hd ↦ disjoint_left.1 hd hyC hys⟩, hyC⟩

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
  obtain ⟨U, 𝒟, hUo, hx₀U, hUV, hUsa, h𝒟fin, h𝒟disj, h𝒟cov, h𝒟cell⟩ :=
    SemianalyticAt.exists_isAnalyticSubmanifold_partition (fun _ : Unit ↦ hs) hV
  obtain ⟨h𝒞fin, h𝒞disj, h𝒞cov⟩ :=
    filter_subset_partition h𝒟fin h𝒟disj h𝒟cov fun C hC ↦ (h𝒟cell C hC).2.2.2 ()
  have hsUsa : IsSemianalytic (s ∩ U) := by
    rw [← h𝒞cov, sUnion_eq_biUnion]
    exact .biUnion h𝒞fin fun C hC ↦ (h𝒟cell C hC.1).2.1
  exact ⟨U, {C ∈ 𝒟 | C ⊆ s}, hUo, hx₀U, hUV, hUsa, hsUsa, h𝒞fin, h𝒞disj, h𝒞cov,
    fun C hC ↦ ⟨(h𝒟cell C hC.1).1, (h𝒟cell C hC.1).2.1, (h𝒟cell C hC.1).2.2.1⟩⟩

/-! ### Coordinate-free local decompositions in finite-dimensional real normed spaces -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem image_symm_coord_partition {n : ℕ} {P : Set E → Prop}
    (φ : E ≃L[ℝ] (Fin n → ℝ)) {x₀ : E} {V : Set E} {U₀ : Set (Fin n → ℝ)}
    {𝒞₀ : Set (Set (Fin n → ℝ))} (hU₀o : IsOpen U₀) (hx₀U₀ : φ x₀ ∈ U₀)
    (hU₀V : U₀ ⊆ φ.symm ⁻¹' V) (hU₀sa : IsSemianalytic U₀)
    (h𝒞₀fin : 𝒞₀.Finite) (h𝒞₀disj : 𝒞₀.PairwiseDisjoint id) (h𝒞₀cov : ⋃₀ 𝒞₀ = U₀)
    (h𝒞₀cell : ∀ C₀ ∈ 𝒞₀, IsConnected C₀ ∧ IsSemianalytic C₀ ∧
      (∃ d ≤ n, IsAnalyticSubmanifold d C₀) ∧ P (φ.symm '' C₀)) :
    ∃ (U : Set E) (𝒞 : Set (Set E)),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ V ∧ IsSemianalytic U ∧
      𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧ ⋃₀ 𝒞 = U ∧
      ∀ C ∈ 𝒞, IsConnected C ∧ IsSemianalytic C ∧ IsLocallyClosed C ∧ P C := by
  refine ⟨φ.symm '' U₀, image φ.symm '' 𝒞₀, φ.symm.toHomeomorph.isOpenMap U₀ hU₀o,
    ⟨φ x₀, hx₀U₀, φ.symm_apply_apply x₀⟩, image_subset_iff.2 hU₀V, ?_,
    h𝒞₀fin.image _, ?_, by rw [← image_sUnion, h𝒞₀cov], ?_⟩
  · rw [φ.symm.image_eq_preimage_symm]
    exact hU₀sa.preimage fun x _ ↦ φ.analyticAt x
  · rintro _ ⟨E₁, hE₁, rfl⟩ _ ⟨E₂, hE₂, rfl⟩ hne
    exact (disjoint_image_iff φ.symm.injective).2 (h𝒞₀disj hE₁ hE₂ fun h ↦ hne (h ▸ rfl))
  · rintro _ ⟨C₀, hC₀, rfl⟩
    obtain ⟨hCc, hCsa, ⟨_, _, hCsub⟩, hCP⟩ := h𝒞₀cell C₀ hC₀
    refine ⟨hCc.image φ.symm φ.symm.continuous.continuousOn, ?_, ?_, hCP⟩
    · rw [φ.symm.image_eq_preimage_symm]
      exact hCsa.preimage fun x _ ↦ φ.analyticAt x
    · rw [φ.symm.image_eq_preimage_symm]
      exact hCsub.isLocallyClosed.preimage φ.continuous

variable [FiniteDimensional ℝ E]

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
  obtain ⟨U₀, 𝒞₀, hU₀o, hx₀U₀, hU₀V, hU₀sa, h𝒞₀fin, h𝒞₀disj, h𝒞₀cov, h𝒞₀cell⟩ :=
    exists_isAnalyticSubmanifold_partition_signInvariant (f := fun i ↦ f i ∘ φ.symm)
      (fun i ↦ (hf i).comp_of_eq (φ.symm.analyticAt (φ x₀)) (φ.symm_apply_apply x₀))
      (φ.toHomeomorph.symm.continuous.continuousAt.preimage_mem_nhds
        (by simpa [φ.symm_apply_apply] using hV))
  refine image_symm_coord_partition φ hU₀o hx₀U₀ hU₀V hU₀sa h𝒞₀fin h𝒞₀disj h𝒞₀cov fun C₀ hC₀ ↦ ?_
  obtain ⟨hCc, hCsa, hCsub, hCsign⟩ := h𝒞₀cell C₀ hC₀
  exact ⟨hCc, hCsa, hCsub, fun i ↦ signInvariant_image.2 (hCsign i)⟩

/-- **Simultaneous local connected partition for semianalytic germs.** Given finitely many sets
`s i` semianalytic at a point `x₀` of a finite-dimensional real normed space `E` and `V ∈ 𝓝 x₀`,
there exists an open semianalytic neighborhood `U ⊆ V` of `x₀` partitioned into finitely many
pairwise disjoint connected, semianalytic, locally closed sets, each lying inside or outside every
`s i`. -/
theorem SemianalyticAt.exists_isConnected_partition {ι : Type*} [Finite ι]
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
  obtain ⟨U₀, 𝒞₀, hU₀o, hx₀U₀, hU₀V, hU₀sa, h𝒞₀fin, h𝒞₀disj, h𝒞₀cov, h𝒞₀cell⟩ :=
    SemianalyticAt.exists_isAnalyticSubmanifold_partition hs'
      (φ.toHomeomorph.symm.continuous.continuousAt.preimage_mem_nhds
        (by simpa [φ.symm_apply_apply] using hV))
  refine image_symm_coord_partition φ hU₀o hx₀U₀ hU₀V hU₀sa h𝒞₀fin h𝒞₀disj h𝒞₀cov fun C₀ hC₀ ↦ ?_
  obtain ⟨hCc, hCsa, hCsub, hCcompat⟩ := h𝒞₀cell C₀ hC₀
  refine ⟨hCc, hCsa, hCsub, fun i ↦ ?_⟩
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
    SemianalyticAt.exists_isConnected_partition (fun _ : Unit ↦ hs) hV
  obtain ⟨h𝒞fin, h𝒞disj, h𝒞cov⟩ :=
    filter_subset_partition h𝒟fin h𝒟disj h𝒟cov fun C hC ↦ (h𝒟cell C hC).2.2.2 ()
  have hsUsa : IsSemianalytic (s ∩ U) := by
    rw [← h𝒞cov, sUnion_eq_biUnion]
    exact .biUnion h𝒞fin fun C hC ↦ (h𝒟cell C hC.1).2.1
  exact ⟨U, {C ∈ 𝒟 | C ⊆ s}, hUo, hx₀U, hUV, hUsa, hsUsa, h𝒞fin, h𝒞disj, h𝒞cov,
    fun C hC ↦ ⟨(h𝒟cell C hC.1).1, (h𝒟cell C hC.1).2.1, (h𝒟cell C hC.1).2.2.1⟩⟩

end FiniteDimensional

end TauCeti
