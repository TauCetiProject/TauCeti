/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import TauCeti.Algebra.Module.DiscreteValuationRing.ElementaryDivisors
import TauCeti.Algebra.Order.BigOperators.Sum.Min
import TauCeti.RingTheory.Ideal.Operations.Pi
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.Length.SMulTop

/-!
# Demazure filtrations of torsion modules

Let `A` be a commutative ring with an ideal `I`, let `M` be an `A`-module, and let
`μ : ι → ℕ` be a finite family of natural numbers, a *type*. Its column lengths are
`#{j | i < μ j}`, the number of parts exceeding `i`. A *Demazure filtration of type `μ`* on `M` is
a decreasing chain of submodules
`M = N 0 ⊇ N 1 ⊇ ⋯ ⊇ N i = 0` (for `i` at least every part of `μ`)
with `I • N i ≤ N (i + 1)`, whose graded pieces `N i ⧸ N (i + 1)` are finite locally free over
`A ⧸ I` of the column ranks `#{j | i < μ j}`. Since `I` kills each graded piece, local freeness is
stated for its base change `(A ⧸ I) ⊗[A] (N i ⧸ N (i + 1))`, which is the graded piece itself.

For the Witt vectors `A = W(R)` of a perfect ring `R`, the ideal `I = (p)` and an isogeny cokernel
`M = W(R)ⁿ ⧸ Λ`, these filtrations are the points of the Demazure resolution of the bounded Witt
vector affine Grassmannian of Bhatt and Scholze: the resolution classifies a lattice together
with such a filtration of its quotient, and maps onto the locus of quotient type `≤ μ`.

At a geometric point the base is a field, and this file shows the filtration is then determined by
its type whenever the module has exact type `μ`. More precisely:

* For a maximal ideal `I`, the graded pieces have length `#{j | i < μ j}` over `A`, so
  `M ⧸ N i` has length `∑ j, min i (μ j)` and `M` has length `∑ j, μ j`. Since always
  `I ^ i • ⊤ ≤ N i`, the filtration is the `I`-adic one at every `i` where `M ⧸ I ^ i • ⊤` has the
  same length `∑ j, min i (μ j)`.
* Over a discrete valuation ring `A` with maximal ideal `𝔪` and `M ≃ ∏ j, A ⧸ 𝔪 ^ μ j`, the
  `𝔪`-adic filtration `𝔪 ^ i • ⊤` is a Demazure filtration of type `μ`, and it is the only one.
  This is the statement that the Demazure resolution is an isomorphism over the locus of exact
  type, at geometric points.

In general, if `M` has a lower type a Demazure filtration of type `μ` need not be unique: the
first step chooses a quotient of `M ⧸ I • M` of the prescribed rank, rather than `M ⧸ I • M`
itself.

## Main definitions

* `Ideal.DemazureFiltration I μ M`: the Demazure filtrations of type `μ` on `M`.
* `Ideal.DemazureFiltration.adic`: over a discrete valuation ring, the `𝔪`-adic filtration of a
  module of exact type `μ`.

## Main results

* `Ideal.DemazureFiltration.pow_smul_top_le`: `I ^ i • ⊤ ≤ N i`.
* `Ideal.DemazureFiltration.subsingleton_of_forall_eq_zero`: a filtration of type zero forces
  `M = 0`.
* `Ideal.DemazureFiltration.nonempty_iff_of_forall_le_one`: a one-column filtration exists exactly
  when `I • M = 0` and `M` is finite locally free over `A ⧸ I` of the column rank.
* `Ideal.DemazureFiltration.length_quotient_N`: for maximal `I`, `M ⧸ N i` has length
  `∑ j, min i (μ j)`.
* `Ideal.DemazureFiltration.N_eq_pow_smul_top_of_length_eq`: for maximal `I`, `N i = I ^ i • ⊤`
  whenever `M ⧸ I ^ i • ⊤` has length `∑ j, min i (μ j)`.
* `Ideal.DemazureFiltration.N_eq_maximalIdeal_pow_smul_top`: over a discrete valuation ring, every
  Demazure filtration of a module of exact type `μ` is the `𝔪`-adic filtration.

## References

* B. Bhatt, P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math. 209
  (2017), §7, especially 7.10–7.13.
-/

public section

open Finset Module TensorProduct

namespace Ideal

variable {A : Type*} [CommRing A] (I : Ideal A) {ι : Type*} [Fintype ι] (μ : ι → ℕ)
  (M : Type*) [AddCommGroup M] [Module A M]

namespace Filtration

variable {I M}

/-- `I` kills every graded piece `N i ⧸ N (i + 1)` of an `I`-filtration. -/
theorem smul_top_gr_eq_bot (F : I.Filtration M) (i : ℕ) :
    I • (⊤ : Submodule A (↥(F.N i) ⧸ (F.N (i + 1)).comap (F.N i).subtype)) = ⊥ := by
  refine eq_bot_iff.2 (Submodule.smul_le.2 fun r hr x _ ↦ ?_)
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    exact F.smul_le i (Submodule.smul_mem_smul hr x.property)

end Filtration

/-- A **Demazure filtration of type `μ`** on an `A`-module `M`: an `I`-filtration
`M = N 0 ⊇ N 1 ⊇ ⋯` that reaches `0` at every index bounding all parts of `μ`, whose graded
pieces `N i ⧸ N (i + 1)` are finite locally free over `A ⧸ I` of rank `#{j | i < μ j}`. Local
freeness is stated for the base change `(A ⧸ I) ⊗[A] (N i ⧸ N (i + 1))`; as `I` kills the graded
piece, this base change is the graded piece itself. -/
structure DemazureFiltration extends I.Filtration M where
  /-- The filtration starts at the whole module. -/
  N_zero : N 0 = ⊤
  /-- The filtration ends at zero once the index bounds every part of the type. -/
  N_eq_bot_of_forall_le : ∀ i, (∀ j, μ j ≤ i) → N i = ⊥
  /-- The graded pieces are finite over `A ⧸ I`. -/
  finite_gr : ∀ i,
    Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] (↥(N i) ⧸ (N (i + 1)).comap (N i).subtype))
  /-- The graded pieces are projective over `A ⧸ I`. -/
  projective_gr : ∀ i,
    Module.Projective (A ⧸ I) ((A ⧸ I) ⊗[A] (↥(N i) ⧸ (N (i + 1)).comap (N i).subtype))
  /-- The `i`-th graded piece has rank `#{j | i < μ j}` at every prime of `A ⧸ I`. -/
  rankAtStalk_gr : ∀ i 𝔭, rankAtStalk (R := A ⧸ I)
    ((A ⧸ I) ⊗[A] (↥(N i) ⧸ (N (i + 1)).comap (N i).subtype)) 𝔭 = #{j | i < μ j}

namespace DemazureFiltration

variable {I μ M}

attribute [simp] N_zero

/-- A Demazure filtration is determined by its underlying `I`-filtration. -/
theorem toFiltration_injective :
    Function.Injective (toFiltration : I.DemazureFiltration μ M → I.Filtration M) := by
  rintro ⟨F, -⟩ ⟨G, -⟩ rfl
  rfl

/-- Two Demazure filtrations agree when all their submodules agree. -/
@[ext]
theorem ext {F G : I.DemazureFiltration μ M} (h : ∀ i, F.N i = G.N i) : F = G :=
  toFiltration_injective (Ideal.Filtration.ext (funext h))

variable (F : I.DemazureFiltration μ M)

/-- The `I`-adic filtration lies below every Demazure filtration. -/
theorem pow_smul_top_le (i : ℕ) : I ^ i • (⊤ : Submodule A M) ≤ F.N i := by
  simpa [F.N_zero] using F.pow_smul_le i 0

/-- A Demazure filtration of type zero exists only on the zero module. -/
theorem subsingleton_of_forall_eq_zero (F : I.DemazureFiltration μ M) (hμ : ∀ j, μ j = 0) :
    Subsingleton M := by
  have h := F.N_eq_bot_of_forall_le 0 fun j ↦ (hμ j).le
  rw [F.N_zero] at h
  exact (Submodule.subsingleton_iff A).1 (subsingleton_iff_bot_eq_top.1 h.symm)

/-- A graded piece `P ⧸ Q` with `P = ⊤` and `Q = ⊥` is the whole module. -/
private noncomputable def grEquivOfEqTop {P Q : Submodule A M} (hP : P = ⊤) (hQ : Q = ⊥) :
    (↥P ⧸ Q.comap P.subtype) ≃ₗ[A] M := by
  subst hP hQ
  exact Submodule.quotEquivOfEqBot _ (by simp) ≪≫ₗ LinearEquiv.ofTop ⊤ rfl

/-- A graded piece `P ⧸ Q` with `P = ⊥` is zero, so its base change is finite projective of
rank zero. -/
private theorem gr_of_eq_bot {P Q : Submodule A M} (hP : P = ⊥) :
    Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] (↥P ⧸ Q.comap P.subtype)) ∧
      Module.Projective (A ⧸ I) ((A ⧸ I) ⊗[A] (↥P ⧸ Q.comap P.subtype)) ∧
      ∀ 𝔭, rankAtStalk (R := A ⧸ I) ((A ⧸ I) ⊗[A] (↥P ⧸ Q.comap P.subtype)) 𝔭 = 0 := by
  subst hP
  exact ⟨inferInstance, inferInstance, fun _ ↦ by simp⟩

/-- **One-column filtrations.** If every part of `μ` is at most one, a Demazure filtration of
type `μ` on `M` exists exactly when `I` kills `M` and `M` is finite locally free over `A ⧸ I` of
rank `#{j | 0 < μ j}`. The filtration is then `M ⊇ 0 ⊇ 0 ⊇ ⋯`. -/
theorem nonempty_iff_of_forall_le_one (hμ : ∀ j, μ j ≤ 1) :
    Nonempty (I.DemazureFiltration μ M) ↔ I • (⊤ : Submodule A M) = ⊥ ∧
      Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ Module.Projective (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧
      ∀ 𝔭, rankAtStalk (R := A ⧸ I) ((A ⧸ I) ⊗[A] M) 𝔭 = #{j | 0 < μ j} := by
  constructor
  · rintro ⟨F⟩
    have h₁ : F.N 1 = ⊥ := F.N_eq_bot_of_forall_le 1 hμ
    let e := (grEquivOfEqTop F.N_zero h₁).baseChange A (A ⧸ I)
    have := F.finite_gr 0
    have := F.projective_gr 0
    refine ⟨eq_bot_iff.2 ?_, Module.Finite.equiv e, Module.Projective.of_equiv' e, fun 𝔭 ↦ ?_⟩
    · simpa [h₁] using F.pow_smul_top_le 1
    · rw [← rankAtStalk_eq_of_equiv e, F.rankAtStalk_gr]
  · rintro ⟨hI, _, _, hrank⟩
    -- The filtration `M ⊇ 0 ⊇ 0 ⊇ ⋯`; its zeroth graded piece is `M`, the later ones vanish.
    let e := (grEquivOfEqTop (ite_eq_left rfl : (if 0 = 0 then ⊤ else ⊥ : Submodule A M) = ⊤)
      (ite_eq_right one_ne_zero : (if 1 = 0 then ⊤ else ⊥ : Submodule A M) = ⊥)).baseChange A
        (A ⧸ I)
    refine ⟨{
      N := fun i ↦ if i = 0 then ⊤ else ⊥
      mono := fun i ↦ by simp
      smul_le := fun i ↦ by split_ifs <;> simp [hI]
      N_zero := ite_eq_left rfl
      N_eq_bot_of_forall_le := fun i hi ↦ ?_
      finite_gr := fun i ↦ ?_
      projective_gr := fun i ↦ ?_
      rankAtStalk_gr := fun i 𝔭 ↦ ?_ }⟩
    · rcases eq_or_ne i 0 with rfl | hi0
      · -- Type zero: the rank condition forces `M = 0`.
        have h0 : rankAtStalk (R := A ⧸ I) ((A ⧸ I) ⊗[A] M) = 0 := funext fun 𝔭 ↦ by
          rw [hrank, Pi.zero_apply, card_eq_zero, filter_eq_empty_iff]
          exact fun j _ ↦ (hi j).not_gt
        have := rankAtStalk_eq_zero_iff_subsingleton.1 h0
        have : Subsingleton M := ((Submodule.quotEquivOfEqBot _ hI).symm ≪≫ₗ
          (TensorProduct.quotTensorEquivQuotSMul M I).symm).toEquiv.subsingleton
        exact Subsingleton.elim _ _
      · exact ite_eq_right hi0
    · rcases i with _ | i
      · exact Module.Finite.equiv e.symm
      · exact (gr_of_eq_bot (ite_eq_right i.succ_ne_zero)).1
    · rcases i with _ | i
      · exact Module.Projective.of_equiv' e.symm
      · exact (gr_of_eq_bot (ite_eq_right i.succ_ne_zero)).2.1
    · rcases i with _ | i
      · exact (congrFun (rankAtStalk_eq_of_equiv e) 𝔭).trans (hrank 𝔭)
      · rw [(gr_of_eq_bot (ite_eq_right i.succ_ne_zero)).2.2, eq_comm, card_eq_zero,
          filter_eq_empty_iff]
        exact fun j _ ↦ ((hμ j).trans (Nat.le_add_left 1 i)).not_gt

end DemazureFiltration

section IsMaximal

variable {I μ M} [I.IsMaximal]

namespace DemazureFiltration

/-- **Demazure filtrations at a field point.** For a maximal ideal `I`, an `I`-filtration from `⊤`
to `⊥` whose `i`-th graded piece has length `#{j | i < μ j}` over `A` is a Demazure filtration of
type `μ`: over the field `A ⧸ I` the graded pieces are vector spaces, of these dimensions. -/
noncomputable def ofLength (F : I.Filtration M) (h₀ : F.N 0 = ⊤)
    (hbot : ∀ i, (∀ j, μ j ≤ i) → F.N i = ⊥)
    (hlen : ∀ i, Module.length A (↥(F.N i) ⧸ (F.N (i + 1)).comap (F.N i).subtype) =
      #{j | i < μ j}) :
    I.DemazureFiltration μ M where
  toFiltration := F
  N_zero := h₀
  N_eq_bot_of_forall_le := hbot
  finite_gr i := TauCeti.finite_quotient_tensor_of_length_ne_top I
    ((hlen i).trans_ne (ENat.natCast_ne_top _))
  projective_gr _ := by
    let := Ideal.Quotient.field I
    exact Module.Projective.of_free
  rankAtStalk_gr i 𝔭 := by
    have := TauCeti.finite_quotient_tensor_of_length_ne_top I
      ((hlen i).trans_ne (ENat.natCast_ne_top _))
    exact_mod_cast (TauCeti.rankAtStalk_quotient_tensor_eq_length I (F.smul_top_gr_eq_bot i)
      𝔭).trans (hlen i)

@[simp]
theorem toFiltration_ofLength (F : I.Filtration M) (h₀ : F.N 0 = ⊤)
    (hbot : ∀ i, (∀ j, μ j ≤ i) → F.N i = ⊥)
    (hlen : ∀ i, Module.length A (↥(F.N i) ⧸ (F.N (i + 1)).comap (F.N i).subtype) =
      #{j | i < μ j}) :
    (ofLength F h₀ hbot hlen).toFiltration = F :=
  (rfl)

variable (F : I.DemazureFiltration μ M)

/-- For a maximal ideal `I`, the `i`-th graded piece of a Demazure filtration has length
`#{j | i < μ j}` over `A`. Together with `ofLength`, this says that at a field point the graded
rank conditions are exactly these length conditions. -/
theorem length_gr (i : ℕ) :
    Module.length A (↥(F.N i) ⧸ (F.N (i + 1)).comap (F.N i).subtype) = #{j | i < μ j} := by
  have := F.finite_gr i
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsMaximal.ne_top ‹_›)
  rw [← TauCeti.rankAtStalk_quotient_tensor_eq_length I (F.toFiltration.smul_top_gr_eq_bot i)
    (Classical.arbitrary _), F.rankAtStalk_gr]

/-- For a maximal ideal `I`, the quotient `M ⧸ N i` by the `i`-th step of a Demazure filtration
has length `∑ j, min i (μ j)`. -/
theorem length_quotient_N (i : ℕ) :
    Module.length A (M ⧸ F.N i) = (∑ j, min i (μ j) : ℕ) := by
  induction i with
  | zero => simp [F.N_zero]
  | succ i ih =>
    rw [TauCeti.length_quotient_eq_length_quotient_comap_subtype_add (F.mono i), F.length_gr, ih,
      sum_min_add_one, Nat.cast_add, add_comm]

/-- For a maximal ideal `I`, a module carrying a Demazure filtration of type `μ` has length
`∑ j, μ j`. -/
theorem length_eq_sum (F : I.DemazureFiltration μ M) : Module.length A M = (∑ j, μ j : ℕ) := by
  have h := F.length_quotient_N (univ.sup μ)
  rw [F.N_eq_bot_of_forall_le _ fun j ↦ le_sup (mem_univ j),
    (Submodule.quotEquivOfEqBot _ rfl).length_eq] at h
  rw [h, sum_congr rfl fun j _ ↦ min_eq_right (le_sup (mem_univ j))]

/-- For a maximal ideal `I`, the `i`-th step of a Demazure filtration of type `μ` is the `I`-adic
one, `I ^ i • ⊤`, whenever `M ⧸ I ^ i • ⊤` has the length `∑ j, min i (μ j)` of a module of exact
type `μ`. -/
theorem N_eq_pow_smul_top_of_length_eq {i : ℕ}
    (h : Module.length A (M ⧸ I ^ i • (⊤ : Submodule A M)) = (∑ j, min i (μ j) : ℕ)) :
    F.N i = I ^ i • ⊤ := by
  refine le_antisymm ?_ (F.pow_smul_top_le i)
  have hlen := TauCeti.length_quotient_eq_length_quotient_comap_subtype_add (F.pow_smul_top_le i)
  rw [h, F.length_quotient_N] at hlen
  have h0 : Module.length A (↥(F.N i) ⧸ (I ^ i • ⊤ : Submodule A M).comap (F.N i).subtype) = 0 :=
    WithTop.add_right_cancel (ENat.natCast_ne_top _) (hlen.symm.trans (zero_add _).symm)
  rwa [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Submodule.comap_subtype_eq_top] at h0

end DemazureFiltration

end IsMaximal

section DiscreteValuationRing

open IsLocalRing

variable {μ M} [IsDomain A] [IsDiscreteValuationRing A]

namespace DemazureFiltration

/-- **Uniqueness over the exact type.** Over a discrete valuation ring with maximal ideal `𝔪`,
every Demazure filtration of type `μ` on a module `M ≃ ∏ j, A ⧸ 𝔪 ^ μ j` is the `𝔪`-adic
filtration. -/
theorem N_eq_maximalIdeal_pow_smul_top (F : (maximalIdeal A).DemazureFiltration μ M)
    (f : M ≃ₗ[A] ∀ j, A ⧸ maximalIdeal A ^ μ j) (i : ℕ) :
    F.N i = maximalIdeal A ^ i • ⊤ :=
  F.N_eq_pow_smul_top_of_length_eq
    (TauCeti.IsDiscreteValuationRing.length_quotient_pow_maximalIdeal_smul_top f i)

/-- **Existence over the exact type.** Over a discrete valuation ring with maximal ideal `𝔪`, the
`𝔪`-adic filtration `𝔪 ^ i • ⊤` of a module `M ≃ ∏ j, A ⧸ 𝔪 ^ μ j` is a Demazure filtration of
type `μ`. -/
noncomputable def adic (f : M ≃ₗ[A] ∀ j, A ⧸ maximalIdeal A ^ μ j) :
    (maximalIdeal A).DemazureFiltration μ M :=
  ofLength ((maximalIdeal A).stableFiltration ⊤) (by simp)
    (fun i hi ↦ by
      rw [stableFiltration_N, ← (Submodule.map_injective_of_injective f.injective).eq_iff,
        Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, Submodule.map_bot]
      exact Submodule.smul_top_pi_quotient_eq_bot fun j ↦ Ideal.pow_le_pow_right (hi j))
    (fun i ↦ by
      have h :=
        TauCeti.IsDiscreteValuationRing.length_pow_maximalIdeal_smul_top_quotient_smul_top f i
      rw [← Submodule.comap_subtype_smul, ← Submodule.mul_smul, ← pow_succ'] at h
      -- `stableFiltration ⊤` has `N i = 𝔪 ^ i • ⊤` by definition.
      exact h)

@[simp]
theorem adic_N (f : M ≃ₗ[A] ∀ j, A ⧸ maximalIdeal A ^ μ j) (i : ℕ) :
    (adic f).N i = maximalIdeal A ^ i • ⊤ :=
  (rfl)

/-- Over a discrete valuation ring, a module `M ≃ ∏ j, A ⧸ 𝔪 ^ μ j` of exact type `μ` carries
exactly one Demazure filtration of type `μ`, the `𝔪`-adic one. -/
@[instance_reducible]
noncomputable def uniqueOfLinearEquiv (f : M ≃ₗ[A] ∀ j, A ⧸ maximalIdeal A ^ μ j) :
    Unique ((maximalIdeal A).DemazureFiltration μ M) where
  default := adic f
  uniq F := ext fun i ↦ by rw [adic_N, F.N_eq_maximalIdeal_pow_smul_top f]

end DemazureFiltration

end DiscreteValuationRing

end Ideal
