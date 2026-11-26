/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.CategoryTheory.Filtration.Decreasing
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

/-!
# Checks: exhaustive, separated and complete filtrations of modules

An antitone family `F : ℤ → Submodule R M` of submodules is a decreasingly filtered object of
`ModuleCat R` (`TauCeti.Examples.DecreasingFiltration.ofSubmodules`), whose step `F^p` is the
subobject of `F p` (`step_ofSubmodules`). Through Mathlib's order isomorphism
`ModuleCat.subobjectModule` between subobjects and submodules, the filtration is exhaustive
exactly when no proper submodule contains every `F p`
(`isExhaustive_ofSubmodules_iff`), and separated exactly when no nonzero submodule lies in every
`F p` (`isSeparated_ofSubmodules_iff`).

Checks on `ℤ` as a `ℤ`-module:

* the constant filtration `F^p = ℤ` is exhaustive and not separated
  (`isExhaustive_const_top`, `not_isSeparated_const_top`);
* the zero filtration `F^p = 0` is separated and not exhaustive
  (`isSeparated_const_bot`, `not_isExhaustive_const_bot`);
* for `ℓ ≥ 2`, the `ℓ`-adic filtration `F^p = ℓ^p ℤ` for `p ≥ 0`, and `ℤ` for `p ≤ 0`, is
  exhaustive and separated (`isExhaustive_adicFiltration`, `isSeparated_adicFiltration`): an
  integer divisible by every power of `ℓ` is `0`. It is not complete
  (`not_isComplete_adicFiltration`): the partial sums `∑_{i < p} (-ℓ)^i` of the `ℓ`-adic expansion
  of `1 / (1 + ℓ)` are a compatible family in the quotients `ℤ / ℓ^p` that no integer represents.

Through `ModuleCat.cokernelIsoRangeQuotient`, two maps `R ⟶ M`, `1 ↦ x` and `1 ↦ y`, agree in the
quotient `M / F^p` of the filtration exactly when `x - y ∈ F p`
(`toSpan_comp_quotientCone_π_eq_iff`).
-/

public section

open CategoryTheory Opposite

namespace TauCeti.Examples.DecreasingFiltration

universe u

variable {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The decreasingly filtered module with steps an antitone family `F` of submodules. -/
noncomputable abbrev ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) :
    FilteredObject (ModuleCat.{u} R) ℤᵒᵖ where
  X := ModuleCat.of R M
  filtration.toMonoOver :=
    { obj p := MonoOver.mk (hf := ModuleCat.mono_as_hom'_subtype (X := ModuleCat.of R M) (F p.unop))
        (ModuleCat.ofHom (F p.unop).subtype)
      map {p q} f := MonoOver.homMk
        (ModuleCat.ofHom (Submodule.inclusion (hF (leOfHom f.unop)))) rfl }

/-- The inclusion of the step `F^p` of `ofSubmodules F hF` is the inclusion of `F p`. -/
theorem stepι_ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) (p : ℤ) :
    (ofSubmodules F hF).stepι (op p) = ModuleCat.ofHom (F p).subtype := by
  rw [← FilteredObject.filtration_ι_app]
  rfl

/-- The step `F^p` of `ofSubmodules F hF` is the subobject of `F p`. -/
theorem step_ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) (p : ℤ) :
    (ofSubmodules F hF).step (op p) =
      (ModuleCat.subobjectModule (ModuleCat.of R M)).symm (F p) := by
  have h := stepι_ofSubmodules F hF p
  have hm : Mono (ModuleCat.ofHom (F p).subtype) :=
    ModuleCat.mono_as_hom'_subtype (X := ModuleCat.of R M) (F p)
  have : Mono ((ofSubmodules F hF).stepι (op p)) := by
    rw [h]
    exact hm
  rw [← FilteredObject.mk_stepι]
  exact Subobject.mk_eq_mk_of_comm _ (ModuleCat.ofHom (F p).subtype) (Iso.refl _) (by simp [h])

/-- `ofSubmodules F hF` is exhaustive exactly when every submodule containing every `F p` is
everything. -/
theorem isExhaustive_ofSubmodules_iff (F : ℤ → Submodule R M) (hF : Antitone F) :
    (ofSubmodules F hF).IsExhaustive ↔ ∀ N : Submodule R M, (∀ p, F p ≤ N) → N = ⊤ := by
  set e := ModuleCat.subobjectModule (ModuleCat.of R M)
  rw [FilteredObject.isExhaustive_iff]
  refine ⟨fun h N hN ↦ ?_, fun h S hS ↦ ?_⟩
  · have := h (e.symm N) fun p ↦ ?_
    · have h' := congrArg e this
      rwa [OrderIso.apply_symm_apply, OrderIso.map_top] at h'
    · induction p using Opposite.rec with
      | op p => exact (step_ofSubmodules F hF p) ▸ e.symm.monotone (hN p)
  · have := h (e S) fun p ↦ by
      have h' := e.monotone (hS (op p))
      rwa [step_ofSubmodules, OrderIso.apply_symm_apply] at h'
    have h' := congrArg e.symm this
    rwa [OrderIso.symm_apply_apply, OrderIso.map_top] at h'

/-- `ofSubmodules F hF` is separated exactly when every submodule contained in every `F p` is
zero. -/
theorem isSeparated_ofSubmodules_iff (F : ℤ → Submodule R M) (hF : Antitone F) :
    (ofSubmodules F hF).IsSeparated ↔ ∀ N : Submodule R M, (∀ p, N ≤ F p) → N = ⊥ := by
  set e := ModuleCat.subobjectModule (ModuleCat.of R M)
  rw [FilteredObject.isSeparated_iff]
  refine ⟨fun h N hN ↦ ?_, fun h S hS ↦ ?_⟩
  · have := h (e.symm N) fun p ↦ ?_
    · have h' := congrArg e this
      rwa [OrderIso.apply_symm_apply, OrderIso.map_bot] at h'
    · induction p using Opposite.rec with
      | op p => exact (step_ofSubmodules F hF p) ▸ e.symm.monotone (hN p)
  · have := h (e S) fun p ↦ by
      have h' := e.monotone (hS (op p))
      rwa [step_ofSubmodules, OrderIso.apply_symm_apply] at h'
    have h' := congrArg e.symm this
    rwa [OrderIso.symm_apply_apply, OrderIso.map_bot] at h'

/-- The linear map underlying the inclusion of the step `F^p` is the inclusion of `F p`. -/
theorem stepι_hom_ofSubmodules (F : ℤ → Submodule R M) (hF : Antitone F) (p : ℤ) :
    ((ofSubmodules F hF).stepι (op p)).hom = (F p).subtype := by
  rw [stepι_ofSubmodules]
  rfl

/-- The map `R ⟶ M`, `1 ↦ x`, into the underlying module of `ofSubmodules F hF`. -/
noncomputable def toSpan (F : ℤ → Submodule R M) (hF : Antitone F) (x : M) :
    ModuleCat.of R R ⟶ (ofSubmodules F hF).quotientCone.pt :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

/-- The maps `R ⟶ M`, `1 ↦ x` and `1 ↦ y`, agree in the quotient `M / F p` exactly when
`x - y ∈ F p`. -/
theorem toSpan_comp_quotientCone_π_eq_iff (F : ℤ → Submodule R M) (hF : Antitone F)
    (p : ℤ) (x y : M) :
    toSpan F hF x ≫ (ofSubmodules F hF).quotientCone.π.app (op p) =
      toSpan F hF y ≫ (ofSubmodules F hF).quotientCone.π.app (op p) ↔ x - y ∈ F p := by
  -- The isomorphism `M / F^p ≅ M ⧸ F p`, with domain the quotient in the diagram.
  obtain ⟨e, he⟩ : ∃ e : (ofSubmodules F hF).quotientDiagram.obj (op p) ⟶
      ModuleCat.of R (M ⧸ LinearMap.range ((ofSubmodules F hF).stepι (op p)).hom),
      e = (ModuleCat.cokernelIsoRangeQuotient ((ofSubmodules F hF).stepι (op p))).hom :=
    ⟨_, rfl⟩
  have : Mono e := (ModuleCat.mono_iff_injective e).2 (by
    subst he
    exact (ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv.injective)
  have hπ : (ofSubmodules F hF).quotientCone.π.app (op p) ≫ e =
      ModuleCat.ofHom (LinearMap.range ((ofSubmodules F hF).stepι (op p)).hom).mkQ :=
    he ▸ ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _
  rw [← cancel_mono e, Category.assoc, Category.assoc, hπ, ModuleCat.hom_ext_iff,
    LinearMap.ext_ring_iff]
  change (LinearMap.range ((ofSubmodules F hF).stepι (op p)).hom).mkQ ((1 : R) • x) =
      (LinearMap.range ((ofSubmodules F hF).stepι (op p)).hom).mkQ ((1 : R) • y) ↔ x - y ∈ F p
  rw [one_smul, one_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
    stepι_hom_ofSubmodules]
  exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ z.property, fun h ↦ ⟨⟨x - y, h⟩, rfl⟩⟩

/-! ### Constant filtrations of `ℤ` -/

/-- The constant filtration `F^p = ℤ` of `ℤ` is exhaustive. -/
theorem isExhaustive_const_top :
    (ofSubmodules (fun _ ↦ (⊤ : Submodule ℤ ℤ)) antitone_const).IsExhaustive :=
  (isExhaustive_ofSubmodules_iff _ _).2 fun _ hN ↦ top_le_iff.1 (hN 0)

/-- The constant filtration `F^p = ℤ` of `ℤ` is not separated. -/
theorem not_isSeparated_const_top :
    ¬ (ofSubmodules (fun _ ↦ (⊤ : Submodule ℤ ℤ)) antitone_const).IsSeparated := by
  rw [isSeparated_ofSubmodules_iff]
  exact fun h ↦ top_ne_bot (h ⊤ fun _ ↦ le_rfl)

/-- The zero filtration `F^p = 0` of `ℤ` is separated. -/
theorem isSeparated_const_bot :
    (ofSubmodules (fun _ ↦ (⊥ : Submodule ℤ ℤ)) antitone_const).IsSeparated :=
  (isSeparated_ofSubmodules_iff _ _).2 fun _ hN ↦ le_bot_iff.1 (hN 0)

/-- The zero filtration `F^p = 0` of `ℤ` is not exhaustive. -/
theorem not_isExhaustive_const_bot :
    ¬ (ofSubmodules (fun _ ↦ (⊥ : Submodule ℤ ℤ)) antitone_const).IsExhaustive := by
  rw [isExhaustive_ofSubmodules_iff]
  exact fun h ↦ bot_ne_top (h ⊥ fun _ ↦ le_rfl)

/-! ### The `ℓ`-adic filtration of `ℤ` -/

/-- The `ℓ`-adic filtration of `ℤ`: `F^p = ℓ^p ℤ` for `p ≥ 0`, and `ℤ` for `p ≤ 0`. -/
def adicStep (ℓ : ℤ) (p : ℤ) : Submodule ℤ ℤ :=
  Ideal.span {ℓ ^ p.toNat}

/-- The `ℓ`-adic steps decrease. -/
theorem antitone_adicStep (ℓ : ℤ) : Antitone (adicStep ℓ) := fun p q hpq ↦ by
  rw [adicStep, adicStep, Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow ℓ (Int.toNat_le_toNat hpq)

/-- The `ℓ`-adic filtration of `ℤ` as a decreasingly filtered `ℤ`-module. -/
noncomputable abbrev adicFiltration (ℓ : ℤ) : FilteredObject (ModuleCat.{0} ℤ) ℤᵒᵖ :=
  ofSubmodules (adicStep ℓ) (antitone_adicStep ℓ)

/-- The `ℓ`-adic filtration of `ℤ` is exhaustive: its step `F^0` is `ℤ`. -/
theorem isExhaustive_adicFiltration (ℓ : ℤ) : (adicFiltration ℓ).IsExhaustive :=
  (isExhaustive_ofSubmodules_iff _ _).2 fun N hN ↦ top_le_iff.1 (by
    simpa [adicStep, Ideal.span_singleton_one] using hN 0)

/-- An integer divisible by every power of `ℓ`, for `ℓ ≥ 2`, is `0`. -/
private theorem eq_zero_of_forall_pow_dvd {ℓ : ℤ} (hℓ : 2 ≤ ℓ) {n : ℤ}
    (h : ∀ k : ℕ, ℓ ^ k ∣ n) : n = 0 := by
  by_contra hn
  have hk := Int.natAbs_le_of_dvd_ne_zero (h n.natAbs) hn
  rw [Int.natAbs_pow] at hk
  have hlt : n.natAbs < ℓ.natAbs ^ n.natAbs :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by omega) _)
  omega

/-- The `ℓ`-adic filtration of `ℤ`, for `ℓ ≥ 2`, is separated: an integer divisible by every
power of `ℓ` is `0`. -/
theorem isSeparated_adicFiltration {ℓ : ℤ} (hℓ : 2 ≤ ℓ) : (adicFiltration ℓ).IsSeparated := by
  refine (isSeparated_ofSubmodules_iff _ _).2 fun N hN ↦ (Submodule.eq_bot_iff N).2 fun n hn ↦ ?_
  refine eq_zero_of_forall_pow_dvd hℓ fun k ↦ ?_
  have := hN k hn
  rwa [adicStep, Int.toNat_natCast, Ideal.mem_span_singleton] at this

/-- The partial sums `sₖ = ∑_{i < k} (-ℓ)^i` of the `ℓ`-adic expansion of `1 / (1 + ℓ)`. -/
private def adicPartialSum (ℓ : ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, (-ℓ) ^ i

/-- `(1 + ℓ) sₖ = 1 - (-ℓ)^k`. -/
private theorem one_add_mul_adicPartialSum (ℓ : ℤ) (k : ℕ) :
    (1 + ℓ) * adicPartialSum ℓ k = 1 - (-ℓ) ^ k := by
  have := geom_sum_mul (-ℓ) k
  rw [adicPartialSum]
  linear_combination -this

/-- The partial sums are compatible: `ℓ^j ∣ s_k - s_j` for `j ≤ k`. -/
private theorem pow_dvd_adicPartialSum_sub (ℓ : ℤ) {j k : ℕ} (hjk : j ≤ k) :
    ℓ ^ j ∣ adicPartialSum ℓ k - adicPartialSum ℓ j := by
  rw [adicPartialSum, adicPartialSum, ← Finset.sum_range_add_sum_Ico _ hjk, add_sub_cancel_left]
  refine Finset.dvd_sum fun i hi ↦ ?_
  rw [neg_pow]
  exact Dvd.dvd.mul_left (pow_dvd_pow ℓ (Finset.mem_Ico.1 hi).1) _

/-- The `ℓ`-adic filtration of `ℤ`, for `ℓ ≥ 2`, is not complete: the partial sums of
`1 / (1 + ℓ) = ∑ (-ℓ)^i` form a compatible family of classes in the quotients `ℤ / ℓ^p`, which no
integer `n` represents, since `(1 + ℓ) n - 1` would be divisible by every power of `ℓ`. -/
theorem not_isComplete_adicFiltration {ℓ : ℤ} (hℓ : 2 ≤ ℓ) :
    ¬ (adicFiltration ℓ).IsComplete := by
  rw [FilteredObject.isComplete_iff]
  rintro ⟨hL⟩
  set s := adicPartialSum ℓ
  let g (k : ℕ) := toSpan (adicStep ℓ) (antitone_adicStep ℓ) (s k)
  let c : Limits.Cone (adicFiltration ℓ).quotientDiagram :=
    { pt := ModuleCat.of ℤ ℤ
      π :=
        { app p := g p.unop.toNat ≫ (adicFiltration ℓ).quotientCone.π.app p
          naturality p q f := by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Category.assoc, Limits.Cone.w]
            refine (toSpan_comp_quotientCone_π_eq_iff (adicStep ℓ)
              (antitone_adicStep ℓ) q.unop _ _).2 ?_
            rw [adicStep, Ideal.mem_span_singleton, ← dvd_neg, neg_sub]
            exact pow_dvd_adicPartialSum_sub ℓ (Int.toNat_le_toNat (leOfHom f.unop)) } }
  set n : ℤ := (hL.lift c).hom (1 : ℤ)
  have hlift : hL.lift c = toSpan (adicStep ℓ) (antitone_adicStep ℓ) n :=
    ModuleCat.hom_ext (LinearMap.ext_ring (by
      change n = (1 : ℤ) • n
      rw [one_smul]))
  have hdvd (k : ℕ) : ℓ ^ k ∣ (1 + ℓ) * n - 1 := by
    have h : toSpan (adicStep ℓ) (antitone_adicStep ℓ) n ≫
        (adicFiltration ℓ).quotientCone.π.app (op (k : ℤ)) =
        toSpan (adicStep ℓ) (antitone_adicStep ℓ) (s k) ≫
          (adicFiltration ℓ).quotientCone.π.app (op (k : ℤ)) := by
      rw [← hlift]
      exact hL.fac c (op (k : ℤ))
    have h' := (toSpan_comp_quotientCone_π_eq_iff (adicStep ℓ) (antitone_adicStep ℓ)
      k n (s k)).1 h
    rw [adicStep, Ideal.mem_span_singleton, Int.toNat_natCast] at h'
    have : (1 + ℓ) * n - 1 = (1 + ℓ) * (n - s k) - (-ℓ) ^ k := by
      have := one_add_mul_adicPartialSum ℓ k
      linear_combination this
    rw [this, neg_pow]
    exact dvd_sub (h'.mul_left _) (dvd_mul_left _ _)
  have h1 : (1 + ℓ) * n = 1 := by
    have := eq_zero_of_forall_pow_dvd hℓ hdvd
    omega
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h <;> omega

end TauCeti.Examples.DecreasingFiltration
