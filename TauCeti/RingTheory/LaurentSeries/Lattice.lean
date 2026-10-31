/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Multiplication
public import TauCeti.RingTheory.LaurentSeries.Convergence

/-!
# The lattices `U_a` of Laurent series

For a module `V` over a semiring `R`, this file defines the `R`-submodules

`U_a(V) = Xᵃ V⟦X⟧ = {f | f.coeff n = 0 for all n < a}`

of `V`-valued Laurent series `HahnSeries ℤ V`. They decrease in `a`, exhaust all series and meet
in `0`. For `V = R` they are the translates `Xᵃ R⟦X⟧` of the power series, they multiply as
`U_a U_b ⊆ U_{a + b}`, and over a field they are the closed balls of the valuation topology.

For coefficients in an `R`-module, the quotient `U_a(V) / (U_a(V) ∩ U_b(V))` records exactly
the coefficients at the exponents `a ≤ n < b`. It is thus a finite product of copies of `V`,
with dimension `(b - a).toNat * Module.finrank R V` when `V` is finite free and `R` satisfies
the strong rank condition. The construction uses coefficients directly, without choosing a
basis of `V`.

The same lattices and finite jets on `HahnModule ℤ R V` are obtained through the
coefficient-preserving comparison `HahnModule.ofLinearEquiv`. This allows finite jets to be
used together with the action of scalar Laurent series on module-valued Laurent series.

## Main definitions

* `TauCeti.LaurentSeries.lattice R V a`: the `R`-submodule `U_a(V)`.
* `TauCeti.LaurentSeries.latticeQuotient R V a b`: the finite-jet module.
* `TauCeti.LaurentSeries.latticeQuotientEquiv R V a b`: coefficients on `[a, b)` identify the
  finite-jet quotient with `Finset.Ico a b → V`.
* `TauCeti.HahnModule.lattice`, `TauCeti.HahnModule.latticeQuotient` and
  `TauCeti.HahnModule.latticeQuotientEquiv`:
  the corresponding lattice and finite-jet comparison on `HahnModule ℤ R V`.

## Main results

* `TauCeti.LaurentSeries.single_mem_lattice_iff`: the monomial `v Xⁿ` lies in `U_a(V)` exactly
  when `v = 0` or `a ≤ n`.
* `TauCeti.LaurentSeries.iSup_lattice`, `TauCeti.LaurentSeries.iInf_lattice`: the lattices
  exhaust all series and meet in `0`.
* `TauCeti.LaurentSeries.mem_lattice_iff_exists`: `U_a(R) = Xᵃ R⟦X⟧`.
* `TauCeti.LaurentSeries.mul_mem_lattice`: `U_a U_b ⊆ U_{a + b}`.
* `TauCeti.LaurentSeries.mem_lattice_iff_valuation_le`: over a field, `U_a` is a closed
  valuation ball.
* `TauCeti.LaurentSeries.hasBasis_nhds_zero_lattice`: the lattices form a neighbourhood basis
  of zero in the valuation topology.
* `TauCeti.LaurentSeries.finrank_latticeQuotient`,
  `TauCeti.HahnModule.finrank_latticeQuotient`: finite jets have `finrank` equal to
  `(b - a).toNat * Module.finrank R V`.
-/

public section

open HahnSeries Filter
open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

section Module

variable (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V]

/-- The lattice `U_a(V) = Xᵃ V⟦X⟧` of `V`-valued Laurent series whose coefficients vanish at
every exponent below `a`, as an `R`-submodule of `HahnSeries ℤ V`. -/
def lattice (a : ℤ) : Submodule R (HahnSeries ℤ V) where
  carrier := {f | ∀ n < a, f.coeff n = 0}
  add_mem' hf hg n hn := by rw [coeff_add, hf n hn, hg n hn, add_zero]
  zero_mem' _ _ := coeff_zero
  smul_mem' r f hf n hn := by rw [coeff_smul, hf n hn, smul_zero]

variable {R V}

/-- Membership in `U_a(V)` is the vanishing of every coefficient below `a`. -/
theorem mem_lattice_iff {a : ℤ} {f : HahnSeries ℤ V} :
    f ∈ lattice R V a ↔ ∀ n < a, f.coeff n = 0 :=
  Iff.rfl

/-- Membership in `U_a(V)` is the order bound `a ≤ ord f`. -/
theorem mem_lattice_iff_le_orderTop {a : ℤ} {f : HahnSeries ℤ V} :
    f ∈ lattice R V a ↔ (a : WithTop ℤ) ≤ f.orderTop := by
  rw [mem_lattice_iff, le_orderTop_iff_forall]
  simp only [WithTop.coe_lt_coe]

/-- A series in `U_a(V)` has zero coefficient at every exponent below `a`. -/
theorem coeff_eq_zero_of_mem_lattice {a n : ℤ} {f : HahnSeries ℤ V} (hf : f ∈ lattice R V a)
    (hn : n < a) : f.coeff n = 0 :=
  hf n hn

/-- The monomial `v Xⁿ` lies in `U_a(V)` once `a ≤ n`. -/
theorem single_mem_lattice {a n : ℤ} (h : a ≤ n) (v : V) : single n v ∈ lattice R V a :=
  fun _ hm ↦ coeff_single_of_ne (by omega)

/-- The monomial `v Xⁿ` lies in `U_a(V)` exactly when `v = 0` or `a ≤ n`. -/
@[simp]
theorem single_mem_lattice_iff {a n : ℤ} {v : V} : single n v ∈ lattice R V a ↔ v = 0 ∨ a ≤ n := by
  refine ⟨fun h ↦ or_iff_not_imp_right.mpr fun hn ↦ ?_, ?_⟩
  · simpa using h n (not_le.mp hn)
  · rintro (rfl | h)
    · rw [single_eq_zero]
      exact zero_mem _
    · exact single_mem_lattice h v

/-- The lattices decrease as the exponent bound increases. -/
theorem lattice_antitone : Antitone (lattice R V) :=
  fun _ _ h _ hf n hn ↦ hf n (hn.trans_le h)

/-- For a nontrivial module `V`, `U_b(V) ⊆ U_a(V)` exactly when `a ≤ b`. -/
theorem lattice_le_lattice_iff [Nontrivial V] {a b : ℤ} :
    lattice R V b ≤ lattice R V a ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ lattice_antitone h⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  simpa [hv] using h (single_mem_lattice le_rfl v)

/-- Every `V`-valued Laurent series lies in some lattice `U_a(V)`. -/
theorem iSup_lattice : ⨆ a, lattice R V a = ⊤ :=
  eq_top_iff.mpr fun f _ ↦ Submodule.mem_iSup_of_mem f.order fun _ hn ↦
    coeff_eq_zero_of_lt_order hn

/-- Only `0` lies in every lattice `U_a(V)`. -/
theorem iInf_lattice : ⨅ a, lattice R V a = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ ?_
  rw [Submodule.mem_iInf] at hf
  rw [Submodule.mem_bot]
  ext n
  exact hf (n + 1) n (Int.lt_succ n)

end Module

section Ring

variable {R : Type*} [Semiring R]

/-- The lattices multiply as `U_a U_b ⊆ U_{a + b}`. -/
theorem mul_mem_lattice {a b : ℤ} {f g : R⸨X⸩} (hf : f ∈ lattice R R a)
    (hg : g ∈ lattice R R b) : f * g ∈ lattice R R (a + b) := by
  rw [mem_lattice_iff_le_orderTop] at hf hg ⊢
  exact (WithTop.coe_add a b ▸ add_le_add hf hg).trans orderTop_add_le_mul

/-- A formal power series lies in `U_0`. -/
theorem coe_powerSeries_mem_lattice_zero (p : R⟦X⟧) : (p : R⸨X⸩) ∈ lattice R R 0 :=
  fun n hn ↦ by rw [PowerSeries.coeff_coe, ite_eq_left hn]

/-- The lattice `U_a` is `Xᵃ R⟦X⟧`: its members are the series `Xᵃ p` with `p` a power
series. -/
theorem mem_lattice_iff_exists {a : ℤ} {f : R⸨X⸩} :
    f ∈ lattice R R a ↔ ∃ p : R⟦X⟧, single a 1 * (p : R⸨X⸩) = f := by
  have hmem (p : R⟦X⟧) : single a 1 * (p : R⸨X⸩) ∈ lattice R R a := by
    simpa using mul_mem_lattice (single_mem_lattice (R := R) (le_refl a) (1 : R))
      (coe_powerSeries_mem_lattice_zero p)
  refine ⟨fun hf ↦ ⟨PowerSeries.mk fun n ↦ f.coeff (a + n), ?_⟩, fun ⟨p, hp⟩ ↦ hp ▸ hmem p⟩
  ext n
  obtain hn | hn := lt_or_ge n a
  · rw [hf n hn, coeff_eq_zero_of_mem_lattice (hmem _) hn]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + a := ⟨(n - a).toNat, by omega⟩
    rw [coeff_single_mul_add, one_mul, PowerSeries.coeff_coe]
    simp [add_comm]

/-- The lattice `U_0` consists of the formal power series. -/
theorem mem_lattice_zero_iff {f : R⸨X⸩} : f ∈ lattice R R 0 ↔ ∃ p : R⟦X⟧, (p : R⸨X⸩) = f := by
  simp only [mem_lattice_iff_exists, single_zero_one, one_mul]

/-- Over a field, `U_a` is the closed valuation ball `{f | v f ≤ exp (-a)}`. -/
theorem mem_lattice_iff_valuation_le {K : Type*} [Field K] {a : ℤ} {f : K⸨X⸩} :
    f ∈ lattice K K a ↔ Valued.v f ≤ WithZero.exp (-a) :=
  (_root_.LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).symm

end Ring

/-- The lattices `U_a` form a neighbourhood basis of zero for the Laurent valuation topology. -/
theorem hasBasis_nhds_zero_lattice {K : Type*} [Field K] :
    (nhds (0 : K⸨X⸩)).HasBasis (fun _ : ℤ ↦ True)
      (fun a ↦ (lattice K K a : Set K⸨X⸩)) := by
  have heq : nhds (0 : K⸨X⸩) = ⨅ a : ℤ, 𝓟 (lattice K K a : Set K⸨X⸩) := by
    apply le_antisymm
    · refine le_iInf fun a ↦ le_principal_iff.mpr ?_
      filter_upwards [(tendsto_laurentSeries_iff_orderTop_sub (K := K) id 0).mp
        tendsto_id a] with f hf
      exact mem_lattice_iff_le_orderTop.mpr (by simpa using hf)
    · exact (tendsto_laurentSeries_iff_orderTop_sub id 0).mpr fun a ↦ by
        simp only [id_eq, sub_zero]
        exact mem_iInf_of_mem a (mem_principal.mpr fun _ hf ↦
          mem_lattice_iff_le_orderTop.mp hf)
  rw [heq]
  exact Filter.hasBasis_iInf_principal fun a b ↦
    ⟨max a b, lattice_antitone (le_max_left a b), lattice_antitone (le_max_right a b)⟩

section Coefficients

variable (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V]

/-- The coefficient map `U_a(V) → V^{[a, b)}`, whose kernel is `U_a(V) ∩ U_b(V)`. -/
private noncomputable def latticeCoeff (a b : ℤ) : lattice R V a →ₗ[R] Finset.Ico a b → V :=
  LinearMap.pi fun k ↦ (coeff.linearMap (k : ℤ)).comp (lattice R V a).subtype

private theorem latticeCoeff_apply (a b : ℤ) (f : lattice R V a) (k : Finset.Ico a b) :
    latticeCoeff R V a b f k = (f : HahnSeries ℤ V).coeff k := by
  simp [latticeCoeff]

private theorem ker_latticeCoeff (a b : ℤ) :
    LinearMap.ker (latticeCoeff R V a b) = (lattice R V b).comap (lattice R V a).subtype := by
  ext ⟨f, hf⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, mem_lattice_iff,
    funext_iff, latticeCoeff_apply, Pi.zero_apply, Subtype.forall,
    Finset.mem_Ico]
  exact ⟨fun h n hn ↦ (lt_or_ge n a).elim (coeff_eq_zero_of_mem_lattice hf) fun han ↦ h n ⟨han, hn⟩,
    fun h n hn ↦ h n hn.2⟩

private theorem latticeCoeff_surjective (a b : ℤ) : Function.Surjective (latticeCoeff R V a b) := by
  intro c
  refine ⟨⟨∑ k : Finset.Ico a b, single (k : ℤ) (c k), Submodule.sum_mem _ fun k _ ↦
    single_mem_lattice (Finset.mem_Ico.mp k.2).1 _⟩, funext fun k ↦ ?_⟩
  rw [latticeCoeff_apply, coeff_sum, Finset.sum_eq_single k
    (fun j _ hj ↦ coeff_single_of_ne (Subtype.coe_ne_coe.mpr hj.symm)) (by simp), coeff_single_same]

end Coefficients

section Quotient

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]

/-- The finite-jet module `U_a(V) / (U_a(V) ∩ U_b(V))` of classes of series in `U_a(V)`.
Two series define the same class when their difference lies in `U_b(V)`; the quotient is zero
when `b ≤ a`. -/
abbrev latticeQuotient (a b : ℤ) :=
  lattice R V a ⧸ (lattice R V b).comap (lattice R V a).subtype

/-- The coefficients at `a ≤ n < b` identify `U_a(V) / (U_a(V) ∩ U_b(V))` with functions
on these exponents. -/
noncomputable def latticeQuotientEquiv (a b : ℤ) :
    latticeQuotient R V a b ≃ₗ[R] (Finset.Ico a b → V) :=
  (Submodule.quotEquivOfEq _ _ (ker_latticeCoeff R V a b).symm).trans
    ((latticeCoeff R V a b).quotKerEquivOfSurjective (latticeCoeff_surjective R V a b))

/-- The class of `f ∈ U_a(V)` in the lattice quotient corresponds to the coefficients of `f` at the
exponents `a ≤ n < b`. -/
@[simp]
theorem latticeQuotientEquiv_mk (a b : ℤ) (f : lattice R V a) (k : Finset.Ico a b) :
    latticeQuotientEquiv R V a b (Submodule.Quotient.mk f) k = (f : HahnSeries ℤ V).coeff k := by
  rw [latticeQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, latticeCoeff_apply]

/-- The function supported at one exponent `a ≤ k < b` corresponds to the class of the monomial
`v Xᵏ` in the lattice quotient. -/
@[simp]
theorem latticeQuotientEquiv_symm_single (a b : ℤ) (k : Finset.Ico a b) (v : V) :
    (latticeQuotientEquiv R V a b).symm (Pi.single k v) =
      Submodule.Quotient.mk ⟨single (k : ℤ) v, single_mem_lattice (Finset.mem_Ico.mp k.2).1 v⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  funext j
  rw [latticeQuotientEquiv_mk]
  obtain rfl | hjk := eq_or_ne j k
  · rw [coeff_single_same, Pi.single_eq_same]
  · rw [coeff_single_of_ne (Subtype.coe_ne_coe.mpr hjk), Pi.single_eq_of_ne hjk]

/-- The lattice quotient is free when `V` is free, via its coefficients at `a ≤ n < b`. -/
instance [Module.Free R V] (a b : ℤ) :
    Module.Free R (latticeQuotient R V a b) :=
  .of_equiv (latticeQuotientEquiv R V a b).symm

/-- The lattice quotient is finite when `V` is finite, via its coefficients at `a ≤ n < b`. -/
instance [Module.Finite R V] (a b : ℤ) :
    Module.Finite R (latticeQuotient R V a b) :=
  .equiv (latticeQuotientEquiv R V a b).symm

/-- The finite-jet quotient has `finrank` equal to the interval length times that of `V`. -/
theorem finrank_latticeQuotient [StrongRankCondition R] [Module.Free R V]
    (a b : ℤ) :
    Module.finrank R (latticeQuotient R V a b) =
      (b - a).toNat * Module.finrank R V := by
  rw [(latticeQuotientEquiv R V a b).finrank_eq]
  simp only [Module.finrank, rank_fun_eq_lift_mul, Cardinal.toNat_mul,
    Cardinal.toNat_natCast, Cardinal.toNat_lift, Fintype.card_coe, Int.card_Ico]

end Quotient

end TauCeti.LaurentSeries

namespace TauCeti.HahnModule

open _root_.HahnModule

section Lattice

variable (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V]

/-- The `R`-linear lattice of module-valued Laurent series with zero coefficients below `a`. -/
noncomputable def lattice (a : ℤ) : Submodule R (HahnModule ℤ R V) :=
  (TauCeti.LaurentSeries.lattice R V a).comap (ofLinearEquiv R).symm.toLinearMap

/-- Membership in the Hahn-module lattice is coefficientwise vanishing below its bound. -/
theorem mem_lattice_iff {a : ℤ} {f : HahnModule ℤ R V} :
    f ∈ lattice R V a ↔ ∀ n < a, ((of R).symm f).coeff n = 0 := by
  simp [lattice, TauCeti.LaurentSeries.mem_lattice_iff]

/-- The comparison from Hahn series to Hahn modules preserves lattice membership. -/
@[simp]
theorem of_mem_lattice_iff {a : ℤ} {f : HahnSeries ℤ V} :
    of R f ∈ lattice R V a ↔ f ∈ TauCeti.LaurentSeries.lattice R V a := by
  simp [mem_lattice_iff, TauCeti.LaurentSeries.mem_lattice_iff]

/-- The coefficient-preserving comparison restricted to a lattice. -/
noncomputable def latticeEquiv (a : ℤ) :
    lattice R V a ≃ₗ[R] TauCeti.LaurentSeries.lattice R V a :=
  (ofLinearEquiv R).symm.ofSubmodule' (TauCeti.LaurentSeries.lattice R V a)

@[simp]
theorem latticeEquiv_apply (a : ℤ) (f : lattice R V a) :
    (latticeEquiv R V a f : HahnSeries ℤ V) =
      (of R).symm (f : HahnModule ℤ R V) := by
  calc
    _ = (ofLinearEquiv R).symm (f : HahnModule ℤ R V) :=
      LinearEquiv.ofSubmodule'_apply _ _ _
    _ = _ := ofLinearEquiv_symm_apply _

@[simp]
theorem latticeEquiv_symm_apply (a : ℤ) (f : TauCeti.LaurentSeries.lattice R V a) :
    ((latticeEquiv R V a).symm f : HahnModule ℤ R V) =
      of R (f : HahnSeries ℤ V) := by
  calc
    _ = ((ofLinearEquiv R).symm).symm (f : HahnSeries ℤ V) :=
      LinearEquiv.ofSubmodule'_symm_apply _ _ _
    _ = _ := by rw [LinearEquiv.symm_symm, ofLinearEquiv_apply]

end Lattice

section Quotient

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]

/-- The finite-jet module `U_a(V) / (U_a(V) ∩ U_b(V))` of classes of series in `U_a(V)`.
Two series define the same class when their difference lies in `U_b(V)`; the quotient is zero
when `b ≤ a`. -/
abbrev latticeQuotient (a b : ℤ) :=
  lattice R V a ⧸ (lattice R V b).comap (lattice R V a).subtype

/-- The class of `f` in the Hahn-module lattice quotient maps to the coefficients of
`(of R).symm f` at the exponents `a ≤ n < b`. -/
noncomputable def latticeQuotientEquiv (a b : ℤ) :
    latticeQuotient R V a b ≃ₗ[R] (Finset.Ico a b → V) :=
  (Submodule.Quotient.equiv _ _ (latticeEquiv R V a) (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext f
    simp [Submodule.mem_comap, mem_lattice_iff, TauCeti.LaurentSeries.mem_lattice_iff])).trans
      (TauCeti.LaurentSeries.latticeQuotientEquiv R V a b)

/-- The class of a module-valued Laurent series is identified with its coefficients. -/
@[simp]
theorem latticeQuotientEquiv_mk (a b : ℤ) (f : lattice R V a) (k : Finset.Ico a b) :
    latticeQuotientEquiv R V a b (Submodule.Quotient.mk f) k =
      ((of R).symm (f : HahnModule ℤ R V)).coeff k := by
  simp [latticeQuotientEquiv, Submodule.Quotient.equiv_apply]

/-- A function supported at one exponent corresponds to the class of that monomial. -/
@[simp]
theorem latticeQuotientEquiv_symm_single (a b : ℤ) (k : Finset.Ico a b) (v : V) :
    (latticeQuotientEquiv R V a b).symm (Pi.single k v) =
      Submodule.Quotient.mk ⟨of R (HahnSeries.single (k : ℤ) v),
        (of_mem_lattice_iff R V).mpr
          (TauCeti.LaurentSeries.single_mem_lattice (Finset.mem_Ico.mp k.2).1 v)⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  funext j
  rw [latticeQuotientEquiv_mk]
  obtain rfl | hjk := eq_or_ne j k
  · simp
  · simp [HahnSeries.coeff_single_of_ne (Subtype.coe_ne_coe.mpr hjk), Pi.single_eq_of_ne hjk]

/-- The finite-jet quotient of Hahn-module lattices is free when the coefficients are free. -/
instance [Module.Free R V] (a b : ℤ) :
    Module.Free R (latticeQuotient R V a b) :=
  .of_equiv (latticeQuotientEquiv R V a b).symm

/-- The finite-jet quotient of Hahn-module lattices is finite when the coefficients are finite. -/
instance [Module.Finite R V] (a b : ℤ) :
    Module.Finite R (latticeQuotient R V a b) :=
  .equiv (latticeQuotientEquiv R V a b).symm

/-- The `finrank` of module-valued finite jets is the interval length times the coefficient
`finrank`. -/
theorem finrank_latticeQuotient [StrongRankCondition R] [Module.Free R V]
    (a b : ℤ) :
    Module.finrank R (latticeQuotient R V a b) =
      (b - a).toNat * Module.finrank R V := by
  rw [(latticeQuotientEquiv R V a b).finrank_eq,
    ← (TauCeti.LaurentSeries.latticeQuotientEquiv R V a b).finrank_eq,
    TauCeti.LaurentSeries.finrank_latticeQuotient]

end Quotient

end TauCeti.HahnModule
