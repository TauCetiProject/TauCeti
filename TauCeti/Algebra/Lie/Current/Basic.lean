/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Loop
public import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial

/-!
# Formal currents and their order filtration

Formal currents in a Lie algebra `L` over `R` are the scalar extension
`R⸨X⸩ ⊗[R] L`, with the coefficientwise scalar action
and Mathlib's scalar-extension bracket. The order submodule
`orderSubmodule R L N` is spanned by tensors whose scalar series vanish below `N`.
The bracket of currents of orders at least `M` and `N` has order at least `M + N`.
Every current has a finite lower bound. The coefficient, order and truncation API
also applies to any coefficient module, without a Lie structure.

When `L` is free, coefficients determine a current, and membership in an order
submodule is equivalent to vanishing of all lower coefficients. These descriptions
make the filtration independent of a choice of basis. No finite-dimensionality is
needed for these statements: in infinite dimension, the tensor product still only
contains finite sums of scalar series times vectors. It need not contain every
`L`-valued Laurent series. When `L` is finite, free or not, every coefficient family vanishing
below some order is the coefficient family of a current.

Polynomial currents embed through `LieAlgebra.ExtendScalars.map` and the existing
Laurent-polynomial inclusion. Their coefficients agree with Mathlib's
`LieAlgebra.LoopAlgebra.toFinsupp`. Truncation below `N` produces a polynomial
current whose difference from the original lies in `orderSubmodule R L N`, and it kills
`orderSubmodule R L N`. A linear map on polynomial currents killing all modes `t^n ⊗ x` with
`n ≥ N` therefore extends to formal currents by composing with truncation below `N`.

## References

* V. Kac, *Infinite-Dimensional Lie Algebras*, Chapter 7 (current algebras).

The constructions use Mathlib's `LieAlgebra.ExtendScalars` and
`TensorProduct.equivFinsuppOfBasisRight`; no additional Lie structure is imposed.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries LaurentPolynomial

namespace TauCeti

variable (R L : Type*) [CommRing R]

-- The coefficientwise algebra structure matches the module used by the tensor product.
-- The other Laurent-series algebra instance has a propositionally equal scalar action.
attribute [local instance 1100] HahnSeries.instAlgebra

/-- Formal currents in a module; for a Lie algebra, equipped with the scalar-extension bracket. -/
abbrev currentAlgebra [AddCommGroup L] [Module R L] := R⸨X⸩ ⊗[R] L

namespace CurrentAlgebra

/-- Formal currents are a module over Laurent series, with the coefficientwise scalar action. -/
instance [AddCommGroup L] [Module R L] : Module R⸨X⸩ (currentAlgebra R L) :=
  TensorProduct.leftModule

section LieInstances

variable [LieRing L] [LieAlgebra R L]

/-- The scalar-extension Lie ring, using the coefficientwise scalar action on series. -/
instance : LieRing (currentAlgebra R L) :=
  LieAlgebra.ExtendScalars.instLieRing R R⸨X⸩ L

/-- Formal currents are a Lie algebra over the coefficient ring. -/
instance : LieAlgebra R (currentAlgebra R L) :=
  LieAlgebra.ExtendScalars.instBaseLieAlgebra R R⸨X⸩ L

/-- Formal currents are also a Lie algebra over the Laurent-series ring. -/
instance : LieAlgebra R⸨X⸩ (currentAlgebra R L) :=
  LieAlgebra.ExtendScalars.instLieAlgebra R R⸨X⸩ L

end LieInstances

section Module

variable [AddCommGroup L] [Module R L]

/-- The coefficient of a formal current at an integer exponent. -/
def coeff (n : ℤ) : currentAlgebra R L →ₗ[R] L :=
  (TensorProduct.lid R L).toLinearMap ∘ₗ (HahnSeries.coeff.linearMap n).rTensor L

@[simp]
theorem coeff_tmul (n : ℤ) (f : R⸨X⸩) (x : L) :
    coeff R L n (f ⊗ₜ x) = f.coeff n • x := by
  simp [coeff]

/-- In any basis of `L`, scalar-series coordinates and current coefficients agree. -/
theorem coeff_equivFinsuppOfBasisRight {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι R L) (u : currentAlgebra R L) (i : ι) (n : ℤ) :
    (TensorProduct.equivFinsuppOfBasisRight b u i).coeff n = b.repr (coeff R L n u) i := by
  induction u using TensorProduct.inductionOn with
  | tmul f x =>
    simp [mul_comm]
  | add u v hu hv => simp [hu, hv]

/-- Coefficients determine a formal current over a free coefficient module. -/
@[ext]
theorem ext [Module.Free R L] {u v : currentAlgebra R L}
    (h : ∀ n, coeff R L n u = coeff R L n v) : u = v := by
  classical
  let b := Module.Free.chooseBasis R L
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i n
  simp only [coeff_equivFinsuppOfBasisRight, h]

/-- Over a finite coefficient module, every coefficient family vanishing below some order is the
coefficient family of a formal current. Freeness is not needed. -/
theorem exists_forall_coeff_eq [Module.Finite R L] (c : ℤ → L) {a : ℤ}
    (hc : ∀ n < a, c n = 0) : ∃ u : currentAlgebra R L, ∀ n, coeff R L n u = c n := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := L)
  have hmem (n : ℤ) : ∃ r : Fin k → R, ∑ i, r i • s i = c n :=
    (Submodule.mem_span_range_iff_exists_fun R).mp (hs ▸ Submodule.mem_top)
  -- Choose zero coordinates for zero coefficients, so that each coordinate is bounded below.
  let r (n : ℤ) : Fin k → R := if c n = 0 then 0 else (hmem n).choose
  have hbdd (i : Fin k) : BddBelow (Function.support fun n ↦ r n i) :=
    ⟨a, fun n hn ↦ not_lt.mp fun h ↦ hn (by simp [r, hc n h])⟩
  refine ⟨∑ i, HahnSeries.ofSuppBddBelow _ (hbdd i) ⊗ₜ s i, fun n ↦ ?_⟩
  simp only [map_sum, coeff_tmul, HahnSeries.coeff_ofSuppBddBelow]
  by_cases h : c n = 0
  · simp [r, h]
  · simpa [r, h] using (hmem n).choose_spec

/-- Currents of order at least `N`, expressed without choosing a basis. -/
def orderSubmodule (N : ℤ) : Submodule R (currentAlgebra R L) :=
  Submodule.span R {u | ∃ f : R⸨X⸩, ∃ x : L, (N : WithTop ℤ) ≤ f.orderTop ∧ u = f ⊗ₜ x}

/-- The order submodule is spanned by the tensors whose scalar series have order at least `N`. -/
theorem orderSubmodule_def (N : ℤ) : orderSubmodule R L N =
    Submodule.span R {u | ∃ f : R⸨X⸩, ∃ x : L, (N : WithTop ℤ) ≤ f.orderTop ∧ u = f ⊗ₜ x} :=
  (rfl)

/-- A tensor has order at least the order of its scalar series. -/
theorem tmul_mem_orderSubmodule (N : ℤ) {f : R⸨X⸩}
    (hf : (N : WithTop ℤ) ≤ f.orderTop) (x : L) :
    f ⊗ₜ[R] x ∈ orderSubmodule R L N :=
  Submodule.subset_span ⟨f, x, hf, rfl⟩

/-- A current of order at least `N` has zero coefficients below `N`. -/
theorem coeff_eq_zero_of_mem_orderSubmodule {N n : ℤ} {u : currentAlgebra R L}
    (hu : u ∈ orderSubmodule R L N) (hn : n < N) : coeff R L n u = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f, x, hf, rfl⟩ := hu
    rw [coeff_tmul, HahnSeries.le_orderTop_iff_forall.mp hf n (by exact_mod_cast hn), zero_smul]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul r u _ hu => simp [hu]

/-- Vanishing of lower coefficients characterizes order for a free coefficient module. -/
theorem mem_orderSubmodule_iff [Module.Free R L] (N : ℤ) (u : currentAlgebra R L) :
    u ∈ orderSubmodule R L N ↔ ∀ n < N, coeff R L n u = 0 := by
  classical
  refine ⟨fun hu n hn ↦ coeff_eq_zero_of_mem_orderSubmodule R L hu hn, fun hu ↦ ?_⟩
  let b := Module.Free.chooseBasis R L
  let e := TensorProduct.equivFinsuppOfBasisRight (M := R⸨X⸩) b
  rw [← e.symm_apply_apply u, TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  apply Submodule.sum_mem
  intro i hi
  apply tmul_mem_orderSubmodule
  rw [HahnSeries.le_orderTop_iff_forall]
  intro n hn
  rw [coeff_equivFinsuppOfBasisRight, hu n (by exact_mod_cast hn)]
  simp

/-- Increasing the required order makes the order submodule smaller. -/
theorem orderSubmodule_antitone : Antitone (orderSubmodule R L) := by
  intro M N hMN
  apply Submodule.span_le.mpr
  rintro u ⟨f, x, hf, rfl⟩
  exact tmul_mem_orderSubmodule R L M ((WithTop.coe_le_coe.mpr hMN).trans hf) x

/-- The order filtration is separated over a free coefficient module. -/
@[simp]
theorem iInf_orderSubmodule [Module.Free R L] :
    ⨅ N, orderSubmodule R L N = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  apply (Submodule.mem_bot R).mpr
  apply ext R L
  intro n
  simpa using coeff_eq_zero_of_mem_orderSubmodule R L
    ((Submodule.mem_iInf _).mp hu (n + 1)) (by omega)

/-- Every formal current has a finite lower order, also in infinite dimension. -/
theorem exists_mem_orderSubmodule (u : currentAlgebra R L) :
    ∃ N : ℤ, u ∈ orderSubmodule R L N := by
  induction u using TensorProduct.inductionOn with
  | tmul f x =>
    refine ⟨f.order, tmul_mem_orderSubmodule R L _ ?_ x⟩
    by_cases hf : f = 0
    · simp [hf]
    · exact (HahnSeries.order_eq_orderTop_of_ne_zero hf).le
  | add u v hu hv =>
    obtain ⟨M, hM⟩ := hu
    obtain ⟨N, hN⟩ := hv
    exact ⟨min M N, (orderSubmodule R L _).add_mem
      (orderSubmodule_antitone R L (min_le_left _ _) hM)
      (orderSubmodule_antitone R L (min_le_right _ _) hN)⟩

/-- A scalar series of order at least `M` times a current of order at least `N`
has order at least `M + N`. -/
theorem smul_mem_orderSubmodule {M N : ℤ} {f : R⸨X⸩} {u : currentAlgebra R L}
    (hf : (M : WithTop ℤ) ≤ f.orderTop) (hu : u ∈ orderSubmodule R L N) :
    f • u ∈ orderSubmodule R L (M + N) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨g, x, hg, rfl⟩ := hu
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    apply tmul_mem_orderSubmodule
    have hMN : ((M + N : ℤ) : WithTop ℤ) ≤ f.orderTop + g.orderTop := by
      simpa using add_le_add hf hg
    exact hMN.trans HahnSeries.orderTop_add_le_mul
  | zero => simp
  | add u v _ _ hu hv => simpa only [smul_add] using Submodule.add_mem _ hu hv
  | smul r u _ hu => simpa only [smul_comm f r] using Submodule.smul_mem _ r hu

/-- Truncate a formal current strictly below an integer cutoff, producing a polynomial current. -/
def trunc (N : ℤ) : currentAlgebra R L →ₗ[R] R[T;T⁻¹] ⊗[R] L :=
  (_root_.LaurentSeries.trunc N).rTensor L

@[simp]
theorem trunc_tmul (N : ℤ) (f : R⸨X⸩) (x : L) :
    trunc R L N (f ⊗ₜ x) = _root_.LaurentSeries.trunc N f ⊗ₜ x := (rfl)

end Module

section Lie

variable [LieRing L] [LieAlgebra R L]

/-- The bracket of currents of orders at least `M` and `N` has order at least `M + N`. -/
theorem lie_mem_orderSubmodule {M N : ℤ} {u v : currentAlgebra R L}
    (hu : u ∈ orderSubmodule R L M) (hv : v ∈ orderSubmodule R L N) :
    ⁅u, v⁆ ∈ orderSubmodule R L (M + N) := by
  -- `LieAlgebra.ad` needs a Lie ring on endomorphisms; instance search cannot find it
  -- because Mathlib registers `LieRing.ofAssociativeRing` only as a local instance.
  let : LieRing (Module.End R (currentAlgebra R L)) := LieRing.ofAssociativeRing
  refine LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (orderSubmodule R L (M + N)) _ _ (LieAlgebra.ad R (currentAlgebra R L)).toLinearMap
    ?_ u v hu hv
  rintro _ ⟨f, x, hf, rfl⟩ _ ⟨g, y, hg, rfl⟩
  rw [LieHom.coe_toLinearMap, LieAlgebra.ad_apply, LieAlgebra.ExtendScalars.bracket_tmul]
  simpa only [TensorProduct.smul_tmul', smul_eq_mul] using
    smul_mem_orderSubmodule R L hf (tmul_mem_orderSubmodule R L N hg ⁅x, y⁆)

/-- The inclusion of polynomial currents into formal currents. -/
def ofLoop : LieAlgebra.loopAlgebra R ℤ L →ₗ⁅R⁆ currentAlgebra R L :=
  LieAlgebra.ExtendScalars.map
    { toRingHom := LaurentPolynomial.toLaurentSeries
      commutes' := fun r ↦ by
        simp [HahnSeries.algebraMap_apply] } LieHom.id

@[simp]
theorem ofLoop_tmul (p : R[T;T⁻¹]) (x : L) :
    ofLoop R L (p ⊗ₜ x) = LaurentPolynomial.toLaurentSeries p ⊗ₜ x := (rfl)

/-- The inclusion preserves polynomial-current coefficients. -/
@[simp]
theorem coeff_ofLoop (n : ℤ) (u : LieAlgebra.loopAlgebra R ℤ L) :
    coeff R L n (ofLoop R L u) = LieAlgebra.LoopAlgebra.toFinsupp R ℤ L u n := by
  obtain ⟨v, rfl⟩ := (LieAlgebra.LoopAlgebra.toFinsupp R ℤ L).symm.surjective u
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simpa only [map_add, Finsupp.add_apply] using congrArg₂ (· + ·) hv hw
  | single k x =>
    rw [LieAlgebra.LoopAlgebra.toFinsupp_symm_single]
    simp only [ofLoop_tmul, coeff_tmul, LaurentPolynomial.coeff_toLaurentSeries,
      AddMonoidAlgebra.coeff_single, LieAlgebra.LoopAlgebra.toFinsupp_single_tmul]
    by_cases h : k = n <;> simp [h]

/-- Polynomial currents embed in formal currents over every commutative base ring. -/
theorem ofLoop_injective : Function.Injective (ofLoop R L) := by
  intro u v h
  apply (LieAlgebra.LoopAlgebra.toFinsupp R ℤ L).injective
  ext n
  simpa only [coeff_ofLoop] using congrArg (coeff R L n) h

/-- Truncation retains exactly the coefficients strictly below its cutoff. -/
@[simp]
theorem toFinsupp_trunc (N n : ℤ) (u : currentAlgebra R L) :
    LieAlgebra.LoopAlgebra.toFinsupp R ℤ L (trunc R L N u) n =
      if n < N then coeff R L n u else 0 := by
  rw [← coeff_ofLoop]
  induction u using TensorProduct.inductionOn with
  | tmul f x =>
    by_cases hn : n < N <;> simp [hn]
  | add u v hu hv =>
    by_cases hn : n < N <;> simp [hu, hv, hn]

/-- The truncation error has order at least the cutoff, without a freeness assumption. -/
theorem ofLoop_trunc_sub_mem_orderSubmodule (N : ℤ) (u : currentAlgebra R L) :
    ofLoop R L (trunc R L N u) - u ∈ orderSubmodule R L N := by
  induction u using TensorProduct.inductionOn with
  | tmul f x =>
    rw [trunc_tmul, ofLoop_tmul, ← TensorProduct.sub_tmul]
    exact tmul_mem_orderSubmodule R L N
      (_root_.LaurentSeries.le_orderTop_sub_toLaurentSeries_trunc N f) x
  | add u v hu hv =>
    simpa only [map_add, add_sub_add_comm] using (orderSubmodule R L N).add_mem hu hv


/-- The polynomial mode `t^a ⊗ x` has order at least `a`. -/
theorem ofLoop_single_tmul_mem_orderSubmodule (a : ℤ) (x : L) :
    ofLoop R L (AddMonoidAlgebra.single a 1 ⊗ₜ x) ∈ orderSubmodule R L a := by
  rw [ofLoop_tmul]
  exact tmul_mem_orderSubmodule R L a
    (by rw [LaurentPolynomial.toLaurentSeries_single]; exact HahnSeries.orderTop_single_le) x

/-- Truncation below `N` kills the currents of order at least `N`. -/
theorem trunc_eq_zero_of_mem_orderSubmodule {N : ℤ} {u : currentAlgebra R L}
    (hu : u ∈ orderSubmodule R L N) : trunc R L N u = 0 :=
  (LieAlgebra.LoopAlgebra.toFinsupp R ℤ L).injective <| by
    ext n
    rw [toFinsupp_trunc, map_zero, Finsupp.zero_apply, ite_eq_right_iff]
    exact coeff_eq_zero_of_mem_orderSubmodule R L hu

/-- A linear map on polynomial currents which vanishes on all modes `t^n ⊗ x` with `n ≥ N` is
unchanged by first truncating polynomial currents below `N`. -/
theorem apply_trunc_ofLoop {V : Type*} [AddCommGroup V] [Module R V] {N : ℤ}
    (g : LieAlgebra.loopAlgebra R ℤ L →ₗ[R] V)
    (hg : ∀ n, N ≤ n → ∀ x, g (AddMonoidAlgebra.single n 1 ⊗ₜ x) = 0)
    (p : LieAlgebra.loopAlgebra R ℤ L) : g (trunc R L N (ofLoop R L p)) = g p := by
  -- The difference has no coefficients below `N`, so it is a sum of modes killed by `g`.
  obtain ⟨v, hv⟩ := (LieAlgebra.LoopAlgebra.toFinsupp R ℤ L).symm.surjective
    (p - trunc R L N (ofLoop R L p))
  have hvN (n : ℤ) (hn : n < N) : v n = 0 := by
    have h := congrArg (LieAlgebra.LoopAlgebra.toFinsupp R ℤ L · n) hv
    simp only [LinearEquiv.apply_symm_apply] at h
    simp [h, hn]
  rw [eq_comm, ← sub_eq_zero, ← map_sub, ← hv, ← Finsupp.sum_single v, map_finsuppSum,
    map_finsuppSum]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  dsimp only
  rw [LieAlgebra.LoopAlgebra.toFinsupp_symm_single,
    hg n (not_lt.mp fun h ↦ Finsupp.mem_support_iff.mp hn (hvN n h))]

end Lie

end CurrentAlgebra

end TauCeti
