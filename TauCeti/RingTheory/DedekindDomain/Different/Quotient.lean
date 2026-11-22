/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different.Basic
public import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# Trace-dual quotient comparison for linear maps

For an integral domain `A` with fraction field `K`, a finite separable extension `L / K`, and the
integral closure `B` of `A` in `L` with `Bᵛ = Submodule.traceDual A K (1 : Submodule B L)`, the
trace descends to `traceDualQuotientMap : L ⧸ Bᵛ →ₗ[A] K ⧸ A`, yielding `traceDualLinearMapEquiv :
(M →ₗ[B] (L ⧸ Bᵛ)) ≃ₗ[A] (M →ₗ[A] (K ⧸ A))` when `B` is finite projective over `A`. When
`differentIdeal A B` is principal, dividing by a generator identifies `L ⧸ B ≃ₗ[B] L ⧸ Bᵛ`. By
contrast, `directTracePairing : L ⧸ B →ₗ[A] (B →ₗ[A] K ⧸ A)` has kernel the image of `Bᵛ` in
`L ⧸ B`, hence is injective iff `differentIdeal A B = ⊤`.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
-/

public section
noncomputable section

namespace TauCeti

section TraceDualQuotient

variable (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

/-- The `A`-linear map `L ⧸ Bᵛ → K ⧸ A` induced by `Algebra.trace K L`. -/
def traceDualQuotientMap :
    (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) →ₗ[A] (K ⧸ (1 : Submodule A K)) :=
  ((Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A).liftQ
    ((1 : Submodule A K).mkQ ∘ₗ (Algebra.trace K L).restrictScalars A) fun x hx ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
      simpa [Algebra.traceForm_apply] using
        Submodule.mem_traceDual.mp hx 1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
@[simp] theorem traceDualQuotientMap_mk (x : L) :
    traceDualQuotientMap A K B L (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Algebra.trace K L x) := (rfl)

/-- For `y ∈ Bᵛ`, multiplication by `y` descends to an `A`-linear map `K ⧸ A → L ⧸ Bᵛ`. -/
def mulByTraceDualQuotientMap (y : L) (hy : y ∈ Submodule.traceDual A K (1 : Submodule B L)) :
    (K ⧸ (1 : Submodule A K)) →ₗ[A] (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) :=
  (1 : Submodule A K).liftQ
    { toFun := fun k ↦ Submodule.Quotient.mk (k • y)
      map_add' := fun _ _ ↦ by rw [add_smul, Submodule.Quotient.mk_add]
      map_smul' := fun _ _ ↦ by simp only [RingHom.id_apply, smul_assoc]; rfl } fun k hk ↦ by
      obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hk
      rw [LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, Submodule.Quotient.mk_eq_zero,
        algebraMap_smul, ← algebraMap_smul B a y]
      exact (Submodule.traceDual A K (1 : Submodule B L)).smul_mem (algebraMap A B a) hy
@[simp] theorem mulByTraceDualQuotientMap_mk (y : L)
    (hy : y ∈ Submodule.traceDual A K (1 : Submodule B L)) (k : K) :
    mulByTraceDualQuotientMap A K B L y hy (Submodule.Quotient.mk k) =
      Submodule.Quotient.mk (k • y) := (rfl)

end TraceDualQuotient

section TraceDualEquiv

variable (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure B A L]

omit [IsDomain A] [IsFractionRing A K] in
/-- Reconstruct `w : B` as `∑ i, a i • b i` from its traces against a dual family `(b, y)`. -/
private theorem sum_smul_eq_of_dualFamily {n : ℕ} (b : Fin n → B) (y : Fin n → L)
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x)
    (w : B) (a : Fin n → A)
    (ha : ∀ i, algebraMap A K (a i) = Algebra.trace K L (y i * algebraMap B L w)) :
    ∑ i, a i • b i = w := by
  apply IsIntegralClosure.algebraMap_injective B A L
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate K L).1 _ fun x ↦ ?_
  rw [Algebra.traceForm_apply, mul_comm, mul_sub, map_sub, sub_eq_zero, map_sum, Finset.mul_sum,
    map_sum]
  conv_rhs => rw [← hsum x, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsm : algebraMap B L (a i • b i) = algebraMap A K (a i) • algebraMap B L (b i) := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A K L, ← Algebra.smul_def]
  rw [hsm, mul_smul_comm, smul_mul_assoc, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ha i,
    mul_comm]

omit [IsDomain A] [IsFractionRing A K] in
/-- Lift `ψ : M →ₗ[A] K ⧸ A` to `M →ₗ[B] L ⧸ Bᵛ` using a finite trace-dual family `(b, y)`. -/
private def traceDualLiftOfDualFamily {M : Type*} [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] {n : ℕ} (b : Fin n → B) (y : Fin n → L)
    (hy : ∀ i, y i ∈ Submodule.traceDual A K (1 : Submodule B L))
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x)
    (ψ : M →ₗ[A] (K ⧸ (1 : Submodule A K))) :
    M →ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) where
  toFun m := ∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (ψ (b i • m))
  map_add' _ _ := by simp only [smul_add, map_add, Finset.sum_add_distrib]
  map_smul' c m := by
    choose t ht using fun i j ↦ Submodule.mem_traceDual.mp (hy i) (algebraMap B L (c * b j))
      (Submodule.mem_one.mpr ⟨c * b j, rfl⟩)
    have htb (j : Fin n) : ∑ i, t i j • b i = c * b j :=
      sum_smul_eq_of_dualFamily A K B L b y hsum (c * b j) (fun i ↦ t i j) fun i ↦ ht i j
    have hty (i : Fin n) : ∑ j, algebraMap A K (t i j) • y j = algebraMap B L c * y i := by
      conv_rhs => rw [← hsum (algebraMap B L c * y i)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [ht i j, Algebra.traceForm_apply, map_mul (algebraMap B L)]; congr 2; ring
    have hstep (i : Fin n) (q : K ⧸ (1 : Submodule A K)) :
        c • mulByTraceDualQuotientMap A K B L (y i) (hy i) q =
          ∑ j, mulByTraceDualQuotientMap A K B L (y j) (hy j) (t i j • q) := by
      obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      simp_rw [← Submodule.Quotient.mk_smul, mulByTraceDualQuotientMap_mk,
        ← Submodule.Quotient.mk_smul]
      simp_rw [← Submodule.mkQ_apply]; rw [← map_sum]; congr 1
      calc c • (k • y i) = k • (algebraMap B L c * y i) := by simp only [Algebra.smul_def]; ring
        _ = ∑ j, k • (algebraMap A K (t i j) • y j) := by rw [← hty i, Finset.smul_sum]
        _ = ∑ j, (t i j • k) • y j := Finset.sum_congr rfl fun j _ ↦ by
          rw [smul_smul, mul_comm k, ← Algebra.smul_def]
    simp only [RingHom.id_apply, Finset.smul_sum]
    calc ∑ j, mulByTraceDualQuotientMap A K B L (y j) (hy j) (ψ (b j • (c • m)))
      = ∑ j, mulByTraceDualQuotientMap A K B L (y j) (hy j) (ψ ((∑ i, t i j • b i) • m)) :=
          Finset.sum_congr rfl fun j _ ↦ by rw [smul_smul, mul_comm (b j), htb j]
      _ = ∑ i, ∑ j, mulByTraceDualQuotientMap A K B L (y j) (hy j) (t i j • ψ (b i • m)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ ↦ by simp [Finset.sum_smul, smul_assoc]
      _ = ∑ i, c • mulByTraceDualQuotientMap A K B L (y i) (hy i) (ψ (b i • m)) :=
          Finset.sum_congr rfl fun i _ ↦ (hstep i _).symm

omit [IsDomain A] [IsFractionRing A K] in
@[simp] private theorem traceDualLiftOfDualFamily_apply {M : Type*} [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] {n : ℕ} (b : Fin n → B) (y : Fin n → L)
    (hy : ∀ i, y i ∈ Submodule.traceDual A K (1 : Submodule B L))
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x)
    (ψ : M →ₗ[A] (K ⧸ (1 : Submodule A K))) (m : M) :
    traceDualLiftOfDualFamily A K B L b y hy hsum ψ m =
      ∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (ψ (b i • m)) := rfl

omit [IsDomain A] [IsFractionRing A K] in
/-- Postcomposing `traceDualLiftOfDualFamily` with `traceDualQuotientMap` recovers `ψ`. -/
private theorem traceDualQuotientMap_traceDualLiftOfDualFamily {M : Type*} [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] {n : ℕ} (b : Fin n → B) (y : Fin n → L)
    (hy : ∀ i, y i ∈ Submodule.traceDual A K (1 : Submodule B L))
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x)
    (ψ : M →ₗ[A] (K ⧸ (1 : Submodule A K))) :
    traceDualQuotientMap A K B L ∘ₗ
        (traceDualLiftOfDualFamily A K B L b y hy hsum ψ).restrictScalars A = ψ := by
  choose a ha using fun i ↦ show ∃ a : A, algebraMap A K a = Algebra.trace K L (y i) by
    simpa [Algebra.traceForm_apply] using
      Submodule.mem_traceDual.mp (hy i) 1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have ha_sum : ∑ i, a i • b i = 1 :=
    sum_smul_eq_of_dualFamily A K B L b y hsum 1 a fun i ↦ by simp [ha i]
  have hcomp (i : Fin n) (q : K ⧸ (1 : Submodule A K)) :
      traceDualQuotientMap A K B L (mulByTraceDualQuotientMap A K B L (y i) (hy i) q) =
        a i • q := by
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [mulByTraceDualQuotientMap_mk, traceDualQuotientMap_mk, map_smul, smul_eq_mul, ← ha i,
      mul_comm k, ← Algebra.smul_def]; rfl
  ext m
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    traceDualLiftOfDualFamily_apply]
  rw [map_sum]; simp_rw [hcomp]
  rw [show ∑ i, a i • ψ (b i • m) = ψ ((∑ i, a i • b i) • m) by simp [Finset.sum_smul, smul_assoc],
    ha_sum, one_smul]

section FiniteProjective

variable [Module.Finite A B] [Module.Projective A B]

/-- **Inverse-different trace comparison for linear maps**: when `B` is finite projective over `A`,
postcomposition with `traceDualQuotientMap` gives `(M →ₗ[B] (L ⧸ Bᵛ)) ≃ₗ[A] (M →ₗ[A] (K ⧸ A))`. -/
def traceDualLinearMapEquiv (M : Type*) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] :
    (M →ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L))) ≃ₗ[A]
      (M →ₗ[A] (K ⧸ (1 : Submodule A K))) :=
  LinearEquiv.ofBijective
    { toFun := fun φ ↦ traceDualQuotientMap A K B L ∘ₗ φ.restrictScalars A
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp } <| by
    obtain ⟨n, b, y, hy, hsum⟩ := exists_sum_trace_mul_smul_eq A K (B := B) (L := L)
    refine Function.bijective_iff_has_inverse.mpr
      ⟨traceDualLiftOfDualFamily A K B L b y hy hsum, fun φ ↦ by
          ext m
          obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (φ m)
          simp only [traceDualLiftOfDualFamily_apply, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.comp_apply, LinearMap.restrictScalars_apply]
          have hbi (i : Fin n) : φ (b i • m) = Submodule.Quotient.mk (algebraMap B L (b i) * x) :=
            by rw [map_smul, ← hx, ← Submodule.Quotient.mk_smul, Algebra.smul_def]
          rw [← hx]; simp only [hbi, traceDualQuotientMap_mk, mulByTraceDualQuotientMap_mk]
          simp_rw [← Submodule.mkQ_apply]; rw [← map_sum]
          congr 1; simpa only [mul_comm x] using hsum x,
        traceDualQuotientMap_traceDualLiftOfDualFamily A K B L b y hy hsum⟩
@[simp] theorem traceDualLinearMapEquiv_apply {M : Type*} [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M]
    (φ : M →ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L))) (m : M) :
    traceDualLinearMapEquiv A K B L M φ m = traceDualQuotientMap A K B L (φ m) := (rfl)

/-- `traceDualLinearMapEquiv` is compatible with the `B`-module structure on `M`. -/
theorem traceDualLinearMapEquiv_smul_apply {M : Type*} [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] (b : B)
    (φ : M →ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L))) (m : M) :
    traceDualLinearMapEquiv A K B L M (b • φ) m = traceDualLinearMapEquiv A K B L M φ (b • m) := by
  simp [traceDualLinearMapEquiv_apply, map_smul]

/-- Explicit formula for `(traceDualLinearMapEquiv).symm` via any finite trace-dual family. -/
theorem traceDualLinearMapEquiv_symm_apply_of_dualFamily {M : Type*} [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] {n : ℕ} (b : Fin n → B) (y : Fin n → L)
    (hy : ∀ i, y i ∈ Submodule.traceDual A K (1 : Submodule B L))
    (hsum : ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x)
    (ψ : M →ₗ[A] (K ⧸ (1 : Submodule A K))) (m : M) :
    (traceDualLinearMapEquiv A K B L M).symm ψ m =
      ∑ i, mulByTraceDualQuotientMap A K B L (y i) (hy i) (ψ (b i • m)) := by
  have h : (traceDualLinearMapEquiv A K B L M).symm ψ =
      traceDualLiftOfDualFamily A K B L b y hy hsum ψ :=
    (traceDualLinearMapEquiv A K B L M).injective <| by
      rw [LinearEquiv.apply_symm_apply]
      exact (traceDualQuotientMap_traceDualLiftOfDualFamily A K B L b y hy hsum ψ).symm
  exact LinearMap.congr_fun h m

end FiniteProjective

end TraceDualEquiv

section PrincipalDifferent

variable (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsFractionRing B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsDedekindDomain B] [Module.IsTorsionFree A B]

/-- When `differentIdeal A B = Ideal.span {δ}`, dividing by `δ` induces a `B`-linear equivalence
`(L ⧸ B) ≃ₗ[B] (L ⧸ Bᵛ)`. -/
def quotientEquivTraceDualQuotientOfDifferentIdealEqSpan {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) :
    (L ⧸ (1 : Submodule B L)) ≃ₗ[B] (L ⧸ Submodule.traceDual A K (1 : Submodule B L)) :=
  let u : Lˣ := Units.mk0 (algebraMap B L δ)
    (algebraMap_ne_zero_of_differentIdeal_eq_span (R := A) (K := K) (L := L) hδ)
  Submodule.Quotient.equiv _ _ (u.mulRightLinearEquiv B).symm <| by
    ext y
    rw [Submodule.mem_map_equiv, mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hδ]
    simp [u]
@[simp] theorem quotientEquivTraceDualQuotientOfDifferentIdealEqSpan_mk {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) (x : L) :
    quotientEquivTraceDualQuotientOfDifferentIdealEqSpan A K B L hδ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x / algebraMap B L δ) := by
  simp [quotientEquivTraceDualQuotientOfDifferentIdealEqSpan, div_eq_mul_inv]
@[simp] theorem quotientEquivTraceDualQuotientOfDifferentIdealEqSpan_symm_mk {δ : B}
    (hδ : differentIdeal A B = Ideal.span {δ}) (x : L) :
    (quotientEquivTraceDualQuotientOfDifferentIdealEqSpan A K B L hδ).symm
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x * algebraMap B L δ) := (rfl)

end PrincipalDifferent

section DirectTrace

variable (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K] [IsIntegrallyClosed A] [IsIntegralClosure B A L] [FiniteDimensional K L]

/-- The direct `A`-linear trace map `L ⧸ B → K ⧸ A`, descending from `Algebra.trace K L`. -/
def directTraceQuotientMap : (L ⧸ (1 : Submodule B L)) →ₗ[A] (K ⧸ (1 : Submodule A K)) :=
  (traceDualQuotientMap A K B L).comp
    ((Submodule.factor Submodule.one_le_traceDual_one).restrictScalars A)
@[simp] theorem directTraceQuotientMap_mk (x : L) :
    directTraceQuotientMap A K B L (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Algebra.trace K L x) := (rfl)

/-- The direct trace pairing `L ⧸ B → (B →ₗ[A] (K ⧸ A))` sending `[x]` to `b ↦ [Tr_{L/K}(b x)]`. -/
def directTracePairing : (L ⧸ (1 : Submodule B L)) →ₗ[A] (B →ₗ[A] (K ⧸ (1 : Submodule A K))) where
  toFun q :=
    { toFun := fun b ↦ directTraceQuotientMap A K B L (b • q)
      map_add' := fun _ _ ↦ by rw [add_smul, map_add]
      map_smul' := fun _ _ ↦ by simp only [RingHom.id_apply, smul_assoc, map_smul] }
  map_add' _ _ := by ext; simp [smul_add, map_add]
  map_smul' a _ := by ext b; simp [smul_comm b a, map_smul]
@[simp] theorem directTracePairing_mk_apply (x : L) (b : B) :
    directTracePairing A K B L (Submodule.Quotient.mk x) b =
      Submodule.Quotient.mk (Algebra.trace K L (algebraMap B L b * x)) := by
  dsimp only [directTracePairing, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Submodule.Quotient.mk_smul, directTraceQuotientMap_mk, Algebra.smul_def]

/-- An element `[x] ∈ L ⧸ B` lies in the kernel of `directTracePairing` if and only if `x ∈ Bᵛ`. -/
theorem mem_ker_directTracePairing_iff (x : L) :
    Submodule.Quotient.mk (p := (1 : Submodule B L)) x ∈
        LinearMap.ker (directTracePairing A K B L) ↔
      x ∈ Submodule.traceDual A K (1 : Submodule B L) := by
  rw [LinearMap.mem_ker, LinearMap.ext_iff, Submodule.mem_traceDual]
  refine ⟨fun h y hy ↦ ?_, fun h b ↦ ?_⟩
  · obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hy
    simpa [Algebra.traceForm_apply, mul_comm, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_one] using h b
  · simpa [Algebra.traceForm_apply, mul_comm, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_one] using h (algebraMap B L b) (Submodule.mem_one.mpr ⟨b, rfl⟩)

/-- **Kernel of the naive trace pairing**: `ker(L ⧸ B → Hom_A(B, K ⧸ A))` is precisely the image
of the inverse different `Bᵛ` in `L ⧸ B`. -/
theorem ker_directTracePairing :
    LinearMap.ker (directTracePairing A K B L) =
      ((Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A).map
        ((1 : Submodule B L).mkQ.restrictScalars A) := by
  ext q; obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [mem_ker_directTracePairing_iff, Submodule.mem_map]
  refine ⟨fun hx ↦ ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ ↦ ?_⟩
  simpa using (Submodule.traceDual A K (1 : Submodule B L)).sub_mem hy
    (Submodule.one_le_traceDual_one ((Submodule.Quotient.eq (1 : Submodule B L)).mp hyx))

/-- The direct trace pairing `L ⧸ B → Hom_A(B, K ⧸ A)` is injective iff `Bᵛ = B`. -/
theorem ker_directTracePairing_eq_bot_iff :
    LinearMap.ker (directTracePairing A K B L) = ⊥ ↔
      Submodule.traceDual A K (1 : Submodule B L) = 1 := by
  rw [eq_bot_iff]
  refine ⟨fun h ↦ le_antisymm (fun x hx ↦ ?_) Submodule.one_le_traceDual_one, fun h q hq ↦ ?_⟩
  · have hq := h ((mem_ker_directTracePairing_iff A K B L x).mpr hx)
    rwa [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hq
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [mem_ker_directTracePairing_iff, h] at hq
    rwa [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]

/-- Over a Dedekind domain `B`, `directTracePairing` is injective iff `differentIdeal A B = ⊤`. -/
theorem ker_directTracePairing_eq_bot_iff_differentIdeal_eq_top
    [IsDomain A] [Algebra.IsSeparable K L] [IsDedekindDomain B] [Module.IsTorsionFree A B] :
    LinearMap.ker (directTracePairing A K B L) = ⊥ ↔ differentIdeal A B = ⊤ := by
  rw [ker_directTracePairing_eq_bot_iff]
  refine ⟨fun h ↦ eq_top_iff.mpr fun y _ ↦ ?_,
    fun h ↦ le_antisymm (fun x hx ↦ ?_) Submodule.one_le_traceDual_one⟩
  · rw [mem_differentIdeal_iff_forall_mem_traceDual (R := A) (K := K) (L := L), h]
    rintro _ hx; obtain ⟨b, rfl⟩ := Submodule.mem_one.mp hx
    exact Submodule.mem_one.mpr ⟨b * y, map_mul (algebraMap B L) b y⟩
  · simpa using (mem_traceDual_one_iff_forall_mem_differentIdeal (R := A) (K := K)).mp hx
      1 (h.symm ▸ Submodule.mem_top)

end DirectTrace

end TauCeti
