/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Algebra.Module.Projective.Schanuel
public import TauCeti.RingTheory.Adjoin.Polynomial.Basic
public import TauCeti.RingTheory.Flat.Extensions
public import TauCeti.RingTheory.PowerSeries.Ideal

/-!
# Submodules of power-series modules with an `X`-power-torsion quotient

Let `R` be a commutative ring, `F` a module over `R⟦X⟧` and `Λ ⊆ F` a submodule containing
`X ^ k F` for some `k`, so that the quotient `Q = F ⧸ Λ` is killed by `X ^ k`. For `F` free of
finite rank, the `R⟦X⟧`-submodules of `R⸨X⸩ⁿ` between `X ^ N R⟦X⟧ⁿ` and `X ^ (-N) R⟦X⟧ⁿ` are of
this form. This file compares projectivity of `Λ` over `R⟦X⟧` with projectivity of `Q` over the
coefficient ring `R`, for arbitrary `R`, including nonreduced and non-Noetherian ones.

* If `F` is projective and `Q` is projective over `R`, then `Λ` is projective over `R⟦X⟧`
  (`PowerSeries.projective_of_projective_quotient`). The proof resolves `Q` by
  `0 → R⟦X⟧ ⊗[R] Q → R⟦X⟧ ⊗[R] Q → Q → 0`, whose first map is `X ⊗ 1 - 1 ⊗ X`
  (`PowerSeries.koszulDiff`): for every module killed by a power of `X`, its range is the kernel
  of the multiplication map (`PowerSeries.range_koszulDiff`) and it is injective
  (`PowerSeries.injective_koszulDiff`). Schanuel's lemma then compares the two
  presentations `F → Q` and `R⟦X⟧ ⊗[R] Q → Q`.
* If `Λ` is flat over `R⟦X⟧` and `F ⧸ Λ₀` is flat over `R` for a submodule `Λ₀ ≤ Λ`, then `Q` is
  flat over `R` (`PowerSeries.flat_quotient_of_flat`). The point is that for an ideal `I` of `R`,
  `X` is a nonzerodivisor on `Λ ⧸ I Λ`, so `Λ ∩ I F = I Λ`
  (`PowerSeries.mem_smul_of_mem_of_mem_smul_top`).

The second statement is applied with `Λ₀ = X ^ N R⟦X⟧ⁿ ⊆ F = X ^ (-N) R⟦X⟧ⁿ`, where `F ⧸ Λ₀` is
free of finite rank over `R`; together with finite presentation it gives projectivity of `Q`.

Finally an `R`-submodule of a module killed by `X ^ k` that is stable under `X` is stable under
all of `R⟦X⟧` (`PowerSeries.smul_mem_of_forall_X_smul_mem`), so it is an `R⟦X⟧`-submodule
(`PowerSeries.submoduleOfXSMulMem`).

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1, the description of lattices of bounded pole order.
-/

public section

open scoped Polynomial PowerSeries TensorProduct
open TensorProduct LinearMap

namespace PowerSeries

variable {R : Type*} [CommRing R]

section Ideal

/-- In a flat `R⟦X⟧`-module `P`, divisibility of `X ^ k • p` by the extension of an ideal of `R`
implies that of `p`: `X` is a nonzerodivisor on `P ⧸ I P`. -/
theorem mem_map_C_smul_top_of_X_pow_smul_mem {P : Type*} [AddCommGroup P] [Module R⟦X⟧ P]
    [Module.Flat R⟦X⟧ P] {I : Ideal R} {k : ℕ} {p : P}
    (h : (X ^ k : R⟦X⟧) • p ∈ I.map C • (⊤ : Submodule R⟦X⟧ P)) :
    p ∈ I.map C • (⊤ : Submodule R⟦X⟧ P) := by
  set J := I.map (C : R →+* R⟦X⟧)
  have hreg : IsSMulRegular (R⟦X⟧ ⧸ J) (X ^ k : R⟦X⟧) :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem J _).mpr fun _ ha ↦
      (X_pow_mul_mem_map_C_iff k).mp ha
  let e := quotTensorEquivQuotSMul P J
  have he : (X ^ k : R⟦X⟧) • e.symm (Submodule.Quotient.mk p) = (X ^ k : R⟦X⟧) • 0 := by
    rw [← map_smul, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).mpr h,
      map_zero, smul_zero]
  rw [← Submodule.Quotient.mk_eq_zero, ← e.symm.map_eq_zero_iff]
  exact IsSMulRegular.rTensor P hreg he

/-- Let `Λ ⊆ F` be a flat `R⟦X⟧`-submodule containing `X ^ k F`. Then `Λ ∩ I F = I Λ` for every
ideal `I` of `R`. -/
theorem mem_smul_of_mem_of_mem_smul_top {F : Type*} [AddCommGroup F] [Module R⟦X⟧ F]
    [Module R F] [IsScalarTower R R⟦X⟧ F] {Λ : Submodule R⟦X⟧ F} [Module.Flat R⟦X⟧ Λ] {k : ℕ}
    (hk : ∀ f : F, (X ^ k : R⟦X⟧) • f ∈ Λ) {I : Ideal R} {m : F} (hm : m ∈ Λ)
    (hmI : m ∈ I • (⊤ : Submodule R F)) : m ∈ I • Λ.restrictScalars R := by
  have hsmul : (X ^ k : R⟦X⟧) • m ∈ I • Λ.restrictScalars R := by
    refine Submodule.smul_induction_on (p := fun x ↦ (X ^ k : R⟦X⟧) • x ∈ I • Λ.restrictScalars R)
      hmI (fun r hr f _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [smul_comm]
      exact Submodule.smul_mem_smul hr (hk f)
    · rw [smul_add]
      exact add_mem hx hy
  rw [← Ideal.smul_restrictScalars, Submodule.restrictScalars_mem, algebraMap_eq] at hsmul ⊢
  have hX : (X ^ k : R⟦X⟧) • (⟨m, hm⟩ : Λ) ∈ I.map C • (⊤ : Submodule R⟦X⟧ Λ) :=
    (Submodule.mem_smul_top_iff _ Λ _).mpr hsmul
  exact (Submodule.mem_smul_top_iff _ Λ ⟨m, hm⟩).mp (mem_map_C_smul_top_of_X_pow_smul_mem hX)

/-- **Flatness of an `X`-power-torsion quotient.** Let `Λ₀ ≤ Λ` be `R⟦X⟧`-submodules of `F` such
that `Λ` contains `X ^ k F`, `Λ` is flat over `R⟦X⟧` and `F ⧸ Λ₀` is flat over `R`. Then `F ⧸ Λ`
is flat over `R`. -/
theorem flat_quotient_of_flat {F : Type*} [AddCommGroup F] [Module R⟦X⟧ F] [Module R F]
    [IsScalarTower R R⟦X⟧ F] {Λ₀ Λ : Submodule R⟦X⟧ F} (hΛ₀ : Λ₀ ≤ Λ) {k : ℕ}
    (hk : ∀ f : F, (X ^ k : R⟦X⟧) • f ∈ Λ) [Module.Flat R⟦X⟧ Λ] [Module.Flat R (F ⧸ Λ₀)] :
    Module.Flat R (F ⧸ Λ) := by
  let g : (F ⧸ Λ₀) →ₗ[R] F ⧸ Λ := (Submodule.factor hΛ₀).restrictScalars R
  let q : F →ₗ[R] F ⧸ Λ₀ := Λ₀.mkQ.restrictScalars R
  have hq : Function.Surjective q := Λ₀.mkQ_surjective
  refine Module.Flat.of_surjective_of_ker_inf_smul_top_le g (Submodule.factor_surjective hΛ₀)
    fun I _ y ⟨hy, hyI⟩ ↦ ?_
  rw [← LinearMap.range_eq_top.mpr hq, LinearMap.range_eq_map, ← Submodule.map_smul''] at hyI
  obtain ⟨m, hmI, rfl⟩ := hyI
  have hm : m ∈ Λ := by
    simpa [g, q, Submodule.Quotient.mk_eq_zero] using LinearMap.mem_ker.mp hy
  have hle : (Λ.restrictScalars R).map q ≤ LinearMap.ker g := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [g, q, Submodule.Quotient.mk_eq_zero] using hx
  refine Submodule.smul_mono le_rfl hle ?_
  rw [← Submodule.map_smul'']
  exact Submodule.mem_map_of_mem (mem_smul_of_mem_of_mem_smul_top hk hm hmI)

end Ideal

section XStable

variable {R : Type*} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R⟦X⟧ M] [Module R M] [IsScalarTower R R⟦X⟧ M]
  {k : ℕ}

/-- In a module killed by `X ^ k`, an `R`-submodule stable under `X` is stable under every power
series. -/
theorem smul_mem_of_forall_X_smul_mem (hk : ∀ m : M, (X ^ k : R⟦X⟧) • m = 0)
    {W : Submodule R M} (hW : ∀ w ∈ W, (X : R⟦X⟧) • w ∈ W) (a : R⟦X⟧) {w : M} (hw : w ∈ W) :
    a • w ∈ W := by
  rw [eq_shift_mul_X_pow_add_trunc k a, add_smul, mul_smul, hk, smul_zero, zero_add,
    ← Polynomial.eval₂_C_X_eq_coe, ← algebraMap_eq, ← Polynomial.aeval_def]
  exact Polynomial.aeval_apply_smul_mem_of_le_comap' hw _ X hW

/-- An `R`-submodule stable under `X` of a module killed by `X ^ k`, as an `R⟦X⟧`-submodule. -/
def submoduleOfXSMulMem (hk : ∀ m : M, (X ^ k : R⟦X⟧) • m = 0) (W : Submodule R M)
    (hW : ∀ w ∈ W, (X : R⟦X⟧) • w ∈ W) : Submodule R⟦X⟧ M where
  toAddSubmonoid := W.toAddSubmonoid
  smul_mem' a _ hw := smul_mem_of_forall_X_smul_mem hk hW a hw

@[simp]
theorem mem_submoduleOfXSMulMem {hk : ∀ m : M, (X ^ k : R⟦X⟧) • m = 0} {W : Submodule R M}
    {hW : ∀ w ∈ W, (X : R⟦X⟧) • w ∈ W} {m : M} : m ∈ submoduleOfXSMulMem hk W hW ↔ m ∈ W :=
  Iff.rfl

@[simp]
theorem restrictScalars_submoduleOfXSMulMem (hk : ∀ m : M, (X ^ k : R⟦X⟧) • m = 0)
    (W : Submodule R M) (hW : ∀ w ∈ W, (X : R⟦X⟧) • w ∈ W) :
    (submoduleOfXSMulMem hk W hW).restrictScalars R = W :=
  Submodule.ext fun _ ↦ Iff.rfl

/-- In a module killed by `X ^ k`, the `R⟦X⟧`-submodule made from an `R⟦X⟧`-submodule is that
submodule. -/
@[simp]
theorem submoduleOfXSMulMem_restrictScalars (hk : ∀ m : M, (X ^ k : R⟦X⟧) • m = 0)
    (W : Submodule R⟦X⟧ M) (hW : ∀ w ∈ W.restrictScalars R, (X : R⟦X⟧) • w ∈ W.restrictScalars R) :
    submoduleOfXSMulMem hk (W.restrictScalars R) hW = W :=
  Submodule.ext fun _ ↦ Iff.rfl

/-- In a module killed by `X ^ k`, a finitely generated `R⟦X⟧`-submodule is finitely generated
over `R`: it is spanned by the `X ^ i • x` for `i < k` and `x` among its generators. -/
theorem fg_restrictScalars_of_fg (hk : ∀ m : M, (X ^ k : R⟦X⟧) • m = 0)
    {W : Submodule R⟦X⟧ M} (hW : W.FG) : (W.restrictScalars R).FG := by
  let : Module R[X] M := Module.compHom M (algebraMap R[X] R⟦X⟧)
  have : IsScalarTower R[X] R⟦X⟧ M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R R[X] M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    -- The polynomial module was defined by restriction along this algebra map.
    change (algebraMap R[X] R⟦X⟧ (Polynomial.C r)) • m = r • m
    simp [algebraMap_apply', ← algebraMap_eq]
  let W' := W.restrictScalars R[X]
  have hW' : W'.FG := by
    obtain ⟨s, hs⟩ := hW
    refine ⟨s, le_antisymm (Submodule.span_le.mpr ?_) ?_⟩
    · intro x hx
      -- Restriction of scalars retains the carrier, so use the power-series generating set.
      change x ∈ W
      rw [← hs]
      exact Submodule.subset_span hx
    · let P := Submodule.span R[X] (s : Set M)
      have hP : ∀ w ∈ P.restrictScalars R, (X : R⟦X⟧) • w ∈ P.restrictScalars R := by
        intro w hw
        have h := P.smul_mem Polynomial.X hw
        -- The polynomial action is restriction along the power-series algebra map.
        change (algebraMap R[X] R⟦X⟧ Polynomial.X) • w ∈ P at h
        simpa [algebraMap_apply'] using h
      have hspan : W ≤ submoduleOfXSMulMem hk (P.restrictScalars R) hP := by
        rw [← hs]
        exact Submodule.span_le.mpr fun x hx ↦ Submodule.subset_span hx
      exact hspan
  exact TauCeti.Algebra.fg_restrictScalars_of_forall_pow_smul_eq_zero
    (Polynomial.adjoin_X (R := R)) hW' (fun y _ ↦ ⟨k, by
      -- Compute the restricted polynomial action through the defining algebra map.
      change (algebraMap R[X] R⟦X⟧ (Polynomial.X ^ k)) • y = 0
      simpa [algebraMap_apply'] using hk y⟩)

end XStable

section Resolution

variable (Q : Type*) [AddCommGroup Q] [Module R⟦X⟧ Q] [Module R Q] [IsScalarTower R R⟦X⟧ Q]

variable (R) in
/-- The map `X ⊗ 1 - 1 ⊗ X` on `R⟦X⟧ ⊗[R] Q`, for an `R⟦X⟧`-module `Q`. When `Q` is killed by a
power of `X`, it is injective with cokernel `Q`. -/
noncomputable def koszulDiff : R⟦X⟧ ⊗[R] Q →ₗ[R⟦X⟧] R⟦X⟧ ⊗[R] Q :=
  (X : R⟦X⟧) • LinearMap.id - ((LinearMap.lsmul R⟦X⟧ Q X).restrictScalars R).baseChange R⟦X⟧

variable {Q}

@[simp]
theorem koszulDiff_tmul (a : R⟦X⟧) (q : Q) :
    koszulDiff R Q (a ⊗ₜ q) = (X * a) ⊗ₜ q - a ⊗ₜ ((X : R⟦X⟧) • q) := by
  simp [koszulDiff, smul_tmul']

/-- The multiplication map `R⟦X⟧ ⊗[R] Q → Q` kills the image of `X ⊗ 1 - 1 ⊗ X`. -/
theorem liftBaseChange_comp_koszulDiff :
    (LinearMap.id : Q →ₗ[R] Q).liftBaseChange R⟦X⟧ ∘ₗ koszulDiff R Q = 0 :=
  TensorProduct.AlgebraTensorModule.curry_injective <| LinearMap.ext₂ fun a q ↦ by
    simp [mul_smul, smul_comm a]

/-- For `Q` killed by `X ^ k`, the image of `X ⊗ 1 - 1 ⊗ X` is the kernel of the multiplication
map `R⟦X⟧ ⊗[R] Q → Q`. -/
theorem range_koszulDiff {k : ℕ} (hk : ∀ q : Q, (X ^ k : R⟦X⟧) • q = 0) :
    LinearMap.range (koszulDiff R Q) =
      LinearMap.ker ((LinearMap.id : Q →ₗ[R] Q).liftBaseChange R⟦X⟧) := by
  refine le_antisymm (LinearMap.range_le_ker_iff.mpr liftBaseChange_comp_koszulDiff) ?_
  set S := LinearMap.range (koszulDiff R Q)
  -- The power series `a` with `a ⊗ q - 1 ⊗ a q ∈ S` for all `q` contain `1`, are stable under
  -- `X`, and contain `X ^ k R⟦X⟧`; they form an `R`-submodule, so they are everything.
  let T : Submodule R R⟦X⟧ :=
    { carrier := {a | ∀ q : Q, a ⊗ₜ q - (1 : R⟦X⟧) ⊗ₜ (a • q) ∈ S}
      add_mem' ha hb q := by
        simpa [add_tmul, add_smul, tmul_add, add_sub_add_comm] using add_mem (ha q) (hb q)
      zero_mem' q := by simp
      smul_mem' r a ha q := by
        have h := S.smul_mem (algebraMap R R⟦X⟧ r) (ha q)
        rwa [algebraMap_smul, smul_sub, smul_tmul', ← tmul_smul, ← smul_assoc] at h }
  have hX {a : R⟦X⟧} (ha : a ∈ T) : X * a ∈ T := fun q ↦ by
    have := add_mem (S.smul_mem X (ha q)) (LinearMap.mem_range_self (koszulDiff R Q) (1 ⊗ₜ (a • q)))
    simpa [smul_tmul', mul_smul, smul_sub] using this
  have hpow (n : ℕ) : (X ^ n : R⟦X⟧) ∈ T := by
    induction n with
    | zero => intro q; simp
    | succ n ih => rw [pow_succ']; exact hX ih
  have hT (a : R⟦X⟧) : a ∈ T := by
    rw [eq_shift_mul_X_pow_add_trunc k a, ← Polynomial.eval₂_C_X_eq_coe, eval₂_trunc_eq_sum_range]
    refine add_mem (fun q ↦ ?_) (sum_mem fun n _ ↦ ?_)
    · have h := S.smul_mem (mk fun i ↦ coeff (i + k) a) (hpow k q)
      rw [hk, tmul_zero, sub_zero, smul_tmul', smul_eq_mul] at h
      rwa [mul_smul, hk, smul_zero, tmul_zero, sub_zero]
    · rw [← algebraMap_eq, ← Algebra.smul_def]
      exact T.smul_mem _ (hpow n)
  have hsub (x : R⟦X⟧ ⊗[R] Q) :
      x - 1 ⊗ₜ ((LinearMap.id : Q →ₗ[R] Q).liftBaseChange R⟦X⟧ x) ∈ S := by
    induction x with
    | tmul a q => simpa using hT a q
    | add x y hx hy => simpa [tmul_add, add_sub_add_comm] using add_mem hx hy
  intro x hx
  simpa [LinearMap.mem_ker.mp hx] using hsub x

/-- For `Q` killed by a power of `X`, the map `X ⊗ 1 - 1 ⊗ X` on `R⟦X⟧ ⊗[R] Q` is injective. -/
theorem injective_koszulDiff {k : ℕ} (hk : ∀ q : Q, (X ^ k : R⟦X⟧) • q = 0) :
    Function.Injective (koszulDiff R Q) := by
  set f : Module.End R Q := Algebra.lsmul R R Q (X : R⟦X⟧)
  set x : Module.End R⟦X⟧ (R⟦X⟧ ⊗[R] Q) := f.baseChange R⟦X⟧
  set y : Module.End R⟦X⟧ (R⟦X⟧ ⊗[R] Q) := (X : R⟦X⟧) • 1
  have hf (n : ℕ) (q : Q) : (f ^ n) q = (X ^ n : R⟦X⟧) • q := by
    rw [← map_pow (Algebra.lsmul R R Q) (X : R⟦X⟧) n]
    rfl
  have hfk : f ^ k = 0 := LinearMap.ext fun q ↦ by simp [hf, hk]
  have hxk : x ^ k = 0 := by
    rw [← LinearMap.baseChange_pow, hfk, LinearMap.baseChange_zero]
  -- `(∑ yⁱ x^(k-1-i)) (y - x) = y ^ k - x ^ k = X ^ k`, and `X ^ k ⊗ 1` has a left inverse.
  have hd : koszulDiff R Q = y - x := by
    have hf' : (LinearMap.lsmul R⟦X⟧ Q X).restrictScalars R = f := LinearMap.ext fun _ ↦ rfl
    rw [koszulDiff, hf', ← Module.End.one_eq_id]
  have hgeom : (∑ i ∈ Finset.range k, y ^ i * x ^ (k - 1 - i)) * koszulDiff R Q = y ^ k := by
    have hc : Commute y x := (Commute.one_left x).smul_left (X : R⟦X⟧)
    rw [hd, Commute.geom_sum₂_mul (R := Module.End R⟦X⟧ (R⟦X⟧ ⊗[R] Q)) hc k, hxk]
    exact sub_zero (y ^ k)
  have hyk : y ^ k = (X ^ k : R⟦X⟧) • 1 := by simp [y, smul_pow]
  have hy (z : R⟦X⟧ ⊗[R] Q) : (y ^ k) z = (LinearMap.mulLeft R (X ^ k : R⟦X⟧)).rTensor Q z := by
    rw [hyk]
    exact AlgebraTensorModule.smul_eq_lsmul_rTensor (R := R) (M := R⟦X⟧) _ _
  -- Multiplication by `X ^ k` on `R⟦X⟧` has the `R`-linear left inverse shifting coefficients.
  let s : R⟦X⟧ →ₗ[R] R⟦X⟧ :=
    { toFun a := mk fun i ↦ coeff (i + k) a
      map_add' a b := by ext; simp
      map_smul' r a := by ext; simp }
  have hs : s ∘ₗ LinearMap.mulLeft R (X ^ k : R⟦X⟧) = LinearMap.id :=
    LinearMap.ext fun a ↦ by ext n; simp [s, coeff_X_pow_mul']
  have hl : Function.LeftInverse (s.rTensor Q) ((LinearMap.mulLeft R (X ^ k : R⟦X⟧)).rTensor Q) :=
    fun z ↦ by rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hs, LinearMap.rTensor_id,
      LinearMap.id_apply]
  have hinj : Function.Injective (y ^ k) := fun u v h ↦ by
    rw [hy, hy] at h
    exact hl.injective h
  intro u v huv
  apply hinj
  rw [← hgeom, mul_apply_eq_comp, mul_apply_eq_comp]
  exact congrArg _ huv

/-- **Projectivity of a submodule with `X`-power-torsion quotient.** Let `F` be a projective
`R⟦X⟧`-module and `Λ ⊆ F` a submodule containing `X ^ k F`. If `F ⧸ Λ` is projective over `R`,
then `Λ` is projective over `R⟦X⟧`. -/
theorem projective_of_projective_quotient {F : Type*} [AddCommGroup F] [Module R⟦X⟧ F]
    [Module R F] [IsScalarTower R R⟦X⟧ F] [Module.Projective R⟦X⟧ F] {Λ : Submodule R⟦X⟧ F}
    {k : ℕ} (hk : ∀ f : F, (X ^ k : R⟦X⟧) • f ∈ Λ) [Module.Projective R (F ⧸ Λ)] :
    Module.Projective R⟦X⟧ Λ := by
  have hkQ (q : F ⧸ Λ) : (X ^ k : R⟦X⟧) • q = 0 := by
    induction q using Submodule.Quotient.induction_on
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hk _
  let μ := (LinearMap.id : (F ⧸ Λ) →ₗ[R] F ⧸ Λ).liftBaseChange R⟦X⟧
  have hμ : Function.Surjective μ := fun q ↦ ⟨1 ⊗ₜ q, by simp [μ]⟩
  -- `ker μ ≅ R⟦X⟧ ⊗[R] (F ⧸ Λ)` through `X ⊗ 1 - 1 ⊗ X`, so it is projective.
  have : Module.Projective R⟦X⟧ (LinearMap.ker μ) :=
    .of_equiv ((LinearEquiv.ofInjective _ (injective_koszulDiff hkQ)).trans
      (LinearEquiv.ofEq _ _ (range_koszulDiff hkQ)))
  have := Λ.mkQ.projective_ker_of_projective_ker Λ.mkQ_surjective μ hμ
  exact .of_equiv (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ Λ))

end Resolution

end PowerSeries
