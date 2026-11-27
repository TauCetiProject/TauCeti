/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Module.Lattice
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Flags of finite Laurent coefficient windows

The native lattice quotient `latticeQuotient R V a b` records the coefficients in `[a,b)`.
Decreasing the upper bound gives a quotient map; decreasing the lower bound gives an
inclusion. These are the maps induced by the quotient and inclusion of Laurent-series
lattices, respectively. They commute with multiplication by `X`.

Cutting an interval at an intermediate exponent splits its underlying coefficient module
into two windows. The resulting splittings are coefficient-linear; they need not respect
multiplication by `X`. This distinction matters when imposing stability conditions on
submodules of successively larger windows.

All scalar extension comparisons use finite coefficient products, so apply to arbitrary
coefficient algebras. The coefficient-ring action is the native coefficientwise Hahn-module
action, and power series act by convolution. No Laurent-series algebra instance is used.
-/

public section

open scoped LaurentSeries PowerSeries TensorProduct

namespace TauCeti.HahnModule

open _root_.HahnModule

section Maps

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]
variable {a a' b b' c : ℤ}

/-- Drop the coefficients at and above `b` from the window `[a,b')`. -/
noncomputable def latticeQuotientProjection (a : ℤ) (h : b ≤ b') :
    latticeQuotient R V a b' →ₗ[R] latticeQuotient R V a b :=
  Submodule.factor (Submodule.comap_mono (lattice_antitone R V h))

/-- The projection is the quotient map on representatives in the same Laurent lattice. -/
@[simp]
theorem latticeQuotientProjection_mk (h : b ≤ b') (f : lattice R V a) :
    latticeQuotientProjection R V a h (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk f := (rfl)

/-- Include `[a,b)` in `[a',b)` by its Laurent-series lattice inclusion. -/
noncomputable def latticeQuotientInclusion (h : a' ≤ a) (b : ℤ) :
    latticeQuotient R V a b →ₗ[R] latticeQuotient R V a' b :=
  Submodule.mapQ _ _ (Submodule.inclusion (lattice_antitone R V h))
    (fun _ hf ↦ hf)

/-- The inclusion is induced by the inclusion of Laurent-series lattices. -/
@[simp]
theorem latticeQuotientInclusion_mk (h : a' ≤ a) (f : lattice R V a) :
    latticeQuotientInclusion R V h b (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (Submodule.inclusion (lattice_antitone R V h) f) := (rfl)

/-- In coefficient coordinates the projection is restriction. -/
@[simp]
theorem latticeQuotientEquiv_projection (h : b ≤ b') (q : latticeQuotient R V a b')
    (k : Finset.Ico a b) :
    latticeQuotientEquiv R V a b (latticeQuotientProjection R V a h q) k =
      latticeQuotientEquiv R V a b' q
        ⟨k, Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp k.property).1,
          lt_of_lt_of_le (Finset.mem_Ico.mp k.property).2 h⟩⟩ := by
  induction q using Submodule.Quotient.induction_on with
  | _ f => simp

/-- In coefficient coordinates the inclusion extends by zero below its source bound. -/
@[simp]
theorem latticeQuotientEquiv_inclusion (h : a' ≤ a) (q : latticeQuotient R V a b)
    (k : Finset.Ico a' b) :
    latticeQuotientEquiv R V a' b (latticeQuotientInclusion R V h b q) k =
      if hk : a ≤ (k : ℤ) then
        latticeQuotientEquiv R V a b q
          ⟨k, Finset.mem_Ico.mpr ⟨hk, (Finset.mem_Ico.mp k.property).2⟩⟩
      else 0 := by
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    simp only [latticeQuotientInclusion_mk, latticeQuotientEquiv_mk,
      Submodule.coe_inclusion]
    split_ifs with hk
    · rfl
    · exact (mem_lattice_iff R V).mp f.property k (by omega)

/-- Successive upper cuts compose to the direct upper cut. -/
@[simp]
theorem latticeQuotientProjection_comp (h : b ≤ b') (h' : b' ≤ c) :
    (latticeQuotientProjection R V a h).comp (latticeQuotientProjection R V a h') =
      latticeQuotientProjection R V a (h.trans h') := by
  ext q
  rfl

/-- Successive lower extensions compose to the direct lower extension. -/
@[simp]
theorem latticeQuotientInclusion_comp (h : a' ≤ a) (h' : a ≤ b) :
    (latticeQuotientInclusion R V h c).comp (latticeQuotientInclusion R V h' c) =
      latticeQuotientInclusion R V (h.trans h') c := by
  ext q
  rfl

/-- Changing the lower and upper bounds in either order gives the same map. -/
theorem latticeQuotientProjection_comp_inclusion (ha : a' ≤ a) (hb : b ≤ b') :
    (latticeQuotientProjection R V a' hb).comp (latticeQuotientInclusion R V ha b') =
      (latticeQuotientInclusion R V ha b).comp (latticeQuotientProjection R V a hb) := by
  ext q
  rfl

/-- Cutting at the existing upper bound is the identity. -/
@[simp]
theorem latticeQuotientProjection_refl :
    latticeQuotientProjection R V a (le_refl b) = LinearMap.id := by
  ext q
  rfl

/-- Extending to the existing lower bound is the identity. -/
@[simp]
theorem latticeQuotientInclusion_refl :
    latticeQuotientInclusion R V (le_refl a) b = LinearMap.id := by
  ext q
  rfl

end Maps

section Coefficients

variable (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V]
variable {a b c : ℤ}

/-- Partition a coefficient window at an intermediate exponent. -/
def coefficientWindowSplit (hab : a ≤ b) (hbc : b ≤ c) :
    (Finset.Ico a c → V) ≃ₗ[R] (Finset.Ico a b → V) × (Finset.Ico b c → V) where
  toFun f := (fun k ↦ f ⟨k, Finset.mem_Ico.mpr
      ⟨(Finset.mem_Ico.mp k.property).1, (Finset.mem_Ico.mp k.property).2.trans_le hbc⟩⟩,
    fun k ↦ f ⟨k, Finset.mem_Ico.mpr
      ⟨hab.trans (Finset.mem_Ico.mp k.property).1, (Finset.mem_Ico.mp k.property).2⟩⟩)
  invFun f k := if hk : (k : ℤ) < b then
    f.1 ⟨k, Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp k.property).1, hk⟩⟩
    else f.2 ⟨k, Finset.mem_Ico.mpr ⟨by omega, (Finset.mem_Ico.mp k.property).2⟩⟩
  left_inv f := by
    ext k
    dsimp only
    split_ifs <;> rfl
  right_inv f := by
    apply Prod.ext
    · ext k
      simp [(Finset.mem_Ico.mp k.property).2]
    · ext k
      simp [not_lt.mpr (Finset.mem_Ico.mp k.property).1]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The first component restricts to the bottom interval. -/
@[simp]
theorem coefficientWindowSplit_apply_fst (hab : a ≤ b) (hbc : b ≤ c)
    (f : Finset.Ico a c → V) (k : Finset.Ico a b) :
    (coefficientWindowSplit R V hab hbc f).1 k =
      f ⟨k, Finset.mem_Ico.mpr
        ⟨(Finset.mem_Ico.mp k.property).1, (Finset.mem_Ico.mp k.property).2.trans_le hbc⟩⟩ :=
  (rfl)

/-- The second component restricts to the top interval. -/
@[simp]
theorem coefficientWindowSplit_apply_snd (hab : a ≤ b) (hbc : b ≤ c)
    (f : Finset.Ico a c → V) (k : Finset.Ico b c) :
    (coefficientWindowSplit R V hab hbc f).2 k =
      f ⟨k, Finset.mem_Ico.mpr
        ⟨hab.trans (Finset.mem_Ico.mp k.property).1, (Finset.mem_Ico.mp k.property).2⟩⟩ := (rfl)

/-- The inverse coefficient splitting concatenates the two vectors. -/
@[simp]
theorem coefficientWindowSplit_symm_apply (hab : a ≤ b) (hbc : b ≤ c)
    (f : (Finset.Ico a b → V) × (Finset.Ico b c → V)) (k : Finset.Ico a c) :
    (coefficientWindowSplit R V hab hbc).symm f k =
      if hk : (k : ℤ) < b then
        f.1 ⟨k, Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp k.property).1, hk⟩⟩
      else f.2 ⟨k, Finset.mem_Ico.mpr ⟨by omega, (Finset.mem_Ico.mp k.property).2⟩⟩ := (rfl)

end Coefficients

section Splitting

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]
variable {a b c : ℤ}

/-- Split a finite Laurent window into its bottom and top coefficient windows.
This is an equivalence of coefficient modules, not of power-series modules. -/
noncomputable def latticeQuotientSplit (hab : a ≤ b) (hbc : b ≤ c) :
    latticeQuotient R V a c ≃ₗ[R]
      latticeQuotient R V a b × latticeQuotient R V b c :=
  (latticeQuotientEquiv R V a c).trans ((coefficientWindowSplit R V hab hbc).trans
    ((latticeQuotientEquiv R V a b).symm.prodCongr
      (latticeQuotientEquiv R V b c).symm))

/-- The bottom component of the splitting is the native upper projection. -/
@[simp]
theorem latticeQuotientSplit_fst (hab : a ≤ b) (hbc : b ≤ c)
    (q : latticeQuotient R V a c) :
    (latticeQuotientSplit R V hab hbc q).1 = latticeQuotientProjection R V a hbc q := by
  apply (latticeQuotientEquiv R V a b).injective
  ext k
  simp [latticeQuotientSplit]

/-- In coefficient coordinates the top component restricts to the upper interval. -/
@[simp]
theorem latticeQuotientEquiv_split_snd (hab : a ≤ b) (hbc : b ≤ c)
    (q : latticeQuotient R V a c) (k : Finset.Ico b c) :
    latticeQuotientEquiv R V b c (latticeQuotientSplit R V hab hbc q).2 k =
      latticeQuotientEquiv R V a c q
        ⟨k, Finset.mem_Ico.mpr
          ⟨hab.trans (Finset.mem_Ico.mp k.property).1, (Finset.mem_Ico.mp k.property).2⟩⟩ := by
  simp [latticeQuotientSplit]

/-- The upper-window inclusion is the second summand of the splitting. -/
@[simp]
theorem latticeQuotientSplit_inclusion (hab : a ≤ b) (hbc : b ≤ c)
    (q : latticeQuotient R V b c) :
    latticeQuotientSplit R V hab hbc (latticeQuotientInclusion R V hab c q) = (0, q) := by
  apply Prod.ext
  · apply (latticeQuotientEquiv R V a b).injective
    ext k
    simp [latticeQuotientSplit_fst, not_le.mpr (Finset.mem_Ico.mp k.property).2]
  · apply (latticeQuotientEquiv R V b c).injective
    ext k
    simp [(Finset.mem_Ico.mp k.property).1]

/-- The lower extension is injective, including when its source window is empty. -/
theorem latticeQuotientInclusion_injective (h : a ≤ b) (c : ℤ) :
    Function.Injective (latticeQuotientInclusion R V h c) := by
  intro q q' heq
  apply (latticeQuotientEquiv R V b c).injective
  ext k
  have hk : a ≤ (k : ℤ) := h.trans (Finset.mem_Ico.mp k.property).1
  have := congrArg (fun x ↦ latticeQuotientEquiv R V a c x
    ⟨k, Finset.mem_Ico.mpr ⟨hk, (Finset.mem_Ico.mp k.property).2⟩⟩) heq
  simpa [(Finset.mem_Ico.mp k.property).1] using this

/-- Every upper projection is surjective. -/
theorem latticeQuotientProjection_surjective (a : ℤ) (h : b ≤ c) :
    Function.Surjective (latticeQuotientProjection R V a h) :=
  Submodule.factor_surjective (Submodule.comap_mono (lattice_antitone R V h))

/-- The kernel of the upper projection is exactly the upper-window inclusion. -/
theorem ker_latticeQuotientProjection (hab : a ≤ b) (hbc : b ≤ c) :
    LinearMap.ker (latticeQuotientProjection R V a hbc) =
      LinearMap.range (latticeQuotientInclusion R V hab c) := by
  ext q
  constructor
  · intro hq
    refine ⟨(latticeQuotientSplit R V hab hbc q).2, ?_⟩
    apply (latticeQuotientSplit R V hab hbc).injective
    rw [latticeQuotientSplit_inclusion]
    exact Prod.ext (by simpa using hq.symm) rfl
  · rintro ⟨x, rfl⟩
    have := congrArg Prod.fst (latticeQuotientSplit_inclusion R V hab hbc x)
    rw [latticeQuotientSplit_fst] at this
    exact this

/-- The top window identifies with the actual kernel of the upper projection. -/
noncomputable def latticeQuotientProjectionKerEquiv (hab : a ≤ b) (hbc : b ≤ c) :
    LinearMap.ker (latticeQuotientProjection R V a hbc) ≃ₗ[R] latticeQuotient R V b c :=
  (LinearEquiv.ofEq _ _ (ker_latticeQuotientProjection R V hab hbc)).trans
    (LinearEquiv.ofInjective (latticeQuotientInclusion R V hab c)
      (latticeQuotientInclusion_injective R V hab c)).symm

/-- The cokernel of the top-window inclusion is the bottom window. -/
noncomputable def latticeQuotientInclusionCokerEquiv (hab : a ≤ b) (hbc : b ≤ c) :
    (latticeQuotient R V a c ⧸ LinearMap.range (latticeQuotientInclusion R V hab c)) ≃ₗ[R]
      latticeQuotient R V a b :=
  (Submodule.quotEquivOfEq _ _ (ker_latticeQuotientProjection R V hab hbc).symm).trans
    ((latticeQuotientProjection R V a hbc).quotKerEquivOfSurjective
      (latticeQuotientProjection_surjective R V a hbc))

/-- The inverse splitting concatenates the two coefficient vectors. In particular, setting
one component to zero gives the coefficient-linear section or retraction of the flag. -/
@[simp]
theorem latticeQuotientEquiv_split_symm (hab : a ≤ b) (hbc : b ≤ c)
    (q : latticeQuotient R V a b) (r : latticeQuotient R V b c) (k : Finset.Ico a c) :
    latticeQuotientEquiv R V a c ((latticeQuotientSplit R V hab hbc).symm (q, r)) k =
      if hk : (k : ℤ) < b then
        latticeQuotientEquiv R V a b q
          ⟨k, Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp k.property).1, hk⟩⟩
      else latticeQuotientEquiv R V b c r
        ⟨k, Finset.mem_Ico.mpr ⟨by omega, (Finset.mem_Ico.mp k.property).2⟩⟩ := by
  simp [latticeQuotientSplit]

/-- On quotient classes the cokernel comparison is the native upper projection. -/
@[simp]
theorem latticeQuotientInclusionCokerEquiv_mk (hab : a ≤ b) (hbc : b ≤ c)
    (q : latticeQuotient R V a c) :
    latticeQuotientInclusionCokerEquiv R V hab hbc (Submodule.Quotient.mk q) =
      latticeQuotientProjection R V a hbc q := by
  simp [latticeQuotientInclusionCokerEquiv]

/-- The inverse kernel comparison is the native inclusion on its underlying element. -/
@[simp]
theorem latticeQuotientProjectionKerEquiv_symm_coe (hab : a ≤ b) (hbc : b ≤ c)
    (q : latticeQuotient R V b c) :
    ((latticeQuotientProjectionKerEquiv R V hab hbc).symm q : latticeQuotient R V a c) =
      latticeQuotientInclusion R V hab c q := by
  simp [latticeQuotientProjectionKerEquiv]

/-- The top component gives the kernel comparison without choosing a representative. -/
@[simp]
theorem latticeQuotientProjectionKerEquiv_apply (hab : a ≤ b) (hbc : b ≤ c)
    (q : LinearMap.ker (latticeQuotientProjection R V a hbc)) :
    latticeQuotientProjectionKerEquiv R V hab hbc q =
      (latticeQuotientSplit R V hab hbc q.val).2 := by
  obtain ⟨x, rfl⟩ := (latticeQuotientProjectionKerEquiv R V hab hbc).symm.surjective q
  simp

end Splitting

section Shift

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
variable {a a' b b' : ℤ}

/-- Truncated multiplication by `X` on a finite Laurent window. -/
noncomputable def latticeQuotientShift (a b : ℤ) : Module.End R (latticeQuotient R V a b) :=
  DistribSMul.toLinearMap R _ (PowerSeries.X : R⟦X⟧)

/-- The truncated shift is the inherited power-series action. -/
theorem latticeQuotientShift_apply (a b : ℤ) (q : latticeQuotient R V a b) :
    latticeQuotientShift R V a b q = (PowerSeries.X : R⟦X⟧) • q := (rfl)

/-- The coefficient of the truncated shift is the preceding coefficient, or zero at the
bottom of the window. -/
@[simp]
theorem latticeQuotientEquiv_shift (q : latticeQuotient R V a b) (k : Finset.Ico a b) :
    latticeQuotientEquiv R V a b (latticeQuotientShift R V a b q) k =
      if hk : a ≤ (k : ℤ) - 1 then
        latticeQuotientEquiv R V a b q
          ⟨(k : ℤ) - 1, Finset.mem_Ico.mpr
            ⟨hk, by have := (Finset.mem_Ico.mp k.property).2; omega⟩⟩
      else 0 := by
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    simp only [latticeQuotientShift_apply, smul_latticeQuotient_mk, latticeQuotientEquiv_mk]
    rw [_root_.HahnModule.powerSeries_smul, HahnSeries.ofPowerSeries_X]
    have hc := coeff_single_smul_vadd (r := (1 : R)) (x := f.val)
      (b := (1 : ℤ)) (a := (k : ℤ) - 1)
    simp only [vadd_eq_add, one_smul] at hc
    have hkadd : (1 : ℤ) + ((k : ℤ) - 1) = k := by omega
    rw [hkadd] at hc
    rw [hc]
    split_ifs with hk
    · rfl
    · exact (mem_lattice_iff R V).mp f.property _ (by omega)

/-- Multiplication by `X` takes the class of `v Xᵏ` to the class of `v X^(k+1)`,
including when the latter monomial lies beyond the upper cut. -/
@[simp]
theorem latticeQuotientShift_mk_single {k : ℤ} (h : a ≤ k) (v : V) :
    latticeQuotientShift R V a b
        (Submodule.Quotient.mk ⟨of R (HahnSeries.single k v), of_single_mem_lattice R V h v⟩) =
      Submodule.Quotient.mk ⟨of R (HahnSeries.single (k + 1) v),
        of_single_mem_lattice R V (by omega : a ≤ k + 1) v⟩ := by
  rw [latticeQuotientShift_apply, smul_latticeQuotient_mk]
  congr 1
  apply Subtype.ext
  simpa using _root_.HahnModule.X_pow_smul_single (R := R) 1 k v

/-- Upper projections intertwine truncated multiplication by `X`. -/
theorem latticeQuotientProjection_shift (h : b ≤ b') (q : latticeQuotient R V a b') :
    latticeQuotientProjection R V a h (latticeQuotientShift R V a b' q) =
      latticeQuotientShift R V a b (latticeQuotientProjection R V a h q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    simp only [latticeQuotientShift_apply, smul_latticeQuotient_mk,
      latticeQuotientProjection_mk]

/-- Lower inclusions intertwine truncated multiplication by `X`. -/
theorem latticeQuotientInclusion_shift (h : a' ≤ a) (q : latticeQuotient R V a b) :
    latticeQuotientInclusion R V h b (latticeQuotientShift R V a b q) =
      latticeQuotientShift R V a' b (latticeQuotientInclusion R V h b q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    simp only [latticeQuotientShift_apply, smul_latticeQuotient_mk,
      latticeQuotientInclusion_mk]
    rfl

/-- A one-degree window has zero truncated shift. -/
@[simp]
theorem latticeQuotientShift_add_one (a : ℤ) : latticeQuotientShift R V a (a + 1) = 0 := by
  apply LinearMap.ext
  intro q
  simpa only [latticeQuotientShift_apply, pow_one, LinearMap.zero_apply] using
    X_pow_smul_latticeQuotient_eq_zero R V a (a + 1) 1 (by omega) q

/-- The top one-degree kernel is annihilated by the ambient truncated shift. -/
theorem latticeQuotientShift_eq_zero_of_mem_ker
    (q : latticeQuotient R V a (b + 1))
    (hq : q ∈ LinearMap.ker (latticeQuotientProjection R V a (by omega : b ≤ b + 1))) :
    latticeQuotientShift R V a (b + 1) q = 0 := by
  by_cases hab : a ≤ b
  · rw [ker_latticeQuotientProjection R V hab (by omega)] at hq
    obtain ⟨x, rfl⟩ := hq
    rw [← latticeQuotientInclusion_shift, latticeQuotientShift_add_one]
    simp
  · simpa only [latticeQuotientShift_apply, pow_one] using
      X_pow_smul_latticeQuotient_eq_zero R V a (b + 1) 1 (by omega) q

/-- The bottom one-degree cokernel has zero induced shift. -/
theorem latticeQuotientInclusionCoker_mk_shift_eq_zero
    (q : latticeQuotient R V a b) :
    (Submodule.Quotient.mk (latticeQuotientShift R V a b q) :
      latticeQuotient R V a b ⧸
        LinearMap.range (latticeQuotientInclusion R V (by omega : a ≤ a + 1) b)) = 0 := by
  by_cases h : a + 1 ≤ b
  · apply (latticeQuotientInclusionCokerEquiv R V (by omega : a ≤ a + 1) h).injective
    rw [latticeQuotientInclusionCokerEquiv_mk, latticeQuotientProjection_shift,
      latticeQuotientShift_add_one]
    simp
  · have hz : latticeQuotientShift R V a b q = 0 := by
      simpa only [latticeQuotientShift_apply, pow_one] using
        X_pow_smul_latticeQuotient_eq_zero R V a b 1 (by omega) q
    simp [hz]

end Shift

section BaseChange

variable (R V A : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  [CommRing A] [Algebra R A]

/-- Extension of coefficients on finite Laurent windows. No flatness is required. -/
noncomputable def latticeQuotientBaseChange (a b : ℤ) :
    A ⊗[R] latticeQuotient R V a b ≃ₗ[A] latticeQuotient A (A ⊗[R] V) a b :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
    (latticeQuotientEquiv R V a b)).trans
    ((TensorProduct.piRight R A A (fun _ : Finset.Ico a b ↦ V)).trans
      (latticeQuotientEquiv A (A ⊗[R] V) a b).symm)

/-- On a pure tensor the coefficient comparison tensors each coefficient separately. -/
@[simp]
theorem latticeQuotientEquiv_baseChange_tmul (a b : ℤ) (x : A)
    (q : latticeQuotient R V a b) (k : Finset.Ico a b) :
    latticeQuotientEquiv A (A ⊗[R] V) a b
      (latticeQuotientBaseChange R V A a b (x ⊗ₜ[R] q)) k =
        x ⊗ₜ[R] latticeQuotientEquiv R V a b q k := by
  simp [latticeQuotientBaseChange]

/-- Scalar extension commutes with upper projection, even along nonflat coefficient maps. -/
theorem latticeQuotientBaseChange_projection {a b b' : ℤ} (h : b ≤ b')
    (q : A ⊗[R] latticeQuotient R V a b') :
    latticeQuotientBaseChange R V A a b
        ((latticeQuotientProjection R V a h).baseChange A q) =
      latticeQuotientProjection A (A ⊗[R] V) a h
        (latticeQuotientBaseChange R V A a b' q) := by
  induction q using TensorProduct.inductionOn with
  | add q q' hq hq' => simp [hq, hq']
  | tmul x q =>
    apply (latticeQuotientEquiv A (A ⊗[R] V) a b).injective
    ext k
    simp

/-- Scalar extension commutes with lower inclusion, even along nonflat coefficient maps. -/
theorem latticeQuotientBaseChange_inclusion {a a' b : ℤ} (h : a' ≤ a)
    (q : A ⊗[R] latticeQuotient R V a b) :
    latticeQuotientBaseChange R V A a' b
        ((latticeQuotientInclusion R V h b).baseChange A q) =
      latticeQuotientInclusion A (A ⊗[R] V) h b
        (latticeQuotientBaseChange R V A a b q) := by
  induction q using TensorProduct.inductionOn with
  | add q q' hq hq' => simp [hq, hq']
  | tmul x q =>
    apply (latticeQuotientEquiv A (A ⊗[R] V) a' b).injective
    ext k
    by_cases hk : a ≤ (k : ℤ) <;> simp [hk]

/-- Scalar extension commutes with the truncated shift. -/
theorem latticeQuotientBaseChange_shift (a b : ℤ)
    (q : A ⊗[R] latticeQuotient R V a b) :
    latticeQuotientBaseChange R V A a b ((latticeQuotientShift R V a b).baseChange A q) =
      latticeQuotientShift A (A ⊗[R] V) a b (latticeQuotientBaseChange R V A a b q) := by
  induction q using TensorProduct.inductionOn with
  | add q q' hq hq' => simp [hq, hq']
  | tmul x q =>
    apply (latticeQuotientEquiv A (A ⊗[R] V) a b).injective
    ext k
    simp only [LinearMap.baseChange_tmul, latticeQuotientEquiv_baseChange_tmul,
      latticeQuotientEquiv_shift]
    split_ifs <;> simp

/-- Scalar extension respects the coefficient-linear splitting of a window. -/
theorem latticeQuotientBaseChange_split_tmul {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c)
    (x : A) (q : latticeQuotient R V a c) :
    latticeQuotientSplit A (A ⊗[R] V) hab hbc
        (latticeQuotientBaseChange R V A a c (x ⊗ₜ[R] q)) =
      (latticeQuotientBaseChange R V A a b
        (x ⊗ₜ[R] (latticeQuotientSplit R V hab hbc q).1),
      latticeQuotientBaseChange R V A b c
        (x ⊗ₜ[R] (latticeQuotientSplit R V hab hbc q).2)) := by
  apply Prod.ext
  · apply (latticeQuotientEquiv A (A ⊗[R] V) a b).injective
    ext k
    simp
  · apply (latticeQuotientEquiv A (A ⊗[R] V) b c).injective
    ext k
    simp

end BaseChange

section Boundary

variable (R V : Type*) [Ring R] [AddCommGroup V] [Module R V]

/-- A one-degree Laurent window is its coefficient module. -/
noncomputable def latticeQuotientSingleEquiv (a : ℤ) :
    latticeQuotient R V a (a + 1) ≃ₗ[R] V := by
  letI : Unique (Finset.Ico a (a + 1)) :=
    { default := ⟨a, by simp⟩
      uniq := fun k ↦ Subtype.ext (by
        dsimp only
        have := Finset.mem_Ico.mp k.property
        omega) }
  exact (latticeQuotientEquiv R V a (a + 1)).trans (LinearEquiv.funUnique _ R V)

/-- The one-degree comparison reads the coefficient at its lower bound. -/
@[simp]
theorem latticeQuotientSingleEquiv_apply (a : ℤ) (q : latticeQuotient R V a (a + 1)) :
    latticeQuotientSingleEquiv R V a q =
      latticeQuotientEquiv R V a (a + 1) q ⟨a, by simp⟩ := (rfl)

/-- A window with no exponents is zero. -/
theorem latticeQuotient_eq_zero_of_le {a b : ℤ} (h : b ≤ a)
    (q : latticeQuotient R V a b) : q = 0 := by
  apply (latticeQuotientEquiv R V a b).injective
  ext k
  have := Finset.mem_Ico.mp k.property
  omega

end Boundary

section FreeBoundary

variable (R : Type*) [Ring R]

/-- For the transition from `[-N,N)` to `[-N-1,N+1)`, the top kernel is a copy of `Rⁿ`.
The equivalence exhibits a basis with `n` elements even over the zero ring. -/
noncomputable def latticeQuotientTopEquiv (N n : ℕ) :
    LinearMap.ker (latticeQuotientProjection R (Fin n → R) (-(N : ℤ))
      (by omega : (N : ℤ) ≤ N + 1)) ≃ₗ[R] (Fin n → R) :=
  (latticeQuotientProjectionKerEquiv R (Fin n → R) (by omega : -(N : ℤ) ≤ N)
    (by omega : (N : ℤ) ≤ N + 1)).trans
      (latticeQuotientSingleEquiv R (Fin n → R) N)

/-- In the same transition, the bottom cokernel is a copy of `Rⁿ`. -/
noncomputable def latticeQuotientBottomEquiv (N n : ℕ) :
    (latticeQuotient R (Fin n → R) (-(N : ℤ) - 1) (N + 1) ⧸
      LinearMap.range (latticeQuotientInclusion R (Fin n → R)
        (by omega : -(N : ℤ) - 1 ≤ -N) (N + 1))) ≃ₗ[R] (Fin n → R) :=
  (latticeQuotientInclusionCokerEquiv R (Fin n → R)
    (by omega : -(N : ℤ) - 1 ≤ -N) (by omega : -(N : ℤ) ≤ N + 1)).trans
      (by
        have h : -(N : ℤ) - 1 + 1 = -N := by omega
        exact h ▸ latticeQuotientSingleEquiv R (Fin n → R) (-(N : ℤ) - 1))

/-- With no vector coordinates every coefficient window is zero, regardless of its bounds. -/
theorem latticeQuotient_fin_zero_eq_zero (a b : ℤ)
    (q : latticeQuotient R (Fin 0 → R) a b) : q = 0 := by
  apply (latticeQuotientEquiv R (Fin 0 → R) a b).injective
  ext k i
  exact Fin.elim0 i

end FreeBoundary

end TauCeti.HahnModule
