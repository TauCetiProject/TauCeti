/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LieRinehartAlgebra.Defs
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg

/-!
# The Chevalley–Eilenberg complex of a Lie–Rinehart algebra

For a Lie–Rinehart algebra `(R, A, L)`, the submodule `L [⋀^Fin n]→ₗ[A] A` inside
`L [⋀^Fin n]→ₗ[R] A` is preserved by the Lie derivative action of `L` and by the
Chevalley–Eilenberg differential `TauCeti.LieModule.Cohomology.d R L A n`. Scalar restriction from
`A` to `R` is injective on alternating maps, so Cartan's identity `L_x = ι_x ∘ d + d ∘ ι_x`, the
commutation rules `[L_x, ι_y] = ι_{[x, y]}`, `[L_x, L_y] = L_{[x, y]}`, `L_x ∘ d = d ∘ L_x`,
nilpotency `d ∘ d = 0`, and the Chevalley–Eilenberg formula transfer from
`TauCeti.LieModule.Cohomology`, assembling into `cochainComplex` and Rinehart `cohomology`.

## References

* G. S. Rinehart, *Differential forms on general commutative algebras*, Trans. Amer. Math. Soc.
  108 (1963), 195–222.
* J. Huebschmann, *Poisson cohomology and quantization*, J. Reine Angew. Math. 408 (1990), 57–113.
-/

public section

open Fin AlternatingMap

namespace AlternatingMap

section RestrictScalars
variable (R : Type*) [Semiring R] {A M N ι : Type*} [Semiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

/-- Reinterpret an `A`-multilinear alternating map as an `R`-multilinear alternating map along a
compatible scalar action of `R` on `A`. -/
def restrictScalars (f : M [⋀^ι]→ₗ[A] N) : M [⋀^ι]→ₗ[R] N where
  __ := f.toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq

@[simp] theorem coe_restrictScalars (f : M [⋀^ι]→ₗ[A] N) : ⇑(f.restrictScalars R) = f := (rfl)
@[simp] theorem restrictScalars_apply (f : M [⋀^ι]→ₗ[A] N) (v : ι → M) :
    f.restrictScalars R v = f v := (rfl)

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M [⋀^ι]→ₗ[A] N) → M [⋀^ι]→ₗ[R] N) :=
  fun _ _ h ↦ ext fun v ↦ congr($h v)

@[simp] theorem restrictScalars_zero : (0 : M [⋀^ι]→ₗ[A] N).restrictScalars R = 0 := (rfl)
@[simp] theorem restrictScalars_add (f g : M [⋀^ι]→ₗ[A] N) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R := (rfl)
@[simp] theorem restrictScalars_smul {S : Type*} [Monoid S] [DistribMulAction S N]
    [SMulCommClass A S N] [SMulCommClass R S N] (c : S) (f : M [⋀^ι]→ₗ[A] N) :
    (c • f).restrictScalars R = c • f.restrictScalars R := (rfl)
end RestrictScalars

section RestrictScalarsRing
variable (R : Type*) [Ring R] {A M N : Type*} [Ring A] [SMul R A] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module A M] [Module R N] [Module A N] [IsScalarTower R A M] [IsScalarTower R A N]

@[simp] theorem restrictScalars_neg {ι : Type*} (f : M [⋀^ι]→ₗ[A] N) :
    (-f).restrictScalars R = -f.restrictScalars R := (rfl)
@[simp] theorem restrictScalars_sub {ι : Type*} (f g : M [⋀^ι]→ₗ[A] N) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R := (rfl)
end RestrictScalarsRing

section RestrictScalarsCommSemiring
variable (R : Type*) [CommSemiring R] {A M N : Type*} [CommSemiring A] [SMul R A]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module A M] [Module R N] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]

@[simp] theorem restrictScalars_curryLeft {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[A] N) (m : M) :
    (f.curryLeft m).restrictScalars R = (f.restrictScalars R).curryLeft m := (rfl)
end RestrictScalarsCommSemiring

/-- Build an `A`-multilinear alternating map from an `R`-multilinear alternating map that is
`A`-homogeneous in its first argument. -/
def ofCurryLeftSMul {R A M N : Type*} [CommRing R] [Semiring A]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module A M] [Module R N] [Module A N] {n : ℕ}
    (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (m : M) (w : Fin n → M), f.curryLeft (a • m) w = a • f.curryLeft m w) :
    M [⋀^Fin (n + 1)]→ₗ[A] N where
  toFun := f
  map_update_add' := by intro _ m i x y; exact f.map_update_add m i x y
  map_update_smul' := by
    intro inst v i a m; obtain rfl : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    rw [← insertNth_removeNth i m v, ← insertNth_removeNth i (a • m) v,
      f.map_insertNth, f.map_insertNth]
    simpa only [curryLeft_apply_apply] using
      (smul_comm ((-1 : ℤ) ^ (i : ℕ)) a (f (Matrix.vecCons m (i.removeNth v)))).symm ▸
        congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) (hf a m (i.removeNth v))
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq

@[simp] theorem restrictScalars_ofCurryLeftSMul {R A M N : Type*} [CommRing R] [Semiring A]
    [SMul R A] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module A M] [Module R N] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N] {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hf : ∀ (a : A) (m : M) (w : Fin n → M), f.curryLeft (a • m) w = a • f.curryLeft m w) :
    (ofCurryLeftSMul f hf).restrictScalars R = f := by ext v; simp [ofCurryLeftSMul]

end AlternatingMap

namespace TauCeti.LieRinehartAlgebra.Cohomology

section LieDeriv
variable (R : Type*) [CommRing R] {A L : Type*} [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L] [Module A L] [LieRingModule L A]
  [LieRinehartRing A L] [LieRinehartAlgebra R A L]

private theorem lie_restrictScalars_update_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) (v : ι → L) (i : ι) (a : A) (y : L) :
    ⁅x, ω.restrictScalars R⁆ (Function.update v i (a • y)) =
      a • ⁅x, ω.restrictScalars R⁆ (Function.update v i y) := by
  rw [AlternatingMap.lie_apply, AlternatingMap.lie_apply]
  have hval : ⁅x, (ω.restrictScalars R) (Function.update v i (a • y))⁆ =
      a • ⁅x, ω (Function.update v i y)⁆ + ⁅x, a⁆ * ω (Function.update v i y) := by
    rw [restrictScalars_apply, ω.map_update_smul, smul_eq_mul, LieRinehartRing.leibniz_mul_right]
  have hsum : ∑ j, (ω.restrictScalars R)
        (Function.update (Function.update v i (a • y)) j ⁅x, Function.update v i (a • y) j⁆) =
      a • ∑ j, ω (Function.update (Function.update v i y) j ⁅x, Function.update v i y j⁆) +
        ⁅x, a⁆ * ω (Function.update v i y) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i), smul_add, Finset.smul_sum]
    have hdiag : (ω.restrictScalars R)
          (Function.update (Function.update v i (a • y)) i ⁅x, Function.update v i (a • y) i⁆) =
        a • ω (Function.update (Function.update v i y) i ⁅x, Function.update v i y i⁆) +
          ⁅x, a⁆ * ω (Function.update v i y) := by
      simp only [restrictScalars_apply, Function.update_self, Function.update_idem,
        LieRinehartRing.leibniz_smul_right, ω.map_update_add, ω.map_update_smul, smul_eq_mul]
    have hoff : ∑ j ∈ Finset.univ.erase i, (ω.restrictScalars R)
          (Function.update (Function.update v i (a • y)) j ⁅x, Function.update v i (a • y) j⁆) =
        ∑ j ∈ Finset.univ.erase i,
          a • ω (Function.update (Function.update v i y) j ⁅x, Function.update v i y j⁆) := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [restrictScalars_apply, Function.update_of_ne hji, Function.update_of_ne hji,
        Function.update_comm hji.symm (a • y) ⁅x, v j⁆ v,
        Function.update_comm hji.symm y ⁅x, v j⁆ v, ω.map_update_smul]
    rw [hoff, hdiag]; abel
  rw [hval, hsum]; simp only [restrictScalars_apply, smul_eq_mul, mul_sub]; ring

/-- The Lie derivative of an `A`-multilinear alternating form `ω` along `x : L`, bundled as an
`R`-bilinear map. -/
def lieDeriv {ι : Type*} [Fintype ι] [inst₀ : DecidableEq ι] :
    L →ₗ[R] (L [⋀^ι]→ₗ[A] A) →ₗ[R] L [⋀^ι]→ₗ[A] A where
  toFun x :=
    { toFun ω :=
        { toFun := ⇑⁅x, ω.restrictScalars R⁆
          map_update_add' := by
            intro inst m i x₁ y; obtain rfl : inst = inst₀ := Subsingleton.elim _ _
            exact ⁅x, ω.restrictScalars R⁆.map_update_add m i x₁ y
          map_update_smul' := by
            intro inst v i a y; obtain rfl : inst = inst₀ := Subsingleton.elim _ _
            exact lie_restrictScalars_update_smul R x ω v i a y
          map_eq_zero_of_eq' := ⁅x, ω.restrictScalars R⁆.map_eq_zero_of_eq }
      map_add' _ _ := by
        ext v; simp only [AlternatingMap.coe_mk, MultilinearMap.coe_mk, add_apply,
          restrictScalars_add, lie_add]
      map_smul' c ω := by
        ext v; simp only [AlternatingMap.coe_mk, MultilinearMap.coe_mk, smul_apply,
          restrictScalars_smul, RingHom.id_apply]
        exact congr($(lie_smul c x (ω.restrictScalars R)) v) }
  map_add' x y := by
    ext ω v; simp only [LinearMap.coe_mk, AddHom.coe_mk, AlternatingMap.coe_mk,
      MultilinearMap.coe_mk, LinearMap.add_apply, add_apply]
    exact congr($(add_lie x y (ω.restrictScalars R)) v)
  map_smul' c x := by
    ext ω v; simp only [LinearMap.coe_mk, AddHom.coe_mk, AlternatingMap.coe_mk,
      MultilinearMap.coe_mk, LinearMap.smul_apply, smul_apply, RingHom.id_apply]
    exact congr($(smul_lie c x (ω.restrictScalars R)) v)

@[simp] theorem restrictScalars_lieDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) :
    (lieDeriv R x ω).restrictScalars R = ⁅x, ω.restrictScalars R⁆ := by ext v; simp [lieDeriv]

@[simp] theorem lieDeriv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (ω : L [⋀^ι]→ₗ[A] A) (v : ι → L) :
    lieDeriv R x ω v = ⁅x, ω v⁆ - ∑ i, ω (Function.update v i ⁅x, v i⁆) := by
  rw [← restrictScalars_apply R (lieDeriv R x ω), restrictScalars_lieDeriv]
  exact AlternatingMap.lie_apply x (ω.restrictScalars R) v

/-- The Lie derivative commutes with the Lie bracket: `L_{[x, y]} = [L_x, L_y]`. -/
theorem lieDeriv_lie {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : L) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R ⁅x, y⁆ ω = lieDeriv R x (lieDeriv R y ω) - lieDeriv R y (lieDeriv R x ω) := by
  refine restrictScalars_injective R ?_
  rw [restrictScalars_sub, restrictScalars_lieDeriv, restrictScalars_lieDeriv,
    restrictScalars_lieDeriv, restrictScalars_lieDeriv, restrictScalars_lieDeriv,
    lie_lie x y (ω.restrictScalars R)]

/-- Commutator of Lie derivative and interior product: `ι_y (L_x ω) = L_x (ι_y ω) - ι_{[x,y]} ω`. -/
theorem curryLeft_lieDeriv {n : ℕ} (x y : L) (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) :
    (lieDeriv R x ω).curryLeft y = lieDeriv R x (ω.curryLeft y) - ω.curryLeft ⁅x, y⁆ := by
  refine restrictScalars_injective R ?_
  simpa only [restrictScalars_curryLeft, restrictScalars_lieDeriv, restrictScalars_sub] using
    AlternatingMap.curryLeft_lie x (ω.restrictScalars R) y

@[simp] theorem lieDeriv_smul_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : L) (a : A) (ω : L [⋀^ι]→ₗ[A] A) :
    lieDeriv R x (a • ω) = a • lieDeriv R x ω + ⁅x, a⁆ • ω := by
  ext v; simp only [lieDeriv_apply, smul_apply, add_apply, smul_eq_mul,
    LieRinehartRing.leibniz_mul_right]; rw [← Finset.mul_sum]; ring
end LieDeriv

section Differential
variable (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L] [Module A L] [LieRingModule L A]
  [LieRinehartRing A L] [LieRinehartAlgebra R A L]

variable {R A L} in
/-- Scalar derivation formula for the `R`-linear Chevalley–Eilenberg differential on `a • η`. -/
theorem d_restrict_smul_apply :
    ∀ {n : ℕ} (a : A) (η : L [⋀^Fin n]→ₗ[R] A) (v : Fin (n + 1) → L),
      TauCeti.LieModule.Cohomology.d R L A n (a • η) v =
        a * TauCeti.LieModule.Cohomology.d R L A n η v +
          ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (⁅v i, a⁆ * η (i.removeNth v))
  | 0, a, η, v => by
    rw [TauCeti.LieModule.Cohomology.d_zero_apply, TauCeti.LieModule.Cohomology.d_zero_apply,
      smul_apply, smul_eq_mul, LieRinehartRing.leibniz_mul_right, smul_eq_mul, Fin.sum_univ_one]
    simp [Subsingleton.elim (Fin.removeNth 0 v) ![]]
  | n + 1, a, η, v => by
    obtain ⟨x, w, rfl⟩ : ∃ x w, v = Matrix.vecCons x w := ⟨v 0, tail v, (cons_self_tail v).symm⟩
    have hcurry : (a • η).curryLeft x = a • η.curryLeft x := by ext u; rfl
    have hlie : ⁅x, a • η⁆ w = a * ⁅x, η⁆ w + ⁅x, a⁆ * η w := by
      simp only [AlternatingMap.lie_apply, smul_apply, smul_eq_mul,
        LieRinehartRing.leibniz_mul_right]; rw [← Finset.mul_sum]; ring
    have hsum : ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (⁅Matrix.vecCons x w i, a⁆ * η (i.removeNth (Matrix.vecCons x w))) =
        ⁅x, a⁆ * η w - ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
          (⁅w j, a⁆ * η.curryLeft x (j.removeNth w)) := by
      rw [Fin.sum_univ_succ]
      simp [Matrix.vecCons, removeNth_succ_cons, pow_succ, curryLeft_apply_apply, sub_eq_add_neg]
    rw [← curryLeft_apply_apply, TauCeti.LieModule.Cohomology.curryLeft_d_succ,
      ← curryLeft_apply_apply, TauCeti.LieModule.Cohomology.curryLeft_d_succ,
      sub_apply, sub_apply, hlie, hcurry, d_restrict_smul_apply a (η.curryLeft x) w, hsum, mul_sub]
    abel

variable {R A L} in
private theorem curryLeft_d_restrictScalars_smul :
    ∀ {n : ℕ} (ω : L [⋀^Fin n]→ₗ[A] A) (a : A) (x : L) (w : Fin n → L),
      (TauCeti.LieModule.Cohomology.d R L A n (ω.restrictScalars R)).curryLeft (a • x) w =
        a • (TauCeti.LieModule.Cohomology.d R L A n (ω.restrictScalars R)).curryLeft x w
  | 0, ω, a, x, w => by
    simp [TauCeti.LieModule.Cohomology.curryLeft_d_zero, AlternatingMap.lie_apply, smul_eq_mul]
  | n + 1, ω, a, x, w => by
    rw [TauCeti.LieModule.Cohomology.curryLeft_d_succ,
      TauCeti.LieModule.Cohomology.curryLeft_d_succ, sub_apply, sub_apply]
    have hcurry : (ω.restrictScalars R).curryLeft (a • x) =
        a • (ω.curryLeft x).restrictScalars R := by ext u; exact ω.map_vecCons_smul u a x
    have hlie : ⁅a • x, ω.restrictScalars R⁆ w =
        a * ⁅x, ω.restrictScalars R⁆ w +
          ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • (⁅w k, a⁆ * ω.curryLeft x (k.removeNth w)) := by
      rw [AlternatingMap.lie_apply, AlternatingMap.lie_apply]
      have hterm (k : Fin (n + 1)) : ω (Function.update w k ⁅a • x, w k⁆) =
          a * ω (Function.update w k ⁅x, w k⁆) -
            (-1 : ℤ) ^ (k : ℕ) • (⁅w k, a⁆ * ω.curryLeft x (k.removeNth w)) := by
        have hbr : ⁅a • x, w k⁆ = a • ⁅x, w k⁆ - ⁅w k, a⁆ • x := by
          rw [← lie_skew, LieRinehartRing.leibniz_smul_right, neg_add, ← smul_neg, lie_skew,
            sub_eq_add_neg]
        rw [hbr, ω.map_update_sub, ω.map_update_smul, ω.map_update_smul, smul_eq_mul, smul_eq_mul]
        congr 1
        rw [← insertNth_removeNth k x w, ω.map_insertNth, curryLeft_apply_apply,
          mul_comm (⁅w k, a⁆), smul_mul_assoc, mul_comm _ (⁅w k, a⁆)]
      simp only [restrictScalars_apply, LieRinehartRing.lie_smul_eq_mul, hterm, sub_eq_add_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]; ring
    rw [hlie, hcurry, d_restrict_smul_apply a ((ω.curryLeft x).restrictScalars R) w]
    simp only [restrictScalars_apply, smul_eq_mul, mul_sub]; abel

/-- The Chevalley–Eilenberg differential on `A`-multilinear alternating cochains of `(R, A, L)`. -/
def d (n : ℕ) : (L [⋀^Fin n]→ₗ[A] A) →ₗ[R] L [⋀^Fin (n + 1)]→ₗ[A] A where
  toFun ω := ofCurryLeftSMul (TauCeti.LieModule.Cohomology.d R L A n (ω.restrictScalars R))
    (curryLeft_d_restrictScalars_smul ω)
  map_add' _ _ := by refine restrictScalars_injective R ?_; simp
  map_smul' _ _ := by refine restrictScalars_injective R ?_; simp

variable {R A L}

@[simp] theorem restrictScalars_d (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) :
    (d R A L n ω).restrictScalars R =
      TauCeti.LieModule.Cohomology.d R L A n (ω.restrictScalars R) := by
  rw [d]; exact restrictScalars_ofCurryLeftSMul _ (curryLeft_d_restrictScalars_smul ω)

theorem d_apply_eq (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) (v : Fin (n + 1) → L) :
    d R A L n ω v = TauCeti.LieModule.Cohomology.d R L A n (ω.restrictScalars R) v := by
  rw [← restrictScalars_apply R, restrictScalars_d]

@[simp] theorem curryLeft_d_zero (ω : L [⋀^Fin 0]→ₗ[A] A) (x : L) :
    (d R A L 0 ω).curryLeft x = lieDeriv R x ω := by
  refine restrictScalars_injective R ?_
  simpa only [restrictScalars_curryLeft, restrictScalars_d, restrictScalars_lieDeriv] using
    TauCeti.LieModule.Cohomology.curryLeft_d_zero (ω.restrictScalars R) x

/-- **Cartan's magic formula** for Lie–Rinehart cochains: `ι_x (d ω) = L_x ω - d (ι_x ω)`. -/
@[simp] theorem curryLeft_d_succ {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (x : L) :
    (d R A L (n + 1) ω).curryLeft x = lieDeriv R x ω - d R A L n (ω.curryLeft x) := by
  refine restrictScalars_injective R ?_
  simpa only [restrictScalars_curryLeft, restrictScalars_d, restrictScalars_sub,
    restrictScalars_lieDeriv] using
    TauCeti.LieModule.Cohomology.curryLeft_d_succ (ω.restrictScalars R) x

@[simp] theorem d_zero_apply (ω : L [⋀^Fin 0]→ₗ[A] A) (v : Fin 1 → L) :
    d R A L 0 ω v = ⁅v 0, ω ![]⁆ := by
  rw [d_apply_eq, TauCeti.LieModule.Cohomology.d_zero_apply, restrictScalars_apply]

/-- **The Chevalley–Eilenberg formula** for a Lie–Rinehart cochain in positive degree. -/
theorem d_succ_apply {n : ℕ} (ω : L [⋀^Fin (n + 1)]→ₗ[A] A) (v : Fin (n + 2) → L) :
    d R A L (n + 1) ω v =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ⁅v i, ω (i.removeNth v)⁆ +
        ∑ i : Fin (n + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          ω (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆ (j.removeNth (i.castSucc.removeNth v))) := by
  simpa only [d_apply_eq, restrictScalars_apply] using
    TauCeti.LieModule.Cohomology.d_succ_apply (ω.restrictScalars R) v

/-- Scalar derivation rule for `d` on `A`-multilinear cochains. -/
theorem d_smul_apply {n : ℕ} (a : A) (ω : L [⋀^Fin n]→ₗ[A] A) (v : Fin (n + 1) → L) :
    d R A L n (a • ω) v = a * d R A L n ω v +
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (⁅v i, a⁆ * ω (i.removeNth v)) := by
  simpa only [d_apply_eq, restrictScalars_smul, restrictScalars_apply] using
    d_restrict_smul_apply (R := R) a (ω.restrictScalars R) v

@[simp] theorem lieDeriv_d (n : ℕ) (x : L) (ω : L [⋀^Fin n]→ₗ[A] A) :
    lieDeriv R x (d R A L n ω) = d R A L n (lieDeriv R x ω) := by
  refine restrictScalars_injective R ?_
  simpa only [restrictScalars_lieDeriv, restrictScalars_d] using
    TauCeti.LieModule.Cohomology.lie_d n x (ω.restrictScalars R)

/-- The Chevalley–Eilenberg differential of a Lie–Rinehart algebra squares to zero. -/
@[simp] theorem d_d (n : ℕ) (ω : L [⋀^Fin n]→ₗ[A] A) : d R A L (n + 1) (d R A L n ω) = 0 := by
  refine restrictScalars_injective R ?_
  simpa only [restrictScalars_d, restrictScalars_zero] using
    TauCeti.LieModule.Cohomology.d_d n (ω.restrictScalars R)

variable (R A L)

theorem d_comp_d (n : ℕ) : d R A L (n + 1) ∘ₗ d R A L n = 0 := LinearMap.ext (d_d n)

/-- The Chevalley–Eilenberg cochain complex of `(R, A, L)` in `ModuleCat R`. -/
@[expose] noncomputable def cochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (L [⋀^Fin n]→ₗ[A] A))
    (fun n ↦ ModuleCat.ofHom (d R A L n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, d_comp_d R A L, ModuleCat.ofHom_zero]

@[simp] theorem cochainComplex_X (n : ℕ) :
    (cochainComplex R A L).X n = ModuleCat.of R (L [⋀^Fin n]→ₗ[A] A) := (rfl)
@[simp] theorem cochainComplex_d_succ (n : ℕ) :
    (cochainComplex R A L).d n (n + 1) = ModuleCat.ofHom (d R A L n) := by simp [cochainComplex]

/-- The degree-`n` Rinehart cohomology `R`-module of `(R, A, L)`. -/
noncomputable abbrev cohomology (n : ℕ) : ModuleCat R := (cochainComplex R A L).homology n
end Differential

end TauCeti.LieRinehartAlgebra.Cohomology
