/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import TauCeti.FieldTheory.MilnorK.SteinbergPairing
public import TauCeti.LinearAlgebra.TensorAlgebra.ToTensorPower
public import TauCeti.RingTheory.MilnorK.Basic
import TauCeti.Data.List.OfFn

/-!
# Structural theorems for Milnor K-theory

This file complements `TauCeti.RingTheory.MilnorK.Basic` by characterizing the Steinberg kernel
degree by degree via `TauCeti.MilnorK.relationSubmodule`, equipping `TauCeti.MilnorK R` with an
internal `ℕ`-grading (`TauCeti.MilnorK.isInternal_degree`, `TauCeti.MilnorK.gradedAlgebraDegree`),
proving general graded-commutativity and permutation-sign rules over fields, and establishing
vanishing in degrees at least two for fields with cyclic unit group and positive characteristic
(in particular, finite fields).

## Main definitions

* `TauCeti.MilnorK.relationSubmodule`: the degree-`n` Steinberg relation submodule of
  `(⨂[ℤ]^n) (Additive Rˣ)`.
* `TauCeti.MilnorK.mapDegree`: functorial `ℤ`-linear map `degree R n →ₗ[ℤ] degree S n`.

## Main results

* `TauCeti.MilnorK.mem_ker_mk_iff` and `TauCeti.MilnorK.toTensorAlgebra_mem_ker_iff`:
  characterization of the Steinberg kernel degree by degree.
* `TauCeti.MilnorK.isInternal_degree`: `MilnorK R` is internally `ℕ`-graded by `MilnorK.degree R`.
* `TauCeti.MilnorK.mul_comm_of_mem_degree`: graded commutativity over a field.
* `TauCeti.MilnorK.symbol_ofFn_comp_perm`: permuting symbol entries multiplies by the sign.
* `TauCeti.MilnorK.subsingleton_degree_of_finite`: `MilnorK.degree F n` vanishes for finite `F`
  and `n ≥ 2`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §III.7.1, Example III.7.2(a).
-/

public section

namespace TauCeti

open scoped DirectSum TensorProduct

namespace MilnorK

section Basic

variable {R : Type*} [CommRing R]

/-- The product of two degree-one unit classes defines a Steinberg pairing on `R`. -/
theorem isSteinbergPairing_ofUnit_mul :
    IsSteinbergPairing (fun a b : Rˣ ↦ ofUnit a * ofUnit b) where
  map_mul_left a₁ a₂ b := by rw [ofUnit_mul, add_mul]
  map_mul_right a b₁ b₂ := by rw [ofUnit_mul, mul_add]
  steinberg := ofUnit_mul_ofUnit_of_add_eq_one

/-- A two-entry symbol equals `ofUnit a * ofUnit b`. -/
theorem symbol_pair (a b : Rˣ) : symbol [a, b] = ofUnit a * ofUnit b := by
  rw [symbol_cons, symbol_singleton]

/-- Replicating a unit `n` times produces `ofUnit a ^ n`. -/
theorem symbol_replicate (n : ℕ) (a : Rˣ) : symbol (List.replicate n a) = ofUnit a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, symbol_cons, ih, pow_succ']

/-- Inverting an entry negates the symbol. -/
theorem symbol_append_cons_inv (l₁ : List Rˣ) (a : Rˣ) (l₂ : List Rˣ) :
    symbol (l₁ ++ a⁻¹ :: l₂) = -symbol (l₁ ++ a :: l₂) := by
  simp only [symbol_append, symbol_cons, ofUnit_inv]
  rw [neg_mul (ofUnit a), mul_neg (symbol l₁)]

/-- Raising an entry to a natural power scales the symbol. -/
theorem symbol_append_cons_pow (l₁ : List Rˣ) (a : Rˣ) (n : ℕ) (l₂ : List Rˣ) :
    symbol (l₁ ++ (a ^ n) :: l₂) = n • symbol (l₁ ++ a :: l₂) := by
  simp only [symbol_append, symbol_cons, ofUnit_pow]
  rw [smul_mul_assoc n (ofUnit a), mul_smul_comm n (symbol l₁)]

/-- Raising an entry to an integer power scales the symbol. -/
theorem symbol_append_cons_zpow (l₁ : List Rˣ) (a : Rˣ) (n : ℤ) (l₂ : List Rˣ) :
    symbol (l₁ ++ (a ^ n) :: l₂) = n • symbol (l₁ ++ a :: l₂) := by
  simp only [symbol_append, symbol_cons, ofUnit_zpow]
  rw [smul_mul_assoc n (ofUnit a), mul_smul_comm n (symbol l₁)]

end Basic

section RelationSubmodule

variable (R : Type*) [CommRing R]

/-- The degree-`n` Steinberg relation submodule of `(⨂[ℤ]^n) (Additive Rˣ)`, spanned by pure
tensors having two consecutive entries whose underlying ring elements sum to `1`. -/
def relationSubmodule (n : ℕ) : Submodule ℤ ((⨂[ℤ]^n) (Additive Rˣ)) :=
  Submodule.span ℤ {t | ∃ (x : Fin n → Additive Rˣ) (i : ℕ) (hi : i + 1 < n),
    ((Additive.toMul (x ⟨i, by omega⟩) : Rˣ) : R) +
      ((Additive.toMul (x ⟨i + 1, hi⟩) : Rˣ) : R) = 1 ∧
    t = PiTensorProduct.tprod ℤ x}

/-- Definitional unfolding of `MilnorK.relationSubmodule`. -/
theorem relationSubmodule_def (n : ℕ) :
    relationSubmodule R n =
      Submodule.span ℤ {t | ∃ (x : Fin n → Additive Rˣ) (i : ℕ) (hi : i + 1 < n),
        ((Additive.toMul (x ⟨i, by omega⟩) : Rˣ) : R) +
          ((Additive.toMul (x ⟨i + 1, hi⟩) : Rˣ) : R) = 1 ∧
        t = PiTensorProduct.tprod ℤ x} :=
  (rfl)

/-- In degree `0`, the Steinberg relation submodule is `⊥`. -/
@[simp]
theorem relationSubmodule_zero : relationSubmodule R 0 = ⊥ :=
  eq_bot_iff.mpr <| Submodule.span_le.mpr fun _ ⟨_, _, hi, _, _⟩ ↦ by omega

/-- In degree `1`, the Steinberg relation submodule is `⊥`. -/
@[simp]
theorem relationSubmodule_one : relationSubmodule R 1 = ⊥ :=
  eq_bot_iff.mpr <| Submodule.span_le.mpr fun _ ⟨_, _, hi, _, _⟩ ↦ by omega

variable {R}

/-- A pure tensor with consecutive complementary entries belongs to `relationSubmodule R n`. -/
theorem tprod_mem_relationSubmodule {n : ℕ} (x : Fin n → Additive Rˣ) {i : ℕ} (hi : i + 1 < n)
    (h : ((Additive.toMul (x ⟨i, by omega⟩) : Rˣ) : R) +
      ((Additive.toMul (x ⟨i + 1, hi⟩) : Rˣ) : R) = 1) :
    PiTensorProduct.tprod ℤ x ∈ relationSubmodule R n :=
  Submodule.subset_span ⟨x, i, hi, h, rfl⟩

/-- Any `ℤ`-linear map between tensor powers sending generating pure tensors into
`relationSubmodule` preserves `relationSubmodule`. -/
theorem map_mem_relationSubmodule {S : Type*} [CommRing S] {m n : ℕ}
    (f : (⨂[ℤ]^m) (Additive Rˣ) →ₗ[ℤ] (⨂[ℤ]^n) (Additive Sˣ))
    (hf : ∀ (x : Fin m → Additive Rˣ) (i : ℕ) (hi : i + 1 < m),
      ((Additive.toMul (x ⟨i, by omega⟩) : Rˣ) : R) +
        ((Additive.toMul (x ⟨i + 1, hi⟩) : Rˣ) : R) = 1 →
      f (PiTensorProduct.tprod ℤ x) ∈ relationSubmodule S n)
    {a : (⨂[ℤ]^m) (Additive Rˣ)} (ha : a ∈ relationSubmodule R m) :
    f a ∈ relationSubmodule S n := by
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hu hv ↦ by rw [map_add]; exact Submodule.add_mem _ hu hv)
    (fun k _ _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ k hu) ha
  rintro _ ⟨x, i, hi, hxy, rfl⟩
  exact hf x i hi hxy

/-- Graded multiplication on the right preserves `relationSubmodule`. -/
theorem gMul_mem_relationSubmodule_left {m n : ℕ}
    {a : (⨂[ℤ]^m) (Additive Rˣ)} {b : (⨂[ℤ]^n) (Additive Rˣ)}
    (ha : a ∈ relationSubmodule R m) :
    GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) a b ∈
      relationSubmodule R (m + n) := by
  induction b using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    rw [← DirectSum.gMulLHom_apply_apply (R := ℤ), ← LinearMap.flip_apply, map_smul]
    refine Submodule.smul_mem _ r (map_mem_relationSubmodule
      ((DirectSum.gMulLHom (R := ℤ) (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ))).flip
        (PiTensorProduct.tprod ℤ y))
      (fun x i hi hxy ↦ ?_) ha)
    rw [LinearMap.flip_apply, DirectSum.gMulLHom_apply_apply, TensorPower.tprod_mul_tprod]
    refine tprod_mem_relationSubmodule (Fin.append x y) (i := i) (by omega) ?_
    have h1 : Fin.append x y ⟨i, by omega⟩ = x ⟨i, by omega⟩ := Fin.append_left x y ⟨i, by omega⟩
    have h2 : Fin.append x y ⟨i + 1, by omega⟩ = x ⟨i + 1, hi⟩ := Fin.append_left x y ⟨i + 1, hi⟩
    rwa [h1, h2]
  | add _ _ hy₁ hy₂ =>
    rw [← DirectSum.gMulLHom_apply_apply (R := ℤ), map_add, DirectSum.gMulLHom_apply_apply,
      DirectSum.gMulLHom_apply_apply]
    exact Submodule.add_mem _ hy₁ hy₂

/-- Graded multiplication on the left preserves `relationSubmodule`. -/
theorem gMul_mem_relationSubmodule_right {m n : ℕ}
    {a : (⨂[ℤ]^m) (Additive Rˣ)} {b : (⨂[ℤ]^n) (Additive Rˣ)}
    (hb : b ∈ relationSubmodule R n) :
    GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) a b ∈
      relationSubmodule R (m + n) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [← DirectSum.gMulLHom_apply_apply (R := ℤ), map_smul, LinearMap.smul_apply]
    refine Submodule.smul_mem _ r (map_mem_relationSubmodule
      (DirectSum.gMulLHom (R := ℤ) (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ))
        (PiTensorProduct.tprod ℤ x))
      (fun y i hi hxy ↦ ?_) hb)
    rw [DirectSum.gMulLHom_apply_apply, TensorPower.tprod_mul_tprod]
    refine tprod_mem_relationSubmodule (Fin.append x y) (i := m + i) (by omega) ?_
    have h1 : Fin.append x y ⟨m + i, by omega⟩ = y ⟨i, by omega⟩ :=
      Fin.append_right x y ⟨i, by omega⟩
    have h2 : Fin.append x y ⟨m + i + 1, by omega⟩ = y ⟨i + 1, hi⟩ := by
      rw [show (⟨m + i + 1, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨i + 1, hi⟩ from
        Fin.ext (by dsimp [Fin.natAdd]; omega), Fin.append_right]
    rwa [h1, h2]
  | add _ _ hx₁ hx₂ =>
    rw [← DirectSum.gMulLHom_apply_apply (R := ℤ), map_add, LinearMap.add_apply,
      DirectSum.gMulLHom_apply_apply, DirectSum.gMulLHom_apply_apply]
    exact Submodule.add_mem _ hx₁ hx₂

end RelationSubmodule

section KernelBridge

variable (R : Type*) [CommRing R]

private theorem mk_list_map_iota_eq_symbol {R : Type*} [CommRing R] (l : List (Additive Rˣ)) :
    (l.map fun u ↦ mk (R := R) (TensorAlgebra.ι ℤ u)).prod = symbol (l.map Additive.toMul) := by
  induction l with
  | nil => simp
  | cons u l ih => rw [List.map_cons, List.prod_cons, mk_ι, List.map_cons, symbol_cons, ih]

/-- The image of a pure tensor under `TensorPower.toTensorAlgebra` and `MilnorK.mk` is the
corresponding Milnor symbol. -/
theorem mk_toTensorAlgebra_tprod {n : ℕ} (x : Fin n → Additive Rˣ) :
    mk (TensorPower.toTensorAlgebra (PiTensorProduct.tprod ℤ x)) =
      symbol (List.ofFn fun i ↦ Additive.toMul (x i)) := by
  rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply, map_list_prod, List.map_ofFn]
  simpa [Function.comp_def, List.map_ofFn] using mk_list_map_iota_eq_symbol (List.ofFn x)

private theorem mk_toTensorAlgebra_eq_zero_of_mem_relationSubmodule {n : ℕ}
    {t : (⨂[ℤ]^n) (Additive Rˣ)} (ht : t ∈ relationSubmodule R n) :
    mk (TensorPower.toTensorAlgebra t) = 0 := by
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hu hv ↦ by rw [map_add, map_add, hu, hv, add_zero])
    (fun _ _ _ hu ↦ by rw [map_zsmul, map_zsmul, hu, smul_zero]) ht
  rintro _ ⟨x, i, hi, hab, rfl⟩
  rw [mk_toTensorAlgebra_tprod]
  have hsplit := List.ofFn_eq_take_cons_of_lt (fun j ↦ Additive.toMul (x j))
    (i := ⟨i, by omega⟩) (j := ⟨i + 1, hi⟩) (by simp)
  simp only [Nat.add_sub_cancel_left, Nat.sub_self, List.take_zero, List.append_assoc,
    List.cons_append, List.nil_append] at hsplit
  rw [hsplit]
  exact symbol_append_cons_cons_of_add_eq_one _ _ hab

private theorem directSum_mul_mem_relationSubmodule
    {u v : ⨁ k : ℕ, (⨂[ℤ]^k) (Additive Rˣ)}
    (h : (∀ k, u k ∈ relationSubmodule R k) ∨ (∀ k, v k ∈ relationSubmodule R k)) (n : ℕ) :
    (u * v) n ∈ relationSubmodule R n := by
  classical
  rw [← DirectSum.sum_support_of u, ← DirectSum.sum_support_of v, Finset.sum_mul,
    DirectSum.sum_apply]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [Finset.mul_sum, DirectSum.sum_apply]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [DirectSum.of_mul_of]
  by_cases hij : i + j = n
  · subst hij; rw [DirectSum.of_eq_same]
    exact h.elim (fun hu ↦ gMul_mem_relationSubmodule_left (hu i))
      (fun hv ↦ gMul_mem_relationSubmodule_right (hv j))
  · rw [DirectSum.of_eq_of_ne (i + j) n _ (Ne.symm hij)]; exact Submodule.zero_mem _

/-- An element of `TensorAlgebra ℤ (Additive Rˣ)` lies in the kernel of `MilnorK.mk` if and only
if each of its homogeneous tensor-power components lies in `relationSubmodule R n`. -/
theorem mem_ker_mk_iff (z : TensorAlgebra ℤ (Additive Rˣ)) :
    z ∈ RingHom.ker (mk (R := R)) ↔
      ∀ n : ℕ, TensorAlgebra.toDirectSum z n ∈ relationSubmodule R n := by
  constructor
  · intro hz
    let H : Set (TensorAlgebra ℤ (Additive Rˣ)) :=
      {w | ∀ n, TensorAlgebra.toDirectSum w n ∈ relationSubmodule R n}
    have hadd : ∀ {x y}, x ∈ H → y ∈ H → x + y ∈ H := fun hx hy n ↦ by
      rw [map_add, DirectSum.add_apply]; exact Submodule.add_mem _ (hx n) (hy n)
    let I : TwoSidedIdeal (TensorAlgebra ℤ (Additive Rˣ)) :=
      TwoSidedIdeal.mk' H (fun _ ↦ by simp) hadd
        (fun {x} hx n ↦ by
          rw [show -x = (-1 : ℤ) • x by abel, map_smul, DirectSum.smul_apply]
          exact Submodule.smul_mem _ _ (hx n))
        (fun hy n ↦ by rw [map_mul]; exact directSum_mul_mem_relationSubmodule R (.inr hy) n)
        (fun hx n ↦ by rw [map_mul]; exact directSum_mul_mem_relationSubmodule R (.inl hx) n)
    have hrel : milnorRel R ≤ I.ringCon := by
      intro _ _ h n
      rcases (milnorRel_iff R).mp h with ⟨a, b, hab, rfl, rfl⟩
      rw [sub_zero, map_mul, TensorAlgebra.toDirectSum_ι, TensorAlgebra.toDirectSum_ι,
        DirectSum.of_mul_of, TensorPower.tprod_mul_tprod]
      by_cases hn : 1 + 1 = n
      · subst hn; rw [DirectSum.of_eq_same]
        refine tprod_mem_relationSubmodule _ (i := 0) (by omega) ?_
        rw [show (⟨0, by omega⟩ : Fin (1 + 1)) = Fin.castAdd 1 0 from rfl, Fin.append_left,
          show (⟨1, by omega⟩ : Fin (1 + 1)) = Fin.natAdd 1 0 from rfl, Fin.append_right]
        simpa using hab
      · rw [DirectSum.of_eq_of_ne (1 + 1) n _ (Ne.symm hn)]; exact Submodule.zero_mem _
    have hz_rel : ringConGen (milnorRel R) z 0 :=
      mk_eq_mk_iff.mp ((RingHom.mem_ker.mp hz).trans (map_zero (mk (R := R))).symm)
    have hrc : z - 0 ∈ H :=
      (RingCon.ringConGen_le.mpr hrel : ringConGen (milnorRel R) ≤ I.ringCon) hz_rel
    rwa [sub_zero] at hrc
  · intro hz
    classical
    rw [RingHom.mem_ker, ← TensorAlgebra.ofDirectSum_toDirectSum z]
    conv_lhs => rw [← DirectSum.sum_support_of (TensorAlgebra.toDirectSum z)]
    rw [map_sum, map_sum]
    exact Finset.sum_eq_zero fun n _ ↦ by
      rw [TensorAlgebra.ofDirectSum_of]
      exact mk_toTensorAlgebra_eq_zero_of_mem_relationSubmodule R (hz n)

/-- A degree-`n` tensor lies in the kernel of `MilnorK.mk` if and only if it belongs to
`relationSubmodule R n`. -/
theorem toTensorAlgebra_mem_ker_iff {n : ℕ} (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    TensorPower.toTensorAlgebra t ∈ RingHom.ker (mk (R := R)) ↔
      t ∈ relationSubmodule R n := by
  rw [mem_ker_mk_iff, TensorAlgebra.toDirectSum_toTensorAlgebra]
  refine ⟨fun h ↦ by simpa [DirectSum.of_eq_same] using h n, fun ht k ↦ ?_⟩
  by_cases hnk : n = k
  · subst hnk; simpa [DirectSum.of_eq_same] using ht
  · rw [DirectSum.of_eq_of_ne n k _ (Ne.symm hnk)]; exact Submodule.zero_mem _

end KernelBridge

section Grading

variable (R : Type*) [CommRing R]

/-- The kernel of `MilnorK.mk` is a homogeneous ideal of `TensorAlgebra ℤ (Additive Rˣ)`. -/
theorem isHomogeneous_ker_mk :
    (RingHom.ker (mk (R := R))).IsHomogeneous
      (fun n : ℕ ↦
        (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n) := by
  classical
  let 𝒜 : ℕ → Submodule ℤ (TensorAlgebra ℤ (Additive Rˣ)) :=
    fun n ↦ (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n
  intro i z hz
  -- Each homogeneous piece of `z` coincides with the image of `toDirectSum z i`.
  have hcomp : (DirectSum.decompose 𝒜 z i : TensorAlgebra ℤ (Additive Rˣ)) =
      TensorPower.toTensorAlgebra (TensorAlgebra.toDirectSum z i) := by
    have hdecomp : DirectSum.decompose 𝒜 z =
        ∑ k ∈ (TensorAlgebra.toDirectSum z).support,
          DirectSum.of (fun k ↦ ↥(𝒜 k)) k
            (⟨TensorPower.toTensorAlgebra (TensorAlgebra.toDirectSum z k),
              TensorPower.toTensorAlgebra_mem_range_pow _⟩ : 𝒜 k) := by
      conv_lhs => rw [← TensorAlgebra.ofDirectSum_toDirectSum z,
        ← DirectSum.sum_support_of (TensorAlgebra.toDirectSum z)]
      rw [map_sum, DirectSum.decompose_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [TensorAlgebra.ofDirectSum_of]
      exact DirectSum.decompose_of_mem 𝒜 (TensorPower.toTensorAlgebra_mem_range_pow _)
    rw [hdecomp, DirectSum.sum_apply, Submodule.coe_sum]
    by_cases hi : i ∈ (TensorAlgebra.toDirectSum z).support
    · rw [Finset.sum_eq_single i (fun k _ hki ↦ by simp [DirectSum.of_eq_of_ne k i _ hki.symm])
        (fun h ↦ absurd hi h), DirectSum.of_eq_same]
    · rw [Finset.sum_eq_zero (fun k hk ↦ by
          simp [DirectSum.of_eq_of_ne k i _ (fun h ↦ hi (h ▸ hk))]),
        DFinsupp.notMem_support_iff.mp hi, map_zero]
  rw [RingHom.mem_ker, hcomp]
  exact RingHom.mem_ker.mp
    ((toTensorAlgebra_mem_ker_iff R _).mpr ((mem_ker_mk_iff R z).mp hz i))

private theorem degree_eq_map_range_pow (n : ℕ) :
    degree R n =
      ((TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n).map
        (mk (R := R)).toIntAlgHom.toLinearMap :=
  Submodule.ext fun _ ↦ mem_degree_iff

/-- `MilnorK R` is internally `ℕ`-graded by `MilnorK.degree R`. -/
theorem isInternal_degree : DirectSum.IsInternal (degree R) := by
  let f := (mk (R := R)).toIntAlgHom
  let 𝒜 : ℕ → Submodule ℤ (TensorAlgebra ℤ (Additive Rˣ)) :=
    fun n ↦ (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n
  let ψ : ∀ i, 𝒜 i →+ degree R i := fun i ↦
    ((LinearEquiv.ofEq _ _ (degree_eq_map_range_pow R i).symm).toLinearMap.comp
      (f.toLinearMap.submoduleMap (𝒜 i))).toAddMonoidHom
  let φ : (⨁ i, 𝒜 i) →+ (⨁ i, degree R i) := DirectSum.map ψ
  have hψ : ∀ i (a : 𝒜 i), ((ψ i a : degree R i) : MilnorK R) = f a := fun i a ↦ by
    dsimp only [ψ]
    rw [LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_ofEq_apply, LinearMap.submoduleMap_coe_apply, AlgHom.toLinearMap_apply]
  have hφ_coe : ∀ w, DirectSum.coeAddMonoidHom (degree R) (φ w) =
      f (DirectSum.coeAddMonoidHom 𝒜 w) := fun w ↦ by
    induction w using DirectSum.induction_on with
    | zero => simp
    | of i a =>
      dsimp only [φ]
      rw [DirectSum.map_of, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of, hψ]
    | add _ _ hx hy => simp [hx, hy]
  have hφ_apply : ∀ w i, ((φ w i : degree R i) : MilnorK R) =
      f (w i : TensorAlgebra ℤ (Additive Rˣ)) := fun w i ↦ by
    dsimp only [φ]; rw [DirectSum.map_apply, hψ]
  have hφ_surj : Function.Surjective φ :=
    (DirectSum.map_surjective ψ).mpr fun i ↦
      (LinearEquiv.ofEq _ _ (degree_eq_map_range_pow R i).symm).surjective.comp
        (f.toLinearMap.submoduleMap_surjective (𝒜 i))
  constructor
  · intro x y hxy
    obtain ⟨wx, rfl⟩ := hφ_surj x; obtain ⟨wy, rfl⟩ := hφ_surj y
    have hdiff : DirectSum.coeAddMonoidHom 𝒜 (wx - wy) ∈ RingHom.ker f.toRingHom := by
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, map_sub,
        ← hφ_coe, ← hφ_coe, hxy, sub_self]
    ext i
    have hi := isHomogeneous_ker_mk R i hdiff
    rw [show DirectSum.decompose 𝒜 (DirectSum.coeAddMonoidHom 𝒜 (wx - wy)) = wx - wy from
      DirectSum.Decomposition.right_inv (wx - wy)] at hi
    have h0 : f (wx i : TensorAlgebra ℤ (Additive Rˣ)) -
        f (wy i : TensorAlgebra ℤ (Additive Rˣ)) = 0 := by rw [← map_sub]; exact hi
    rw [← hφ_apply, ← hφ_apply, sub_eq_zero] at h0
    exact h0
  · intro z
    obtain ⟨u, rfl⟩ := mk_surjective z
    refine ⟨φ (DirectSum.decompose 𝒜 u), ?_⟩
    rw [hφ_coe]
    exact congrArg f (DirectSum.Decomposition.left_inv u)

/-- `MilnorK R` is a graded `ℤ`-algebra with homogeneous components `MilnorK.degree R`. -/
noncomputable instance gradedAlgebraDegree : GradedAlgebra (degree R) :=
  (isInternal_degree R).gradedAlgebra

variable {R}

/-- `1` lies in `MilnorK.degree R 0`. -/
theorem one_mem_degree_zero : (1 : MilnorK R) ∈ degree R 0 := SetLike.GradedOne.one_mem

/-- Every symbol of length `n` lies in `MilnorK.degree R n`. -/
theorem symbol_mem_degree_of_length {l : List Rˣ} {n : ℕ} (hl : l.length = n) :
    symbol l ∈ degree R n := hl ▸ symbol_mem_degree l

/-- Induction principle for elements of `MilnorK.degree R n` generated by length-`n` symbols. -/
@[elab_as_elim]
theorem degree_inductionOn {n : ℕ} {motive : degree R n → Prop} (x : degree R n)
    (zero : motive 0)
    (symbol : ∀ (l : List Rˣ) (hl : l.length = n),
      motive ⟨symbol l, symbol_mem_degree_of_length hl⟩)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (k : ℤ) (x : degree R n), motive x → motive (k • x)) :
    motive x := by
  rcases x with ⟨v, hv⟩
  refine Submodule.span_induction
    (p := fun y hy ↦ motive ⟨y, (degree_eq_span (R := R) n).symm ▸ hy⟩)
    (fun _ ⟨l, hl, h⟩ ↦ by subst h; exact symbol l hl) zero
    (fun a b _ _ hma hmb ↦ add ⟨a, _⟩ ⟨b, _⟩ hma hmb)
    (fun k a _ hma ↦ smul k ⟨a, _⟩ hma) ((degree_eq_span (R := R) n) ▸ hv)

end Grading

section Universal

variable {R : Type*} [CommRing R]

/-- Two `ℤ`-algebra homomorphisms out of `MilnorK R` agreeing on `ofUnit` are equal. -/
theorem algHom_ext {A : Type*} [Semiring A] [Algebra ℤ A] {f g : MilnorK R →ₐ[ℤ] A}
    (h : ∀ a : Rˣ, f (ofUnit a) = g (ofUnit a)) : f = g := by
  refine AlgHom.toRingHom_injective (ringHom_ext_mk (RingHom.ext fun z ↦ ?_))
  induction z using TensorAlgebra.induction with
  | algebraMap k =>
    exact RingHom.congr_fun
      (RingHom.ext_int ((f.toRingHom.comp mk).comp (algebraMap ℤ _))
        ((g.toRingHom.comp mk).comp (algebraMap ℤ _))) k
  | ι u => simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      mk_ι] using h u.toMul
  | mul _ _ hx hy => simp only [RingHom.comp_apply, map_mul] at *; rw [hx, hy]
  | add _ _ hx hy => simp only [RingHom.comp_apply, map_add] at *; rw [hx, hy]

end Universal

section Functoriality

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The degree-`n` `ℤ`-linear map `MilnorK.degree R n →ₗ[ℤ] MilnorK.degree S n` induced by `f`. -/
def mapDegree (f : R →+* S) (n : ℕ) : degree R n →ₗ[ℤ] degree S n where
  toFun x := ⟨map f x.val, map_mem_degree f x.property⟩
  map_add' x y := Subtype.ext (map_add (map f) x.val y.val)
  map_smul' k x := Subtype.ext (map_zsmul (map f) k x.val)

/-- Underlying value of `mapDegree f n x`. -/
@[simp]
theorem mapDegree_apply (f : R →+* S) (n : ℕ) (x : degree R n) :
    (mapDegree f n x : MilnorK S) = map f x.val := by
  rw [mapDegree, LinearMap.coe_mk, AddHom.coe_mk]

/-- `MilnorK.mapDegree` preserves the identity ring homomorphism. -/
@[simp]
theorem mapDegree_id (n : ℕ) : mapDegree (RingHom.id R) n = LinearMap.id := by
  ext x
  rw [mapDegree_apply, map_id, RingHom.id_apply, LinearMap.id_apply]

/-- `MilnorK.mapDegree` preserves composition of ring homomorphisms. -/
theorem mapDegree_comp (g : S →+* T) (f : R →+* S) (n : ℕ) :
    mapDegree (g.comp f) n = (mapDegree g n).comp (mapDegree f n) := by
  ext x
  rw [LinearMap.comp_apply, mapDegree_apply, mapDegree_apply, mapDegree_apply, map_comp,
    RingHom.comp_apply]

end Functoriality

section FieldIdentities

variable {F : Type*} [Field F]

/-- Over a field, `2 • (ofUnit a * ofUnit a) = 0`. -/
theorem two_nsmul_ofUnit_mul_self (a : Fˣ) : 2 • (ofUnit a * ofUnit a) = 0 :=
  isSteinbergPairing_ofUnit_mul.two_nsmul_map_self a

/-- In characteristic `2`, `ofUnit a * ofUnit a = 0`. -/
theorem ofUnit_mul_self_of_charTwo [CharP F 2] (a : Fˣ) : ofUnit a * ofUnit a = 0 :=
  isSteinbergPairing_ofUnit_mul.map_self_of_charTwo a

/-- A consecutive repeated entry `a, a` may be replaced by `a, -1`. -/
theorem symbol_repeat_adjacent (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: a :: l₂) = symbol (l₁ ++ a :: (-1 : Fˣ) :: l₂) := by
  simp only [symbol_append, symbol_cons, ← mul_assoc (ofUnit a)]
  rw [ofUnit_mul_ofUnit_self a]

/-- A symbol with a consecutive repeated entry is 2-torsion. -/
theorem two_nsmul_symbol_repeat_adjacent (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    2 • symbol (l₁ ++ a :: a :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc (ofUnit a)]
  rw [← mul_smul_comm 2 (symbol l₁), ← smul_mul_assoc 2 (ofUnit a * ofUnit a),
    two_nsmul_ofUnit_mul_self a, zero_mul, mul_zero]

/-- In characteristic `2`, any symbol with a consecutive repeated entry vanishes. -/
theorem symbol_repeat_adjacent_of_charTwo [CharP F 2] (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: a :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc (ofUnit a)]
  rw [ofUnit_mul_self_of_charTwo a, zero_mul, mul_zero]

/-- Moving a degree-one class past a length-`n` symbol multiplies by `(-1) ^ n`. -/
theorem ofUnit_mul_symbol (a : Fˣ) (l : List Fˣ) :
    ofUnit a * symbol l = ((-1 : ℤ) ^ l.length) • (symbol l * ofUnit a) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [symbol_cons, ← mul_assoc, ofUnit_mul_ofUnit_comm a b, neg_mul (ofUnit b * ofUnit a),
      mul_assoc, ih, mul_smul_comm, ← neg_smul, ← neg_one_mul, ← pow_succ', List.length_cons,
      mul_assoc]

/-- Multiplying two symbols commutes up to `(-1) ^ (l₁.length * l₂.length)`. -/
theorem symbol_mul_symbol (l₁ l₂ : List Fˣ) :
    symbol l₁ * symbol l₂ = ((-1 : ℤ) ^ (l₁.length * l₂.length)) • (symbol l₂ * symbol l₁) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [symbol_cons, mul_assoc, ih, mul_smul_comm, ← mul_assoc, ofUnit_mul_symbol]
    simp only [smul_mul_assoc, smul_smul, mul_assoc, List.length_cons, Nat.add_mul, Nat.one_mul,
      pow_add]

/-- Graded commutativity of `MilnorK F`: homogeneous elements `x ∈ degree F m` and `y ∈ degree F n`
satisfy `x * y = (-1) ^ (m * n) • (y * x)`. -/
theorem mul_comm_of_mem_degree {m n : ℕ} {x y : MilnorK F}
    (hx : x ∈ degree F m) (hy : y ∈ degree F n) :
    x * y = ((-1 : ℤ) ^ (m * n)) • (y * x) := by
  rw [degree_eq_span] at hx hy
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hu hv ↦ by rw [add_mul, mul_add, smul_add, hu, hv])
    (fun k u _ hu ↦ by rw [smul_mul_assoc k u, mul_smul_comm k y, hu, smul_comm]) hx
  rintro _ ⟨l₁, rfl, rfl⟩
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hu hv ↦ by rw [mul_add, add_mul, smul_add, hu, hv])
    (fun k u _ hu ↦ by rw [mul_smul_comm k (symbol l₁), smul_mul_assoc k u, hu, smul_comm]) hy
  rintro _ ⟨l₂, rfl, rfl⟩
  exact symbol_mul_symbol l₁ l₂

private theorem symbol_swap_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) (b : Fˣ) (l₃ : List Fˣ) :
    symbol (l₁ ++ a :: l₂ ++ b :: l₃) = -symbol (l₁ ++ b :: l₂ ++ a :: l₃) := by
  have hba : ofUnit b * symbol l₂ * ofUnit a = -(ofUnit a * symbol l₂ * ofUnit b) := by
    rw [ofUnit_mul_symbol, smul_mul_assoc, mul_assoc, ofUnit_mul_ofUnit_comm b a,
      mul_neg (symbol l₂), smul_neg, ← mul_assoc (symbol l₂), ← smul_mul_assoc, ← ofUnit_mul_symbol]
  simp only [symbol_append, symbol_cons, mul_assoc]
  rw [← mul_assoc (ofUnit a), ← mul_assoc (ofUnit a * symbol l₂), ← mul_assoc (ofUnit b),
    ← mul_assoc (ofUnit b * symbol l₂), ← neg_eq_iff_eq_neg.mpr hba,
    neg_mul (ofUnit b * symbol l₂ * ofUnit a), mul_neg (symbol l₁)]

/-- Applying a transposition to the entries of a Milnor symbol negates it. -/
theorem symbol_ofFn_comp_swap {n : ℕ} (a : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j) :
    symbol (List.ofFn (a ∘ Equiv.swap i j)) = -symbol (List.ofFn a) := by
  wlog hlt : i.val < j.val generalizing i j
  · rw [Equiv.swap_comm]
    exact this hij.symm (lt_of_le_of_ne (not_lt.mp hlt) (Fin.val_ne_of_ne hij).symm)
  conv_lhs => rw [List.ofFn_comp_swap_of_lt a hlt]
  conv_rhs => rw [List.ofFn_eq_take_cons_of_lt a hlt]
  exact symbol_swap_middle _ (a j) _ (a i) _

/-- Permuting the entries of a Milnor symbol multiplies it by the sign of the permutation. -/
theorem symbol_ofFn_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → Fˣ) :
    symbol (List.ofFn (a ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • symbol (List.ofFn a) := by
  induction σ using Equiv.Perm.swap_induction_on generalizing a with
  | one => simp
  | swap_mul τ i j hij ih =>
    rw [show a ∘ (Equiv.swap i j * τ) = (a ∘ Equiv.swap i j) ∘ τ from rfl,
      ih (a ∘ Equiv.swap i j), symbol_ofFn_comp_swap a hij, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hij]
    simp only [Units.val_neg, neg_mul, one_mul, neg_zsmul, smul_neg]

/-- Any symbol with a repeated entry (not necessarily adjacent) is 2-torsion. -/
theorem two_nsmul_symbol_ofFn_eq_zero_of_eq {n : ℕ} {a : Fin n → Fˣ} {i j : Fin n}
    (hij : i ≠ j) (ha : a i = a j) :
    2 • symbol (List.ofFn a) = 0 := by
  have hcomp : a ∘ Equiv.swap i j = a := funext fun k ↦ by
    rcases eq_or_ne k i with rfl | hki
    · simp [ha]
    · rcases eq_or_ne k j with rfl | hkj
      · simp [ha]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [two_nsmul, add_eq_zero_iff_eq_neg]
  simpa only [hcomp] using symbol_ofFn_comp_swap a hij

/-- In characteristic `2`, any symbol with a repeated entry vanishes. -/
theorem symbol_ofFn_eq_zero_of_charTwo_of_eq [CharP F 2] {n : ℕ} {a : Fin n → Fˣ} {i j : Fin n}
    (hij : i ≠ j) (ha : a i = a j) :
    symbol (List.ofFn a) = 0 := by
  wlog hlt : i.val < j.val generalizing i j
  · exact this hij.symm ha.symm (lt_of_le_of_ne (not_lt.mp hlt) (Fin.val_ne_of_ne hij).symm)
  rw [List.ofFn_eq_take_cons_of_lt a hlt, ha]
  simp only [symbol_append, symbol_cons, mul_assoc]
  rw [← mul_assoc (ofUnit (a j)), ofUnit_mul_symbol, smul_mul_assoc, mul_assoc (symbol _),
    ← mul_assoc (ofUnit (a j)), ofUnit_mul_self_of_charTwo, zero_mul, mul_zero, smul_zero, mul_zero]

end FieldIdentities

section FiniteField

variable {F : Type*} [Field F]

/-- Over a field with cyclic unit group and positive characteristic, every product of two
degree-one classes vanishes in `MilnorK F`. -/
theorem ofUnit_mul_ofUnit_eq_zero_of_isCyclic_of_ringChar_ne_zero [IsCyclic Fˣ]
    (hchar : ringChar F ≠ 0) (a b : Fˣ) : ofUnit a * ofUnit b = 0 :=
  isSteinbergPairing_ofUnit_mul.eq_zero_of_isCyclic_of_ringChar_ne_zero hchar a b

/-- Over a field with cyclic unit group and positive characteristic, every symbol of length at
least two vanishes. -/
theorem symbol_eq_zero_of_isCyclic_of_ringChar_ne_zero [IsCyclic Fˣ] (hchar : ringChar F ≠ 0)
    {l : List Fˣ} (hl : 2 ≤ l.length) : symbol l = 0 := by
  match l with
  | a :: b :: rest =>
    rw [symbol_cons, symbol_cons, ← mul_assoc,
      ofUnit_mul_ofUnit_eq_zero_of_isCyclic_of_ringChar_ne_zero hchar a b, zero_mul]

/-- Over a field with cyclic unit group and positive characteristic, `MilnorK.degree F n` vanishes
for every `n ≥ 2`. -/
theorem subsingleton_degree_of_isCyclic_of_ringChar_ne_zero [IsCyclic Fˣ] (hchar : ringChar F ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) : Subsingleton (degree F n) := by
  refine subsingleton_iff_forall_eq 0 |>.mpr fun x ↦ ?_
  induction x using degree_inductionOn with
  | zero => rfl
  | symbol l hl =>
    exact Subtype.ext (symbol_eq_zero_of_isCyclic_of_ringChar_ne_zero hchar (hl.symm ▸ hn))
  | add x y hx hy => rw [hx, hy, add_zero]
  | smul k x hx => rw [hx, smul_zero]

/-- Milnor K-groups of finite fields vanish in every degree at least two. -/
theorem subsingleton_degree_of_finite (F : Type*) [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (degree F n) :=
  subsingleton_degree_of_isCyclic_of_ringChar_ne_zero (CharP.ringChar_ne_zero_of_finite F) n hn

end FiniteField

end MilnorK

end TauCeti
