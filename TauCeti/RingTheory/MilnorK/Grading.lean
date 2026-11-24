/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.LinearAlgebra.TensorAlgebra.ToTensorPower
public import TauCeti.RingTheory.MilnorK.Basic
public import TauCeti.RingTheory.MilnorK.MatsumotoGroup
import TauCeti.Data.List.OfFn
import TauCeti.LinearAlgebra.TensorSquare
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous

/-!
# Grading, kernel bridge, and degree-two identification of Milnor K-theory

This file complements `TauCeti.RingTheory.MilnorK.Basic` by characterizing the Steinberg kernel
degree by degree via `TauCeti.MilnorK.relationSubmodule`, equipping `TauCeti.MilnorK R` with an
internal `ℕ`-grading (`TauCeti.MilnorK.isInternal_degree`, `TauCeti.MilnorK.gradedAlgebraDegree`),
bridging `MilnorK.degree R n` with the homogeneous tensor-power quotients
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ MilnorK.relationSubmodule R n` naturally in `R`, and deriving the
canonical degree-2 identification with `TauCeti.MatsumotoGroup R`.

## Main definitions

* `TauCeti.MilnorK.relationSubmodule`: the degree-`n` Steinberg relation submodule of
  `(⨂[ℤ]^n) (Additive Rˣ)`.
* `TauCeti.MilnorK.toDegree`: the canonical surjection `(⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] degree R n`.
* `TauCeti.MilnorK.degreeEquivQuotient`: the canonical linear equivalence
  `degree R n ≃ₗ[ℤ] ((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n`.
* `TauCeti.MilnorK.mapQuotient`: functorial map on degree-`n` tensor-power quotients.
* `TauCeti.MilnorK.degreeTwoEquivMatsumotoGroup`: the canonical equivalence
  `degree R 2 ≃ₗ[ℤ] MatsumotoGroup R`.

## Main results

* `TauCeti.MilnorK.ker_mk_eq_span`: the kernel of `MilnorK.mk` as a `TwoSidedIdeal.span`.
* `TauCeti.MilnorK.mem_ker_mk_iff` and `TauCeti.MilnorK.toTensorAlgebra_mem_ker_iff`:
  characterization of the Steinberg kernel degree by degree.
* `TauCeti.MilnorK.isInternal_degree`: `MilnorK R` is internally `ℕ`-graded by `MilnorK.degree R`.
* `TauCeti.MilnorK.degreeEquivQuotient_mapDegree`: naturality of the degree-`n` quotient bridge
  under ring homomorphisms.
* `TauCeti.MilnorK.degreeTwoEquivMatsumotoGroup_mapDegree`: naturality of the degree-2
  identification with `MatsumotoGroup`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §III.7.1, §III.6.1.
* H. Matsumoto, *Sur les sous-groupes arithmétiques des groupes semi-simples déployés*, Section 9.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

namespace MilnorK

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
  refine (Submodule.map_span_le f _ _).mpr ?_
    (Submodule.mem_map_of_mem (relationSubmodule_def R m ▸ ha))
  rintro _ ⟨x, i, hi, hxy, rfl⟩
  exact hf x i hi hxy

/-- Graded multiplication on the right preserves `relationSubmodule`. -/
theorem gMul_mem_relationSubmodule_right {m n : ℕ}
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
theorem gMul_mem_relationSubmodule_left {m n : ℕ}
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
  refine LinearMap.mem_ker.mp ((Submodule.span_le (p := LinearMap.ker
    ((mk (R := R)).toIntAlgHom.toLinearMap.comp TensorPower.toTensorAlgebra)).mpr ?_) ht)
  rintro _ ⟨x, i, hi, hab, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    RingHom.toIntAlgHom_apply, mk_toTensorAlgebra_tprod]
  have hsplit := List.ofFn_eq_take_cons_of_lt (fun j ↦ Additive.toMul (x j))
    (i := ⟨i, by omega⟩) (j := ⟨i + 1, hi⟩) (by simp)
  simp only [Nat.add_sub_cancel_left, Nat.sub_self, List.take_zero, List.append_assoc,
    List.cons_append, List.nil_append] at hsplit
  rw [hsplit]
  exact symbol_append_cons_cons_of_add_eq_one _ _ hab

private theorem of_apply_mem_relationSubmodule {i n : ℕ} {x : (⨂[ℤ]^i) (Additive Rˣ)}
    (hx : x ∈ relationSubmodule R i) :
    DirectSum.of (fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) i x n ∈ relationSubmodule R n := by
  by_cases h : i = n
  · subst h; simpa [DirectSum.of_eq_same] using hx
  · rw [DirectSum.of_eq_of_ne i n _ (Ne.symm h)]; exact Submodule.zero_mem _

private theorem directSum_mul_mem_relationSubmodule
    {u v : ⨁ k : ℕ, (⨂[ℤ]^k) (Additive Rˣ)}
    (h : (∀ k, u k ∈ relationSubmodule R k) ∨ (∀ k, v k ∈ relationSubmodule R k)) (n : ℕ) :
    (u * v) n ∈ relationSubmodule R n := by
  classical
  rw [DirectSum.mul_eq_sum_support_ghas_mul, DirectSum.sum_apply]
  refine Submodule.sum_mem _ fun ij _ ↦ of_apply_mem_relationSubmodule R ?_
  exact h.elim (fun hu ↦ gMul_mem_relationSubmodule_right (hu ij.1))
    (fun hv ↦ gMul_mem_relationSubmodule_left (hv ij.2))

private theorem ringCon_eq_span_ringCon :
    MilnorK.ringCon R =
      (TwoSidedIdeal.span
        {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
          z = TensorAlgebra.ι ℤ (Additive.ofMul a) *
            TensorAlgebra.ι ℤ (Additive.ofMul b)}).ringCon := by
  refine le_antisymm ?_ ?_
  · rw [MilnorK.ringCon_eq, RingCon.ringConGen_le]
    rintro _ _ h
    rcases (milnorRel_iff R).mp h with ⟨a, b, hab, rfl, rfl⟩
    rw [TwoSidedIdeal.rel_iff, sub_zero]
    exact TwoSidedIdeal.subset_span ⟨a, b, hab, rfl⟩
  · refine (TwoSidedIdeal.ringCon_le_iff
      (J := TwoSidedIdeal.ofRingCon (MilnorK.ringCon R))).mp (TwoSidedIdeal.span_le.mpr ?_)
    rintro _ ⟨a, b, hab, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_ofRingCon, MilnorK.ringCon_eq]
    exact RingConGen.Rel.of _ _ ((milnorRel_iff R).mpr ⟨a, b, hab, rfl, rfl⟩)

/-- The kernel of `MilnorK.mk` is the two-sided ideal of `TensorAlgebra ℤ (Additive Rˣ)` generated
by the Steinberg products `ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)` with
`(a : R) + b = 1`. -/
theorem ker_mk_eq_span :
    RingHom.ker (mk (R := R)) =
      (TwoSidedIdeal.span
        {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
          z = TensorAlgebra.ι ℤ (Additive.ofMul a) *
            TensorAlgebra.ι ℤ (Additive.ofMul b)}).asIdeal := by
  ext z
  rw [RingHom.mem_ker, ← map_zero (mk (R := R)), mk_eq_mk_iff, ← MilnorK.ringCon_eq,
    ringCon_eq_span_ringCon, TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_iff]

/-- The two-sided ideal of tensors whose homogeneous components all lie in `relationSubmodule`. -/
private def relationTwoSidedIdeal : TwoSidedIdeal (TensorAlgebra ℤ (Additive Rˣ)) :=
  TwoSidedIdeal.mk'
    {w | ∀ n, TensorAlgebra.toDirectSum w n ∈ relationSubmodule R n}
    (fun _ ↦ by simp)
    (fun hx hy n ↦ by
      rw [map_add, DirectSum.add_apply]
      exact Submodule.add_mem _ (hx n) (hy n))
    (fun {x} hx n ↦ by
      rw [show -x = (-1 : ℤ) • x by abel, map_smul, DirectSum.smul_apply]
      exact Submodule.smul_mem _ _ (hx n))
    (fun hy n ↦ by rw [map_mul]; exact directSum_mul_mem_relationSubmodule R (.inr hy) n)
    (fun hx n ↦ by rw [map_mul]; exact directSum_mul_mem_relationSubmodule R (.inl hx) n)

private theorem steinbergGenerators_subset_relationTwoSidedIdeal :
    {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
      z = TensorAlgebra.ι ℤ (Additive.ofMul a) * TensorAlgebra.ι ℤ (Additive.ofMul b)} ⊆
      (relationTwoSidedIdeal R : Set (TensorAlgebra ℤ (Additive Rˣ))) := by
  rintro _ ⟨a, b, hab, rfl⟩
  rw [SetLike.mem_coe, relationTwoSidedIdeal, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq]
  intro n
  rw [map_mul, TensorAlgebra.toDirectSum_ι, TensorAlgebra.toDirectSum_ι,
    DirectSum.of_mul_of, TensorPower.tprod_mul_tprod]
  refine of_apply_mem_relationSubmodule R (tprod_mem_relationSubmodule _ (i := 0) (by omega) ?_)
  have h0 : (⟨0, by omega⟩ : Fin (1 + 1)) = Fin.castAdd 1 0 := Fin.ext (by simp)
  have h1 : (⟨1, by omega⟩ : Fin (1 + 1)) = Fin.natAdd 1 0 := Fin.ext (by simp)
  rw [h0, Fin.append_left, h1, Fin.append_right]
  simpa using hab

/-- An element of `TensorAlgebra ℤ (Additive Rˣ)` lies in the kernel of `MilnorK.mk` if and only
if each of its homogeneous tensor-power components lies in `relationSubmodule R n`. -/
theorem mem_ker_mk_iff (z : TensorAlgebra ℤ (Additive Rˣ)) :
    z ∈ RingHom.ker (mk (R := R)) ↔
      ∀ n : ℕ, TensorAlgebra.toDirectSum z n ∈ relationSubmodule R n := by
  constructor
  · -- Forward: `ker mk` is spanned by Steinberg generators, which lie in `relationTwoSidedIdeal`.
    intro hz
    rw [ker_mk_eq_span, TwoSidedIdeal.mem_asIdeal] at hz
    have hle : TwoSidedIdeal.span
        {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
          z = TensorAlgebra.ι ℤ (Additive.ofMul a) * TensorAlgebra.ι ℤ (Additive.ofMul b)} ≤
        relationTwoSidedIdeal R :=
      TwoSidedIdeal.span_le.mpr (steinbergGenerators_subset_relationTwoSidedIdeal R)
    exact (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp (hle hz)
  · -- Backward: decompose `z` into homogeneous components, each killed by `mk`.
    intro hz
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
  exact ⟨fun h ↦ by simpa [DirectSum.of_eq_same] using h n,
    fun ht k ↦ of_apply_mem_relationSubmodule R ht⟩

end KernelBridge

section Grading

variable (R : Type*) [CommRing R]

private abbrev tensorAlgDegree (n : ℕ) : Submodule ℤ (TensorAlgebra ℤ (Additive Rˣ)) :=
  (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n

/-- The kernel of `MilnorK.mk` is a homogeneous ideal of `TensorAlgebra ℤ (Additive Rˣ)`. -/
theorem isHomogeneous_ker_mk :
    (RingHom.ker (mk (R := R))).IsHomogeneous
      (fun n : ℕ ↦
        (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n) := by
  rw [ker_mk_eq_span]
  refine TwoSidedIdeal.homogeneous_span
    (fun n : ℕ ↦
      (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n) ?_
  rintro _ ⟨a, b, _, rfl⟩
  refine ⟨2, ?_⟩
  dsimp only
  rw [pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

/-- `MilnorK R` is internally `ℕ`-graded by `MilnorK.degree R`. -/
theorem isInternal_degree : DirectSum.IsInternal (degree R) := by
  classical
  have hker : (RingHom.ker (mk (R := R)).toIntAlgHom).IsHomogeneous (tensorAlgDegree R) := by
    have heq : RingHom.ker (mk (R := R)).toIntAlgHom = RingHom.ker (mk (R := R)) := by
      ext; simp [RingHom.toIntAlgHom_apply]
    simpa only [heq] using isHomogeneous_ker_mk R
  have hint := TauCeti.GradedAlgebra.isInternal_map (tensorAlgDegree R)
    (mk (R := R)).toIntAlgHom mk_surjective hker
  rwa [show (fun i ↦ (tensorAlgDegree R i).map (mk (R := R)).toIntAlgHom.toLinearMap) =
      degree R from funext fun i ↦ (degree_eq_map_range_pow (R := R) i).symm] at hint

/-- `MilnorK R` is a graded `ℤ`-algebra with homogeneous components `MilnorK.degree R`. -/
noncomputable instance gradedAlgebraDegree : GradedAlgebra (degree R) :=
  (isInternal_degree R).gradedAlgebra

end Grading

section DegreeQuotient

variable (R : Type*) [CommRing R]

/-- The canonical `ℤ`-linear surjection `(⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] MilnorK.degree R n`. -/
noncomputable def toDegree (n : ℕ) : (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] degree R n :=
  LinearMap.codRestrict (degree R n)
    ((mk (R := R)).toIntAlgHom.toLinearMap ∘ₗ TensorPower.toTensorAlgebra)
    fun t ↦ mem_degree_iff.mpr ⟨_, TensorPower.toTensorAlgebra_mem_range_pow t, rfl⟩

/-- Underlying element of `toDegree R n t` in `MilnorK R`. -/
@[simp]
theorem coe_toDegree (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    (toDegree R n t : MilnorK R) = mk (TensorPower.toTensorAlgebra t) := by
  rw [toDegree, LinearMap.codRestrict_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    RingHom.toIntAlgHom_apply]

/-- `toDegree R n` maps a pure tensor `tprod ℤ x` to the corresponding Milnor symbol. -/
theorem toDegree_tprod {n : ℕ} (x : Fin n → Additive Rˣ) :
    (toDegree R n (PiTensorProduct.tprod ℤ x) : MilnorK R) =
      symbol (List.ofFn fun i ↦ Additive.toMul (x i)) := by
  rw [coe_toDegree, mk_toTensorAlgebra_tprod]

/-- `toDegree` intertwines graded tensor multiplication with multiplication in `MilnorK R`. -/
theorem toDegree_gMul {m n : ℕ} (a : (⨂[ℤ]^m) (Additive Rˣ)) (b : (⨂[ℤ]^n) (Additive Rˣ)) :
    (toDegree R (m + n)
      (GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) a b) : MilnorK R) =
      (toDegree R m a : MilnorK R) * (toDegree R n b : MilnorK R) := by
  rw [coe_toDegree, coe_toDegree, coe_toDegree, TensorPower.toTensorAlgebra_gMul, map_mul]

/-- The kernel of `toDegree R n` is precisely `relationSubmodule R n`. -/
theorem ker_toDegree (n : ℕ) : LinearMap.ker (toDegree R n) = relationSubmodule R n := by
  ext t
  rw [LinearMap.mem_ker, Subtype.ext_iff, coe_toDegree]
  exact toTensorAlgebra_mem_ker_iff R t

/-- `toDegree R n` is surjective onto `MilnorK.degree R n`. -/
theorem surjective_toDegree (n : ℕ) : Function.Surjective (toDegree R n) := fun x ↦ by
  induction x using degree_induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | symbol l hl =>
    refine ⟨PiTensorProduct.tprod ℤ fun i ↦ Additive.ofMul (l.get (i.cast hl.symm)),
      Subtype.ext ?_⟩
    rw [toDegree_tprod]; congr 1
    exact List.ext_get (by simp [hl]) fun _ _ _ ↦ by simp
  | add _ _ hx hy => obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, map_add _ a b⟩
  | smul k _ hx => obtain ⟨a, rfl⟩ := hx; exact ⟨k • a, map_smul _ k a⟩

/-- The canonical `ℤ`-linear equivalence between `MilnorK.degree R n` and the degree-`n`
tensor-power quotient `((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n`. -/
noncomputable def degreeEquivQuotient (n : ℕ) :
    degree R n ≃ₗ[ℤ] ((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n :=
  ((Submodule.quotEquivOfEq (LinearMap.ker (toDegree R n)) (relationSubmodule R n)
      (ker_toDegree R n)).symm.trans
    (LinearMap.quotKerEquivOfSurjective (toDegree R n) (surjective_toDegree R n))).symm

/-- `(degreeEquivQuotient R n).symm` sends a quotient class `mk t` to `toDegree R n t`. -/
@[simp]
theorem degreeEquivQuotient_symm_mk (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    (degreeEquivQuotient R n).symm (Submodule.Quotient.mk t) = toDegree R n t := by
  rw [degreeEquivQuotient, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    (LinearEquiv.symm_apply_eq _).mpr (Submodule.quotEquivOfEq_mk _ _ (ker_toDegree R n) t).symm,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- `degreeEquivQuotient R n` sends `toDegree R n t` to the quotient class of `t`. -/
@[simp]
theorem degreeEquivQuotient_toDegree (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    degreeEquivQuotient R n (toDegree R n t) = Submodule.Quotient.mk t := by
  rw [← degreeEquivQuotient_symm_mk, LinearEquiv.apply_symm_apply]

/-- `degreeEquivQuotient R n` sends a symbol `{a₀, …, aₙ₋₁}` to the quotient class of the
corresponding pure tensor. -/
theorem degreeEquivQuotient_symbol_ofFn {n : ℕ} (a : Fin n → Rˣ) :
    degreeEquivQuotient R n
      ⟨symbol (List.ofFn a), symbol_mem_degree_of_length (List.length_ofFn (f := a))⟩ =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ (fun i ↦ Additive.ofMul (a i))) := by
  have h : (⟨symbol (List.ofFn a), symbol_mem_degree_of_length (List.length_ofFn (f := a))⟩ :
      degree R n) = toDegree R n (PiTensorProduct.tprod ℤ (fun i ↦ Additive.ofMul (a i))) :=
    Subtype.ext (by rw [toDegree_tprod]; simp)
  rw [h, degreeEquivQuotient_toDegree]

end DegreeQuotient

section QuotientFunctoriality

variable {R S : Type*} [CommRing R] [CommRing S]

private noncomputable def mapTensorPower (f : R →+* S) (n : ℕ) :
    (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] (⨂[ℤ]^n) (Additive Sˣ) :=
  PiTensorProduct.map fun _ ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap

private theorem mapTensorPower_mem_relationSubmodule (f : R →+* S) (n : ℕ)
    {t : (⨂[ℤ]^n) (Additive Rˣ)} (ht : t ∈ relationSubmodule R n) :
    mapTensorPower f n t ∈ relationSubmodule S n := by
  refine map_mem_relationSubmodule (mapTensorPower f n) (fun x i hi hab ↦ ?_) ht
  rw [mapTensorPower, PiTensorProduct.map_tprod]
  refine tprod_mem_relationSubmodule _ (i := i) hi ?_
  simpa [Units.map] using (map_add f _ _).symm.trans ((congrArg f hab).trans (map_one f))

/-- The `ℤ`-linear map on degree-`n` tensor-power quotients induced by a ring homomorphism `f`. -/
noncomputable def mapQuotient (f : R →+* S) (n : ℕ) :
    (((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n) →ₗ[ℤ]
      (((⨂[ℤ]^n) (Additive Sˣ)) ⧸ relationSubmodule S n) :=
  Submodule.mapQ (relationSubmodule R n) (relationSubmodule S n) (mapTensorPower f n)
    fun _ ht ↦ mapTensorPower_mem_relationSubmodule f n ht

/-- `mapQuotient f n` acts on quotient classes via `PiTensorProduct.map`. -/
theorem mapQuotient_mk (f : R →+* S) (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    mapQuotient f n (Submodule.Quotient.mk t) = Submodule.Quotient.mk
      (PiTensorProduct.map (fun _ ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap) t) := by
  rw [mapQuotient, Submodule.mapQ_apply, mapTensorPower]

/-- `mapQuotient f n` maps a pure tensor `tprod ℤ x` to the pure tensor obtained by applying
`Units.map f.toMonoidHom` entrywise. -/
@[simp]
theorem mapQuotient_mk_tprod (f : R →+* S) {n : ℕ} (x : Fin n → Additive Rˣ) :
    mapQuotient f n (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ x)) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ fun i ↦
        Additive.ofMul (Units.map f.toMonoidHom (Additive.toMul (x i)))) := by
  rw [mapQuotient_mk, PiTensorProduct.map_tprod]
  simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive, Function.comp_apply]

/-- `MilnorK.mapQuotient` preserves the identity ring homomorphism. -/
@[simp]
theorem mapQuotient_id (n : ℕ) : mapQuotient (RingHom.id R) n = LinearMap.id := by
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [Submodule.Quotient.mk_smul, map_smul, mapQuotient_mk_tprod,
      RingHom.toMonoidHom_eq_coe, LinearMap.id_apply]
    congr 2
  | add _ _ hx hy =>
    simp only [Submodule.Quotient.mk_add, map_add] at hx hy ⊢
    rw [hx, hy]

/-- `MilnorK.mapQuotient` preserves composition of ring homomorphisms. -/
theorem mapQuotient_comp {T : Type*} [CommRing T] (g : S →+* T) (f : R →+* S) (n : ℕ) :
    mapQuotient (g.comp f) n = (mapQuotient g n).comp (mapQuotient f n) := by
  refine LinearMap.ext fun q ↦ ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [Submodule.Quotient.mk_smul, map_smul, LinearMap.comp_apply, mapQuotient_mk_tprod,
      toMul_ofMul, RingHom.toMonoidHom_eq_coe]
    congr 2
  | add _ _ hx hy =>
    simp only [Submodule.Quotient.mk_add, map_add] at hx hy ⊢
    rw [hx, hy]

/-- The quotient bridge `degreeEquivQuotient` is natural with respect to ring homomorphisms. -/
theorem degreeEquivQuotient_mapDegree (f : R →+* S) (n : ℕ) (x : degree R n) :
    degreeEquivQuotient S n (mapDegree f n x) = mapQuotient f n (degreeEquivQuotient R n x) := by
  obtain ⟨t, rfl⟩ := surjective_toDegree R n x
  rw [degreeEquivQuotient_toDegree]
  have hcomm : mapDegree f n (toDegree R n t) = toDegree S n (mapTensorPower f n t) := by
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r y =>
      rw [map_smul, map_smul, map_smul, map_smul]; congr 1
      apply Subtype.ext
      rw [mapDegree_apply, toDegree_tprod, map_symbol, mapTensorPower,
        PiTensorProduct.map_tprod, toDegree_tprod]
      congr 1
      simp only [List.map_ofFn, Function.comp_def, AddMonoidHom.coe_toIntLinearMap,
        MonoidHom.coe_toAdditive, toMul_ofMul, RingHom.toMonoidHom_eq_coe]
    | add _ _ hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  rw [hcomm, degreeEquivQuotient_toDegree, mapTensorPower, ← mapQuotient_mk]

end QuotientFunctoriality

section DegreeTwo

variable (R : Type*) [CommRing R]

@[simp]
private theorem tensorProductEquivTensorSquare_symm_int_tprod (x : Fin 2 → Additive Rˣ) :
    ((tensorProductEquivTensorSquare ℤ (Additive Rˣ)).symm.toAddEquiv.toIntLinearEquiv :
        (⨂[ℤ]^2 (Additive Rˣ)) ≃ₗ[ℤ] Additive Rˣ ⊗[ℤ] Additive Rˣ)
      (PiTensorProduct.tprod ℤ x) = x 0 ⊗ₜ[ℤ] x 1 := by
  simp [tensorProductEquivTensorSquare_symm_tprod]

private theorem map_relationSubmodule_two :
    (relationSubmodule R 2).map
        ((tensorProductEquivTensorSquare ℤ
          (Additive Rˣ)).symm.toAddEquiv.toIntLinearEquiv.toLinearMap) =
      MatsumotoGroup.steinbergRelations R := by
  refine le_antisymm ?_ ?_
  · rw [relationSubmodule_def, Submodule.map_span_le]
    rintro _ ⟨x, i, hi, hab, rfl⟩
    obtain rfl : i = 0 := by omega
    rw [LinearEquiv.coe_coe, tensorProductEquivTensorSquare_symm_int_tprod,
      MatsumotoGroup.steinbergRelations_def]
    exact Submodule.subset_span ⟨Additive.toMul (x 0), Additive.toMul (x 1), hab, by simp⟩
  · rw [MatsumotoGroup.steinbergRelations_def, Submodule.span_le]
    rintro _ ⟨a, b, hab, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_map]
    refine ⟨PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b],
      tprod_mem_relationSubmodule _ (i := 0) (by omega) (by simpa using hab), ?_⟩
    rw [LinearEquiv.coe_coe, tensorProductEquivTensorSquare_symm_int_tprod]
    simp

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 2 ≃ₗ[ℤ] MatsumotoGroup R`, taking
`MilnorK.symbol [a, b]` to `MatsumotoGroup.symbol a b`. -/
noncomputable def degreeTwoEquivMatsumotoGroup : degree R 2 ≃ₗ[ℤ] MatsumotoGroup R :=
  (degreeEquivQuotient R 2).trans
    (Submodule.Quotient.equiv (relationSubmodule R 2) (MatsumotoGroup.steinbergRelations R)
      (tensorProductEquivTensorSquare ℤ (Additive Rˣ)).symm.toAddEquiv.toIntLinearEquiv
      (map_relationSubmodule_two R))

/-- `degreeTwoEquivMatsumotoGroup R` sends the image of a pure tensor `tprod ℤ x` in degree `2`
to `MatsumotoGroup.symbol (toMul (x 0)) (toMul (x 1))`. -/
@[simp]
theorem degreeTwoEquivMatsumotoGroup_toDegree_tprod (x : Fin 2 → Additive Rˣ) :
    degreeTwoEquivMatsumotoGroup R (toDegree R 2 (PiTensorProduct.tprod ℤ x)) =
      MatsumotoGroup.symbol (Additive.toMul (x 0)) (Additive.toMul (x 1)) := by
  rw [degreeTwoEquivMatsumotoGroup, LinearEquiv.trans_apply, degreeEquivQuotient_toDegree,
    Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe,
    tensorProductEquivTensorSquare_symm_int_tprod]
  simpa using MatsumotoGroup.mk_tmul (Additive.toMul (x 0)) (Additive.toMul (x 1))

/-- `degreeTwoEquivMatsumotoGroup R` sends the two-entry Milnor symbol `{a, b}` to
`MatsumotoGroup.symbol a b`. -/
theorem degreeTwoEquivMatsumotoGroup_symbol_pair (a b : Rˣ) :
    degreeTwoEquivMatsumotoGroup R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
      MatsumotoGroup.symbol a b := by
  have hsub : (⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ : degree R 2) =
      toDegree R 2 (PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b]) :=
    Subtype.ext (by rw [toDegree_tprod]; simp)
  rw [hsub]
  simp

/-- `degreeTwoEquivMatsumotoGroup R` sends `ofUnit a * ofUnit b` to
`MatsumotoGroup.symbol a b`. -/
@[simp]
theorem degreeTwoEquivMatsumotoGroup_ofUnit_mul (a b : Rˣ) :
    degreeTwoEquivMatsumotoGroup R
      ⟨ofUnit a * ofUnit b,
        SetLike.GradedMul.mul_mem (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ =
      MatsumotoGroup.symbol a b := by
  simpa [Subtype.ext_iff, symbol_pair] using degreeTwoEquivMatsumotoGroup_symbol_pair R a b

/-- `(degreeTwoEquivMatsumotoGroup R).symm` sends `MatsumotoGroup.symbol a b` to the two-entry
Milnor symbol `{a, b}`. -/
@[simp]
theorem degreeTwoEquivMatsumotoGroup_symm_symbol (a b : Rˣ) :
    (degreeTwoEquivMatsumotoGroup R).symm (MatsumotoGroup.symbol a b) =
      ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ := by
  rw [LinearEquiv.symm_apply_eq, degreeTwoEquivMatsumotoGroup_symbol_pair]

/-- The degree-two identification `degree R 2 ≃ₗ[ℤ] MatsumotoGroup R` is natural with respect to
ring homomorphisms. -/
theorem degreeTwoEquivMatsumotoGroup_mapDegree {S : Type*} [CommRing S] (f : R →+* S)
    (x : degree R 2) :
    degreeTwoEquivMatsumotoGroup S (mapDegree f 2 x) =
      MatsumotoGroup.map f (degreeTwoEquivMatsumotoGroup R x) := by
  obtain ⟨t, rfl⟩ := surjective_toDegree R 2 x
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    have hmap : mapDegree f 2 (toDegree R 2 (PiTensorProduct.tprod ℤ y)) =
        toDegree S 2 (PiTensorProduct.tprod ℤ fun i ↦
          Additive.ofMul (Units.map f.toMonoidHom (Additive.toMul (y i)))) := by
      rw [← degreeEquivQuotient_symm_mk S 2, ← mapQuotient_mk_tprod, ← degreeEquivQuotient_toDegree,
        ← degreeEquivQuotient_mapDegree, LinearEquiv.symm_apply_apply]
    simp [map_smul, hmap]
  | add _ _ hu hv => simp [map_add, hu, hv]

end DegreeTwo

end MilnorK

end TauCeti
