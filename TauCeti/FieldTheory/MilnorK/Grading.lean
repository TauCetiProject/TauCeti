/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import TauCeti.FieldTheory.MilnorK.Basic
public import TauCeti.FieldTheory.MilnorK.SymbolGroup

/-!
# Homogeneous quotient bridge and low-degree identifications of Milnor K-theory

This file bridges the ungraded Steinberg ring quotient `MilnorK R` with the homogeneous quotients
`(⨂[ℤ]^n (Additive Rˣ)) ⧸ MilnorK.relationSubmodule R n` of Mathlib's `TensorPower`. It proves
that the Steinberg kernel intersects degree `n` in `relationSubmodule R n`, identifies
`MilnorK.degree R n` with the corresponding tensor-power quotient naturally in `R`, and derives the
canonical degree-0, degree-1, and degree-2 identifications with `ℤ`, `Additive Rˣ`, and
`SymbolGroup R`.

## Main definitions

* `TauCeti.MilnorK.relationSubmodule`: the degree-`n` Steinberg relation submodule of
  `(⨂[ℤ]^n) (Additive Rˣ)`.
* `TauCeti.MilnorK.toDegree`: the canonical surjection `(⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] degree R n`.
* `TauCeti.MilnorK.degreeEquivQuotient`: the canonical linear equivalence
  `degree R n ≃ₗ[ℤ] ((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n`.
* `TauCeti.MilnorK.directSumDegreeEquiv`: the graded algebra equivalence
  `(⨁ n : ℕ, degree R n) ≃ₐ[ℤ] MilnorK R`.
* `TauCeti.MilnorK.degreeZeroEquiv`: the canonical equivalence `degree R 0 ≃ₗ[ℤ] ℤ`.
* `TauCeti.MilnorK.degreeOneEquiv`: the canonical equivalence `degree R 1 ≃ₗ[ℤ] Additive Rˣ`.
* `TauCeti.MilnorK.degreeTwoEquivSymbolGroup`: the canonical equivalence
  `degree R 2 ≃ₗ[ℤ] SymbolGroup R`.

## Main results

* `TauCeti.MilnorK.gMul_mem_relationSubmodule_left` and
  `TauCeti.MilnorK.gMul_mem_relationSubmodule_right`: graded two-sided ideal stability of
  `relationSubmodule`.
* `TauCeti.MilnorK.mem_ker_mkRingHom_iff` and `TauCeti.MilnorK.toTensorAlgebra_mem_ker_iff`:
  characterization of the Steinberg kernel degree by degree.
* `TauCeti.MilnorK.degreeEquivQuotient_mapDegree`: naturality of the degree-`n` quotient bridge
  under ring homomorphisms.
* `TauCeti.MilnorK.intCast_injective`, `TauCeti.MilnorK.one_ne_zero`, and
  `TauCeti.MilnorK.ofUnit_injective`: injectivity of the degree-0 and degree-1 embeddings.
* `TauCeti.MilnorK.degreeTwoEquivSymbolGroup_mapDegree`: naturality of the degree-2 identification
  with `SymbolGroup`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Definition III.7.1 and
  Section III.6.1.
* H. Matsumoto, *Sur les sous-groupes arithmétiques des groupes semi-simples déployés*, Section 9.
-/

public section

namespace TauCeti

open scoped DirectSum TensorProduct

universe u

namespace MilnorK

section RelationSubmodule

variable (R : Type u) [CommSemiring R]

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

/-- Graded multiplication on the right preserves `relationSubmodule`. -/
theorem gMul_mem_relationSubmodule_left {m n : ℕ}
    {a : (⨂[ℤ]^m) (Additive Rˣ)} {b : (⨂[ℤ]^n) (Additive Rˣ)}
    (ha : a ∈ relationSubmodule R m) :
    GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) a b ∈
      relationSubmodule R (m + n) := by
  let gMulLin : (⨂[ℤ]^m) (Additive Rˣ) →ₗ[ℤ] (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ]
      (⨂[ℤ]^(m + n)) (Additive Rˣ) :=
    (TensorProduct.mk ℤ _ _).compr₂ (TensorPower.mulEquiv (n := m) (m := n)).toLinearMap
  change gMulLin a b ∈ relationSubmodule R (m + n)
  induction b using PiTensorProduct.induction_on with
  | smul_tprod r y =>
    rw [map_smul]; refine Submodule.smul_mem _ r ?_
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ hu hv ↦ by rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hu hv)
      (fun k _ _ hu ↦ by rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ k hu) ha
    rintro _ ⟨x, i, hi, hxy, rfl⟩
    change GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ))
      (PiTensorProduct.tprod ℤ x) (PiTensorProduct.tprod ℤ y) ∈ _
    rw [TensorPower.tprod_mul_tprod]
    refine tprod_mem_relationSubmodule (Fin.append x y) (i := i) (by omega) ?_
    rw [show Fin.append x y ⟨i, by omega⟩ = x ⟨i, by omega⟩ from Fin.append_left x y ⟨i, by omega⟩,
      show Fin.append x y ⟨i + 1, by omega⟩ = x ⟨i + 1, hi⟩ from Fin.append_left x y ⟨i + 1, hi⟩]
    exact hxy
  | add _ _ hy₁ hy₂ => rw [map_add]; exact Submodule.add_mem _ hy₁ hy₂

/-- Graded multiplication on the left preserves `relationSubmodule`. -/
theorem gMul_mem_relationSubmodule_right {m n : ℕ}
    {a : (⨂[ℤ]^m) (Additive Rˣ)} {b : (⨂[ℤ]^n) (Additive Rˣ)}
    (hb : b ∈ relationSubmodule R n) :
    GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) a b ∈
      relationSubmodule R (m + n) := by
  let gMulLin : (⨂[ℤ]^m) (Additive Rˣ) →ₗ[ℤ] (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ]
      (⨂[ℤ]^(m + n)) (Additive Rˣ) :=
    (TensorProduct.mk ℤ _ _).compr₂ (TensorPower.mulEquiv (n := m) (m := n)).toLinearMap
  change gMulLin a b ∈ relationSubmodule R (m + n)
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, LinearMap.smul_apply]; refine Submodule.smul_mem _ r ?_
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ hu hv ↦ by rw [map_add]; exact Submodule.add_mem _ hu hv)
      (fun k _ _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ k hu) hb
    rintro _ ⟨y, i, hi, hxy, rfl⟩
    change GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ))
      (PiTensorProduct.tprod ℤ x) (PiTensorProduct.tprod ℤ y) ∈ _
    rw [TensorPower.tprod_mul_tprod]
    refine tprod_mem_relationSubmodule (Fin.append x y) (i := m + i) (by omega) ?_
    have h1 : Fin.append x y ⟨m + i, by omega⟩ = y ⟨i, by omega⟩ :=
      Fin.append_right x y ⟨i, by omega⟩
    have h2 : Fin.append x y ⟨m + i + 1, by omega⟩ = y ⟨i + 1, hi⟩ := by
      rw [show (⟨m + i + 1, by omega⟩ : Fin (m + n)) = Fin.natAdd m ⟨i + 1, hi⟩ from
        Fin.ext (by dsimp [Fin.natAdd]; omega), Fin.append_right]
    rwa [h1, h2]
  | add _ _ hx₁ hx₂ => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx₁ hx₂

end RelationSubmodule

section KernelBridge

variable (R : Type u) [CommSemiring R]

private theorem toDirectSum_toTensorAlgebra (n : ℕ) (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    TensorAlgebra.toDirectSum (TensorPower.toTensorAlgebra t) =
      DirectSum.of (fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) n t := by
  rw [← show TensorAlgebra.ofDirectSum (DirectSum.of (fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) n t) =
      TensorPower.toTensorAlgebra t from
    DirectSum.toAddMonoid_of (fun _ ↦ LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) n t,
    TensorAlgebra.toDirectSum_ofDirectSum]

/-- The image of a pure tensor under `TensorPower.toTensorAlgebra` and `RingQuot.mkRingHom` is the
corresponding Milnor symbol. -/
theorem mkRingHom_toTensorAlgebra_tprod {n : ℕ} (x : Fin n → Additive Rˣ) :
    RingQuot.mkRingHom (milnorRel R) (TensorPower.toTensorAlgebra (PiTensorProduct.tprod ℤ x)) =
      symbol (List.ofFn fun i ↦ Additive.toMul (x i)) := by
  rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply, map_list_prod, symbol_def,
    List.map_ofFn, List.map_ofFn]
  congr 1; ext i; simp [Function.comp_def, ofUnit_def, ofMul_toMul]

private theorem mkRingHom_toTensorAlgebra_eq_zero_of_mem_relationSubmodule {n : ℕ}
    {t : (⨂[ℤ]^n) (Additive Rˣ)} (ht : t ∈ relationSubmodule R n) :
    RingQuot.mkRingHom (milnorRel R) (TensorPower.toTensorAlgebra t) = 0 := by
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hu hv ↦ by rw [map_add, map_add, hu, hv, add_zero])
    (fun _ _ _ hu ↦ by rw [map_zsmul, map_zsmul, hu, smul_zero]) ht
  rintro _ ⟨x, i, hi, hab, rfl⟩
  rw [mkRingHom_toTensorAlgebra_tprod]
  let l : List Rˣ := List.ofFn fun j ↦ Additive.toMul (x j)
  have hsplit : l = l.take i ++ Additive.toMul (x ⟨i, by omega⟩) ::
      Additive.toMul (x ⟨i + 1, hi⟩) :: l.drop (i + 2) := by
    have hi1 : i < l.length := by simp [l]; omega
    have hi2 : i + 1 < l.length := by simp [l]; omega
    conv_lhs => rw [← List.take_append_drop i l, List.drop_eq_getElem_cons hi1,
      List.drop_eq_getElem_cons hi2]
    simp [l]
  change symbol l = 0; rw [hsplit]
  exact symbol_of_add_eq_one_at (l.take i) hab (l.drop (i + 2))

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

/-- An element of `TensorAlgebra ℤ (Additive Rˣ)` lies in the kernel of the Steinberg quotient map
if and only if each of its homogeneous tensor-power components lies in `relationSubmodule R n`. -/
theorem mem_ker_mkRingHom_iff (z : TensorAlgebra ℤ (Additive Rˣ)) :
    z ∈ RingHom.ker (RingQuot.mkRingHom (milnorRel R)) ↔
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
    have hrel : ∀ x y, milnorRel R x y → I.ringCon.mk' x = I.ringCon.mk' y := by
      intro _ _ h
      rcases (milnorRel_def R _ _).mp h with ⟨a, b, hab, rfl, rfl⟩
      refine I.ringCon.eq.mpr fun n ↦ ?_
      rw [sub_zero, map_mul, TensorAlgebra.toDirectSum_ι, TensorAlgebra.toDirectSum_ι,
        DirectSum.of_mul_of, TensorPower.tprod_mul_tprod]
      by_cases hn : 1 + 1 = n
      · subst hn; rw [DirectSum.of_eq_same]
        refine tprod_mem_relationSubmodule _ (i := 0) (by omega) ?_
        change (a : R) + (b : R) = 1; exact hab
      · rw [DirectSum.of_eq_of_ne (1 + 1) n _ (Ne.symm hn)]; exact Submodule.zero_mem _
    have hq := RingQuot.lift_mkRingHom_apply I.ringCon.mk' hrel z
    rw [RingHom.mem_ker.mp hz, map_zero] at hq
    have hrc : z - 0 ∈ H := I.ringCon.eq.mp hq.symm
    rwa [sub_zero] at hrc
  · intro hz
    classical
    rw [RingHom.mem_ker, ← TensorAlgebra.ofDirectSum_toDirectSum z]
    conv_lhs => rw [← DirectSum.sum_support_of (TensorAlgebra.toDirectSum z)]
    rw [map_sum, map_sum]
    exact Finset.sum_eq_zero fun n _ ↦ by
      rw [show TensorAlgebra.ofDirectSum (DirectSum.of (fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) n
          (TensorAlgebra.toDirectSum z n)) =
          TensorPower.toTensorAlgebra (TensorAlgebra.toDirectSum z n) from
        DirectSum.toAddMonoid_of
          (fun _ ↦ LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) n _]
      exact mkRingHom_toTensorAlgebra_eq_zero_of_mem_relationSubmodule R (hz n)

/-- A degree-`n` tensor lies in the kernel of the Steinberg quotient map if and only if it belongs
to `relationSubmodule R n`. -/
theorem toTensorAlgebra_mem_ker_iff {n : ℕ} (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    TensorPower.toTensorAlgebra t ∈ RingHom.ker (RingQuot.mkRingHom (milnorRel R)) ↔
      t ∈ relationSubmodule R n := by
  rw [mem_ker_mkRingHom_iff, toDirectSum_toTensorAlgebra]
  refine ⟨fun h ↦ by simpa [DirectSum.of_eq_same] using h n, fun ht k ↦ ?_⟩
  by_cases hnk : n = k
  · subst hnk; simpa [DirectSum.of_eq_same] using ht
  · rw [DirectSum.of_eq_of_ne n k _ (Ne.symm hnk)]; exact Submodule.zero_mem _

end KernelBridge

section DegreeQuotient

variable (R : Type u) [CommSemiring R]

private theorem toTensorAlgebra_mem_range_pow {n : ℕ} (t : (⨂[ℤ]^n) (Additive Rˣ)) :
    TensorPower.toTensorAlgebra t ∈
      (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ n := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul]; refine Submodule.smul_mem _ r ?_
    rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]
    have hlen : ∀ l : List (Additive Rˣ), (l.map (TensorAlgebra.ι ℤ)).prod ∈
        (TensorAlgebra.ι ℤ : Additive Rˣ →ₗ[ℤ] TensorAlgebra ℤ (Additive Rˣ)).range ^ l.length := by
      intro l; induction l with
      | nil =>
        rw [List.map_nil, List.prod_nil, List.length_nil, pow_zero]
        exact Submodule.one_le.mp le_rfl
      | cons u l ih =>
        rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
        exact Submodule.mul_mem_mul ⟨u, rfl⟩ ih
    simpa [List.length_ofFn, List.map_ofFn, Function.comp_def] using hlen (List.ofFn x)
  | add _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- The canonical `ℤ`-linear surjection `(⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] MilnorK.degree R n`. -/
noncomputable def toDegree (n : ℕ) : (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] degree R n where
  toFun t :=
    ⟨RingQuot.mkRingHom (milnorRel R) (TensorPower.toTensorAlgebra t), by
      rw [degree_def]
      exact ⟨TensorPower.toTensorAlgebra t, toTensorAlgebra_mem_range_pow R t, rfl⟩⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

/-- `toDegree R n` maps a pure tensor `tprod ℤ x` to the corresponding Milnor symbol. -/
theorem toDegree_tprod {n : ℕ} (x : Fin n → Additive Rˣ) :
    (toDegree R n (PiTensorProduct.tprod ℤ x) : MilnorK R) =
      symbol (List.ofFn fun i ↦ Additive.toMul (x i)) :=
  mkRingHom_toTensorAlgebra_tprod R x

/-- `toDegree` intertwines graded tensor multiplication with multiplication in `MilnorK R`. -/
theorem toDegree_gMul {m n : ℕ} (a : (⨂[ℤ]^m) (Additive Rˣ)) (b : (⨂[ℤ]^n) (Additive Rˣ)) :
    (toDegree R (m + n)
      (GradedMonoid.GMul.mul (A := fun k ↦ (⨂[ℤ]^k) (Additive Rˣ)) a b) : MilnorK R) =
      (toDegree R m a : MilnorK R) * (toDegree R n b : MilnorK R) := by
  change RingQuot.mkRingHom (milnorRel R) (TensorPower.toTensorAlgebra _) = _
  rw [TensorPower.toTensorAlgebra_gMul, map_mul]; rfl

/-- The kernel of `toDegree R n` is precisely `relationSubmodule R n`. -/
theorem ker_toDegree (n : ℕ) : LinearMap.ker (toDegree R n) = relationSubmodule R n := by
  ext t
  rw [LinearMap.mem_ker, Subtype.ext_iff]
  exact toTensorAlgebra_mem_ker_iff R t

/-- `toDegree R n` is surjective onto `MilnorK.degree R n`. -/
theorem surjective_toDegree (n : ℕ) : Function.Surjective (toDegree R n) := fun x ↦ by
  induction x using degree_inductionOn with
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
    (degreeEquivQuotient R n).symm (Submodule.Quotient.mk t) = toDegree R n t := by rfl

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

/-- The canonical graded `ℤ`-algebra equivalence `(⨁ n : ℕ, MilnorK.degree R n) ≃ₐ[ℤ] MilnorK R`. -/
noncomputable def directSumDegreeEquiv : (⨁ n : ℕ, degree R n) ≃ₐ[ℤ] MilnorK R :=
  (isInternal_degree R).coeAlgEquiv

end DegreeQuotient

section Functoriality

variable {R : Type u} {S : Type*} [CommSemiring R] [CommSemiring S]

private noncomputable def mapTensorPower (f : R →+* S) (n : ℕ) :
    (⨂[ℤ]^n) (Additive Rˣ) →ₗ[ℤ] (⨂[ℤ]^n) (Additive Sˣ) :=
  PiTensorProduct.map fun _ ↦ (Units.map f.toMonoidHom).toAdditive.toIntLinearMap

private theorem mapTensorPower_mem_relationSubmodule (f : R →+* S) (n : ℕ)
    {t : (⨂[ℤ]^n) (Additive Rˣ)} (ht : t ∈ relationSubmodule R n) :
    mapTensorPower f n t ∈ relationSubmodule S n := by
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hu hv ↦ by rw [map_add]; exact Submodule.add_mem _ hu hv)
    (fun k _ _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ k hu) ht
  rintro _ ⟨x, i, hi, hab, rfl⟩
  change PiTensorProduct.map _ (PiTensorProduct.tprod ℤ x) ∈ relationSubmodule S n
  rw [PiTensorProduct.map_tprod]
  refine tprod_mem_relationSubmodule _ (i := i) hi ?_
  simpa [Units.map] using (map_add f _ _).symm.trans ((congrArg f hab).trans (map_one f))

/-- The `ℤ`-linear map on degree-`n` tensor-power quotients induced by a ring homomorphism `f`. -/
noncomputable def mapQuotient (f : R →+* S) (n : ℕ) :
    (((⨂[ℤ]^n) (Additive Rˣ)) ⧸ relationSubmodule R n) →ₗ[ℤ]
      (((⨂[ℤ]^n) (Additive Sˣ)) ⧸ relationSubmodule S n) :=
  Submodule.mapQ (relationSubmodule R n) (relationSubmodule S n) (mapTensorPower f n)
    fun _ ht ↦ mapTensorPower_mem_relationSubmodule f n ht

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
      rw [mapDegree_apply, toDegree_tprod, map_symbol]
      change symbol _ = (toDegree S n (PiTensorProduct.map _ (PiTensorProduct.tprod ℤ y)) :
        MilnorK S)
      rw [PiTensorProduct.map_tprod, toDegree_tprod, List.map_ofFn]; rfl
    | add _ _ hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  rw [hcomm, degreeEquivQuotient_toDegree]; rfl

end Functoriality

section LowDegrees

variable (R : Type u) [CommSemiring R]

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 0 ≃ₗ[ℤ] ℤ`. -/
noncomputable def degreeZeroEquiv : degree R 0 ≃ₗ[ℤ] ℤ :=
  (degreeEquivQuotient R 0).trans
    ((Submodule.quotEquivOfEqBot (relationSubmodule R 0) (relationSubmodule_zero R)).trans
      (PiTensorProduct.isEmptyEquiv (Fin 0)))

/-- `(degreeZeroEquiv R).symm k` has underlying value `(k : MilnorK R)`. -/
@[simp]
theorem degreeZeroEquiv_symm_apply (k : ℤ) :
    ((degreeZeroEquiv R).symm k : MilnorK R) = (k : MilnorK R) := by
  change RingQuot.mkRingHom (milnorRel R)
    (TensorPower.toTensorAlgebra (k • PiTensorProduct.tprod ℤ Fin.elim0)) = k
  rw [map_zsmul, map_zsmul, TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]
  simp [zsmul_eq_mul]

/-- `degreeZeroEquiv R` sends `1 ∈ MilnorK.degree R 0` to `1 : ℤ`. -/
@[simp]
theorem degreeZeroEquiv_one : degreeZeroEquiv R ⟨1, one_mem_degree_zero⟩ = 1 :=
  (degreeZeroEquiv R).symm.injective <| by
    rw [LinearEquiv.symm_apply_apply]
    exact Subtype.ext (by rw [degreeZeroEquiv_symm_apply, Int.cast_one])

/-- The canonical integer map `ℤ → MilnorK R` is injective for every commutative semiring `R`. -/
theorem intCast_injective : Function.Injective (Int.cast : ℤ → MilnorK R) := fun _ _ h ↦
  (degreeZeroEquiv R).symm.injective <|
    Subtype.ext (by rw [degreeZeroEquiv_symm_apply, degreeZeroEquiv_symm_apply, h])

/-- `1 ≠ 0` in `MilnorK R` for every commutative semiring `R`. -/
theorem one_ne_zero : (1 : MilnorK R) ≠ 0 := fun h ↦
  Int.one_ne_zero (intCast_injective R (by simpa using h))

/-- `MilnorK R` is nontrivial for every commutative semiring `R`. -/
theorem nontrivial : Nontrivial (MilnorK R) := ⟨⟨1, 0, one_ne_zero R⟩⟩

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 1 ≃ₗ[ℤ] Additive Rˣ`. -/
noncomputable def degreeOneEquiv : degree R 1 ≃ₗ[ℤ] Additive Rˣ :=
  (degreeEquivQuotient R 1).trans
    ((Submodule.quotEquivOfEqBot (relationSubmodule R 1) (relationSubmodule_one R)).trans
      (PiTensorProduct.subsingletonEquiv (0 : Fin 1)))

/-- `(degreeOneEquiv R).symm (Additive.ofMul a)` has underlying value `MilnorK.ofUnit a`. -/
@[simp]
theorem degreeOneEquiv_symm_ofMul (a : Rˣ) :
    ((degreeOneEquiv R).symm (Additive.ofMul a) : MilnorK R) = ofUnit a := by
  change (toDegree R 1 (PiTensorProduct.tprod ℤ (fun _ : Fin 1 ↦ Additive.ofMul a)) :
    MilnorK R) = ofUnit a
  rw [toDegree_tprod]; simp

/-- `degreeOneEquiv R` sends `ofUnit a ∈ MilnorK.degree R 1` to `Additive.ofMul a`. -/
@[simp]
theorem degreeOneEquiv_ofUnit (a : Rˣ) :
    degreeOneEquiv R ⟨ofUnit a, ofUnit_mem_degree_one a⟩ = Additive.ofMul a :=
  (degreeOneEquiv R).symm.injective <| by
    rw [LinearEquiv.symm_apply_apply]
    exact Subtype.ext (degreeOneEquiv_symm_ofMul R a).symm

/-- `MilnorK.ofUnit : Rˣ → MilnorK R` is injective for every commutative semiring `R`. -/
theorem ofUnit_injective : Function.Injective (ofUnit (R := R)) := fun a b h ↦ by
  have h' : (⟨ofUnit a, ofUnit_mem_degree_one a⟩ : degree R 1) =
      ⟨ofUnit b, ofUnit_mem_degree_one b⟩ := Subtype.ext h
  have h'' := congrArg (degreeOneEquiv R) h'
  rw [degreeOneEquiv_ofUnit, degreeOneEquiv_ofUnit] at h''
  exact Additive.ofMul.injective h''

private noncomputable def tensorPowerTwoToSymbolGroup :
    (⨂[ℤ]^2) (Additive Rˣ) →ₗ[ℤ] SymbolGroup R :=
  PiTensorProduct.lift
    { toFun := fun x ↦ TauCeti.symbol (Additive.toMul (x 0)) (Additive.toMul (x 1))
      map_update_add' := fun _ i _ _ ↦ by fin_cases i <;> simp [symbol_mul_left, symbol_mul_right]
      map_update_smul' := fun _ i _ _ ↦ by
        fin_cases i <;> simp [symbol_zpow_left, symbol_zpow_right] }

private theorem relationSubmodule_two_le_ker_toSymbolGroup :
    relationSubmodule R 2 ≤ LinearMap.ker (tensorPowerTwoToSymbolGroup R) := by
  rw [relationSubmodule, Submodule.span_le]
  rintro _ ⟨x, i, hi, hab, rfl⟩
  obtain rfl : i = 0 := by omega
  rw [SetLike.mem_coe, LinearMap.mem_ker, tensorPowerTwoToSymbolGroup, PiTensorProduct.lift.tprod]
  exact symbol_of_add_eq_one hab

private noncomputable def degreeTwoToSymbolGroup : degree R 2 →ₗ[ℤ] SymbolGroup R :=
  (Submodule.liftQ (relationSubmodule R 2) (tensorPowerTwoToSymbolGroup R)
      (relationSubmodule_two_le_ker_toSymbolGroup R)).comp
    (degreeEquivQuotient R 2).toLinearMap

private theorem degreeTwoToSymbolGroup_symbol_pair (a b : Rˣ) :
    degreeTwoToSymbolGroup R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
      TauCeti.symbol a b := by
  have hsub : (⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ : degree R 2) =
      ⟨symbol (List.ofFn ![a, b]), symbol_mem_degree_of_length (List.length_ofFn (f := ![a, b]))⟩ :=
    Subtype.ext (congrArg symbol (by simp))
  rw [hsub]
  dsimp only [degreeTwoToSymbolGroup, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [degreeEquivQuotient_symbol_ofFn, Submodule.liftQ_apply, tensorPowerTwoToSymbolGroup,
    PiTensorProduct.lift.tprod]
  simp

private noncomputable def symbolGroupToDegreeTwo : SymbolGroup R →ₗ[ℤ] degree R 2 :=
  SymbolGroup.lift (fun a b ↦ ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩)
    { map_mul_left := fun _ _ _ ↦ Subtype.ext (by simp [symbol_pair, ofUnit_mul, add_mul])
      map_mul_right := fun _ _ _ ↦ Subtype.ext (by simp [symbol_pair, ofUnit_mul, mul_add])
      steinberg := fun hab ↦ Subtype.ext (by
        simpa [symbol_pair] using ofUnit_mul_ofUnit_of_add_eq_one hab) }

private theorem symbolGroupToDegreeTwo_symbol (a b : Rˣ) :
    symbolGroupToDegreeTwo R (TauCeti.symbol a b) =
      ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ :=
  SymbolGroup.lift_symbol _ _ a b

/-- The canonical `ℤ`-linear equivalence `MilnorK.degree R 2 ≃ₗ[ℤ] SymbolGroup R`, taking
`MilnorK.symbol [a, b]` to `TauCeti.symbol a b`. -/
noncomputable def degreeTwoEquivSymbolGroup : degree R 2 ≃ₗ[ℤ] SymbolGroup R :=
  LinearEquiv.ofLinearMap (degreeTwoToSymbolGroup R) (symbolGroupToDegreeTwo R)
    (LinearMap.ext fun q ↦ by
      induction q using SymbolGroup.inductionOn with
      | symbol a b => simp [symbolGroupToDegreeTwo_symbol, degreeTwoToSymbolGroup_symbol_pair]
      | add _ _ hx hy =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at hx hy ⊢; rw [hx, hy])
    (LinearMap.ext fun x ↦ by
      induction x using degree_inductionOn with
      | zero => simp
      | symbol l hl =>
        match l, hl with
        | [a, b], _ => simp [degreeTwoToSymbolGroup_symbol_pair, symbolGroupToDegreeTwo_symbol]
      | add _ _ hx hy =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at hx hy ⊢; rw [hx, hy]
      | smul _ _ hx =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_smul] at hx ⊢; rw [hx])

/-- `degreeTwoEquivSymbolGroup R` sends the two-entry Milnor symbol `{a, b}` to `symbol a b`. -/
@[simp]
theorem degreeTwoEquivSymbolGroup_symbol_pair (a b : Rˣ) :
    degreeTwoEquivSymbolGroup R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
      TauCeti.symbol a b :=
  degreeTwoToSymbolGroup_symbol_pair R a b

/-- `(degreeTwoEquivSymbolGroup R).symm` sends `symbol a b` to the two-entry Milnor symbol
`{a, b}`. -/
@[simp]
theorem degreeTwoEquivSymbolGroup_symm_symbol (a b : Rˣ) :
    (degreeTwoEquivSymbolGroup R).symm (TauCeti.symbol a b) =
      ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ :=
  symbolGroupToDegreeTwo_symbol R a b

/-- The degree-two identification `degree R 2 ≃ₗ[ℤ] SymbolGroup R` is natural with respect to ring
homomorphisms. -/
theorem degreeTwoEquivSymbolGroup_mapDegree {S : Type*} [CommSemiring S] (f : R →+* S)
    (x : degree R 2) :
    degreeTwoEquivSymbolGroup S (mapDegree f 2 x) =
      SymbolGroup.map f (degreeTwoEquivSymbolGroup R x) := by
  induction x using degree_inductionOn with
  | zero => simp
  | symbol l hl =>
    match l, hl with
    | [a, b], _ =>
      have hmap : mapDegree f 2 ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ =
          ⟨symbol [Units.map f.toMonoidHom a, Units.map f.toMonoidHom b],
            symbol_mem_degree_of_length rfl⟩ :=
        Subtype.ext (by rw [mapDegree_apply, map_symbol]; simp)
      rw [hmap, degreeTwoEquivSymbolGroup_symbol_pair, degreeTwoEquivSymbolGroup_symbol_pair,
        SymbolGroup.map_symbol]
  | add _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul _ _ hx => rw [map_smul, map_smul, map_smul, map_smul, hx]

end LowDegrees

end MilnorK

end TauCeti
