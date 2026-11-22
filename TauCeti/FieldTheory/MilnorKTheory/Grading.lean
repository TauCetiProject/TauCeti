/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.FieldTheory.MilnorKTheory.Basic
public import TauCeti.LinearAlgebra.TensorAlgebra.Projection
import TauCeti.Algebra.Algebra.Operations
import TauCeti.Algebra.RingQuot
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
import TauCeti.RingTheory.TwoSidedIdeal.Span

/-!
# Grading and low-degree identifications of Milnor K-theory

The Steinberg relation ideal in `TensorAlgebra ℤ (Additive Rˣ)` is generated in degree `2`, so its
degree-`n` slice equals `milnorRelPiece R n` (`mem_ker_quotient_and_mem_range_pow_iff`) and the
images `MilnorK.degree R n` give an internal `ℕ`-grading `GradedAlgebra (MilnorK.degree R)` with
graded universal property `MilnorK.gradedLift`. Identifying each piece with
`TensorPower ℤ n (Additive Rˣ) ⧸ milnorTensorRel R n` (`degreeEquivQuotient`) yields canonical
low-degree equivalences `degreeZeroEquiv` (`K₀ᴹ ≃ₗ[ℤ] ℤ`), `degreeOneEquiv`
(`K₁ᴹ ≃ₗ[ℤ] Additive Rˣ`), and `degreeTwoEquiv` (`K₂ᴹ ≃ₗ[ℤ] SymbolGroup R`), all natural with
respect to `gradedMap` and `mapDegree`.

## References

* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, §7.1.
* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), 318–344.
-/

public section

open scoped DirectSum TensorProduct
open TensorAlgebra (ι tensorPowerProjection)
open LinearMap (range)

namespace TauCeti.MilnorK

universe u v

variable {R : Type u} [CommSemiring R]

/-! ### Degree-`n` submodules -/

variable (R) in
/-- The degree-`n` Milnor K-group `Kₙᴹ(R)`, defined as the image of Mathlib's degree-`n`
tensor-algebra submodule `(TensorAlgebra.ι ℤ).range ^ n` under `MilnorK.quotient`. -/
def degree (n : ℕ) : Submodule ℤ (MilnorK R) :=
  Submodule.map (quotient R).toIntAlgHom.toLinearMap ((ι ℤ (M := Additive Rˣ)).range ^ n)

/-- Unfolding lemma for `TauCeti.MilnorK.degree`. -/
theorem degree_def (R : Type u) [CommSemiring R] (n : ℕ) : degree R n =
    Submodule.map (quotient R).toIntAlgHom.toLinearMap
      ((ι ℤ (M := Additive Rˣ)).range ^ n) := by rfl
theorem one_mem_degree_zero : (1 : MilnorK R) ∈ degree R 0 := by
  rw [← map_one (quotient R)]
  exact Submodule.mem_map_of_mem (by rw [pow_zero]; exact Submodule.one_le.mp le_rfl)
theorem intCast_mem_degree_zero (k : ℤ) : (k : MilnorK R) ∈ degree R 0 := by
  simpa only [zsmul_eq_mul, mul_one] using Submodule.smul_mem (degree R 0) k one_mem_degree_zero
theorem ofUnit_mem_degree_one (a : Rˣ) : ofUnit a ∈ degree R 1 := by
  rw [ofUnit_def]
  exact Submodule.mem_map_of_mem
    (by rw [pow_one]; exact LinearMap.mem_range_self _ (Additive.ofMul a))
theorem mul_mem_degree {m n : ℕ} {x y : MilnorK R} (hx : x ∈ degree R m) (hy : y ∈ degree R n) :
    x * y ∈ degree R (m + n) := by
  rw [degree] at hx hy
  obtain ⟨t₁, ht₁, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨t₂, ht₂, rfl⟩ := Submodule.mem_map.mp hy
  simp only [AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, ← map_mul]
  exact Submodule.mem_map_of_mem (by rw [pow_add]; exact Submodule.mul_mem_mul ht₁ ht₂)

/-- Multiplication adds degrees in `MilnorK R`. -/
instance : SetLike.GradedMonoid (degree R) where
  one_mem := one_mem_degree_zero
  mul_mem _ _ _ _ hx hy := mul_mem_degree hx hy

theorem symbol_mem_degree (l : List Rˣ) : symbol l ∈ degree R l.length := by
  simpa [symbol_def] using
    SetLike.list_prod_map_mem_graded (A := degree R) l (fun _ => (1 : ℕ)) ofUnit
      fun a _ => ofUnit_mem_degree_one a
theorem symbol_mem_degree_of_length {n : ℕ} {l : List Rˣ} (hl : l.length = n) :
    symbol l ∈ degree R n := hl ▸ symbol_mem_degree l

/-- `MilnorK.degree R n` is spanned over `ℤ` by the Milnor symbols of length `n`. -/
theorem degree_eq_span (R : Type u) [CommSemiring R] (n : ℕ) :
    degree R n = Submodule.span ℤ {x | ∃ l : List Rˣ, l.length = n ∧ x = symbol l} := by
  rw [degree, Submodule.range_pow_eq_span, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨List.ofFn fun i => Additive.toMul (v i), List.length_ofFn, ?_⟩
    rw [← TensorAlgebra.tprod_apply, quotient_tprod]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨_, ⟨fun i => Additive.ofMul (l[i]'(by omega)), rfl⟩, ?_⟩
    rw [← TensorAlgebra.tprod_apply, quotient_tprod]
    congr 1
    exact List.ext_getElem (by simp [hl]) fun i hi _ => by simp

theorem degree_le_iff {n : ℕ} {S : Submodule ℤ (MilnorK R)} :
    degree R n ≤ S ↔ ∀ l : List Rˣ, l.length = n → symbol l ∈ S := by
  rw [degree_eq_span, Submodule.span_le]
  exact ⟨fun h l hl => h ⟨l, hl, rfl⟩, fun h _ ⟨l, hl, hx⟩ => hx ▸ h l hl⟩

/-- Two additive homomorphisms out of `degree R n` agree if they agree on length-`n` symbols. -/
theorem degree_addMonoidHom_ext {n : ℕ} {A : Type*} [AddCommGroup A] {f g : degree R n →+ A}
    (h : ∀ (l : List Rˣ) (hl : l.length = n),
      f ⟨symbol l, symbol_mem_degree_of_length hl⟩ = g ⟨symbol l, symbol_mem_degree_of_length hl⟩) :
    f = g := by
  apply AddMonoidHom.toIntLinearMap_injective
  rw [Submodule.linearMap_eq_iff_of_eq_span _ _ (degree_eq_span R n)]
  rintro ⟨_, l, hl, rfl⟩
  exact h l hl

/-- Two `ℤ`-linear maps out of `degree R n` agree if they agree on length-`n` symbols. -/
theorem degree_linearMap_ext {n : ℕ} {A : Type*} [AddCommGroup A] {f g : degree R n →ₗ[ℤ] A}
    (h : ∀ (l : List Rˣ) (hl : l.length = n),
      f ⟨symbol l, symbol_mem_degree_of_length hl⟩ = g ⟨symbol l, symbol_mem_degree_of_length hl⟩) :
    f = g := LinearMap.toAddMonoidHom_injective (degree_addMonoidHom_ext h)

/-! ### Homogeneity of the two-sided Steinberg ideal -/

variable (R) in
/-- The two-sided Steinberg ideal in `TensorAlgebra ℤ (Additive Rˣ)`, generated by the degree-two
products `ι(a) * ι(b)` with `(a : R) + b = 1`. -/
def milnorIdeal : TwoSidedIdeal (TensorAlgebra ℤ (Additive Rˣ)) :=
  TwoSidedIdeal.span
    {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧ z = ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)}

/-- Unfolding lemma for `TauCeti.MilnorK.milnorIdeal`. -/
theorem milnorIdeal_def (R : Type u) [CommSemiring R] : milnorIdeal R = TwoSidedIdeal.span
    {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧ z = ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)} := by
  rfl

/-- The kernel of `MilnorK.quotient R` is the two-sided Steinberg ideal. -/
theorem ker_quotient_eq_milnorIdeal (R : Type u) [CommSemiring R] :
    RingHom.ker (quotient R) = (milnorIdeal R).asIdeal := by
  rw [RingQuot.ker_mkRingHom_eq_span, milnorIdeal]; congr 2; ext z; constructor
  · rintro ⟨_, _, hxy, rfl⟩
    obtain ⟨a, b, hab, rfl, rfl⟩ := milnorRel_iff.mp hxy; exact ⟨a, b, hab, by rw [sub_zero]⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨_, 0, milnorRel_iff.mpr ⟨a, b, hab, rfl, rfl⟩, (sub_zero _).symm⟩

/-- The kernel of `MilnorK.quotient R` is homogeneous for Mathlib's `ℕ`-grading of the tensor
algebra. -/
theorem isHomogeneous_ker_quotient (R : Type u) [CommSemiring R] :
    (RingHom.ker (quotient R)).IsHomogeneous
      ((range (ι ℤ (M := Additive Rˣ)) ^ ·) : ℕ → Submodule ℤ _) := by
  rw [ker_quotient_eq_milnorIdeal]
  refine TwoSidedIdeal.homogeneous_span _ fun _ ⟨_, _, _, h⟩ => ⟨2, ?_⟩
  dsimp only; rw [h, sq]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

variable (R) in
/-- The degree-`n` Steinberg relation submodule `Rₙ` in `TensorAlgebra ℤ (Additive Rˣ)`, spanned
by all homogeneous products `x * (ι(a) * ι(b)) * y` of total degree `i + 2 + j = n`. -/
def milnorRelPiece (n : ℕ) : Submodule ℤ (TensorAlgebra ℤ (Additive Rˣ)) :=
  Submodule.span ℤ {z | ∃ (i j : ℕ) (x y : TensorAlgebra ℤ (Additive Rˣ)) (a b : Rˣ),
    i + 2 + j = n ∧ x ∈ range (ι ℤ (M := Additive Rˣ)) ^ i ∧
    y ∈ range (ι ℤ (M := Additive Rˣ)) ^ j ∧ (a : R) + b = 1 ∧
    z = x * (ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)) * y}

/-- Unfolding lemma for `TauCeti.MilnorK.milnorRelPiece`. -/
theorem milnorRelPiece_def (R : Type u) [CommSemiring R] (n : ℕ) :
    milnorRelPiece R n = Submodule.span ℤ
      {z | ∃ (i j : ℕ) (x y : TensorAlgebra ℤ (Additive Rˣ)) (a b : Rˣ),
        i + 2 + j = n ∧ x ∈ range (ι ℤ (M := Additive Rˣ)) ^ i ∧
        y ∈ range (ι ℤ (M := Additive Rˣ)) ^ j ∧ (a : R) + b = 1 ∧
        z = x * (ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)) * y} := by rfl

theorem milnorRelPiece_le_range_pow (R : Type u) [CommSemiring R] (n : ℕ) :
    milnorRelPiece R n ≤ range (ι ℤ (M := Additive Rˣ)) ^ n := by
  rw [milnorRelPiece, Submodule.span_le]
  rintro _ ⟨i, j, _, _, _, _, rfl, hx, hy, -, rfl⟩
  rw [pow_add, pow_add, sq]
  exact Submodule.mul_mem_mul (Submodule.mul_mem_mul hx
    (Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _))) hy

/-- **Homogeneous slice of the Steinberg ideal**: a degree-`n` tensor lies in the kernel of
`MilnorK.quotient R` if and only if it belongs to `milnorRelPiece R n` (`J ∩ Tₙ = Rₙ`). -/
theorem mem_ker_quotient_and_mem_range_pow_iff {n : ℕ} {z : TensorAlgebra ℤ (Additive Rˣ)} :
    (z ∈ RingHom.ker (quotient R) ∧ z ∈ range (ι ℤ (M := Additive Rˣ)) ^ n) ↔
      z ∈ milnorRelPiece R n := by
  classical
  let 𝒯 : ℕ → Submodule ℤ (TensorAlgebra ℤ (Additive Rˣ)) := (range (ι ℤ (M := Additive Rˣ)) ^ ·)
  constructor
  · rintro ⟨hzker, hzdeg⟩
    let H : AddSubgroup (TensorAlgebra ℤ (Additive Rˣ)) :=
      (milnorRelPiece R n).toAddSubgroup.comap (GradedRing.proj 𝒯 n)
    have hsub : (milnorIdeal R : Set (TensorAlgebra ℤ (Additive Rˣ))) ⊆ H := by
      rw [milnorIdeal, TauCeti.TwoSidedIdeal.coe_span_subset_addSubgroup_iff]
      rintro x _ ⟨a, b, hab, rfl⟩ y
      rw [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, ← DirectSum.sum_support_decompose 𝒯 x,
        ← DirectSum.sum_support_decompose 𝒯 y, Finset.sum_mul, Finset.sum_mul, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Finset.mul_sum, map_sum]; refine Submodule.sum_mem _ fun j _ => ?_
      have h2 : ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b) ∈ 𝒯 2 := by
        dsimp only [𝒯]; rw [sq]
        exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
      have hmem := SetLike.mul_mem_graded
        (SetLike.mul_mem_graded (SetLike.coe_mem (DirectSum.decompose 𝒯 x i)) h2)
        (SetLike.coe_mem (DirectSum.decompose 𝒯 y j))
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒯 hmem]
      by_cases hdeg : i + 2 + j = n
      · subst hdeg; rw [DirectSum.of_eq_same]
        exact Submodule.subset_span
          ⟨i, j, _, _, a, b, rfl, SetLike.coe_mem _, SetLike.coe_mem _, hab, rfl⟩
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hdeg)]; exact Submodule.zero_mem _
    have hproj_z : GradedRing.proj 𝒯 n z ∈ milnorRelPiece R n :=
      hsub (TwoSidedIdeal.mem_asIdeal.mp (ker_quotient_eq_milnorIdeal R ▸ hzker))
    rwa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒯 hzdeg] at hproj_z
  · intro hz
    refine ⟨?_, milnorRelPiece_le_range_pow R n hz⟩
    rw [milnorRelPiece] at hz
    induction hz using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨_, _, _, _, _, _, -, -, -, hab, rfl⟩ := hw
      rw [RingHom.mem_ker, map_mul, map_mul, map_mul, quotient_ι, quotient_ι, toMul_ofMul,
        toMul_ofMul, ofUnit_mul_ofUnit_eq_zero hab, mul_zero, zero_mul]
    | zero => exact Ideal.zero_mem _
    | add _ _ _ _ hx hy => exact Ideal.add_mem _ hx hy
    | smul k _ _ hx => exact zsmul_mem hx k

@[simp] theorem milnorRelPiece_zero (R : Type u) [CommSemiring R] : milnorRelPiece R 0 = ⊥ := by
  rw [eq_bot_iff, milnorRelPiece, Submodule.span_le]; rintro _ ⟨i, j, -, -, -, -, hij, -⟩; omega
@[simp] theorem milnorRelPiece_one (R : Type u) [CommSemiring R] : milnorRelPiece R 1 = ⊥ := by
  rw [eq_bot_iff, milnorRelPiece, Submodule.span_le]; rintro _ ⟨i, j, -, -, -, -, hij, -⟩; omega

/-- In degree `2`, `milnorRelPiece R 2` is spanned by the Steinberg products `ι(a) * ι(b)`. -/
theorem milnorRelPiece_two (R : Type u) [CommSemiring R] :
    milnorRelPiece R 2 = Submodule.span ℤ
      {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧ z = ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)} := by
  refine le_antisymm ?_ (Submodule.span_le.mpr fun _ ⟨a, b, hab, hz⟩ => hz ▸ Submodule.subset_span
    ⟨0, 0, 1, 1, a, b, rfl, by rw [pow_zero]; exact Submodule.one_le.mp le_rfl,
      by rw [pow_zero]; exact Submodule.one_le.mp le_rfl, hab, by simp⟩)
  rw [milnorRelPiece, Submodule.span_le]
  rintro _ ⟨i, j, x, y, a, b, hij, hx, hy, hab, rfl⟩
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
  rw [pow_zero, Submodule.one_eq_range] at hx hy
  obtain ⟨m, rfl⟩ := hx; obtain ⟨k, rfl⟩ := hy
  have hmk : Algebra.linearMap ℤ _ m * (ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)) *
      Algebra.linearMap ℤ _ k = (m * k) • (ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)) := by
    simp only [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one, smul_smul, mul_comm m k]
  exact hmk ▸ Submodule.smul_mem _ (m * k) (Submodule.subset_span ⟨a, b, hab, rfl⟩)

variable (R) in
/-- The degree-`n` Steinberg relation submodule inside the `n`-th tensor power
`⨂[ℤ]^n (Additive Rˣ)`. -/
noncomputable def milnorTensorRel (n : ℕ) : Submodule ℤ (TensorPower ℤ n (Additive Rˣ)) :=
  (milnorRelPiece R n).map (tensorPowerProjection n)

/-- Unfolding lemma for `TauCeti.MilnorK.milnorTensorRel`. -/
theorem milnorTensorRel_def (R : Type u) [CommSemiring R] (n : ℕ) :
    milnorTensorRel R n = (milnorRelPiece R n).map (tensorPowerProjection n) := by rfl
@[simp] theorem milnorTensorRel_zero (R : Type u) [CommSemiring R] :
    milnorTensorRel R 0 = ⊥ := by simp [milnorTensorRel]
@[simp] theorem milnorTensorRel_one (R : Type u) [CommSemiring R] :
    milnorTensorRel R 1 = ⊥ := by simp [milnorTensorRel]

/-- In degree `2`, `milnorTensorRel R 2` is spanned by the pure Steinberg tensors
`tprod ![ofMul a, ofMul b]` with `(a : R) + b = 1`. -/
theorem milnorTensorRel_two (R : Type u) [CommSemiring R] :
    milnorTensorRel R 2 = Submodule.span ℤ {z | ∃ a b : Rˣ, (a : R) + b = 1 ∧
      z = PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b]} := by
  have hproj (a b : Rˣ) :
      tensorPowerProjection 2 (ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b)) =
        PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b] := by
    have htprod : ι ℤ (Additive.ofMul a) * ι ℤ (Additive.ofMul b) =
        TensorAlgebra.tprod ℤ (Additive Rˣ) 2 ![Additive.ofMul a, Additive.ofMul b] := by
      simp [TensorAlgebra.tprod_apply]
    rw [htprod, TensorAlgebra.tensorPowerProjection_tprod_self]
  rw [milnorTensorRel, milnorRelPiece_two, Submodule.map_span]; congr 1; ext z
  exact ⟨fun ⟨_, ⟨a, b, hab, hx⟩, hz⟩ => ⟨a, b, hab, hz.symm.trans (hx ▸ hproj a b)⟩,
    fun ⟨a, b, hab, hz⟩ => ⟨_, ⟨a, b, hab, rfl⟩, hz ▸ hproj a b⟩⟩

/-- Every element in `ker (MilnorK.quotient R)` projects in degree `n` into `milnorTensorRel`. -/
theorem tensorPowerProjection_mem_milnorTensorRel_of_mem_ker {n : ℕ}
    {z : TensorAlgebra ℤ (Additive Rˣ)} (hz : z ∈ RingHom.ker (quotient R)) :
    tensorPowerProjection n z ∈ milnorTensorRel R n := by
  let 𝒯 : ℕ → Submodule ℤ (TensorAlgebra ℤ (Additive Rˣ)) := (range (ι ℤ (M := Additive Rˣ)) ^ ·)
  rw [← TensorAlgebra.tensorPowerProjection_decompose n z]
  exact Submodule.mem_map_of_mem <| mem_ker_quotient_and_mem_range_pow_iff.mp
    ⟨isHomogeneous_ker_quotient R n hz, SetLike.coe_mem (DirectSum.decompose 𝒯 z n)⟩

/-! ### Internal `ℕ`-grading and graded universal property -/

/-- The degree pieces `MilnorK.degree R` form an internal direct sum decomposition of
`MilnorK R`. -/
theorem isInternal_degree (R : Type u) [CommSemiring R] : DirectSum.IsInternal (degree R) :=
  TauCeti.GradedAlgebra.isInternal_map ((range (ι ℤ (M := Additive Rˣ)) ^ ·) : ℕ → Submodule ℤ _)
    (quotient R).toIntAlgHom (RingQuot.mkRingHom_surjective (milnorRel R))
    (isHomogeneous_ker_quotient R)

/-- `MilnorK R` is internally `ℕ`-graded by `MilnorK.degree R`. -/
noncomputable instance : GradedAlgebra (degree R) := (isInternal_degree R).gradedAlgebra

/-- Two graded ring homomorphisms out of `degree R` agree when they agree on degree-one classes. -/
@[ext 1200] theorem gradedHom_ext {A τ : Type*} [Ring A] [SetLike τ A]
    {ℬ : ℕ → τ} {φ ψ : degree R →+*ᵍ ℬ} (h : ∀ a : Rˣ, φ (ofUnit a) = ψ (ofUnit a)) : φ = ψ :=
  GradedRingHom.ext fun x => RingHom.congr_fun (ringHom_ext h) x

section GradedLift

variable {A τ : Type*} [Ring A] [SetLike τ A] [AddSubgroupClass τ A]
  (ℬ : ℕ → τ) [SetLike.GradedMonoid ℬ] (f : Additive Rˣ →+ A)
  (hdeg : ∀ a : Rˣ, f (Additive.ofMul a) ∈ ℬ 1)
  (hf : ∀ a b : Rˣ, (a : R) + b = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)

variable (R) in
/-- **Graded universal property of `MilnorK R`**: an additive homomorphism `f : Additive Rˣ →+ A`
landing in `ℬ 1` and satisfying the Steinberg relation extends uniquely to `degree R →+*ᵍ ℬ`. -/
def gradedLift : degree R →+*ᵍ ℬ where
  toRingHom := lift R f hf
  map_mem {n _} hx := by
    rw [degree_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨l, rfl, rfl⟩ := hy; rw [lift_symbol]
      simpa using SetLike.list_prod_map_mem_graded (A := ℬ) l (fun _ => (1 : ℕ))
        (fun a => f (Additive.ofMul a)) fun a _ => hdeg a
    | zero => rw [map_zero]; exact zero_mem (ℬ n)
    | add _ _ _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul k _ _ hy => rw [map_zsmul]; exact zsmul_mem hy k

@[simp] theorem gradedLift_toRingHom : (gradedLift R ℬ f hdeg hf).toRingHom = lift R f hf := by rfl
@[simp] theorem gradedLift_apply (x : MilnorK R) :
    gradedLift R ℬ f hdeg hf x = lift R f hf x := by rfl
theorem gradedLift_unique (φ : degree R →+*ᵍ ℬ)
    (hφ : ∀ a : Rˣ, φ (ofUnit a) = f (Additive.ofMul a)) : φ = gradedLift R ℬ f hdeg hf :=
  gradedHom_ext fun a => (hφ a).trans (lift_ofUnit f hf a).symm

end GradedLift

/-! ### Degree-`n` quotient presentation and low-degree equivalences -/

/-- Canonical surjective `ℤ`-linear map from `⨂[ℤ]^n (Additive Rˣ)` onto `MilnorK.degree R n`. -/
noncomputable def tensorPowerToDegree (R : Type u) [CommSemiring R] (n : ℕ) :
    TensorPower ℤ n (Additive Rˣ) →ₗ[ℤ] degree R n :=
  (((quotient R).toIntAlgHom.toLinearMap.domRestrict _).codRestrict (degree R n)
      fun x => Submodule.mem_map_of_mem x.property).comp
    (TensorAlgebra.rangePowEquivTensorPower n).symm.toLinearMap

/-- Unfolding lemma for `TauCeti.MilnorK.tensorPowerToDegree`. -/
theorem tensorPowerToDegree_coe (n : ℕ) (x : TensorPower ℤ n (Additive Rˣ)) :
    (tensorPowerToDegree R n x : MilnorK R) = quotient R (TensorPower.toTensorAlgebra x) := by
  have h : (tensorPowerToDegree R n x : MilnorK R) =
      quotient R ((TensorAlgebra.rangePowEquivTensorPower n).symm x :
        TensorAlgebra ℤ (Additive Rˣ)) := rfl
  rw [h, TensorAlgebra.rangePowEquivTensorPower_symm_apply]
@[simp] theorem tensorPowerToDegree_tprod (n : ℕ) (v : Fin n → Additive Rˣ) :
    (tensorPowerToDegree R n (PiTensorProduct.tprod ℤ v) : MilnorK R) =
      symbol (List.ofFn fun i => Additive.toMul (v i)) := by
  rw [tensorPowerToDegree_coe, TensorPower.toTensorAlgebra_tprod, quotient_tprod]

theorem tensorPowerToDegree_surjective (R : Type u) [CommSemiring R] (n : ℕ) :
    Function.Surjective (tensorPowerToDegree R n) := by
  rintro ⟨_, hx⟩
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hx
  refine ⟨TensorAlgebra.rangePowEquivTensorPower n ⟨t, ht⟩, Subtype.ext ?_⟩
  dsimp only [tensorPowerToDegree, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem ker_tensorPowerToDegree (R : Type u) [CommSemiring R] (n : ℕ) :
    LinearMap.ker (tensorPowerToDegree R n) = milnorTensorRel R n := by
  ext x
  rw [LinearMap.mem_ker, Subtype.ext_iff, ZeroMemClass.coe_zero, tensorPowerToDegree_coe]
  constructor
  · intro hx
    exact ⟨_, mem_ker_quotient_and_mem_range_pow_iff.mp
      ⟨hx, TensorAlgebra.toTensorAlgebra_mem_range_ι_pow x⟩, by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (TensorAlgebra.tensorPowerProjection_comp_toTensorAlgebra n) x⟩
  · rintro ⟨z, hz, rfl⟩
    rw [TensorAlgebra.toTensorAlgebra_tensorPowerProjection_of_mem
      (milnorRelPiece_le_range_pow R n hz)]
    exact (mem_ker_quotient_and_mem_range_pow_iff.mpr hz).left

variable (R) in
/-- **Degree-`n` presentation of Milnor K-theory**: `MilnorK.degree R n` is canonically
`ℤ`-linearly equivalent to `(⨂[ℤ]^n (Additive Rˣ)) ⧸ milnorTensorRel R n`. -/
noncomputable def degreeEquivQuotient (n : ℕ) :
    degree R n ≃ₗ[ℤ] TensorPower ℤ n (Additive Rˣ) ⧸ milnorTensorRel R n :=
  ((tensorPowerToDegree R n).quotKerEquivOfSurjective
    (tensorPowerToDegree_surjective R n)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_tensorPowerToDegree R n))

@[simp] theorem degreeEquivQuotient_symm_mk_tprod (n : ℕ) (v : Fin n → Additive Rˣ) :
    ((degreeEquivQuotient R n).symm (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ v)) :
        MilnorK R) = symbol (List.ofFn fun i => Additive.toMul (v i)) := by
  have hmk : (Submodule.quotEquivOfEq _ _ (ker_tensorPowerToDegree R n)).symm
      (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ v)) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ v) :=
    (LinearEquiv.symm_apply_eq _).mpr (Submodule.quotEquivOfEq_mk _ _ _ _).symm
  rw [degreeEquivQuotient, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    hmk, LinearMap.quotKerEquivOfSurjective_apply_mk, tensorPowerToDegree_tprod]

theorem degreeEquivQuotient_symbol (n : ℕ) (v : Fin n → Rˣ) :
    degreeEquivQuotient R n ⟨symbol (List.ofFn v), symbol_mem_degree_of_length List.length_ofFn⟩ =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ fun i => Additive.ofMul (v i)) := by
  apply (degreeEquivQuotient R n).symm.injective
  rw [LinearEquiv.symm_apply_apply]; exact Subtype.ext (by simp)

variable (R) in
/-- **Degree-zero identification**: `K₀ᴹ(R) ≃ₗ[ℤ] ℤ`. -/
noncomputable def degreeZeroEquiv : degree R 0 ≃ₗ[ℤ] ℤ :=
  (degreeEquivQuotient R 0).trans
    ((Submodule.quotEquivOfEqBot _ (milnorTensorRel_zero R)).trans
      (PiTensorProduct.isEmptyEquiv (Fin 0)))

@[simp] theorem degreeZeroEquiv_one : degreeZeroEquiv R ⟨1, one_mem_degree_zero⟩ = 1 := by
  have h1 : (⟨1, one_mem_degree_zero⟩ : degree R 0) = (degreeEquivQuotient R 0).symm
      (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ Fin.elim0)) := Subtype.ext (by simp)
  rw [h1]
  simp [degreeZeroEquiv]
@[simp] theorem degreeZeroEquiv_intCast (k : ℤ) :
    degreeZeroEquiv R ⟨(k : MilnorK R), intCast_mem_degree_zero k⟩ = k := by
  have hk : (⟨(k : MilnorK R), intCast_mem_degree_zero k⟩ : degree R 0) =
      k • ⟨1, one_mem_degree_zero⟩ := Subtype.ext (by simp [zsmul_eq_mul])
  rw [hk, map_zsmul, degreeZeroEquiv_one, smul_eq_mul, mul_one]
@[simp] theorem degreeZeroEquiv_symm_apply (k : ℤ) :
    ((degreeZeroEquiv R).symm k : MilnorK R) = (k : MilnorK R) :=
  congrArg Subtype.val ((degreeZeroEquiv R).injective
    (a₂ := ⟨(k : MilnorK R), intCast_mem_degree_zero k⟩) (by simp))

/-- `MilnorK R` is always nontrivial: `1 ≠ 0` because `K₀ᴹ(R) ≃ₗ[ℤ] ℤ`. -/
instance : Nontrivial (MilnorK R) :=
  ⟨1, 0, fun h => one_ne_zero (by
    simpa only [degreeZeroEquiv_one, map_zero] using
      congrArg (degreeZeroEquiv R) (Subtype.ext h : (⟨1, one_mem_degree_zero⟩ : degree R 0) = 0))⟩

variable (R) in
/-- **Degree-one identification**: `K₁ᴹ(R) ≃ₗ[ℤ] Additive Rˣ`. -/
noncomputable def degreeOneEquiv : degree R 1 ≃ₗ[ℤ] Additive Rˣ :=
  (degreeEquivQuotient R 1).trans
    ((Submodule.quotEquivOfEqBot _ (milnorTensorRel_one R)).trans
      (PiTensorProduct.subsingletonEquiv (0 : Fin 1)))

@[simp] theorem degreeOneEquiv_ofUnit (a : Rˣ) :
    degreeOneEquiv R ⟨ofUnit a, ofUnit_mem_degree_one a⟩ = Additive.ofMul a := by
  have ha : (⟨ofUnit a, ofUnit_mem_degree_one a⟩ : degree R 1) = (degreeEquivQuotient R 1).symm
      (Submodule.Quotient.mk (PiTensorProduct.tprod ℤ fun _ : Fin 1 => Additive.ofMul a)) :=
    Subtype.ext (by simp)
  rw [ha]
  simp [degreeOneEquiv]
@[simp] theorem degreeOneEquiv_symm_apply (u : Additive Rˣ) :
    ((degreeOneEquiv R).symm u : MilnorK R) = ofUnit (Additive.toMul u) :=
  congrArg Subtype.val ((degreeOneEquiv R).injective
    (a₂ := ⟨ofUnit (Additive.toMul u), ofUnit_mem_degree_one _⟩) (by simp))

/-- The canonical unit map `ofUnit : Rˣ → MilnorK R` is injective. -/
theorem ofUnit_injective : Function.Injective (ofUnit (R := R)) := fun a b hab => by
  have h := congrArg (degreeOneEquiv R) (Subtype.ext hab :
    (⟨ofUnit a, ofUnit_mem_degree_one a⟩ : degree R 1) = ⟨ofUnit b, ofUnit_mem_degree_one b⟩)
  simpa using h

/-- The canonical additive homomorphism `ofUnitHom R : Additive Rˣ →+ MilnorK R` is injective. -/
theorem ofUnitHom_injective (R : Type u) [CommSemiring R] : Function.Injective (ofUnitHom R) :=
  fun _ _ h => by
    rw [ofUnitHom_apply, ofUnitHom_apply] at h; exact Additive.toMul.injective (ofUnit_injective h)

private noncomputable def tensorPowerTwoEquiv (R : Type u) [CommSemiring R] :
    Additive Rˣ ⊗[ℤ] Additive Rˣ ≃ₗ[ℤ] TensorPower ℤ 2 (Additive Rˣ) :=
  (TensorProduct.congr
    (PiTensorProduct.subsingletonEquiv (0 : Fin 1)).symm
    (PiTensorProduct.subsingletonEquiv (0 : Fin 1)).symm).trans
    (TensorPower.mulEquiv (R := ℤ) (M := Additive Rˣ) (n := 1) (m := 1))

private theorem tensorPowerTwoEquiv_tmul (a b : Additive Rˣ) :
    tensorPowerTwoEquiv R (a ⊗ₜ[ℤ] b) = PiTensorProduct.tprod ℤ ![a, b] := by
  simp only [tensorPowerTwoEquiv, TensorPower.mulEquiv]
  refine congrArg (PiTensorProduct.tprod ℤ) (funext fun i => ?_)
  fin_cases i <;> rfl

/-- Auxiliary `ℤ`-linear map from `⨂[ℤ]^2 (Additive Rˣ)` to `SymbolGroup R`. -/
private noncomputable def tensorPowerTwoToSymbolGroup (R : Type u) [CommSemiring R] :
    TensorPower ℤ 2 (Additive Rˣ) →ₗ[ℤ] SymbolGroup R :=
  ((steinbergRelations R).mkQ).comp (tensorPowerTwoEquiv R).symm.toLinearMap

private theorem tensorPowerTwoToSymbolGroup_tprod (a b : Rˣ) :
    tensorPowerTwoToSymbolGroup R
      (PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b]) = TauCeti.symbol a b := by
  have happly (x : TensorPower ℤ 2 (Additive Rˣ)) :
      tensorPowerTwoToSymbolGroup R x =
        (steinbergRelations R).mkQ ((tensorPowerTwoEquiv R).symm x) := rfl
  rw [happly, ← tensorPowerTwoEquiv_tmul, LinearEquiv.symm_apply_apply, Submodule.mkQ_apply,
    TauCeti.symbol_def]

private theorem milnorTensorRel_two_le_ker (R : Type u) [CommSemiring R] :
    milnorTensorRel R 2 ≤ LinearMap.ker (tensorPowerTwoToSymbolGroup R) := by
  rw [milnorTensorRel_two, Submodule.span_le]; rintro _ ⟨a, b, hab, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, tensorPowerTwoToSymbolGroup_tprod]
  exact TauCeti.symbol_eq_zero_of_add_eq_one hab

/-- Auxiliary `ℤ`-linear map `SymbolGroup R →ₗ[ℤ] degree R 2` sending `{a, b}` to `a * b`. -/
private noncomputable def symbolGroupToDegreeTwo (R : Type u) [CommSemiring R] :
    SymbolGroup R →ₗ[ℤ] degree R 2 :=
  SymbolGroup.lift (fun a b : Rˣ =>
      ⟨ofUnit a * ofUnit b, mul_mem_degree (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩)
    { map_mul_left := fun _ _ _ => Subtype.ext (by simp [ofUnit_mul, add_mul])
      map_mul_right := fun _ _ _ => Subtype.ext (by simp [ofUnit_mul, mul_add])
      steinberg := fun _ _ hab => Subtype.ext (ofUnit_mul_ofUnit_eq_zero hab) }

/-- `degreeEquivQuotient R 2` evaluates `ofUnit a * ofUnit b` to the quotient class of
`ofMul a ⊗ₜ ofMul b`. -/
theorem degreeEquivQuotient_ofUnit_mul (a b : Rˣ) :
    degreeEquivQuotient R 2 ⟨ofUnit a * ofUnit b,
      mul_mem_degree (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℤ ![Additive.ofMul a, Additive.ofMul b]) := by
  have h : (⟨ofUnit a * ofUnit b,
      mul_mem_degree (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ : degree R 2) =
      ⟨symbol (List.ofFn ![a, b]), symbol_mem_degree_of_length List.length_ofFn⟩ :=
    Subtype.ext (by simp [symbol_def])
  rw [h, degreeEquivQuotient_symbol]
  refine congrArg (Submodule.Quotient.mk ∘ PiTensorProduct.tprod ℤ) (funext fun i => ?_)
  fin_cases i <;> rfl

private theorem degreeTwo_symbol_eq_ofUnit_mul (a b : Rˣ) :
    (⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ : degree R 2) =
      ⟨ofUnit a * ofUnit b, mul_mem_degree (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ :=
  Subtype.ext (by simp)

variable (R) in
/-- **Degree-two identification**: `K₂ᴹ(R) ≃ₗ[ℤ] SymbolGroup R`, sending `ofUnit a * ofUnit b`
to `TauCeti.symbol a b`. -/
noncomputable def degreeTwoEquiv : degree R 2 ≃ₗ[ℤ] SymbolGroup R :=
  LinearEquiv.ofLinearMap
    ((Submodule.liftQ (milnorTensorRel R 2) (tensorPowerTwoToSymbolGroup R)
      (milnorTensorRel_two_le_ker R)).comp (degreeEquivQuotient R 2).toLinearMap)
    (symbolGroupToDegreeTwo R)
    (SymbolGroup.hom_ext fun a b => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, symbolGroupToDegreeTwo,
        SymbolGroup.lift_symbol, degreeEquivQuotient_ofUnit_mul, Submodule.liftQ_apply,
        tensorPowerTwoToSymbolGroup_tprod, LinearMap.id_apply])
    (degree_linearMap_ext fun l hl => match l, hl with
      | [a, b], _ => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
          degreeTwo_symbol_eq_ofUnit_mul, degreeEquivQuotient_ofUnit_mul, Submodule.liftQ_apply,
          tensorPowerTwoToSymbolGroup_tprod]
        exact Subtype.ext (by simp [symbolGroupToDegreeTwo]))

@[simp] theorem degreeTwoEquiv_ofUnit_mul (a b : Rˣ) :
    degreeTwoEquiv R ⟨ofUnit a * ofUnit b,
      mul_mem_degree (ofUnit_mem_degree_one a) (ofUnit_mem_degree_one b)⟩ = TauCeti.symbol a b := by
  have hsymm : (⟨ofUnit a * ofUnit b, mul_mem_degree (ofUnit_mem_degree_one a)
      (ofUnit_mem_degree_one b)⟩ : degree R 2) = (degreeTwoEquiv R).symm (TauCeti.symbol a b) :=
    Subtype.ext (by simp [degreeTwoEquiv, symbolGroupToDegreeTwo])
  rw [hsymm, LinearEquiv.apply_symm_apply]
theorem degreeTwoEquiv_symbol (a b : Rˣ) :
    degreeTwoEquiv R ⟨symbol [a, b], symbol_mem_degree_of_length rfl⟩ = TauCeti.symbol a b := by
  rw [degreeTwo_symbol_eq_ofUnit_mul, degreeTwoEquiv_ofUnit_mul]
@[simp] theorem degreeTwoEquiv_symm_symbol (a b : Rˣ) :
    ((degreeTwoEquiv R).symm (TauCeti.symbol a b) : MilnorK R) = ofUnit a * ofUnit b := by
  simp [degreeTwoEquiv, symbolGroupToDegreeTwo]

/-! ### Graded functoriality -/

section Map

variable {S T : Type*} [CommSemiring S] [CommSemiring T]

/-- Graded ring homomorphism `degree R →+*ᵍ degree S` induced by `f : R →+* S`. -/
def gradedMap (f : R →+* S) : degree R →+*ᵍ degree S where
  toRingHom := map f
  map_mem {n _} hx := by
    rw [degree, Submodule.map_pow, ← LinearMap.range_comp] at hx ⊢
    refine AlgHom.apply_mem_pow_of_mem_pow (map f).toIntAlgHom ?_ hx
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨Additive.ofMul (Units.map f.toMonoidHom (Additive.toMul u)), by
      simp [quotient_ι, map_ofUnit]⟩

@[simp] theorem gradedMap_toRingHom (f : R →+* S) : (gradedMap f).toRingHom = map f := by rfl
@[simp] theorem gradedMap_apply (f : R →+* S) (x : MilnorK R) : gradedMap f x = map f x := by rfl
@[simp] theorem gradedMap_id : gradedMap (RingHom.id R) = GradedRingHom.id (degree R) :=
  gradedHom_ext fun _ => by simp
@[simp] theorem gradedMap_comp (g : S →+* T) (f : R →+* S) :
    gradedMap (g.comp f) = (gradedMap g).comp (gradedMap f) :=
  gradedHom_ext fun _ => by
    simp only [gradedMap_apply, map_comp, RingHom.comp_apply, GradedRingHom.comp_apply]

/-- `MilnorK.map f` preserves degrees. -/
theorem map_mem_degree (f : R →+* S) {n : ℕ} {x : MilnorK R} (hx : x ∈ degree R n) :
    map f x ∈ degree S n := by
  rw [← gradedMap_apply f x]
  exact (gradedMap f).map_mem hx

/-- The degree-`n` `ℤ`-linear map `Kₙᴹ(R) →ₗ[ℤ] Kₙᴹ(S)` induced by `f : R →+* S`. -/
def mapDegree (f : R →+* S) (n : ℕ) : degree R n →ₗ[ℤ] degree S n :=
  ((gradedMap f).gradedAddHom n).toIntLinearMap

@[simp] theorem mapDegree_coe (f : R →+* S) (n : ℕ) (x : degree R n) :
    (mapDegree f n x : MilnorK S) = map f x.val := by
  simp [mapDegree, gradedMap_apply]
@[simp] theorem mapDegree_id (n : ℕ) : mapDegree (RingHom.id R) n = LinearMap.id := by ext x; simp
@[simp] theorem mapDegree_comp (g : S →+* T) (f : R →+* S) (n : ℕ) :
    mapDegree (g.comp f) n = (mapDegree g n).comp (mapDegree f n) := by ext x; simp

@[simp] theorem mapDegree_symbol (f : R →+* S) {n : ℕ} (l : List Rˣ) (hl : l.length = n) :
    mapDegree f n ⟨symbol l, symbol_mem_degree_of_length hl⟩ =
      ⟨symbol (l.map (Units.map f.toMonoidHom)),
        symbol_mem_degree_of_length (by simp [hl])⟩ :=
  Subtype.ext (by simp)

@[simp] theorem mapDegree_degreeZeroEquiv_symm (f : R →+* S) (k : ℤ) :
    mapDegree f 0 ((degreeZeroEquiv R).symm k) = (degreeZeroEquiv S).symm k :=
  Subtype.ext (by simp)

@[simp] theorem mapDegree_degreeOneEquiv_symm (f : R →+* S) (u : Additive Rˣ) :
    mapDegree f 1 ((degreeOneEquiv R).symm u) =
      (degreeOneEquiv S).symm (MonoidHom.toAdditive (Units.map f.toMonoidHom) u) :=
  Subtype.ext (by simp)

/-- Naturality of `degreeZeroEquiv` with respect to ring homomorphisms. -/
theorem degreeZeroEquiv_mapDegree (f : R →+* S) (x : degree R 0) :
    degreeZeroEquiv S (mapDegree f 0 x) = degreeZeroEquiv R x := by
  obtain ⟨k, rfl⟩ := (degreeZeroEquiv R).symm.surjective x
  simp

/-- Naturality of `degreeOneEquiv` with respect to ring homomorphisms. -/
theorem degreeOneEquiv_mapDegree (f : R →+* S) (x : degree R 1) :
    degreeOneEquiv S (mapDegree f 1 x) =
      MonoidHom.toAdditive (Units.map f.toMonoidHom) (degreeOneEquiv R x) := by
  obtain ⟨u, rfl⟩ := (degreeOneEquiv R).symm.surjective x
  simp

/-- Naturality of `degreeTwoEquiv` with respect to `SymbolGroup.map`. -/
theorem degreeTwoEquiv_mapDegree (f : R →+* S) (x : degree R 2) :
    degreeTwoEquiv S (mapDegree f 2 x) = SymbolGroup.map f (degreeTwoEquiv R x) := by
  refine LinearMap.congr_fun (f := (degreeTwoEquiv S).toLinearMap.comp (mapDegree f 2))
    (g := (SymbolGroup.map f).comp (degreeTwoEquiv R).toLinearMap) (degree_linearMap_ext fun l hl =>
      match l, hl with
      | [a, b], _ => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [mapDegree_symbol f (n := 2) [a, b] rfl]
        simp only [List.map_cons, List.map_nil]
        rw [degreeTwoEquiv_symbol, degreeTwoEquiv_symbol, SymbolGroup.map_symbol]) x

end Map

end TauCeti.MilnorK
