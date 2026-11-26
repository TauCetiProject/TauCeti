/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.GradedComul
public import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
public import TauCeti.RingTheory.Nilpotent.Exp.Ideal
public import TauCeti.RingTheory.Nilpotent.Log

/-!
# Baker–Campbell–Hausdorff products in truncated enveloping algebras

Let `L` be a Lie algebra with a grading by `ℕ`, and let `F` be the total-degree filtration of its
enveloping algebra `U`. In the truncation `U ⧸ F (c + 1)` every Lie element `x` of positive
degree has a nilpotent class, so the finite exponential `exp x` is defined. This file proves that
the product of two such exponentials is again the exponential of a Lie element: for `x` and `y`
in a positively graded rational Lie algebra there is `b` with `exp b = exp x * exp y` in
`U ⧸ F (c + 1)`. Applied to the free Lie algebra on two generators, this is the existence of the
Baker–Campbell–Hausdorff element of class `c`.

The proof is Friedrichs' criterion in truncated form. The comultiplication of `U` induces an
algebra map from `U ⧸ F (c + 1)` to the quotient of `U ⊗ U` by the order-`(c + 1)` term of its
total-degree filtration. It sends `exp x * exp y` to the product of its images under the two
inclusions, which commute, so it sends the logarithm of `exp x * exp y` to the sum of the images
of that logarithm under the two inclusions. A representative `u` of the logarithm therefore
satisfies `Δ u = 1 ⊗ u + u ⊗ 1` modulo filtration order `c + 1`. Its homogeneous components of
degree at most `c` are then primitive, hence Lie elements, because over a rational algebra
primitive elements of an enveloping algebra are exactly the image of the Lie algebra.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.exists_ι_sub_mem_of_comul_sub_mem`: over a commutative
  rational algebra, an element whose comultiplication agrees with `1 ⊗ u + u ⊗ 1` modulo
  filtration order `k` agrees with a Lie element modulo filtration order `k`.
* `TauCeti.UniversalEnvelopingAlgebra.exists_exp_ι_eq_exp_mul_exp`: in the truncated enveloping
  algebra of a positively graded rational Lie algebra, a product of two exponentials of Lie
  elements is the exponential of a Lie element.

## References

* K. O. Friedrichs, *Mathematical aspects of the quantum theory of fields V*, Comm. Pure Appl.
  Math. 6 (1953).
* C. Reutenauer, *Free Lie Algebras*, Oxford University Press (1993), §3.1, for the derivation
  of the Baker–Campbell–Hausdorff formula from Friedrichs' criterion.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section Criterion

variable {R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  (ℒ : ℕ → Submodule R L) [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝒜" => homogeneousSubmodule ℒ
local notation "π" => _root_.GradedAlgebra.proj (homogeneousSubmodule ℒ)
local notation "𝓕" => degreeFiltration ℒ (Nat.castAddMonoidHom ℤ)
  (fun n hn => absurd hn (not_lt.mpr (Int.natCast_nonneg n)))

/-- **Truncated Friedrichs criterion.** Over a commutative rational algebra, if the
comultiplication of `u` agrees with `1 ⊗ u + u ⊗ 1` modulo the order-`k` term of the total-degree
filtration of `U ⊗ U`, then `u` agrees with a Lie element modulo filtration order `k`. -/
theorem exists_ι_sub_mem_of_comul_sub_mem {u : U} {k : ℕ}
    (hu : Coalgebra.comul (R := R) u - (1 ⊗ₜ[R] u + u ⊗ₜ[R] 1) ∈
      ((𝓕).tensorProduct R 𝓕).ideal k) :
    ∃ x : L, _root_.UniversalEnvelopingAlgebra.ι R x - u ∈ (𝓕).ideal k := by
  classical
  -- Every homogeneous component of degree below `k` is primitive, hence a Lie element.
  have hprim : ∀ n : Fin k, ∃ x : L, _root_.UniversalEnvelopingAlgebra.ι R x = π n u := fun n =>
    (_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι (π n u)).mp
      (isPrimitiveElem_proj ℒ fun i j hij => by
        rw [← sub_eq_zero, ← map_sub]
        exact map_proj_eq_zero_of_mem_tensorProduct_ideal ℒ hu (by omega))
  choose f hf using hprim
  refine ⟨∑ n, f n, (mem_degreeFiltration_ideal_iff ℒ _ _).mpr fun m hm => ?_⟩
  have hmk : m < k := by simpa using hm
  have hproj : ∀ n : Fin k, π m (π n u) = if (n : ℕ) = m then π m u else 0 := by
    intro n
    have hn := TauCeti.GradedAlgebra.proj_mem 𝒜 n u
    split_ifs with h
    · rw [TauCeti.GradedAlgebra.proj_of_mem_same (h ▸ hn), h]
    · rw [TauCeti.GradedAlgebra.proj_of_mem_ne hn h]
  rw [← _root_.GradedAlgebra.proj_apply, map_sub, map_sum, map_sum]
  simp only [hf, hproj]
  rw [Finset.sum_eq_single ⟨m, hmk⟩ (fun n _ hn => by simp [Fin.ext_iff] at hn; simp [hn])
    (by simp)]
  simp

end Criterion

section Exp

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι ℚ

/-- Let `I` and `K` be two-sided ideals of `U` and `U ⊗ U` such that the comultiplication and
both tensor inclusions send `I` into `K`. If `x` and `y` have nilpotent classes modulo `I` and `u`
represents the logarithm of `exp x * exp y` modulo `I`, then `Δ u = 1 ⊗ u + u ⊗ 1` modulo `K`. -/
private theorem comul_sub_mem_of_mk_eq_log (I : Ideal U) [I.IsTwoSided]
    (K : Ideal (U ⊗[ℚ] U)) [K.IsTwoSided] (hΔ : I ≤ K.comap (Bialgebra.comulAlgHom ℚ U))
    (hl : I ≤ K.comap (Algebra.TensorProduct.includeLeft : U →ₐ[ℚ] U ⊗[ℚ] U))
    (hr : I ≤ K.comap (Algebra.TensorProduct.includeRight : U →ₐ[ℚ] U ⊗[ℚ] U))
    {x y : L} (hx : IsNilpotent (Ideal.Quotient.mk I (ι x)))
    (hy : IsNilpotent (Ideal.Quotient.mk I (ι y)))
    (hg : IsNilpotent (IsNilpotent.exp (Ideal.Quotient.mk I (ι x)) *
      IsNilpotent.exp (Ideal.Quotient.mk I (ι y)) - 1))
    {u : U} (hu : Ideal.Quotient.mk I u = IsNilpotent.log
      (IsNilpotent.exp (Ideal.Quotient.mk I (ι x)) * IsNilpotent.exp (Ideal.Quotient.mk I (ι y)))) :
    Coalgebra.comul (R := ℚ) u - (1 ⊗ₜ[ℚ] u + u ⊗ₜ[ℚ] 1) ∈ K := by
  -- The comultiplication and the two tensor inclusions, on the quotients.
  let Δ := Ideal.quotientMapₐ K (Bialgebra.comulAlgHom ℚ U) hΔ
  let ιₗ := Ideal.quotientMapₐ K _ hl
  let ιᵣ := Ideal.quotientMapₐ K _ hr
  have hcomm : ∀ a b, Commute (ιₗ a) (ιᵣ b) := by
    intro a b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine Commute.map ?_ (Ideal.Quotient.mk K)
    simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]
  -- The quotient comultiplication sends `exp z` to `ιₗ (exp z) * ιᵣ (exp z)`.
  have hΔexp : ∀ z : L, IsNilpotent (Ideal.Quotient.mk I (ι z)) →
      Δ (IsNilpotent.exp (Ideal.Quotient.mk I (ι z))) =
        ιₗ (IsNilpotent.exp (Ideal.Quotient.mk I (ι z))) *
          ιᵣ (IsNilpotent.exp (Ideal.Quotient.mk I (ι z))) := by
    intro z hz
    have hΔι : Δ (Ideal.Quotient.mk I (ι z)) =
        ιₗ (Ideal.Quotient.mk I (ι z)) + ιᵣ (Ideal.Quotient.mk I (ι z)) := by
      simp only [Δ, ιₗ, ιᵣ, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
        Bialgebra.comulAlgHom_apply, comul_ι, map_add, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply]
    rw [hz.map_exp, hΔι, IsNilpotent.exp_add_of_commute (hcomm _ _) (hz.map _) (hz.map _),
      ← hz.map_exp, ← hz.map_exp]
  set g := IsNilpotent.exp (Ideal.Quotient.mk I (ι x)) *
    IsNilpotent.exp (Ideal.Quotient.mk I (ι y)) with hg_def
  have hΔg : Δ g = ιₗ g * ιᵣ g := by
    rw [hg_def, map_mul, hΔexp x hx, hΔexp y hy, map_mul, map_mul, mul_assoc,
      ← mul_assoc (ιᵣ _), ← (hcomm _ _).eq, mul_assoc, mul_assoc]
  -- Hence it sends `log g` to `ιₗ (log g) + ιᵣ (log g)`.
  have hgₗ : IsNilpotent (ιₗ g - 1) := by simpa only [map_sub, map_one] using hg.map ιₗ
  have hgᵣ : IsNilpotent (ιᵣ g - 1) := by simpa only [map_sub, map_one] using hg.map ιᵣ
  have hΔlog : Δ (Ideal.Quotient.mk I u) =
      ιₗ (Ideal.Quotient.mk I u) + ιᵣ (Ideal.Quotient.mk I u) := by
    rw [hu, IsNilpotent.map_log hg, hΔg, IsNilpotent.log_mul_of_commute (hcomm g g) hgₗ hgᵣ,
      ← IsNilpotent.map_log hg, ← IsNilpotent.map_log hg]
  simp only [Δ, ιₗ, ιᵣ, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, ← map_add] at hΔlog
  rw [← Ideal.Quotient.eq, hΔlog, add_comm]

variable (ℒ : ℕ → Submodule ℚ L) [GradedLieAlgebra ℒ]

local notation "𝓕" => degreeFiltration ℒ (Nat.castAddMonoidHom ℤ)
  (fun n hn => absurd hn (not_lt.mpr (Int.natCast_nonneg n)))

/-- **Exponentials in a truncated enveloping algebra.** For a positively graded Lie algebra over
`ℚ`, in the quotient of the enveloping algebra by the order-`(c + 1)` term of its total-degree
filtration, a product of the exponentials of two Lie elements is the exponential of a Lie
element. -/
theorem exists_exp_ι_eq_exp_mul_exp (hpos : ℒ 0 = ⊥) (c : ℕ) (x y : L) :
    ∃ b : L, IsNilpotent.exp (Ideal.Quotient.mk ((𝓕).ideal (c + 1)) (ι b)) =
      IsNilpotent.exp (Ideal.Quotient.mk ((𝓕).ideal (c + 1)) (ι x)) *
        IsNilpotent.exp (Ideal.Quotient.mk ((𝓕).ideal (c + 1)) (ι y)) := by
  -- Classes of filtration order one form an ideal of nilpotent elements, containing the classes
  -- of all Lie elements.
  have hJ : ∀ z ∈ ((𝓕).ideal 1).map (Ideal.Quotient.mk ((𝓕).ideal (c + 1))), IsNilpotent z := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hz
    refine ⟨c + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact (𝓕).ideal_one_pow_le (c + 1) (Ideal.pow_mem_pow ha _)
  have hιJ : ∀ z : L, Ideal.Quotient.mk ((𝓕).ideal (c + 1)) (ι z) ∈
      ((𝓕).ideal 1).map (Ideal.Quotient.mk ((𝓕).ideal (c + 1))) := fun z =>
    Ideal.mem_map_of_mem _ (ι_mem_degreeFiltration_one ℒ _ (fun n hn => by
      obtain rfl : n = 0 := by simpa using hn
      exact hpos) z)
  have hg := hJ _ (Ideal.exp_mul_exp_sub_one_mem _ (hιJ x) (hιJ y) (hJ _ (hιJ x)) (hJ _ (hιJ y)))
  -- A representative of the logarithm is primitive modulo filtration order `c + 1`, hence a Lie
  -- element modulo filtration order `c + 1`.
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (IsNilpotent.log
    (IsNilpotent.exp (Ideal.Quotient.mk ((𝓕).ideal (c + 1)) (ι x)) *
      IsNilpotent.exp (Ideal.Quotient.mk ((𝓕).ideal (c + 1)) (ι y))))
  obtain ⟨b, hb⟩ := exists_ι_sub_mem_of_comul_sub_mem ℒ (comul_sub_mem_of_mk_eq_log _ _
    (fun _ ha => comul_mem_tensorProduct_ideal ℒ ha)
    ((𝓕).ideal_le_comap_includeLeft ℚ 𝓕 (c + 1)) ((𝓕).ideal_le_comap_includeRight ℚ 𝓕 (c + 1))
    (hJ _ (hιJ x)) (hJ _ (hιJ y)) hg hu)
  refine ⟨b, ?_⟩
  rw [Ideal.Quotient.eq.mpr hb, hu, IsNilpotent.exp_log hg]

end Exp

end TauCeti.UniversalEnvelopingAlgebra
