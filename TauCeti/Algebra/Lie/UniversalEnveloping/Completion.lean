/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.Algebra.Lie.UniversalEnveloping.Primitive
public import TauCeti.RingTheory.FilteredAlgebra.Bialgebra

/-!
# Completed universal enveloping bialgebras of graded Lie algebras

Let `L` be a graded Lie algebra over a commutative ring `R`, equipped with a degree homomorphism
`d : Γ →+ ℤ` such that negative-degree Lie pieces vanish, and let
`TauCeti.UniversalEnvelopingAlgebra.degreeFiltration` be the resulting total-degree filtration on
the universal enveloping algebra `U(L)`.

The bialgebra comultiplication maps each homogeneous piece of degree `n` into the sum of tensor
products of homogeneous pieces whose degrees add to `n`
(`TauCeti.UniversalEnvelopingAlgebra.comul_mem_iSup_map₂_homogeneousSubmodule`). Consequently,
comultiplication respects the total-degree filtration and extends to the completion, while the
order-one filtration ideal lies in the kernel of the counit and coincides with it whenever the Lie
grading is supported in strictly positive degrees.

For any completed primitive element `x` of the degree-completed enveloping algebra, every
homogeneous component of degree at most `k` of a representative of the order-`k` projection of `x`
is a primitive element of `U(L)`
(`TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_decompose_of_isCompletedPrimitive`). This
holds over any commutative ring, without a basis or flatness hypothesis.

Over a commutative `ℚ`-algebra `R : Type`, every primitive element of `U(L)` is the canonical image
of a Lie element, so every finite-order projection of a completed primitive element is represented
by a Lie element
(`TauCeti.UniversalEnvelopingAlgebra.exists_mk_ι_eq_projection_of_isCompletedPrimitive`).
When `L` is strictly positively graded and `U(L)` is also a `ℚ`-algebra, combining this with the
completed exponential and logarithm of filtered bialgebras shows that the product of exponentials of
two Lie elements in any finite-order degree quotient is again the exponential of a Lie element
(`TauCeti.UniversalEnvelopingAlgebra.exists_exp_eq_exp_mul_exp_degreeFiltration`).

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.comul_mem_iSup_map₂_homogeneousSubmodule`: comultiplication
  respects the total-degree grading of `U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_le_comap_comul`: comultiplication respects
  the enveloping degree filtration.
* `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_one_le_ker_counit` and
  `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_one_eq_ker_counit`: comparison of the
  order-one degree filtration ideal with the kernel of the counit.
* `TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_decompose_of_isCompletedPrimitive`: the
  low-degree homogeneous components of a completed primitive element are primitive in `U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.exists_mk_ι_eq_projection_of_isCompletedPrimitive`: over a
  commutative `ℚ`-algebra, every finite-order projection of a completed primitive element lifts to
  a Lie element.
* `TauCeti.UniversalEnvelopingAlgebra.exists_log_exp_mul_exp_degreeFiltration` and
  `TauCeti.UniversalEnvelopingAlgebra.exists_exp_eq_exp_mul_exp_degreeFiltration`: in every
  finite-order degree quotient of a strictly positively graded enveloping algebra over `ℚ`, the
  logarithm of `exp (ι x) * exp (ι y)` is represented by a Lie element.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section GradedComul

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

private theorem tmul_mul_mem_iSup_map₂ {a b m : Γ} {u v : U}
    (hu : u ∈ homogeneousSubmodule ℒ a) (hv : v ∈ homogeneousSubmodule ℒ b)
    {t : U ⊗[R] U}
    (ht : t ∈ ⨆ (p : Γ) (q : Γ) (_ : p + q = m),
      Submodule.map₂ (TensorProduct.mk R U U)
        (homogeneousSubmodule ℒ p) (homogeneousSubmodule ℒ q)) :
    (u ⊗ₜ[R] v) * t ∈ ⨆ (p : Γ) (q : Γ) (_ : p + q = a + b + m),
      Submodule.map₂ (TensorProduct.mk R U U)
        (homogeneousSubmodule ℒ p) (homogeneousSubmodule ℒ q) := by
  have hle :
      (⨆ (p : Γ) (q : Γ) (_ : p + q = m),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ p) (homogeneousSubmodule ℒ q)) ≤
      (⨆ (p : Γ) (q : Γ) (_ : p + q = a + b + m),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ p) (homogeneousSubmodule ℒ q)).comap
        (LinearMap.mulLeft R (u ⊗ₜ[R] v)) := by
    refine iSup_le fun p => iSup_le fun q => iSup_le fun hpq => Submodule.map₂_le.mpr ?_
    intro y hy z hz
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
    refine Submodule.mem_iSup_of_mem (a + p) (Submodule.mem_iSup_of_mem (b + q) ?_)
    rw [iSup_pos (by rw [← hpq, add_add_add_comm, add_assoc])]
    exact Submodule.apply_mem_map₂ _
      (SetLike.GradedMul.mul_mem hu hy) (SetLike.GradedMul.mul_mem hv hz)
  exact hle ht

private theorem comul_prod_mem_iSup_map₂ (l : List (Σ i, ℒ i)) :
    Coalgebra.comul (R := R) (l.map (fun x => ι R (x.2 : L))).prod ∈
      ⨆ (p : Γ) (q : Γ) (_ : p + q = (l.map Sigma.fst).sum),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ p) (homogeneousSubmodule ℒ q) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil]
    have h1 : Coalgebra.comul (R := R) (1 : U) = (1 : U) ⊗ₜ[R] (1 : U) := by
      rw [← Bialgebra.comulAlgHom_apply (R := R), map_one]
      rfl
    rw [h1]
    refine Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem 0 ?_)
    rw [iSup_pos (zero_add 0)]
    exact Submodule.apply_mem_map₂ _
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ))
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ))
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [← Bialgebra.comulAlgHom_apply (R := R), map_mul, Bialgebra.comulAlgHom_apply,
      Bialgebra.comulAlgHom_apply, comul_ι, add_mul]
    have h1 := tmul_mul_mem_iSup_map₂ ℒ (ι_mem_homogeneousSubmodule ℒ x.2.property)
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ)) ih
    have h2 := tmul_mul_mem_iSup_map₂ ℒ
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ))
      (ι_mem_homogeneousSubmodule ℒ x.2.property) ih
    rw [add_zero] at h1
    rw [zero_add] at h2
    exact Submodule.add_mem _ h1 h2

/-- Comultiplication on `U(L)` maps each homogeneous piece of degree `n` into the sum of tensor
products of homogeneous pieces whose degrees add to `n`. -/
theorem comul_mem_iSup_map₂_homogeneousSubmodule {n : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ n) :
    Coalgebra.comul (R := R) a ∈
      ⨆ (p : Γ) (q : Γ) (_ : p + q = n),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ p) (homogeneousSubmodule ℒ q) := by
  have hle :
      homogeneousSubmodule ℒ n ≤
        (⨆ (p : Γ) (q : Γ) (_ : p + q = n),
          Submodule.map₂ (TensorProduct.mk R U U)
            (homogeneousSubmodule ℒ p) (homogeneousSubmodule ℒ q)).comap
          (Coalgebra.comul (R := R)) := by
    rw [homogeneousSubmodule_le_iff]
    intro l hl
    rw [Submodule.mem_comap, ← hl]
    exact comul_prod_mem_iSup_map₂ ℒ l
  exact hle ha

end GradedComul

section FilteredBialgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- Comultiplication respects the total-degree filtration on `U(L)`. -/
theorem degreeFiltration_le_comap_comul (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (degreeFiltration ℒ d hneg).ideal k ≤
      (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal k).comap
        (Bialgebra.comulAlgHom R U) := by
  let F := degreeFiltration ℒ d hneg
  rw [degreeFiltration_ideal_le_iff]
  intro n hn a ha
  -- Unfold ideal comap membership to evaluate `Bialgebra.comulAlgHom` in the tensor filtration.
  change Bialgebra.comulAlgHom R U a ∈ (F.tensorProduct R F).ideal k
  rw [Bialgebra.comulAlgHom_apply, AlgFiltration.mem_tensorProduct_ideal_iff]
  have hsub :
      (⨆ (p : Γ) (q : Γ) (_ : p + q = n),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ p) (homogeneousSubmodule ℒ q)) ≤
      tensorFiltrationTail (fun m => (F.ideal m).restrictScalars R)
        (fun m => (F.ideal m).restrictScalars R) k := by
    refine iSup_le fun p => iSup_le fun q => iSup_le fun hpq => Submodule.map₂_le.mpr ?_
    intro u hu v hv
    rw [TensorProduct.mk_apply]
    by_cases hp : d p < 0
    · have hu0 : u = 0 := by
        simpa only [homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hp,
          Submodule.mem_bot] using hu
      simp [hu0]
    · by_cases hq : d q < 0
      · have hv0 : v = 0 := by
          simpa only [homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hq,
            Submodule.mem_bot] using hv
        simp [hv0]
      · have hdpq : d p + d q = d n := by rw [← map_add, hpq]
        refine tmul_mem_tensorFiltrationTail _ _ (a := (d p).toNat) (b := (d q).toNat)
          (by omega) ?_ ?_
        · exact mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hu (by omega)
        · exact mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hv (by omega)
  exact hsub (comul_mem_iSup_map₂_homogeneousSubmodule ℒ ha)

/-- The order-one degree filtration ideal lies in the kernel of the counit. -/
theorem degreeFiltration_one_le_ker_counit (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d hneg).ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R U) := by
  rw [← HopfIdeal.augmentation_toIdeal]
  exact degreeFiltration_le_augmentation ℒ d hneg Nat.one_pos

/-- For a strictly positive Lie grading, the order-one degree filtration ideal is precisely the
kernel of the counit. -/
theorem degreeFiltration_one_eq_ker_counit (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 =
      RingHom.ker (Bialgebra.counitAlgHom R U) := by
  rw [← HopfIdeal.augmentation_toIdeal]
  exact le_antisymm (degreeFiltration_le_augmentation ℒ d _ Nat.one_pos)
    (augmentation_le_degreeFiltration_one ℒ d hpos)

private noncomputable def homogProj (p : Γ) : U →ₗ[R] U :=
  (homogeneousSubmodule ℒ p).subtype.comp
    ((DirectSum.component R Γ (fun i => homogeneousSubmodule ℒ i) p).comp
      (DirectSum.decomposeLinearEquiv (homogeneousSubmodule ℒ)).toLinearMap)

private theorem homogProj_apply (p : Γ) (a : U) :
    homogProj ℒ p a = (DirectSum.decompose (homogeneousSubmodule ℒ) a p : U) := (rfl)

private theorem homogProj_mem (p : Γ) (a : U) :
    homogProj ℒ p a ∈ homogeneousSubmodule ℒ p :=
  (DirectSum.decompose (homogeneousSubmodule ℒ) a p).property

private theorem homogProj_of_mem_same {p : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ p) : homogProj ℒ p a = a :=
  DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ) ha

private theorem homogProj_of_mem_ne {p q : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ p) (h : p ≠ q) : homogProj ℒ q a = 0 :=
  DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ) ha h

private theorem exists_finset_sum_homogProj (a : U) :
    ∃ S : Finset Γ, ∀ T : Finset Γ, S ⊆ T → ∑ p ∈ T, homogProj ℒ p a = a := by
  classical
  refine ⟨(DirectSum.decompose (homogeneousSubmodule ℒ) a).support, fun T hT => ?_⟩
  rw [← Finset.sum_subset hT]
  · exact DirectSum.sum_support_decompose (homogeneousSubmodule ℒ) a
  · intro p _ hp
    rw [homogProj_apply, DFinsupp.notMem_support_iff.mp hp, ZeroMemClass.coe_zero]

private theorem exists_finset_map_sum_homogProj (t : U ⊗[R] U) :
    ∃ S₁ S₂ : Finset Γ, ∀ T₁ T₂ : Finset Γ, S₁ ⊆ T₁ → S₂ ⊆ T₂ →
      TensorProduct.map (∑ p ∈ T₁, homogProj ℒ p) (∑ q ∈ T₂, homogProj ℒ q) t = t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨S₁, hS₁⟩ := exists_finset_sum_homogProj ℒ a
    obtain ⟨S₂, hS₂⟩ := exists_finset_sum_homogProj ℒ b
    refine ⟨S₁, S₂, fun T₁ T₂ h₁ h₂ => ?_⟩
    simp only [TensorProduct.map_tmul, LinearMap.sum_apply, hS₁ T₁ h₁, hS₂ T₂ h₂]
  | add x y hx hy =>
    obtain ⟨S₁, S₂, hx⟩ := hx
    obtain ⟨S₁', S₂', hy⟩ := hy
    refine ⟨S₁ ∪ S₁', S₂ ∪ S₂', fun T₁ T₂ h₁ h₂ => ?_⟩
    rw [map_add,
      hx T₁ T₂ (Finset.union_subset_left h₁) (Finset.union_subset_left h₂),
      hy T₁ T₂ (Finset.union_subset_right h₁) (Finset.union_subset_right h₂)]

omit [AddCommMonoid Γ] [DecidableEq Γ] in
private theorem map_sum_left {S : Finset Γ} (f : Γ → U →ₗ[R] U) (g : U →ₗ[R] U) (t : U ⊗[R] U) :
    TensorProduct.map (∑ p ∈ S, f p) g t = ∑ p ∈ S, TensorProduct.map (f p) g t := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, TensorProduct.map_add_left, LinearMap.add_apply, ih]

omit [AddCommMonoid Γ] [DecidableEq Γ] in
private theorem map_sum_right {S : Finset Γ} (f : U →ₗ[R] U) (g : Γ → U →ₗ[R] U) (t : U ⊗[R] U) :
    TensorProduct.map f (∑ q ∈ S, g q) t = ∑ q ∈ S, TensorProduct.map f (g q) t := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, TensorProduct.map_add_right, LinearMap.add_apply, ih]

private theorem tensor_eq_zero_of_forall_map_homogProj_eq_zero {t : U ⊗[R] U}
    (ht : ∀ p q : Γ, TensorProduct.map (homogProj ℒ p) (homogProj ℒ q) t = 0) : t = 0 := by
  obtain ⟨S₁, S₂, hS⟩ := exists_finset_map_sum_homogProj ℒ t
  have h1 := hS S₁ S₂ (Finset.Subset.refl _) (Finset.Subset.refl _)
  rw [← h1, map_sum_left]
  simp only [map_sum_right, ht, Finset.sum_const_zero]

private theorem map_homogProj_comul_of_mem_ne {n p q : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ n) (h : p + q ≠ n) :
    TensorProduct.map (homogProj ℒ p) (homogProj ℒ q) (Coalgebra.comul (R := R) a) = 0 := by
  have hle :
      (⨆ (r : Γ) (s : Γ) (_ : r + s = n),
        Submodule.map₂ (TensorProduct.mk R U U)
          (homogeneousSubmodule ℒ r) (homogeneousSubmodule ℒ s)) ≤
      LinearMap.ker (TensorProduct.map (homogProj ℒ p) (homogProj ℒ q)) := by
    refine iSup_le fun r => iSup_le fun s => iSup_le fun hrs => Submodule.map₂_le.mpr ?_
    intro u hu v hv
    rw [LinearMap.mem_ker, TensorProduct.mk_apply, TensorProduct.map_tmul]
    by_cases hrp : r = p
    · have hsq : s ≠ q := fun hsq => h (by rw [← hrp, ← hsq, hrs])
      rw [homogProj_of_mem_ne ℒ hv hsq, TensorProduct.tmul_zero]
    · rw [homogProj_of_mem_ne ℒ hu hrp, TensorProduct.zero_tmul]
  exact LinearMap.mem_ker.mp (hle (comul_mem_iSup_map₂_homogeneousSubmodule ℒ ha))

private theorem map_homogProj_comul_eq_map_homogProj_comul_homogProj (p q : Γ) (a : U) :
    TensorProduct.map (homogProj ℒ p) (homogProj ℒ q) (Coalgebra.comul (R := R) a) =
      TensorProduct.map (homogProj ℒ p) (homogProj ℒ q)
        (Coalgebra.comul (R := R) (homogProj ℒ (p + q) a)) := by
  obtain ⟨S₀, hS₀⟩ := exists_finset_sum_homogProj ℒ a
  let S := insert (p + q) S₀
  have ha : ∑ m ∈ S, homogProj ℒ m a = a := hS₀ S (Finset.subset_insert _ _)
  conv_lhs => rw [← ha]
  rw [map_sum, map_sum]
  exact Finset.sum_eq_single (p + q)
    (fun m _ hm => map_homogProj_comul_of_mem_ne ℒ (homogProj_mem ℒ m a) (Ne.symm hm))
    (fun h => (h (Finset.mem_insert_self _ _)).elim)

private theorem map_homogProj_eq_zero_of_mem_tensorProduct_ideal
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) {k : ℕ} {t : U ⊗[R] U}
    (ht : t ∈ ((degreeFiltration ℒ d hneg).tensorProduct R
      (degreeFiltration ℒ d hneg)).ideal k)
    {p q : Γ} (hpq : d p + d q < k) :
    TensorProduct.map (homogProj ℒ p) (homogProj ℒ q) t = 0 := by
  rw [AlgFiltration.mem_tensorProduct_ideal_iff] at ht
  have hle :
      tensorFiltrationTail (fun m => ((degreeFiltration ℒ d hneg).ideal m).restrictScalars R)
        (fun m => ((degreeFiltration ℒ d hneg).ideal m).restrictScalars R) k ≤
      LinearMap.ker (TensorProduct.map (homogProj ℒ p) (homogProj ℒ q)) := by
    rw [tensorFiltrationTail_le_iff]
    intro r s hrs u hu v hv
    rw [LinearMap.mem_ker, TensorProduct.map_tmul]
    by_cases hpr : d p < r
    · rw [homogProj_apply ℒ p u,
        (mem_degreeFiltration_ideal_iff ℒ d hneg).mp hu p hpr, TensorProduct.zero_tmul]
    · have hqs : d q < s := by omega
      rw [homogProj_apply ℒ q v,
        (mem_degreeFiltration_ideal_iff ℒ d hneg).mp hv q hqs, TensorProduct.tmul_zero]
  exact LinearMap.mem_ker.mp (hle ht)

private theorem homogProj_tmul_one_eq {p q n : Γ} (hpq : p + q = n) (a : U) :
    homogProj ℒ p (homogProj ℒ n a) ⊗ₜ[R] homogProj ℒ q 1 =
      homogProj ℒ p a ⊗ₜ[R] homogProj ℒ q 1 := by
  by_cases hq : q = 0
  · subst hq
    rw [add_zero] at hpq
    subst hpq
    rw [homogProj_of_mem_same ℒ (homogProj_mem ℒ p a)]
  · rw [homogProj_of_mem_ne ℒ
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ)) (Ne.symm hq),
      TensorProduct.tmul_zero, TensorProduct.tmul_zero]

private theorem one_tmul_homogProj_eq {p q n : Γ} (hpq : p + q = n) (a : U) :
    homogProj ℒ p 1 ⊗ₜ[R] homogProj ℒ q (homogProj ℒ n a) =
      homogProj ℒ p 1 ⊗ₜ[R] homogProj ℒ q a := by
  by_cases hp : p = 0
  · subst hp
    rw [zero_add] at hpq
    subst hpq
    rw [homogProj_of_mem_same ℒ (homogProj_mem ℒ q a)]
  · rw [homogProj_of_mem_ne ℒ
      (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ)) (Ne.symm hp),
      TensorProduct.zero_tmul, TensorProduct.zero_tmul]

/-- **Componentwise primitivity of completed primitives.** If `x` is a completed primitive element
of the degree-completed enveloping algebra and `a` represents `x` modulo filtration order `k + 1`,
then every homogeneous component of `a` of degree at most `k` is a primitive element of `U(L)`. -/
theorem isPrimitiveElem_decompose_of_isCompletedPrimitive
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : (degreeFiltration ℒ d hneg).completion}
    (hx : (degreeFiltration ℒ d hneg).IsCompletedPrimitive R
      (degreeFiltration_le_comap_comul ℒ d hneg) x)
    {k : ℕ} {a : U}
    (ha : Ideal.Quotient.mk ((degreeFiltration ℒ d hneg).ideal (k + 1)) a =
      (degreeFiltration ℒ d hneg).projection k x)
    {n : Γ} (hn : d n ≤ k) :
    Bialgebra.IsPrimitiveElem R
      (DirectSum.decompose (homogeneousSubmodule ℒ) a n : U) := by
  let F := degreeFiltration ℒ d hneg
  let hcomul := degreeFiltration_le_comap_comul ℒ d hneg
  apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr
  rw [add_comm, ← sub_eq_zero]
  apply tensor_eq_zero_of_forall_map_homogProj_eq_zero ℒ
  intro p q
  rw [map_sub, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul]
  -- Rewrite the degree-`n` component via the private projection `homogProj`.
  change TensorProduct.map (homogProj ℒ p) (homogProj ℒ q)
      (Coalgebra.comul (R := R) (homogProj ℒ n a)) -
    (homogProj ℒ p (homogProj ℒ n a) ⊗ₜ[R] homogProj ℒ q 1 +
      homogProj ℒ p 1 ⊗ₜ[R] homogProj ℒ q (homogProj ℒ n a)) = 0
  by_cases hpq : p + q = n
  · have hmem : Coalgebra.comul (R := R) a - (a ⊗ₜ[R] (1 : U) + (1 : U) ⊗ₜ[R] a) ∈
        (F.tensorProduct R F).ideal (k + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      have hproj := congrArg ((F.tensorProduct R F).projection k) hx.completedCoproduct_eq
      rw [F.projection_completedCoproduct R hcomul, map_add,
        F.projection_includeLeftCompletion R F, F.projection_includeRightCompletion R F, ← ha,
        Ideal.quotient_map_mkₐ, Ideal.quotient_map_mkₐ, Ideal.quotient_map_mkₐ,
        Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, ← map_add] at hproj
      exact hproj
    have hdpq : d p + d q < ((k + 1 : ℕ) : ℤ) := by
      have : d p + d q = d n := by rw [← map_add, hpq]
      omega
    have hkill := map_homogProj_eq_zero_of_mem_tensorProduct_ideal ℒ d hneg hmem hdpq
    rw [map_sub, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul,
      map_homogProj_comul_eq_map_homogProj_comul_homogProj ℒ p q a, hpq] at hkill
    rw [homogProj_tmul_one_eq ℒ hpq a, one_tmul_homogProj_eq ℒ hpq a]
    exact hkill
  · rw [map_homogProj_comul_of_mem_ne ℒ (homogProj_mem ℒ n a) hpq]
    have h1 : homogProj ℒ p (homogProj ℒ n a) ⊗ₜ[R] homogProj ℒ q 1 = 0 := by
      by_cases hq : q = 0
      · subst hq
        rw [add_zero] at hpq
        rw [homogProj_of_mem_ne ℒ (homogProj_mem ℒ n a) (Ne.symm hpq), TensorProduct.zero_tmul]
      · rw [homogProj_of_mem_ne ℒ
          (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ)) (Ne.symm hq),
          TensorProduct.tmul_zero]
    have h2 : homogProj ℒ p 1 ⊗ₜ[R] homogProj ℒ q (homogProj ℒ n a) = 0 := by
      by_cases hp : p = 0
      · subst hp
        rw [zero_add] at hpq
        rw [homogProj_of_mem_ne ℒ (homogProj_mem ℒ n a) (Ne.symm hpq), TensorProduct.tmul_zero]
      · rw [homogProj_of_mem_ne ℒ
          (SetLike.GradedOne.one_mem (A := homogeneousSubmodule ℒ)) (Ne.symm hp),
          TensorProduct.zero_tmul]
    rw [h1, h2, add_zero, sub_zero]

end FilteredBialgebra

section RationalLifting

universe v

variable {Γ : Type*} {R : Type} {L : Type v}
  [AddCommMonoid Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ) [GradedLieAlgebra ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- Over a commutative `ℚ`-algebra `R : Type`, every finite-order projection of a completed
primitive element of a degree-completed universal enveloping algebra is represented by a Lie
element. -/
theorem exists_mk_ι_eq_projection_of_isCompletedPrimitive
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {x : (degreeFiltration ℒ d hneg).completion}
    (hx : (degreeFiltration ℒ d hneg).IsCompletedPrimitive R
      (degreeFiltration_le_comap_comul ℒ d hneg) x)
    (k : ℕ) :
    ∃ b : L,
      Ideal.Quotient.mk ((degreeFiltration ℒ d hneg).ideal (k + 1)) (ι R b) =
        (degreeFiltration ℒ d hneg).projection k x := by
  classical
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((degreeFiltration ℒ d hneg).projection k x)
  let S : Finset Γ :=
    (DirectSum.decompose (homogeneousSubmodule ℒ) a).support.filter (fun n => d n ≤ k)
  let bU : U := ∑ n ∈ S, (DirectSum.decompose (homogeneousSubmodule ℒ) a n : U)
  have hbU : Bialgebra.IsPrimitiveElem R bU :=
    Submodule.sum_mem (Coalgebra.skewPrimitive R (1 : U) 1) fun n hn => by
      rw [Finset.mem_filter] at hn
      exact isPrimitiveElem_decompose_of_isCompletedPrimitive ℒ d hneg hx ha hn.2
  obtain ⟨b, hb⟩ :=
    (_root_.UniversalEnvelopingAlgebra.isPrimitiveElem_iff_mem_range_ι bU).mp hbU
  refine ⟨b, ?_⟩
  rw [← ha, Ideal.Quotient.eq, mem_degreeFiltration_ideal_iff]
  intro m hm
  rw [hb, DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, sub_eq_zero]
  simp only [bU, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  by_cases hmS : m ∈ S
  · rw [Finset.sum_eq_single m]
    · exact DirectSum.decompose_of_mem_same (homogeneousSubmodule ℒ)
        (DirectSum.decompose (homogeneousSubmodule ℒ) a m).property
    · intro n _ hnm
      exact DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ)
        (DirectSum.decompose (homogeneousSubmodule ℒ) a n).property hnm
    · exact fun h => (h hmS).elim
  · rw [Finset.sum_eq_zero]
    · have hnot : m ∉ (DirectSum.decompose (homogeneousSubmodule ℒ) a).support := fun hsup =>
        hmS (Finset.mem_filter.mpr ⟨hsup, by omega⟩)
      rw [DFinsupp.notMem_support_iff.mp hnot, ZeroMemClass.coe_zero]
    · intro n hn
      have hnm : n ≠ m := fun h => hmS (h ▸ hn)
      exact DirectSum.decompose_of_mem_ne (homogeneousSubmodule ℒ)
        (DirectSum.decompose (homogeneousSubmodule ℒ) a n).property hnm

/-- For a strictly positively graded Lie algebra over a commutative `ℚ`-algebra `R : Type` whose
enveloping algebra is a `ℚ`-algebra, the logarithm of `exp (ι x) * exp (ι y)` in any finite-order
degree quotient is represented by a Lie element. -/
theorem exists_log_exp_mul_exp_degreeFiltration [Algebra ℚ U]
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (x y : L) (k : ℕ) :
    ∃ b : L,
      Ideal.Quotient.mk ((degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal (k + 1))
          (ι R b) =
        IsNilpotent.log
          (IsNilpotent.exp
              (Ideal.Quotient.mk
                ((degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal (k + 1)) (ι R x)) *
            IsNilpotent.exp
              (Ideal.Quotient.mk
                ((degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal (k + 1)) (ι R y))) := by
  let hneg : ∀ n, d n < 0 → ℒ n = ⊥ := fun n hn => hpos n hn.le
  let F := degreeFiltration ℒ d hneg
  let hcomul := degreeFiltration_le_comap_comul ℒ d hneg
  let hker := degreeFiltration_one_eq_ker_counit ℒ d hpos
  let xc : F.completionIdeal 1 :=
    ⟨F.toCompletion (ι R x),
      (F.toCompletion_mem_completionIdeal_iff 1 (ι R x)).mpr
        (ι_mem_degreeFiltration_one ℒ d hpos x)⟩
  let yc : F.completionIdeal 1 :=
    ⟨F.toCompletion (ι R y),
      (F.toCompletion_mem_completionIdeal_iff 1 (ι R y)).mpr
        (ι_mem_degreeFiltration_one ℒ d hpos y)⟩
  have hxgl := F.isCompletedGroupLike_completedExp R hcomul hker.le xc
    (AlgFiltration.IsCompletedPrimitive.toCompletion (isPrimitiveElem_ι R L x))
  have hygl := F.isCompletedGroupLike_completedExp R hcomul hker.le yc
    (AlgFiltration.IsCompletedPrimitive.toCompletion (isPrimitiveElem_ι R L y))
  have hugl := hxgl.mul hygl
  have hu₁ := hugl.sub_one_mem_completionIdeal_one hker
  have hz := F.isCompletedPrimitive_completedLog R hcomul
    ⟨F.completedExp xc * F.completedExp yc, hu₁⟩ hugl.comul_eq_completedTensor_self
  obtain ⟨b, hb⟩ := exists_mk_ι_eq_projection_of_isCompletedPrimitive ℒ d hneg hz k
  refine ⟨b, hb.trans ?_⟩
  simp only [AlgFiltration.projection_completedLog, map_mul, AlgFiltration.projection_completedExp,
    AlgFiltration.projection_toCompletion, F, xc, yc]

/-- For a strictly positively graded Lie algebra over a commutative `ℚ`-algebra `R : Type` whose
enveloping algebra is a `ℚ`-algebra, the product of exponentials of two Lie elements in any
finite-order degree quotient is the exponential of a Lie element. -/
theorem exists_exp_eq_exp_mul_exp_degreeFiltration [Algebra ℚ U]
    (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) (x y : L) (k : ℕ) :
    ∃ b : L,
      IsNilpotent.exp
          (Ideal.Quotient.mk ((degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal (k + 1))
            (ι R b)) =
        IsNilpotent.exp
            (Ideal.Quotient.mk ((degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal (k + 1))
              (ι R x)) *
          IsNilpotent.exp
            (Ideal.Quotient.mk ((degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal (k + 1))
              (ι R y)) := by
  let hneg : ∀ n, d n < 0 → ℒ n = ⊥ := fun n hn => hpos n hn.le
  let F := degreeFiltration ℒ d hneg
  obtain ⟨b, hb⟩ := exists_log_exp_mul_exp_degreeFiltration ℒ d hpos x y k
  refine ⟨b, ?_⟩
  rw [hb]
  let xc : F.completionIdeal 1 :=
    ⟨F.toCompletion (ι R x),
      (F.toCompletion_mem_completionIdeal_iff 1 (ι R x)).mpr
        (ι_mem_degreeFiltration_one ℒ d hpos x)⟩
  let yc : F.completionIdeal 1 :=
    ⟨F.toCompletion (ι R y),
      (F.toCompletion_mem_completionIdeal_iff 1 (ι R y)).mpr
        (ι_mem_degreeFiltration_one ℒ d hpos y)⟩
  have hu₁ : F.completedExp xc * F.completedExp yc - 1 ∈ F.completionIdeal 1 := by
    have h1 := F.completedExp_sub_one_mem xc
    have h2 := F.completedExp_sub_one_mem yc
    have heq : F.completedExp xc * F.completedExp yc - 1 =
        (F.completedExp xc - 1) * F.completedExp yc + (F.completedExp yc - 1) := by
      rw [sub_mul, one_mul, sub_add_sub_cancel]
    rw [heq]
    exact Ideal.add_mem _ ((F.completionIdeal 1).mul_mem_right _ h1) h2
  have hnil :
      IsNilpotent
        (IsNilpotent.exp (Ideal.Quotient.mk (F.ideal (k + 1)) (ι R x)) *
          IsNilpotent.exp (Ideal.Quotient.mk (F.ideal (k + 1)) (ι R y)) - 1) := by
    simpa only [map_sub, map_mul, map_one, F.projection_completedExp, F.projection_toCompletion,
      xc, yc] using F.isNilpotent_projection hu₁ k
  exact IsNilpotent.exp_log hnil

end RationalLifting

end TauCeti.UniversalEnvelopingAlgebra
