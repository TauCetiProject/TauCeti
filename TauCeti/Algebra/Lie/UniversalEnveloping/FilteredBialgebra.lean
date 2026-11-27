/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
public import TauCeti.RingTheory.FilteredAlgebra.TensorProduct.Basic

import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Filtered and graded bialgebra properties of universal enveloping algebras

For a `Γ`-graded Lie algebra `L`, the bialgebra comultiplication `Δ : U(L) → U(L) ⊗[R] U(L)`
preserves total Lie degree (`comul_mem_tensorTotalDegree`) and hence the total-degree filtration
(`degreeFiltration_le_comap_comulAlgHom`). When negative degrees vanish, the first ideals of the
enveloping degree filtration and the induced tensor-product filtration lie in the kernels of their
respective counits.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra
open _root_.DirectSum (decompose decompose_of_mem_ne)

section Graded

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L)

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The `(p.1, p.2)`-homogeneous tensor component `U_{p.1} ⊗ U_{p.2}` inside `U(L) ⊗[R] U(L)`. -/
def tensorGrading (p : Γ × Γ) : Submodule R (U ⊗[R] U) :=
  InternalGrading.tensorProductBidegreePiece (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ) p

/-- Unfolding characterization of `tensorGrading`. -/
theorem tensorGrading_def (p : Γ × Γ) :
    tensorGrading ℒ p = Submodule.map₂ (TensorProduct.mk R U U)
      (homogeneousSubmodule ℒ p.1) (homogeneousSubmodule ℒ p.2) :=
  InternalGrading.tensorProductBidegreePiece_def _ _ p

/-- The homogeneous tensor components `tensorGrading ℒ` form an internal direct sum decomposition
of `U(L) ⊗[R] U(L)`. -/
theorem isInternal_tensorGrading [DecidableEq Γ] [GradedLieAlgebra ℒ] :
    _root_.DirectSum.IsInternal (tensorGrading ℒ) := by
  rw [funext (tensorGrading_def ℒ)]
  exact _root_.DirectSum.IsInternal.tensorProduct _ _
    (isInternal_homogeneousSubmodule ℒ) (isInternal_homogeneousSubmodule ℒ)

/-- Multiplication of homogeneous tensor components adds their bidegrees. -/
theorem mul_mem_tensorGrading {p q : Γ × Γ} {x y : U ⊗[R] U}
    (hx : x ∈ tensorGrading ℒ p) (hy : y ∈ tensorGrading ℒ q) :
    x * y ∈ tensorGrading ℒ (p + q) := by
  rw [tensorGrading_def] at hx hy ⊢
  exact ((Submodule.map₂_tmul_mul_le _ _ _ _).trans <| Submodule.map₂_le_map₂
    (GradedAlgebra.mul_le_grade_add (homogeneousSubmodule ℒ) p.1 q.1)
    (GradedAlgebra.mul_le_grade_add (homogeneousSubmodule ℒ) p.2 q.2))
    (Submodule.mul_mem_mul hx hy)

/-- The total-degree-`m` submodule `⨆ p₁ + p₂ = m, U_{p₁} ⊗ U_{p₂}` of `U(L) ⊗[R] U(L)`. -/
def tensorTotalDegree (m : Γ) : Submodule R (U ⊗[R] U) :=
  InternalGrading.tensorProductPiece (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ) m

/-- Unfolding characterization of `tensorTotalDegree`. -/
theorem tensorTotalDegree_def (m : Γ) :
    tensorTotalDegree ℒ m = ⨆ p : Γ × Γ, ⨆ _ : p.1 + p.2 = m, tensorGrading ℒ p :=
  InternalGrading.tensorProductPiece_def _ _ m

/-- Multiplication preserves the total-degree grading on `U(L) ⊗[R] U(L)`. -/
theorem mul_mem_tensorTotalDegree {m₁ m₂ : Γ} {x y : U ⊗[R] U}
    (hx : x ∈ tensorTotalDegree ℒ m₁) (hy : y ∈ tensorTotalDegree ℒ m₂) :
    x * y ∈ tensorTotalDegree ℒ (m₁ + m₂) := by
  rw [tensorTotalDegree_def] at hx hy
  refine Submodule.iSup_induction _ (motive := fun x => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hx
    (fun p x hx => ?_) (by simp) (fun _ _ h₁ h₂ => by simpa [add_mul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun x => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hx
    (fun hp x hx => ?_) (by simp) (fun _ _ h₁ h₂ => by simpa [add_mul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun y => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hy
    (fun q y hy => ?_) (by simp) (fun _ _ h₁ h₂ => by simpa [mul_add] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun y => x * y ∈ tensorTotalDegree ℒ (m₁ + m₂)) hy
    (fun hq y hy => ?_) (by simp) (fun _ _ h₁ h₂ => by simpa [mul_add] using add_mem h₁ h₂)
  rw [tensorTotalDegree_def]
  exact Submodule.mem_iSup_of_mem (p + q) <| Submodule.mem_iSup_of_mem
    (by simp only [Prod.fst_add, Prod.snd_add]; rw [add_add_add_comm, hp, hq])
    (mul_mem_tensorGrading ℒ hx hy)

/-- Comultiplication sends homogeneous elements of degree `m` into total tensor degree `m`. -/
theorem comul_mem_tensorTotalDegree {m : Γ} {a : U} (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a ∈ tensorTotalDegree ℒ m := by
  refine ((homogeneousSubmodule_le_iff ℒ m
    ((tensorTotalDegree ℒ m).comap (Bialgebra.comulAlgHom R U).toLinearMap)).mpr fun l hl => ?_) ha
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, ← hl]; clear ha a hl m
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_one, Algebra.TensorProduct.one_def]
    rw [tensorTotalDegree_def]
    exact Submodule.mem_iSup_of_mem (0, 0) <| Submodule.mem_iSup_of_mem (add_zero 0) <| by
      rw [tensorGrading_def]
      exact Submodule.apply_mem_map₂ _ (SetLike.one_mem_graded _) (SetLike.one_mem_graded _)
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul]
    refine mul_mem_tensorTotalDegree ℒ ?_ ih
    rw [Bialgebra.comulAlgHom_apply, comul_ι, tensorTotalDegree_def]
    refine add_mem
      (Submodule.mem_iSup_of_mem (b.1, 0) <| Submodule.mem_iSup_of_mem (add_zero b.1) ?_)
      (Submodule.mem_iSup_of_mem (0, b.1) <| Submodule.mem_iSup_of_mem (zero_add b.1) ?_)
    · rw [tensorGrading_def]
      exact Submodule.apply_mem_map₂ _
        (ι_mem_homogeneousSubmodule ℒ b.2.property) (SetLike.one_mem_graded _)
    · rw [tensorGrading_def]
      exact Submodule.apply_mem_map₂ _
        (SetLike.one_mem_graded _) (ι_mem_homogeneousSubmodule ℒ b.2.property)

/-- `Δ(a) - (1 ⊗ a + a ⊗ 1)` of a degree-`m` element has total tensor degree `m`. -/
theorem comul_sub_tmul_add_tmul_mem_tensorTotalDegree {m : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ m) :
    Coalgebra.comul (R := R) a - (1 ⊗ₜ[R] a + a ⊗ₜ[R] 1) ∈ tensorTotalDegree ℒ m := by
  refine sub_mem (comul_mem_tensorTotalDegree ℒ ha) ?_
  rw [tensorTotalDegree_def]
  refine add_mem
    (Submodule.mem_iSup_of_mem (0, m) <| Submodule.mem_iSup_of_mem (zero_add m) ?_)
    (Submodule.mem_iSup_of_mem (m, 0) <| Submodule.mem_iSup_of_mem (add_zero m) ?_)
  · rw [tensorGrading_def]
    exact Submodule.apply_mem_map₂ _ (SetLike.one_mem_graded _) ha
  · rw [tensorGrading_def]
    exact Submodule.apply_mem_map₂ _ ha (SetLike.one_mem_graded _)

private noncomputable def tensorComponentKer [DecidableEq Γ]
    [DirectSum.Decomposition (tensorGrading ℒ)] (p : Γ × Γ) : Submodule R (U ⊗[R] U) :=
  LinearMap.ker ((Submodule.subtype _) ∘ₗ
    (_root_.DirectSum.component R (Γ × Γ) (fun p => tensorGrading ℒ p) p) ∘ₗ
    (_root_.DirectSum.decomposeLinearEquiv (tensorGrading ℒ)).toLinearMap)

private theorem mem_tensorComponentKer [DecidableEq Γ]
    [DirectSum.Decomposition (tensorGrading ℒ)] {p : Γ × Γ} {z : U ⊗[R] U} :
    z ∈ tensorComponentKer ℒ p ↔ (decompose (tensorGrading ℒ) z p : U ⊗[R] U) = 0 :=
  LinearMap.mem_ker

/-- A tensor of total degree `m` has vanishing `(p.1, p.2)` component whenever `p.1 + p.2 ≠ m`. -/
theorem decompose_eq_zero_of_mem_tensorTotalDegree [DecidableEq Γ]
    [DirectSum.Decomposition (tensorGrading ℒ)] {m : Γ} {z : U ⊗[R] U}
    (hz : z ∈ tensorTotalDegree ℒ m) {p : Γ × Γ} (hp : p.1 + p.2 ≠ m) :
    (decompose (tensorGrading ℒ) z p : U ⊗[R] U) = 0 :=
  (mem_tensorComponentKer ℒ).mp <| (by
    rw [tensorTotalDegree_def]
    exact iSup_le fun q => iSup_le fun hq _ hw => (mem_tensorComponentKer ℒ).mpr <|
      decompose_of_mem_ne (tensorGrading ℒ) hw fun h => hp (h ▸ hq) :
      tensorTotalDegree ℒ m ≤ tensorComponentKer ℒ p) hz

end Graded

section Filtered

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ) [DecidableEq Γ] [GradedLieAlgebra ℒ]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "𝓕" => degreeFiltration ℒ d

/-- An element of the `m`-th tensor degree-filtration ideal has vanishing `(p.1, p.2)` component
whenever `d p.1 + d p.2 < m`. -/
theorem decompose_eq_zero_of_mem_tensorProduct_ideal (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    [DirectSum.Decomposition (tensorGrading ℒ)] {m : ℕ} {t : U ⊗[R] U}
    (ht : t ∈ ((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal m)
    {p : Γ × Γ} (hp : d p.1 + d p.2 < m) :
    (decompose (tensorGrading ℒ) t p : U ⊗[R] U) = 0 := by
  refine (mem_tensorComponentKer ℒ).mp <| (?_ : tensorFiltrationTail
      (fun n => ((𝓕 hneg).ideal n).restrictScalars R)
      (fun n => ((𝓕 hneg).ideal n).restrictScalars R) m ≤
      tensorComponentKer ℒ p) (((𝓕 hneg).mem_tensorProduct_ideal_iff R (𝓕 hneg)).mp ht)
  rw [tensorFiltrationTail_def]; refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  simp only [degreeFiltration_ideal, GradedAlgebra.degreeIdeal_restrictScalars,
    DirectSum.degreeTail_def, Submodule.map₂_iSup_left, Submodule.map₂_iSup_right, iSup_le_iff,
    Submodule.map₂_le]
  intro j hj i hi x hx y hy
  refine (mem_tensorComponentKer ℒ).mpr <| decompose_of_mem_ne (tensorGrading ℒ) (i := (i, j))
    (by rw [tensorGrading_def]; exact Submodule.apply_mem_map₂ (TensorProduct.mk R U U) hx hy)
    fun heq => ?_
  rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩; omega

private theorem comul_prod_mem_tensorProduct (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ∀ (l : List (Σ i, ℒ i)), (∀ a ∈ l, 0 ≤ d a.1) →
      Bialgebra.comulAlgHom R U (l.map (fun x => ι R (x.2 : L))).prod ∈
        ((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal (d (l.map Sigma.fst).sum).toNat
  | [], _ => by simp [Submodule.mem_top]
  | a :: l, hnonneg => by
    let 𝒯 := (𝓕 hneg).tensorProduct R (𝓕 hneg)
    have ha0 : 0 ≤ d a.1 := hnonneg a List.mem_cons_self
    have hl : ∀ b ∈ l, 0 ≤ d b.1 := fun b hb => hnonneg b (List.mem_cons_of_mem a hb)
    have : 0 ≤ d (l.map Sigma.fst).sum := by
      rw [map_list_sum, List.map_map]; exact List.sum_nonneg <| List.forall_mem_map.mpr hl
    have hι := ι_mem_degreeFiltration ℒ d hneg a.2.property (k := (d a.1).toNat) (by omega)
    have hhead : Bialgebra.comulAlgHom R U (ι R (a.2 : L)) ∈ 𝒯.ideal (d a.1).toNat := by
      rw [Bialgebra.comulAlgHom_apply, comul_ι]
      exact Ideal.add_mem _
        ((𝓕 hneg).tmul_mem_tensorProduct_ideal R (𝓕 hneg) (b := 0) (by omega) hι (by simp))
        ((𝓕 hneg).tmul_mem_tensorProduct_ideal R (𝓕 hneg) (a := 0) (by omega) (by simp) hι)
    have htoNat : (d ((a :: l).map Sigma.fst).sum).toNat =
        (d a.1).toNat + (d (l.map Sigma.fst).sum).toNat := by
      simp only [List.map_cons, List.sum_cons, map_add]; omega
    rw [htoNat, List.map_cons, List.prod_cons, map_mul]
    exact 𝒯.mul_mem hhead (comul_prod_mem_tensorProduct hneg l hl)

/-- Comultiplication preserves the total-degree filtration on a graded enveloping algebra. -/
theorem degreeFiltration_le_comap_comulAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (𝓕 hneg).ideal k ≤
      (((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal k).comap (Bialgebra.comulAlgHom R U) := by
  let 𝒯 := (𝓕 hneg).tensorProduct R (𝓕 hneg)
  rw [degreeFiltration_ideal_le_iff]; intro n hn a ha
  refine (Submodule.restrictScalars_mem R _ _).mp <| (homogeneousSubmodule_le_iff ℒ n
    ((𝒯.ideal k).comap (Bialgebra.comulAlgHom R U) |>.restrictScalars R)).mpr (fun l hl => ?_) ha
  rw [Submodule.restrictScalars_mem, Ideal.mem_comap]
  by_cases hnonneg : ∀ a ∈ l, 0 ≤ d a.1
  · exact 𝒯.antitone (by rw [hl]; omega) (comul_prod_mem_tensorProduct ℒ d hneg l hnonneg)
  · push Not at hnonneg; obtain ⟨b, hbl, hbneg⟩ := hnonneg
    have hb0 : (b.2 : L) = 0 := by simpa [hneg b.1 hbneg] using b.2.property
    rw [List.prod_eq_zero (List.mem_map.mpr ⟨b, hbl, by simp [hb0]⟩), map_zero]; exact zero_mem _

/-- The first degree-filtration ideal lies in the kernel of the enveloping counit. -/
theorem degreeFiltration_one_le_ker_counitAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (𝓕 hneg).ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R U) :=
  fun _ hu => (HopfIdeal.mem_augmentation R U).mp
    (HopfIdeal.mem_toIdeal.mp (degreeFiltration_le_augmentation ℒ d hneg Nat.one_pos hu))

/-- The first tensor degree-filtration ideal lies in the kernel of the tensor counit. -/
theorem tensorProduct_degreeFiltration_one_le_ker_counitAlgHom (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    ((𝓕 hneg).tensorProduct R (𝓕 hneg)).ideal 1 ≤
      RingHom.ker (Bialgebra.counitAlgHom R (U ⊗[R] U)) := by
  intro t ht
  refine ((tensorFiltrationTail_le_iff (fun n => ((𝓕 hneg).ideal n).restrictScalars R)
      (fun n => ((𝓕 hneg).ideal n).restrictScalars R)
      (P := (RingHom.ker (Bialgebra.counitAlgHom R (U ⊗[R] U))).restrictScalars R)).mpr
    fun a b hab u hu v hv => ?_) (((𝓕 hneg).mem_tensorProduct_ideal_iff R (𝓕 hneg)).mp ht)
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, Bialgebra.counitAlgHom_apply,
    TensorProduct.counit_tmul]
  have hzero {w : U} (hw : w ∈ (𝓕 hneg).ideal 1) : Coalgebra.counit (R := R) w = 0 := by
    simpa [Bialgebra.counitAlgHom_apply] using degreeFiltration_one_le_ker_counitAlgHom ℒ d hneg hw
  rcases Nat.lt_or_ge 0 a with ha | ha
  · simp [hzero ((𝓕 hneg).antitone ha hu)]
  · simp [hzero ((𝓕 hneg).antitone (by omega) hv)]

end Filtered

end TauCeti.UniversalEnvelopingAlgebra
