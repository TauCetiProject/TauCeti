/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Borcherds
import TauCeti.Algebra.Vertex.FormalDistribution

/-!
# Reconstruction of formal vertex algebras from generating fields

Given a commutative ring `R`, an `R`-module `V` with unique division by positive integers
(`HasUniqueDiv V`), a vacuum `vac : V`, an endomorphism `T : Module.End R V` killing `vac`, and
pairwise local, `T`-covariant fields `F : ι → VertexOperator R V` whose modes generate `V` from
`vac`, there is a unique `TauCeti.FormalVertexAxioms R V` with vacuum `vac`, translation `T`, and
`Y((F i)₍₋₁₎ vac, z) = F i` for every `i`.

## Main definitions and results

* `TauCeti.FormalVertexAxioms.ofGeneratingFields`: the reconstructed formal vertex algebra on `V`,
  with simp laws `ofGeneratingFields_vacuum`, `ofGeneratingFields_translation`,
  `ofGeneratingFields_field_ncoeff_neg_one_apply`, and `ofGeneratingFields_field_eq`.
* `TauCeti.FormalVertexAxioms.eq_ofGeneratingFields`,
  `TauCeti.FormalVertexAxioms.existsUnique_of_generatingFields`: uniqueness and existence-uniqueness
  for the reconstruction theorem.

## References

* V. Kac, *Introduction to vertex algebras, Poisson vertex algebras, and integrable Hamiltonian PDE*
  (arXiv:1512.00821v2), Theorem 1.1; *Vertex Algebras for Beginners*, 2nd ed., §4.5 (Theorem 4.5).
* E. Frenkel, V. Kac, A. Radul, W. Wang, *W_{1+∞} and W(gl_N) with central charge N*, Comm. Math.
  Phys. 170 (1995), 337–357.
* P. Goddard, *Meromorphic conformal field theory*, Adv. Ser. Math. Phys. 7 (1989), 556–587.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.9 and §3.2.1.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Proposition 3.12.
-/

public section

noncomputable section

open scoped VertexOperator
open VertexOperator

namespace TauCeti.FormalVertexAxioms

section GeneratedFields

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private inductive GenDepth (F : ι → VertexOperator R V) : ℕ → VertexOperator R V → Prop
  | zero (d : ℕ) : GenDepth F d 0
  | id (d : ℕ) : GenDepth F d (VertexOperator.id R V)
  | gen (d : ℕ) (i : ι) : GenDepth F d (F i)
  | mono {d : ℕ} {A} : GenDepth F d A → GenDepth F (d + 1) A
  | add {d : ℕ} {A B} : GenDepth F d A → GenDepth F d B → GenDepth F (d + 1) (A + B)
  | smul {d : ℕ} (r : R) {A} : GenDepth F d A → GenDepth F (d + 1) (r • A)
  | derivative {d : ℕ} {A} : GenDepth F d A → GenDepth F (d + 1) (derivative A)
  | nthProduct {d : ℕ} (n : ℤ) {A B} :
      GenDepth F d A → GenDepth F d B → GenDepth F (d + 1) (nthProduct n A B)

private theorem genDepth_mono_le {F : ι → VertexOperator R V} {d₁ d₂ : ℕ} (hle : d₁ ≤ d₂)
    {A : VertexOperator R V} (hA : GenDepth F d₁ A) : GenDepth F d₂ A := by
  induction hle with | refl => exact hA | step _ ih => exact .mono ih

private theorem genDepth_lie_translation {T : Module.End R V} {F : ι → VertexOperator R V}
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]]) :
    ∀ {d : ℕ} {B : VertexOperator R V}, GenDepth F d B →
      ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]] := fun hB ↦ by
  induction hB with
  | zero => intro _; simp
  | id => intro m; rcases eq_or_ne m (-1) with rfl | hm <;> simp [Ring.lie_def, ncoeff_id, *]
  | gen _ i => exact hcov i
  | mono _ ih => exact ih
  | add _ _ ihA ihB => intro m; simp only [map_add, Pi.add_apply, lie_add, ihA, ihB]
  | smul r _ ihA => intro m; simp only [map_smul, Pi.smul_apply, lie_smul, ihA]
  | derivative _ ihA => intro m; simpa only [hasseDeriv_one] using lie_ncoeff_hasseDeriv ihA 1 m
  | nthProduct n _ _ ihA ihB => exact lie_ncoeff_nthProduct ihA ihB n

private theorem genDepth_step_isLocalOfOrder {F : ι → VertexOperator R V} {d : ℕ}
    (ih : ∀ {X Y : VertexOperator R V}, GenDepth F d X → GenDepth F d Y →
      ∃ N : ℕ, X.IsLocalOfOrder Y N)
    {A C : VertexOperator R V} (hA : GenDepth F (d + 1) A)
    (hCA : ∀ {X : VertexOperator R V}, GenDepth F d X → ∃ N : ℕ, X.IsLocalOfOrder C N) :
    ∃ N : ℕ, A.IsLocalOfOrder C N := by
  cases hA with
  | zero => exact ⟨0, IsLocalOfOrder.zero_left C⟩
  | id => exact ⟨0, IsLocalOfOrder.id_left C⟩
  | gen _ i => exact hCA (.gen d i)
  | mono hA₀ => exact hCA hA₀
  | add hA₁ hA₂ => obtain ⟨_, h₁⟩ := hCA hA₁; obtain ⟨_, h₂⟩ := hCA hA₂; exact ⟨_, h₁.add_left h₂⟩
  | smul r hA₀ => obtain ⟨_, h⟩ := hCA hA₀; exact ⟨_, h.smul_left r⟩
  | derivative hA₀ => obtain ⟨_, h⟩ := hCA hA₀; exact ⟨_, h.derivative_left⟩
  | nthProduct n hA₁ hA₂ =>
    obtain ⟨_, h₁⟩ := ih hA₁ hA₂; obtain ⟨_, h₂⟩ := hCA hA₂; obtain ⟨_, h₃⟩ := hCA hA₁
    exact ⟨_, h₁.nthProduct_left h₂ h₃ n⟩

private theorem genDepth_isLocalOfOrder {F : ι → VertexOperator R V}
    (hloc : ∀ i j, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N) (d : ℕ) :
    ∀ {A B : VertexOperator R V}, GenDepth F d A → GenDepth F d B →
      ∃ N : ℕ, A.IsLocalOfOrder B N := by
  induction d with
  | zero =>
    intro A B hA hB
    cases hA <;> cases hB <;> first
      | exact ⟨0, IsLocalOfOrder.zero_left _⟩ | exact ⟨0, IsLocalOfOrder.id_left _⟩
      | exact ⟨0, IsLocalOfOrder.zero_right _⟩ | exact ⟨0, IsLocalOfOrder.id_right _⟩
      | exact hloc _ _
  | succ d ih =>
    have half : ∀ {A C}, GenDepth F (d + 1) A → GenDepth F d C → ∃ N, A.IsLocalOfOrder C N :=
      fun hA hC ↦ genDepth_step_isLocalOfOrder ih hA (fun hX ↦ ih hX hC)
    exact fun _ _ hA hB ↦ genDepth_step_isLocalOfOrder ih hA fun hX ↦
      let ⟨N, h⟩ := half hB hX; ⟨N, h.symm⟩

private def generatedFields (F : ι → VertexOperator R V) : Submodule R (VertexOperator R V) where
  carrier := {B | ∃ d : ℕ, GenDepth F d B}
  zero_mem' := ⟨0, .zero 0⟩
  add_mem' := fun ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ ↦ ⟨max d₁ d₂ + 1,
    .add (genDepth_mono_le (le_max_left _ _) h₁) (genDepth_mono_le (le_max_right _ _) h₂)⟩
  smul_mem' := fun r _ ⟨d, h⟩ ↦ ⟨d + 1, .smul r h⟩

private theorem generatedFields_isLocalOfOrder {F : ι → VertexOperator R V}
    (hloc : ∀ i j, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N) {A B : VertexOperator R V} :
    A ∈ generatedFields F → B ∈ generatedFields F → ∃ N : ℕ, A.IsLocalOfOrder B N :=
  fun ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ ↦ genDepth_isLocalOfOrder hloc (max d₁ d₂)
    (genDepth_mono_le (le_max_left _ _) h₁) (genDepth_mono_le (le_max_right _ _) h₂)

private def evalVacLinearMap (vac : V) (F : ι → VertexOperator R V) : generatedFields F →ₗ[R] V :=
  { toFun B := (B.1[[-1]]) vac, map_add' _ _ := by simp, map_smul' _ _ := by simp }

end GeneratedFields

section Reconstruction

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V] [HasUniqueDiv V]
variable (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
  (hT : T vac = 0)
  (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
  (hloc : ∀ i j, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
  (hgen : ∀ W : Submodule R V, vac ∈ W →
    (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
include hT hcov hloc hgen

private theorem eq_zero_of_mem_generatedFields {B : VertexOperator R V} (hB : B ∈ generatedFields F)
    (hker : (B[[-1]]) vac = 0) : B = 0 := by
  have hcovB := let ⟨_, hd⟩ := hB; genDepth_lie_translation hcov hd
  have hvac (m : ℤ) : (B[[m]]) vac = 0 := by
    rcases le_or_gt 0 m with hm | hm
    · exact ncoeff_apply_eq_zero_of_lie_of_nonneg hT hcovB hm
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
      exact (nsmul_right_inj k.factorial_ne_zero).mp <| by
        rw [factorial_smul_ncoeff_neg_succ_apply_of_lie hT hcovB k, hker, map_zero, smul_zero]
  have hW : (⨅ m : ℤ, LinearMap.ker (B[[m]])) = ⊤ :=
    hgen _ ((Submodule.mem_iInf _).mpr fun m ↦ LinearMap.mem_ker.mpr (hvac m)) fun i n v hv ↦
      (Submodule.mem_iInf _).mpr fun m ↦ LinearMap.mem_ker.mpr <|
        let ⟨_, hlocBi⟩ := generatedFields_isLocalOfOrder hloc hB ⟨0, .gen 0 i⟩
        hlocBi.ncoeff_apply_ncoeff_apply_eq_zero
          (fun p ↦ LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hv p)) m n
  exact ext_ncoeff fun m ↦ LinearMap.ker_eq_top.mp (iInf_eq_top.mp hW m)

private theorem evalVacLinearMap_bijective : Function.Bijective (evalVacLinearMap vac F) := by
  refine ⟨fun x y hxy ↦ Subtype.ext <| sub_eq_zero.mp <|
      eq_zero_of_mem_generatedFields vac T F hT hcov hloc hgen (sub_mem x.2 y.2)
        (by simpa [evalVacLinearMap, sub_eq_zero] using hxy), ?_⟩
  rw [← LinearMap.range_eq_top]
  refine hgen _ ⟨⟨VertexOperator.id R V, ⟨0, .id 0⟩⟩, by simp [evalVacLinearMap]⟩
    fun i n v ⟨⟨B, ⟨d, hd⟩⟩, hBv⟩ ↦ ⟨⟨nthProduct n (F i) B,
      ⟨d + 1, .nthProduct n (genDepth_mono_le (Nat.zero_le d) (.gen 0 i)) hd⟩⟩, ?_⟩
  rw [← hBv]; exact ncoeff_neg_one_nthProduct_apply
    (fun _ hm ↦ ncoeff_apply_eq_zero_of_lie_of_nonneg hT (hcov i) hm)
    (fun _ hm ↦ ncoeff_apply_eq_zero_of_lie_of_nonneg hT (genDepth_lie_translation hcov hd) hm) n

private def evalVacEquiv : generatedFields F ≃ₗ[R] V :=
  LinearEquiv.ofBijective (evalVacLinearMap vac F)
    (evalVacLinearMap_bijective vac T F hT hcov hloc hgen)

/-- **Reconstruction of a formal vertex algebra from generating fields.** Given `vac : V` killed by
`T : Module.End R V` on an `R`-module `V` with unique division by positive integers, and pairwise
local, `T`-covariant fields `F i` whose mode iterates generate `V` from `vac`, this constructs the
unique `TauCeti.FormalVertexAxioms R V` with vacuum `vac`, translation `T`, and
`Y((F i)₍₋₁₎ vac, z) = F i`. -/
def ofGeneratingFields : FormalVertexAxioms R V :=
  let e := evalVacEquiv vac T F hT hcov hloc hgen
  let Y : V →ₗ[R] VertexOperator R V := (generatedFields F).subtype.comp e.symm.toLinearMap
  have he (B : generatedFields F) : e B = (B.1[[-1]]) vac := rfl
  have hY_mem (a : V) : Y a ∈ generatedFields F := (e.symm a).2
  have hY_cov (a : V) := let ⟨_, hd⟩ := hY_mem a; genDepth_lie_translation hcov hd
  have hY_eval (B : generatedFields F) : Y ((B.1[[-1]]) vac) = B.1 := by
    rw [← he B]; exact congrArg Subtype.val (e.symm_apply_apply B)
  have heval_Y (a : V) : ((Y a)[[-1]]) vac = a := by
    simpa only [Y, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_toLinearMap,
      ← he] using e.apply_symm_apply a
  { field := Y, vacuum := vac, translation := T, translation_vacuum := hT
    ncoeff_field_vacuum := fun n ↦ by
      rw [show Y vac = VertexOperator.id R V by
        simpa only [ncoeff_neg_one_id, one_apply_eq_self] using
          hY_eval ⟨VertexOperator.id R V, ⟨0, .id 0⟩⟩, ncoeff_id]
    ncoeff_field_apply_vacuum_of_nonneg := fun a _ hn ↦
      ncoeff_apply_eq_zero_of_lie_of_nonneg hT (hY_cov a) hn
    ncoeff_neg_one_field_apply_vacuum := heval_Y
    field_translation := fun a ↦ by
      have hrec := apply_ncoeff_apply_of_lie hT (hY_cov a) (-1); rw [heval_Y a] at hrec
      have h := hY_eval ⟨derivative (Y a), let ⟨d, hd⟩ := hY_mem a; ⟨d + 1, .derivative hd⟩⟩
      dsimp only at h; rwa [ncoeff_derivative, LinearMap.smul_apply, ← hrec] at h
    lie_translation_ncoeff := fun a n ↦ hY_cov a n
    exists_isLocalOfOrder := fun a b ↦ generatedFields_isLocalOfOrder hloc (hY_mem a) (hY_mem b) }

variable {vac T F hT hcov hloc hgen}

/-- The vacuum vector of `ofGeneratingFields` is `vac`. -/
@[simp] theorem ofGeneratingFields_vacuum :
    (ofGeneratingFields vac T F hT hcov hloc hgen).vacuum = vac := by rfl

/-- The translation operator of `ofGeneratingFields` is `T`. -/
@[simp] theorem ofGeneratingFields_translation :
    (ofGeneratingFields vac T F hT hcov hloc hgen).translation = T := by rfl

/-- Each generating field `F i` is recovered as the state–field operator of `(F i)₍₋₁₎ vac`. -/
@[simp] theorem ofGeneratingFields_field_ncoeff_neg_one_apply (i : ι) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).field (((F i)[[-1]]) vac) = F i := by
  exact congrArg Subtype.val <| (evalVacEquiv vac T F hT hcov hloc hgen).symm_apply_apply
    ⟨F i, ⟨0, .gen 0 i⟩⟩

/-- Convenience form of generator recovery when `((F i)[[-1]]) vac = a` is given. -/
theorem ofGeneratingFields_field_eq {i : ι} {a : V} (ha : ((F i)[[-1]]) vac = a) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).field a = F i := by
  rw [← ha, ofGeneratingFields_field_ncoeff_neg_one_apply]

/-- Any formal vertex algebra with vacuum `vac` whose state–field map recovers each generator
`F i` at `(F i)₍₋₁₎ vac` coincides with `ofGeneratingFields`. -/
theorem eq_ofGeneratingFields {A : FormalVertexAxioms R V} (hvac : A.vacuum = vac)
    (hF : ∀ i, A.field (((F i)[[-1]]) vac) = F i) :
    A = ofGeneratingFields vac T F hT hcov hloc hgen := by
  let A₀ := ofGeneratingFields vac T F hT hcov hloc hgen
  refine FormalVertexAxioms.ext <| LinearMap.eqLocus_eq_top.mp <|
    hgen (LinearMap.eqLocus A.field A₀.field) ?_ fun i n v hv ↦ ?_
  · rw [LinearMap.mem_eqLocus, ← hvac, A.field_vacuum, hvac,
      ← ofGeneratingFields_vacuum (hT := hT) (hcov := hcov) (hloc := hloc) (hgen := hgen),
      A₀.field_vacuum]
  · rw [LinearMap.mem_eqLocus, ← hF i, A.field_ncoeff_apply, hF i, LinearMap.mem_eqLocus.mp hv,
      ← ofGeneratingFields_field_ncoeff_neg_one_apply (hT := hT) (hcov := hcov) (hloc := hloc)
        (hgen := hgen) i, ← A₀.field_ncoeff_apply, ofGeneratingFields_field_ncoeff_neg_one_apply]

variable (vac T F hT hcov hloc hgen)

/-- **Existence and uniqueness in the reconstruction theorem.** On an `R`-module `V` with unique
division by positive integers, there is a unique formal vertex algebra with vacuum `vac`,
translation `T`, and `Y((F i)₍₋₁₎ vac, z) = F i` for every `i`. -/
theorem existsUnique_of_generatingFields :
    ∃! A : FormalVertexAxioms R V,
      A.vacuum = vac ∧ A.translation = T ∧ ∀ i, A.field (((F i)[[-1]]) vac) = F i :=
  ⟨ofGeneratingFields vac T F hT hcov hloc hgen,
    ⟨ofGeneratingFields_vacuum, ofGeneratingFields_translation,
      ofGeneratingFields_field_ncoeff_neg_one_apply⟩,
    fun _ ⟨hvac, _, hF⟩ ↦ eq_ofGeneratingFields hvac hF⟩

end Reconstruction

end TauCeti.FormalVertexAxioms
