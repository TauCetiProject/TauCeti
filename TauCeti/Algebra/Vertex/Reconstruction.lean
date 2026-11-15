/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Borcherds

/-!
# Reconstruction and extension of formal vertex algebras

Given an additive-torsion-free `R`-module `V`, a vacuum vector `vac : V`, a translation endomorphism
`T : Module.End R V` killing `vac`, and an indexed family of pairwise mutually local, `T`-covariant
fields `F : ι → VertexOperator R V` whose modes generate `V` from `vac`, there exists a unique
formal vertex algebra structure `A : TauCeti.FormalVertexAxioms R V` with vacuum `vac` and
`A.field (((F i)[[-1]]) vac) = F i` for all `i` (necessarily with `A.translation = T`).

Notice that vacuum regularity `(F i)₍ₘ₎ vac = 0` for `m ≥ 0` need not be assumed: under
`[IsAddTorsionFree V]` (automatic on any `ℚ`-module via `HasUniqueDiv.of_module_rat V`), it follows
automatically from `T vac = 0`, translation covariance, and Laurent lower truncation
(`VertexOperator.ncoeff_apply_eq_zero_of_lie_derivative`). Likewise, the generation hypothesis asks
only that no proper `R`-submodule of `V` containing `vac` is stable under all modes `(F i)₍ₙ₎`
(`n : ℤ`); in particular it holds whenever `V` is spanned over `R` by negative-mode monomials
`(F i₁)₍₋ₖ₁₋₁₎ ⋯ (F iᵣ)₍₋ₖᵣ₋₁₎ vac` (`TauCeti.FormalVertexAxioms.ofNegModeGenerators`).

The proof constructs the smallest `R`-submodule of `VertexOperator R V` containing `idField` and the
generators `F i` and closed under `derivative` and left `n`-th products `nthProduct n (F i)`. Dong's
lemma makes every pair of fields in this submodule mutually local, and vacuum evaluation
`B ↦ B₍₋₁₎ vac` gives an `R`-linear isomorphism onto `V` whose inverse defines `field`.

## Main definitions

* `TauCeti.FormalVertexAxioms.ofGenerators`: reconstructs a formal vertex algebra from pairwise
  mutually local, translation-covariant generating fields.
* `TauCeti.FormalVertexAxioms.ofNegModeGenerators`: specialization when `V` is generated from `vac`
  by negative modes `(F i)₍₋ₖ₋₁₎` (`k : ℕ`) alone (the PBW setting of Kac's Theorem 4.5).

## Main results

* `TauCeti.FormalVertexAxioms.ofGenerators_field_ncoeff_neg_one_vacuum`,
  `TauCeti.FormalVertexAxioms.ofGenerators_field_eq`: the reconstructed state–field map sends
  `((F i)[[-1]]) vac` to `F i`.
* `TauCeti.FormalVertexAxioms.eq_of_vacuum_eq_of_field_eq`,
  `TauCeti.FormalVertexAxioms.existsUnique_of_isLocalOfOrder`: uniqueness and existence-and-
  uniqueness of the formal vertex algebra extending `F`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.5 (Theorem 4.5, Existence theorem).
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., Theorem 2.3.11 and
  Theorem 3.2.1 (Reconstruction theorem).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Theorem 3.2.10.
* A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum fields*, MSJ
  Memoirs 4 (1999), §3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### The submodule of generated fields -/

private inductive IsGenField (F : ι → VertexOperator R V) : VertexOperator R V → Prop
  | zero : IsGenField F 0
  | id : IsGenField F idField
  | gen (i : ι) : IsGenField F (F i)
  | add {B₁ B₂} : IsGenField F B₁ → IsGenField F B₂ → IsGenField F (B₁ + B₂)
  | smul (r : R) {B} : IsGenField F B → IsGenField F (r • B)
  | deriv {B} : IsGenField F B → IsGenField F (derivative B)
  | nth (n : ℤ) (i : ι) {B} : IsGenField F B → IsGenField F (nthProduct n (F i) B)

private def genSubmodule (F : ι → VertexOperator R V) : Submodule R (VertexOperator R V) where
  carrier := {B | IsGenField F B}
  zero_mem' := .zero
  add_mem' := .add
  smul_mem' := .smul

private theorem isGenField_lie {T : Module.End R V} {F : ι → VertexOperator R V}
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    {B : VertexOperator R V} (hB : IsGenField F B) :
    ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]] := by
  induction hB with
  | zero => intro m; simp [Ring.lie_def]
  | id =>
    intro m
    rw [derivative_idField, ncoeff_idField]
    split_ifs <;> simp [Ring.lie_def]
  | gen i => exact hT i
  | add _ _ ih₁ ih₂ =>
    intro m
    simp only [map_add, Pi.add_apply, ← ih₁ m, ← ih₂ m, Ring.lie_def, mul_add, add_mul]
    abel
  | smul r _ ih =>
    intro m
    simp only [map_smul, Pi.smul_apply, ← ih m, Ring.lie_def, mul_smul_comm, smul_mul_assoc,
      smul_sub]
  | deriv _ ih =>
    intro m
    simpa only [hasseDeriv_one] using lie_ncoeff_hasseDeriv T ih 1 m
  | nth n i _ ih => exact lie_ncoeff_nthProduct T (hT i) ih n

private theorem isGenField_local_gen {F : ι → VertexOperator R V}
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    {B : VertexOperator R V} (hB : IsGenField F B) :
    ∀ j : ι, ∃ N : ℕ, B.IsLocalOfOrder (F j) N := by
  induction hB with
  | zero => exact fun j ↦ ⟨0, isLocalOfOrder_zero_left (F j) 0⟩
  | id => exact fun j ↦ ⟨0, isLocalOfOrder_idField_left (F j) 0⟩
  | gen i => exact hLoc i
  | add _ _ ih₁ ih₂ =>
    intro j
    obtain ⟨N₁, h₁⟩ := ih₁ j
    obtain ⟨N₂, h₂⟩ := ih₂ j
    exact ⟨max N₁ N₂, (h₁.mono (le_max_left N₁ N₂)).add_left (h₂.mono (le_max_right N₁ N₂))⟩
  | smul r _ ih =>
    intro j
    obtain ⟨N, h⟩ := ih j
    exact ⟨N, h.smul_left r⟩
  | deriv _ ih =>
    intro j
    obtain ⟨N, h⟩ := ih j
    exact ⟨N + 1, h.derivative_left⟩
  | nth n i _ ih =>
    intro j
    obtain ⟨N₁, h₁⟩ := ih i
    obtain ⟨N₂, h₂⟩ := hLoc i j
    obtain ⟨N₃, h₃⟩ := ih j
    exact ⟨_, h₁.symm.nthProduct_left h₂ h₃ n⟩

private theorem isGenField_local {F : ι → VertexOperator R V}
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    {C : VertexOperator R V} (hC : IsGenField F C) :
    ∀ {B : VertexOperator R V}, IsGenField F B → ∃ N : ℕ, B.IsLocalOfOrder C N := by
  induction hC with
  | zero => exact fun _ ↦ ⟨0, isLocalOfOrder_zero_right _ 0⟩
  | id => exact fun _ ↦ ⟨0, isLocalOfOrder_idField_right _ 0⟩
  | gen j => exact fun hB ↦ isGenField_local_gen hLoc hB j
  | add _ _ ih₁ ih₂ =>
    intro B hB
    obtain ⟨N₁, h₁⟩ := ih₁ hB
    obtain ⟨N₂, h₂⟩ := ih₂ hB
    exact ⟨max N₁ N₂, (h₁.mono (le_max_left N₁ N₂)).add_right (h₂.mono (le_max_right N₁ N₂))⟩
  | smul r _ ih =>
    intro B hB
    obtain ⟨N, h⟩ := ih hB
    exact ⟨N, h.smul_right r⟩
  | deriv _ ih =>
    intro B hB
    obtain ⟨N, h⟩ := ih hB
    exact ⟨N + 1, h.derivative_right⟩
  | nth n i _ ih =>
    intro B hB
    obtain ⟨N₁, h₁⟩ := ih (.gen i)
    obtain ⟨N₂, h₂⟩ := isGenField_local_gen hLoc hB i
    obtain ⟨N₃, h₃⟩ := ih hB
    exact ⟨_, h₂.nthProduct_right h₃ h₁ n⟩

/-! ### Vacuum evaluation equivalence -/

private theorem ncoeff_apply_mode_eq_zero_of_isLocalOfOrder
    {B G : VertexOperator R V} {N : ℕ} (hLoc : B.IsLocalOfOrder G N)
    {v : V} (hv : ∀ m : ℤ, (B[[m]]) v = 0) :
    ∀ (n m : ℤ), (B[[m]]) ((G[[n]]) v) = 0 := by
  obtain ⟨K, hK⟩ := G.exists_forall_ncoeff_apply_eq_zero v
  have hdown (d : ℕ) : ∀ (n : ℤ), (K : ℤ) - d ≤ n → ∀ m : ℤ, (B[[m]]) ((G[[n]]) v) = 0 := by
    induction d with
    | zero =>
      intro n hn m
      rw [hK n (by omega), map_zero]
    | succ d ih =>
      intro n hn m
      have h0 := LinearMap.congr_fun (isLocalOfOrder_iff.mp hLoc (m - N) n) v
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
        mul_apply_eq_comp, LinearMap.zero_apply, hv, map_zero, sub_zero] at h0
      rw [sum_eq_single (N, 0) (fun ij hij hne ↦ ?_) (by simp)] at h0
      · simpa using h0
      · have hj : ij.2 ≠ 0 := fun hj ↦
          hne (Prod.ext (by simpa [hj] using mem_antidiagonal.mp hij) hj)
        rw [ih (n + ij.2) (by omega) (m - N + ij.1), smul_zero, smul_zero]
  exact fun n m ↦ hdown ((K : ℤ) - n).toNat n (by omega) m

private theorem eq_zero_of_isGenField_of_ncoeff_neg_one_eq_zero [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤)
    {B : VertexOperator R V} (hB : IsGenField F B) (h0 : (B[[-1]]) vac = 0) :
    B = 0 := by
  have hBT := isGenField_lie hT hB
  let P : Submodule R V :=
    { carrier := {v | ∀ m : ℤ, (B[[m]]) v = 0}
      zero_mem' m := map_zero _
      add_mem' ha hb m := by rw [map_add, ha m, hb m, add_zero]
      smul_mem' r a ha m := by rw [map_smul, ha m, smul_zero] }
  have hvacP : vac ∈ P := fun m ↦ by
    rcases le_or_gt 0 m with hm | hm
    · exact ncoeff_apply_eq_zero_of_lie_derivative hvac hBT hm
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
      refine (nsmul_eq_zero_iff_right k.factorial_ne_zero).mp ?_
      rw [factorial_smul_ncoeff_apply_of_lie_derivative hvac hBT k, h0, map_zero]
  have hstepP (i : ι) (n : ℤ) (v : V) (hv : v ∈ P) : ((F i)[[n]]) v ∈ P := by
    obtain ⟨N, hN⟩ := isGenField_local_gen hLoc hB i
    exact ncoeff_apply_mode_eq_zero_of_isLocalOfOrder hN hv n
  have htop := hGen P hvacP hstepP
  refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
  have hv : v ∈ P := htop.symm ▸ Submodule.mem_top
  exact hv m

private def evalVac (vac : V) (F : ι → VertexOperator R V) : genSubmodule F →ₗ[R] V where
  toFun B := (B.1[[-1]]) vac
  map_add' B₁ B₂ := by simp
  map_smul' r B := by simp

private def evalVacEquiv [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤) :
    genSubmodule F ≃ₗ[R] V := by
  refine LinearEquiv.ofBijective (evalVac vac F) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro B hB
    exact Subtype.ext
      (eq_zero_of_isGenField_of_ncoeff_neg_one_eq_zero hvac hT hLoc hGen B.2 hB)
  · rw [← LinearMap.range_eq_top]
    refine hGen (LinearMap.range (evalVac vac F)) ⟨⟨idField, .id⟩, by simp [evalVac]⟩ ?_
    rintro i n _ ⟨B, rfl⟩
    refine ⟨⟨nthProduct n (F i) B.1, .nth n i B.2⟩, ?_⟩
    exact ncoeff_neg_one_nthProduct_apply n
      (fun _ hm ↦ ncoeff_apply_eq_zero_of_lie_derivative hvac (hT i) hm)
      (fun _ hm ↦ ncoeff_apply_eq_zero_of_lie_derivative hvac (isGenField_lie hT B.2) hm)

/-! ### Main reconstruction theorems -/

/-- **Reconstruction of a formal vertex algebra from generating fields.** Given an additive-
torsion-free `R`-module `V`, a vacuum `vac : V`, an endomorphism `T : Module.End R V` killing
`vac`, and pairwise mutually local, `T`-covariant fields `F i` whose modes generate `V` from `vac`,
constructs the formal vertex algebra on `V` with `vacuum = vac`, `translation = T`, and
`field (((F i)[[-1]]) vac) = F i`. -/
def ofGenerators [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤) :
    FormalVertexAxioms R V :=
  let e := evalVacEquiv hvac hT hLoc hGen
  { field := (genSubmodule F).subtype ∘ₗ e.symm.toLinearMap
    vacuum := vac
    translation := T
    translation_vacuum := hvac
    ncoeff_field_vacuum n := by
      have hid : e.symm vac = ⟨idField, .id⟩ :=
        e.injective (by simp [e, evalVacEquiv, evalVac])
      simp [hid, ncoeff_idField]
    ncoeff_field_apply_vacuum_of_nonneg a n hn :=
      ncoeff_apply_eq_zero_of_lie_derivative hvac (isGenField_lie hT (e.symm a).2) hn
    ncoeff_neg_one_field_apply_vacuum a := e.apply_symm_apply a
    field_translation a := by
      have hTa : e ⟨derivative (e.symm a).1, .deriv (e.symm a).2⟩ = T a := by
        have h := LinearMap.congr_fun (isGenField_lie hT (e.symm a).2 (-1)) vac
        rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, hvac,
          map_zero, sub_zero] at h
        exact h.symm.trans (congrArg T (e.apply_symm_apply a))
      exact congrArg Subtype.val (e.symm_apply_eq.mpr hTa.symm)
    lie_translation_ncoeff a n := isGenField_lie hT (e.symm a).2 n
    exists_isLocalOfOrder a b := isGenField_local hLoc (e.symm b).2 (e.symm a).2 }

/-- The vacuum of `ofGenerators` is `vac`. -/
@[simp]
theorem ofGenerators_vacuum [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤) :
    (ofGenerators hvac hT hLoc hGen).vacuum = vac := (rfl)

/-- The translation operator of `ofGenerators` is `T`. -/
@[simp]
theorem ofGenerators_translation [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤) :
    (ofGenerators hvac hT hLoc hGen).translation = T := (rfl)

/-- The reconstructed state–field map sends each generating state `((F i)[[-1]]) vac` to `F i`. -/
@[simp]
theorem ofGenerators_field_ncoeff_neg_one_vacuum [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤) (i : ι) :
    (ofGenerators hvac hT hLoc hGen).field (((F i)[[-1]]) vac) = F i := by
  let e := evalVacEquiv hvac hT hLoc hGen
  have hi : e.symm (((F i)[[-1]]) vac) = ⟨F i, .gen i⟩ :=
    e.injective (e.apply_symm_apply (((F i)[[-1]]) vac))
  exact congrArg Subtype.val hi

/-- Convenience form of `ofGenerators_field_ncoeff_neg_one_vacuum` when a state `a` is identified
with `((F i)[[-1]]) vac`. -/
theorem ofGenerators_field_eq [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤)
    {i : ι} {a : V} (ha : ((F i)[[-1]]) vac = a) :
    (ofGenerators hvac hT hLoc hGen).field a = F i := by
  rw [← ha, ofGenerators_field_ncoeff_neg_one_vacuum]

/-- Any formal vertex algebra on `V` with vacuum `vac` and `A.field (((F i)[[-1]]) vac) = F i`
coincides with `ofGenerators` (in particular `A.translation = T` is forced). -/
theorem eq_of_vacuum_eq_of_field_eq [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤)
    (A : FormalVertexAxioms R V) (hAvac : A.vacuum = vac)
    (hAF : ∀ i : ι, A.field (((F i)[[-1]]) vac) = F i) :
    A = ofGenerators hvac hT hLoc hGen := by
  let A₀ := ofGenerators hvac hT hLoc hGen
  refine FormalVertexAxioms.ext ?_
  have hvacEq : A.field vac = A₀.field vac := by
    refine ext_ncoeff fun n ↦ ?_
    have h₁ := A.ncoeff_field_vacuum n
    have h₂ := A₀.ncoeff_field_vacuum n
    rwa [hAvac, ← h₂] at h₁
  have htop := hGen (LinearMap.eqLocus A.field A₀.field) hvacEq fun i n v hv ↦ by
    change A.field (((F i)[[n]]) v) = A₀.field (((F i)[[n]]) v)
    have hv' : A.field v = A₀.field v := hv
    have h₁ : A.field (((F i)[[n]]) v) = nthProduct n (F i) (A.field v) := by
      simpa only [hAF i] using A.field_ncoeff_apply (((F i)[[-1]]) vac) v n
    have h₂ : A₀.field (((F i)[[n]]) v) = nthProduct n (F i) (A₀.field v) := by
      simpa only [A₀, ofGenerators_field_ncoeff_neg_one_vacuum] using
        A₀.field_ncoeff_apply (((F i)[[-1]]) vac) v n
    rw [h₁, h₂, hv']
  exact LinearMap.ext fun v ↦ LinearMap.mem_eqLocus.mp (htop.symm ▸ Submodule.mem_top)

/-- **Existence and uniqueness** of the formal vertex algebra extending a generating family of
pairwise local, translation-covariant fields. -/
theorem existsUnique_of_isLocalOfOrder [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ P, ((F i)[[n]]) v ∈ P) → P = ⊤) :
    ∃! A : FormalVertexAxioms R V,
      A.vacuum = vac ∧ ∀ i : ι, A.field (((F i)[[-1]]) vac) = F i :=
  ⟨ofGenerators hvac hT hLoc hGen,
    ⟨rfl, ofGenerators_field_ncoeff_neg_one_vacuum hvac hT hLoc hGen⟩,
    fun A ⟨hAvac, hAF⟩ ↦ eq_of_vacuum_eq_of_field_eq hvac hT hLoc hGen A hAvac hAF⟩

/-- **Kac's negative-mode Reconstruction Theorem (Theorem 4.5).** When `V` is generated from `vac`
by negative modes `(F i)₍₋ₖ₋₁₎` (`k : ℕ`) alone (the PBW setting of Fock and affine Verma modules),
every submodule containing `vac` and closed under all modes is `⊤`, yielding a formal vertex algebra
extending `F`. -/
def ofNegModeGenerators [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hNegGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (k : ℕ), ∀ v ∈ P, ((F i)[[-(k : ℤ) - 1]]) v ∈ P) → P = ⊤) :
    FormalVertexAxioms R V :=
  ofGenerators hvac hT hLoc fun P hP hall ↦
    hNegGen P hP fun i k v hv ↦ hall i (-(k : ℤ) - 1) v hv

/-- The vacuum of `ofNegModeGenerators` is `vac`. -/
@[simp]
theorem ofNegModeGenerators_vacuum [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hNegGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (k : ℕ), ∀ v ∈ P, ((F i)[[-(k : ℤ) - 1]]) v ∈ P) → P = ⊤) :
    (ofNegModeGenerators hvac hT hLoc hNegGen).vacuum = vac := (rfl)

/-- The translation operator of `ofNegModeGenerators` is `T`. -/
@[simp]
theorem ofNegModeGenerators_translation [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hNegGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (k : ℕ), ∀ v ∈ P, ((F i)[[-(k : ℤ) - 1]]) v ∈ P) → P = ⊤) :
    (ofNegModeGenerators hvac hT hLoc hNegGen).translation = T := (rfl)

/-- `ofNegModeGenerators` sends each generating state `((F i)[[-1]]) vac` to `F i`. -/
@[simp]
theorem ofNegModeGenerators_field_ncoeff_neg_one_vacuum [IsAddTorsionFree V]
    {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hvac : T vac = 0)
    (hT : ∀ (i : ι) (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hLoc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hNegGen : ∀ P : Submodule R V, vac ∈ P →
      (∀ (i : ι) (k : ℕ), ∀ v ∈ P, ((F i)[[-(k : ℤ) - 1]]) v ∈ P) → P = ⊤) (i : ι) :
    (ofNegModeGenerators hvac hT hLoc hNegGen).field (((F i)[[-1]]) vac) = F i :=
  ofGenerators_field_ncoeff_neg_one_vacuum hvac hT hLoc _ i

end FormalVertexAxioms

end TauCeti
