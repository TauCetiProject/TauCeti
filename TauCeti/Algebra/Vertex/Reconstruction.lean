/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Borcherds
import Mathlib.Tactic.Abel

/-!
# Reconstruction of formal vertex algebras from generating fields

Given an `R`-module `V` over a `ℚ`-algebra `R`, a vacuum vector `vac : V`, an endomorphism
`T : Module.End R V` killing `vac`, and pairwise local, `T`-covariant fields
`F : ι → VertexOperator R V` whose modes generate `V` from `vac`, there is a unique
`TauCeti.FormalVertexAxioms R V` with vacuum `vac`, translation `T`, and `Y((F i)₍₋₁₎ vac, z) = F i`
for every `i`. Annihilation of `vac` by nonnegative modes follows automatically over `ℚ`.

## Main definitions

* `TauCeti.FormalVertexAxioms.ofGeneratingFields`: the reconstructed formal vertex algebra on `V`.

## Main results

* `TauCeti.FormalDistribution.eq_zero_of_mulSub_pow_eq_zero`: vanishing of a truncated distribution
  annihilated by `(z - w)ᴺ`.
* `VertexOperator.IsLocalOfOrder.ncoeff_apply_ncoeff_apply_eq_zero`: mode annihilation propagation
  across mutually local fields.
* `TauCeti.FormalVertexAxioms.existsUnique_of_generatingFields`: existence and uniqueness of the
  formal vertex algebra extending a generating family of local `T`-covariant fields.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.5 (Theorem 4.5).
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.9 and §3.2.1.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Proposition 3.12.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti.FormalDistribution

/-- If a two-variable formal distribution `c` is annihilated by `(z - w)ᴺ` and vanishes for all
sufficiently large indices in the second variable (uniformly in the first), then `c = 0`. -/
theorem eq_zero_of_mulSub_pow_eq_zero {M : Type*} [AddCommGroup M] {c : FormalDistribution M}
    {N : ℕ} (hc : (mulSub ^ N) c = 0) (htrunc : ∃ K : ℤ, ∀ m n : ℤ, K ≤ n → c m n = 0) :
    c = 0 := by
  induction N generalizing c with
  | zero => simpa using hc
  | succ N ih =>
    obtain ⟨K, hK⟩ := htrunc
    have hmul : mulSub c = 0 := ih (by simpa [pow_succ, AddMonoid.End.coe_mul] using hc)
      ⟨K, fun m n hn ↦ by rw [mulSub_apply, hK (m + 1) n hn, hK m (n + 1) (by omega), sub_self]⟩
    have hshift (k : ℕ) (m n : ℤ) : c m n = c (m - k) (n + k) := by
      induction k with
      | zero => simp
      | succ k ihk =>
        have h := congrFun (congrFun hmul (m - k - 1)) (n + k)
        simp only [mulSub_apply, Pi.zero_apply, sub_eq_zero,
          show m - (k : ℤ) - 1 + 1 = m - k by omega] at h
        rw [ihk, h]; congr 1 <;> omega
    funext m n; rw [hshift (K - n).toNat m n]; exact hK _ _ (by omega)

end TauCeti.FormalDistribution

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Zero is local of order `0` to every vertex operator. -/
theorem IsLocalOfOrder.zero_left (C : VertexOperator R V) :
    (0 : VertexOperator R V).IsLocalOfOrder C 0 := by
  rw [isLocalOfOrder_iff]; intro _ _; simp

/-- Sums of vertex operators local to `C` are local to `C`. -/
theorem IsLocalOfOrder.add_left {A₁ A₂ C : VertexOperator R V} {N₁ N₂ : ℕ}
    (h₁ : A₁.IsLocalOfOrder C N₁) (h₂ : A₂.IsLocalOfOrder C N₂) :
    (A₁ + A₂).IsLocalOfOrder C (max N₁ N₂) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  have hcomm : (A₁ + A₂).commutatorDistribution C =
      A₁.commutatorDistribution C + A₂.commutatorDistribution C := by
    ext m n; simp only [commutatorDistribution_apply, Pi.add_apply, map_add, add_mul, mul_add]
    abel_nf
  rw [hcomm, map_add, (isLocalOfOrder_iff_mulSub_pow_eq_zero _ _ _).mp (h₁.mono (le_max_left _ _)),
    (isLocalOfOrder_iff_mulSub_pow_eq_zero _ _ _).mp (h₂.mono (le_max_right _ _)), add_zero]

/-- Scalar multiples of a vertex operator local to `C` remain local to `C` of the same order. -/
theorem IsLocalOfOrder.smul_left {A C : VertexOperator R V} {N : ℕ}
    (h : A.IsLocalOfOrder C N) (r : R) : (r • A).IsLocalOfOrder C N := by
  rw [isLocalOfOrder_iff]; intro m n
  rw [sum_congr rfl fun ij _ ↦ by
      simp only [map_smul, Pi.smul_apply, smul_mul_assoc, mul_smul_comm, ← smul_sub]
      rw [smul_comm _ r, smul_comm _ r],
    ← smul_sum, isLocalOfOrder_iff.mp h m n, smul_zero]

/-- If `B` is mutually local with `C` and all modes of `B` annihilate `v`, then all modes of `B`
also annihilate `(C[[n]]) v` for every `n : ℤ`. -/
theorem IsLocalOfOrder.ncoeff_apply_ncoeff_apply_eq_zero {B C : VertexOperator R V} {N : ℕ}
    (h : B.IsLocalOfOrder C N) {v : V} (hv : ∀ m : ℤ, (B[[m]]) v = 0) (m n : ℤ) :
    (B[[m]]) ((C[[n]]) v) = 0 := by
  have hc : (TauCeti.FormalDistribution.mulSub ^ N) (fun p q ↦ (B[[p]]) ((C[[q]]) v)) = 0 := by
    funext p q; rw [TauCeti.FormalDistribution.mulSub_pow_apply]
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, mul_apply_eq_comp,
      LinearMap.zero_apply, Pi.zero_apply, hv, map_zero, sub_zero] using
      LinearMap.congr_fun (isLocalOfOrder_iff.mp h p q) v
  obtain ⟨K, hK⟩ := C.exists_forall_ncoeff_apply_eq_zero v
  exact congrFun (congrFun (TauCeti.FormalDistribution.eq_zero_of_mulSub_pow_eq_zero hc
    ⟨K, fun _ q hq ↦ by simp [hK q hq]⟩) m) n

end VertexOperator

namespace TauCeti.FormalVertexAxioms

section GeneratedFields

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

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
  induction hle with
  | refl => exact hA
  | step _ ih => exact .mono ih

private theorem genDepth_lie_translation {T : Module.End R V} {F : ι → VertexOperator R V}
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]]) :
    ∀ {d : ℕ} {B : VertexOperator R V}, GenDepth F d B →
      ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]] := fun hB ↦ by
  induction hB with
  | zero => intro _; simp [Ring.lie_def]
  | id => intro m; rcases eq_or_ne m (-1) with rfl | hm <;> simp [Ring.lie_def, ncoeff_id, *]
  | gen _ i => exact hcov i
  | mono _ ih => exact ih
  | add _ _ ihA ihB =>
    intro m; rw [map_add, Pi.add_apply, map_add, map_add, Pi.add_apply, Ring.lie_def, mul_add,
      add_mul, ← sub_add_sub_comm, ← Ring.lie_def, ← Ring.lie_def, ihA m, ihB m]
  | smul r _ ihA =>
    intro m; rw [map_smul, Pi.smul_apply, map_smul, map_smul, Pi.smul_apply, Ring.lie_def,
      mul_smul_comm, smul_mul_assoc, ← smul_sub, ← Ring.lie_def, ihA m]
  | derivative _ ihA =>
    intro m; rw [ncoeff_derivative, ncoeff_derivative, Ring.lie_def, mul_smul_comm, smul_mul_assoc,
      ← smul_sub, ← Ring.lie_def, ihA (m - 1)]
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
      | exact ⟨0, (IsLocalOfOrder.zero_left _).symm⟩ | exact ⟨0, IsLocalOfOrder.id_right _⟩
      | exact hloc _ _
  | succ d ih =>
    have half : ∀ {A C}, GenDepth F (d + 1) A → GenDepth F d C → ∃ N, A.IsLocalOfOrder C N :=
      fun hA hC ↦ genDepth_step_isLocalOfOrder ih hA (fun hX ↦ ih hX hC)
    exact fun _ _ hA hB ↦ genDepth_step_isLocalOfOrder ih hA fun hX ↦
      let ⟨N, h⟩ := half hB hX; ⟨N, h.symm⟩

private def generatedFields (F : ι → VertexOperator R V) : Submodule R (VertexOperator R V) where
  carrier := {B | ∃ d : ℕ, GenDepth F d B}
  zero_mem' := ⟨0, .zero 0⟩
  add_mem' := fun ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ ↦
    ⟨max d₁ d₂ + 1, .add (genDepth_mono_le (le_max_left _ _) h₁)
      (genDepth_mono_le (le_max_right _ _) h₂)⟩
  smul_mem' := fun r _ ⟨d, h⟩ ↦ ⟨d + 1, .smul r h⟩

private theorem mem_generatedFields_nthProduct {F : ι → VertexOperator R V} (n : ℤ)
    {A B : VertexOperator R V} : A ∈ generatedFields F → B ∈ generatedFields F →
    nthProduct n A B ∈ generatedFields F := fun ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ ↦
  ⟨max d₁ d₂ + 1, .nthProduct n (genDepth_mono_le (le_max_left _ _) h₁)
    (genDepth_mono_le (le_max_right _ _) h₂)⟩

private theorem generatedFields_isLocalOfOrder {F : ι → VertexOperator R V}
    (hloc : ∀ i j, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N) {A B : VertexOperator R V} :
    A ∈ generatedFields F → B ∈ generatedFields F → ∃ N : ℕ, A.IsLocalOfOrder B N :=
  fun ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ ↦ genDepth_isLocalOfOrder hloc (max d₁ d₂)
    (genDepth_mono_le (le_max_left _ _) h₁) (genDepth_mono_le (le_max_right _ _) h₂)

private def evalVacLinearMap (vac : V) (F : ι → VertexOperator R V) : generatedFields F →ₗ[R] V :=
  { toFun B := (B.1[[-1]]) vac, map_add' _ _ := by simp, map_smul' _ _ := by simp }

end GeneratedFields

section Reconstruction

variable {R V ι : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]
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
  have hvac_zero (m : ℤ) : (B[[m]]) vac = 0 := by
    rcases le_or_gt 0 m with hm | hm
    · exact ncoeff_apply_eq_zero_of_nonneg_of_lie hT hcovB hm
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
      rw [ncoeff_neg_succ_apply_of_lie hT hcovB k, hker, map_zero, smul_zero]
  let W : Submodule R V :=
    { carrier := {v : V | ∀ m : ℤ, (B[[m]]) v = 0}
      zero_mem' := fun _ ↦ map_zero _
      add_mem' := fun hx hy m ↦ by rw [map_add, hx m, hy m, add_zero]
      smul_mem' := fun _ _ hx m ↦ by rw [map_smul, hx m, smul_zero] }
  have hW : W = ⊤ := hgen W hvac_zero fun i n v hv m ↦
    let ⟨_, hlocBi⟩ := generatedFields_isLocalOfOrder hloc hB ⟨0, .gen 0 i⟩
    hlocBi.ncoeff_apply_ncoeff_apply_eq_zero hv m n
  exact ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ (show v ∈ W from hW ▸ Submodule.mem_top) m

private theorem evalVacLinearMap_bijective : Function.Bijective (evalVacLinearMap vac F) := by
  refine ⟨fun x y hxy ↦ Subtype.ext <| sub_eq_zero.mp <|
      eq_zero_of_mem_generatedFields vac T F hT hcov hloc hgen (sub_mem x.2 y.2) ?_, ?_⟩
  · simpa [evalVacLinearMap, sub_eq_zero] using hxy
  · rw [← LinearMap.range_eq_top]
    refine hgen (LinearMap.range (evalVacLinearMap vac F))
      ⟨⟨VertexOperator.id R V, ⟨0, .id 0⟩⟩, by simp [evalVacLinearMap]⟩
      fun i n v ⟨⟨B, hB⟩, hBv⟩ ↦ ⟨⟨nthProduct n (F i) B,
        mem_generatedFields_nthProduct n ⟨0, .gen 0 i⟩ hB⟩, ?_⟩
    rw [← hBv]
    exact ncoeff_neg_one_nthProduct_apply
      (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie hT (hcov i) hm)
      (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie hT
        (let ⟨_, hd⟩ := hB; genDepth_lie_translation hcov hd) hm) n

/-- **Reconstruction of a formal vertex algebra from generating fields.** Given `vac : V` killed by
`T : Module.End R V` over a `ℚ`-algebra `R`, and pairwise local, `T`-covariant fields `F i` whose
mode iterates generate `V` from `vac`, this constructs the unique `TauCeti.FormalVertexAxioms R V`
with vacuum `vac`, translation `T`, and `Y((F i)₍₋₁₎ vac, z) = F i`. -/
def ofGeneratingFields : FormalVertexAxioms R V :=
  let e := LinearEquiv.ofBijective (evalVacLinearMap vac F)
    (evalVacLinearMap_bijective vac T F hT hcov hloc hgen)
  let Y : V →ₗ[R] VertexOperator R V := (generatedFields F).subtype.comp e.symm.toLinearMap
  have hY_mem (a : V) : Y a ∈ generatedFields F := (e.symm a).2
  have hY_cov (a : V) := let ⟨_, hd⟩ := hY_mem a; genDepth_lie_translation hcov hd
  have hY_eval (B : generatedFields F) : Y ((B.1[[-1]]) vac) = B.1 :=
    congrArg Subtype.val (e.symm_apply_apply B)
  have heval_Y (a : V) : ((Y a)[[-1]]) vac = a := e.apply_symm_apply a
  { field := Y, vacuum := vac, translation := T, translation_vacuum := hT
    ncoeff_field_vacuum := fun n ↦ by
      rw [show Y vac = VertexOperator.id R V by
        simpa using hY_eval ⟨VertexOperator.id R V, ⟨0, .id 0⟩⟩, ncoeff_id]
    ncoeff_field_apply_vacuum_of_nonneg := fun a _ hn ↦
      ncoeff_apply_eq_zero_of_nonneg_of_lie hT (hY_cov a) hn
    ncoeff_neg_one_field_apply_vacuum := heval_Y
    field_translation := fun a ↦ by
      have hd_eval : ((derivative (Y a))[[-1]]) vac = T a := by
        have hrec := apply_ncoeff_apply_of_lie hT (hY_cov a) (-1)
        rw [heval_Y a] at hrec; rw [ncoeff_derivative, LinearMap.smul_apply, hrec]
      have h := hY_eval ⟨derivative (Y a), let ⟨d, hd⟩ := hY_mem a; ⟨d + 1, .derivative hd⟩⟩
      dsimp only at h; rwa [hd_eval] at h
    lie_translation_ncoeff := fun a n ↦ hY_cov a n
    exists_isLocalOfOrder := fun a b ↦ generatedFields_isLocalOfOrder hloc (hY_mem a) (hY_mem b) }

/-- The vacuum vector of `ofGeneratingFields` is `vac`. -/
@[simp] theorem ofGeneratingFields_vacuum :
    (ofGeneratingFields vac T F hT hcov hloc hgen).vacuum = vac := by rfl

/-- The translation operator of `ofGeneratingFields` is `T`. -/
@[simp] theorem ofGeneratingFields_translation :
    (ofGeneratingFields vac T F hT hcov hloc hgen).translation = T := by rfl

/-- Each generating field `F i` is recovered as the state–field operator of `(F i)₍₋₁₎ vac`. -/
@[simp] theorem ofGeneratingFields_field_ncoeff_neg_one_apply (i : ι) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).field (((F i)[[-1]]) vac) = F i := by
  exact congrArg Subtype.val <| (LinearEquiv.ofBijective (evalVacLinearMap vac F)
    (evalVacLinearMap_bijective vac T F hT hcov hloc hgen)).symm_apply_apply ⟨F i, ⟨0, .gen 0 i⟩⟩

/-- Convenience form of generator recovery when `((F i)[[-1]]) vac = a` is given. -/
theorem ofGeneratingFields_field_eq {i : ι} {a : V} (ha : ((F i)[[-1]]) vac = a) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).field a = F i := by
  rw [← ha, ofGeneratingFields_field_ncoeff_neg_one_apply]

/-- **Existence and uniqueness in the reconstruction theorem.** There is a unique formal vertex
algebra on `V` over a `ℚ`-algebra `R` with vacuum `vac`, translation `T`, and
`Y((F i)₍₋₁₎ vac, z) = F i` for every `i`. -/
theorem existsUnique_of_generatingFields :
    ∃! A : FormalVertexAxioms R V,
      A.vacuum = vac ∧ A.translation = T ∧ ∀ i, A.field (((F i)[[-1]]) vac) = F i := by
  let A₀ := ofGeneratingFields vac T F hT hcov hloc hgen
  refine ⟨A₀, ⟨ofGeneratingFields_vacuum vac T F hT hcov hloc hgen,
    ofGeneratingFields_translation vac T F hT hcov hloc hgen,
    ofGeneratingFields_field_ncoeff_neg_one_apply vac T F hT hcov hloc hgen⟩, ?_⟩
  rintro A ⟨hvac, _, hF⟩
  have hW : LinearMap.eqLocus A.field A₀.field = ⊤ := by
    refine hgen (LinearMap.eqLocus A.field A₀.field) ?_ fun i n v hv ↦ ?_
    · rw [LinearMap.mem_eqLocus, ← hvac, A.field_vacuum, hvac,
        ← ofGeneratingFields_vacuum vac T F hT hcov hloc hgen, A₀.field_vacuum]
    · rw [LinearMap.mem_eqLocus]
      have hA₀i := ofGeneratingFields_field_ncoeff_neg_one_apply vac T F hT hcov hloc hgen i
      rw [← hF i, A.field_ncoeff_apply, hF i, LinearMap.mem_eqLocus.mp hv,
        ← hA₀i, ← A₀.field_ncoeff_apply, hA₀i]
  exact FormalVertexAxioms.ext <| LinearMap.ext fun a ↦
    show a ∈ LinearMap.eqLocus A.field A₀.field from hW ▸ Submodule.mem_top

end Reconstruction

end TauCeti.FormalVertexAxioms
