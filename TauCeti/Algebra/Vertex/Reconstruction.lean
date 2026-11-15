/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Borcherds
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Reconstruction theorem for formal vertex algebras

We prove **Kac's existence and reconstruction theorem** (`FormalVertexAxioms.ofGeneratingFields`,
`FormalVertexAxioms.eq_ofGeneratingFields`, `FormalVertexAxioms.existsUnique_of_generatingFields`)
for formal vertex algebras (`TauCeti.FormalVertexAxioms R V`) over an arbitrary commutative ring
`R` when `V` is additively torsion-free (`[IsAddTorsionFree V]`).

Given:
* a vacuum vector `vac : V` killed by an `R`-linear translation operator `T : Module.End R V`;
* a family `F : ι → VertexOperator R V` of pairwise mutually local, `T`-covariant fields on `V`;
* the generation hypothesis that no proper `R`-submodule of `V` contains `vac` and is stable under
  all modes `(F i)[[n]]` (`n : ℤ`);

there exists a unique `FormalVertexAxioms R V` structure on `V` with vacuum `vac` such that
`Y((F i)₍₋₁₎ vac, z) = F i` for every `i`, and its translation operator is `T`. Regularity on the
vacuum (`(F i)[[n]] vac = 0` for `n ≥ 0`) does not need to be assumed separately:
`VertexOperator.ncoeff_apply_eq_zero_of_nonneg_of_lie_derivative` derives it from `T vac = 0`,
translation covariance, and `[IsAddTorsionFree V]`.

## Main definitions and results

* `TauCeti.FormalVertexAxioms.ofGeneratingFields`: constructs a `FormalVertexAxioms R V` structure
  from a family of mutually local, translation-covariant generating fields.
* `TauCeti.FormalVertexAxioms.ofGeneratingFields_field_apply`: `Y((F i)₍₋₁₎ vac, z) = F i`.
* `TauCeti.FormalVertexAxioms.eq_ofGeneratingFields`: uniqueness of the reconstructed structure.
* `TauCeti.FormalVertexAxioms.existsUnique_of_generatingFields`: combined existence and uniqueness.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.5 (Theorem 4.5, Existence theorem).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), §3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.9 and §3.2.1
  (Reconstruction theorem).
-/

public section

noncomputable section

open scoped VertexOperator
open Finset TauCeti VertexOperator

namespace TauCeti.FormalVertexAxioms

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### Double-centralizer submodule of covariant local fields -/

/-- Translation covariance `[T, G₍ₘ₎] = (∂G)₍ₘ₎` for a field `G`. -/
private def IsCovariant (T : Module.End R V) (G : VertexOperator R V) : Prop :=
  ∀ m : ℤ, ⁅T, G[[m]]⁆ = (derivative G)[[m]]

private theorem isCovariant_zero (T : Module.End R V) :
    IsCovariant T (0 : VertexOperator R V) := fun _ ↦ by
  simp [Ring.lie_def]

private theorem IsCovariant.add {T : Module.End R V} {G₁ G₂ : VertexOperator R V}
    (h₁ : IsCovariant T G₁) (h₂ : IsCovariant T G₂) : IsCovariant T (G₁ + G₂) := fun m ↦ by
  rw [map_add, Pi.add_apply, Ring.lie_def, mul_add, add_mul, add_sub_add_comm, ← Ring.lie_def,
    ← Ring.lie_def, h₁ m, h₂ m, map_add, map_add, Pi.add_apply]

private theorem IsCovariant.smul {T : Module.End R V} {G : VertexOperator R V}
    (r : R) (h : IsCovariant T G) : IsCovariant T (r • G) := fun m ↦ by
  rw [map_smul, Pi.smul_apply, Ring.lie_def, mul_smul_comm, smul_mul_assoc, ← smul_sub,
    ← Ring.lie_def, h m, map_smul, map_smul, Pi.smul_apply]

private theorem isCovariant_identity (T : Module.End R V) :
    IsCovariant T (identity : VertexOperator R V) := fun m ↦ by
  rw [derivative_identity, map_zero, Pi.zero_apply, ncoeff_identity]
  split_ifs <;> simp [Ring.lie_def]

private theorem IsCovariant.derivative {T : Module.End R V} {G : VertexOperator R V}
    (h : IsCovariant T G) : IsCovariant T (VertexOperator.derivative G) := fun m ↦ by
  have hz (z : ℤ) (u : Module.End R V) : ⁅T, z • u⁆ = z • ⁅T, u⁆ := by
    simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [ncoeff_derivative G m, hz, h (m - 1), ← ncoeff_derivative (VertexOperator.derivative G) m]

/-- `localCentralizer₀ T F` is the set of `T`-covariant fields mutually local with every generating
field `F j`. -/
private def localCentralizer₀ (T : Module.End R V) (F : ι → VertexOperator R V) :
    Set (VertexOperator R V) :=
  {G | IsCovariant T G ∧ ∀ j, ∃ N, G.IsLocalOfOrder (F j) N}

/-- `localSubmodule T F` is the double-locality `R`-submodule inside `localCentralizer₀ T F`: those
fields `G ∈ localCentralizer₀ T F` that are mutually local with every `H ∈ localCentralizer₀ T F`.
By Dong's lemma it is closed under all `n`-th products (`n : ℤ`). -/
private def localSubmodule (T : Module.End R V) (F : ι → VertexOperator R V) :
    Submodule R (VertexOperator R V) where
  carrier := {G | G ∈ localCentralizer₀ T F ∧
    ∀ H ∈ localCentralizer₀ T F, ∃ N, G.IsLocalOfOrder H N}
  zero_mem' :=
    ⟨⟨isCovariant_zero T, fun j ↦ ⟨0, IsLocalOfOrder.zero_left (F j) 0⟩⟩,
      fun H _ ↦ ⟨0, IsLocalOfOrder.zero_left H 0⟩⟩
  add_mem' {G₁ G₂} h₁ h₂ :=
    ⟨⟨h₁.1.1.add h₂.1.1, fun j ↦ by
        obtain ⟨N₁, hN₁⟩ := h₁.1.2 j
        obtain ⟨N₂, hN₂⟩ := h₂.1.2 j
        exact ⟨max N₁ N₂, hN₁.add_left hN₂⟩⟩,
      fun H hH ↦ by
        obtain ⟨N₁, hN₁⟩ := h₁.2 H hH
        obtain ⟨N₂, hN₂⟩ := h₂.2 H hH
        exact ⟨max N₁ N₂, hN₁.add_left hN₂⟩⟩
  smul_mem' r {G} h :=
    ⟨⟨h.1.1.smul r, fun j ↦ by
        obtain ⟨N, hN⟩ := h.1.2 j
        exact ⟨N, hN.smul_left r⟩⟩,
      fun H hH ↦ by
        obtain ⟨N, hN⟩ := h.2 H hH
        exact ⟨N, hN.smul_left r⟩⟩

private theorem identity_mem_localSubmodule (T : Module.End R V) (F : ι → VertexOperator R V) :
    (identity : VertexOperator R V) ∈ localSubmodule T F :=
  ⟨⟨isCovariant_identity T, fun j ↦ ⟨0, isLocalOfOrder_identity_left (F j) 0⟩⟩,
    fun H _ ↦ ⟨0, isLocalOfOrder_identity_left H 0⟩⟩

private theorem generator_mem_localSubmodule {T : Module.End R V} {F : ι → VertexOperator R V}
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N) (i : ι) :
    F i ∈ localSubmodule T F :=
  ⟨⟨hcov i, hloc i⟩, fun _ hH ↦ let ⟨N, hN⟩ := hH.2 i; ⟨N, hN.symm⟩⟩

private theorem derivative_mem_localSubmodule {T : Module.End R V} {F : ι → VertexOperator R V}
    {G : VertexOperator R V} (hG : G ∈ localSubmodule T F) :
    derivative G ∈ localSubmodule T F :=
  ⟨⟨hG.1.1.derivative, fun j ↦ let ⟨N, hN⟩ := hG.1.2 j; ⟨N + 1, hN.derivative_left⟩⟩,
    fun H hH ↦ let ⟨N, hN⟩ := hG.2 H hH; ⟨N + 1, hN.derivative_left⟩⟩

private theorem nthProduct_mem_localSubmodule {T : Module.End R V} {F : ι → VertexOperator R V}
    (n : ℤ) {A B : VertexOperator R V}
    (hA : A ∈ localSubmodule T F) (hB : B ∈ localSubmodule T F) :
    nthProduct n A B ∈ localSubmodule T F := by
  obtain ⟨r₁, hr₁⟩ := hA.2 B hB.1
  refine ⟨⟨lie_ncoeff_nthProduct hA.1.1 hB.1.1 n, fun j ↦ ?_⟩, fun H hH ↦ ?_⟩
  · obtain ⟨r₂, hr₂⟩ := hA.1.2 j
    obtain ⟨r₃, hr₃⟩ := hB.1.2 j
    exact ⟨_, hr₁.nthProduct_left hr₂ hr₃ n⟩
  · obtain ⟨r₂, hr₂⟩ := hA.2 H hH
    obtain ⟨r₃, hr₃⟩ := hB.2 H hH
    exact ⟨_, hr₁.nthProduct_left hr₂ hr₃ n⟩

/-- Evaluation of a field in `localSubmodule T F` at mode `-1` on the vacuum vector. -/
private def evalVacuum (T : Module.End R V) (vac : V) (F : ι → VertexOperator R V) :
    localSubmodule T F →ₗ[R] V where
  toFun G := (G.1[[-1]]) vac
  map_add' _ _ := by simp [map_add]
  map_smul' _ _ := by simp [map_smul]

section Reconstruction

variable [IsAddTorsionFree V]

private theorem evalVacuum_injective {T : Module.End R V} {vac : V} {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    Function.Injective (evalVacuum T vac F) := by
  rw [injective_iff_map_eq_zero]
  intro G hG0
  let W : Submodule R V :=
    { carrier := {v | ∀ m : ℤ, (G.1[[m]]) v = 0}
      zero_mem' := fun _ ↦ map_zero _
      add_mem' := fun {u v} hu hv m ↦ by rw [map_add, hu m, hv m, add_zero]
      smul_mem' := fun c {v} hv m ↦ by rw [map_smul, hv m, smul_zero] }
  have hvac_mem : vac ∈ W := fun m ↦
    ncoeff_apply_eq_zero_of_lie_derivative hT G.2.1.1 hG0 m
  have hinv : ∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W := by
    intro i n v hv
    obtain ⟨P, hPv⟩ := (F i).exists_forall_ncoeff_apply_eq_zero v
    obtain ⟨N, hlocG⟩ := G.2.1.2 i
    have hdown : ∀ (d : ℕ) (k : ℤ), (P - k).toNat ≤ d → ∀ m : ℤ,
        (G.1[[m]]) (((F i)[[k]]) v) = 0 := by
      intro d
      induction d with
      | zero =>
        intro k hk m
        rw [hPv k (by omega), map_zero]
      | succ d ih =>
        intro k hk m
        rcases le_or_gt (P : ℤ) k with hge | hlt
        · rw [hPv k hge, map_zero]
        · have h₀ := LinearMap.congr_fun (isLocalOfOrder_iff.1 hlocG (m - N) k) v
          simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
            mul_apply_eq_comp, LinearMap.zero_apply] at h₀
          rw [sum_eq_single (N, 0) (fun ij hij hne ↦ ?_) (by simp)] at h₀
          · simpa [hv m] using h₀
          · have hij2 : ij.2 ≠ 0 := fun h2 ↦
              hne (Prod.ext (by have := mem_antidiagonal.1 hij; omega) h2)
            have h₁ : (G.1[[m - N + ij.1]]) (((F i)[[k + ij.2]]) v) = 0 :=
              ih (k + ij.2) (by omega) (m - N + ij.1)
            rw [h₁, hv (m - N + ij.1), map_zero, sub_self, smul_zero, smul_zero]
    exact hdown (P - n).toNat n le_rfl
  have hW : W = ⊤ := hgen W hvac_mem hinv
  ext : 1
  exact ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ Submodule.eq_top_iff'.1 hW v m

private theorem evalVacuum_surjective {T : Module.End R V} {vac : V} {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    Function.Surjective (evalVacuum T vac F) := by
  rw [← LinearMap.range_eq_top]
  refine hgen (LinearMap.range (evalVacuum T vac F)) ?_ ?_
  · exact ⟨⟨identity, identity_mem_localSubmodule T F⟩, by simp [evalVacuum]⟩
  · rintro i n _ ⟨B, rfl⟩
    refine ⟨⟨nthProduct n (F i) B.1,
      nthProduct_mem_localSubmodule n (generator_mem_localSubmodule hcov hloc i) B.2⟩, ?_⟩
    exact ncoeff_neg_one_nthProduct_apply
      (fun m hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_derivative hT (hcov i) hm)
      (fun m hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_derivative hT B.2.1.1 hm) n

/-- **Kac's reconstruction (existence) theorem for formal vertex algebras.**

Let `V` be an additively torsion-free `R`-module equipped with a vector `vac : V`, a linear
endomorphism `T : Module.End R V` killing `vac`, and a family `F : ι → VertexOperator R V` of
pairwise mutually local, `T`-covariant fields whose modes generate `V` from `vac` as an
`R`-submodule. Then there is a canonical `FormalVertexAxioms R V` structure on `V` with vacuum
`vac`, translation `T`, and `Y((F i)₍₋₁₎ vac, z) = F i` for every `i`. -/
def ofGeneratingFields {T : Module.End R V} {vac : V} {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    FormalVertexAxioms R V :=
  let e : localSubmodule T F ≃ₗ[R] V :=
    LinearEquiv.ofBijective (evalVacuum T vac F)
      ⟨evalVacuum_injective hT hgen, evalVacuum_surjective hT hcov hloc hgen⟩
  have he_symm (G : localSubmodule T F) : e.symm ((G.1[[-1]]) vac) = G :=
    e.symm_apply_apply G
  have he_apply (a : V) : (((e.symm a).1)[[-1]]) vac = a :=
    e.apply_symm_apply a
  { field := (localSubmodule T F).subtype.comp e.symm.toLinearMap
    vacuum := vac
    translation := T
    translation_vacuum := hT
    ncoeff_field_vacuum n := by
      have hid : e.symm vac = ⟨identity, identity_mem_localSubmodule T F⟩ := by
        simpa using he_symm ⟨identity, identity_mem_localSubmodule T F⟩
      rw [LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_toLinearMap, hid,
        ncoeff_identity]
    ncoeff_field_apply_vacuum_of_nonneg a n hn :=
      ncoeff_apply_eq_zero_of_nonneg_of_lie_derivative hT (e.symm a).2.1.1 hn
    ncoeff_neg_one_field_apply_vacuum := he_apply
    field_translation a := by
      let G : localSubmodule T F := e.symm a
      have hder : ((derivative G.1)[[-1]]) vac = T a := by
        have hc := LinearMap.congr_fun (G.2.1.1 (-1)) vac
        rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
          he_apply a, hT, map_zero, sub_zero] at hc
        exact hc.symm
      have hsymm : e.symm (T a) = ⟨derivative G.1, derivative_mem_localSubmodule G.2⟩ := by
        rw [← hder]
        exact he_symm ⟨derivative G.1, derivative_mem_localSubmodule G.2⟩
      exact congrArg Subtype.val hsymm
    lie_translation_ncoeff a n := (e.symm a).2.1.1 n
    exists_isLocalOfOrder a b := (e.symm a).2.2 (e.symm b).1 (e.symm b).2.1 }

/-- The vacuum vector of `ofGeneratingFields` is `vac`. -/
@[simp]
theorem ofGeneratingFields_vacuum {T : Module.End R V} {vac : V} {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    (ofGeneratingFields hT hcov hloc hgen).vacuum = vac :=
  (rfl)

/-- The translation operator of `ofGeneratingFields` is `T`. -/
@[simp]
theorem ofGeneratingFields_translation {T : Module.End R V} {vac : V} {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    (ofGeneratingFields hT hcov hloc hgen).translation = T :=
  (rfl)

/-- Each generating field `F i` is recovered as the state–field image of `(F i)₍₋₁₎ vac`. -/
@[simp]
theorem ofGeneratingFields_field_apply {T : Module.End R V} {vac : V} {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    (i : ι) :
    (ofGeneratingFields hT hcov hloc hgen).field (((F i)[[-1]]) vac) = F i := by
  let e : localSubmodule T F ≃ₗ[R] V :=
    LinearEquiv.ofBijective (evalVacuum T vac F)
      ⟨evalVacuum_injective hT hgen, evalVacuum_surjective hT hcov hloc hgen⟩
  exact congrArg Subtype.val
    (e.symm_apply_apply ⟨F i, generator_mem_localSubmodule hcov hloc i⟩)

/-- **Uniqueness in Kac's reconstruction theorem.** Any formal vertex algebra structure on `V`
with vacuum `vac` that assigns `F i` to `(F i)₍₋₁₎ vac` coincides with
`ofGeneratingFields hT hcov hloc hgen` (and therefore also has translation operator `T`). -/
theorem eq_ofGeneratingFields {T : Module.End R V} {vac : V} {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    (B : FormalVertexAxioms R V) (hB_vac : B.vacuum = vac)
    (hB_field : ∀ i, B.field (((F i)[[-1]]) vac) = F i) :
    B = ofGeneratingFields hT hcov hloc hgen := by
  let A := ofGeneratingFields hT hcov hloc hgen
  refine FormalVertexAxioms.ext (LinearMap.eqLocus_eq_top.1 ?_)
  refine hgen (LinearMap.eqLocus B.field A.field) ?_ ?_
  · rw [LinearMap.mem_eqLocus, ← hB_vac, B.field_vacuum, hB_vac,
      ← ofGeneratingFields_vacuum hT hcov hloc hgen, A.field_vacuum]
  · intro i n v hv
    rw [LinearMap.mem_eqLocus] at hv ⊢
    have hB_i := hB_field i
    have hA_i : A.field (((F i)[[-1]]) vac) = F i :=
      ofGeneratingFields_field_apply hT hcov hloc hgen i
    calc B.field (((F i)[[n]]) v)
        = B.field (((B.field (((F i)[[-1]]) vac))[[n]]) v) := by rw [hB_i]
      _ = nthProduct n (B.field (((F i)[[-1]]) vac)) (B.field v) :=
          B.field_ncoeff_apply _ v n
      _ = nthProduct n (A.field (((F i)[[-1]]) vac)) (A.field v) := by
          rw [hB_i, hA_i, hv]
      _ = A.field (((A.field (((F i)[[-1]]) vac))[[n]]) v) :=
          (A.field_ncoeff_apply _ v n).symm
      _ = A.field (((F i)[[n]]) v) := by rw [hA_i]

/-- **Existence and uniqueness** form of Kac's reconstruction theorem. -/
theorem existsUnique_of_generatingFields {T : Module.End R V} {vac : V}
    {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ i (m : ℤ), ⁅T, (F i)[[m]]⁆ = (derivative (F i))[[m]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    ∃! A : FormalVertexAxioms R V,
      A.vacuum = vac ∧ ∀ i, A.field (((F i)[[-1]]) vac) = F i :=
  ⟨ofGeneratingFields hT hcov hloc hgen,
    ⟨rfl, ofGeneratingFields_field_apply hT hcov hloc hgen⟩,
    fun B ⟨hvac, hfield⟩ ↦ eq_ofGeneratingFields hT hcov hloc hgen B hvac hfield⟩

end Reconstruction

end TauCeti.FormalVertexAxioms
