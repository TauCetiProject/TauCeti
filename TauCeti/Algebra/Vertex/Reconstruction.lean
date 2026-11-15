/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.NthProduct
import TauCeti.Algebra.Vertex.FormalDistribution
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.Abel

/-!
# State–field correspondence and the vertex algebra reconstruction theorem

In a formal vertex algebra over a `ℚ`-algebra `R`, the state–field map intertwines every mode
product `a₍ₙ₎ b` (`n : ℤ`) with the `n`-th field product `Y(a, z)₍ₙ₎ Y(b, z)`
(`TauCeti.FormalVertexAxioms.field_ncoeff_apply`). Specializing `n` expresses the field of a
nonnegative mode `a₍ₙ₎ b` (`n : ℕ`) as `Res_z (z - w)ⁿ [Y(a, z), Y(b, w)]` and the field of a
negative mode `a₍₋ₖ₋₁₎ b` as the divided-power normal-ordered product
`(k!)⁻¹ : (∂_z^k Y(a, z)) Y(b, z) :` (in particular, `Y(a₍₋₁₎ b, z) = :Y(a, z) Y(b, z):`).

Conversely, given an `R`-module `V` over a `ℚ`-algebra `R`, a vacuum vector `vac`, an endomorphism
`T` killing `vac`, and a family of pairwise local fields `F : ι → VertexOperator R V` covariant
with `T` whose modes generate `V` from `vac`, there is a unique formal vertex algebra structure on
`V` with vacuum `vac`, translation `T`, and `Y(((F i)[[-1]]) vac, z) = F i`
(`TauCeti.FormalVertexAxioms.ofGeneratingFields`,
`TauCeti.FormalVertexAxioms.existsUnique_of_generatingFields`). Notably, lower truncation of each
field `F i` combined with `[T, (F i)[[n]]] = (∂(F i))[[n]]` and `T vac = 0` automatically implies
that `F i` annihilates `vac` in all nonnegative modes, and no `vac ≠ 0` hypothesis is needed.

## Main definitions

* `TauCeti.FormalVertexAxioms.ofGeneratingFields`: the formal vertex algebra reconstructed from a
  family of pairwise local, translation-covariant generating fields.

## Main results

* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: state–field correspondence
  `Y(a₍ₙ₎ b, z) = Y(a, z)₍ₙ₎ Y(b, z)` for all `n : ℤ`.
* `TauCeti.FormalVertexAxioms.field_ncoeff_natCast_apply`,
  `TauCeti.FormalVertexAxioms.field_ncoeff_neg_one_apply`,
  `TauCeti.FormalVertexAxioms.field_ncoeff_neg_apply`: specializations to residue products, normal
  ordering, and negative modes.
* `TauCeti.FormalVertexAxioms.eq_of_generatingFields`,
  `TauCeti.FormalVertexAxioms.existsUnique_of_generatingFields`: uniqueness and existence-uniqueness
  of the reconstructed formal vertex algebra.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.4–§4.5 (Theorem 4.5, the existence theorem).
* V. Kac, *Introduction to vertex algebras, Poisson vertex algebras, and integrable Hamiltonian
  systems*, Theorem 1.1.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Theorem 3.2.10.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.3, Theorem 2.3.11.
-/

public section

noncomputable section

open scoped VertexOperator
open VertexOperator

namespace TauCeti.FormalVertexAxioms

/-! ### State–field correspondence -/

section StateField

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]

private theorem hasUniqueDiv_of_algebra_rat (R V : Type*) [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] : HasUniqueDiv V :=
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ R)
  .of_module_rat V

/-- **State–field correspondence.** For every state `a`, `b` and integer `n : ℤ`, the field of
`a₍ₙ₎ b` is the `n`-th field product `Y(a, z)₍ₙ₎ Y(b, z)`. -/
theorem field_ncoeff_apply (A : FormalVertexAxioms R V) (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  have := hasUniqueDiv_of_algebra_rat R V
  symm
  refine A.eq_field_of_ncoeff_apply_vacuum_eq (fun d ↦ ?_) fun m ↦ ?_
  · obtain ⟨r, hr⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨s, hs⟩ := A.exists_isLocalOfOrder a d
    obtain ⟨t, ht⟩ := A.exists_isLocalOfOrder b d
    exact ⟨_, hr.nthProduct_left hs ht n⟩
  · rcases lt_or_ge m 0 with hm | hm
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -k - 1 := ⟨(-m - 1).toNat, by omega⟩
      refine nsmul_right_injective k.factorial_ne_zero ?_
      dsimp only
      rw [factorial_smul_ncoeff_apply_of_lie_eq_derivative A.translation_vacuum
            (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n) k,
          ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
            (A.ncoeff_field_apply_vacuum_of_nonneg b) n,
          A.ncoeff_neg_one_field_apply_vacuum,
          A.factorial_smul_ncoeff_field_apply_vacuum]
    · rw [ncoeff_nthProduct_apply_of_nonneg (A.ncoeff_field_apply_vacuum_of_nonneg a)
            (A.ncoeff_field_apply_vacuum_of_nonneg b) n hm,
          A.ncoeff_field_apply_vacuum_of_nonneg _ m hm]

/-- State–field correspondence for nonnegative residue products (`n : ℕ`). -/
theorem field_ncoeff_natCast_apply (A : FormalVertexAxioms R V) (a b : V) (n : ℕ) :
    A.field (((A.field a)[[(n : ℤ)]]) b) = nonnegResidueProduct n (A.field a) (A.field b) := by
  simpa using A.field_ncoeff_apply a b n

/-- State–field correspondence for the normal-ordered product (`n = -1`):
`Y(a₍₋₁₎ b, z) = :Y(a, z) Y(b, z):`. -/
theorem field_ncoeff_neg_one_apply (A : FormalVertexAxioms R V) (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  simpa using A.field_ncoeff_apply a b (-1)

/-- State–field correspondence for negative modes (`n = -k - 1`):
`Y(a₍₋ₖ₋₁₎ b, z) = (k!)⁻¹ : (∂_z^k Y(a, z)) Y(b, z) :`. -/
theorem field_ncoeff_neg_apply (A : FormalVertexAxioms R V) (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-k - 1]]) b) =
      algebraMap ℚ R (k.factorial : ℚ)⁻¹ •
        normalOrder ((derivative (R := R) (V := V))^[k] (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_apply]

end StateField

/-! ### Reconstruction from generating fields -/

section Reconstruction

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem bddBelow_idField (v : V) :
    BddBelow (Function.support fun k : ℤ ↦ (if k = 0 then (1 : Module.End R V) else 0) v) :=
  ⟨0, fun k hk ↦ by
    by_contra! hlt
    exact hk (by
      have h₀ : k ≠ 0 := by omega
      simp [h₀])⟩

/-- The identity field `id_V · z^0`, whose `(-1)`-mode is `1` and all other modes vanish. -/
private def idField : VertexOperator R V :=
  of_coeff (fun k ↦ if k = 0 then 1 else 0) bddBelow_idField

private theorem ncoeff_idField (n : ℤ) :
    (idField (R := R) (V := V))[[n]] = if n = -1 then 1 else 0 := by
  rw [idField, ncoeff_of_coeff]
  have : (-n - 1 = 0) ↔ (n = -1) := by omega
  simp [this]

private theorem isLocalOfOrder_idField_left (B : VertexOperator R V) :
    idField.IsLocalOfOrder B 0 :=
  IsLocalOfOrder.of_commute fun m _ ↦ by
    rw [ncoeff_idField]
    split_ifs
    · exact Commute.one_left _
    · exact Commute.zero_left _

/-- The `R`-submodule of fields that are translation-covariant with `T` and mutually local with
every generating field `F j`. -/
private def goodFields (T : Module.End R V) (F : ι → VertexOperator R V) :
    Submodule R (VertexOperator R V) where
  carrier := { B | (∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]]) ∧
    ∀ j : ι, ∃ N : ℕ, B.IsLocalOfOrder (F j) N }
  zero_mem' := ⟨fun _ ↦ by simp [Ring.lie_def], fun j ↦ ⟨0, IsLocalOfOrder.zero_left (F j) 0⟩⟩
  add_mem' {A B} hA hB :=
    ⟨fun n ↦ by
       rw [map_add, Pi.add_apply, map_add, map_add, Pi.add_apply, ← hA.1 n, ← hB.1 n]
       simp only [Ring.lie_def, mul_add, add_mul]
       abel,
     fun j ↦ by
       obtain ⟨M, hM⟩ := hA.2 j
       obtain ⟨N, hN⟩ := hB.2 j
       exact ⟨max M N, hM.add_left hN⟩⟩
  smul_mem' r {B} hB :=
    ⟨fun n ↦ by
       rw [map_smul, Pi.smul_apply, map_smul, map_smul, Pi.smul_apply, ← hB.1 n,
         Ring.lie_def, Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub],
     fun j ↦ by
       obtain ⟨N, hN⟩ := hB.2 j
       exact ⟨N, IsLocalOfOrder.smul_left r hN⟩⟩

private theorem idField_mem_goodFields (T : Module.End R V) (F : ι → VertexOperator R V) :
    idField ∈ goodFields T F := by
  refine ⟨fun n ↦ ?_, fun j ↦ ⟨0, isLocalOfOrder_idField_left (F j)⟩⟩
  rw [ncoeff_derivative]
  by_cases h₁ : n = -1
  · subst h₁
    simp [ncoeff_idField, Ring.lie_def]
  · by_cases h₂ : n = 0
    · subst h₂
      simp [ncoeff_idField, Ring.lie_def]
    · have hm : n - 1 ≠ -1 := by omega
      simp [ncoeff_idField, h₁, hm, Ring.lie_def]

private theorem generator_mem_goodFields {T : Module.End R V} {F : ι → VertexOperator R V}
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N) (i : ι) :
    F i ∈ goodFields T F :=
  ⟨hcov i, hloc i⟩

private theorem derivative_mem_goodFields {T : Module.End R V} {F : ι → VertexOperator R V}
    {B : VertexOperator R V} (hB : B ∈ goodFields T F) :
    derivative B ∈ goodFields T F :=
  ⟨lie_ncoeff_derivative hB.1, fun j ↦ by
    obtain ⟨N, hN⟩ := hB.2 j
    exact ⟨N + 1, hN.derivative_left⟩⟩

/-- Evaluation of a good field on the vacuum at mode `-1`: `B ↦ (B[[-1]]) vac`. -/
private def evalVacuum (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V) :
    goodFields T F →ₗ[R] V where
  toFun B := (B.1[[-1]]) vac
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem evalVacuum_apply (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (B : goodFields T F) :
    evalVacuum vac T F B = (B.1[[-1]]) vac :=
  rfl

variable [Algebra ℚ R]

private theorem nthProduct_generator_mem_goodFields {T : Module.End R V}
    {F : ι → VertexOperator R V}
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (i : ι) (n : ℤ) {B : VertexOperator R V} (hB : B ∈ goodFields T F) :
    nthProduct n (F i) B ∈ goodFields T F :=
  ⟨lie_ncoeff_nthProduct (hcov i) hB.1 n, fun j ↦ by
    obtain ⟨r, hr⟩ := hB.2 i
    obtain ⟨s, hs⟩ := hloc i j
    obtain ⟨t, ht⟩ := hB.2 j
    exact ⟨_, hr.symm.nthProduct_left hs ht n⟩⟩

private theorem evalVacuum_bijective (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    Function.Bijective (evalVacuum vac T F) := by
  have := hasUniqueDiv_of_algebra_rat R V
  refine ⟨fun x y hxy ↦ sub_eq_zero.mp ?_, ?_⟩
  · -- Injectivity: a good field with `(B[[-1]]) vac = 0` kills `vac` in all modes, hence kills `V`.
    let B := (x - y).1
    have hB := (x - y).2
    have hB0 : (B[[-1]]) vac = 0 := by
      simp only [evalVacuum_apply] at hxy
      simp [B, hxy]
    have hBvac : ∀ m : ℤ, (B[[m]]) vac = 0 := by
      intro m
      rcases lt_or_ge m 0 with hm | hm
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -k - 1 := ⟨(-m - 1).toNat, by omega⟩
        refine nsmul_right_injective k.factorial_ne_zero ?_
        dsimp only
        rw [factorial_smul_ncoeff_apply_of_lie_eq_derivative hT hB.1 k, hB0, map_zero, smul_zero]
      · exact ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT hB.1 hm
    let W : Submodule R V :=
      { carrier := { v | ∀ m : ℤ, (B[[m]]) v = 0 }
        zero_mem' := fun m ↦ map_zero _
        add_mem' := fun ha hb m ↦ by simp [ha m, hb m]
        smul_mem' := fun r _ ha m ↦ by simp [ha m] }
    have hW : W = ⊤ := hgen W hBvac fun i n v hv m ↦ by
      obtain ⟨N, hN⟩ := hB.2 i
      exact hN.ncoeff_apply_ncoeff_apply_eq_zero hv m n
    ext1
    refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
    exact (Submodule.eq_top_iff'.mp hW v) m
  · -- Surjectivity: `range (evalVacuum vac T F)` contains `vac` and is closed under `(F i)[[n]]`.
    rw [← LinearMap.range_eq_top]
    refine hgen (LinearMap.range (evalVacuum vac T F)) ?_ ?_
    · exact ⟨⟨idField, idField_mem_goodFields T F⟩, by simp [ncoeff_idField]⟩
    · rintro i n _ ⟨⟨B, hB⟩, rfl⟩
      refine ⟨⟨nthProduct n (F i) B, nthProduct_generator_mem_goodFields hcov hloc i n hB⟩, ?_⟩
      exact ncoeff_neg_one_nthProduct_apply
        (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT (hcov i) hm)
        (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT hB.1 hm) n

/-- Any good field `A` is mutually local with every field in the image of a state–field map `Y`
reconstructed from `evalVacuum`. -/
private theorem exists_isLocalOfOrder_of_mem_goodFields {vac : V} {T : Module.End R V}
    {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    {Y : V →ₗ[R] VertexOperator R V}
    (hY_mem : ∀ x : V, Y x ∈ goodFields T F)
    (hY_eval : ∀ x : V, ((Y x)[[-1]]) vac = x)
    (hY_eq : ∀ {B : VertexOperator R V}, B ∈ goodFields T F → Y ((B[[-1]]) vac) = B)
    (hY_vac : Y vac = idField)
    {A : VertexOperator R V} (hA : A ∈ goodFields T F) (b : V) :
    ∃ N : ℕ, A.IsLocalOfOrder (Y b) N := by
  have := hasUniqueDiv_of_algebra_rat R V
  let W : Submodule R V :=
    { carrier := { x | ∃ N : ℕ, A.IsLocalOfOrder (Y x) N }
      zero_mem' := ⟨0, by rw [map_zero]; exact IsLocalOfOrder.zero_right A 0⟩
      add_mem' := fun ⟨M, hM⟩ ⟨N, hN⟩ ↦
        ⟨max M N, by rw [map_add]; exact hM.add_right hN⟩
      smul_mem' := fun r x ⟨N, hN⟩ ↦
        ⟨N, by rw [map_smul]; exact IsLocalOfOrder.smul_right r hN⟩ }
  have hW_vac : vac ∈ W := ⟨0, hY_vac ▸ (isLocalOfOrder_idField_left A).symm⟩
  have hW_step : ∀ (i : ι) (n : ℤ), ∀ x ∈ W, ((F i)[[n]]) x ∈ W := by
    rintro i n x ⟨t, ht⟩
    have hprod_mem := nthProduct_generator_mem_goodFields hcov hloc i n (hY_mem x)
    have hprod_eval : ((nthProduct n (F i) (Y x))[[-1]]) vac = ((F i)[[n]]) x := by
      rw [ncoeff_neg_one_nthProduct_apply
            (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT (hcov i) hm)
            (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT (hY_mem x).1 hm) n,
          hY_eval]
    have hY_prod : Y (((F i)[[n]]) x) = nthProduct n (F i) (Y x) := by
      rw [← hprod_eval]
      exact hY_eq hprod_mem
    obtain ⟨s, hs⟩ := hA.2 i
    obtain ⟨r, hr⟩ := (hY_mem x).2 i
    exact ⟨_, hY_prod ▸ IsLocalOfOrder.nthProduct_right hs ht hr.symm n⟩
  exact Submodule.eq_top_iff'.mp (hgen W hW_vac hW_step) b

/-- **Reconstruction (extension) theorem for formal vertex algebras.** Given a vacuum vector `vac`,
an endomorphism `T` with `T vac = 0`, and a family of pairwise mutually local fields `F i` on an
`R`-module `V` over a `ℚ`-algebra `R` such that `[T, (F i)[[n]]] = (∂(F i))[[n]]` and `V` is
generated as an `R`-submodule from `vac` by the modes `(F i)[[n]]` (`n : ℤ`), there is a canonical
formal vertex algebra structure on `V` with vacuum `vac`, translation `T`, and
`Y(((F i)[[-1]]) vac, z) = F i`. -/
def ofGeneratingFields (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    FormalVertexAxioms R V :=
  have := hasUniqueDiv_of_algebra_rat R V
  let e : goodFields T F ≃ₗ[R] V :=
    LinearEquiv.ofBijective (evalVacuum vac T F) (evalVacuum_bijective vac T F hT hcov hloc hgen)
  let Y : V →ₗ[R] VertexOperator R V := (goodFields T F).subtype.comp e.symm.toLinearMap
  have hY_mem (a : V) : Y a ∈ goodFields T F := (e.symm a).2
  have hY_eval (a : V) : ((Y a)[[-1]]) vac = a := e.apply_symm_apply a
  have hY_eq {B : VertexOperator R V} (hB : B ∈ goodFields T F) :
      Y ((B[[-1]]) vac) = B :=
    congr_arg Subtype.val (e.symm_apply_eq.mpr rfl : e.symm (e ⟨B, hB⟩) = ⟨B, hB⟩)
  have hY_vac : Y vac = idField := by
    have hid : ((idField (R := R) (V := V))[[-1]]) vac = vac := by simp [ncoeff_idField]
    simpa only [hid] using hY_eq (idField_mem_goodFields T F)
  { field := Y
    vacuum := vac
    translation := T
    translation_vacuum := hT
    ncoeff_field_vacuum n := by rw [hY_vac, ncoeff_idField]
    ncoeff_field_apply_vacuum_of_nonneg a n hn :=
      ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT (hY_mem a).1 hn
    ncoeff_neg_one_field_apply_vacuum := hY_eval
    field_translation a := by
      have hd_eval : ((derivative (Y a))[[-1]]) vac = T a := by
        have h := LinearMap.congr_fun ((hY_mem a).1 (-1)) vac
        rw [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, hT,
          map_zero, sub_zero, hY_eval] at h
        exact h.symm
      rw [← hd_eval]
      exact hY_eq (derivative_mem_goodFields (hY_mem a))
    lie_translation_ncoeff a := (hY_mem a).1
    exists_isLocalOfOrder a b :=
      exists_isLocalOfOrder_of_mem_goodFields hT hcov hloc hgen hY_mem hY_eval hY_eq hY_vac
        (hY_mem a) b }

/-- The vacuum of `ofGeneratingFields` is the given vector `vac`. -/
@[simp]
theorem ofGeneratingFields_vacuum (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).vacuum = vac :=
  (rfl)

/-- The translation operator of `ofGeneratingFields` is the given endomorphism `T`. -/
@[simp]
theorem ofGeneratingFields_translation (vac : V) (T : Module.End R V)
    (F : ι → VertexOperator R V) (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).translation = T :=
  (rfl)

/-- Reconstructed state–field assignment on the generating states `((F i)[[-1]]) vac`. -/
@[simp]
theorem ofGeneratingFields_field_apply_generator (vac : V) (T : Module.End R V)
    (F : ι → VertexOperator R V) (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) (i : ι) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).field (((F i)[[-1]]) vac) = F i := by
  let e : goodFields T F ≃ₗ[R] V :=
    LinearEquiv.ofBijective (evalVacuum vac T F) (evalVacuum_bijective vac T F hT hcov hloc hgen)
  exact congr_arg Subtype.val
    (e.symm_apply_eq.mpr rfl : e.symm (e ⟨F i, generator_mem_goodFields hcov hloc i⟩) = _)

/-- **Uniqueness in the reconstruction theorem.** Any formal vertex algebra on `V` with vacuum
`vac` whose state–field map assigns `F i` to `((F i)[[-1]]) vac` for each `i` equals
`ofGeneratingFields`. -/
theorem eq_of_generatingFields (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    {A : FormalVertexAxioms R V} (hvac : A.vacuum = vac)
    (hF : ∀ i : ι, A.field (((F i)[[-1]]) vac) = F i) :
    A = ofGeneratingFields vac T F hT hcov hloc hgen := by
  let G := ofGeneratingFields vac T F hT hcov hloc hgen
  refine FormalVertexAxioms.ext ?_
  rw [← LinearMap.eqLocus_eq_top]
  refine hgen (LinearMap.eqLocus A.field G.field) ?_ ?_
  · rw [LinearMap.mem_eqLocus]
    refine ext_ncoeff fun n ↦ ?_
    have hGvac : G.vacuum = vac := rfl
    rw [← hGvac, G.ncoeff_field_vacuum, hGvac, ← hvac, A.ncoeff_field_vacuum]
  · intro i n v hv
    rw [LinearMap.mem_eqLocus] at hv ⊢
    have hGi : G.field (((F i)[[-1]]) vac) = F i :=
      ofGeneratingFields_field_apply_generator vac T F hT hcov hloc hgen i
    calc
      A.field (((F i)[[n]]) v) =
          A.field (((A.field (((F i)[[-1]]) vac))[[n]]) v) := by rw [hF i]
      _ = nthProduct n (F i) (A.field v) := by rw [A.field_ncoeff_apply, hF i]
      _ = nthProduct n (F i) (G.field v) := by rw [hv]
      _ = G.field (((G.field (((F i)[[-1]]) vac))[[n]]) v) := by rw [G.field_ncoeff_apply, hGi]
      _ = G.field (((F i)[[n]]) v) := by rw [hGi]

/-- **Existence and uniqueness of the reconstructed formal vertex algebra.** -/
theorem existsUnique_of_generatingFields (vac : V) (T : Module.End R V)
    (F : ι → VertexOperator R V) (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    ∃! A : FormalVertexAxioms R V,
      A.vacuum = vac ∧ A.translation = T ∧ ∀ i : ι, A.field (((F i)[[-1]]) vac) = F i :=
  ⟨ofGeneratingFields vac T F hT hcov hloc hgen,
    ⟨rfl, rfl, ofGeneratingFields_field_apply_generator vac T F hT hcov hloc hgen⟩,
    fun _ ⟨hvac, _, hF⟩ ↦ eq_of_generatingFields vac T F hT hcov hloc hgen hvac hF⟩

end Reconstruction

end TauCeti.FormalVertexAxioms
