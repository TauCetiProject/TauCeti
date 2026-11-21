/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.StateFieldProduct

/-!
# The reconstruction theorem for formal vertex algebras

Let `V` be a module with unique divisibility (for instance a `ℚ`-module) over a commutative ring
`R`, with a vector `vac`, an endomorphism `T` with `T vac = 0`, and a family of fields
`F i : VertexOperator R V` that are

* translation covariant: `⁅T, (F i)₍ₙ₎⁆ = (∂ F i)₍ₙ₎`;
* pairwise mutually local;
* generating: every submodule containing `vac` and stable under all modes `(F i)₍ₙ₎` is `V`.

The **reconstruction theorem** (Kac's extension theorem) says that there is a unique formal vertex
algebra on `V` with vacuum `vac`, translation `T` and `Y((F i)₍₋₁₎ vac, z) = F i`
(`TauCeti.FormalVertexAxioms.ofGeneratingFields`, `TauCeti.existsUnique_formalVertexAxioms`). Its
fields are computed by iterated `n`-th products: `Y((F i)₍ₙ₎ b, z) = (F i)₍ₙ₎ Y(b, z)`
(`TauCeti.FormalVertexAxioms.ofGeneratingFields_field_ncoeff_apply`). The theorem puts vertex
algebra structures on modules generated from a vacuum by local fields, such as the vacuum modules
of affine and Heisenberg Lie algebras.

Lower truncation and covariance already force `(F i)₍ₙ₎ vac = 0` for `n ≥ 0`
(`VertexOperator.ncoeff_apply_of_nonneg`), so no creation hypothesis is needed. The vacuum may be
zero, in which case generation forces `V = 0`.

## Implementation notes

Call a field *admissible* if it is local with every `F i`, translation covariant, and its
nonnegative modes kill `vac`. Admissible fields form a submodule, containing the identity field
and closed under `B ↦ (F i)₍ₙ₎ B` (Dong's lemma, `VertexOperator.IsLocalOfOrder.nthProduct_left`)
and under `∂`. The linear map `B ↦ B₍₋₁₎ vac` is

* injective on admissible fields: covariance gives `k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac)`, and a field
  local with every `F i` whose modes all kill `vac` kills a generating, hence the whole, space
  (`VertexOperator.IsLocalOfOrder.ncoeff_apply_ncoeff_apply_eq_zero`);
* surjective already on the span of the iterated products `(F i₁)₍ₙ₁₎ ⋯ (F iₖ)₍ₙₖ₎ 1`, whose
  image is generated from `vac` by the modes of the `F i`.

The state–field map `Y` is its inverse. The iterated products are mutually local by Dong's lemma,
which gives locality of `Y`; the other axioms are checked on the vacuum through injectivity.

## Main definitions

* `TauCeti.FormalVertexAxioms.ofGeneratingFields`: the formal vertex algebra reconstructed from
  generating fields.

## Main results

* `TauCeti.FormalVertexAxioms.ofGeneratingFields_field_ncoeff_neg_one_apply_vacuum`:
  `Y((F i)₍₋₁₎ vac, z) = F i`.
* `TauCeti.FormalVertexAxioms.ofGeneratingFields_field_ncoeff_apply`:
  `Y((F i)₍ₙ₎ b, z) = (F i)₍ₙ₎ Y(b, z)`.
* `TauCeti.FormalVertexAxioms.eq_ofGeneratingFields`: any formal vertex algebra with vacuum `vac`,
  translation `T` and these generating fields is the reconstructed one.
* `TauCeti.existsUnique_formalVertexAxioms`: the reconstruction theorem.

## References

* V. Kac, *Introduction to vertex algebras, Poisson vertex algebras, and integrable Hamiltonian
  PDE*, Theorem 1.1 (the extension theorem).
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., Theorem 4.5.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., Theorem 2.3.11.
-/

public section

noncomputable section

open scoped VertexOperator
open VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {ι : Type*} {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}

/-! ### Admissible fields -/

variable (vac T F) in
/-- The admissible fields: local with every generating field, translation covariant, and with
nonnegative modes killing `vac`. -/
private def admissible : Submodule R (VertexOperator R V) where
  carrier := {B | (∀ i, ∃ N, B.IsLocalOfOrder (F i) N) ∧
    (∀ k : ℤ, ⁅T, B[[k]]⁆ = (derivative B)[[k]]) ∧ ∀ n : ℤ, 0 ≤ n → (B[[n]]) vac = 0}
  zero_mem' := ⟨fun i ↦ ⟨0, .zero_left _ 0⟩, fun k ↦ by simp [Ring.lie_def], fun n _ ↦ by simp⟩
  add_mem' {B B'} hB hB' := by
    refine ⟨fun i ↦ ?_, fun k ↦ ?_, fun n hn ↦ ?_⟩
    · obtain ⟨N, hN⟩ := hB.1 i
      obtain ⟨N', hN'⟩ := hB'.1 i
      exact ⟨max N N', (hN.mono (le_max_left N N')).add_left (hN'.mono (le_max_right N N'))⟩
    · have h := hB.2.1 k
      have h' := hB'.2.1 k
      rw [Ring.lie_def] at h h' ⊢
      simp only [map_add, Pi.add_apply, mul_add, add_mul, ← h, ← h']
      abel
    · simp [hB.2.2 n hn, hB'.2.2 n hn]
  smul_mem' r B hB := by
    refine ⟨fun i ↦ ?_, fun k ↦ ?_, fun n hn ↦ ?_⟩
    · obtain ⟨N, hN⟩ := hB.1 i
      exact ⟨N, hN.smul_left r⟩
    · have h := hB.2.1 k
      rw [Ring.lie_def] at h ⊢
      simp only [map_smul, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, ← h, smul_sub]
    · simp [hB.2.2 n hn]

variable (vac) in
/-- The `(-1)`-st mode on the vacuum, `B ↦ B₍₋₁₎ vac`, which inverts the state–field map. -/
private def vacuumCoeff : VertexOperator R V →ₗ[R] V :=
  (LinearMap.applyₗ vac).comp ((LinearMap.proj (-1 : ℤ)).comp ncoeff)

private theorem vacuumCoeff_apply (B : VertexOperator R V) :
    vacuumCoeff vac B = (B[[-1]]) vac :=
  (rfl)

private theorem vacuumCoeff_idField : vacuumCoeff vac (idField : VertexOperator R V) = vac := by
  simp [vacuumCoeff_apply, ncoeff_idField]

private theorem idField_mem_admissible :
    (idField : VertexOperator R V) ∈ admissible vac T F := by
  refine ⟨fun i ↦ ⟨0, isLocalOfOrder_idField _⟩, fun k ↦ ?_, fun n hn ↦ ?_⟩
  · rw [derivative_idField, ncoeff_idField]
    split_ifs <;> simp [Ring.lie_def]
  · simp [ncoeff_idField, show n ≠ -1 by omega]

/-- A generating field is admissible. -/
private theorem mem_admissible [HasUniqueDiv V] (hT : T vac = 0)
    (hcov : ∀ i (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N) (i : ι) :
    F i ∈ admissible vac T F :=
  ⟨hloc i, hcov i, fun _ hn ↦ ncoeff_apply_of_nonneg hT (hcov i) hn⟩

/-- Admissible fields are closed under `B ↦ (F i)₍ₙ₎ B`. -/
private theorem nthProduct_mem_admissible [HasUniqueDiv V] (hT : T vac = 0)
    (hcov : ∀ i (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N) {B : VertexOperator R V}
    (hB : B ∈ admissible vac T F) (i : ι) (n : ℤ) :
    nthProduct n (F i) B ∈ admissible vac T F := by
  refine ⟨fun j ↦ ?_, lie_ncoeff_nthProduct (hcov i) hB.2.1 n, fun m hm ↦ ?_⟩
  · obtain ⟨r₀, h₀⟩ := hB.1 i
    obtain ⟨r₁, h₁⟩ := hloc i j
    obtain ⟨r₂, h₂⟩ := hB.1 j
    exact ⟨_, h₀.symm.nthProduct_left h₁ h₂ n⟩
  · exact ncoeff_nthProduct_apply_of_nonneg (fun k hk ↦ ncoeff_apply_of_nonneg hT (hcov i) hk)
      hB.2.2 n hm

/-- Admissible fields are closed under `∂`. -/
private theorem derivative_mem_admissible {B : VertexOperator R V}
    (hB : B ∈ admissible vac T F) : derivative B ∈ admissible vac T F := by
  refine ⟨fun i ↦ ?_, fun k ↦ ?_, fun n hn ↦ ?_⟩
  · obtain ⟨N, hN⟩ := hB.1 i
    exact ⟨N + 1, hN.derivative_left⟩
  · rw [ncoeff_derivative, ncoeff_derivative, ← hB.2.1, Ring.lie_def, Ring.lie_def,
      mul_smul_comm, smul_mul_assoc, smul_sub]
  · rcases hn.eq_or_lt with rfl | hn
    · simp
    · rw [ncoeff_derivative, LinearMap.smul_apply, hB.2.2 (n - 1) (by omega), smul_zero]

/-- `T` acts on `B₍₋₁₎ vac` through `∂`: `T (B₍₋₁₎ vac) = (∂B)₍₋₁₎ vac`. -/
private theorem vacuumCoeff_derivative (hT : T vac = 0) {B : VertexOperator R V}
    (hB : B ∈ admissible vac T F) :
    vacuumCoeff vac (derivative B) = T (vacuumCoeff vac B) := by
  rw [vacuumCoeff_apply, vacuumCoeff_apply, apply_ncoeff_apply_of_lie hT hB.2.1, ncoeff_derivative,
    LinearMap.smul_apply]

/-- **Uniqueness.** An admissible field `B` with `B₍₋₁₎ vac = 0` vanishes. -/
private theorem eq_zero_of_mem_admissible [HasUniqueDiv V] (hT : T vac = 0)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    {B : VertexOperator R V} (hB : B ∈ admissible vac T F) (h₀ : vacuumCoeff vac B = 0) :
    B = 0 := by
  -- Every mode of `B` kills `vac`: the nonnegative ones by admissibility, the negative ones by
  -- `k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac) = 0`.
  have hvac (n : ℤ) : (B[[n]]) vac = 0 := by
    rcases le_or_gt 0 n with hn | hn
    · exact hB.2.2 n hn
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
      refine nsmul_right_injective k.factorial_ne_zero ?_
      beta_reduce
      rw [factorial_smul_ncoeff_apply hT hB.2.1 k, ← vacuumCoeff_apply, h₀, map_zero, smul_zero]
  -- The vectors killed by every mode of `B` form a generating subspace, hence all of `V`.
  let W : Submodule R V := ⨅ n : ℤ, LinearMap.ker (B[[n]])
  have hW : W = ⊤ := by
    refine hgen W (Submodule.mem_iInf _ |>.2 fun n ↦ hvac n) fun i n v hv ↦ ?_
    obtain ⟨N, hN⟩ := hB.1 i
    exact Submodule.mem_iInf _ |>.2 fun m ↦ hN.ncoeff_apply_ncoeff_apply_eq_zero
      (fun k ↦ (Submodule.mem_iInf _).1 hv k) m n
  refine ext_ncoeff fun n ↦ LinearMap.ext fun v ↦ ?_
  have hv : v ∈ W := hW ▸ Submodule.mem_top
  simpa using (Submodule.mem_iInf _).1 hv n

/-! ### Iterated products of the generating fields -/

variable (F) in
/-- The iterated products `(F i₁)₍ₙ₁₎ ((F i₂)₍ₙ₂₎ ⋯ ((F iₖ)₍ₙₖ₎ 1))` of the generating fields. -/
private def iteratedProduct : List (ι × ℤ) → VertexOperator R V
  | [] => idField
  | p :: l => nthProduct p.2 (F p.1) (iteratedProduct l)

private theorem iteratedProduct_mem_admissible [HasUniqueDiv V] (hT : T vac = 0)
    (hcov : ∀ i (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N) (l : List (ι × ℤ)) :
    iteratedProduct F l ∈ admissible vac T F := by
  induction l with
  | nil => exact idField_mem_admissible
  | cons p l ih => exact nthProduct_mem_admissible hT hcov hloc ih p.1 p.2

/-- The span of the iterated products consists of admissible fields. -/
private theorem span_iteratedProduct_le_admissible [HasUniqueDiv V] (hT : T vac = 0)
    (hcov : ∀ i (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N) :
    Submodule.span R (Set.range (iteratedProduct F)) ≤ admissible vac T F :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 (iteratedProduct_mem_admissible hT hcov hloc)

/-- Iterated products of the generating fields are local with every generating field, by Dong's
lemma. -/
private theorem exists_isLocalOfOrder_iteratedProduct_left
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N) (l : List (ι × ℤ)) (j : ι) :
    ∃ N, (iteratedProduct F l).IsLocalOfOrder (F j) N := by
  induction l generalizing j with
  | nil => exact ⟨0, isLocalOfOrder_idField _⟩
  | cons p l ih =>
    obtain ⟨r₀, h₀⟩ := ih p.1
    obtain ⟨r₁, h₁⟩ := hloc p.1 j
    obtain ⟨r₂, h₂⟩ := ih j
    exact ⟨_, h₀.symm.nthProduct_left h₁ h₂ p.2⟩

/-- Iterated products of the generating fields are mutually local, by Dong's lemma. -/
private theorem exists_isLocalOfOrder_iteratedProduct
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N) (l l' : List (ι × ℤ)) :
    ∃ N, (iteratedProduct F l).IsLocalOfOrder (iteratedProduct F l') N := by
  induction l with
  | nil => exact ⟨0, isLocalOfOrder_idField _⟩
  | cons p l ih =>
    obtain ⟨r₀, h₀⟩ := exists_isLocalOfOrder_iteratedProduct_left hloc l p.1
    obtain ⟨r₁, h₁⟩ := exists_isLocalOfOrder_iteratedProduct_left hloc l' p.1
    obtain ⟨r₂, h₂⟩ := ih
    exact ⟨_, h₀.symm.nthProduct_left h₁.symm h₂ p.2⟩

/-- The `(-1)`-st modes on the vacuum of the iterated products exhaust `V`. -/
private theorem map_vacuumCoeff_span_iteratedProduct [HasUniqueDiv V] (hT : T vac = 0)
    (hcov : ∀ i (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    (Submodule.span R (Set.range (iteratedProduct F))).map (vacuumCoeff vac) = ⊤ := by
  set S := Submodule.span R (Set.range (iteratedProduct F))
  have hS : S ≤ admissible vac T F := span_iteratedProduct_le_admissible hT hcov hloc
  refine hgen _ ⟨idField, Submodule.subset_span ⟨[], rfl⟩, vacuumCoeff_idField⟩ ?_
  rintro i n _ ⟨B, hB, rfl⟩
  -- `S` is stable under `B ↦ (F i)₍ₙ₎ B`, which acts on `B₍₋₁₎ vac` as `(F i)₍ₙ₎`.
  have hmap : S ≤ S.comap (nthProduct n (F i)) :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun l ↦ Submodule.subset_span ⟨(i, n) :: l, rfl⟩
  refine ⟨nthProduct n (F i) B, hmap hB, ?_⟩
  rw [vacuumCoeff_apply, vacuumCoeff_apply, ncoeff_neg_one_nthProduct_apply
    (fun k hk ↦ ncoeff_apply_of_nonneg hT (hcov i) hk) (hS hB).2.2]

/-- The inverse of the state–field map: admissible fields are identified with `V` by
`B ↦ B₍₋₁₎ vac`. -/
private def admissibleEquiv [HasUniqueDiv V] (hT : T vac = 0)
    (hcov : ∀ i (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    admissible vac T F ≃ₗ[R] V :=
  LinearEquiv.ofBijective ((vacuumCoeff vac).comp (admissible vac T F).subtype)
    ⟨(injective_iff_map_eq_zero _).2 fun B hB ↦ Subtype.ext <|
        eq_zero_of_mem_admissible hT hgen B.property hB, fun a ↦ by
      obtain ⟨B, hB, rfl⟩ : a ∈ _ :=
        (map_vacuumCoeff_span_iteratedProduct hT hcov hloc hgen).symm ▸ Submodule.mem_top
      exact ⟨⟨B, span_iteratedProduct_le_admissible hT hcov hloc hB⟩, rfl⟩⟩

/-! ### The reconstructed formal vertex algebra -/

section Reconstruction

variable [HasUniqueDiv V] (hT : T vac = 0)
  (hcov : ∀ i (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
  (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
  (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)

/-- The reconstructed state–field map: `Y(a, z)` is the unique admissible field `B` with
`B₍₋₁₎ vac = a`. -/
private def reconstructField : V →ₗ[R] VertexOperator R V :=
  (admissible vac T F).subtype.comp (admissibleEquiv hT hcov hloc hgen).symm.toLinearMap

private theorem reconstructField_mem (a : V) :
    reconstructField hT hcov hloc hgen a ∈ admissible vac T F :=
  ((admissibleEquiv hT hcov hloc hgen).symm a).property

private theorem vacuumCoeff_reconstructField (a : V) :
    vacuumCoeff vac (reconstructField hT hcov hloc hgen a) = a :=
  (admissibleEquiv hT hcov hloc hgen).apply_symm_apply a

/-- An admissible field is the reconstructed field of its `(-1)`-st mode on the vacuum. -/
private theorem reconstructField_vacuumCoeff {B : VertexOperator R V}
    (hB : B ∈ admissible vac T F) :
    reconstructField hT hcov hloc hgen (vacuumCoeff vac B) = B :=
  congrArg Subtype.val ((admissibleEquiv hT hcov hloc hgen).symm_apply_apply ⟨B, hB⟩)

/-- Reconstructed fields lie in the span of the iterated products of the generating fields. -/
private theorem reconstructField_mem_span (a : V) :
    reconstructField hT hcov hloc hgen a ∈ Submodule.span R (Set.range (iteratedProduct F)) := by
  obtain ⟨B, hB, rfl⟩ : a ∈ _ :=
    (map_vacuumCoeff_span_iteratedProduct hT hcov hloc hgen).symm ▸ Submodule.mem_top
  rwa [reconstructField_vacuumCoeff hT hcov hloc hgen
    (span_iteratedProduct_le_admissible hT hcov hloc hB)]

/-- **Reconstruction.** The formal vertex algebra generated by mutually local, translation
covariant fields `F i` from a vacuum `vac` killed by `T`, with `Y((F i)₍₋₁₎ vac, z) = F i`
(`ofGeneratingFields_field_ncoeff_neg_one_apply_vacuum`). -/
def ofGeneratingFields : FormalVertexAxioms R V where
  field := reconstructField hT hcov hloc hgen
  vacuum := vac
  translation := T
  translation_vacuum := hT
  ncoeff_field_vacuum n := by
    have h := reconstructField_vacuumCoeff hT hcov hloc hgen idField_mem_admissible
    rw [vacuumCoeff_idField] at h
    rw [h, ncoeff_idField]
  ncoeff_field_apply_vacuum_of_nonneg a := (reconstructField_mem hT hcov hloc hgen a).2.2
  ncoeff_neg_one_field_apply_vacuum := vacuumCoeff_reconstructField hT hcov hloc hgen
  field_translation a := by
    have ha := reconstructField_mem hT hcov hloc hgen a
    rw [← reconstructField_vacuumCoeff hT hcov hloc hgen (derivative_mem_admissible ha),
      vacuumCoeff_derivative hT ha, vacuumCoeff_reconstructField]
  lie_translation_ncoeff a := (reconstructField_mem hT hcov hloc hgen a).2.1
  exists_isLocalOfOrder a b := exists_isLocalOfOrder_of_mem_span
    (by
      rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩
      exact exists_isLocalOfOrder_iteratedProduct hloc l l')
    (reconstructField_mem_span hT hcov hloc hgen a) (reconstructField_mem_span hT hcov hloc hgen b)

/-- The vacuum of the reconstructed formal vertex algebra is `vac`. -/
@[simp]
theorem ofGeneratingFields_vacuum : (ofGeneratingFields hT hcov hloc hgen).vacuum = vac :=
  (rfl)

/-- The translation operator of the reconstructed formal vertex algebra is `T`. -/
@[simp]
theorem ofGeneratingFields_translation : (ofGeneratingFields hT hcov hloc hgen).translation = T :=
  (rfl)

/-- The reconstructed field of the state `(F i)₍₋₁₎ vac` is the generating field `F i`. -/
@[simp]
theorem ofGeneratingFields_field_ncoeff_neg_one_apply_vacuum (i : ι) :
    (ofGeneratingFields hT hcov hloc hgen).field (((F i)[[-1]]) vac) = F i :=
  reconstructField_vacuumCoeff hT hcov hloc hgen (mem_admissible hT hcov hloc i)

/-- The reconstructed fields are iterated products of the generating fields:
`Y((F i)₍ₙ₎ b, z) = (F i)₍ₙ₎ Y(b, z)`. -/
theorem ofGeneratingFields_field_ncoeff_apply (i : ι) (n : ℤ) (b : V) :
    (ofGeneratingFields hT hcov hloc hgen).field (((F i)[[n]]) b) =
      nthProduct n (F i) ((ofGeneratingFields hT hcov hloc hgen).field b) := by
  conv_lhs => rw [← ofGeneratingFields_field_ncoeff_neg_one_apply_vacuum hT hcov hloc hgen i]
  rw [field_ncoeff_apply, ofGeneratingFields_field_ncoeff_neg_one_apply_vacuum]

/-- **Uniqueness in the reconstruction theorem.** A formal vertex algebra with vacuum `vac`,
translation `T` and `Y((F i)₍₋₁₎ vac, z) = F i` is `ofGeneratingFields`. -/
theorem eq_ofGeneratingFields {A : FormalVertexAxioms R V} (hvac : A.vacuum = vac)
    (htr : A.translation = T) (hF : ∀ i, A.field (((F i)[[-1]]) vac) = F i) :
    A = ofGeneratingFields hT hcov hloc hgen := by
  subst hvac htr
  ext1
  refine LinearMap.ext fun a ↦ ?_
  have ha : A.field a ∈ admissible A.vacuum A.translation F :=
    ⟨fun i ↦ hF i ▸ A.exists_isLocalOfOrder a _, A.lie_translation_ncoeff a,
      A.ncoeff_field_apply_vacuum_of_nonneg a⟩
  have h := reconstructField_vacuumCoeff hT hcov hloc hgen ha
  rw [vacuumCoeff_apply, A.ncoeff_neg_one_field_apply_vacuum] at h
  exact h.symm

end Reconstruction

end FormalVertexAxioms

/-- **The reconstruction theorem** (Kac's extension theorem). If `V` has unique divisibility,
`T vac = 0`, and the fields `F i` are translation covariant, pairwise mutually local and generate
`V` from `vac`, then there is a unique formal vertex algebra on `V` with vacuum `vac`, translation
`T` and `Y((F i)₍₋₁₎ vac, z) = F i`. -/
theorem existsUnique_formalVertexAxioms {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [HasUniqueDiv V] {ι : Type*} {vac : V} {T : Module.End R V} {F : ι → VertexOperator R V}
    (hT : T vac = 0) (hcov : ∀ i (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j, ∃ N, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W → (∀ i (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    ∃! A : FormalVertexAxioms R V, A.vacuum = vac ∧ A.translation = T ∧
      ∀ i, A.field (((F i)[[-1]]) vac) = F i :=
  ⟨FormalVertexAxioms.ofGeneratingFields hT hcov hloc hgen,
    ⟨FormalVertexAxioms.ofGeneratingFields_vacuum hT hcov hloc hgen,
      FormalVertexAxioms.ofGeneratingFields_translation hT hcov hloc hgen,
      FormalVertexAxioms.ofGeneratingFields_field_ncoeff_neg_one_apply_vacuum hT hcov hloc hgen⟩,
    fun _ ⟨hvac, htr, hF⟩ ↦ FormalVertexAxioms.eq_ofGeneratingFields hT hcov hloc hgen hvac htr hF⟩

end TauCeti
