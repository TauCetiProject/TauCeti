/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Isotypic
public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.UnitarizingMatrix
public import TauCeti.Algebra.Coalgebra.Star
public import TauCeti.Algebra.HopfAlgebra.Integral.Haar
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Coalgebra.Comodule.Conjugate
import TauCeti.Algebra.Coalgebra.Comodule.Unitary.SchurOrthogonality
import TauCeti.Algebra.HopfAlgebra.Integral.CompactType

/-!
# The modular automorphism of an algebraic Haar functional

Let `h` be an algebraic Haar functional (`TauCeti.AlgebraicHaar`) on a complex Hopf star algebra
`A`. Then there is exactly one algebra automorphism `θ` of `A` with `h (a * b) = h (b * θ a)` for
all `a` and `b` (`TauCeti.haar_modular_automorphism`). This is the modular automorphism of the
Haar functional; `h` is a trace exactly when `θ` is the identity
(`TauCeti.AlgebraicHaar.modularAut_eq_refl_iff`).

Uniqueness is algebraic faithfulness of the invariant integral. Existence uses the Peter–Weyl
structure of `A`: `A` is spanned by the coefficient spaces `P` of its simple comodules, which are
finite-dimensional. Haar orthogonality of distinct blocks
(`TauCeti.AlgebraicHaar.map_star_mul_eq_zero_of_mem_simpleCoefficientSubmodules`) shows that for
`a, c ∈ P` both functionals `h (a * ·)` and `h (· * c)` vanish off the conjugate block `star P`.
By faithfulness, `a ↦ h (a * ·)` and `c ↦ h (· * c)` are then two injective linear maps from `P`
into the dual of `star P`, and the same maps for `star P` give the reverse dimension inequality.
So both maps are bijective, and every `h (a * ·)` is some `h (· * c)` with `c` in the same block.
In particular `θ` preserves every simple coefficient space
(`TauCeti.AlgebraicHaar.modularAut_mem_of_mem_simpleCoefficientSubmodules`).

On the coefficient matrix `u` of a simple comodule in a basis where `u` is unitary, `θ` acts by
`θ(u) = F u F`, where `F` is the transpose of the normalized unitarizing matrix `Ft` of weighted
Schur orthogonality (`TauCeti.AlgebraicHaar.map_modularAut_coefficientMatrix`). Both sides lie in
the coefficient space of `u`, and the Schur orthogonality relations show that they pair in the same
way with every `star (u k l)`; Haar orthogonality of distinct blocks and faithfulness of `h` then
identify them.

The construction of `θ` as an algebra automorphism adapts that of the Nakayama automorphism of a
Frobenius functional (`LinearMap.IsFrobeniusFunctional.nakayamaAut`): a linear map characterized by
the pairing identity, made unital and multiplicative by faithfulness. In infinite dimension there
is no perfect pairing, and the block-dimension argument above takes its place.

## Main declarations

* `TauCeti.AlgebraicHaar.modularAut`: the modular automorphism `θ` of an algebraic Haar
  functional, characterized by `TauCeti.AlgebraicHaar.apply_mul_modularAut` and
  `TauCeti.AlgebraicHaar.coe_modularAut_eq`.
* `TauCeti.haar_modular_automorphism`: there is exactly one algebra automorphism `θ` with
  `h (a * b) = h (b * θ a)`.
* `TauCeti.AlgebraicHaar.star_modularAut`: `star (θ a) = θ⁻¹ (star a)`.
* `TauCeti.AlgebraicHaar.modularAut_eq_refl_iff`: `θ` is the identity if and only if `h` is a
  trace.
* `TauCeti.AlgebraicHaar.map_modularAut_coefficientMatrix`: `θ(u) = F u F` on a unitary
  coefficient matrix of a simple comodule.

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.7.3.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
-/

public section

open Module

namespace TauCeti

open Comodule

universe u

variable {A : Type u} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A] [StarCoalgebra ℂ A]

namespace AlgebraicHaar

variable (h : AlgebraicHaar A)

/-- An identity `h (a * y) = h (y * c)` holding on every simple coefficient space holds on `A`. -/
private theorem apply_mul_eq_apply_mul_of_forall_mem {a c : A}
    (H : ∀ P ∈ simpleCoefficientSubmodules ℂ A, ∀ y ∈ P, h (a * y) = h (y * c)) (y : A) :
    h (a * y) = h (y * c) := by
  induction y using h.induction_simpleCoefficientSubmodules with
  | mem P hP y hy => exact H P hP y hy
  | zero => simp
  | add y y' hy hy' => simp [mul_add, add_mul, hy, hy']

section Block

/-! Throughout this section `P` and `P'` are simple coefficient spaces with `P' = star P`. -/

variable {P P' : Submodule ℂ A} (hP : P ∈ simpleCoefficientSubmodules ℂ A)
  (hP' : P' ∈ simpleCoefficientSubmodules ℂ A) (hstar : ∀ x, x ∈ P' ↔ star x ∈ P)

include hP' hstar in
/-- For `a ∈ P`, the functional `h (a * ·)` vanishes on every simple block other than `star P`. -/
private theorem apply_mul_eq_zero_of_ne {Q : Submodule ℂ A}
    (hQ : Q ∈ simpleCoefficientSubmodules ℂ A) (hQP' : Q ≠ P') {a y : A} (ha : a ∈ P)
    (hy : y ∈ Q) : h (a * y) = 0 := by
  simpa using h.map_star_mul_eq_zero_of_mem_simpleCoefficientSubmodules hP' hQ hQP'.symm
    ((hstar (star a)).mpr (by simpa using ha)) hy

include hP hstar in
/-- For `c ∈ P`, the functional `h (· * c)` vanishes on every simple block other than `star P`. -/
private theorem apply_mul_eq_zero_of_ne' {Q : Submodule ℂ A}
    (hQ : Q ∈ simpleCoefficientSubmodules ℂ A) (hQP' : Q ≠ P') {c y : A} (hc : c ∈ P)
    (hy : y ∈ Q) : h (y * c) = 0 := by
  have hQ'P : Q.comap (starLinearEquiv ℂ (A := A)).toLinearMap ≠ P := fun hEq ↦ hQP' <|
    Submodule.ext fun x ↦ by simp [hstar, ← hEq]
  simpa using h.map_star_mul_eq_zero_of_mem_simpleCoefficientSubmodules
    (comap_starLinearEquiv_mem_simpleCoefficientSubmodules hQ) hP hQ'P (x := star y)
    (by simpa using hy) hc

include hP hP' hstar in
/-- For `a, c ∈ P`, the identity `h (a * y) = h (y * c)` on `star P` holds on all of `A`. -/
private theorem apply_mul_eq_apply_mul_of_forall_mem_star {a c : A} (ha : a ∈ P) (hc : c ∈ P)
    (H : ∀ y ∈ P', h (a * y) = h (y * c)) (y : A) : h (a * y) = h (y * c) :=
  h.apply_mul_eq_apply_mul_of_forall_mem (fun Q hQ y hy ↦ by
    by_cases hQP' : Q = P'
    · exact H y (hQP' ▸ hy)
    · rw [h.apply_mul_eq_zero_of_ne hP' hstar hQ hQP' ha hy,
        h.apply_mul_eq_zero_of_ne' hP hstar hQ hQP' hc hy]) y

/-- The Haar pairing `(a, y) ↦ h (a * y)`. -/
private noncomputable def pairing : A →ₗ[ℂ] A →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ A).compr₂ h.toLinearMap

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
private theorem pairing_apply (a y : A) : h.pairing a y = h (a * y) := (rfl)

include hP hP' hstar in
/-- Left multiplication into the dual of `star P` is injective on `P`. -/
private theorem injective_pairing_domRestrict₁₂ :
    Function.Injective (h.pairing.domRestrict₁₂ P P') := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha ↦ Subtype.ext ?_
  refine h.isRightInvariantIntegral.eq_zero_of_forall_mul_eq_zero h.toLinearMap_ne_zero fun y ↦ ?_
  simpa using h.apply_mul_eq_apply_mul_of_forall_mem_star hP hP' hstar a.property P.zero_mem
    (fun y hy ↦ by
      simpa [pairing_apply, LinearMap.domRestrict₁₂_apply] using LinearMap.congr_fun ha ⟨y, hy⟩) y

include hP hP' hstar in
/-- Right multiplication into the dual of `star P` is injective on `P`. -/
private theorem injective_pairing_flip_domRestrict₁₂ :
    Function.Injective (h.pairing.flip.domRestrict₁₂ P P') := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ Subtype.ext ?_
  refine h.isLeftInvariantIntegral.eq_zero_of_forall_mul_eq_zero h.toLinearMap_ne_zero fun y ↦ ?_
  simpa using (h.apply_mul_eq_apply_mul_of_forall_mem_star hP hP' hstar P.zero_mem c.property
    (fun y hy ↦ by
      simpa [pairing_apply, LinearMap.domRestrict₁₂_apply] using
        (LinearMap.congr_fun hc ⟨y, hy⟩).symm) y).symm

include h hP hP' hstar in
private theorem finrank_le_finrank : finrank ℂ P ≤ finrank ℂ P' := by
  have := finite_of_mem_simpleCoefficientSubmodules hP'
  simpa [Subspace.dual_finrank_eq] using
    LinearMap.finrank_le_finrank_of_injective (h.injective_pairing_domRestrict₁₂ hP hP' hstar)

include h hP hP' hstar in
private theorem finrank_dual_eq : finrank ℂ P = finrank ℂ (Module.Dual ℂ P') := by
  have := finite_of_mem_simpleCoefficientSubmodules hP'
  rw [Subspace.dual_finrank_eq]
  exact le_antisymm (h.finrank_le_finrank hP hP' hstar) <|
    h.finrank_le_finrank hP' hP fun x ↦ by rw [hstar, star_star]

include hP hP' hstar in
/-- Every functional `h (a * ·)` with `a ∈ P` is a functional `h (· * c)` with `c ∈ P`. -/
private theorem exists_mem_forall_apply_mul_eq {a : A} (ha : a ∈ P) :
    ∃ c ∈ P, ∀ y, h (a * y) = h (y * c) := by
  have := finite_of_mem_simpleCoefficientSubmodules hP
  have := finite_of_mem_simpleCoefficientSubmodules hP'
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (h.finrank_dual_eq hP hP' hstar)).mp (h.injective_pairing_flip_domRestrict₁₂ hP hP' hstar)
    (h.pairing.domRestrict₁₂ P P' ⟨a, ha⟩)
  refine ⟨c, c.property, h.apply_mul_eq_apply_mul_of_forall_mem_star hP hP' hstar ha c.property fun
      y hy ↦ ?_⟩
  simpa [pairing_apply, LinearMap.domRestrict₁₂_apply] using (LinearMap.congr_fun hc ⟨y, hy⟩).symm

include hP hP' hstar in
/-- Every functional `h (· * c)` with `c ∈ P` is a functional `h (a * ·)` with `a ∈ P`. -/
private theorem exists_mem_forall_apply_mul_eq' {c : A} (hc : c ∈ P) :
    ∃ a ∈ P, ∀ y, h (a * y) = h (y * c) := by
  have := finite_of_mem_simpleCoefficientSubmodules hP
  have := finite_of_mem_simpleCoefficientSubmodules hP'
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (h.finrank_dual_eq hP hP' hstar)).mp (h.injective_pairing_domRestrict₁₂ hP hP' hstar)
    (h.pairing.flip.domRestrict₁₂ P P' ⟨c, hc⟩)
  refine ⟨a, a.property, h.apply_mul_eq_apply_mul_of_forall_mem_star hP hP' hstar a.property hc fun
      y hy ↦ ?_⟩
  simpa [pairing_apply, LinearMap.domRestrict₁₂_apply] using LinearMap.congr_fun ha ⟨y, hy⟩

end Block

private theorem exists_forall_apply_mul_eq (a : A) : ∃ c, ∀ y, h (a * y) = h (y * c) := by
  induction a using h.induction_simpleCoefficientSubmodules with
  | mem P hP a ha =>
    obtain ⟨c, -, hc⟩ := h.exists_mem_forall_apply_mul_eq hP
      (comap_starLinearEquiv_mem_simpleCoefficientSubmodules hP) (fun _ ↦ Iff.rfl) ha
    exact ⟨c, hc⟩
  | zero => exact ⟨0, by simp⟩
  | add a a' ha ha' =>
    obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := And.intro ha ha'
    exact ⟨c + c', fun y ↦ by simp [add_mul, mul_add, hc, hc']⟩

private theorem exists_forall_apply_mul_eq' (c : A) : ∃ a, ∀ y, h (a * y) = h (y * c) := by
  induction c using h.induction_simpleCoefficientSubmodules with
  | mem P hP c hc =>
    obtain ⟨a, -, ha⟩ := h.exists_mem_forall_apply_mul_eq' hP
      (comap_starLinearEquiv_mem_simpleCoefficientSubmodules hP) (fun _ ↦ Iff.rfl) hc
    exact ⟨a, ha⟩
  | zero => exact ⟨0, by simp⟩
  | add c c' hc hc' =>
    obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := And.intro hc hc'
    exact ⟨a + a', fun y ↦ by simp [add_mul, mul_add, ha, ha']⟩

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
/-- Faithfulness of `h` in the second factor. -/
private theorem eq_of_forall_apply_mul_eq {c c' : A} (H : ∀ y, h (y * c) = h (y * c')) :
    c = c' :=
  sub_eq_zero.mp <| h.isLeftInvariantIntegral.eq_zero_of_forall_mul_eq_zero
    h.toLinearMap_ne_zero fun y ↦ by simp [mul_sub, H]

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
/-- Faithfulness of `h` in the first factor. -/
private theorem eq_of_forall_apply_mul_eq' {a a' : A} (H : ∀ y, h (a * y) = h (a' * y)) :
    a = a' :=
  sub_eq_zero.mp <| h.isRightInvariantIntegral.eq_zero_of_forall_mul_eq_zero
    h.toLinearMap_ne_zero fun y ↦ by simp [sub_mul, H]

/-- The modular map: `a` goes to the element pairing from the right as `a` pairs from the left. -/
private noncomputable def modularFun (a : A) : A := (h.exists_forall_apply_mul_eq a).choose

private theorem apply_mul_modularFun (a y : A) : h (y * h.modularFun a) = h (a * y) :=
  ((h.exists_forall_apply_mul_eq a).choose_spec y).symm

/-- The modular map as a linear map. -/
private noncomputable def modularLinearMap : A →ₗ[ℂ] A where
  toFun := h.modularFun
  map_add' a a' := h.eq_of_forall_apply_mul_eq fun y ↦ by
    rw [mul_add, map_add, apply_mul_modularFun, apply_mul_modularFun, apply_mul_modularFun,
      add_mul, map_add]
  map_smul' z a := h.eq_of_forall_apply_mul_eq fun y ↦ by
    rw [mul_smul_comm, map_smul, apply_mul_modularFun, apply_mul_modularFun, RingHom.id_apply,
      smul_mul_assoc, map_smul]

private theorem apply_mul_modularLinearMap (a y : A) :
    h (y * h.modularLinearMap a) = h (a * y) :=
  h.apply_mul_modularFun a y

/-- The **modular automorphism** of an algebraic Haar functional `h`: the unique map `θ` with
`h (b * θ a) = h (a * b)` for all `a` and `b` (`TauCeti.AlgebraicHaar.apply_mul_modularAut`,
`TauCeti.AlgebraicHaar.coe_modularAut_eq`). It is an algebra automorphism. -/
noncomputable def modularAut : A ≃ₐ[ℂ] A :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap h.modularLinearMap
      (h.eq_of_forall_apply_mul_eq fun y ↦ by rw [apply_mul_modularLinearMap, one_mul, mul_one])
      fun x z ↦ h.eq_of_forall_apply_mul_eq fun y ↦ by
        -- `h (y * θ (x * z)) = h (x * (z * y)) = h (y * (θ x * θ z))`, one factor at a time.
        rw [apply_mul_modularLinearMap, ← mul_assoc, apply_mul_modularLinearMap, ← mul_assoc,
          apply_mul_modularLinearMap, mul_assoc])
    ⟨fun a a' haa' ↦ h.eq_of_forall_apply_mul_eq' fun y ↦ by
        simp only [AlgHom.ofLinearMap_apply] at haa'
        rw [← apply_mul_modularLinearMap, haa', apply_mul_modularLinearMap],
      fun c ↦ by
        obtain ⟨a, ha⟩ := h.exists_forall_apply_mul_eq' c
        exact ⟨a, h.eq_of_forall_apply_mul_eq fun y ↦ by
          rw [AlgHom.ofLinearMap_apply, apply_mul_modularLinearMap, ha]⟩⟩

/-- The defining identity of the modular automorphism: `h (b * θ a) = h (a * b)`. -/
@[simp]
theorem apply_mul_modularAut (a b : A) : h (b * h.modularAut a) = h (a * b) :=
  h.apply_mul_modularLinearMap a b

/-- The defining identity of the inverse modular automorphism: `h (θ⁻¹ a * b) = h (b * a)`. -/
@[simp]
theorem apply_modularAut_symm_mul (a b : A) : h (h.modularAut.symm a * b) = h (b * a) := by
  simpa using (h.apply_mul_modularAut (h.modularAut.symm a) b).symm

/-- An algebraic Haar functional is invariant under its modular automorphism. -/
@[simp]
theorem apply_modularAut (a : A) : h (h.modularAut a) = h a := by
  simpa using h.apply_mul_modularAut a 1

/-- An algebraic Haar functional is invariant under the inverse of its modular automorphism. -/
@[simp]
theorem apply_modularAut_symm (a : A) : h (h.modularAut.symm a) = h a := by
  simpa using (h.apply_modularAut (h.modularAut.symm a)).symm

/-- **Uniqueness of the modular automorphism.** Any map `σ` with `h (b * σ a) = h (a * b)` is the
modular automorphism. -/
theorem coe_modularAut_eq {σ : A → A} (hσ : ∀ a b, h (b * σ a) = h (a * b)) :
    ⇑h.modularAut = σ :=
  funext fun a ↦ h.eq_of_forall_apply_mul_eq fun b ↦ by rw [apply_mul_modularAut, hσ]

/-- The modular automorphism maps each simple coefficient space into itself. -/
theorem modularAut_mem_of_mem_simpleCoefficientSubmodules {P : Submodule ℂ A}
    (hP : P ∈ simpleCoefficientSubmodules ℂ A) {a : A} (ha : a ∈ P) : h.modularAut a ∈ P := by
  obtain ⟨c, hcP, hc⟩ := h.exists_mem_forall_apply_mul_eq hP
    (comap_starLinearEquiv_mem_simpleCoefficientSubmodules hP) (fun _ ↦ Iff.rfl) ha
  rwa [h.eq_of_forall_apply_mul_eq (c := h.modularAut a) (c' := c) fun b ↦ by
    rw [apply_mul_modularAut, hc]]

/-- The modular automorphism intertwines the involution with its inverse:
`star (θ a) = θ⁻¹ (star a)`. -/
theorem star_modularAut (a : A) : star (h.modularAut a) = h.modularAut.symm (star a) := by
  refine h.modularAut.injective (h.eq_of_forall_apply_mul_eq fun b ↦ ?_)
  -- `h (b * θ (star (θ a))) = h (star (star b * θ a)) = h (star (a * star b)) = h (b * star a)`.
  rw [apply_mul_modularAut, AlgEquiv.apply_symm_apply, ← star_star b, ← star_mul, map_star,
    apply_mul_modularAut, ← map_star, star_mul, star_star]

/-- The modular automorphism is the identity if and only if the Haar functional is a trace. -/
theorem modularAut_eq_refl_iff :
    h.modularAut = AlgEquiv.refl ↔ ∀ a b : A, h (a * b) = h (b * a) := by
  refine ⟨fun hθ a b ↦ ?_, fun H ↦ AlgEquiv.ext fun a ↦ ?_⟩
  · simpa [hθ] using (h.apply_mul_modularAut a b).symm
  · exact congrFun (h.coe_modularAut_eq (σ := id) fun a b ↦ (H a b).symm) a

section CoefficientMatrix

open Matrix
open scoped ComplexOrder

variable {M ι : Type*} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι] [DecidableEq ι]

omit [StarRing A] [StarModule ℂ A] [StarCoalgebra ℂ A] [IsSimpleOrder (Subcomodule ℂ A M)]
  [DecidableEq ι] in
/-- Entries of `F u F` for a complex matrix `F`, as linear combinations of entries of `u`. -/
private theorem transpose_mul_mul_apply (F : Matrix ι ι ℂ) (u : Matrix ι ι A) (i j : ι) :
    (Fᵀ.map (algebraMap ℂ A) * u * Fᵀ.map (algebraMap ℂ A)) i j =
      ∑ q, ∑ p, (F j q * F p i) • u p q := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    Finset.smul_sum, smul_smul]

/-- By Schur orthogonality, `F u F` pairs with the starred coefficients as `θ(u)` does:
`h (star (u k l) * (F u F) i j) = h (u i j * star (u k l))`. -/
private theorem apply_star_mul_transpose_mul_mul (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (star (coefficientMatrix (C := A) b k l) *
        ((unitarizingMatrix h.toLinearMap b)ᵀ.map (algebraMap ℂ A) * coefficientMatrix (C := A) b *
          (unitarizingMatrix h.toLinearMap b)ᵀ.map (algebraMap ℂ A)) i j) =
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) := by
  set u := coefficientMatrix (C := A) b with hu_def
  set Ft := unitarizingMatrix h.toLinearMap b with hFt_def
  have hFt : Ft⁻¹ * Ft = 1 :=
    Ft.nonsing_inv_mul ((isUnit_iff_isUnit_det _).mp (h.posDef_unitarizingMatrix b).isUnit)
  have htr : Ft⁻¹.trace = Ft.trace := (h.trace_unitarizingMatrix_eq_trace_inv b).symm
  have hsum : ∑ q, ∑ p, Ft j q * Ft p i * h (star (u k l) * u p q) =
      Ft j l * (Ft⁻¹ * Ft) k i / Ft.trace := by
    calc ∑ q, ∑ p, Ft j q * Ft p i * h (star (u k l) * u p q)
        = ∑ q, if l = q then ∑ p, Ft j q * Ft p i * (Ft⁻¹ k p / Ft.trace) else 0 := by
          simp only [hu_def, h.apply_star_mul_coefficientMatrix b hu, ← hFt_def, htr, mul_ite,
            mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
      _ = Ft j l * (Ft⁻¹ * Ft) k i / Ft.trace := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.mul_apply,
          Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun p _ ↦ by ring
  rw [transpose_mul_mul_apply, h.apply_coefficientMatrix_mul_star b hu, ← hFt_def]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  rw [hsum, hFt, Matrix.one_apply]
  rcases eq_or_ne i k with rfl | hik
  · simp
  · simp [hik, hik.symm]

/-- **The modular automorphism on a unitary coefficient matrix.** If `u` is the coefficient matrix
of a simple comodule in a basis where it is unitary, then `θ(u) = F u F`, where `F` is the
transpose of the normalized unitarizing matrix `Ft` of weighted Schur orthogonality
(`TauCeti.AlgebraicHaar.apply_coefficientMatrix_mul_star`). -/
theorem map_modularAut_coefficientMatrix (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (coefficientMatrix (C := A) b).map h.modularAut =
      (unitarizingMatrix h.toLinearMap b)ᵀ.map (algebraMap ℂ A) * coefficientMatrix (C := A) b *
        (unitarizingMatrix h.toLinearMap b)ᵀ.map (algebraMap ℂ A) := by
  set P := matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)
  have hP : P ∈ simpleCoefficientSubmodules ℂ A :=
    matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules
  have huP (p q : ι) : coefficientMatrix (C := A) b p q ∈ P := by
    rw [coefficientMatrix_apply]
    exact matrixCoefficient_mem_submodule _ _
  ext i j
  rw [Matrix.map_apply, ← sub_eq_zero]
  -- The difference `x` of the two sides lies in `P`, pairs to zero with `star P`, and therefore
  -- with all of `A` by Haar orthogonality of the other blocks; faithfulness of `h` gives `x = 0`.
  set x := h.modularAut (coefficientMatrix (C := A) b i j) -
    ((unitarizingMatrix h.toLinearMap b)ᵀ.map (algebraMap ℂ A) * coefficientMatrix (C := A) b *
      (unitarizingMatrix h.toLinearMap b)ᵀ.map (algebraMap ℂ A)) i j
  have hxP : x ∈ P := by
    refine sub_mem (h.modularAut_mem_of_mem_simpleCoefficientSubmodules hP (huP i j)) ?_
    rw [transpose_mul_mul_apply]
    exact Submodule.sum_mem _ fun q _ ↦ Submodule.sum_mem _ fun p _ ↦
      Submodule.smul_mem _ _ (huP p q)
  have hkl (k l : ι) : h (star (coefficientMatrix (C := A) b k l) * x) = 0 := by
    rw [mul_sub, map_sub, apply_mul_modularAut, h.apply_star_mul_transpose_mul_mul b hu, sub_self]
  refine h.eq_zero_of_forall_mul_left_eq_zero fun y ↦ ?_
  suffices H : ∀ c, h (star c * x) = 0 by simpa using H (star y)
  intro c
  induction c using h.induction_simpleCoefficientSubmodules with
  | mem Q hQ c hc =>
    by_cases hQP : Q = P
    · subst hQP
      obtain ⟨X, rfl⟩ := (b.mem_matrixCoefficientSubmodule_iff_exists_matrix).mp hc
      simp only [star_sum, star_smul, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hkl,
        smul_zero, Finset.sum_const_zero]
    · exact h.map_star_mul_eq_zero_of_mem_simpleCoefficientSubmodules hQ hP hQP hc hxP
  | zero => simp
  | add c c' hc hc' => simp [add_mul, hc, hc']

end CoefficientMatrix

end AlgebraicHaar

/-- **The modular automorphism of the Haar functional.** For an algebraic Haar functional `h` on
a complex Hopf star algebra `A`, there is exactly one algebra automorphism `θ` of `A` with
`h (a * b) = h (b * θ a)` for all `a` and `b`, namely `TauCeti.AlgebraicHaar.modularAut`. -/
theorem haar_modular_automorphism (h : AlgebraicHaar A) :
    ∃! θ : A ≃ₐ[ℂ] A, ∀ a b, h (a * b) = h (b * θ a) :=
  ⟨h.modularAut, fun a b ↦ (h.apply_mul_modularAut a b).symm, fun θ hθ ↦ AlgEquiv.ext fun a ↦
    (congrFun (h.coe_modularAut_eq (σ := θ) fun a b ↦ (hθ a b).symm) a).symm⟩

end TauCeti
