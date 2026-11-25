/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.Algebra.Homology.AInfinity.Curved.Stasheff

/-!
# Curved `A∞` algebras

A curved `A∞` algebra on an internally `ℤ`-graded module `A` consists of operations `m n` of
degree `2 - n` for every `n ≥ 0`, including a nullary operation, whose value `m₀ = m 0 ![]` is the
*curvature*, an element of degree two. The operations satisfy the curved Stasheff identities
`TauCeti.AInfinity.curvedStasheffSum` in every arity, the arity zero included. In arity zero the
identity says that the curvature is a cycle, `m₁(m₀) = 0`, and in arity one it says that

`m₁(m₁(a)) = m₂(a, m₀) - m₂(m₀, a)`,

so the unary operation squares to the commutator with the curvature, in the right-module
convention used by `TauCeti.IsCurvedDGAlgebra`. Curved `A∞` algebras arise as the endomorphism
algebras of Lagrangian branes in Floer theory, where the curvature counts discs with boundary on
the Lagrangian and no inputs.

The uncurved `A∞` algebras `TauCeti.AInfinityAlgebra` are exactly the curved ones of curvature
zero (`TauCeti.AInfinityAlgebra.equivCurvatureEqZero`). Unlike `TauCeti.AInfinityAlgebra`, the
structure is stated through its unsuspended Stasheff identities rather than a square-zero
coderivation of the bar construction: with curvature, the bar coderivation has a component on
the empty word, so it lives on the coaugmented tensor coalgebra.

A strict unit `e` of a curved `A∞` algebra is defined as in the uncurved case. When the curvature
is a scalar multiple `λ e` of a strict unit, the two terms of the arity-one identity cancel and the
unary operation squares to zero
(`CurvedAInfinityAlgebra.StrictUnit.differential_differential_eq_zero_of_curvature_eq_smul`).

## Main definitions

* `TauCeti.CurvedAInfinityAlgebra`: a curved nonunital `A∞` algebra.
* `TauCeti.CurvedAInfinityAlgebra.curvature`: the value `m₀` of its nullary operation.
* `TauCeti.CurvedAInfinityAlgebra.differential`: its unary operation as a linear map.
* `TauCeti.CurvedAInfinityAlgebra.StrictUnit`: a strict unit.
* `TauCeti.AInfinityAlgebra.toCurvedAInfinityAlgebra`: an uncurved `A∞` algebra as a curved one.
* `TauCeti.CurvedAInfinityAlgebra.toAInfinityAlgebra`: a curved `A∞` algebra of curvature zero as
  an uncurved one.
* `TauCeti.AInfinityAlgebra.equivCurvatureEqZero`: uncurved `A∞` algebras are the curved ones of
  curvature zero.

## Main results

* `TauCeti.CurvedAInfinityAlgebra.m_one_curvature`: the arity-zero identity `m₁(m₀) = 0`.
* `TauCeti.CurvedAInfinityAlgebra.differential_differential`: the arity-one identity
  `m₁(m₁(a)) = m₂(a, m₀) - m₂(m₀, a)`.
* `TauCeti.CurvedAInfinityAlgebra.stasheff_arity_two_of_m_three_eq_zero`: when `m₃` vanishes, the
  unary operation is a graded derivation of `m₂`.
* `CurvedAInfinityAlgebra.StrictUnit.differential_differential_eq_zero_of_curvature_eq_smul`:
  for curvature a scalar multiple of a strict unit, the unary operation squares to zero.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Section 3.2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.5.
-/

public section

universe uR uA

namespace TauCeti

/-- A curved nonunital `A∞` algebra over a commutative ring: operations `m n` of degree `2 - n`
for every `n ≥ 0`, including the nullary operation, satisfying the curved Stasheff identities on
homogeneous inputs in every arity. -/
structure CurvedAInfinityAlgebra (R : Type uR) (A : Type uA) [CommRing R] [AddCommGroup A]
    [Module R A] where
  /-- The internal cohomological grading of the carrier. -/
  grading : InternalGrading R A ℤ
  /-- The unsuspended arity-`n` operation. -/
  m : ∀ n : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) A
  /-- The operation `m n` has cohomological degree `2 - n`; in particular the curvature has degree
  two. -/
  m_degree : ∀ n, MultilinearMap.IsHomogeneous (m n) (fun _ ↦ grading.piece) grading.piece (2 - n)
  /-- The curved Stasheff identities on homogeneous inputs, in every arity. -/
  stasheff : ∀ (n : ℕ) (d : ℕ → ℤ) (x : ℕ → A), (∀ i < n, x i ∈ grading.piece (d i)) →
    AInfinity.curvedStasheffSum m d x n = 0

namespace CurvedAInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- Curved `A∞` algebras are determined by their grading and their operations. -/
@[ext]
theorem ext {𝒜 𝒜' : CurvedAInfinityAlgebra R A} (hG : 𝒜.grading = 𝒜'.grading)
    (hm : 𝒜.m = 𝒜'.m) : 𝒜 = 𝒜' := by
  cases 𝒜
  cases 𝒜'
  simp only at hG hm
  subst hG hm
  rfl

variable (𝒜 : CurvedAInfinityAlgebra R A)

/-! ### The curvature and the differential -/

/-- The **curvature** of a curved `A∞` algebra: the value `m₀` of its nullary operation. -/
def curvature : A := 𝒜.m 0 ![]

/-- The nullary operation is constant, with value the curvature. -/
@[simp]
theorem m_zero_apply (x : Fin 0 → A) : 𝒜.m 0 x = 𝒜.curvature := by
  rw [curvature, Subsingleton.elim x ![]]

/-- The nullary operation vanishes exactly when the curvature does. -/
theorem m_zero_eq_zero_iff : 𝒜.m 0 = 0 ↔ 𝒜.curvature = 0 :=
  ⟨fun h ↦ by simp [curvature, h], fun h ↦ by ext x; simp [h]⟩

/-- The curvature has degree two. -/
theorem curvature_mem : 𝒜.curvature ∈ 𝒜.grading.piece 2 := by
  simpa using (𝒜.m_degree 0).map_mem (fun i ↦ i.elim0) ![] fun i ↦ i.elim0

/-- The unary operation, regarded as a linear map on the total module. -/
def differential : A →ₗ[R] A :=
  (𝒜.m 1).curryRight ![]

/-- Evaluating the differential is evaluating the unary operation. -/
@[simp]
theorem differential_apply (x : A) : 𝒜.differential x = 𝒜.m 1 ![x] := by
  simp [differential, MultilinearMap.curryRight_apply]

/-- The unary operation raises the degree by one. -/
theorem differential_mem_piece {p : ℤ} {x : A} (hx : x ∈ 𝒜.grading.piece p) :
    𝒜.differential x ∈ 𝒜.grading.piece (p + 1) := by
  simpa using (𝒜.m_degree 1).map_mem (fun _ ↦ p) ![x] (fun _ ↦ by simpa using hx)

/-- **The arity-zero curved Stasheff identity**: the curvature is a cycle, `m₁(m₀) = 0`. -/
@[simp]
theorem m_one_curvature : 𝒜.m 1 ![𝒜.curvature] = 0 := by
  have h := 𝒜.stasheff 0 0 0 fun _ h ↦ absurd h (Nat.not_lt_zero _)
  rw [AInfinity.curvedStasheffSum_zero] at h
  simpa using h

/-- The curvature is a cycle for the differential. -/
theorem differential_curvature : 𝒜.differential 𝒜.curvature = 0 := by
  simp

/-- **The arity-one curved Stasheff identity**: the unary operation squares to the commutator
`m₂(a, m₀) - m₂(m₀, a)` with the curvature. -/
theorem differential_differential (x : A) :
    𝒜.differential (𝒜.differential x) = 𝒜.m 2 ![x, 𝒜.curvature] - 𝒜.m 2 ![𝒜.curvature, x] := by
  have h₀ (y : A) : Function.update ![0, 𝒜.curvature] 0 y = ![y, 𝒜.curvature] :=
    Fin.update_cons_zero ..
  let L : A →ₗ[R] A := 𝒜.differential ∘ₗ 𝒜.differential
  let Q : A →ₗ[R] A :=
    (𝒜.m 2).toLinearMap ![0, 𝒜.curvature] 0 - (𝒜.m 2).curryRight ![𝒜.curvature]
  suffices L x = Q x by simpa [L, Q, h₀] using this
  refine LinearMap.congr_fun (𝒜.grading.linearMap_ext fun p y hy ↦ ?_) x
  have h := 𝒜.stasheff 1 (fun _ ↦ p) (fun _ ↦ y) fun _ _ ↦ hy
  rw [AInfinity.curvedStasheffSum_one, ← curvature, sub_eq_zero] at h
  simp [L, Q, h₀, eq_sub_of_add_eq h]

/-- **The arity-two curved Stasheff identity when `m₃` vanishes**: the unary operation is a
graded derivation of `m₂`, with the Koszul sign determined by the degree of the first input. -/
theorem stasheff_arity_two_of_m_three_eq_zero (hm₃ : 𝒜.m 3 = 0) (x y : A) (p : ℤ)
    (hx : x ∈ 𝒜.grading.piece p) :
    𝒜.m 1 ![𝒜.m 2 ![x, y]] =
      𝒜.m 2 ![𝒜.m 1 ![x], y] + negOnePowCast R p • 𝒜.m 2 ![x, 𝒜.m 1 ![y]] :=
  AInfinity.stasheff_arity_two_of_stasheffSum_eq_zero 𝒜.grading 𝒜.m (fun e a ha ↦
    (AInfinity.curvedStasheffSum_eq_stasheffSum_of_m_succ_eq_zero _ _ _ hm₃).symm.trans
      (𝒜.stasheff 2 e a ha)) x y p hx

/-! ### Strict units -/

/-- A **strict unit** of a curved `A∞` algebra, as for uncurved ones: an element of degree zero
which is a two-sided unit for `m₂` and on which every operation of arity other than two vanishes.
The arity-zero condition is vacuous, so the curvature is not constrained. -/
structure StrictUnit (e : A) : Prop where
  /-- The unit is homogeneous of degree zero. -/
  degree_zero : e ∈ 𝒜.grading.piece 0
  /-- The unit is a left unit for `m₂`. -/
  binary_left : ∀ x, 𝒜.m 2 ![e, x] = x
  /-- The unit is a right unit for `m₂`. -/
  binary_right : ∀ x, 𝒜.m 2 ![x, e] = x
  /-- The operations of arity other than two vanish on every tuple containing the unit. -/
  higher : ∀ (n : ℕ), n ≠ 2 → ∀ x : Fin n → A, (∃ i, x i = e) → 𝒜.m n x = 0

attribute [simp] StrictUnit.binary_left StrictUnit.binary_right

namespace StrictUnit

variable {𝒜} {e e' : A}

/-- A strict unit is annihilated by the unary operation. -/
@[simp]
theorem unary_eq_zero (h : 𝒜.StrictUnit e) : 𝒜.m 1 ![e] = 0 :=
  h.higher 1 (by decide) ![e] ⟨0, rfl⟩

/-- A strict unit is a cycle for the differential. -/
theorem differential_eq_zero (h : 𝒜.StrictUnit e) : 𝒜.differential e = 0 := by
  simp [h]

/-- A strict unit of a curved `A∞` algebra is unique. -/
theorem eq (h : 𝒜.StrictUnit e) (h' : 𝒜.StrictUnit e') : e = e' := by
  calc
    e = 𝒜.m 2 ![e', e] := (h'.binary_left e).symm
    _ = e' := h.binary_right e'

/-- **Scalar curvature.** If the curvature is a scalar multiple `c • e` of a strict unit, the two
curvature terms of the arity-one identity cancel, and the unary operation squares to zero. -/
theorem differential_differential_eq_zero_of_curvature_eq_smul (h : 𝒜.StrictUnit e) {c : R}
    (hc : 𝒜.curvature = c • e) (x : A) : 𝒜.differential (𝒜.differential x) = 0 := by
  have hr : 𝒜.m 2 ![x, c • e] = c • x := by
    have hu (y : A) : Function.update ![x, e] 1 y = ![x, y] := by ext i; fin_cases i <;> rfl
    rw [← hu (c • e), (𝒜.m 2).map_update_smul, hu, h.binary_right, RingHom.id_apply]
  have hl : 𝒜.m 2 ![c • e, x] = c • x := by
    have hu (y : A) : Function.update ![e, x] 0 y = ![y, x] := Fin.update_cons_zero ..
    rw [← hu (c • e), (𝒜.m 2).map_update_smul, hu, h.binary_left, RingHom.id_apply]
  rw [differential_differential, hc, hr, hl, sub_self]

end StrictUnit

end CurvedAInfinityAlgebra

/-! ### Comparison with uncurved `A∞` algebras -/

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- An uncurved `A∞` algebra is a curved `A∞` algebra with the same operations: its curvature is
zero, and its curved Stasheff identities are its Stasheff identities. -/
def toCurvedAInfinityAlgebra : CurvedAInfinityAlgebra R A where
  grading := 𝒜.grading
  m := 𝒜.m
  m_degree n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · rw [𝒜.m_zero]
      exact MultilinearMap.isHomogeneous_zero _ _ _
    · exact 𝒜.m_degree n hn
  stasheff n d x hx := by
    rw [AInfinity.curvedStasheffSum_eq_stasheffSum_of_m_zero_eq_zero _ _ _ 𝒜.m_zero]
    exact 𝒜.stasheff n d x hx

@[simp]
theorem toCurvedAInfinityAlgebra_grading : 𝒜.toCurvedAInfinityAlgebra.grading = 𝒜.grading :=
  (rfl)

@[simp]
theorem toCurvedAInfinityAlgebra_m : 𝒜.toCurvedAInfinityAlgebra.m = 𝒜.m := (rfl)

/-- An uncurved `A∞` algebra has curvature zero. -/
@[simp]
theorem curvature_toCurvedAInfinityAlgebra : 𝒜.toCurvedAInfinityAlgebra.curvature = 0 := by
  rw [← CurvedAInfinityAlgebra.m_zero_eq_zero_iff, toCurvedAInfinityAlgebra_m, 𝒜.m_zero]

@[simp]
theorem differential_toCurvedAInfinityAlgebra :
    𝒜.toCurvedAInfinityAlgebra.differential = 𝒜.differential := by
  ext x
  simp

end AInfinityAlgebra

namespace CurvedAInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : CurvedAInfinityAlgebra R A)

/-- A curved `A∞` algebra of curvature zero is an uncurved `A∞` algebra with the same operations;
its Taylor map is the suspension of the operations. -/
noncomputable def toAInfinityAlgebra (h : 𝒜.curvature = 0) : AInfinityAlgebra R A :=
  AInfinityAlgebra.ofStasheff 𝒜.grading 𝒜.m (𝒜.m_zero_eq_zero_iff.2 h) (fun n _ ↦ 𝒜.m_degree n)
    (AInfinity.suspensionTaylor _ _) (AInfinity.isSuspension_suspensionTaylor _ _)
    fun n _ d x hx ↦ by
      rw [← AInfinity.curvedStasheffSum_eq_stasheffSum_of_m_zero_eq_zero _ _ _
        (𝒜.m_zero_eq_zero_iff.2 h)]
      exact 𝒜.stasheff n d x hx

@[simp]
theorem toAInfinityAlgebra_grading (h : 𝒜.curvature = 0) :
    (𝒜.toAInfinityAlgebra h).grading = 𝒜.grading :=
  AInfinityAlgebra.ofStasheff_grading ..

@[simp]
theorem toAInfinityAlgebra_m (h : 𝒜.curvature = 0) : (𝒜.toAInfinityAlgebra h).m = 𝒜.m :=
  AInfinityAlgebra.ofStasheff_m ..

@[simp]
theorem toCurvedAInfinityAlgebra_toAInfinityAlgebra (h : 𝒜.curvature = 0) :
    (𝒜.toAInfinityAlgebra h).toCurvedAInfinityAlgebra = 𝒜 :=
  ext (by simp) (by simp)

end CurvedAInfinityAlgebra

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

@[simp]
theorem toAInfinityAlgebra_toCurvedAInfinityAlgebra (𝒜 : AInfinityAlgebra R A) :
    𝒜.toCurvedAInfinityAlgebra.toAInfinityAlgebra 𝒜.curvature_toCurvedAInfinityAlgebra = 𝒜 :=
  ext (by simp) (by simp)

/-- **Uncurved `A∞` algebras are the curved `A∞` algebras of curvature zero.** -/
noncomputable def equivCurvatureEqZero :
    AInfinityAlgebra R A ≃ {𝒜 : CurvedAInfinityAlgebra R A // 𝒜.curvature = 0} where
  toFun 𝒜 := ⟨𝒜.toCurvedAInfinityAlgebra, 𝒜.curvature_toCurvedAInfinityAlgebra⟩
  invFun 𝒜 := 𝒜.val.toAInfinityAlgebra 𝒜.property
  left_inv 𝒜 := 𝒜.toAInfinityAlgebra_toCurvedAInfinityAlgebra
  right_inv 𝒜 := Subtype.ext (𝒜.val.toCurvedAInfinityAlgebra_toAInfinityAlgebra 𝒜.property)

@[simp]
theorem coe_equivCurvatureEqZero_apply (𝒜 : AInfinityAlgebra R A) :
    (equivCurvatureEqZero 𝒜 : CurvedAInfinityAlgebra R A) = 𝒜.toCurvedAInfinityAlgebra := (rfl)

@[simp]
theorem equivCurvatureEqZero_symm_apply (𝒜 : {𝒜 : CurvedAInfinityAlgebra R A // 𝒜.curvature = 0}) :
    equivCurvatureEqZero.symm 𝒜 = 𝒜.val.toAInfinityAlgebra 𝒜.property := (rfl)

end AInfinityAlgebra

end TauCeti
