/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Tactic.Linarith

/-!
# Completed combinations of torsor elements

For a potential `F : S → ℝ`, `NovikovModule R F` consists of coefficient functions on `S`
with finite support above every potential threshold. It is a submodule of `S → R`, with the
usual pointwise addition and ground-ring scalar multiplication.

Suppose `S` is a finite disjoint union of torsors `P i` under an additive group `H`, and
`F (h +ᵥ p) = F p - N h`. Choosing one lift in each torsor identifies this completion with
one Novikov series per orbit. Changing the lifts multiplies each coordinate on the right by
the monomial of the old lift minus the new lift. In particular the completion retains the actual
lifted generators, while the coordinate description depends on the chosen lifts. The transported
Novikov scalar action is independent of those lifts. Its module laws and basis use Mathlib's
`AddEquiv.module` and `Pi.basisFun`.

The cutoff formulas include the potential of each chosen lift; they do not require an
injective or discrete period map. These are the coefficient coordinates used for completed
chains on an abelian cover, or for capped generators with an action functional.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

namespace TauCeti

variable (R : Type*) [Semiring R] {S : Type*}

/-- Completed `R`-linear combinations of `S`, finite above each threshold of the potential `F`.
The scalar multiplication in this submodule is the ground-ring action. -/
def NovikovModule (F : S → ℝ) : Submodule R (S → R) where
  carrier := {a | ∀ C : ℝ, {s | a s ≠ 0 ∧ C < F s}.Finite}
  zero_mem' := by simp
  add_mem' ha hb C := ((ha C).union (hb C)).subset fun s hs => by
    by_contra h
    simp_all
  smul_mem' r a ha C := (ha C).subset fun s hs =>
    ⟨fun h => hs.1 (by simp [h]), hs.2⟩

namespace NovikovModule

variable {R} {F : S → ℝ}

/-- Membership is precisely finiteness of the nonzero coefficients above every potential
threshold. -/
@[simp]
theorem mem_iff {a : S → R} : a ∈ NovikovModule R F ↔
    ∀ C : ℝ, {s | a s ≠ 0 ∧ C < F s}.Finite := Iff.rfl

/-- Only finitely many nonzero coefficients occur above any fixed potential threshold. -/
theorem finite_gt (a : NovikovModule R F) (C : ℝ) :
    {s | a.val s ≠ 0 ∧ C < F s}.Finite := a.property C

/-- The support condition is unchanged if the potential cutoff is inclusive. -/
theorem mem_iff_finite_ge {a : S → R} : a ∈ NovikovModule R F ↔
    ∀ C : ℝ, {s | a s ≠ 0 ∧ C ≤ F s}.Finite := by
  constructor
  · intro ha C
    exact (ha (C - 1)).subset fun s hs => ⟨hs.1, by linarith [hs.2]⟩
  · intro ha C
    exact (ha C).subset fun s hs => ⟨hs.1, hs.2.le⟩

/-- A completed combination has only finitely many nonzero coefficients at or above a fixed
potential threshold. -/
theorem finite_ge (a : NovikovModule R F) (C : ℝ) :
    {s | a.val s ≠ 0 ∧ C ≤ F s}.Finite := mem_iff_finite_ge.mp a.property C

/-- The potential is bounded above on the support of a completed combination. -/
theorem bddAbove_image_support (a : NovikovModule R F) :
    BddAbove (F '' Function.support a.val) := by
  obtain ⟨m, hm⟩ := ((finite_gt a 0).image F).bddAbove
  refine ⟨max m 0, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  rcases lt_or_ge 0 (F s) with h | h
  · exact (hm ⟨s, ⟨hs, h⟩, rfl⟩).trans (le_max_left _ _)
  · exact h.trans (le_max_right _ _)

section Coordinates

variable {H ι : Type*} [AddGroup H] [Finite ι] {P : ι → Type*}
    [∀ i, AddTorsor H (P i)] {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)

include hF

omit [Finite ι] in
/-- The potential of a generator is its reference potential minus the period of its displacement. -/
theorem potential_eq_sub_vsub (r : ∀ i, P i) (i : ι) (p : P i) :
    F ⟨i, p⟩ = F ⟨i, r i⟩ - N (p -ᵥ r i) := by
  simpa only [vsub_vadd] using hF i (p -ᵥ r i) (r i)

/-- Finiteness above potential thresholds is equivalent to the Novikov support condition in
every orbit, for any chosen lifts. -/
theorem mem_iff_forall_finite_vadd_lt (r : ∀ i, P i) (a : (Σ i, P i) → R) :
    a ∈ NovikovModule R F ↔
      ∀ i C, {h | a ⟨i, h +ᵥ r i⟩ ≠ 0 ∧ N h < C}.Finite := by
  constructor
  · intro ha i C
    have hf := ha (F ⟨i, r i⟩ - C)
    have hinj : Function.Injective (fun h : H => (⟨i, h +ᵥ r i⟩ : Σ i, P i)) := by
      intro h k heq
      exact (vadd_right_injective (r i)) (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
    refine (hf.preimage hinj.injOn).subset fun h hh => ?_
    exact ⟨hh.1, by rw [hF]; linarith [hh.2]⟩
  · intro ha C
    have hf : ∀ i, (fun h => (⟨i, h +ᵥ r i⟩ : Σ i, P i)) ''
        {h | a ⟨i, h +ᵥ r i⟩ ≠ 0 ∧ N h < F ⟨i, r i⟩ - C} |>.Finite :=
      fun i => (ha i _).image _
    refine (Set.finite_iUnion hf).subset ?_
    rintro ⟨i, p⟩ hp
    refine Set.mem_iUnion.mpr ⟨i, p -ᵥ r i, ⟨?_, ?_⟩, ?_⟩
    · simpa using hp.1
    · linarith [potential_eq_sub_vsub hF r i p, hp.2]
    · simp

/-- Coordinates of a completed combination relative to one lift in each orbit. This is a
ground-ring linear equivalence with a finite family of Novikov series. -/
def coordinates (r : ∀ i, P i) :
    NovikovModule R F ≃ₗ[R] (ι → NovikovSeries R H N) where
  toFun a i := ⟨fun h => a.val ⟨i, h +ᵥ r i⟩,
    (mem_iff_forall_finite_vadd_lt hF r a.val).mp a.property i⟩
  invFun b := ⟨fun s => (b s.1).coeff (s.2 -ᵥ r s.1), by
    apply (mem_iff_forall_finite_vadd_lt hF r _).mpr
    intro i C
    simpa using (b i).finite_lt C⟩
  left_inv a := by
    ext ⟨i, p⟩
    simp
  right_inv b := by
    ext i h
    simp
  map_add' a b := by
    ext i h
    rfl
  map_smul' c a := by
    ext i h
    rfl

/-- The coefficient at exponent `h` is the coefficient of the generator `h +ᵥ r i`. -/
@[simp]
theorem coordinates_coeff (r : ∀ i, P i) (a : NovikovModule R F) (i : ι) (h : H) :
    (coordinates hF r a i).coeff h = a.val ⟨i, h +ᵥ r i⟩ := (rfl)

/-- Recover the coefficient of a lifted generator by subtracting its reference lift. -/
@[simp]
theorem coordinates_symm_apply (r : ∀ i, P i) (b : ι → NovikovSeries R H N)
    (i : ι) (p : P i) :
    ((coordinates hF r).symm b).val ⟨i, p⟩ = (b i).coeff (p -ᵥ r i) := (rfl)

/-- The potential cutoff in an orbit is the period cutoff measured from its chosen lift. -/
theorem coordinates_coeff_eq_zero_iff (r : ∀ i, P i) (a : NovikovModule R F) (C : ℝ) :
    (∀ i h, N h < F ⟨i, r i⟩ - C → (coordinates hF r a i).coeff h = 0) ↔
      ∀ s, C < F s → a.val s = 0 := by
  constructor
  · intro ha ⟨i, p⟩ hp
    simpa using ha i (p -ᵥ r i) (by linarith [potential_eq_sub_vsub hF r i p])
  · intro ha i h hh
    exact ha ⟨i, h +ᵥ r i⟩ (by rw [hF]; linarith)

/-- Changing the reference lift translates the exponent by the old lift minus the new lift.
Thus the matrix of a lift change is diagonal with monomial entries. -/
theorem coordinates_apply_eq_mul_single (r r' : ∀ i, P i) (a : NovikovModule R F) (i : ι) :
    coordinates hF r' a i =
      coordinates hF r a i * NovikovSeries.single (r i -ᵥ r' i) 1 := by
  ext h
  simp only [NovikovSeries.coeff_mul_single, mul_one, coordinates_coeff, sub_eq_add_neg,
    neg_vsub_eq_vsub_rev, add_vadd, vsub_vadd]

/-- The Novikov module structure, transported using arbitrary orbit lifts. Install it with
`letI := NovikovModule.module (R := R) hF`. Every choice of lifts is linear for this one
structure by `coordinates_smul`. -/
@[instance_reducible]
def module : Module (NovikovSeries R H N) (NovikovModule R F) :=
  (coordinates hF (fun i => Classical.arbitrary (P i))).toAddEquiv.module _

/-- Novikov scalar multiplication is componentwise multiplication in any lift coordinates. -/
theorem coordinates_smul (r : ∀ i, P i) (b : NovikovSeries R H N)
    (a : NovikovModule R F) :
    letI := module (R := R) hF
    coordinates hF r (b • a) = b • coordinates hF r a := by
  let := module (R := R) hF
  let r₀ := fun i => Classical.arbitrary (P i)
  have hc : coordinates hF r₀ (b • a) = b • coordinates hF r₀ a := by
    exact ((coordinates hF r₀).toAddEquiv.linearEquiv (NovikovSeries R H N)).map_smul b a
  ext i h
  have hcoord := congrFun hc i
  rw [coordinates_apply_eq_mul_single hF r₀ r, hcoord]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [coordinates_apply_eq_mul_single hF r₀ r]
  exact congrArg (fun x : NovikovSeries R H N => x.coeff h) (mul_assoc _ _ _)

/-- Coordinates in any chosen lifts form a Novikov-linear equivalence for the shared module
structure. -/
def coordinatesLinearEquiv (r : ∀ i, P i) :
    letI := module (R := R) hF
    NovikovModule R F ≃ₗ[NovikovSeries R H N] (ι → NovikovSeries R H N) :=
  letI := module (R := R) hF
  { (coordinates hF r).toAddEquiv with map_smul' := coordinates_smul hF r }

/-- The Novikov-linear coordinate equivalence evaluates to the original coefficient coordinates. -/
@[simp]
theorem coordinatesLinearEquiv_apply (r : ∀ i, P i) (a : NovikovModule R F) :
    coordinatesLinearEquiv hF r a = coordinates hF r a := (rfl)

/-- The inverse Novikov-linear equivalence reconstructs the same coefficient function. -/
@[simp]
theorem coordinatesLinearEquiv_symm_apply (r : ∀ i, P i) (b : ι → NovikovSeries R H N) :
    (coordinatesLinearEquiv hF r).symm b = (coordinates hF r).symm b := (rfl)

/-- A monomial acts by deck translation, with its coefficient multiplying on the left. -/
theorem single_smul_apply (h : H) (c : R) (a : NovikovModule R F)
    (i : ι) (p : P i) :
    letI := module (R := R) hF
    (NovikovSeries.single (N := N) h c • a).val ⟨i, p⟩ = c * a.val ⟨i, -h +ᵥ p⟩ := by
  let r := fun i => Classical.arbitrary (P i)
  have heq := congrArg (fun b : ι → NovikovSeries R H N => (b i).coeff (p -ᵥ r i))
    (coordinates_smul hF r (NovikovSeries.single h c) a)
  simpa only [coordinates_coeff, vsub_vadd, Pi.smul_apply, smul_eq_mul,
    NovikovSeries.coeff_single_mul, add_vadd] using heq

/-- The basis of the completed module consisting of the chosen orbit lifts. This exhibits
it as a finite free Novikov module. -/
def basis (r : ∀ i, P i) :
    letI := module (R := R) hF
    Module.Basis ι (NovikovSeries R H N) (NovikovModule R F) := by
  letI := module (R := R) hF
  exact (Pi.basisFun (NovikovSeries R H N) ι).map
    (coordinatesLinearEquiv hF r).symm

/-- In lift coordinates, the basis vector for an orbit is the unit series in that orbit
and zero in every other orbit. -/
@[simp]
theorem coordinates_basis [DecidableEq ι] (r : ∀ i, P i) (i : ι) :
    coordinates (R := R) hF r (basis hF r i) = Pi.single i 1 := by
  simp [basis, coordinatesLinearEquiv, Pi.basisFun_apply]

/-- Basis representation is precisely the Novikov coordinate series in each orbit. -/
@[simp]
theorem basis_repr_apply (r : ∀ i, P i) (a : NovikovModule R F) (i : ι) :
    letI := module (R := R) hF
    (basis hF r).repr a i = coordinates hF r a i := by
  simp [basis, coordinatesLinearEquiv]

/-- Changing a basis lift multiplies its basis vector on the left by the monomial of the
new lift minus the old lift. Both bases belong to the same Novikov module. -/
theorem basis_eq_single_smul (r r' : ∀ i, P i) (i : ι) :
    letI := module (R := R) hF
    basis (R := R) hF r' i =
      NovikovSeries.single (N := N) (r' i -ᵥ r i) (1 : R) • basis (R := R) hF r i := by
  classical
  let := module (R := R) hF
  apply (coordinates hF r).injective
  rw [coordinates_smul, coordinates_basis]
  ext j
  rw [coordinates_apply_eq_mul_single hF r' r, coordinates_basis]
  by_cases hij : i = j
  · subst j
    simp
  · simp [Ne.symm hij]

end Coordinates

end NovikovModule

end TauCeti
