/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.Algebra.MvPolynomial.Rename
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# The simply blocked grid map

The unblocked grid complex `GC⁻` has one polynomial variable `V_c` for each `O`-marking.  Blocking
the `O`-marking in a chosen column `i` means setting `V_i = 0`.  The resulting simply blocked
construction keeps the variables indexed by the other columns and counts exactly the empty
rectangles which cover neither an `X`-marking nor the blocked `O`-marking.  This specialization is
defined for every grid diagram and every commutative coefficient semiring.  For a knot grid over a
coefficient semiring of characteristic two, it is the simply blocked differential.  Outside
characteristic two it is only the unsigned candidate linear map: exactly as for the unblocked
differential it specializes, the unsigned rectangle count squares to zero only after a sign
assignment, and signs use additive inverses, so the sign-corrected construction needs a
commutative coefficient ring.  For a multi-component link, the corresponding simply blocked theory
instead requires blocking one `O`-marking on each component.

The coefficients form the polynomial semiring `R[V_c | c ≠ i]`, rather than one carrying a
redundant variable known to act by zero.  Mathlib's `MvPolynomial.killCompl` makes the relation to
`GC⁻` explicit, while `simplyBlockedCoefficient_eq_sum` identifies the terms that remain after
specialization.

## Main definitions

* `TauCeti.GridChainHat`: the free module underlying the one-variable specialization.
* `TauCeti.simplyBlockedRingHom`: setting `V_i` to zero, as a ring homomorphism.
* `TauCeti.simplyBlockedRingHomAlong`: rename surviving variables along a column map, then block
  the target column.
* `TauCeti.simplyBlockedSpecialization`: coefficientwise specialization of `GC⁻` at `V_i = 0`.
* `TauCeti.simplyBlockedSpecializationLinearMap`: the same, as a linear map over the ground
  semiring.
* `TauCeti.simplyBlockedLift`: coefficientwise inclusion of the surviving variables, a section
  of the specialization (`TauCeti.simplyBlockedSpecialization_simplyBlockedLift`).
* `TauCeti.simplyBlockedRenameEquiv`: rename surviving variables and transport the blocked column.
* `TauCeti.simplyBlockedRenameRingHomInvPair`, `TauCeti.simplyBlockedRenameRingHomInvPairSymm`:
  the renaming and its inverse form a `RingHomInvPair`.
* `TauCeti.simplyBlockedMap`: coefficient specialization of a semilinear map of `GC⁻`.
* `TauCeti.GridChain.simplyBlockedRelabelColumnsEquiv`: relabel the columns of a specialized
  chain by a permutation and rename its surviving variables, transporting the blocked column.
* `TauCeti.GridDiagram.simplyBlockedRectangles`: the empty, `X`-avoiding rectangles which also
  avoid the chosen `O`-marking.
* `TauCeti.GridDiagram.simplyBlockedCoefficient`: the matrix coefficient of the specialized map.
* `TauCeti.GridDiagram.simplyBlockedDifferential`: the map obtained from `GC⁻` by
  specializing `V_i` to zero.

## Main results

* `TauCeti.simplyBlockedRingHom_rename`: blocking commutes with column renaming when the
  blocked column is transported.
* `TauCeti.simplyBlockedSpecialization_relabelRowsEquiv` and
  `TauCeti.simplyBlockedSpecialization_relabelColumnsRenameEquiv`: row and column relabelings
  commute with specialization.
* `TauCeti.simplyBlockedSpecialization_apply_eq_of_single`: compatible semilinear maps commute
  with specialization whenever they do so on basis generators.
* `TauCeti.simplyBlockedRingHomAlong_specialization`: column maps commute with blocking when
  they carry the blocked source column to the blocked target column.
* `TauCeti.simplyBlockedMap_simplyBlockedSpecialization`: specialization intertwines an
  unblocked semilinear map with its specialization `TauCeti.simplyBlockedMap`.
* `TauCeti.simplyBlockedSpecialization_simplyBlockedLift`: specializing the lift of a specialized
  chain recovers it.
* `TauCeti.simplyBlockedSpecialization_surjective` and
  `TauCeti.exact_X_smul_simplyBlockedSpecialization`: specialization presents the specialized
  chain module as the quotient of `GC⁻` by the multiples of `V_i`, which
  `TauCeti.X_smul_gridChainMinus_injective` says form a copy of `GC⁻`.
  `TauCeti.simplyBlockedSpecializationLinearMap_surjective` and
  `TauCeti.exact_X_smul_simplyBlockedSpecializationLinearMap` are the same for the linear maps
  over the ground semiring.
* `TauCeti.GridDiagram.simplyBlockedCoefficient_eq_sum`: a matrix coefficient is the sum, over the
  rectangles which avoid the blocked `O`-marking, of the product of the variables of the other
  `O`-markings the rectangle covers.
* `TauCeti.GridDiagram.simplyBlockedSpecialization_unblockedDifferential`: coefficientwise
  specialization intertwines the unblocked differential with the simply blocked map, so the latter
  really is the `V_i = 0` reduction of the former;
  `TauCeti.GridDiagram.simplyBlockedSpecializationLinearMap_comp_unblockedDifferential` is the same
  over the ground semiring.
* `TauCeti.GridDiagram.map_simplyBlockedDifferential_of_simplyBlockedSpecialization`: a compatible
  function between specialized chains inherits the unblocked chain equation.

## References

The specialization and rectangle formula follow Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

open MvPolynomial

/-- The chain module underlying the one-variable specialization, freely generated by grid states
over the polynomial semiring in the columns other than the blocked column `i`.  Its homology, for
a knot grid in characteristic two, is the simply blocked grid homology, which is not defined
here. -/
abbrev GridChainHat (R : Type*) [CommSemiring R] (n : ℕ) (i : Fin n) : Type _ :=
  GridChain (MvPolynomial {c : Fin n // c ≠ i} R) n

/-- Setting the blocked variable `V_i` to zero, as a ring homomorphism
`R[V₀, …, V_{n-1}] → R[V_c | c ≠ i]`. It is the homomorphism over which
`TauCeti.simplyBlockedSpecialization` is semilinear. -/
noncomputable abbrev simplyBlockedRingHom {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n) :
    MvPolynomial (Fin n) R →+* MvPolynomial {c : Fin n // c ≠ i} R :=
  (MvPolynomial.killCompl (R := R) (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
    Subtype.val_injective).toRingHom

/-- The coefficient specialization is `MvPolynomial.killCompl`. -/
@[simp]
theorem simplyBlockedRingHom_apply {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n)
    (p : MvPolynomial (Fin n) R) :
    simplyBlockedRingHom R i p =
      MvPolynomial.killCompl (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
        Subtype.val_injective p :=
  by
    unfold simplyBlockedRingHom
    rfl

/-- The blocked variable specializes to zero.

Not a `simp` lemma: `TauCeti.simplyBlockedRingHom_apply` and
`MvPolynomial.killCompl_X_of_notMem_range` already rewrite the left-hand side to `0`. -/
theorem simplyBlockedRingHom_X_eq_zero {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n) :
    simplyBlockedRingHom R i (MvPolynomial.X i) = 0 := by
  rw [simplyBlockedRingHom_apply]
  exact MvPolynomial.killCompl_X_of_notMem_range Subtype.val_injective (by simp)

/-- Coefficientwise specialization of an unblocked grid chain at `V_i = 0`.

This is semilinear over `MvPolynomial.killCompl`: specializing a polynomial multiple of a chain
specializes both the scalar and every coefficient. -/
noncomputable def simplyBlockedSpecialization {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n) :
    GridChainMinus R n →ₛₗ[simplyBlockedRingHom R i] GridChainHat R n i :=
  Finsupp.mapRange.linearMap (simplyBlockedRingHom R i).toSemilinearMap

/-- Specializing a grid chain applies `MvPolynomial.killCompl` to each coefficient. -/
@[simp]
theorem simplyBlockedSpecialization_apply {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n)
    (c : GridChainMinus R n) (x : GridState n) :
    simplyBlockedSpecialization R i c x =
      MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective (c x) := by
  rw [simplyBlockedSpecialization, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    RingHom.coe_toSemilinearMap, simplyBlockedRingHom_apply]

/-- Specialization sends a single supported coefficient to the single supported specialized
coefficient. -/
@[simp]
theorem simplyBlockedSpecialization_single {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n)
    (x : GridState n) (a : MvPolynomial (Fin n) R) :
    simplyBlockedSpecialization R i (Finsupp.single x a) =
      Finsupp.single x
        (MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective a) := by
  classical
  rw [simplyBlockedSpecialization, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    RingHom.coe_toSemilinearMap, simplyBlockedRingHom_apply]

/-- Renaming the unblocked columns also renames the surviving variables, carrying the blocked
column `i` to `e i`. -/
noncomputable def simplyBlockedRenameEquiv {n m : ℕ} (R : Type*) [CommSemiring R]
    (e : Fin n ≃ Fin m) (i : Fin n) :
    MvPolynomial {c : Fin n // c ≠ i} R ≃ₐ[R]
      MvPolynomial {c : Fin m // c ≠ e i} R :=
  renameEquiv R (e.subtypeEquiv fun _ => not_congr e.injective.eq_iff.symm)

/-- Renaming the surviving variables is polynomial renaming along the induced equivalence
of complements of the blocked columns. This expansion is for support computations;
simplification instead uses the variable-level formula `simplyBlockedRenameEquiv_X`. -/
theorem simplyBlockedRenameEquiv_apply {n m : ℕ} (R : Type*) [CommSemiring R]
    (e : Fin n ≃ Fin m) (i : Fin n) (p : MvPolynomial {c : Fin n // c ≠ i} R) :
    simplyBlockedRenameEquiv R e i p =
      rename (e.subtypeEquiv fun _ => not_congr e.injective.eq_iff.symm) p :=
  (rfl)

/-- Renaming the surviving variables and its inverse form a `RingHomInvPair`, so that maps
semilinear along the renaming can be inverted. -/
noncomputable instance simplyBlockedRenameRingHomInvPair {n m : ℕ} (R : Type*)
    [CommSemiring R] (e : Fin n ≃ Fin m) (i : Fin n) :
    RingHomInvPair
      ((simplyBlockedRenameEquiv R e i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin m // c ≠ e i} R)
      ((simplyBlockedRenameEquiv R e i).toRingEquiv.symm :
        MvPolynomial {c : Fin m // c ≠ e i} R →+* MvPolynomial {c : Fin n // c ≠ i} R) :=
  RingHomInvPair.of_ringEquiv _

/-- The inverse renaming of the surviving variables and the forward renaming form a
`RingHomInvPair`. -/
noncomputable instance simplyBlockedRenameRingHomInvPairSymm {n m : ℕ} (R : Type*)
    [CommSemiring R] (e : Fin n ≃ Fin m) (i : Fin n) :
    RingHomInvPair
      ((simplyBlockedRenameEquiv R e i).toRingEquiv.symm :
        MvPolynomial {c : Fin m // c ≠ e i} R →+* MvPolynomial {c : Fin n // c ≠ i} R)
      ((simplyBlockedRenameEquiv R e i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin m // c ≠ e i} R) :=
  RingHomInvPair.of_ringEquiv_symm _

/-- A surviving variable is renamed by the underlying column equivalence. -/
@[simp]
theorem simplyBlockedRenameEquiv_X {n m : ℕ} (R : Type*) [CommSemiring R]
    (e : Fin n ≃ Fin m) (i : Fin n) (c : {c : Fin n // c ≠ i}) :
    simplyBlockedRenameEquiv R e i (X c) = X ⟨e c, fun h => c.property (e.injective h)⟩ := by
  simp [simplyBlockedRenameEquiv, Equiv.subtypeEquiv]

/-- Blocking a column and then renaming the surviving variables agrees with renaming all
columns first and blocking the image column. -/
theorem simplyBlockedRingHom_rename {n m : ℕ} (R : Type*) [CommSemiring R]
    (e : Fin n ≃ Fin m) (i : Fin n) (p : MvPolynomial (Fin n) R) :
    simplyBlockedRingHom R (e i) (rename e p) =
      simplyBlockedRenameEquiv R e i (simplyBlockedRingHom R i p) := by
  have h : (killCompl (R := R) (f := (Subtype.val : {c : Fin m // c ≠ e i} → Fin m))
      Subtype.val_injective).comp (rename e) =
      (simplyBlockedRenameEquiv R e i).toAlgHom.comp
        (killCompl (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
          Subtype.val_injective) := by
    ext c
    by_cases hc : c = i
    · subst c
      simp
    · have hec : e c ≠ e i := fun h => hc (e.injective h)
      have hX : X c = rename Subtype.val (X (R := R) (⟨c, hc⟩ : {c // c ≠ i})) := by
        simp
      have heX : X (e c) = rename Subtype.val
          (X (R := R) (⟨e c, hec⟩ : {c // c ≠ e i})) := by simp
      simp only [AlgHom.comp_apply, rename_X]
      rw [hX, killCompl_rename_app, heX, killCompl_rename_app]
      simp
  exact DFunLike.congr_fun h p

section ColumnMap

variable {n m : ℕ} (R : Type*)

variable [CommSemiring R] (π : Fin m → Fin n) (i : Fin n) (j : Fin m)

/-- Rename surviving source variables along `π`, then block the target column. -/
noncomputable def simplyBlockedRingHomAlong :
    MvPolynomial {c : Fin m // c ≠ j} R →+* MvPolynomial {c : Fin n // c ≠ i} R :=
  (simplyBlockedRingHom R i).comp
    ((rename (R := R) π).toRingHom.comp (rename Subtype.val).toRingHom)

/-- A surviving variable is renamed and specialized. -/
@[simp]
theorem simplyBlockedRingHomAlong_X (c : {c : Fin m // c ≠ j}) :
    simplyBlockedRingHomAlong R π i j (X c) = simplyBlockedRingHom R i (X (π c)) := by
  simp [simplyBlockedRingHomAlong]

/-- Ground coefficients are unchanged. -/
@[simp]
theorem simplyBlockedRingHomAlong_C (r : R) :
    simplyBlockedRingHomAlong R π i j (C r) = C r := by
  simp [simplyBlockedRingHomAlong]

/-- Renaming commutes with blocking when `π` carries the blocked source column to the target. -/
theorem simplyBlockedRingHomAlong_specialization (hπ : π j = i)
    (p : MvPolynomial (Fin m) R) :
    simplyBlockedRingHomAlong R π i j (simplyBlockedRingHom R j p) =
      simplyBlockedRingHom R i (rename π p) := by
  have h : (simplyBlockedRingHomAlong R π i j).comp (simplyBlockedRingHom R j) =
      (simplyBlockedRingHom R i).comp (rename π).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [simplyBlockedRingHomAlong]
    · intro c
      by_cases hc : c = j
      · subst c
        simp [hπ]
      · have hX : X c = rename Subtype.val
            (X (R := R) (⟨c, hc⟩ : {c : Fin m // c ≠ j})) := by simp
        simp only [RingHom.comp_apply, simplyBlockedRingHom_apply]
        rw [hX, killCompl_rename_app]
        simp [simplyBlockedRingHomAlong]
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    RingHom.congr_fun h p

end ColumnMap

/-! ### Specializing semilinear maps -/

section SemilinearMap

variable {n m : ℕ} (R : Type*) [CommSemiring R] (i : Fin n) (j : Fin m)

variable {σ : MvPolynomial (Fin m) R →+* MvPolynomial (Fin n) R}
  {τ : MvPolynomial {c : Fin m // c ≠ j} R →+* MvPolynomial {c : Fin n // c ≠ i} R}

/-- Compatible coefficient specialization intertwines semilinear maps as soon as it does so on
basis generators, allowing different source and target grid sizes and blocked columns. -/
theorem simplyBlockedSpecialization_apply_eq_of_single
    {f : GridChainMinus R m →ₛₗ[σ] GridChainMinus R n}
    {g : GridChainHat R m j →ₛₗ[τ] GridChainHat R n i}
    (hστ : ∀ p, τ (simplyBlockedRingHom R j p) = simplyBlockedRingHom R i (σ p))
    (h : ∀ x, simplyBlockedSpecialization R i (f (Finsupp.single x 1)) = g (Finsupp.single x 1))
    (c : GridChainMinus R m) :
    simplyBlockedSpecialization R i (f c) = g (simplyBlockedSpecialization R j c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x p =>
    rw [← Finsupp.smul_single_one x p]
    simp only [map_smulₛₗ, h, hστ, simplyBlockedSpecialization_single, map_one]

variable (τ : MvPolynomial {c : Fin m // c ≠ j} R →+* MvPolynomial {c : Fin n // c ≠ i} R)
  (f : GridChainMinus R m →ₛₗ[σ] GridChainMinus R n)

/-- Specialize the matrix coefficients of a semilinear unblocked grid map along a homomorphism
`τ` of surviving coefficient rings. The full coefficient homomorphism `σ` need not be a variable
renaming, and compatibility with blocking is needed only for the descent equations. -/
noncomputable def simplyBlockedMap :
    GridChainHat R m j →ₛₗ[τ] GridChainHat R n i :=
  (Finsupp.linearCombination _ fun x : GridState m =>
    simplyBlockedSpecialization R i (f (Finsupp.single x 1))).comp
      (Finsupp.mapRange.linearMap τ.toSemilinearMap)

/-- The specialized map on a single coefficient. -/
theorem simplyBlockedMap_single (x : GridState m)
    (p : MvPolynomial {c : Fin m // c ≠ j} R) :
    simplyBlockedMap R i j τ f (Finsupp.single x p) =
      τ p • simplyBlockedSpecialization R i (f (Finsupp.single x 1)) := by
  simp [simplyBlockedMap]

/-- Matrix evaluation of the specialized map. -/
@[simp 900] -- Prefer the generator formula to the general chain expansion.
theorem simplyBlockedMap_apply_apply (c : GridChainHat R m j) (y : GridState n) :
    simplyBlockedMap R i j τ f c y = c.sum fun x p =>
      τ p * simplyBlockedRingHom R i (f (Finsupp.single x 1) y) := by
  simp only [simplyBlockedMap, LinearMap.comp_apply, Finsupp.linearCombination_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    simplyBlockedSpecialization_apply, simplyBlockedRingHom_apply]
  exact Finsupp.sum_mapRange_index fun _ => zero_mul _

/-- Specialization intertwines the unblocked map with its specialized map. -/
theorem simplyBlockedMap_simplyBlockedSpecialization
    (hστ : ∀ p, τ (simplyBlockedRingHom R j p) = simplyBlockedRingHom R i (σ p))
    (c : GridChainMinus R m) :
    simplyBlockedMap R i j τ f (simplyBlockedSpecialization R j c) =
      simplyBlockedSpecialization R i (f c) := by
  exact (simplyBlockedSpecialization_apply_eq_of_single R i j hστ
    (fun x => by rw [simplyBlockedMap_single, map_one, one_smul]) c).symm

/-- The matrix entry on a basis generator is the specialized original matrix entry. -/
@[simp]
theorem simplyBlockedMap_single_apply (x : GridState m) (y : GridState n) :
    simplyBlockedMap R i j τ f (Finsupp.single x 1) y =
      simplyBlockedRingHom R i (f (Finsupp.single x 1) y) := by
  rw [simplyBlockedMap_single, map_one, one_smul, simplyBlockedSpecialization_apply,
    simplyBlockedRingHom_apply]

end SemilinearMap

section LinearMap

variable {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n)

/-- Setting `V_i = 0` in a squarefree monomial discards it if it contains `V_i`; otherwise it
leaves the product of the same variables. -/
theorem killCompl_monomial_sum_single_one (s : Finset (Fin n)) :
    MvPolynomial.killCompl (R := R) (f := Subtype.val)
      (Subtype.val_injective : Function.Injective
        (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
      (monomial (∑ c ∈ s, Finsupp.single c 1) 1) =
      if i ∈ s then 0 else ∏ c ∈ s.subtype (· ≠ i), X c := by
  split_ifs with hi
  · refine killCompl_monomial_eq_zero_of_notMem_range _ 1 (a := i) ?_ ?_
    · rw [Finsupp.support_sum_eq_biUnion _ (by simp)]
      simpa using hi
    · rintro ⟨⟨c, hc⟩, hci⟩
      exact hc hci
  · have hrename :
        rename (Subtype.val : {c : Fin n // c ≠ i} → Fin n)
            (∏ c ∈ s.subtype (· ≠ i), X (R := R) c) =
          monomial (∑ c ∈ s, Finsupp.single c 1) 1 := by
      rw [map_prod, monomial_sum_one]
      simp only [rename_X]
      simpa only [← X_pow_eq_monomial, pow_one] using
        Finset.prod_subtype_of_mem (s := s) (p := fun c : Fin n => c ≠ i) (X (R := R))
          (fun c hc (hci : c = i) => hi (hci ▸ hc))
    rw [← hrename, killCompl_rename_app]

end LinearMap

/-! ### Specialization as a quotient map -/

section Specialization

variable {n : ℕ} (R : Type*) [CommSemiring R] (i : Fin n)

/-- The coefficient specialization is surjective. -/
theorem simplyBlockedRingHom_surjective : Function.Surjective (simplyBlockedRingHom R i) :=
  fun p ↦ ⟨MvPolynomial.rename Subtype.val p, by simp⟩

/-- Specialization at `V_i = 0` is surjective: renaming the surviving variables back is a
section of it. -/
theorem simplyBlockedSpecialization_surjective :
    Function.Surjective (simplyBlockedSpecialization R i) := by
  intro g
  obtain ⟨f, hf⟩ := Finsupp.mapRange_surjective (simplyBlockedRingHom R i) (map_zero _)
    (simplyBlockedRingHom_surjective R i) g
  refine ⟨f, ?_⟩
  unfold simplyBlockedSpecialization
  exact hf

/-- Including the surviving variables `V_c`, `c ≠ i`, in the full polynomial ring, coefficientwise.
It is a section of the specialization at `V_i = 0`
(`TauCeti.simplyBlockedSpecialization_simplyBlockedLift`), linear over the ground semiring. -/
noncomputable def simplyBlockedLift : GridChainHat R n i →ₗ[R] GridChainMinus R n :=
  Finsupp.mapRange.linearMap (MvPolynomial.rename Subtype.val).toLinearMap

/-- The lift renames each coefficient into the full polynomial ring. -/
@[simp]
theorem simplyBlockedLift_apply (c : GridChainHat R n i) (x : GridState n) :
    simplyBlockedLift R i c x = MvPolynomial.rename Subtype.val (c x) :=
  (rfl)

/-- Specializing the lift of a chain at `V_i = 0` recovers the chain. -/
@[simp]
theorem simplyBlockedSpecialization_simplyBlockedLift (c : GridChainHat R n i) :
    simplyBlockedSpecialization R i (simplyBlockedLift R i c) = c := by
  ext x
  rw [simplyBlockedSpecialization_apply, simplyBlockedLift_apply, killCompl_rename_app]

/-- Specialization at `V_i = 0`, as a linear map over the ground semiring. -/
noncomputable def simplyBlockedSpecializationLinearMap :
    GridChainMinus R n →ₗ[R] GridChainHat R n i :=
  Finsupp.mapRange.linearMap
    (MvPolynomial.killCompl (R := R) (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
      Subtype.val_injective).toLinearMap

/-- The linear specialization is `simplyBlockedSpecialization`. -/
@[simp]
theorem simplyBlockedSpecializationLinearMap_apply (c : GridChainMinus R n) :
    simplyBlockedSpecializationLinearMap R i c = simplyBlockedSpecialization R i c :=
  (rfl)

/-- The linear specialization at `V_i = 0` is surjective. -/
theorem simplyBlockedSpecializationLinearMap_surjective :
    Function.Surjective (simplyBlockedSpecializationLinearMap (n := n) R i) := by
  intro y
  simpa only [simplyBlockedSpecializationLinearMap_apply] using
    simplyBlockedSpecialization_surjective R i y

/-- Multiplication by the blocked variable `V_i` is injective on the unblocked grid chain
module. -/
theorem X_smul_gridChainMinus_injective :
    Function.Injective
      fun c : GridChainMinus R n => (MvPolynomial.X i : MvPolynomial (Fin n) R) • c :=
  (MvPolynomial.isRegular_X (R := R) (n := i)).left.isSMulRegular.finsupp

/-- Multiplication by `V_i` and coefficient specialization form an exact pair. -/
theorem exact_X_mul_simplyBlockedRingHom :
    Function.Exact (fun p : MvPolynomial (Fin n) R => MvPolynomial.X i * p)
      (simplyBlockedRingHom R i) := by
  have hrange : Set.range (Subtype.val : {c : Fin n // c ≠ i} → Fin n) = {i}ᶜ := by
    ext d
    simp
  intro p
  rw [simplyBlockedRingHom_apply,
    MvPolynomial.killCompl_eq_zero_iff_X_dvd Subtype.val_injective hrange]
  constructor <;> rintro ⟨q, hq⟩ <;> exact ⟨q, hq.symm⟩

/-- The chains killed by specialization at `V_i = 0` are exactly the multiples of `V_i`:
together with `TauCeti.X_smul_gridChainMinus_injective` and
`TauCeti.simplyBlockedSpecialization_surjective` this presents the specialized chain module as
the quotient of `GC⁻` by a copy of itself. -/
theorem exact_X_smul_simplyBlockedSpecialization :
    Function.Exact
      (fun c : GridChainMinus R n => (MvPolynomial.X i : MvPolynomial (Fin n) R) • c)
      (simplyBlockedSpecialization R i) := by
  have hmap :
      (fun c : GridChainMinus R n => (MvPolynomial.X i : MvPolynomial (Fin n) R) • c) =
        Finsupp.mapRange (fun p => MvPolynomial.X i * p) (mul_zero _) := by
    funext c
    ext x
    simp [Finsupp.smul_apply]
  intro c
  rw [Finsupp.ext_iff, hmap, Finsupp.range_mapRange]
  simp only [simplyBlockedSpecialization_apply, Finsupp.coe_zero, Pi.zero_apply,
    Set.mem_ofPred_eq]
  exact forall_congr' fun x => exact_X_mul_simplyBlockedRingHom R i (c x)

/-- `TauCeti.exact_X_smul_simplyBlockedSpecialization` with multiplication by `V_i` and the
specialization at `V_i = 0` as linear maps over the ground semiring. -/
theorem exact_X_smul_simplyBlockedSpecializationLinearMap :
    Function.Exact
      (DistribSMul.toLinearMap R (GridChainMinus R n) (MvPolynomial.X i : MvPolynomial (Fin n) R))
      (simplyBlockedSpecializationLinearMap R i) := by
  intro c
  simpa only [simplyBlockedSpecializationLinearMap_apply, Set.mem_range,
    DistribSMul.toLinearMap_apply] using
    exact_X_smul_simplyBlockedSpecialization R i c

/-- Specialization at `V_i = 0` kills multiples of `V_i`. -/
@[simp]
theorem simplyBlockedSpecialization_X_smul (c : GridChainMinus R n) :
    simplyBlockedSpecialization R i ((MvPolynomial.X i : MvPolynomial (Fin n) R) • c) = 0 :=
  (exact_X_smul_simplyBlockedSpecialization R i _).mpr ⟨c, rfl⟩

end Specialization

section Relabeling

variable {n : ℕ} (R : Type*) [CommSemiring R]

namespace GridChain

/-- Relabel the columns of a chain of the specialization `V_i = 0` by `κ`, renaming its surviving
variables by `κ` as well, so that the blocked column becomes `κ i`. -/
noncomputable def simplyBlockedRelabelColumnsEquiv (κ : Equiv.Perm (Fin n)) (i : Fin n) :
    GridChainHat R n i ≃ₛₗ[((simplyBlockedRenameEquiv R κ i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+* MvPolynomial {c : Fin n // c ≠ κ i} R)]
      GridChainHat R n (κ i) :=
  (Finsupp.mapRange.linearEquiv
    (simplyBlockedRenameEquiv R κ i).toRingEquiv.toSemilinearEquiv).trans
    (relabelColumnsEquiv κ)

/-- The coefficient of a relabeled specialized chain is the renamed coefficient at the
inverse-relabeled state. -/
@[simp]
theorem simplyBlockedRelabelColumnsEquiv_apply (κ : Equiv.Perm (Fin n)) (i : Fin n)
    (c : GridChainHat R n i) (y : GridState n) :
    simplyBlockedRelabelColumnsEquiv R κ i c y =
      simplyBlockedRenameEquiv R κ i (c (y.relabelColumns κ.symm)) := by
  simp only [simplyBlockedRelabelColumnsEquiv, LinearEquiv.trans_apply, relabelColumnsEquiv_apply,
    Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply,
    RingEquiv.toSemilinearEquiv_apply, AlgEquiv.coe_toRingEquiv]

/-- The inverse relabeling reads coefficients at relabeled states and undoes the renaming. -/
@[simp]
theorem simplyBlockedRelabelColumnsEquiv_symm_apply (κ : Equiv.Perm (Fin n)) (i : Fin n)
    (c : GridChainHat R n (κ i)) (y : GridState n) :
    (simplyBlockedRelabelColumnsEquiv R κ i).symm c y =
      (simplyBlockedRenameEquiv R κ i).symm (c (y.relabelColumns κ)) := by
  rw [AlgEquiv.eq_symm_apply]
  have h := congrArg (fun c => c (y.relabelColumns κ))
    ((simplyBlockedRelabelColumnsEquiv R κ i).apply_symm_apply c)
  simpa only [simplyBlockedRelabelColumnsEquiv_apply, GridState.relabelColumns_relabelColumns,
    Equiv.self_trans_symm, GridState.relabelColumns_refl] using h

/-- The column relabeling sends a generator to the relabeled generator with renamed
coefficient. -/
@[simp]
theorem simplyBlockedRelabelColumnsEquiv_single (κ : Equiv.Perm (Fin n)) (i : Fin n)
    (x : GridState n) (p : MvPolynomial {c : Fin n // c ≠ i} R) :
    simplyBlockedRelabelColumnsEquiv R κ i (Finsupp.single x p) =
      Finsupp.single (x.relabelColumns κ) (simplyBlockedRenameEquiv R κ i p) := by
  simp only [simplyBlockedRelabelColumnsEquiv, LinearEquiv.trans_apply,
    Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_single, relabelColumnsEquiv_single,
    RingEquiv.toSemilinearEquiv_apply, AlgEquiv.coe_toRingEquiv]

end GridChain

/-- Row relabeling commutes with setting `V_i = 0`. -/
@[simp]
theorem simplyBlockedSpecialization_relabelRowsEquiv (ρ : Equiv.Perm (Fin n)) (i : Fin n)
    (c : GridChainMinus R n) :
    simplyBlockedSpecialization R i (GridChain.relabelRowsEquiv ρ c) =
      GridChain.relabelRowsEquiv ρ (simplyBlockedSpecialization R i c) := by
  ext y : 1
  simp only [simplyBlockedSpecialization_apply, GridChain.relabelRowsEquiv_apply]

/-- Column relabeling with renamed variables commutes with specialization, when the blocked
column is relabeled too. -/
@[simp]
theorem simplyBlockedSpecialization_relabelColumnsRenameEquiv (κ : Equiv.Perm (Fin n))
    (i : Fin n) (c : GridChainMinus R n) :
    simplyBlockedSpecialization R (κ i) (GridChain.relabelColumnsRenameEquiv R κ c) =
      GridChain.simplyBlockedRelabelColumnsEquiv R κ i (simplyBlockedSpecialization R i c) := by
  ext y : 1
  rw [simplyBlockedSpecialization_apply, ← LinearEquiv.coe_coe,
    GridChain.relabelColumnsRenameEquiv_apply, GridChain.simplyBlockedRelabelColumnsEquiv_apply,
    simplyBlockedSpecialization_apply, ← simplyBlockedRingHom_apply, ← simplyBlockedRingHom_apply,
    simplyBlockedRingHom_rename]

end Relabeling

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)
variable (R : Type*) [CommSemiring R]

/-- A rectangle covering the blocked `O`-marking has weight zero after specialization. -/
@[simp]
theorem killCompl_OMonomial_eq_zero_of_mem {i : Fin n} {r : GridRectangle n}
    (hi : i ∈ G.OColumns r) :
    MvPolynomial.killCompl (R := R) (f := Subtype.val)
      (Subtype.val_injective : Function.Injective
        (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
      (G.OMonomial R r) = 0 := by
  rw [G.OMonomial_eq_monomial R, killCompl_monomial_sum_single_one, ite_eq_left hi]

/-- A rectangle avoiding the blocked `O`-marking keeps as its weight the product of the variables
of the other `O`-markings it covers. -/
@[simp]
theorem killCompl_OMonomial_eq_prod_of_notMem {i : Fin n} {r : GridRectangle n}
    (hi : i ∉ G.OColumns r) :
    MvPolynomial.killCompl (R := R) (f := Subtype.val)
      (Subtype.val_injective : Function.Injective
        (Subtype.val : {c : Fin n // c ≠ i} → Fin n)) (G.OMonomial R r) =
      ∏ c ∈ (G.OColumns r).subtype (· ≠ i), MvPolynomial.X c := by
  rw [G.OMonomial_eq_monomial R, killCompl_monomial_sum_single_one, ite_eq_right hi]

/-- The rectangles counted after blocking column `i`: unblocked rectangles which do not cover
the `O`-marking in column `i`. -/
noncomputable def simplyBlockedRectangles (i : Fin n) (x y : GridState n) :
    Finset (GridRectangleBetween x y) :=
  (G.unblockedRectangles x y).filter fun r => i ∉ G.OColumns r.toGridRectangle

/-- Membership in the simply blocked rectangle set is emptiness, `X`-avoidance, and avoidance of
the `O`-marking in the selected column. -/
@[simp]
theorem mem_simplyBlockedRectangles (i : Fin n) {x y : GridState n}
    (r : GridRectangleBetween x y) :
    r ∈ G.simplyBlockedRectangles i x y ↔
      r.IsEmpty ∧ Disjoint r.toGridRectangle.coveredSquares G.XSet ∧
        (i, G.O i) ∉ r.toGridRectangle.coveredSquares := by
  rw [simplyBlockedRectangles, Finset.mem_filter, G.mem_unblockedRectangles,
    G.mem_OColumns]
  tauto

/-- Simply blocked rectangles are among those counted by the unblocked differential. -/
theorem simplyBlockedRectangles_subset_unblockedRectangles (i : Fin n) (x y : GridState n) :
    G.simplyBlockedRectangles i x y ⊆ G.unblockedRectangles x y :=
  Finset.filter_subset _ _

/-- There are no simply blocked rectangles from a grid state to itself. -/
@[simp]
theorem simplyBlockedRectangles_self (i : Fin n) (x : GridState n) :
    G.simplyBlockedRectangles i x x = ∅ := by
  simp [simplyBlockedRectangles]

/-- The matrix coefficient of the simply blocked map, obtained by specializing the
corresponding coefficient of `GC⁻`. -/
noncomputable def simplyBlockedCoefficient (i : Fin n) (x y : GridState n) :
    MvPolynomial {c : Fin n // c ≠ i} R :=
  MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective
    (G.unblockedCoefficient R x y)

/-- The simply blocked coefficient is the finite sum over the contributing rectangles.  Terms
covering the blocked marking disappear; each of the other terms is the product of the variables of
the remaining `O`-markings the rectangle covers. -/
theorem simplyBlockedCoefficient_eq_sum (i : Fin n) (x y : GridState n) :
    G.simplyBlockedCoefficient R i x y =
      ∑ r ∈ G.simplyBlockedRectangles i x y,
        ∏ c ∈ (G.OColumns r.toGridRectangle).subtype (· ≠ i), MvPolynomial.X c := by
  classical
  rw [simplyBlockedCoefficient, G.unblockedCoefficient_def R, map_sum,
    ← Finset.sum_subset (G.simplyBlockedRectangles_subset_unblockedRectangles i x y)]
  · refine Finset.sum_congr rfl fun r hr => ?_
    refine G.killCompl_OMonomial_eq_prod_of_notMem R ?_
    rw [G.mem_OColumns]
    exact ((G.mem_simplyBlockedRectangles i r).mp hr).2.2
  · intro r hr hri
    have hi : i ∈ G.OColumns r.toGridRectangle := by
      by_contra hi
      exact hri (Finset.mem_filter.mpr ⟨hr, hi⟩)
    exact G.killCompl_OMonomial_eq_zero_of_mem R hi

/-- The simply blocked map has no diagonal matrix coefficient. -/
@[simp]
theorem simplyBlockedCoefficient_self (i : Fin n) (x : GridState n) :
    G.simplyBlockedCoefficient R i x x = 0 := by
  simp [simplyBlockedCoefficient]

/-- The value of the simply blocked map on one grid-state generator. -/
noncomputable def simplyBlockedDifferentialOnGenerator (i : Fin n) (x : GridState n) :
    GridChainHat R n i :=
  Finsupp.equivFunOnFinite.symm (G.simplyBlockedCoefficient R i x)

/-- The `y`-coefficient of the simply blocked map on the generator `x`. -/
@[simp]
theorem simplyBlockedDifferentialOnGenerator_apply (i : Fin n) (x y : GridState n) :
    G.simplyBlockedDifferentialOnGenerator R i x y = G.simplyBlockedCoefficient R i x y :=
  congrFun (Finsupp.coe_equivFunOnFinite_symm (G.simplyBlockedCoefficient R i x)) y

/-- The simply blocked map of a generator is supported on its column transpositions. -/
theorem simplyBlockedDifferentialOnGenerator_support_subset (i : Fin n) (x : GridState n) :
    (G.simplyBlockedDifferentialOnGenerator R i x).support ⊆ x.columnSwapNeighbors := by
  intro y hy
  rw [Finsupp.mem_support_iff, simplyBlockedDifferentialOnGenerator_apply] at hy
  apply G.unblockedDifferentialOnGenerator_support_subset R x
  rw [Finsupp.mem_support_iff, G.unblockedDifferentialOnGenerator_apply R]
  intro hzero
  rw [simplyBlockedCoefficient, hzero, map_zero] at hy
  exact hy rfl

/-- Specializing the unblocked differential of a generator gives its simply blocked row. -/
@[simp]
theorem simplyBlockedSpecialization_unblockedDifferentialOnGenerator (i : Fin n)
    (x : GridState n) :
    simplyBlockedSpecialization R i (G.unblockedDifferentialOnGenerator R x) =
      G.simplyBlockedDifferentialOnGenerator R i x := by
  apply Finsupp.ext
  intro y
  rw [simplyBlockedSpecialization_apply,
    G.simplyBlockedDifferentialOnGenerator_apply R i x y,
    G.unblockedDifferentialOnGenerator_apply R x y, simplyBlockedCoefficient]

/-- The linear map obtained from the `GC⁻` differential by setting `V_i = 0`.  For a knot grid
over a coefficient semiring of characteristic two it is the simply blocked differential;
outside characteristic two it is only the unsigned candidate map, since sign correction uses
additive inverses and so needs a commutative coefficient ring.  A link with multiple components
requires one blocked marking on each component instead. -/
noncomputable def simplyBlockedDifferential (i : Fin n) :
    GridChainHat R n i →ₗ[MvPolynomial {c : Fin n // c ≠ i} R] GridChainHat R n i :=
  Finsupp.linearCombination (MvPolynomial {c : Fin n // c ≠ i} R)
    (G.simplyBlockedDifferentialOnGenerator R i)

/-- The simply blocked map sends a single generator to its rectangle-weight row. -/
@[simp]
theorem simplyBlockedDifferential_single (i : Fin n) (x : GridState n) :
    G.simplyBlockedDifferential R i (Finsupp.single x 1) =
      G.simplyBlockedDifferentialOnGenerator R i x := by
  simp [simplyBlockedDifferential]

/-- The simply blocked map is the finite sum of its generator rows over the support of
a chain. -/
theorem simplyBlockedDifferential_apply (i : Fin n) (c : GridChainHat R n i) :
    G.simplyBlockedDifferential R i c =
      c.sum fun x a => a • G.simplyBlockedDifferentialOnGenerator R i x := by
  rw [simplyBlockedDifferential, Finsupp.linearCombination_apply]

/-- The coefficient formula for the simply blocked map on an arbitrary chain. -/
@[simp]
theorem simplyBlockedDifferential_apply_apply (i : Fin n)
    (c : GridChainHat R n i) (y : GridState n) :
    G.simplyBlockedDifferential R i c y =
      c.sum fun x a => a * G.simplyBlockedCoefficient R i x y := by
  rw [G.simplyBlockedDifferential_apply R i c]
  simp [Finsupp.sum_apply]

/-- Coefficientwise specialization intertwines the unblocked and simply blocked maps. -/
@[simp]
theorem simplyBlockedSpecialization_unblockedDifferential (i : Fin n)
    (c : GridChainMinus R n) :
    simplyBlockedSpecialization R i (G.unblockedDifferential R c) =
      G.simplyBlockedDifferential R i (simplyBlockedSpecialization R i c) :=
  simplyBlockedSpecialization_apply_eq_of_single R i i (fun _ => rfl) (fun x => by
    rw [G.unblockedDifferential_single R x,
      G.simplyBlockedSpecialization_unblockedDifferentialOnGenerator R i x,
      G.simplyBlockedDifferential_single R i x]) c

/-- A chain equation descends through specialization for any compatible functions. -/
theorem map_simplyBlockedDifferential_of_simplyBlockedSpecialization {m : ℕ} {G' : GridDiagram m}
    {i : Fin n} {j : Fin m}
    {f : GridChainMinus R m → GridChainMinus R n}
    {g : GridChainHat R m j → GridChainHat R n i}
    (hg : ∀ c, g (simplyBlockedSpecialization R j c) = simplyBlockedSpecialization R i (f c))
    (hf : ∀ c, f (G'.unblockedDifferential R c) = G.unblockedDifferential R (f c))
    (c : GridChainHat R m j) :
    g (G'.simplyBlockedDifferential R j c) = G.simplyBlockedDifferential R i (g c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R j c
  rw [← simplyBlockedSpecialization_unblockedDifferential, hg, hg,
    ← simplyBlockedSpecialization_unblockedDifferential, hf]

/-- Over the ground semiring, linear specialization intertwines the unblocked and simply blocked
maps. -/
theorem simplyBlockedSpecializationLinearMap_comp_unblockedDifferential (i : Fin n) :
    simplyBlockedSpecializationLinearMap R i ∘ₗ (G.unblockedDifferential R).restrictScalars R =
      (G.simplyBlockedDifferential R i).restrictScalars R ∘ₗ
        simplyBlockedSpecializationLinearMap R i :=
  LinearMap.ext (G.simplyBlockedSpecialization_unblockedDifferential R i)

end GridDiagram

end TauCeti
