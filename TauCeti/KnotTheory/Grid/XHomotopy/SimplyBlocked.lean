/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.Algebra.Homology.Linear
public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked
public import TauCeti.KnotTheory.Grid.XHomotopy.Complex

/-!
# The variables act trivially on simply blocked grid homology

Blocking the `O`-marking of column `i` specializes the unblocked grid complex `GC⁻` at `V_i = 0`
to the simply blocked complex `GC^`, a complex over `R[V_c | c ≠ i]`. The `X`-marking homotopy
`H_k` of `GC⁻` specializes in the same way to a map `hat H_k` of `GC^`
(`simplyBlockedXHomotopy`), and specializing the homotopy identity `∂⁻ ∘ H_k + H_k ∘ ∂⁻ = V_k + V_j`
gives

`∂^ ∘ hat H_k + hat H_k ∘ ∂^ = V_k + V_j` with `V_i` read as zero

(`simplyBlockedDifferential_comp_simplyBlockedXHomotopy_add_simplyBlockedXHomotopy_comp`), where
`O_j` is the `O`-marking in the row of `X_k`. So, as for `GC⁻`, the variables of two consecutive
`O`-markings of a link component act identically on the homology of `GC^`. Since `V_i` itself
acts by zero, every variable on the component of the blocked marking acts by zero on the homology
(`homologyMap_X_smul_simplyBlockedComplex_eq_zero_of_sameCycle`).

For a knot grid all markings lie on one component, so every variable acts by zero on the simply
blocked grid homology `G-hat` (`IsKnot.X_smul_simplyBlockedHomology`), and a polynomial acts through
its constant coefficient (`IsKnot.smul_simplyBlockedHomology`). The chain module of `GC^` is
finitely generated over the Noetherian ring `R[V_c | c ≠ i]` when `R` is Noetherian, hence so is
`G-hat`; and since the variables act by zero, `G-hat` is then finitely generated over `R` itself
(`IsKnot.finite_restrictScalars_simplyBlockedHomology`). Over a field `G-hat` is thus a
finite-dimensional vector space, although the complex computing it is not.

## Main definitions

* `TauCeti.GridDiagram.simplyBlockedXHomotopy`: the `X`-marking homotopy specialized at
  `V_i = 0`.
* `TauCeti.GridDiagram.simplyBlockedComplexXHomotopy`: the chain homotopy it provides on the
  simply blocked complex.

## Main results

* `TauCeti.GridDiagram.simplyBlockedSpecialization_XHomotopy`: specialization intertwines `H_k`
  with `hat H_k`.
* `simplyBlockedDifferential_comp_simplyBlockedXHomotopy_add_simplyBlockedXHomotopy_comp`: the
  specialized homotopy identity.
* `TauCeti.GridDiagram.homologyMap_X_smul_simplyBlockedComplex_eq_zero_of_sameCycle`: the variables
  on the component of the blocked marking act by zero on homology.
* `TauCeti.GridDiagram.IsKnot.X_smul_simplyBlockedHomology` and
  `TauCeti.GridDiagram.IsKnot.smul_simplyBlockedHomology`: on a knot grid every variable acts by
  zero on `G-hat`, and a polynomial acts through its constant coefficient.
* `TauCeti.GridDiagram.IsKnot.finite_simplyBlockedHomology` and
  `TauCeti.GridDiagram.IsKnot.finite_restrictScalars_simplyBlockedHomology`: over a Noetherian
  coefficient ring `G-hat` is finitely generated, over `R[V_c | c ≠ i]` and over `R`.

## References

This follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 4.6: by
Lemma 4.6.9 the variables of a knot grid act identically on grid homology, so on the simply blocked
theory, where one of them is zero, they all act by zero and `G-hat` is a finite-dimensional vector
space.
-/

public section

open CategoryTheory

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The specialized homotopy -/

section Specialization

variable (R : Type*) [CommSemiring R]

/-- Specialization at `V_i = 0` intertwines a linear map of `GC⁻` with a linear map of `GC^` as
soon as it does so on the generators. -/
private theorem simplyBlockedSpecialization_apply_eq_of_single (i : Fin n)
    {f : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n}
    {g : GridChainHat R n i →ₗ[MvPolynomial {c : Fin n // c ≠ i} R] GridChainHat R n i}
    (h : ∀ x, simplyBlockedSpecialization R i (f (Finsupp.single x 1)) = g (Finsupp.single x 1))
    (c : GridChainMinus R n) :
    simplyBlockedSpecialization R i (f c) = g (simplyBlockedSpecialization R i c) := by
  induction c using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add x a c _ _ ih =>
    rw [← Finsupp.smul_single_one x a]
    simp only [map_add, map_smul, LinearMap.map_smulₛₗ, h, ih,
      simplyBlockedSpecialization_single, map_one]

/-- The `X`-marking homotopy `H_k` specialized at `V_i = 0`: the map of the simply blocked chain
module counting the empty rectangles whose only covered `X`-marking is `X_k` and which avoid the
blocked `O`-marking, each weighted by the variables of the other `O`-markings it covers. -/
noncomputable def simplyBlockedXHomotopy (i k : Fin n) :
    GridChainHat R n i →ₗ[MvPolynomial {c : Fin n // c ≠ i} R] GridChainHat R n i :=
  Finsupp.linearCombination _ fun x =>
    simplyBlockedSpecialization R i (G.XHomotopy R k (Finsupp.single x 1))

/-- The specialized homotopy sends a generator to the specialization of its image under `H_k`. -/
theorem simplyBlockedXHomotopy_single (i k : Fin n) (x : GridState n) :
    G.simplyBlockedXHomotopy R i k (Finsupp.single x 1) =
      simplyBlockedSpecialization R i (G.XHomotopy R k (Finsupp.single x 1)) := by
  rw [simplyBlockedXHomotopy, Finsupp.linearCombination_single, one_smul]

/-- The matrix coefficients of the specialized homotopy are the specialized matrix coefficients of
`H_k`. -/
@[simp]
theorem simplyBlockedXHomotopy_single_apply (i k : Fin n) (x y : GridState n) :
    G.simplyBlockedXHomotopy R i k (Finsupp.single x 1) y =
      MvPolynomial.killCompl (σ := {c : Fin n // c ≠ i}) Subtype.val_injective
        (G.XHomotopyCoefficient R k x y) := by
  rw [simplyBlockedXHomotopy_single, simplyBlockedSpecialization_apply, XHomotopy_single_apply]

/-- Coefficientwise specialization at `V_i = 0` intertwines the `X`-marking homotopy with its
specialization. -/
@[simp]
theorem simplyBlockedSpecialization_XHomotopy (i k : Fin n) (c : GridChainMinus R n) :
    simplyBlockedSpecialization R i (G.XHomotopy R k c) =
      G.simplyBlockedXHomotopy R i k (simplyBlockedSpecialization R i c) :=
  simplyBlockedSpecialization_apply_eq_of_single R i
    (fun x => (G.simplyBlockedXHomotopy_single R i k x).symm) c

variable [CharP R 2]

/-- The homotopy identity `∂^ ∘ hat H_k + hat H_k ∘ ∂^ = V_k + V_j` on the simply blocked chain
module in characteristic two, where `O_j` is the `O`-marking in the row of `X_k` and the variable
`V_i` of the blocked column is read as zero. -/
theorem simplyBlockedDifferential_comp_simplyBlockedXHomotopy_add_simplyBlockedXHomotopy_comp
    (i k : Fin n) :
    G.simplyBlockedDifferential R i ∘ₗ G.simplyBlockedXHomotopy R i k +
        G.simplyBlockedXHomotopy R i k ∘ₗ G.simplyBlockedDifferential R i =
      MvPolynomial.killCompl (σ := {c : Fin n // c ≠ i}) Subtype.val_injective
          (MvPolynomial.X k + MvPolynomial.X (G.O.columnOfRow (G.X k)) :
            MvPolynomial (Fin n) R) • LinearMap.id := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  have hx : (Finsupp.single x 1 : GridChainHat R n i) =
      simplyBlockedSpecialization R i (Finsupp.single x 1) := by
    rw [simplyBlockedSpecialization_single, map_one]
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  have hid := congrArg (simplyBlockedSpecialization R i) (LinearMap.congr_fun
    (G.unblockedDifferential_comp_XHomotopy_add_XHomotopy_comp R k) (Finsupp.single x 1))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hid
  rw [hx, ← simplyBlockedSpecialization_XHomotopy,
    ← simplyBlockedSpecialization_unblockedDifferential,
    ← simplyBlockedSpecialization_unblockedDifferential, ← simplyBlockedSpecialization_XHomotopy,
    ← LinearMap.map_add, hid, LinearMap.map_smulₛₗ]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

end Specialization

/-! ### Chain homotopies and homology -/

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The specialized `X`-marking homotopy `hat H_k` as a chain homotopy on the simply blocked
complex, from multiplication by `V_k` to multiplication by `V_j`, where `O_j` is the `O`-marking in
the row of `X_k` and the variable `V_i` of the blocked column is read as zero. -/
noncomputable def simplyBlockedComplexXHomotopy (i k : Fin n) :
    Homotopy
      (MvPolynomial.killCompl (σ := {c : Fin n // c ≠ i}) Subtype.val_injective
          (MvPolynomial.X k : MvPolynomial (Fin n) R) • 𝟙 (G.simplyBlockedComplex R i))
      (MvPolynomial.killCompl (σ := {c : Fin n // c ≠ i}) Subtype.val_injective
          (MvPolynomial.X (G.O.columnOfRow (G.X k)) : MvPolynomial (Fin n) R) •
        𝟙 (G.simplyBlockedComplex R i)) where
  hom _ _ := eqToHom (G.simplyBlockedComplex_X R i ()) ≫
    ModuleCat.ofHom (G.simplyBlockedXHomotopy R i k) ≫
      eqToHom (G.simplyBlockedComplex_X R i ()).symm
  zero a b h := absurd (Subsingleton.elim b a) h
  comm _ := by
    -- Transport the identity across the object equation `X () = GC^` of the one-object complex.
    have transport : ∀ {A B : ModuleCat (MvPolynomial {c : Fin n // c ≠ i} R)} (e : A = B)
        (d h : B ⟶ B) (a b : MvPolynomial {c : Fin n // c ≠ i} R),
        a • 𝟙 B = d ≫ h + h ≫ d + b • 𝟙 B →
        a • 𝟙 A = (eqToHom e ≫ d ≫ eqToHom e.symm) ≫ (eqToHom e ≫ h ≫ eqToHom e.symm) +
          (eqToHom e ≫ h ≫ eqToHom e.symm) ≫ (eqToHom e ≫ d ≫ eqToHom e.symm) + b • 𝟙 A := by
      intro A B e d h a b hB
      subst e
      simpa using hB
    rw [dNext_eq _ (rfl : (ComplexShape.refl Unit).Rel () ()),
      prevD_eq _ (rfl : (ComplexShape.refl Unit).Rel () ()), HomologicalComplex.smul_f_apply,
      HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, simplyBlockedComplex_d]
    refine transport _ _ _ _ _ (ModuleCat.hom_ext ?_)
    have hid :=
      G.simplyBlockedDifferential_comp_simplyBlockedXHomotopy_add_simplyBlockedXHomotopy_comp R i k
    simp only [ModuleCat.hom_add, ModuleCat.hom_smul, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      ModuleCat.hom_id]
    rw [add_comm (G.simplyBlockedXHomotopy R i k ∘ₗ _), hid, ← add_smul]
    simp [add_assoc, CharTwo.add_self_eq_zero]

/-- Multiplication by the variables of two columns on the same link component, with the variable
of the blocked column read as zero, is chain homotopic on the simply blocked complex. -/
theorem nonempty_homotopy_killCompl_X_smul_of_pow_componentPerm_apply (i : Fin n) {c c' : Fin n}
    (m : ℕ) (h : (G.componentPerm ^ m) c = c') :
    Nonempty (Homotopy
      (MvPolynomial.killCompl (σ := {c : Fin n // c ≠ i}) Subtype.val_injective
          (MvPolynomial.X c : MvPolynomial (Fin n) R) • 𝟙 (G.simplyBlockedComplex R i))
      (MvPolynomial.killCompl (σ := {c : Fin n // c ≠ i}) Subtype.val_injective
          (MvPolynomial.X c' : MvPolynomial (Fin n) R) • 𝟙 (G.simplyBlockedComplex R i))) := by
  subst h
  induction m with
  | zero => exact ⟨Homotopy.refl _⟩
  | succ m ih =>
    obtain ⟨h⟩ := ih
    rw [pow_succ', Equiv.Perm.mul_apply]
    refine ⟨h.trans ((G.simplyBlockedComplexXHomotopy R i _).trans (Homotopy.ofEq ?_)).symm⟩
    rw [columnOfRow_X_componentPerm]

/-- The variables of the columns on the link component of the blocked `O`-marking act by zero on
the homology of the simply blocked complex. -/
theorem homologyMap_X_smul_simplyBlockedComplex_eq_zero_of_sameCycle {i : Fin n}
    {c : {c : Fin n // c ≠ i}} (hc : G.componentPerm.SameCycle i c) :
    HomologicalComplex.homologyMap
        ((MvPolynomial.X c : MvPolynomial {c : Fin n // c ≠ i} R) • 𝟙 (G.simplyBlockedComplex R i))
        () = 0 := by
  obtain ⟨m, hm⟩ := hc.exists_nat_pow_eq
  obtain ⟨h⟩ := G.nonempty_homotopy_killCompl_X_smul_of_pow_componentPerm_apply R i m hm
  rw [← MvPolynomial.rename_X Subtype.val c, MvPolynomial.killCompl_rename_app] at h
  simp [MvPolynomial.killCompl] at h
  rw [h.symm.homologyMap_eq, HomologicalComplex.homologyMap_zero]

namespace IsKnot

variable {G} (hG : G.IsKnot)
include hG

/-- On a knot grid every variable acts by zero on the simply blocked grid homology. -/
@[simp]
theorem X_smul_simplyBlockedHomology {i : Fin n} (c : {c : Fin n // c ≠ i})
    (x : hG.simplyBlockedHomology R i) :
    (MvPolynomial.X c : MvPolynomial {c : Fin n // c ≠ i} R) • x = 0 := by
  have hc : G.componentPerm.SameCycle i c :=
    ((G.isKnot_iff_componentPerm_isCycle).mp hG).sameCycle (G.componentPerm_apply_ne_self i)
      (G.componentPerm_apply_ne_self c)
  simpa using congrArg (fun f => f.hom x)
    (G.homologyMap_X_smul_simplyBlockedComplex_eq_zero_of_sameCycle R hc)

/-- On a knot grid a polynomial acts on the simply blocked grid homology through its constant
coefficient. -/
theorem smul_simplyBlockedHomology {i : Fin n} (p : MvPolynomial {c : Fin n // c ≠ i} R)
    (x : hG.simplyBlockedHomology R i) :
    p • x = (MvPolynomial.C (MvPolynomial.constantCoeff p) :
      MvPolynomial {c : Fin n // c ≠ i} R) • x := by
  induction p using MvPolynomial.induction_on generalizing x with
  | C r => rw [MvPolynomial.constantCoeff_C]
  | add p q hp hq => rw [add_smul, hp, hq, map_add, map_add, add_smul]
  | mul_X p c _ => simp [mul_smul]

/-- Over a Noetherian coefficient ring, the simply blocked grid homology of a knot grid is a
finitely generated module over the polynomial ring of the unblocked columns. -/
theorem finite_simplyBlockedHomology [IsNoetherianRing R] (i : Fin n) :
    Module.Finite (MvPolynomial {c : Fin n // c ≠ i} R) (hG.simplyBlockedHomology R i) := by
  have : Module.Finite (MvPolynomial {c : Fin n // c ≠ i} R)
      ((G.simplyBlockedComplex R i).sc' () () ()).X₂ :=
    Module.Finite.equiv (eqToIso (G.simplyBlockedComplex_X R i ())).symm.toLinearEquiv
  exact Module.Finite.of_surjective _ (hG.simplyBlockedHomologyClass_surjective R i)

/-- Over a Noetherian coefficient ring `R`, the simply blocked grid homology of a knot grid is a
finitely generated `R`-module; in particular it is finite-dimensional over a field. -/
theorem finite_restrictScalars_simplyBlockedHomology [IsNoetherianRing R] (i : Fin n) :
    Module.Finite R ((ModuleCat.restrictScalars
      (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
        (hG.simplyBlockedHomology R i)) := by
  obtain ⟨s, hs⟩ := (hG.finite_simplyBlockedHomology R i).fg_top
  -- Restriction of scalars keeps the carrier of `G-hat`, so `s` also lists elements of it, and
  -- every `R[V_c | c ≠ i]`-combination of `s` is an `R`-combination.
  let N : ModuleCat R := (ModuleCat.restrictScalars
    (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
      (hG.simplyBlockedHomology R i)
  let t : Finset N := s
  refine ⟨⟨t, eq_top_iff.mpr fun x _ => ?_⟩⟩
  have key : ∀ y ∈ Submodule.span (MvPolynomial {c : Fin n // c ≠ i} R)
      (s : Set (hG.simplyBlockedHomology R i)), (y : N) ∈ Submodule.span R (t : Set N) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul p y _ hy =>
      rw [hG.smul_simplyBlockedHomology R p y, ← ModuleCat.restrictScalars.smul_def']
      exact Submodule.smul_mem _ _ hy
  exact key x (hs ▸ Submodule.mem_top)

end IsKnot

end GridDiagram

end TauCeti
