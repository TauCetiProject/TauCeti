/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SimplyBlocked.Basic
import TauCeti.KnotTheory.Grid.Homology.ExactSequence

/-!
# Specializing semilinear grid chain maps

A column map `π` carrying the blocked source column `j` to the blocked target column `i`
induces a map on surviving coefficient variables. Specializing a semilinear unblocked map
along this coefficient map preserves its chain equation. The short exact specialization
sequences transfer its cycle-surjectivity and boundary-reflection properties as well.

The matrix specialization and exact-sequence proof are factored from the south-west
stabilization comparison in `Stabilization/SimplyBlocked/Basic.lean`.

## Main results

* `TauCeti.simplyBlockedMapAlong_specialization`: the specialized map descends the original map.
* `TauCeti.simplyBlockedMapAlong_differential`: the chain equation descends as well.
* `TauCeti.exists_sub_simplyBlockedMapAlong_mem_range` and
  `TauCeti.mem_range_of_simplyBlockedMapAlong_mem_range`: specialization preserves the
  elementwise criteria for a quasi-isomorphism.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
-/

public section

open MvPolynomial

namespace TauCeti

variable {n m : ℕ} (R : Type*)

section Semiring

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
  have h : ((killCompl (R := R) (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
      Subtype.val_injective).comp ((rename π).comp (rename Subtype.val))).comp
        (killCompl (f := (Subtype.val : {c : Fin m // c ≠ j} → Fin m))
          Subtype.val_injective) =
      (killCompl (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
        Subtype.val_injective).comp (rename π) := by
    ext c
    by_cases hc : c = j
    · subst c
      simp [hπ]
    · have hX : X c = rename Subtype.val
          (X (R := R) (⟨c, hc⟩ : {c : Fin m // c ≠ j})) := by simp
      simp only [AlgHom.comp_apply]
      rw [hX, killCompl_rename_app]
  exact DFunLike.congr_fun h p

variable (f : GridChainMinus R m →ₛₗ[(rename (R := R) π).toRingHom] GridChainMinus R n)

/-- Specialize the matrix coefficients of a semilinear unblocked grid map. -/
noncomputable def simplyBlockedMapAlong :
    GridChainHat R m j →ₛₗ[simplyBlockedRingHomAlong R π i j] GridChainHat R n i :=
  (Finsupp.linearCombination _ fun x : GridState m =>
    simplyBlockedSpecialization R i (f (Finsupp.single x 1))).comp
      (Finsupp.mapRange.linearMap (simplyBlockedRingHomAlong R π i j).toSemilinearMap)

/-- The specialized map on a single coefficient. -/
theorem simplyBlockedMapAlong_single (x : GridState m)
    (p : MvPolynomial {c : Fin m // c ≠ j} R) :
    simplyBlockedMapAlong R π i j f (Finsupp.single x p) =
      simplyBlockedRingHomAlong R π i j p •
        simplyBlockedSpecialization R i (f (Finsupp.single x 1)) := by
  simp [simplyBlockedMapAlong]

/-- Matrix evaluation of the specialized map. -/
theorem simplyBlockedMapAlong_apply_apply (c : GridChainHat R m j) (y : GridState n) :
    simplyBlockedMapAlong R π i j f c y = c.sum fun x p =>
      simplyBlockedRingHomAlong R π i j p *
        simplyBlockedRingHom R i (f (Finsupp.single x 1) y) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.zero_apply, Finsupp.sum_zero_index]
  | add c d hc hd =>
    rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.sum_add_index'] <;> simp [add_mul]
  | single x p =>
    rw [simplyBlockedMapAlong_single, Finsupp.smul_apply, smul_eq_mul,
      simplyBlockedSpecialization_apply, ← simplyBlockedRingHom_apply,
      Finsupp.sum_single_index (by simp)]

/-- Specialization intertwines the unblocked map with its specialized map. -/
theorem simplyBlockedMapAlong_specialization (hπ : π j = i) (c : GridChainMinus R m) :
    simplyBlockedMapAlong R π i j f (simplyBlockedSpecialization R j c) =
      simplyBlockedSpecialization R i (f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x p =>
    rw [simplyBlockedSpecialization_single, simplyBlockedMapAlong_single,
      ← simplyBlockedRingHom_apply, simplyBlockedRingHomAlong_specialization R π i j hπ,
      ← Finsupp.smul_single_one x p, map_smulₛₗ, map_smulₛₗ]
    rfl

variable (G : GridDiagram n) (G' : GridDiagram m)

/-- A semilinear chain equation descends through specialization. -/
theorem simplyBlockedMapAlong_differential (hπ : π j = i)
    (hf : ∀ c, f (G'.unblockedDifferential R c) = G.unblockedDifferential R (f c))
    (c : GridChainHat R m j) :
    simplyBlockedMapAlong R π i j f (G'.simplyBlockedDifferential R j c) =
      G.simplyBlockedDifferential R i (simplyBlockedMapAlong R π i j f c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R j c
  rw [← GridDiagram.simplyBlockedSpecialization_unblockedDifferential,
    simplyBlockedMapAlong_specialization R π i j f hπ,
    simplyBlockedMapAlong_specialization R π i j f hπ,
    ← GridDiagram.simplyBlockedSpecialization_unblockedDifferential, hf]

end Semiring

section Ring

variable [CommRing R] [CharP R 2] (π : Fin m → Fin n) (i : Fin n) (j : Fin m)
  (f : GridChainMinus R m →ₛₗ[(rename (R := R) π).toRingHom] GridChainMinus R n)
  (G : GridDiagram n) (G' : GridDiagram m) (hπ : π j = i)
  (hf : ∀ c, f (G'.unblockedDifferential R c) = G.unblockedDifferential R (f c))
  (hsur : ∀ c ∈ LinearMap.ker (G.unblockedDifferential R),
    ∃ x ∈ LinearMap.ker (G'.unblockedDifferential R),
      c - f x ∈ LinearMap.range (G.unblockedDifferential R))
  (hinj : ∀ x ∈ LinearMap.ker (G'.unblockedDifferential R),
    f x ∈ LinearMap.range (G.unblockedDifferential R) →
      x ∈ LinearMap.range (G'.unblockedDifferential R))

omit [CharP R 2] in
include hπ in
private theorem map_X_smul (c : GridChainMinus R m) :
    f ((X j : MvPolynomial (Fin m) R) • c) =
      (X i : MvPolynomial (Fin n) R) • f c := by
  rw [map_smulₛₗ]
  simp [hπ]

include hπ hf hsur hinj

/-- The specialization five lemma preserves surjectivity on cycles modulo boundaries. -/
theorem exists_sub_simplyBlockedMapAlong_mem_range {y : GridChainHat R n i}
    (hy : y ∈ LinearMap.ker (G.simplyBlockedDifferential R i)) :
    ∃ x ∈ LinearMap.ker (G'.simplyBlockedDifferential R j),
      y - simplyBlockedMapAlong R π i j f x ∈
        LinearMap.range (G.simplyBlockedDifferential R i) := by
  have hs : ∀ c ∈ (G.unblockedDifferential R).toAddMonoidHom.ker,
      ∃ x ∈ (G'.unblockedDifferential R).toAddMonoidHom.ker,
        c - f.toAddMonoidHom x ∈ (G.unblockedDifferential R).toAddMonoidHom.range := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := hsur c (by simpa using hc)
    refine ⟨x, by simpa using hx, ?_⟩
    change c - f x ∈ (G.unblockedDifferential R).toAddMonoidHom.range
    simpa using hcx
  have hi : ∀ x ∈ (G'.unblockedDifferential R).toAddMonoidHom.ker,
      f.toAddMonoidHom x ∈ (G.unblockedDifferential R).toAddMonoidHom.range →
        x ∈ (G'.unblockedDifferential R).toAddMonoidHom.range := by
    intro x hx hb
    have hb' : f x ∈ LinearMap.range (G.unblockedDifferential R) := by
      change f x ∈ (G.unblockedDifferential R).toAddMonoidHom.range at hb
      simpa using hb
    simpa using hinj x (by simpa using hx) hb'
  simpa using AddMonoidHom.exists_mem_ker_sub_mem_range_of_exact
    (simplyBlockedMapAlong R π i j f).toAddMonoidHom
    (f₁ := f.toAddMonoidHom) (f := f.toAddMonoidHom)
    (G'.isShortExactDifferential_X_smul_simplyBlockedSpecialization R j)
    (G.isShortExactDifferential_X_smul_simplyBlockedSpecialization R i)
    hf (map_X_smul R π i j f hπ)
    (simplyBlockedMapAlong_specialization R π i j f hπ) hs hs hi (by simpa using hy)

/-- The specialization five lemma preserves reflection of boundaries among cycles. -/
theorem mem_range_of_simplyBlockedMapAlong_mem_range {x : GridChainHat R m j}
    (hx : x ∈ LinearMap.ker (G'.simplyBlockedDifferential R j))
    (h : simplyBlockedMapAlong R π i j f x ∈
      LinearMap.range (G.simplyBlockedDifferential R i)) :
    x ∈ LinearMap.range (G'.simplyBlockedDifferential R j) := by
  have hs : ∀ c ∈ (G.unblockedDifferential R).toAddMonoidHom.ker,
      ∃ x ∈ (G'.unblockedDifferential R).toAddMonoidHom.ker,
        c - f.toAddMonoidHom x ∈ (G.unblockedDifferential R).toAddMonoidHom.range := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := hsur c (by simpa using hc)
    refine ⟨x, by simpa using hx, ?_⟩
    change c - f x ∈ (G.unblockedDifferential R).toAddMonoidHom.range
    simpa using hcx
  have hi : ∀ x ∈ (G'.unblockedDifferential R).toAddMonoidHom.ker,
      f.toAddMonoidHom x ∈ (G.unblockedDifferential R).toAddMonoidHom.range →
        x ∈ (G'.unblockedDifferential R).toAddMonoidHom.range := by
    intro x hx hb
    have hb' : f x ∈ LinearMap.range (G.unblockedDifferential R) := by
      change f x ∈ (G.unblockedDifferential R).toAddMonoidHom.range at hb
      simpa using hb
    simpa using hinj x (by simpa using hx) hb'
  simpa using AddMonoidHom.mem_range_of_map_mem_range_of_exact
    (simplyBlockedMapAlong R π i j f).toAddMonoidHom
    (f₁ := f.toAddMonoidHom) (f := f.toAddMonoidHom)
    (G'.isShortExactDifferential_X_smul_simplyBlockedSpecialization R j)
    (G.isShortExactDifferential_X_smul_simplyBlockedSpecialization R i)
    hf hf (map_X_smul R π i j f hπ)
    (simplyBlockedMapAlong_specialization R π i j f hπ) hs hi hi
    (by simpa using hx) (by simpa using h)

end Ring

end TauCeti
