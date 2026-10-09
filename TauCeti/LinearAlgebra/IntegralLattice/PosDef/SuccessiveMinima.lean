/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Localization.Module
import Mathlib.Order.Minimal

/-!
# Successive minima of integral lattices

The successive minima are squared norms, rather than lengths. With indices starting at zero,
`L.successiveMinimum i` is the least natural bound containing `i + 1` linearly independent
lattice vectors. Indices lie in `Fin (Module.finrank ℤ L)`, so there are no successive minima
in rank zero. Linear independence is over `ℤ`, equivalently over `ℚ` after embedding in the
ambient rational space.

The construction is defined for every integral lattice. For positive semidefinite lattices each
successive minimum is represented by a nonzero vector, the first is the ordinary minimum,
and an independent family attains all values simultaneously. The sequence is nondecreasing.
For positive definite lattices the values are positive. The characterization by independent bounded
vectors is intended for estimates and reduction theory;
it does not assert that those vectors form an integral basis. A vector independent of `i` vectors
whose norms are bounded by the first `i` successive minima has norm at least the next one; this is
the lattice-theoretic input to Minkowski's second theorem.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Chapter VIII.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2.
-/

public section

namespace TauCeti.IntegralLattice

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {W : Type v} [AddCommGroup W] [Module ℚ W]

/-- The `(i + 1)`-st successive minimum, measured as an integral squared norm. It is the least
natural bound containing `i + 1` independent lattice vectors. -/
noncomputable def successiveMinimum (L : IntegralLattice V)
    (i : Fin (Module.finrank ℤ L)) : ℕ :=
  sInf {c : ℕ | ∃ x : Fin (i.val + 1) → L,
    LinearIndependent ℤ x ∧ ∀ j, L.integralNorm (x j) ≤ c}

/-- The defining infimum of the successive minimum. -/
theorem successiveMinimum_def (L : IntegralLattice V) (i : Fin (Module.finrank ℤ L)) :
    L.successiveMinimum i = sInf {c : ℕ | ∃ x : Fin (i.val + 1) → L,
      LinearIndependent ℤ x ∧ ∀ j, L.integralNorm (x j) ≤ c} := (rfl)

variable {L : IntegralLattice V}

/-- Each successive minimum contains the required number of independent bounded vectors. -/
theorem exists_linearIndependent_integralNorm_le_successiveMinimum
    (L : IntegralLattice V) (i : Fin (Module.finrank ℤ L)) :
    ∃ x : Fin (i.val + 1) → L,
      LinearIndependent ℤ x ∧ ∀ j, L.integralNorm (x j) ≤ L.successiveMinimum i := by
  rw [successiveMinimum_def]
  refine Nat.sInf_mem (s := {c : ℕ | ∃ x : Fin (i.val + 1) → L,
    LinearIndependent ℤ x ∧ ∀ j, L.integralNorm (x j) ≤ c}) ?_
  obtain ⟨x, hx⟩ := exists_linearIndependent_of_le_finrank (R := ℤ) (M := L)
    (Nat.succ_le_of_lt i.isLt)
  refine ⟨∑ j, (L.integralNorm (x j)).toNat, x, hx, fun j ↦ ?_⟩
  exact (Int.self_le_toNat _).trans (Int.ofNat_le.mpr
    (Finset.single_le_sum (f := fun j ↦ (L.integralNorm (x j)).toNat)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)))

/-- A successive minimum is at most any bound containing enough independent vectors. -/
theorem successiveMinimum_le_of_linearIndependent (L : IntegralLattice V)
    (i : Fin (Module.finrank ℤ L)) {c : ℕ} {x : Fin (i.val + 1) → L}
    (hx : LinearIndependent ℤ x) (hc : ∀ j, L.integralNorm (x j) ≤ c) :
    L.successiveMinimum i ≤ c := by
  rw [successiveMinimum_def]
  exact Nat.sInf_le ⟨x, hx, hc⟩

/-- A natural bound reaches the successive minimum exactly when it contains enough independent
lattice vectors. -/
theorem successiveMinimum_le_iff (L : IntegralLattice V)
    (i : Fin (Module.finrank ℤ L)) (c : ℕ) :
    L.successiveMinimum i ≤ c ↔ ∃ x : Fin (i.val + 1) → L,
      LinearIndependent ℤ x ∧ ∀ j, L.integralNorm (x j) ≤ c := by
  constructor
  · intro hc
    obtain ⟨x, hx, hbound⟩ := L.exists_linearIndependent_integralNorm_le_successiveMinimum i
    exact ⟨x, hx, fun j ↦ (hbound j).trans (Int.ofNat_le.mpr hc)⟩
  · rintro ⟨x, hx, hc⟩
    exact L.successiveMinimum_le_of_linearIndependent i hx hc

/-- Successive minima form a nondecreasing sequence. -/
theorem monotone_successiveMinimum (L : IntegralLattice V) : Monotone L.successiveMinimum := by
  intro i j hij
  obtain ⟨x, hx, hbound⟩ := L.exists_linearIndependent_integralNorm_le_successiveMinimum j
  let f : Fin (i.val + 1) → Fin (j.val + 1) := Fin.castLE (Nat.add_le_add_right hij 1)
  exact L.successiveMinimum_le_of_linearIndependent i
    (hx.comp f (Fin.castLE_injective _)) (fun k ↦ hbound (f k))

/-- The first successive minimum of a positive semidefinite lattice is its ordinary minimum. -/
@[simp]
theorem IsPosSemidef.successiveMinimum_zero (hL : L.IsPosSemidef)
    (h : 0 < Module.finrank ℤ L) : L.successiveMinimum ⟨0, h⟩ = L.minimum := by
  have : Nontrivial L := Module.nontrivial_of_finrank_pos h
  apply Nat.le_antisymm
  · obtain ⟨x, hx, hnorm⟩ := hL.exists_ne_zero_integralNorm_eq_minimum
    apply L.successiveMinimum_le_of_linearIndependent (x := fun _ ↦ x)
    · have hx' : LinearIndependent ℤ (fun _ : Fin 1 ↦ x) :=
        linearIndependent_unique_iff.mpr hx
      exact hx'
    · intro j
      exact hnorm.le
  · obtain ⟨x, hx, hnorm⟩ := L.exists_linearIndependent_integralNorm_le_successiveMinimum ⟨0, h⟩
    have hle := (hL.minimum_le_integralNorm (hx.ne_zero 0)).trans (hnorm 0)
    exact_mod_cast hle

/-- At the next successive minimum there is a bounded vector outside the rational span of any
family of fewer vectors. -/
theorem exists_integralNorm_le_successiveMinimum_not_mem_span (L : IntegralLattice V)
    (i : Fin (Module.finrank ℤ L)) (x : Fin i.val → L) :
    ∃ y : L, L.integralNorm y ≤ L.successiveMinimum i ∧
      (y : V) ∉ Submodule.span ℚ (Set.range (fun j ↦ (x j : V))) := by
  let : FiniteDimensional ℚ V := L.finiteDimensional
  obtain ⟨y, hy, hbound⟩ := L.exists_linearIndependent_integralNorm_le_successiveMinimum i
  have hyq : LinearIndependent ℚ (fun j ↦ (y j : V)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (hy.map' L.carrier.subtype (Submodule.ker_subtype _))
  by_contra! h
  let S := Submodule.span ℚ (Set.range (fun j ↦ (x j : V)))
  have hmem (j) : (y j : V) ∈ S := h (y j) (hbound j)
  have hli : LinearIndependent ℚ (fun j ↦ (⟨(y j : V), hmem j⟩ : S)) :=
    hyq.of_comp S.subtype
  have hlo := hli.fintype_card_le_finrank
  have hhi : Module.finrank ℚ S ≤ i.val := by
    simpa only [S, Set.finrank, Fintype.card_fin] using
      finrank_range_le_card (R := ℚ) (fun j ↦ (x j : V))
  simp only [Fintype.card_fin] at hlo
  omega

/-- In a positive semidefinite lattice, let `x₀, …, x_{i-1}` be lattice vectors of norms at most
the corresponding successive minima. Every vector `z` for which `x₀, …, x_{i-1}, z` are linearly
independent has norm at least the next successive minimum `λᵢ`. For a family attaining the
successive minima, this bounds below every vector outside the span of its first `i` members. -/
theorem IsPosSemidef.successiveMinimum_le_integralNorm_of_linearIndependent (hL : L.IsPosSemidef)
    (i : Fin (Module.finrank ℤ L)) {x : Fin i.val → L}
    (hx : ∀ j, L.integralNorm (x j) ≤ L.successiveMinimum (Fin.castLE i.isLt.le j)) {z : L}
    (hz : LinearIndependent ℤ (Fin.snoc x z : Fin (i.val + 1) → L)) :
    (L.successiveMinimum i : ℤ) ≤ L.integralNorm z := by
  classical
  by_contra! hlt
  -- The least index `m ≤ i` whose successive minimum exceeds the norm of `z`.
  have hex : ∃ m, ∃ hm : m ≤ i.val, L.integralNorm z <
      L.successiveMinimum ⟨m, hm.trans_lt i.isLt⟩ := ⟨i.val, le_rfl, hlt⟩
  set m := Nat.find hex
  obtain ⟨hmi, hm⟩ : ∃ hm : m ≤ i.val, L.integralNorm z <
      L.successiveMinimum ⟨m, hm.trans_lt i.isLt⟩ := Nat.find_spec hex
  have hbelow (j : Fin m) : L.integralNorm (x (Fin.castLE hmi j)) ≤ L.integralNorm z := by
    have h := Nat.find_min hex j.isLt
    push Not at h
    exact (hx _).trans (h (j.isLt.le.trans hmi))
  -- The vectors `x₀, …, x_{m-1}, z` are independent and of norm at most `B(z, z)`.
  let f : Fin (m + 1) → Fin (i.val + 1) :=
    Fin.snoc (fun j : Fin m ↦ (Fin.castLE hmi j).castSucc) (Fin.last i.val)
  have hf : Function.Injective f := by
    intro a b hab
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp_all [f, Fin.ext_iff] <;> omega
  have hcomp : (Fin.snoc x z : Fin (i.val + 1) → L) ∘ f =
      Fin.snoc (fun j : Fin m ↦ x (Fin.castLE hmi j)) z := by
    ext j
    induction j using Fin.lastCases <;>
      simp only [Function.comp_apply, f, Fin.snoc_castSucc, Fin.snoc_last]
  have hle := L.successiveMinimum_le_of_linearIndependent ⟨m, hmi.trans_lt i.isLt⟩
    (c := (L.integralNorm z).toNat) (hcomp ▸ hz.comp f hf) fun j ↦ by
      induction j using Fin.lastCases with
      | last => simp
      | cast j => simpa using (hbelow j).trans (Int.self_le_toNat _)
  have := Int.toNat_of_nonneg (hL.integralNorm_nonneg z)
  omega

/-- A positive semidefinite lattice admits independent vectors attaining all successive minima
simultaneously. These vectors are not asserted to be an integral basis. -/
theorem IsPosSemidef.exists_linearIndependent_integralNorm_eq_successiveMinimum
    (hL : L.IsPosSemidef) :
    ∃ x : Fin (Module.finrank ℤ L) → L,
      LinearIndependent ℤ x ∧ ∀ i, L.integralNorm (x i) = L.successiveMinimum i := by
  -- Greedily take a least-norm vector outside the rational span. The extra invariant says
  -- that every selected vector has norm at most every vector outside the current span.
  have haux (m : ℕ) (hm : m ≤ Module.finrank ℤ L) :
      ∃ x : Fin m → L, LinearIndependent ℤ x ∧
        (∀ j, L.integralNorm (x j) = L.successiveMinimum ⟨j.val, j.isLt.trans_le hm⟩) ∧
        (∀ y : L, (y : V) ∉ Submodule.span ℚ (Set.range (fun j ↦ (x j : V))) →
          ∀ j, L.integralNorm (x j) ≤ L.integralNorm y) := by
    induction m with
    | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, by simp, by simp⟩
    | succ m ih =>
      have hm' : m < Module.finrank ℤ L := by omega
      obtain ⟨x, hx, hnorm, hmin⟩ := ih (by omega)
      let S := Submodule.span ℚ (Set.range (fun j ↦ (x j : V)))
      obtain ⟨y, -, hy⟩ := L.exists_integralNorm_le_successiveMinimum_not_mem_span ⟨m, hm'⟩ x
      obtain ⟨w, hwmin⟩ := exists_minimalFor_of_wellFoundedLT
        (fun y : L ↦ (y : V) ∉ S) (fun y ↦ (L.integralNorm y).toNat) ⟨y, hy⟩
      have hw := hwmin.1
      have hleast (y : L) (hy : (y : V) ∉ S) : L.integralNorm w ≤ L.integralNorm y := by
        have hle := hwmin.le hy
        have hwcast := Int.toNat_of_nonneg (hL.integralNorm_nonneg w)
        have hycast := Int.toNat_of_nonneg (hL.integralNorm_nonneg y)
        exact hwcast ▸ hycast ▸ Int.ofNat_le.mpr hle
      have hcw : L.integralNorm w = ((L.integralNorm w).toNat : ℤ) :=
        (Int.toNat_of_nonneg (hL.integralNorm_nonneg w)).symm
      have hsnoc : LinearIndependent ℤ (Fin.snoc x w) := by
        have h := (hx.map' L.carrier.subtype
          (Submodule.ker_subtype _)).finSnoc_of_not_mem_span_over hw
        have h' : LinearIndependent ℤ (L.carrier.subtype ∘ Fin.snoc x w) := by
          simpa only [Fin.comp_snoc, Submodule.subtype_apply] using h
        exact h'.of_comp L.carrier.subtype
      have hcw' : L.integralNorm w = L.successiveMinimum ⟨m, hm'⟩ := by
        obtain ⟨y, hybound, hy⟩ :=
          L.exists_integralNorm_le_successiveMinimum_not_mem_span ⟨m, hm'⟩ x
        apply le_antisymm ((hleast y hy).trans hybound)
        have hle := L.successiveMinimum_le_of_linearIndependent ⟨m, hm'⟩ hsnoc
          (c := (L.integralNorm w).toNat) (fun j ↦ Fin.lastCases (by simp)
            (fun k ↦ by simpa using (hmin w hw k).trans hcw.le) j)
        rw [hcw]
        exact_mod_cast hle
      refine ⟨Fin.snoc x w, hsnoc, ?_, ?_⟩
      · intro j
        induction j using Fin.lastCases with
        | last => simpa using hcw'
        | cast k => simpa using hnorm k
      · intro y hy j
        have hsub : S ≤ Submodule.span ℚ
            (Set.range (L.carrier.subtype ∘ (Fin.snoc x w : Fin (m + 1) → L))) := by
          apply Submodule.span_mono
          rintro z ⟨k, rfl⟩
          exact ⟨k.castSucc, by simp⟩
        have hyS : (y : V) ∉ S := fun h ↦ hy (hsub h)
        exact Fin.lastCases (by simpa using hleast y hyS)
          (fun k ↦ by simpa using hmin y hyS k) j
  obtain ⟨x, hx, hnorm, -⟩ := haux (Module.finrank ℤ L) le_rfl
  exact ⟨x, hx, hnorm⟩

/-- Every successive minimum of a positive semidefinite lattice is the norm of a nonzero vector.
This asserts attainment as a squared norm, rather than merely existence of a bounding infimum. -/
theorem IsPosSemidef.exists_ne_zero_integralNorm_eq_successiveMinimum
    (hL : L.IsPosSemidef) (i : Fin (Module.finrank ℤ L)) :
    ∃ x : L, x ≠ 0 ∧ L.integralNorm x = L.successiveMinimum i := by
  obtain ⟨x, hx, hnorm⟩ := hL.exists_linearIndependent_integralNorm_eq_successiveMinimum
  exact ⟨x i, hx.ne_zero i, hnorm i⟩

/-- Successive minima of a positive definite lattice are positive. -/
theorem IsPosDef.successiveMinimum_pos (hL : L.IsPosDef)
    (i : Fin (Module.finrank ℤ L)) : 0 < L.successiveMinimum i := by
  obtain ⟨x, hx, hnorm⟩ := hL.isPosSemidef.exists_ne_zero_integralNorm_eq_successiveMinimum i
  have := hL.posDef_integralNorm x hx
  rw [hnorm] at this
  exact_mod_cast this

/-- The successive minimum is invariant under isometry; indices are transported by equality of
carrier ranks. -/
theorem Isometry.successiveMinimum_eq {M : IntegralLattice W} (e : Isometry L M)
    (i : Fin (Module.finrank ℤ L)) :
    L.successiveMinimum i = M.successiveMinimum (Fin.cast e.carrierEquiv.finrank_eq i) := by
  apply Nat.le_antisymm
  · obtain ⟨x, hx, hbound⟩ := M.exists_linearIndependent_integralNorm_le_successiveMinimum
      (Fin.cast e.carrierEquiv.finrank_eq i)
    apply L.successiveMinimum_le_of_linearIndependent i (x := fun j ↦ e.carrierEquiv.symm (x j))
    · exact hx.map' e.carrierEquiv.symm.toLinearMap e.carrierEquiv.symm.ker
    · intro j
      simpa only [← e.integralNorm_carrierEquiv, e.carrierEquiv.apply_symm_apply] using hbound j
  · obtain ⟨x, hx, hbound⟩ := L.exists_linearIndependent_integralNorm_le_successiveMinimum i
    apply M.successiveMinimum_le_of_linearIndependent _ (x := fun j ↦ e.carrierEquiv (x j))
    · exact hx.map' e.carrierEquiv.toLinearMap e.carrierEquiv.ker
    · intro j
      simpa only [e.integralNorm_carrierEquiv] using hbound j

end TauCeti.IntegralLattice
