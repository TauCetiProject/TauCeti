/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# The center of the symplectic group

Over any commutative ring, a matrix commuting with every symplectic matrix is scalar.
Consequently the center of `Sp₂ₘ` in positive rank consists of scalar matrices whose
scalar squares to one. This description retains the infinitesimal center in characteristic two.

The scalar homomorphism realizes square roots of one as central symplectic matrices,
providing the pointwise description used for the center of the symplectic group scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 21, the classical semisimple groups.

The elementary matrices are those of
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic`.
-/

public section

open Matrix

namespace Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

/-- A matrix commuting with all symplectic matrices is scalar, over any commutative ring. -/
theorem mem_range_scalar_of_commute_symplectic
    (M : Matrix (Fin (m + m)) (Fin (m + m)) R)
    (hM : ∀ g : TauCeti.GLSymplecticFin m R, Commute M (g.val : Matrix _ _ R)) :
    M ∈ Set.range (scalar (Fin (m + m))) := by
  classical
  by_cases hm : m = 0
  · subst m
    exact ⟨0, by ext i; exact Fin.elim0 i⟩
  let z : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  -- Commutation with a long-root transvection isolates one column and compares its
  -- diagonal entry with the entry at the paired coordinate.
  have hlong (a b : Fin (m + m))
      (h : Commute M (transvection a b (1 : R))) : Commute (single a b 1) M := by
    have he := h.eq
    rw [transvection, mul_add, add_mul, mul_one, one_mul] at he
    exact (add_left_cancel he).symm
  have hp (i : Fin m) := hlong _ _ (by
    simpa only [TauCeti.GLSymplecticFin.coe_positiveLongRootTransvectionUnit,
      TauCeti.coe_transvectionUnit] using
      hM (TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit i 1))
  have hn (i : Fin m) := hlong _ _ (by
    simpa only [TauCeti.GLSymplecticFin.coe_negativeLongRootTransvectionUnit,
      TauCeti.coe_transvectionUnit] using
      hM (TauCeti.GLSymplecticFin.negativeLongRootTransvectionUnit i 1))
  have hoff (a b : Fin (m + m)) (hab : a ≠ b) : M a b = 0 := by
    induction b using Fin.addCases with
    | left i =>
      exact col_eq_zero_of_commute_single (hp i) hab
    | right i => exact col_eq_zero_of_commute_single (hn i) hab
  have hd (i : Fin m) : M (Fin.castAdd m i) (Fin.castAdd m i) =
      M (Fin.castAdd m z) (Fin.castAdd m z) := by
    by_cases hiz : i = z
    · simp [hiz]
    have he := congrArg
      (fun N : Matrix (Fin (m + m)) (Fin (m + m)) R ↦
        N (Fin.castAdd m i) (Fin.castAdd m z))
      (hM (TauCeti.GLSymplecticFin.differenceShortRootUnit hiz (1 : R))).eq
    rw [TauCeti.GLSymplecticFin.coe_differenceShortRootUnit_eq_one_add_single_sub_single] at he
    have hcross (a b : Fin m) : Fin.castAdd m a ≠ b.addNat m := by
      simpa using TauCeti.GLSymplecticFin.finSumFinEquiv_inl_ne_inr a b
    simpa [mul_sub, sub_mul, mul_add, add_mul, hoff, hiz,
      mul_single_apply_of_ne _ _ _ _ _ (hcross z i),
      single_mul_apply_of_ne _ _ _ _ _ (hcross i z)] using he
  refine ⟨M (Fin.castAdd m z) (Fin.castAdd m z), ?_⟩
  ext a b
  by_cases hab : a = b
  · subst b
    rw [scalar_apply, diagonal_apply_eq]
    symm
    refine Fin.addCases (fun i ↦ hd i) (fun i ↦ ?_) a
    exact (diag_eq_of_commute_single (hn i)).trans (hd i)
  · simp [scalar_apply, diagonal_apply_ne _ hab, hoff a b hab]

end Matrix

namespace TauCeti.GLSymplecticFin

variable {R : Type*} [CommRing R] {m : ℕ}

/-- In positive rank the center of the symplectic group consists exactly of scalar matrices
whose scalar squares to one. No reducedness or characteristic assumption is needed. -/
theorem mem_center_iff (hm : m ≠ 0) (g : GLSymplecticFin m R) :
    g ∈ Subgroup.center (GLSymplecticFin m R) ↔
      ∃ c : R, (g.val : Matrix _ _ R) = Matrix.scalar (Fin (m + m)) c ∧ c ^ 2 = 1 := by
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_symplectic
      (g.val : Matrix _ _ R) (fun h ↦ by
        have he := Subgroup.mem_center_iff.mp hg h
        exact congrArg (fun x : GLSymplecticFin m R ↦
          (x.val : Matrix (Fin (m + m)) (Fin (m + m)) R)) he.symm)
    refine ⟨c, hc.symm, ?_⟩
    apply sq_eq_one_of_smul_one_mul_JFin_mul_transpose_eq hm
    simpa only [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using
      GLSymplecticFin.mem_iff.mp g.property
  · rintro ⟨c, hc, -⟩
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_mul, Units.val_mul, hc] using
      (Matrix.scalar_commute c (fun r ↦ Commute.all c r)
        (h.val : Matrix (Fin (m + m)) (Fin (m + m)) R)).eq.symm

variable (m)

/-- A square root of one acts by a scalar symplectic matrix. -/
noncomputable def rootsOfUnityScalar {A : Type*} [CommRing A] :
    rootsOfUnity 2 A →* GLSymplecticFin m A :=
  (Matrix.GeneralLinearGroup.scalar (Fin (m + m))).comp
      (rootsOfUnity 2 A).subtype |>.codRestrict (GLSymplecticFin m A) fun ζ ↦ by
    rw [GLSymplecticFin.mem_iff, MonoidHom.comp_apply,
      Subgroup.subtype_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    have hζ := (mem_rootsOfUnity' 2 (ζ : Aˣ)).mp ζ.property
    simp [smul_smul, ← sq, hζ]

/-- The underlying matrix of a scalar symplectic point is its scalar matrix. -/
@[simp]
theorem coe_rootsOfUnityScalar {A : Type*} [CommRing A] (ζ : rootsOfUnity 2 A) :
    ((rootsOfUnityScalar m ζ).val : Matrix (Fin (m + m)) (Fin (m + m)) A) =
      Matrix.scalar (Fin (m + m)) ((ζ : Aˣ) : A) := (rfl)

end TauCeti.GLSymplecticFin
