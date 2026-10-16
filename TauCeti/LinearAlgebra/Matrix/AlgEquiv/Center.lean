/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut
public import Mathlib.LinearAlgebra.Matrix.DualNumber
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Detecting trivial matrix-algebra automorphisms

An automorphism of a matrix algebra which commutes with every inner derivation is the
identity. This detects universally central automorphisms: commuting with conjugation by
`1 + εX` over dual numbers implies commuting with the derivation `Y ↦ XY - YX`.
The argument works over arbitrary commutative rings, including rings with nilpotents.
-/

public section

open Matrix

namespace AlgHom

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- An algebra endomorphism of a matrix algebra that changes each matrix by a scalar is
the identity. No restriction on the rank or characteristic is needed. -/
theorem eq_id_of_sub_mem_range_scalar (f : Matrix ι ι R →ₐ[R] Matrix ι ι R)
    (hf : ∀ X, f X - X ∈ Set.range (Matrix.scalar ι)) : f = AlgHom.id R _ := by
  cases subsingleton_or_nontrivial ι with
  | inl h =>
    apply AlgHom.toLinearMap_injective
    apply (stdBasis R ι ι).ext
    intro ij
    obtain ⟨i, j⟩ := ij
    have hij : i = j := Subsingleton.elim _ _
    subst j
    have hsingle : Matrix.single i i (1 : R) = 1 := by
      ext a b
      simp [Matrix.one_apply, Subsingleton.elim a i, Subsingleton.elim b i]
    simp [stdBasis_eq_single, hsingle]
  | inr h =>
    have hdiag (i : ι) : f (Matrix.single i i 1) = Matrix.single i i 1 := by
      obtain ⟨j, hij⟩ := exists_ne i
      obtain ⟨c, hc⟩ := hf (Matrix.single i i 1)
      obtain ⟨d, hd⟩ := hf (Matrix.single i j 1)
      have hc' : f (Matrix.single i i 1) = Matrix.single i i 1 + Matrix.scalar ι c :=
        sub_eq_iff_eq_add'.mp hc.symm
      have hd' : f (Matrix.single i j 1) = Matrix.single i j 1 + Matrix.scalar ι d :=
        sub_eq_iff_eq_add'.mp hd.symm
      have hm := congrArg (fun X : Matrix ι ι R ↦ X i j)
        (f.map_mul (Matrix.single i i 1) (Matrix.single i j 1))
      have hc0 : c = 0 := by
        simpa [hc', hd', Matrix.mul_add, Matrix.add_mul, Matrix.scalar, hij.symm] using hm
      simpa [hc0] using hc'
    apply AlgHom.toLinearMap_injective
    apply (stdBasis R ι ι).ext
    rintro ⟨i, j⟩
    simp only [stdBasis_eq_single, AlgHom.toLinearMap_apply, AlgHom.id_apply]
    by_cases hij : i = j
    · subst j
      exact hdiag i
    obtain ⟨c, hc⟩ := hf (Matrix.single i j 1)
    have hc' : f (Matrix.single i j 1) = Matrix.single i j 1 + Matrix.scalar ι c :=
      sub_eq_iff_eq_add'.mp hc.symm
    have hm := congrArg (fun X : Matrix ι ι R ↦ X j j)
      (f.map_mul (Matrix.single i i 1) (Matrix.single i j 1))
    have hc0 : c = 0 := by
      simpa [hdiag, hc', Matrix.scalar, hij, Ne.symm hij] using hm
    simpa [hc0] using hc'

end AlgHom

namespace AlgEquiv

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- An automorphism of a matrix algebra commuting with every inner derivation is the identity.
This criterion uses associative commutators and holds in every characteristic. -/
theorem eq_one_of_map_commutator (f : Matrix ι ι R ≃ₐ[R] Matrix ι ι R)
    (hf : ∀ X Y, f (X * Y - Y * X) = X * f Y - f Y * X) : f = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply f.toAlgHom.eq_id_of_sub_mem_range_scalar
  intro X
  apply Matrix.mem_range_scalar_iff_commute_single'.mpr
  intro i j
  have h := hf X (f.symm (Matrix.single i j 1))
  simp only [map_sub, map_mul, f.apply_symm_apply] at h
  dsimp only [Commute, SemiconjBy]
  rw [mul_sub, sub_mul]
  exact (sub_eq_sub_iff_sub_eq_sub.mp h).symm

/-- An automorphism of a matrix algebra is trivial if its extension to dual numbers
commutes with all inner automorphisms. Compatibility is needed only on constant matrices. -/
theorem eq_one_of_commute_innerAut_dualNumber
    (f : Matrix ι ι R ≃ₐ[R] Matrix ι ι R)
    (f' : Matrix ι ι (DualNumber R) ≃ₐ[DualNumber R] Matrix ι ι (DualNumber R))
    (hbase : ∀ Y, f' (Y.map (TrivSqZeroExt.inlHom R R)) =
      (f Y).map (TrivSqZeroExt.inlHom R R))
    (hc : ∀ g : GL ι (DualNumber R), Commute f' (Matrix.GeneralLinearGroup.innerAut g)) :
    f = 1 := by
  let e := Matrix.dualNumberEquiv (R := R) (n := ι)
  let L (Y : Matrix ι ι R) : Matrix ι ι (DualNumber R) :=
    Y.map (TrivSqZeroExt.inlHom R R)
  have heL (Y : Matrix ι ι R) : e (L Y) = TrivSqZeroExt.inl Y := by
    ext <;> simp [e, L, Matrix.dualNumberEquiv_apply]
  have heps (Y : Matrix ι ι R) :
      e ((DualNumber.eps : DualNumber R) • L Y) = TrivSqZeroExt.inr Y := by
    ext <;> simp [e, L, Matrix.dualNumberEquiv_apply, smul_eq_mul]
  have hbase' (Y : Matrix ι ι R) : f' (L Y) = L (f Y) := hbase Y
  have hε (Y : Matrix ι ι R) : f' ((DualNumber.eps : DualNumber R) • L Y) =
      (DualNumber.eps : DualNumber R) • L (f Y) := by rw [map_smul, hbase']
  apply f.eq_one_of_map_commutator
  intro X Y
  let u : (DualNumber (Matrix ι ι R))ˣ :=
    ⟨TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr X,
      TrivSqZeroExt.inl 1 - TrivSqZeroExt.inr X, by
        ext <;> simp [TrivSqZeroExt.snd_mul, smul_eq_mul], by
        ext <;> simp [TrivSqZeroExt.snd_mul, smul_eq_mul]⟩
  let g : GL ι (DualNumber R) := Units.map e.symm.toMonoidHom u
  have hconj (Z : Matrix ι ι R) : Matrix.GeneralLinearGroup.innerAut g (L Z) =
      L Z + (DualNumber.eps : DualNumber R) • L (X * Z - Z * X) := by
    apply e.injective
    rw [Matrix.GeneralLinearGroup.innerAut_apply, map_mul, map_mul, heL, map_add, heL, heps]
    simp only [g, Units.coe_map]
    ext <;> simp [u, TrivSqZeroExt.snd_mul, smul_eq_mul, sub_eq_add_neg, add_comm]
  have h := congrArg (fun a : Matrix ι ι (DualNumber R) ≃ₐ[DualNumber R]
      Matrix ι ι (DualNumber R) ↦ a (L Y)) (hc g).eq
  simp only [AlgEquiv.mul_apply, hconj, map_add, hbase', hε] at h
  have he := congrArg e h
  rw [map_add, heL, heps, map_add, heL, heps] at he
  simpa using congrArg TrivSqZeroExt.snd he

end AlgEquiv
