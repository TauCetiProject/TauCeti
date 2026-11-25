/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.Charpoly.Quotient
public import TauCeti.RingTheory.CompositionSeries.Semisimplification

/-!
# Characteristic polynomials on the semisimplification

Let `A` be an algebra over a field `k` and `M` an `A`-module that is finite-dimensional over `k`.
The semisimplification `M^ss` is again a finite-dimensional `k`-vector space
(`TauCeti.semisimplification.instModule`), and every `a : A` has the same characteristic polynomial
on `M^ss` as on `M` (`TauCeti.charpoly_lsmul_semisimplification`). Applied to `A = k[Γ]`, a
finite-dimensional representation and its semisimplification have the same characteristic
polynomial, hence the same trace and determinant, at every element of `Γ`.

The proof is by induction on the dimension: a nonzero proper submodule `N` gives
`M^ss ≅ N^ss × (M/N)^ss`, and the characteristic polynomial is multiplicative on `N` and `M/N`
(`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`); a module with no such submodule is
zero or simple, hence semisimple and isomorphic to `M^ss`.

## Main results

* `TauCeti.charpoly_lsmul_semisimplification`: `charpoly (a | M^ss) = charpoly (a | M)`.
-/

public section

namespace TauCeti

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

section Instances

variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- A submodule of a finite-dimensional module over a `k`-algebra is finite-dimensional. -/
theorem finiteDimensional_submodule [FiniteDimensional k M] (N : Submodule A M) :
    FiniteDimensional k N :=
  .of_injective (N.subtype.restrictScalars k) Subtype.val_injective

variable [IsNoetherian A M] [IsArtinian A M]

/-- The `k`-vector space structure of the semisimplification of an `A`-module, for a
`k`-algebra `A`. -/
noncomputable instance semisimplification.instModule : Module k (semisimplification A M) :=
  inferInstanceAs (Module k (seriesSemisimplification _))

/-- The `k`- and `A`-actions on the semisimplification are compatible. -/
instance semisimplification.instIsScalarTower : IsScalarTower k A (semisimplification A M) :=
  inferInstanceAs (IsScalarTower k A (seriesSemisimplification _))

/-- The semisimplification of a finite-dimensional module is finite-dimensional. -/
instance semisimplification.instFiniteDimensional [FiniteDimensional k M] :
    FiniteDimensional k (semisimplification A M) :=
  let s := (exists_compositionSeries_of_isNoetherian_isArtinian A M).choose
  have (i : Fin s.length) :
      FiniteDimensional k (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) :=
    have := finiteDimensional_submodule (k := k) (s i.succ)
    inferInstance
  inferInstanceAs (FiniteDimensional k (seriesSemisimplification _))

end Instances

section Charpoly

variable {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [FiniteDimensional k M] [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [FiniteDimensional k N]

/-- `A`-linearly equivalent modules have the same characteristic polynomials over `k`. -/
theorem charpoly_lsmul_eq_of_linearEquiv (e : M ≃ₗ[A] N) (a : A) :
    (Algebra.lsmul k k M a).charpoly = (Algebra.lsmul k k N a).charpoly := by
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k)]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply]

/-- The characteristic polynomial of `a` on a product is the product of the characteristic
polynomials. -/
theorem charpoly_lsmul_prod (a : A) :
    (Algebra.lsmul k k (M × N) a).charpoly =
      (Algebra.lsmul k k M a).charpoly * (Algebra.lsmul k k N a).charpoly := by
  rw [← LinearMap.charpoly_prodMap]
  congr 1

/-- The characteristic polynomial of `a` on `M` is the product of those on a submodule `N` and on
`M ⧸ N`. -/
theorem charpoly_lsmul_eq_mul_quotient (P : Submodule A M) (a : A) :
    haveI := finiteDimensional_submodule (k := k) P
    (Algebra.lsmul k k M a).charpoly =
      (Algebra.lsmul k k P a).charpoly * (Algebra.lsmul k k (M ⧸ P) a).charpoly := by
  have := finiteDimensional_submodule (k := k) P
  let W := P.restrictScalars k
  have hW : W ≤ W.comap (Algebra.lsmul k k M a) := fun x hx ↦ P.smul_mem a hx
  let eW : W ≃ₗ[k] P := { AddEquiv.refl _ with map_smul' := fun _ _ ↦ rfl }
  let eQ := Submodule.Quotient.restrictScalarsEquiv k P
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ W _ hW,
    ← LinearEquiv.charpoly_conj eW, ← LinearEquiv.charpoly_conj eQ]
  congr 2
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := P.mkQ_surjective x
  rfl

variable [IsNoetherian A M] [IsArtinian A M]

/-- **The semisimplification has the characteristic polynomials of the module.** For an
`A`-module `M` that is finite-dimensional over a field `k` (with `A` a `k`-algebra), every
`a : A` has the same characteristic polynomial on `M^ss` as on `M`. -/
theorem charpoly_lsmul_semisimplification (a : A) :
    (Algebra.lsmul k k (semisimplification A M) a).charpoly =
      (Algebra.lsmul k k M a).charpoly := by
  induction hn : Module.finrank k M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  by_cases hP : ∃ P : Submodule A M, P ≠ ⊥ ∧ P ≠ ⊤
  · obtain ⟨P, hbot, htop⟩ := hP
    have := finiteDimensional_submodule (k := k) P
    obtain ⟨e⟩ := nonempty_linearEquiv_semisimplification_prod_quotient P
    have hW : Module.finrank k P = Module.finrank k (P.restrictScalars k) := rfl
    have hsum : Module.finrank k (M ⧸ P) = n - Module.finrank k P :=
      hn ▸ Submodule.finrank_quotient (R := k) P
    have hP : Module.finrank k P < n := by
      rw [← hn, hW]
      exact Submodule.finrank_lt (by rwa [Ne, Submodule.restrictScalars_eq_top_iff])
    have hQ : Module.finrank k (M ⧸ P) < n := by
      have : Module.finrank k P ≠ 0 := by
        rwa [hW, Ne, Submodule.finrank_eq_zero, Submodule.restrictScalars_eq_bot_iff]
      omega
    rw [charpoly_lsmul_eq_of_linearEquiv e, charpoly_lsmul_prod, ih _ hP rfl, ih _ hQ rfl,
      charpoly_lsmul_eq_mul_quotient P]
  · have : IsSemisimpleModule A M :=
      { exists_isCompl P := by
          rcases eq_or_ne P ⊥ with rfl | hbot
          · exact ⟨⊤, isCompl_bot_top⟩
          · obtain rfl : P = ⊤ := by_contra fun htop ↦ hP ⟨P, hbot, htop⟩
            exact ⟨⊥, isCompl_top_bot⟩ }
    obtain ⟨e⟩ := nonempty_linearEquiv_semisimplification_of_isSemisimpleModule (R := A) (M := M)
    exact charpoly_lsmul_eq_of_linearEquiv e a

end Charpoly

end TauCeti
