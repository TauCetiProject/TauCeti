/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Plucker
public import TauCeti.LinearAlgebra.Matrix.Compound
public import TauCeti.NumberTheory.Height.Adelic.Basic
public import TauCeti.NumberTheory.Height.Arakelov.Subspace.Basic
import TauCeti.LinearAlgebra.Projectivization.Plucker

/-!
# Adelic subspace heights over number fields

For a linear subspace `U ≤ (ι → L)` of dimension `k` over a finite extension `L / K` and an
invertible adelic matrix `A : GL ι (AdeleRing (𝓞 K) K)`, `TauCeti.adelicSubspaceHeight A U` is
the adelic height of the Plücker coordinates of a basis of `U`, twisted by the `k`-th compound
matrix `A.compound k` (`⋀^k A`).

## Main definitions

* `TauCeti.adelicSubspaceHeight`: the twisted adelic height of a linear subspace `U ≤ (ι → L)`.

## Main results

* `TauCeti.adelicSubspaceHeight_nonneg`, `TauCeti.adelicSubspaceHeight_pos`: nonnegativity and
  strict positivity.
* `TauCeti.adelicSubspaceHeight_eq_adelicHeight_plucker`: independence of basis choice for `U`.
* `TauCeti.adelicSubspaceHeight_bot`, `TauCeti.adelicSubspaceHeight_span_singleton`: zero- and
  one-dimensional evaluations.
* `TauCeti.adelicSubspaceHeight_one`: for `L = K` and `A = 1`, recovers `Submodule.subspaceHeight`.
* `TauCeti.adelicSubspaceHeight_top`: for `U = ⊤`, equals `(ideleNorm (det A)) ^ ([K : ℚ]⁻¹)`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §§2.8–2.9.
* J. Vaaler and E. Bombieri, *On Siegel's lemma*, Invent. Math. 73 (1983), 11–32.
-/

public section

open IsDedekindDomain Module NumberField Set.powersetCard TauCeti.GlobalNumberFields
open scoped NumberField NNReal

namespace TauCeti

/-- The twisted adelic height of a linear subspace `U ≤ (ι → L)`: the adelic height of the
Plücker coordinates of `Module.finBasis L U`, twisted by `A.compound (finrank L U)`. -/
noncomputable def adelicSubspaceHeight {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (U : Submodule L (ι → L)) : ℝ :=
  adelicHeight (A.compound (finrank L U)) (plucker fun i ↦ (Module.finBasis L U i : ι → L))

/-- Defining equation of `TauCeti.adelicSubspaceHeight`. -/
theorem adelicSubspaceHeight_def {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (U : Submodule L (ι → L)) :
    adelicSubspaceHeight A U =
      adelicHeight (A.compound (finrank L U)) (plucker fun i ↦ (Module.finBasis L U i : ι → L)) :=
  (rfl)

/-- Every adelic subspace height is nonnegative. -/
theorem adelicSubspaceHeight_nonneg {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (U : Submodule L (ι → L)) :
    0 ≤ adelicSubspaceHeight A U :=
  adelicHeight_nonneg _ _

private theorem plucker_coe_basis_ne_zero {L ι : Type*} [Field L] [Finite ι] [LinearOrder ι]
    {U : Submodule L (ι → L)} {p : ℕ} (b : Basis (Fin p) L U) :
    plucker (fun i ↦ (b i : ι → L)) ≠ 0 :=
  (plucker_ne_zero_iff _).mpr <| b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)

/-- Every adelic subspace height is strictly positive. -/
theorem adelicSubspaceHeight_pos {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) (U : Submodule L (ι → L)) :
    0 < adelicSubspaceHeight A U :=
  adelicHeight_pos _ (plucker_coe_basis_ne_zero _)

/-- Independence of `TauCeti.adelicSubspaceHeight` from the choice of basis of `U`. -/
theorem adelicSubspaceHeight_eq_adelicHeight_plucker {K L ι : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) {U : Submodule L (ι → L)}
    (b : Basis (Fin (finrank L U)) L U) :
    adelicSubspaceHeight A U =
      adelicHeight (A.compound (finrank L U)) (plucker fun i ↦ (b i : ι → L)) := by
  have hmk : Projectivization.mk L (plucker fun i ↦ (Module.finBasis L U i : ι → L))
        (plucker_coe_basis_ne_zero (Module.finBasis L U)) =
      Projectivization.mk L (plucker fun i ↦ (b i : ι → L)) (plucker_coe_basis_ne_zero b) := by
    rw [← Submodule.relativePluckerPoint_eq_mk (Module.finBasis L U),
      ← Submodule.relativePluckerPoint_eq_mk b]
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff L _ _ _ _).mp hmk
  rw [adelicSubspaceHeight_def, ← hu, Units.smul_def, adelicHeight_smul _ _ u.ne_zero]

/-- The adelic subspace height of the zero subspace is `1`. -/
@[simp]
theorem adelicSubspaceHeight_bot {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) :
    adelicSubspaceHeight (L := L) A (⊥ : Submodule L (ι → L)) = 1 := by
  have hrank : finrank L (⊥ : Submodule L (ι → L)) = 0 := finrank_bot L (ι → L)
  let : Unique (Set.powersetCard ι (finrank L (⊥ : Submodule L (ι → L)))) :=
    Classical.choice <| Fintype.card_eq_one_iff_nonempty_unique.mp <| by
      rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, hrank, Nat.choose_zero_right]
  have hdet : ∀ (p : ℕ), p = 0 → Matrix.GeneralLinearGroup.det (A.compound p) = 1 := by
    rintro p rfl
    rw [Matrix.GeneralLinearGroup.compound_zero_right, map_one]
  rw [adelicSubspaceHeight_def, adelicHeight_unique _ (plucker_coe_basis_ne_zero _),
    hdet _ hrank, map_one, Units.val_one, NNReal.coe_one, Real.one_rpow]

/-- The adelic subspace height of a line `L ∙ x` equals the adelic height of `x`. -/
theorem adelicSubspaceHeight_span_singleton {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) {x : ι → L} (hx : x ≠ 0) :
    adelicSubspaceHeight (L := L) A (Submodule.span L {x}) = adelicHeight A x := by
  let U := Submodule.span L {x}
  have hrank : finrank L U = 1 := finrank_span_singleton hx
  let b : Basis (Fin (finrank L U)) L U :=
    ((Module.Basis.singleton (Fin 1) L).map
      (LinearEquiv.toSpanNonzeroSingleton L (ι → L) x hx)).reindex (finCongr hrank.symm)
  have hb : ∀ i : Fin (finrank L U), (b i : ι → L) = x := fun i ↦ by
    simp [b, LinearEquiv.toSpanNonzeroSingleton_apply]
  rw [adelicSubspaceHeight_eq_adelicHeight_plucker A b]
  have hmain : ∀ (p : ℕ), p = 1 → ∀ (v : Fin p → ι → L), (∀ i, v i = x) →
      adelicHeight (A.compound p) (plucker v) = adelicHeight A x := by
    rintro p rfl v hv
    have hA : Units.map (Matrix.reindexAlgEquiv (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K)
        (ofSingleton : ι ≃ Set.powersetCard ι 1).symm).toMonoidHom (A.compound 1) = A :=
      Units.ext <| by simp [Matrix.submatrix_compound_ofSingleton]
    have hpl : plucker v ∘ ofSingleton = x := funext fun i ↦ by
      rw [Function.comp_apply, plucker_ofSingleton, hv 0]
    rw [← adelicHeight_reindex (ofSingleton : ι ≃ Set.powersetCard ι 1) (A.compound 1) (plucker v),
      hA, hpl]
  exact hmain _ hrank _ hb

/-- Over `K`, the untwisted adelic subspace height agrees with `Submodule.subspaceHeight`. -/
theorem adelicSubspaceHeight_one {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    [LinearOrder ι] (U : Submodule K (ι → K)) :
    adelicSubspaceHeight (L := K) (1 : GL ι (AdeleRing (𝓞 K) K)) U = U.subspaceHeight := by
  rw [adelicSubspaceHeight_def, Matrix.GeneralLinearGroup.compound_one, adelicHeight_one,
    Submodule.subspaceHeight_eq_height2_plucker (Module.finBasis K U)]

/-- For the full space `⊤ : Submodule L (ι → L)`, the twisted adelic subspace height equals
`(ideleNorm (det A)) ^ ([K : ℚ]⁻¹)`. -/
theorem adelicSubspaceHeight_top {K L ι : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Fintype ι] [LinearOrder ι]
    (A : GL ι (AdeleRing (𝓞 K) K)) :
    adelicSubspaceHeight (L := L) A (⊤ : Submodule L (ι → L)) =
      ((GlobalNumberFields.ideleNorm (Matrix.GeneralLinearGroup.det A) : ℝ≥0) : ℝ) ^
        ((finrank ℚ K : ℝ)⁻¹) := by
  have hrank : finrank L (⊤ : Submodule L (ι → L)) = Fintype.card ι := by
    rw [finrank_top, Module.finrank_pi]
  let : Unique (Set.powersetCard ι (finrank L (⊤ : Submodule L (ι → L)))) :=
    Classical.choice <| Fintype.card_eq_one_iff_nonempty_unique.mp <| by
      rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, hrank,
        Nat.card_eq_fintype_card, Nat.choose_self]
  have hdet : Matrix.GeneralLinearGroup.det
      (A.compound (finrank L (⊤ : Submodule L (ι → L)))) = Matrix.GeneralLinearGroup.det A := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique,
      Matrix.GeneralLinearGroup.val_compound, Matrix.compound_eq_det_of_card_eq hrank,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [adelicSubspaceHeight_def, adelicHeight_unique _ (plucker_coe_basis_ne_zero _), hdet]

end TauCeti
