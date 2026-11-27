/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.ToLin

import TauCeti.GroupTheory.OrderOfElement.InfiniteOrder
import TauCeti.LinearAlgebra.Eigenspace.Decomposition
import TauCeti.LinearAlgebra.LinearMap.EqOn
import TauCeti.LinearAlgebra.Matrix.DetDescent

/-!
# Endomorphisms scaled by conjugation

Let `F` and `N` be endomorphisms of a module `M` over a commutative ring with
`F * N = c • (N * F)`. Then `N` maps the generalized `μ`-eigenspace of `F` into the generalized
`c μ`-eigenspace (`Module.End.mapsTo_maxGenEigenspace_of_mul_eq_smul_mul`).

If `V` is a finite-dimensional vector space over a field `K`, `F` is injective and `c` has
infinite multiplicative order, then for every `a ≠ 0` there is an automorphism `g` of `V` which
commutes with every endomorphism commuting with `F` and satisfies `g * N = a • (N * g)`, so that
`g` conjugates `N` to `a • N`, that is `g * N * g⁻¹ = a • N`, while fixing everything that
commutes with `F`
(`Module.End.exists_mul_eq_smul_mul_of_mul_eq_smul_mul`).

For `c = 0` the endomorphism `N` vanishes, and over a finite field every `c ≠ 0` has finite order,
so the content is the case of an infinite field and `c ≠ 0`. Over an algebraically closed field
the automorphism acts on the generalized `μ`-eigenspace of `F` by `a ^ k(μ)`, where `k : K → ℤ`
satisfies `k (c * μ) = k μ + 1` for `μ ≠ 0`: such an exponent exists because the powers of `c`
act freely on `Kˣ` (`TauCeti.exists_apply_mul_eq_add_one_of_not_isOfFinOrder`). The eigenvalue `0`
does not occur since `F` is injective (`Module.End.maxGenEigenspace_zero_eq_bot_of_injective`),
and the generalized eigenspaces decompose `V` (`Module.End.isInternal_maxGenEigenspace`), so the
automorphism is `Module.End.scalarOn F fun μ ↦ a ^ k μ`. Over an infinite field the automorphism
found over the algebraic closure descends, by the matrix form of the Noether–Deuring theorem
`Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap`.

This is the linear algebra behind the isomorphism `(r, N) ≅ (r, a N)` of Weil–Deligne parameters
with finite inertia image, `TauCeti.WeilDeligneParameter.nonempty_iso_rescale`: there `F` is the
image of a suitable power of a Frobenius element, which commutes with the whole Weil action, and
`c` is a nonzero power of `q`.

## Main results

* `Module.End.mapsTo_maxGenEigenspace_of_mul_eq_smul_mul`: `N` maps the generalized
  `μ`-eigenspace of `F` into the generalized `c μ`-eigenspace.
* `Module.End.exists_mul_eq_smul_mul_of_mul_eq_smul_mul`: the automorphism `g`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), proof of §8.4.3, p. 569.
-/

public section

namespace Module.End

open Function

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `F * N = c • (N * F)`, then `N` maps the generalized `μ`-eigenspace of `F` into the
generalized `c μ`-eigenspace. -/
theorem mapsTo_maxGenEigenspace_of_mul_eq_smul_mul {F N : End R M} {c : R}
    (h : F * N = c • (N * F)) (μ : R) :
    Set.MapsTo N (F.maxGenEigenspace μ) (F.maxGenEigenspace (c * μ)) := fun _ hv ↦
  mapsTo_genEigenspace_of_comp N (by rw [← mul_eq_comp, h, mul_eq_comp, LinearMap.comp_smul])
    (c * μ) ⊤ (genEigenspace_le_smul F μ c ⊤ hv)

end CommRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section IsAlgClosed

variable [IsAlgClosed K] [FiniteDimensional K V]

/-- The automorphism of `Module.End.exists_mul_eq_smul_mul_of_mul_eq_smul_mul` over an
algebraically closed field, for `c ≠ 0`: it acts on the generalized `μ`-eigenspace of `F` by
`a ^ k(μ)`. -/
private theorem exists_mul_eq_smul_mul_of_isAlgClosed {F N : End K V} (hF : Injective F) {c : K}
    (hc0 : c ≠ 0) (hc : ¬IsOfFinOrder c) (hFN : F * N = c • (N * F)) {a : K} (ha : a ≠ 0) :
    ∃ g : (End K V)ˣ, (∀ T : End K V, Commute F T → Commute (g : End K V) T) ∧
      (g : End K V) * N = a • (N * g) := by
  classical
  obtain ⟨e, he⟩ := TauCeti.exists_apply_mul_eq_add_one_of_not_isOfFinOrder
    (u := Units.mk0 c hc0) (Units.isOfFinOrder_val.not.mp hc)
  let k : K → ℤ := fun μ ↦ if h : μ = 0 then 0 else e (Units.mk0 μ h)
  have hk (μ : K) (hμ : μ ≠ 0) : k (c * μ) = k μ + 1 := by
    have hu : Units.mk0 (c * μ) (mul_ne_zero hc0 hμ) = Units.mk0 μ hμ * Units.mk0 c hc0 :=
      Units.ext (mul_comm c μ)
    simp only [k, hμ, mul_ne_zero hc0 hμ, dite_false, hu, he]
  have hunit (m₁ m₂ : K → ℤ) (h : ∀ μ, m₁ μ + m₂ μ = 0) :
      scalarOn F (fun μ ↦ a ^ m₁ μ) * scalarOn F (fun μ ↦ a ^ m₂ μ) = 1 := by
    rw [← scalarOn_mul, ← scalarOn_one F]
    congr 1
    funext μ
    rw [Pi.mul_apply, Pi.one_apply, ← zpow_add₀ ha, h, zpow_zero]
  refine ⟨⟨scalarOn F fun μ ↦ a ^ k μ, scalarOn F fun μ ↦ a ^ (-k μ),
    hunit _ _ fun μ ↦ add_neg_cancel _, hunit _ _ fun μ ↦ neg_add_cancel _⟩,
    fun T hT ↦ commute_scalarOn hT _, ?_⟩
  refine LinearMap.ext_of_iSup_eq_top (iSup_maxGenEigenspace_eq_top F) fun μ v hv ↦ ?_
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [maxGenEigenspace_zero_eq_bot_of_injective hF, Submodule.mem_bot] at hv
    simp [hv]
  · have hNv := mapsTo_maxGenEigenspace_of_mul_eq_smul_mul hFN μ hv
    rw [mul_apply_eq_comp, scalarOn_apply F _ hNv, LinearMap.smul_apply,
      mul_apply_eq_comp, scalarOn_apply F _ hv, map_smul, smul_smul, hk μ hμ,
      zpow_add_one₀ ha, mul_comm]

end IsAlgClosed

/-- The matrix step of the descent: a nonsingular matrix `Y` commuting with the matrices of the
endomorphisms commuting with `F`, with `(a • N) * Y = Y * N` in matrices, is the matrix of an
automorphism `g` with the same properties. -/
private theorem exists_unit_of_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    {F N : End K V} {a : K} {Y : Matrix ι ι K} (hY : Y.det ≠ 0)
    (hT : ∀ T : End K V, Commute F T →
      LinearMap.toMatrixAlgEquiv b T * Y = Y * LinearMap.toMatrixAlgEquiv b T)
    (hN : (a • LinearMap.toMatrixAlgEquiv b N) * Y = Y * LinearMap.toMatrixAlgEquiv b N) :
    ∃ g : (End K V)ˣ, (∀ T : End K V, Commute F T → Commute (g : End K V) T) ∧
      (g : End K V) * N = a • (N * g) := by
  let M := LinearMap.toMatrixAlgEquiv b
  have hYu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).mpr (isUnit_iff_ne_zero.mpr hY)
  have hgu : IsUnit (M.symm Y) := hYu.map M.symm
  refine ⟨hgu.unit, fun T hT' ↦ ?_, ?_⟩
  · refine (commute_iff_eq _ _).mpr ?_
    rw [IsUnit.unit_spec]
    apply M.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
    exact (hT T hT').symm
  · rw [IsUnit.unit_spec]
    apply M.injective
    rw [map_mul, map_smul, map_mul, AlgEquiv.apply_symm_apply, ← Matrix.smul_mul]
    exact hN.symm

/-- The automorphism of `Module.End.exists_mul_eq_smul_mul_of_mul_eq_smul_mul` over an infinite
field, for `c ≠ 0`: constructed over the algebraic closure, it descends by the Noether–Deuring
theorem for infinite fields. -/
private theorem exists_mul_eq_smul_mul_of_infinite [Infinite K] [FiniteDimensional K V]
    {F N : End K V} (hF : Injective F) {c : K} (hc0 : c ≠ 0) (hc : ¬IsOfFinOrder c)
    (hFN : F * N = c • (N * F)) {a : K} (ha : a ≠ 0) :
    ∃ g : (End K V)ˣ, (∀ T : End K V, Commute F T → Commute (g : End K V) T) ∧
      (g : End K V) * N = a • (N * g) := by
  classical
  let L := AlgebraicClosure K
  let b := Module.finBasis K V
  let n := Module.finrank K V
  let M : End K V ≃ₐ[K] Matrix (Fin n) (Fin n) K := LinearMap.toMatrixAlgEquiv b
  -- `P` identifies endomorphisms of `Fin n → L` with matrices; `ψ` is base change to `L`
  let P := LinearMap.toMatrixAlgEquiv' (R := L) (n := Fin n)
  let ψ : End K V →ₐ[K] End L (Fin n → L) :=
    (P.symm.restrictScalars K).toAlgHom.comp ((Algebra.ofId K L).mapMatrix.comp M.toAlgHom)
  have hψ (T : End K V) : P (ψ T) = (M T).map (algebraMap K L) := by
    ext i j
    simp [ψ, AlgHom.mapMatrix_apply]
  have hψsmul (x : K) (T : End K V) : ψ (x • T) = algebraMap K L x • ψ T := by
    rw [map_smul, algebraMap_smul]
  have hFu : IsUnit F :=
    (Module.End.isUnit_iff F).mpr ⟨hF, LinearMap.injective_iff_surjective.mp hF⟩
  have hFL : Injective (ψ F) := ((Module.End.isUnit_iff _).mp (hFu.map ψ)).injective
  have hcL : ¬IsOfFinOrder (algebraMap K L c) :=
    ((algebraMap K L).injective.isOfFinOrder_iff (f := (algebraMap K L : K →* L))).not.mpr hc
  have hFNL : ψ F * ψ N = algebraMap K L c • (ψ N * ψ F) := by
    rw [← map_mul, ← map_mul, ← hψsmul, hFN]
  obtain ⟨gL, hgT, hgN⟩ := exists_mul_eq_smul_mul_of_isAlgClosed hFL
    ((map_ne_zero _).mpr hc0) hcL hFNL ((map_ne_zero (algebraMap K L)).mpr ha)
  let X : Matrix (Fin n) (Fin n) L := P gL
  have hX : X.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det X).mp (gL.isUnit.map P)).ne_zero
  -- the relations satisfied by `gL` translate into relations between matrices
  have hmat (T : End K V) {x : L} (h : (gL : End L (Fin n → L)) * ψ T = x • (ψ T * gL)) :
      x • ((M T).map (algebraMap K L) * X) = X * (M T).map (algebraMap K L) := by
    simpa only [map_mul, map_smul, hψ] using (congrArg P h).symm
  let ι := Option {T : End K V // Commute F T}
  let A : ι → Matrix (Fin n) (Fin n) K := fun s ↦ s.elim (M N) fun T ↦ M T
  let B : ι → Matrix (Fin n) (Fin n) K := fun s ↦ s.elim (a • M N) fun T ↦ M T
  obtain ⟨Y, hY, hYAB⟩ := Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap A B hX
    (by
      rintro (_ | ⟨T, hT⟩)
      · simpa only [B, A, Option.elim_none, Matrix.map_smul' _ a _ (map_mul _), Matrix.smul_mul]
          using hmat N hgN
      · simpa only [A, B, Option.elim_some, one_smul] using
          hmat T (x := 1) (by rw [one_smul]; exact (hgT _ (hT.map ψ)).eq))
  exact exists_unit_of_matrix b hY (fun T hT ↦ hYAB (some ⟨T, hT⟩)) (hYAB none)

/-- **Rescaling a conjugation-scaled endomorphism.** Let `F` be an injective endomorphism of a
finite-dimensional vector space and `F * N = c • (N * F)` with `c` of infinite multiplicative
order. For every `a ≠ 0` there is an automorphism `g` commuting with every endomorphism that
commutes with `F`, with `g * N = a • (N * g)`. -/
theorem exists_mul_eq_smul_mul_of_mul_eq_smul_mul [FiniteDimensional K V] {F N : End K V}
    (hF : Injective F) {c : K} (hc : ¬IsOfFinOrder c) (hFN : F * N = c • (N * F)) {a : K}
    (ha : a ≠ 0) :
    ∃ g : (End K V)ˣ, (∀ T : End K V, Commute F T → Commute (g : End K V) T) ∧
      (g : End K V) * N = a • (N * g) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · -- `F * N = 0` and `F` is injective, so `N = 0`
    have hN : N = 0 := LinearMap.ext fun v ↦ hF <| by
      simpa using LinearMap.congr_fun hFN v
    exact ⟨1, fun T _ ↦ Commute.one_left T, by simp [hN]⟩
  cases finite_or_infinite K with
  | inl _ =>
    -- over a finite field every nonzero element has finite order
    exact absurd (Units.isOfFinOrder_val.mpr (isOfFinOrder_of_finite (Units.mk0 c hc0))) hc
  | inr _ => exact exists_mul_eq_smul_mul_of_infinite hF hc0 hc hFN ha

end Module.End
