/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic

/-!
# Graded maps out of a row-finite twisted free module

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)`, with free
differential graded left module `K_m = P →₀ A`, and let `N` be a differential graded left module.
A graded `A`-linear map `Ψ : K_m → N` of degree `j` satisfies the Koszul rule
`Ψ (a • f) = (-1)^(j |a|) a • Ψ f`, so it is determined by the images `u x ∈ N` of the generators,
of degree `j - ind x`, which may be chosen freely. The map with these values is the signed map
`TauCeti.rowFiniteSignedMap 𝒜 j u` of `TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Basic`,
which sends `single x a` to `(-1)^(j |a|) a • u x`. For `j = 0` it is the linear combination
`Finsupp.linearCombination A u` (`TauCeti.rowFiniteSignedMap_zero_left`).

The complex of graded maps `K_m → N` has differential `δ Ψ = d_N ∘ Ψ - (-1)^j Ψ ∘ D`. Read on
generators, it sends a family `u` of degree `j` to the family
`δ_j u = x ↦ d_N (u x) - (-1)^j Ψ_u (m x)` (`TauCeti.rowFiniteHomDifferential`), because the
differential of the generator `x` is its row `m x`. The Leibniz identity
`Ψ_{δ_j u} = d_N ∘ Ψ_u - (-1)^j Ψ_u ∘ D` holds on the whole free module
(`TauCeti.rowFiniteSignedMap_rowFiniteHomDifferential`), so `δ_j` is the differential of
the complex of graded maps out of `K_m`, written on generator values, and it squares to zero
(`TauCeti.RowFiniteTwistingCocycle.rowFiniteHomDifferential_rowFiniteHomDifferential`).
Its zero-cycles are the families giving morphisms of differential graded modules
(`TauCeti.forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero`), and for free targets
its degree `0` and `-1`
equations are those of row-finite continuation and parametrized cocycles.

The value of `δ_j u` at `x` only reads `u` on `x` and on the support of the row `m x`
(`TauCeti.rowFiniteHomDifferential_congr`, from `TauCeti.rowFiniteSignedMap_congr` for `Ψ_u`).
This locality is what lets maps out of `K_m` be built one generator at a time when the rows lower
a bounded-below index, as in `TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Lifting`.

## Main definitions

* `TauCeti.rowFiniteHomDifferential m dN j u`: the differential of the complex of graded maps out
  of `K_m`, on generator values.

## References

* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational homotopy theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6.
-/

public noncomputable section

open DirectSum

namespace TauCeti

universe uR uA uN uN' uP

variable {R : Type uR} {A : Type uA} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {ind : P → ℤ}
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {N' : Type uN'} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

/-! ### The differential of the complex of graded maps -/

section HomDifferential

variable (𝒜) in
/-- **The differential of the complex of graded maps out of `K_m`, on generator values.** A family
`u` of degree `j`, with `u x` of degree `j - ind x`, is sent to the family
`x ↦ d_N (u x) - (-1)^j Ψ_u (m x)` of degree `j + 1`, where `Ψ_u` is the graded map with
generator values `u`. These are the generator values of `d_N ∘ Ψ_u - (-1)^j Ψ_u ∘ D`
(`TauCeti.rowFiniteSignedMap_rowFiniteHomDifferential`). -/
def rowFiniteHomDifferential (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u : P → N) : P → N :=
  fun x ↦ dN (u x) - j.negOnePow • rowFiniteSignedMap 𝒜 j u (m x)

theorem rowFiniteHomDifferential_apply (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u : P → N)
    (x : P) :
    rowFiniteHomDifferential 𝒜 m dN j u x =
      dN (u x) - j.negOnePow • rowFiniteSignedMap 𝒜 j u (m x) :=
  (rfl)

/-- The differential of graded maps vanishes on the zero family. -/
@[simp]
theorem rowFiniteHomDifferential_zero (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) :
    rowFiniteHomDifferential 𝒜 m dN j (0 : P → N) = 0 := by
  funext x
  simp [rowFiniteHomDifferential_apply]

/-- The differential of graded maps is additive. -/
theorem rowFiniteHomDifferential_add (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u u' : P → N) :
    rowFiniteHomDifferential 𝒜 m dN j (u + u') =
      rowFiniteHomDifferential 𝒜 m dN j u + rowFiniteHomDifferential 𝒜 m dN j u' := by
  funext x
  simp only [rowFiniteHomDifferential_apply, Pi.add_apply, map_add,
    rowFiniteSignedMap_add, smul_add]
  abel

/-- The differential of graded maps is subtractive. -/
theorem rowFiniteHomDifferential_sub (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u u' : P → N) :
    rowFiniteHomDifferential 𝒜 m dN j (u - u') =
      rowFiniteHomDifferential 𝒜 m dN j u - rowFiniteHomDifferential 𝒜 m dN j u' := by
  funext x
  simp only [rowFiniteHomDifferential_apply, Pi.sub_apply, map_sub,
    rowFiniteSignedMap_sub, smul_sub]
  abel

/-- The differential of graded maps commutes with negation. -/
@[simp]
theorem rowFiniteHomDifferential_neg (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) (u : P → N) :
    rowFiniteHomDifferential 𝒜 m dN j (-u) = -rowFiniteHomDifferential 𝒜 m dN j u := by
  funext x
  simp only [rowFiniteHomDifferential_apply, Pi.neg_apply, map_neg,
    rowFiniteSignedMap_neg, smul_neg]
  abel

/-- The value of the differential at `x` only depends on the generator values at `x` and on the
support of the row of `x`. -/
theorem rowFiniteHomDifferential_congr (m : P → P →₀ A) (dN : N →ₗ[R] N) (j : ℤ) {u u' : P → N}
    {x : P} (hx : u x = u' x) (h : ∀ y ∈ (m x).support, u y = u' y) :
    rowFiniteHomDifferential 𝒜 m dN j u x = rowFiniteHomDifferential 𝒜 m dN j u' x := by
  rw [rowFiniteHomDifferential_apply, rowFiniteHomDifferential_apply, hx,
    rowFiniteSignedMap_congr j h]

/-- Postcomposition with an `A`-linear map commuting with the differentials commutes with the
differential of graded maps. -/
theorem map_rowFiniteHomDifferential (m : P → P →₀ A) {dN : N →ₗ[R] N} {dN' : N' →ₗ[R] N'}
    (g : N →ₗ[A] N') (hg : ∀ z, g (dN z) = dN' (g z)) (j : ℤ) (u : P → N) :
    g ∘ rowFiniteHomDifferential 𝒜 m dN j u = rowFiniteHomDifferential 𝒜 m dN' j (g ∘ u) := by
  funext x
  simp only [Function.comp_apply, rowFiniteHomDifferential_apply, map_sub, hg,
    LinearMap.map_rowFiniteSignedMap, Units.smul_def, map_zsmul]

variable {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {dN : N →ₗ[R] N} {hA : IsDGAlgebra 𝒜 d}

/-- The differential of graded maps raises the degree of generator values by one. -/
theorem rowFiniteHomDifferential_mem (hN : IsDGLeftModule hA 𝒩 dN)
    (m : RowFiniteTwistingCocycle 𝒜 d P ind) {j : ℤ} {u : P → N}
    (hu : ∀ x, u x ∈ 𝒩 (j - ind x)) (x : P) :
    rowFiniteHomDifferential 𝒜 m.m dN j u x ∈ 𝒩 (j + 1 - ind x) := by
  refine Submodule.sub_mem _ ?_ (Submodule.smul_of_tower_mem _ _ ?_)
  · convert hN.isHomogeneous.map_mem (hu x) using 2
    ring
  · convert rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading
      (m.m_mem_rowFiniteTotalGrading x) fun y _ ↦ hu y
      using 2
    ring

/-- **The Leibniz identity of graded maps.** The graded map with generator values `δ_j u` is
`d_N ∘ Ψ_u - (-1)^j Ψ_u ∘ D` on the whole free module. -/
theorem rowFiniteSignedMap_rowFiniteHomDifferential (hN : IsDGLeftModule hA 𝒩 dN)
    (m : P → P →₀ A) (j : ℤ) (u : P → N) (f : P →₀ A) :
    rowFiniteSignedMap 𝒜 (j + 1) (rowFiniteHomDifferential 𝒜 m dN j u) f =
      dN (rowFiniteSignedMap 𝒜 j u f) -
        j.negOnePow • rowFiniteSignedMap 𝒜 j u
          (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, hf, hg, smul_add]
    abel
  | single x a =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add a b ha hb =>
      simp only [Finsupp.single_add, map_add, ha, hb, smul_add]
      abel
    | @homogeneous q a =>
      -- The two terms involving `d a` cancel; what remains is `a` times the generator value.
      have hΨ : rowFiniteSignedMap 𝒜 j u (q.negOnePow • ((a : A) • m x)) =
          (j * q + q).negOnePow • ((a : A) • rowFiniteSignedMap 𝒜 j u (m x)) := by
        rw [LinearMap.map_smul_of_tower, rowFiniteSignedMap_smul_of_mem j u a.2, smul_smul,
          ← Int.negOnePow_add, add_comm q]
      have hd : dN (rowFiniteSignedMap 𝒜 j u (Finsupp.single x a)) =
          (j * q).negOnePow • (d a • u x) + (j * q + q).negOnePow • ((a : A) • dN (u x)) := by
        rw [rowFiniteSignedMap_single j u x a.2, LinearMap.map_smul_of_tower,
          hN.leibniz a.2, smul_add, smul_smul, ← Int.negOnePow_add]
      have hj : j.negOnePow * (j * (q + 1)).negOnePow = (j * q).negOnePow := by
        rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
        exact ⟨j, by ring⟩
      rw [rowFiniteSignedMap_single _ _ x a.2, rowFiniteTwistedDifferential_single m x a.2,
        map_add, rowFiniteSignedMap_single j u x (hA.map_mem a.2), hΨ, hd,
        rowFiniteHomDifferential_apply, smul_add, smul_smul, hj, smul_sub, smul_sub, smul_smul,
        ← Int.negOnePow_add, smul_comm (a : A) j.negOnePow, smul_smul, ← Int.negOnePow_add,
        show (j + 1) * q = j * q + q by ring, show j + (j * q + q) = j * q + q + j by ring]
      abel

/-- The differential of graded maps squares to zero at each generator:
`δ_(j+1) (δ_j u) x = 0`. -/
theorem RowFiniteTwistingCocycle.rowFiniteHomDifferential_rowFiniteHomDifferential_apply
    (hN : IsDGLeftModule hA 𝒩 dN) (m : RowFiniteTwistingCocycle 𝒜 d P ind) (j : ℤ) (u : P → N)
    (x : P) :
    rowFiniteHomDifferential 𝒜 m.m dN (j + 1) (rowFiniteHomDifferential 𝒜 m.m dN j u) x = 0 := by
  rw [rowFiniteHomDifferential_apply, rowFiniteSignedMap_rowFiniteHomDifferential hN,
    m.differential_row, map_zero, smul_zero, sub_zero, rowFiniteHomDifferential_apply, map_sub,
    hN.sq_zero, LinearMap.map_smul_of_tower, Int.negOnePow_succ, Units.neg_smul]
  abel

/-- **The differential of graded maps squares to zero.** -/
theorem RowFiniteTwistingCocycle.rowFiniteHomDifferential_rowFiniteHomDifferential
    (hN : IsDGLeftModule hA 𝒩 dN) (m : RowFiniteTwistingCocycle 𝒜 d P ind) (j : ℤ) (u : P → N) :
    rowFiniteHomDifferential 𝒜 m.m dN (j + 1) (rowFiniteHomDifferential 𝒜 m.m dN j u) = 0 :=
  funext (m.rowFiniteHomDifferential_rowFiniteHomDifferential_apply hN j u)

omit [DirectSum.Decomposition 𝒩] in
/-- **The zero-cycles are the morphisms of differential graded modules**: the linear combination
of generator values `u` commutes with the differentials exactly when `u` has vanishing
differential in degree `0`. -/
theorem forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero (m : P → P →₀ A)
    (u : P → N) :
    (∀ x, Finsupp.linearCombination A u (m x) = dN (u x)) ↔
      rowFiniteHomDifferential 𝒜 m dN 0 u = 0 := by
  simp only [funext_iff, rowFiniteHomDifferential_apply, Int.negOnePow_zero, one_smul,
    rowFiniteSignedMap_zero_left, LinearMap.restrictScalars_apply, Pi.zero_apply,
    sub_eq_zero]
  exact forall_congr' fun _ ↦ eq_comm

omit [DirectSum.Decomposition 𝒩] in
/-- In degree `-1`, the differential of graded maps adds the signed row substitution: this is the
left-hand side of the equation of a parametrized cocycle. -/
theorem rowFiniteHomDifferential_neg_one_apply (m : P → P →₀ A) (u : P → N) (x : P) :
    rowFiniteHomDifferential 𝒜 m dN (-1) u x =
      dN (u x) + rowFiniteSignedMap 𝒜 1 u (m x) := by
  rw [rowFiniteHomDifferential_apply, rowFiniteSignedMap_neg_one, Int.negOnePow_neg,
    Int.negOnePow_one, Units.neg_smul, one_smul, sub_neg_eq_add]

end HomDifferential

end TauCeti
