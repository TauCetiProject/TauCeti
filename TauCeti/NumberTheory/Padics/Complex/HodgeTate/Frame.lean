/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.NumberTheory.Padics.Complex.HodgeTate.Jump

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.StdBasis

/-!
# Hodge–Tate frames and jumps from row relations

Let `p` be a prime and `G_{ℚ_p} = Gal(PadicAlgCl p / ℚ_p)` act on `ℂ_p`. A square matrix
`P : Matrix ι ι ℂ_p` is a *Hodge–Tate frame* of weights `k : ι → ℤ` for a matrix `N` and
`g ∈ G_{ℚ_p}` (`PadicComplex.IsHodgeTateFrame`) if its columns satisfy
`N *ᵥ (g • P.col j) = χ(g) ^ (-k j) • P.col j`. In these coordinates the semilinear map
`v ↦ N *ᵥ (g • v)` acts diagonally on coordinates by `w j ↦ χ(g) ^ (-k j) * g • w j`
(`PadicComplex.IsHodgeTateFrame.mulVec_twist`), and when `P` is invertible the rows of `P⁻¹`
satisfy `P⁻¹ * N = diag(χ(g) ^ (-k i)) * g • P⁻¹` (`PadicComplex.IsHodgeTateFrame.inv_mul_apply`).

Conversely, given a finite basis `e` of an `R`-representation `ρ` and an invertible matrix
`Q ∈ GL ι ℂ_p` whose rows satisfy `Q * γ(ρ g) = diag(χ(j g) ^ (-k i)) * (j g) • Q` for `g` near
`1`, the `γ`-semilinear maps taking `e l` to `Q i l` form a `ℂ_p`-basis of Hodge–Tate maps of
weights `k i`, so `Finset.univ.val.map k` is the multiset of Hodge–Tate jumps
(`PadicComplex.hasHodgeTateJumps_of_rows`).

## Main definitions and results

* `PadicComplex.IsHodgeTateFrame`: Hodge–Tate frame predicate for a matrix over `ℂ_p`.
* `PadicComplex.IsHodgeTateFrame.mulVec_twist`: coordinate action in a Hodge–Tate frame.
* `PadicComplex.IsHodgeTateFrame.inv_mul_apply`: row transformation of `P⁻¹`.
* `PadicComplex.hasHodgeTateJumps_of_rows`: Hodge–Tate jumps and basis from an invertible row
  matrix `Q`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/PadicHodge/Crystalline/HodgeTateJumps.lean`
(`New.Period.IsHodgeTateFrame`, `New.Period.IsHodgeTateFrame.mulVec_twist`,
`New.Period.inv_mul_apply_of_isHodgeTateFrame`, `New.Period.hasJumps_of_rows`).
-/

public section

open Topology Filter Matrix

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]

/-- The columns of `P` are Hodge–Tate vectors of weights `k` for the semilinear map
`v ↦ N *ᵥ (g • v)` of `ℂ_p ^ ι`: it multiplies column `j` by `χ(g) ^ (-k j)`. -/
def IsHodgeTateFrame (N P : Matrix ι ι ℂ_[p]) (k : ι → ℤ)
    (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Prop :=
  ∀ j : ι, N *ᵥ (g • P.col j) = twist (-k j) g.toRingEquiv • P.col j

/-- In the coordinates given by a Hodge–Tate frame `P`, the map `v ↦ N *ᵥ (g • v)` acts on
coordinate `j` by `w j ↦ χ(g) ^ (-k j) * g • w j`. -/
theorem IsHodgeTateFrame.mulVec_twist {N P : Matrix ι ι ℂ_[p]} {k : ι → ℤ}
    {g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (h : IsHodgeTateFrame N P k g) (w : ι → ℂ_[p]) :
    P *ᵥ (fun j : ι ↦ twist (-k j) g.toRingEquiv * g • w j) = N *ᵥ (g • (P *ᵥ w)) := by
  funext i
  have hentry (j : ι) : twist (-k j) g.toRingEquiv * P i j = ∑ m, N i m * g • P m j :=
    (congrFun (h j) i).symm
  calc (P *ᵥ fun j ↦ twist (-k j) g.toRingEquiv * g • w j) i
      = ∑ j, (twist (-k j) g.toRingEquiv * P i j) * g • w j := by
        simp only [mulVec, dotProduct]; exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ∑ j, ∑ m, N i m * g • P m j * g • w j := by simp only [hentry, Finset.sum_mul]
    _ = ∑ m, N i m * ∑ j, g • P m j * g • w j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ ↦ by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = (N *ᵥ (g • (P *ᵥ w))) i := by
        simp [mulVec, dotProduct, smul_mul', Finset.smul_sum]

/-- The rows of the inverse of an invertible Hodge–Tate frame `P` satisfy
`P⁻¹ * N = diag(χ(g) ^ (-k i)) * g • P⁻¹`. -/
theorem IsHodgeTateFrame.inv_mul_apply [DecidableEq ι] {N : Matrix ι ι ℂ_[p]} {k : ι → ℤ}
    {g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {P : Matrix.GeneralLinearGroup ι ℂ_[p]}
    (h : IsHodgeTateFrame N P k g) (i l : ι) :
    (((P⁻¹ : Matrix.GeneralLinearGroup ι ℂ_[p]) : Matrix ι ι ℂ_[p]) * N) i l =
      twist (-k i) g.toRingEquiv * g •
        ((P⁻¹ : Matrix.GeneralLinearGroup ι ℂ_[p]) : Matrix ι ι ℂ_[p]) i l := by
  set Pinv : Matrix ι ι ℂ_[p] := P⁻¹.val with hPinv
  have hentry : (Pinv *ᵥ (P *ᵥ fun j : ι ↦
      twist (-k j) g.toRingEquiv * g • (Pinv *ᵥ (1 : Matrix ι ι ℂ_[p]).col l) j)) i =
      (Pinv *ᵥ (N *ᵥ (g • (P *ᵥ (Pinv *ᵥ (1 : Matrix ι ι ℂ_[p]).col l))))) i := by
    rw [h.mulVec_twist]
  simp only [mulVec_mulVec, hPinv, Units.inv_mul, Units.mul_inv, one_mulVec] at hentry
  simpa [hPinv, Matrix.one_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply] using hentry.symm

/-- Given a finite `R`-basis `e` of `T`, a ring map `γ : R →+* ℂ_p` whose values are fixed near
`1`, and an invertible matrix `Q ∈ GL ι ℂ_p` with `Q * γ(ρ g) = diag(χ(j g) ^ (-k i)) * (j g) • Q`
for `g` near `1`, the `k i` form the multiset of Hodge–Tate jumps at `γ` and the rows of `Q` define
a `ℂ_p`-basis of Hodge–Tate maps of weights `k i`. -/
theorem hasHodgeTateJumps_of_rows [DecidableEq ι] {Γ R T : Type*} [Monoid Γ] [CommRing R]
    [AddCommGroup T] [Module R T] {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)}
    (hj : Set.range j ∈ 𝓝 1) {ρ : Representation R Γ T} {γ : R →+* ℂ_[p]}
    (hγ : ∀ r : R, ∀ᶠ g in comap j (𝓝 1), j g • γ r = γ r)
    (e : Module.Basis ι R T) (Q : Matrix.GeneralLinearGroup ι ℂ_[p]) (k : ι → ℤ)
    (hrows : ∀ᶠ g in comap j (𝓝 1), ∀ i l : ι,
      ((Q : Matrix ι ι ℂ_[p]) * (LinearMap.toMatrix e e (ρ g)).map γ) i l =
        twist (-k i) (j g).toRingEquiv * j g • (Q : Matrix ι ι ℂ_[p]) i l) :
    HasHodgeTateJumps j ρ γ (Finset.univ.val.map k) ∧
      ∃ b : Module.Basis ι ℂ_[p] (T →ₛₗ[γ] ℂ_[p]),
        (∀ i : ι, b i ∈ hodgeTateMaps j ρ γ (k i)) ∧
        ∀ i l : ι, b i (e l) = (Q : Matrix ι ι ℂ_[p]) i l := by
  let eval : (T →ₛₗ[γ] ℂ_[p]) ≃ₗ[ℂ_[p]] (ι → ℂ_[p]) :=
    LinearEquiv.ofBijective (LinearMap.pi fun l ↦ LinearMap.id.flip (e l))
      ⟨fun f g hfg ↦ e.ext (congrFun hfg), fun c ↦ by
        let _ : Algebra R ℂ_[p] := γ.toAlgebra
        exact ⟨⟨(e.constr ℕ c).toAddHom, (e.constr ℕ c).map_smul'⟩, funext (e.constr_basis ℕ c)⟩⟩
  let Qlin : (ι → ℂ_[p]) ≃ₗ[ℂ_[p]] (ι → ℂ_[p]) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' (Q : Matrix ι ι ℂ_[p])ᵀ)
      (Matrix.toLin' Q⁻¹.valᵀ)
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
        Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
        Matrix.toLin'_one])
  let b : Module.Basis ι ℂ_[p] (T →ₛₗ[γ] ℂ_[p]) :=
    (Pi.basisFun ℂ_[p] ι).map (Qlin.trans eval.symm)
  have hval (i l : ι) : b i (e l) = (Q : Matrix ι ι ℂ_[p]) i l := by
    change eval (b i) l = (Q : Matrix ι ι ℂ_[p]) i l
    simp [b, Qlin, Matrix.mulVec_single]
  have hmem (i : ι) : b i ∈ hodgeTateMaps j ρ γ (k i) := mem_hodgeTateMaps.mpr fun x ↦ by
    filter_upwards [hrows, eventually_all.mpr fun l ↦ hγ (e.repr x l)] with g hg hfix
    have hx : x = ∑ l, e.repr x l • e l := (e.sum_repr x).symm
    have hbasis (l : ι) : b i (ρ g (e l)) =
        twist (-k i) (j g).toRingEquiv * j g • (Q : Matrix ι ι ℂ_[p]) i l := by
      have hexp : ρ g (e l) = ∑ m, LinearMap.toMatrix e e (ρ g) m l • e m := by
        simp only [LinearMap.toMatrix_apply, e.sum_repr]
      rw [hexp, map_sum]
      simpa [hval, Matrix.mul_apply, mul_comm] using hg i l
    conv_lhs => rw [hx, map_sum, map_sum]
    conv_rhs => rw [hx, map_sum]
    simp only [map_smul, map_smulₛₗ, hbasis, hval, Finset.smul_sum, smul_mul', Finset.mul_sum,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [hfix l]; ring
  exact ⟨hasHodgeTateJumps_of_basis hj b hmem, b, hmem, hval⟩

end PadicComplex
