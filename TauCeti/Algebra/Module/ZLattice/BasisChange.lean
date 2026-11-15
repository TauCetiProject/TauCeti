/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.Geometry.Manifold.Algebra.Quotient

/-!
# Integral changes of coordinates on standard real tori

Let `b` and `c` be two `ℤ`-bases of the same free abelian group `Λ`, indexed by finite types `ι`
and `κ`. The coordinates of an element of `Λ` in the two bases are related by the integral
change-of-basis matrix `c.toMatrix b`. Extending scalars to `ℝ`, this matrix is a real linear
equivalence `ℝ^ι ≃ ℝ^κ` (`Module.Basis.realCoordChange`), with inverse the reverse change of
basis, and it carries the standard lattice `ℤ^ι = span ℤ (range (Pi.basisFun ℝ ι))` onto `ℤ^κ`
(`Module.Basis.map_realCoordChange_span_basisFun`). It therefore descends to a smooth
diffeomorphism of the standard tori `ℝ^ι/ℤ^ι ≃ ℝ^κ/ℤ^κ` (`Module.Basis.torusCoordChange`), the
orbit spaces of translation by the standard lattices with their quotient manifold structures.

These are the fixed coordinate changes by which trivializations of a family of tori built from
two integral bases of its period lattice differ. The torus maps are induced by real-linear maps of
the covering vector spaces, not complex-linear ones.

## Main definitions

* `Module.Basis.realCoordChange`: the real coordinate change `ℝ^ι ≃ₗ[ℝ] ℝ^κ` from `b` to `c`.
* `Module.Basis.torusCoordChange`: the induced `C^n` diffeomorphism of standard tori.

## Main results

* `Module.Basis.realCoordChange_intCast`: on integral coordinates of `l : Λ` in `b` the coordinate
  change gives the integral coordinates of `l` in `c`.
* `Module.Basis.realCoordChange_symm`, `Module.Basis.realCoordChange_refl`,
  `Module.Basis.realCoordChange_trans`, `Module.Basis.realCoordChange_realCoordChange`: inverse,
  identity and composition laws, with the corresponding laws `Module.Basis.torusCoordChange_symm`,
  `Module.Basis.torusCoordChange_refl`, `Module.Basis.torusCoordChange_trans` and
  `Module.Basis.torusCoordChange_torusCoordChange` on standard tori.
* `Module.Basis.map_realCoordChange_span_basisFun`: the coordinate change carries `ℤ^ι` onto `ℤ^κ`.
* `Module.Basis.torusCoordChange_mk`, `Module.Basis.coe_torusCoordChange`: the diffeomorphism of
  standard tori on representatives, and as an additive equivalence.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices, and the effect of a change of lattice basis).
* Tau Ceti PR [#21079](https://github.com/TauCetiProject/TauCeti/pull/21079) (closed, unmerged)
  proved basis independence for the topological trivialization of a family of tori; the design of
  `Module.Basis.realCoordChange` (an integral change-of-basis matrix extended to `ℝ`) and of its
  `intCast`, `symm`, `refl` and `trans` laws is adapted from it.
-/

public section

open Set Submodule
open scoped Matrix Manifold ContDiff

namespace Module.Basis

variable {Λ : Type*} [AddCommGroup Λ] {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

/-- The real coordinate change from the `ℤ`-basis `b` to the `ℤ`-basis `c` of `Λ`: multiplication
by the integral change-of-basis matrix `c.toMatrix b`, whose `(j, i)` entry is `c.repr (b i) j`,
as a real linear equivalence `ℝ^ι ≃ₗ[ℝ] ℝ^κ`. Its inverse is the change from `c` to `b`
(`Module.Basis.realCoordChange_symm`). -/
noncomputable def realCoordChange (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ) := by
  classical
  exact Matrix.toLin'OfInv (M := (b.toMatrix c).map (Int.castRingHom ℝ))
    (M' := (c.toMatrix b).map (Int.castRingHom ℝ))
    (by rw [← Matrix.map_mul, toMatrix_mul_toMatrix_flip]; simp)
    (by rw [← Matrix.map_mul, toMatrix_mul_toMatrix_flip]; simp)

/-- The real coordinate change is multiplication by the integral change-of-basis matrix. -/
theorem realCoordChange_apply (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (x : ι → ℝ) :
    realCoordChange b c x = (c.toMatrix b).map (Int.castRingHom ℝ) *ᵥ x := by
  classical
  ext j
  rw [realCoordChange, Matrix.toLin'OfInv_apply, Matrix.toLin'_apply]

/-- The real coordinate change sends the coordinates of `l : Λ` in `b` to its coordinates in
`c`. -/
@[simp]
theorem realCoordChange_intCast (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (l : Λ) :
    realCoordChange b c (fun i ↦ (b.repr l i : ℝ)) = fun j ↦ (c.repr l j : ℝ) := by
  have h := (Int.castRingHom ℝ).map_mulVec (c.toMatrix b) (b.repr l)
  rw [toMatrix_mulVec_repr] at h
  ext j
  simpa [realCoordChange_apply, Function.comp_def] using (h j).symm

/-- The real coordinate change from a basis to itself is the identity. -/
@[simp]
theorem realCoordChange_refl (b : Basis ι ℤ Λ) :
    realCoordChange b b = LinearEquiv.refl ℝ (ι → ℝ) := by
  classical
  ext x : 1
  simp [realCoordChange_apply]

/-- Successive real coordinate changes compose. -/
@[simp]
theorem realCoordChange_trans (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (d : Basis η ℤ Λ) :
    (realCoordChange b c).trans (realCoordChange c d) = realCoordChange b d := by
  ext x : 1
  simp only [LinearEquiv.trans_apply, realCoordChange_apply, Matrix.mulVec_mulVec,
    ← Matrix.map_mul, toMatrix_mul_toMatrix]

/-- Successive real coordinate changes compose, applied to a point. Together with
`Module.Basis.realCoordChange_refl`, this collapses round trips `b → c → b`. -/
@[simp]
theorem realCoordChange_realCoordChange (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (d : Basis η ℤ Λ)
    (x : ι → ℝ) : realCoordChange c d (realCoordChange b c x) = realCoordChange b d x := by
  rw [← LinearEquiv.trans_apply, realCoordChange_trans]

/-- Reversing the two bases inverts the real coordinate change. -/
@[simp]
theorem realCoordChange_symm (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    (realCoordChange b c).symm = realCoordChange c b := by
  ext x : 1
  rw [LinearEquiv.symm_apply_eq]
  simp

/-- The real coordinate change carries the standard lattice `ℤ^ι` into `ℤ^κ`. -/
private theorem realCoordChange_mem_span_basisFun (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ)
    {x : ι → ℝ} (hx : x ∈ span ℤ (range (Pi.basisFun ℝ ι))) :
    realCoordChange b c x ∈ span ℤ (range (Pi.basisFun ℝ κ)) := by
  obtain ⟨l, rfl⟩ := (mem_span_basisFun_iff b).1 hx
  exact (mem_span_basisFun_iff c).2 ⟨l, (realCoordChange_intCast b c l).symm⟩

/-- The real coordinate change carries the standard lattice `ℤ^ι` onto `ℤ^κ`. -/
theorem map_realCoordChange_span_basisFun (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    (span ℤ (range (Pi.basisFun ℝ ι))).map
        ((realCoordChange b c).restrictScalars ℤ : (ι → ℝ) →ₗ[ℤ] κ → ℝ) =
      span ℤ (range (Pi.basisFun ℝ κ)) := by
  refine le_antisymm (map_le_iff_le_comap.2 fun x hx ↦ realCoordChange_mem_span_basisFun b c hx)
    fun x hx ↦ ⟨realCoordChange c b x, realCoordChange_mem_span_basisFun c b hx, ?_⟩
  simp

variable {n : ℕ∞ω}

/-- The real coordinate change is smooth. -/
theorem contDiff_realCoordChange (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    ContDiff ℝ n (realCoordChange b c) :=
  (realCoordChange b c).toContinuousLinearEquiv.contDiff

/-- The `C^n` diffeomorphism of standard tori `ℝ^ι/ℤ^ι ≃ ℝ^κ/ℤ^κ` induced by the real coordinate
change `Module.Basis.realCoordChange b c`, for the quotient manifold structures on the orbit spaces
of translation by the standard lattices. As a map it is the additive equivalence
`Submodule.orbitRelQuotientCongr` induced by the coordinate change
(`Module.Basis.coe_torusCoordChange`), and its inverse is the change from `c` to `b`
(`Module.Basis.torusCoordChange_symm`). -/
noncomputable def torusCoordChange (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    Diffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ)
      (AddAction.orbitRel.Quotient (span ℤ (range (Pi.basisFun ℝ ι))) (ι → ℝ))
      (AddAction.orbitRel.Quotient (span ℤ (range (Pi.basisFun ℝ κ))) (κ → ℝ)) n :=
  (span ℤ (range (Pi.basisFun ℝ ι))).orbitRelQuotientDiffeomorph _
    ((realCoordChange b c).restrictScalars ℤ) (map_realCoordChange_span_basisFun b c)
    -- Restricting scalars to `ℤ` does not change the underlying maps.
    (contDiff_realCoordChange b c)
    (by
      have h := contDiff_realCoordChange (n := n) c b
      rw [← realCoordChange_symm] at h
      exact h)

/-- As a map, the diffeomorphism of standard tori is the additive equivalence
`Submodule.orbitRelQuotientCongr` induced by the real coordinate change. -/
theorem coe_torusCoordChange (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    ⇑(torusCoordChange b c (n := n)) = (span ℤ (range (Pi.basisFun ℝ ι))).orbitRelQuotientCongr _
      ((realCoordChange b c).restrictScalars ℤ) (map_realCoordChange_span_basisFun b c) :=
  Submodule.coe_orbitRelQuotientDiffeomorph ..

/-- The diffeomorphism of standard tori sends the class of `x` to the class of the real
coordinate change of `x`. -/
@[simp]
theorem torusCoordChange_mk (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (x : ι → ℝ) :
    torusCoordChange b c (n := n) (Quotient.mk _ x) = Quotient.mk _ (realCoordChange b c x) := by
  rw [coe_torusCoordChange, Submodule.orbitRelQuotientCongr_mk, LinearEquiv.restrictScalars_apply]

/-- The change of coordinates from a basis to itself is the identity of the standard torus. -/
@[simp]
theorem torusCoordChange_refl (b : Basis ι ℤ Λ) :
    torusCoordChange b b (n := n) = Diffeomorph.refl _ _ n := by
  ext z
  induction z using Quotient.inductionOn with | h x => ?_
  simp

/-- Successive changes of coordinates of standard tori compose, applied to a point. Together with
`Module.Basis.torusCoordChange_refl`, this collapses round trips `b → c → b`. -/
@[simp]
theorem torusCoordChange_torusCoordChange (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (d : Basis η ℤ Λ)
    (z : AddAction.orbitRel.Quotient (span ℤ (range (Pi.basisFun ℝ ι))) (ι → ℝ)) :
    torusCoordChange c d (n := n) (torusCoordChange b c (n := n) z) =
      torusCoordChange b d (n := n) z := by
  induction z using Quotient.inductionOn with | h x => ?_
  simp

/-- Successive changes of coordinates of standard tori compose. -/
@[simp]
theorem torusCoordChange_trans (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) (d : Basis η ℤ Λ) :
    (torusCoordChange b c (n := n)).trans (torusCoordChange c d) = torusCoordChange b d := by
  ext z
  rw [Diffeomorph.coe_trans, Function.comp_apply, torusCoordChange_torusCoordChange]

/-- The inverse of the diffeomorphism of standard tori is the change of coordinates from `c` to
`b`. -/
@[simp]
theorem torusCoordChange_symm (b : Basis ι ℤ Λ) (c : Basis κ ℤ Λ) :
    (torusCoordChange b c (n := n)).symm = torusCoordChange c b := by
  ext z
  rw [← Diffeomorph.toEquiv_coe_symm, Equiv.symm_apply_eq]
  simp

end Module.Basis
