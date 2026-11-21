/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Topology
public import TauCeti.Algebra.AlgebraicGroup.NormTorus.Complex
public import TauCeti.Topology.Algebra.PointTopology.WeilRestriction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Algebra.HopfAlgebra.Antipode
import TauCeti.Analysis.Complex.Circle

/-!
# The Deligne torus

The **Deligne torus** is the real algebraic group `S = Res_{ℂ/ℝ} 𝔾ₘ`, the Weil restriction of the
multiplicative group of `ℂ`. Here it is the commutative Hopf `ℝ`-algebra
`TauCeti.DeligneTorus.S := WeilRestriction ℝ ℂ ℂ[T;T⁻¹]`. Its points over a commutative
`ℝ`-algebra `R` are the units of `ℂ ⊗[ℝ] R` (`TauCeti.DeligneTorus.pointsMulEquiv`), and its real
points are `ℂˣ` (`TauCeti.DeligneTorus.realPointsMulEquiv`), homeomorphically for the point
topology (`TauCeti.DeligneTorus.isHomeomorph_realPointsMulEquiv`).

It carries the homomorphisms pinned in Milne's conventions for Hodge structures, both as bialgebra
maps of coordinate Hopf algebras and on points:

* the diagonal `d : 𝔾ₘ → S`, `r ↦ 1 ⊗ r`, which on real points is the inclusion `ℝˣ → ℂˣ`
  (`TauCeti.Algebra.WeilRestriction.multiplicativeGroupDiagonal ℝ ℂ`,
  `TauCeti.DeligneTorus.diagonal`);
* the weight `w = d ∘ inv`, `r ↦ r⁻¹`
  (`TauCeti.DeligneTorus.weightBialgHom`, `TauCeti.DeligneTorus.weight`);
* the norm `Nm : S → 𝔾ₘ`, the norm of `ℂ/ℝ`
  (`TauCeti.NormTorus.normBialgHom ℝ ℂ`, `TauCeti.DeligneTorus.norm`), which on real points is
  `z ↦ z * conj z = |z|²`, so that `Nm ∘ d` is the squaring map and `Nm ∘ w` is `r ↦ r⁻²`.

## Main definitions

* `TauCeti.DeligneTorus.S`: the coordinate Hopf algebra of the Deligne torus.
* `TauCeti.DeligneTorus.pointsMulEquiv`: `S(R) ≃* (ℂ ⊗[ℝ] R)ˣ`.
* `TauCeti.DeligneTorus.realPointsMulEquiv`: `S(ℝ) ≃* ℂˣ`.
* `TauCeti.DeligneTorus.weightBialgHom`: the weight as a bialgebra homomorphism of coordinate Hopf
  algebras (alongside `TauCeti.Algebra.WeilRestriction.multiplicativeGroupDiagonal ℝ ℂ` and
  `TauCeti.NormTorus.normBialgHom ℝ ℂ`).
* `TauCeti.DeligneTorus.diagonal`, `TauCeti.DeligneTorus.weight`, `TauCeti.DeligneTorus.norm`: the
  diagonal, weight and norm on points.

## Main results

* `TauCeti.DeligneTorus.realPointsMulEquiv_apply`: the complex number attached to a real point is
  its value on the coordinate `T` of `𝔾ₘ`, read in `ℂ ⊗[ℝ] ℝ ≃ ℂ`.
* `TauCeti.DeligneTorus.isHomeomorph_realPointsMulEquiv`: `S(ℝ) ≃ ℂˣ` is a homeomorphism.
* `TauCeti.DeligneTorus.mapDomain_multiplicativeGroupDiagonal` and
  `TauCeti.DeligneTorus.mapDomain_weightBialgHom`: precomposition by the diagonal and weight
  bialgebra maps induces `diagonal` and `weight` on points over every commutative `ℝ`-algebra `R`
  (and `TauCeti.NormTorus.pointsMulEquiv_mapDomain_normBialgHom` induces `norm`).
* `TauCeti.DeligneTorus.pointsMulEquiv_mapValue`, `TauCeti.DeligneTorus.mapValue_diagonal`,
  `TauCeti.DeligneTorus.mapValue_weight`, `TauCeti.DeligneTorus.norm_mapValue`: the identification
  of points, the diagonal, the weight and the norm are natural in `R`.
* `TauCeti.DeligneTorus.norm_diagonal`, `TauCeti.DeligneTorus.norm_weight`: `Nm ∘ d` is `r ↦ r²`
  and `Nm ∘ w` is `r ↦ r⁻²`.
* `TauCeti.DeligneTorus.weight_eq_inv_diagonal`, `TauCeti.DeligneTorus.weight_two`: the weight is
  `r ↦ d(r)⁻¹`; for instance `w(2) = 1/2` in `ℂˣ`.
* `TauCeti.DeligneTorus.coe_norm_real`, `TauCeti.DeligneTorus.norm_real_eq_one_iff`,
  `TauCeti.DeligneTorus.isCompact_ker_norm_real`: on real points the norm is `Complex.normSq`, and
  its kernel is the compact unit circle `U(1)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, p. 26, displays (20)–(23).
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
-/

public section

open WithConv TauCeti.Algebra
open scoped LaurentPolynomial TensorProduct TauCeti.PointTopology

namespace TauCeti.DeligneTorus

/-- **The Deligne torus** `S = Res_{ℂ/ℝ} 𝔾ₘ`, as its coordinate Hopf `ℝ`-algebra, the Weil
restriction of the Laurent polynomials `ℂ[T, T⁻¹]`. -/
abbrev S : Type := WeilRestriction ℝ ℂ ℂ[T;T⁻¹]

variable (R : Type*) [CommRing R] [Algebra ℝ R]

/-- **The points of the Deligne torus.** For a commutative `ℝ`-algebra `R`, the points `S(R)` are
the units of `ℂ ⊗[ℝ] R`. -/
noncomputable def pointsMulEquiv : WithConv (S →ₐ[ℝ] R) ≃* (ℂ ⊗[ℝ] R)ˣ :=
  WeilRestriction.multiplicativeGroupPoints ℝ ℂ R

variable {R}

/-- The unit attached to a point of `S` is the value at the coordinate `T` of the point of `𝔾ₘ`
over `ℂ ⊗[ℝ] R` that it classifies. -/
@[simp]
theorem coe_pointsMulEquiv (f : WithConv (S →ₐ[ℝ] R)) :
    (pointsMulEquiv R f : ℂ ⊗[ℝ] R) =
      WeilRestriction.homEquiv ℝ ℂ ℂ[T;T⁻¹] R f.ofConv (LaurentPolynomial.T 1) :=
  WeilRestriction.multiplicativeGroupPoints_apply f

/-- The point of `S` attached to a unit `u` of `ℂ ⊗[ℝ] R` classifies evaluation of Laurent
polynomials at `u`. -/
@[simp]
theorem pointsMulEquiv_symm_apply (u : (ℂ ⊗[ℝ] R)ˣ) :
    ((pointsMulEquiv R).symm u).ofConv =
      (WeilRestriction.homEquiv ℝ ℂ ℂ[T;T⁻¹] R).symm (laurentEval u) :=
  WeilRestriction.multiplicativeGroupPoints_symm_apply u

/-- **Naturality of `pointsMulEquiv` in `R`**: post-composing a point with `h : R →ₐ[ℝ] R'`
corresponds to applying `ℂ ⊗ h` to units. -/
theorem pointsMulEquiv_mapValue {R' : Type*} [CommRing R'] [Algebra ℝ R'] (h : R →ₐ[ℝ] R')
    (f : WithConv (S →ₐ[ℝ] R)) :
    pointsMulEquiv R' (AlgHom.mapValue h f) =
      Units.map (Algebra.TensorProduct.lTensor (S := ℂ) ℂ h : ℂ ⊗[ℝ] R →* ℂ ⊗[ℝ] R')
        (pointsMulEquiv R f) := by
  rw [AlgHom.mapValue_apply]
  exact WeilRestriction.multiplicativeGroupPoints_naturality h f

/-- **The real points of the Deligne torus** are `ℂˣ`, through `ℂ ⊗[ℝ] ℝ ≃ ℂ`. -/
noncomputable def realPointsMulEquiv : WithConv (S →ₐ[ℝ] ℝ) ≃* ℂˣ :=
  (pointsMulEquiv ℝ).trans (Units.mapEquiv (Algebra.TensorProduct.rid ℝ ℝ ℂ).toMulEquiv)

/-- The complex number attached to a real point of `S` is its unit in `ℂ ⊗[ℝ] ℝ`, read in
`ℂ ⊗[ℝ] ℝ ≃ ℂ`. -/
theorem coe_realPointsMulEquiv (f : WithConv (S →ₐ[ℝ] ℝ)) :
    (realPointsMulEquiv f : ℂ) = Algebra.TensorProduct.rid ℝ ℝ ℂ (pointsMulEquiv ℝ f) := by
  simp [realPointsMulEquiv]

/-- The real point of `S` attached to `z : ℂˣ` is the unit `z ⊗ 1` of `ℂ ⊗[ℝ] ℝ`. -/
@[simp]
theorem pointsMulEquiv_realPointsMulEquiv_symm (z : ℂˣ) :
    pointsMulEquiv ℝ (realPointsMulEquiv.symm z) =
      Units.map ((Algebra.TensorProduct.rid ℝ ℝ ℂ).symm : ℂ →* ℂ ⊗[ℝ] ℝ) z := by
  ext
  simp [realPointsMulEquiv]

/-- The complex number attached to a real point of `S` is its value on the coordinate `T` of `𝔾ₘ`,
read in `ℂ ⊗[ℝ] ℝ ≃ ℂ`. -/
theorem realPointsMulEquiv_apply (f : WithConv (S →ₐ[ℝ] ℝ)) :
    (realPointsMulEquiv f : ℂ) = Algebra.TensorProduct.rid ℝ ℝ ℂ
      (WeilRestriction.homEquiv ℝ ℂ ℂ[T;T⁻¹] ℝ f.ofConv (LaurentPolynomial.T 1)) := by
  rw [coe_realPointsMulEquiv, coe_pointsMulEquiv]

/-- **`S(ℝ) ≃ ℂˣ` is a homeomorphism** for the point topology on `S(ℝ)` and the units topology on
`ℂˣ`. It is the Weil restriction comparison of point topologies followed by the identification of
the points of `𝔾ₘ` over `ℂ` with `ℂˣ`. -/
theorem isHomeomorph_realPointsMulEquiv : IsHomeomorph realPointsMulEquiv := by
  have := isModuleTopologyOfFiniteDimensional (𝕜 := ℝ) (E := ℂ)
  let h := (PointTopology.isHomeomorph_ofConv.homeomorph _).trans
    ((WeilRestriction.pointsHomeomorph ℝ ℂ ℂ[T;T⁻¹]).trans
      ((PointTopology.isHomeomorph_ofConv.homeomorph _).symm.trans
        (MultiplicativeGroup.pointsContinuousMulEquiv ℂ ℂ).toHomeomorph))
  have heq : ⇑realPointsMulEquiv = ⇑h := funext fun f => Units.ext <| by
    simp [h, realPointsMulEquiv_apply, Function.surjInv_eq, Algebra.TensorProduct.coe_rid]
  rw [heq]
  exact h.isHomeomorph

/-! ### The diagonal, the weight and the norm -/

variable (R)

/-- **The diagonal** `d : 𝔾ₘ → S` on points, `r ↦ 1 ⊗ r`. On real points it is the inclusion
`ℝˣ → ℂˣ` (`TauCeti.DeligneTorus.coe_realPointsMulEquiv_diagonal`). -/
noncomputable def diagonal : Rˣ →* WithConv (S →ₐ[ℝ] R) :=
  (pointsMulEquiv R).symm.toMonoidHom.comp
    (Units.map (Algebra.TensorProduct.includeRight : R →ₐ[ℝ] ℂ ⊗[ℝ] R).toMonoidHom)

/-- **The weight** `w = d ∘ inv : 𝔾ₘ → S` on points, `r ↦ 1 ⊗ r⁻¹`. -/
noncomputable def weight : Rˣ →* WithConv (S →ₐ[ℝ] R) :=
  (diagonal R).comp (MulEquiv.inv Rˣ).toMonoidHom

/-- **The norm** `Nm : S → 𝔾ₘ` on points, the norm of `ℂ ⊗[ℝ] R` over `R`. -/
noncomputable def norm : WithConv (S →ₐ[ℝ] R) →* Rˣ :=
  (NormTorus.norm ℝ ℂ R).comp (pointsMulEquiv R).toMonoidHom

variable {R}

@[simp]
theorem pointsMulEquiv_diagonal (r : Rˣ) :
    pointsMulEquiv R (diagonal R r) =
      Units.map (Algebra.TensorProduct.includeRight : R →ₐ[ℝ] ℂ ⊗[ℝ] R).toMonoidHom r := by
  simp [diagonal]

/-- The weight is `r ↦ d(r)⁻¹`, which pins its sign convention. -/
theorem weight_eq_inv_diagonal (r : Rˣ) : weight R r = (diagonal R r)⁻¹ := by
  simp [weight]

/-- The weight on points is `r ↦ (1 ⊗ r)⁻¹`. -/
@[simp]
theorem pointsMulEquiv_weight (r : Rˣ) :
    pointsMulEquiv R (weight R r) =
      (Units.map (Algebra.TensorProduct.includeRight : R →ₐ[ℝ] ℂ ⊗[ℝ] R).toMonoidHom r)⁻¹ := by
  rw [weight_eq_inv_diagonal, map_inv (pointsMulEquiv R), pointsMulEquiv_diagonal]

theorem norm_apply (f : WithConv (S →ₐ[ℝ] R)) :
    norm R f = NormTorus.norm ℝ ℂ R (pointsMulEquiv R f) :=
  (rfl)

/-- **Naturality of the diagonal in `R`**: post-composing `d(r)` with `h : R →ₐ[ℝ] R'` is
`d(h r)`. -/
theorem mapValue_diagonal {R' : Type*} [CommRing R'] [Algebra ℝ R'] (h : R →ₐ[ℝ] R')
    (r : Rˣ) : AlgHom.mapValue h (diagonal R r) = diagonal R' (Units.map (h : R →* R') r) := by
  apply (pointsMulEquiv R').injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_diagonal, pointsMulEquiv_diagonal]
  ext
  simp

/-- **Naturality of the weight in `R`**: post-composing `w(r)` with `h : R →ₐ[ℝ] R'` is
`w(h r)`. -/
theorem mapValue_weight {R' : Type*} [CommRing R'] [Algebra ℝ R'] (h : R →ₐ[ℝ] R')
    (r : Rˣ) : AlgHom.mapValue h (weight R r) = weight R' (Units.map (h : R →* R') r) := by
  apply (pointsMulEquiv R').injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_weight, pointsMulEquiv_weight]
  ext
  simp

/-- **Naturality of the norm in `R`**: the norm of a point post-composed with `h : R →ₐ[ℝ] R'`
is `h` applied to its norm. -/
theorem norm_mapValue {R' : Type*} [CommRing R'] [Algebra ℝ R'] (h : R →ₐ[ℝ] R')
    (f : WithConv (S →ₐ[ℝ] R)) :
    norm R' (AlgHom.mapValue h f) = Units.map (h : R →* R') (norm R f) := by
  rw [norm_apply, pointsMulEquiv_mapValue, NormTorus.norm_unitsMap_lTensor, norm_apply]

/-- **`Nm ∘ d` is the squaring map**: `Nm(d(r)) = r²`. -/
@[simp]
theorem norm_diagonal (r : Rˣ) : norm R (diagonal R r) = r ^ 2 := by
  rw [norm_apply, pointsMulEquiv_diagonal, ← Complex.finrank_real_complex]
  exact NormTorus.norm_unitsMap_includeRight r

/-- `Nm ∘ w` is `r ↦ r⁻²`. -/
@[simp]
theorem norm_weight (r : Rˣ) : norm R (weight R r) = (r ^ 2)⁻¹ := by
  rw [weight_eq_inv_diagonal, map_inv (norm R), norm_diagonal]

/-- On real points the diagonal is the inclusion `ℝˣ → ℂˣ`. -/
@[simp]
theorem coe_realPointsMulEquiv_diagonal (r : ℝˣ) :
    (realPointsMulEquiv (diagonal ℝ r) : ℂ) = (r : ℝ) := by
  simp [realPointsMulEquiv]

/-- On real points the weight is `r ↦ r⁻¹`. -/
@[simp]
theorem coe_realPointsMulEquiv_weight (r : ℝˣ) :
    (realPointsMulEquiv (weight ℝ r) : ℂ) = ((r : ℝ) : ℂ)⁻¹ := by
  rw [weight_eq_inv_diagonal, map_inv realPointsMulEquiv, Units.val_inv_eq_inv_val,
    coe_realPointsMulEquiv_diagonal]

/-- `w(2) = 1/2` in `S(ℝ) = ℂˣ`: the weight is `r ↦ r⁻¹`, not `r ↦ r`. -/
theorem weight_two : (realPointsMulEquiv (weight ℝ (Units.mk0 2 two_ne_zero)) : ℂ) = 1 / 2 := by
  rw [coe_realPointsMulEquiv_weight]
  norm_num

/-- On real points, read in `ℂ`, the norm is the squared modulus `z ↦ z * conj z`. -/
theorem coe_norm_real (f : WithConv (S →ₐ[ℝ] ℝ)) :
    (norm ℝ f : ℝ) = Complex.normSq (realPointsMulEquiv f) := by
  rw [norm_apply, NormTorus.coe_norm_complex, coe_realPointsMulEquiv]

/-- **The real points of the kernel of the norm are the unit circle `U(1)`.** -/
theorem norm_real_eq_one_iff (f : WithConv (S →ₐ[ℝ] ℝ)) :
    norm ℝ f = 1 ↔ ‖(realPointsMulEquiv f : ℂ)‖ = 1 := by
  rw [norm_apply, ← NormTorus.mem_normOne, coe_realPointsMulEquiv]
  exact NormTorus.mem_normOne_complex_iff

/-- **The real norm-one locus of the Deligne torus is compact** in the point topology, being the
homeomorphic preimage of the compact unit circle `U(1)` under `S(ℝ) ≃ ℂˣ`. -/
theorem isCompact_ker_norm_real : IsCompact {f : WithConv (S →ₐ[ℝ] ℝ) | norm ℝ f = 1} := by
  let e := isHomeomorph_realPointsMulEquiv.homeomorph
  have hrange : {f : WithConv (S →ₐ[ℝ] ℝ) | norm ℝ f = 1} =
      Set.range (fun z : Circle ↦ e.symm z.toUnits) := by
    ext f
    simp only [Set.mem_ofPred_eq, norm_real_eq_one_iff, Set.mem_range]
    exact ⟨fun hf ↦ ⟨⟨(realPointsMulEquiv f : ℂ), mem_sphere_zero_iff_norm.2 hf⟩,
        e.symm_apply_eq.2 (Units.ext rfl)⟩,
      fun ⟨z, hz⟩ ↦ hz ▸ by
        rw [← isHomeomorph_realPointsMulEquiv.homeomorph_apply, e.apply_symm_apply,
          Circle.toUnits_apply, Units.val_mk0, Circle.norm_coe]⟩
  rw [hrange]
  exact isCompact_range (e.continuous_symm.comp Circle.continuous_toUnits)

/-! ### Coordinate bialgebra homomorphisms -/

/-- **The weight `w = d ∘ inv : 𝔾ₘ → S`**, as a bialgebra homomorphism `S →ₐc[ℝ] ℝ[T;T⁻¹]` of
coordinate Hopf algebras, composing `WeilRestriction.multiplicativeGroupDiagonal ℝ ℂ` with the
antipode of `ℝ[T;T⁻¹]`. On points over `R` it induces `TauCeti.DeligneTorus.weight`
(`TauCeti.DeligneTorus.mapDomain_weightBialgHom`). -/
noncomputable def weightBialgHom : S →ₐc[ℝ] ℝ[T;T⁻¹] :=
  (HopfAlgebra.antipodeBialgHom (R := ℝ) (A := ℝ[T;T⁻¹])).comp
    (WeilRestriction.multiplicativeGroupDiagonal ℝ ℂ)

/-- Precomposing a point of `𝔾ₘ` over `R` with `WeilRestriction.multiplicativeGroupDiagonal ℝ ℂ`
gives `diagonal R` applied to the corresponding unit of `R`. -/
@[simp↓]
theorem mapDomain_multiplicativeGroupDiagonal (x : WithConv (ℝ[T;T⁻¹] →ₐ[ℝ] R)) :
    BialgHom.mapDomain (WeilRestriction.multiplicativeGroupDiagonal ℝ ℂ) x =
      diagonal R (MultiplicativeGroup.pointsMulEquiv x) := by
  apply (pointsMulEquiv R).injective
  rw [pointsMulEquiv_diagonal]
  exact WeilRestriction.multiplicativeGroupPoints_mapDomain_multiplicativeGroupDiagonal x

/-- Precomposing a point of `𝔾ₘ` over `R` with `weightBialgHom` gives `weight R` applied to the
corresponding unit of `R`. -/
@[simp↓]
theorem mapDomain_weightBialgHom (x : WithConv (ℝ[T;T⁻¹] →ₐ[ℝ] R)) :
    BialgHom.mapDomain weightBialgHom x = weight R (MultiplicativeGroup.pointsMulEquiv x) := by
  rw [weightBialgHom, BialgHom.mapDomain_comp, MonoidHom.comp_apply,
    BialgHom.mapDomain_antipodeBialgHom, map_inv, mapDomain_multiplicativeGroupDiagonal,
    weight_eq_inv_diagonal]

end TauCeti.DeligneTorus
