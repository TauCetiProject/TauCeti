/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.OrthogonalGroup
public import TauCeti.LinearAlgebra.IntegralLattice.Dual.Scaling

/-!
# Discriminant forms of rescaled unimodular lattices

Let `L` be a unimodular integral lattice and `n` a nonzero integer. The rescaled lattice `n L`
has the same carrier as `L` and the form multiplied by `n`, so its dual carrier is
`n⁻¹ Lᵛ = n⁻¹ L`. Multiplication by `n` therefore identifies its discriminant group with the
reduction of `L` modulo `n`:

```text
A_(nL) = n⁻¹ L / L ≃ L / n L,    n⁻¹ y + L ↦ y + n L.
```

Under this identification the discriminant pairing of `n L` is `([y], [z]) ↦ B(y, z) / n mod ℤ`,
and, when `n L` is even, its half-norm discriminant form is `[y] ↦ B(y, y) / (2n) mod ℤ`. An
isometry of unimodular lattices is also an isometry of their rescalings, and its action on the
discriminant groups is its reduction modulo `n`. In particular the discriminant kernel of `n L`
consists of the isometries of `L` in its principal congruence subgroup of level `n`.

For `n = 2` the rescaled lattice `M(2)` of a unimodular lattice `M` is always even
(`TauCeti.IntegralLattice.isEven_smul_of_even`), and these
statements identify its discriminant form with the `𝔽₂`-space `M / 2M` carrying the quadratic
form `[x] ↦ (x, x) / 4 mod ℤ`, on which `O(M)` acts by reduction modulo two.

## Main declarations

* `TauCeti.IntegralLattice.IsUnimodular.discriminantGroupScaleEquiv`: the equivalence
  `A_(nL) ≃ L / nL` for unimodular `L` and `n ≠ 0`, characterized by
  `TauCeti.IntegralLattice.IsUnimodular.discriminantGroupScaleEquiv_mk_eq_mk_of_coe_eq`.
* `TauCeti.IntegralLattice.IsUnimodular.discriminantPairing_discriminantGroupScaleEquiv_symm_mk`:
  the discriminant pairing of `n L` is `B(y, z) / n mod ℤ`.
* its half-norm discriminant form is `B(y, y) / (2n) mod ℤ`:
`TauCeti.IntegralLattice.IsUnimodular.discriminantQuadraticMap_discriminantGroupScaleEquiv_symm_mk`
* `TauCeti.IntegralLattice.Isometry.discriminantGroupScaleEquiv_discriminantGroupEquiv_smul`:
  the rescaled isometry acts on discriminant groups as the reduction modulo `n` of the
  isometry, with the self-isometry case
  `TauCeti.IntegralLattice.Isometry.discriminantGroupScaleEquiv_discriminantGroupHom_smul`.
* `TauCeti.IntegralLattice.Isometry.smul_mem_discriminantKernel_iff`: a rescaled isometry lies in
  the discriminant kernel of `n L` exactly when the isometry lies in the congruence subgroup of
  level `n` of `L`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.
* V. Gritsenko and K. Hulek, *Moduli of polarized Enriques surfaces*, §2.
-/

public section

open Module
open scoped Pointwise

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

namespace IsUnimodular

/-- For unimodular `L`, multiplication by `n` identifies the dual carrier of `n L` with the
carrier of `L`. -/
private noncomputable def dualCarrierScaleEquivCarrier (hL : L.IsUnimodular) {n : ℤ}
    (hn : n ≠ 0) : (n • L).dualCarrier ≃ₗ[ℤ] L :=
  (L.dualCarrierScaleEquiv hn).trans (LinearEquiv.ofEq _ _ (L.isUnimodular_def.mp hL).symm)

private theorem coe_dualCarrierScaleEquivCarrier_apply (hL : L.IsUnimodular) {n : ℤ}
    (hn : n ≠ 0) (x : (n • L).dualCarrier) :
    (hL.dualCarrierScaleEquivCarrier hn x : V) = (n : ℚ) • (x : V) := by
  rw [dualCarrierScaleEquivCarrier, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    coe_dualCarrierScaleEquiv_apply]

private theorem coe_dualCarrierScaleEquivCarrier_symm_apply (hL : L.IsUnimodular) {n : ℤ}
    (hn : n ≠ 0) (y : L) :
    (((hL.dualCarrierScaleEquivCarrier hn).symm y : (n • L).dualCarrier) : V) =
      (n : ℚ)⁻¹ • (y : V) :=
  coe_dualCarrierScaleEquiv_symm_apply hn L _

/-- Multiplication by `n` carries the copy of the carrier inside the dual carrier of `n L` onto
`n L ⊆ L`, the submodule by which `L / n L` is formed. -/
private theorem map_carrierInDual_dualCarrierScaleEquivCarrier (hL : L.IsUnimodular) {n : ℤ}
    (hn : n ≠ 0) :
    (n • L).carrierInDual.map (hL.dualCarrierScaleEquivCarrier hn).toLinearMap =
      n • (⊤ : Submodule ℤ L) := by
  have hn' : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  ext y
  rw [Submodule.mem_map_equiv, mem_carrierInDual_iff, Submodule.mem_smul_pointwise_iff_exists,
    hL.coe_dualCarrierScaleEquivCarrier_symm_apply hn]
  constructor
  · intro hy
    refine ⟨⟨_, hy⟩, Submodule.mem_top, Subtype.ext ?_⟩
    rw [Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, smul_inv_smul₀ hn']
  · rintro ⟨z, -, rfl⟩
    rw [Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, inv_smul_smul₀ hn']
    exact z.property

/-- **The discriminant group of a rescaled unimodular lattice.** For a unimodular lattice `L`
and a nonzero integer `n`, multiplication by `n` identifies the discriminant group
`A_(nL) = n⁻¹ L / L` of the rescaled lattice with `L / n L`. -/
noncomputable def discriminantGroupScaleEquiv (hL : L.IsUnimodular) {n : ℤ} (hn : n ≠ 0) :
    (n • L).DiscriminantGroup ≃ₗ[ℤ] QuotSMulTop n L :=
  Submodule.Quotient.equiv _ _ (hL.dualCarrierScaleEquivCarrier hn)
    (hL.map_carrierInDual_dualCarrierScaleEquivCarrier hn)

/-- The class of a dual vector `x` of `n L` corresponds to the class of `y = n • x` in
`L / n L`. -/
theorem discriminantGroupScaleEquiv_mk_eq_mk_of_coe_eq (hL : L.IsUnimodular) {n : ℤ}
    (hn : n ≠ 0) {x : (n • L).dualCarrier} {y : L} (h : (y : V) = (n : ℚ) • (x : V)) :
    hL.discriminantGroupScaleEquiv hn (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  rw [discriminantGroupScaleEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext ((hL.coe_dualCarrierScaleEquivCarrier_apply hn x).trans h.symm))

/-- The inverse equivalence sends the class of `y` in `L / n L` to the class of any dual vector
`x` of `n L` with `n • x = y`, namely `x = n⁻¹ • y`. -/
theorem discriminantGroupScaleEquiv_symm_mk_eq_mk_of_coe_eq (hL : L.IsUnimodular) {n : ℤ}
    (hn : n ≠ 0) {x : (n • L).dualCarrier} {y : L} (h : (y : V) = (n : ℚ) • (x : V)) :
    (hL.discriminantGroupScaleEquiv hn).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk x := by
  rw [LinearEquiv.symm_apply_eq, hL.discriminantGroupScaleEquiv_mk_eq_mk_of_coe_eq hn h]

/-- Every class of `L / n L` is the image of the class of the dual vector `n⁻¹ • y` of `n L`. -/
private theorem exists_discriminantGroupScaleEquiv_symm_mk (hL : L.IsUnimodular) {n : ℤ}
    (hn : n ≠ 0) (y : L) :
    ∃ x : (n • L).dualCarrier, (x : V) = (n : ℚ)⁻¹ • (y : V) ∧
      (hL.discriminantGroupScaleEquiv hn).symm (Submodule.Quotient.mk y) =
        Submodule.Quotient.mk x := by
  refine ⟨(hL.dualCarrierScaleEquivCarrier hn).symm y,
    hL.coe_dualCarrierScaleEquivCarrier_symm_apply hn y,
    hL.discriminantGroupScaleEquiv_symm_mk_eq_mk_of_coe_eq hn ?_⟩
  rw [← hL.coe_dualCarrierScaleEquivCarrier_apply hn, LinearEquiv.apply_symm_apply]

/-- **The discriminant pairing of a rescaled unimodular lattice.** Under
`A_(nL) ≃ L / n L`, the discriminant pairing of `n L` is `([y], [z]) ↦ B(y, z) / n mod ℤ`. -/
theorem discriminantPairing_discriminantGroupScaleEquiv_symm_mk (hL : L.IsUnimodular) {n : ℤ}
    (hn : n ≠ 0) (y z : L) :
    (n • L).discriminantPairing
        ((hL.discriminantGroupScaleEquiv hn).symm (Submodule.Quotient.mk y))
        ((hL.discriminantGroupScaleEquiv hn).symm (Submodule.Quotient.mk z)) =
      ((L.form y z / n : ℚ) : AddCircle (1 : ℚ)) := by
  have hn' : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  obtain ⟨x, hx, hxy⟩ := hL.exists_discriminantGroupScaleEquiv_symm_mk hn y
  obtain ⟨x', hx', hxz⟩ := hL.exists_discriminantGroupScaleEquiv_symm_mk hn z
  rw [hxy, hxz, discriminantPairing_mk, smul_form, hx, hx']
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  congr 1
  field_simp

/-- **The discriminant form of a rescaled unimodular lattice.** When `n L` is even, under
`A_(nL) ≃ L / n L` its half-norm discriminant form is `[y] ↦ B(y, y) / (2n) mod ℤ`. -/
theorem discriminantQuadraticMap_discriminantGroupScaleEquiv_symm_mk (hL : L.IsUnimodular)
    {n : ℤ} (hn : n ≠ 0) (hnL : (n • L).IsEven) (y : L) :
    (n • L).discriminantQuadraticMap hnL
        ((hL.discriminantGroupScaleEquiv hn).symm (Submodule.Quotient.mk y)) =
      ((L.form y y / (2 * n) : ℚ) : AddCircle (1 : ℚ)) := by
  have hn' : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  obtain ⟨x, hx, hxy⟩ := hL.exists_discriminantGroupScaleEquiv_symm_mk hn y
  rw [hxy, discriminantQuadraticMap_mk, smul_form, hx]
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  congr 1
  field_simp

end IsUnimodular

namespace Isometry

variable {W : Type v} [AddCommGroup W] [Module ℚ W] {M : IntegralLattice W}

/-- **Isometries act on rescaled discriminant groups by reduction.** An isometry `e : L ≅ M` of
unimodular lattices is an isometry of the rescalings `n L ≅ n M`, and under
`A_(nL) ≃ L / n L` and `A_(nM) ≃ M / n M` its action on discriminant groups is the reduction of
`e` modulo `n`. -/
theorem discriminantGroupScaleEquiv_discriminantGroupEquiv_smul (e : Isometry L M)
    (hL : L.IsUnimodular) {n : ℤ} (hn : n ≠ 0) (a : (n • L).DiscriminantGroup) :
    (e.isUnimodular_iff.mp hL).discriminantGroupScaleEquiv hn
        ((e.smul n).discriminantGroupEquiv a) =
      QuotSMulTop.map n (e.carrierEquiv : L →ₗ[ℤ] M) (hL.discriminantGroupScaleEquiv hn a) := by
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    rw [discriminantGroupEquiv_mk,
      hL.discriminantGroupScaleEquiv_mk_eq_mk_of_coe_eq hn
        (hL.coe_dualCarrierScaleEquivCarrier_apply hn x),
      QuotSMulTop.map_apply_mk]
    refine IsUnimodular.discriminantGroupScaleEquiv_mk_eq_mk_of_coe_eq _ hn ?_
    rw [LinearEquiv.coe_coe, coe_carrierEquiv_apply, coe_dualCarrierEquiv_apply, smul_apply,
      hL.coe_dualCarrierScaleEquivCarrier_apply hn, map_smul]

/-- **Self-isometries act on rescaled discriminant groups by reduction.** For a unimodular
lattice `L` and `g ∈ O(L)`, viewed in `O(n L)`, the action of `g` on `A_(nL) ≃ L / n L` is the
reduction of `g` modulo `n`. -/
theorem discriminantGroupScaleEquiv_discriminantGroupHom_smul (g : Isometry L L)
    (hL : L.IsUnimodular) {n : ℤ} (hn : n ≠ 0) (a : (n • L).DiscriminantGroup) :
    hL.discriminantGroupScaleEquiv hn (discriminantGroupHom (n • L) (g.smul n) a) =
      reductionHom L n g (hL.discriminantGroupScaleEquiv hn a) := by
  rw [discriminantGroupHom_apply, reductionHom_apply]
  exact g.discriminantGroupScaleEquiv_discriminantGroupEquiv_smul hL hn a

/-- **The discriminant kernel of a rescaled unimodular lattice.** For unimodular `L` and `n ≠ 0`,
a self-isometry `g` of `L` acts trivially on the discriminant group of `n L` exactly when it acts
trivially on `L / n L`. -/
theorem smul_mem_discriminantKernel_iff (hL : L.IsUnimodular) {n : ℤ} (hn : n ≠ 0)
    {g : Isometry L L} :
    g.smul n ∈ discriminantKernel (n • L) ↔ g ∈ congruenceSubgroup L n := by
  let φ := hL.discriminantGroupScaleEquiv hn
  rw [← ker_discriminantGroupHom, ← ker_reductionHom, MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hg
    refine LinearMap.ext fun c ↦ ?_
    rw [one_apply_eq_self, ← φ.apply_symm_apply c,
      ← g.discriminantGroupScaleEquiv_discriminantGroupHom_smul hL hn, hg, one_apply_eq_self]
  · intro hg
    refine LinearEquiv.ext fun a ↦ φ.injective ?_
    rw [g.discriminantGroupScaleEquiv_discriminantGroupHom_smul hL hn, hg, one_apply_eq_self,
      one_apply_eq_self]

end Isometry

end TauCeti.IntegralLattice
