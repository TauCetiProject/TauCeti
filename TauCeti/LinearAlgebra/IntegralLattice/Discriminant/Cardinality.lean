/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group
public import TauCeti.LinearAlgebra.IntegralLattice.Gram

/-!
# Cardinality of an integral lattice's discriminant group

For a nondegenerate integral lattice `L`, the order of its discriminant group is the absolute
value of any Gram determinant:

```text
#(Lᵛ / L) = |det Gram(L)|.
```

The proof uses Mathlib's quotient-cardinality theorem for full-rank free `ℤ`-submodules.  Given
a carrier basis `b`, the corresponding bilinear dual basis is a basis of `Lᵛ`, while `b` itself
gives a basis of the copy of `L` inside `Lᵛ`.  The change-of-basis matrix between them is the
Gram matrix of `b`: the coefficient of `b j` along the dual vector indexed by `i` is
`B(b j, b i)`, which equals `B(b i, b j)` by symmetry.

## Main results

* `TauCeti.IntegralLattice.dualCarrierBasis_toMatrix_carrierInDualBasis`: the associated
  change-of-basis matrix is the Gram matrix.
* `TauCeti.IntegralLattice.natCard_discriminantGroup_eq_natAbs_gramDet`: the basis-relative
  cardinality formula.
* `TauCeti.IntegralLattice.natCard_discriminantGroup`: the discriminant-group cardinality is the
  lattice discriminant.
* `TauCeti.IntegralLattice.natCard_discriminantGroup_ofGramMatrix`: the formula for a lattice
  constructed from a nonsingular integral symmetric matrix.
* `TauCeti.IntegralLattice.inv_smul_mem_carrier_of_forall_dvd`: for `p` prime to `det L`, a vector
  pairing into `pℤ` with all of `L` lies in `p L`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md` (Layer 2).
* `TauCetiRoadmap/IntegralLattices/Suggested.lean`.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

open Classical in
/-- The change-of-basis matrix from the dual basis to the embedded carrier basis is the Gram
matrix. -/
theorem dualCarrierBasis_toMatrix_carrierInDualBasis (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Finite ι]
    (b : Basis ι ℤ L) :
    (L.dualCarrierBasis b).toMatrix
        ((↑) ∘ L.carrierInDualBasis b) = L.gramMatrix b := by
  ext i j
  rw [Basis.toMatrix_apply]
  apply Int.cast_injective (α := ℚ)
  rw [L.intCast_gramMatrix_apply]
  simp only [L.dualCarrierBasis_repr, Function.comp_apply, Basis.dualBasis_repr,
    L.dualPairingEquiv_cast, coe_carrierInDualBasis_apply]
  exact L.isSymm.eq _ _

open Classical in
/-- The determinant of the carrier basis inside the dual basis is the signed Gram determinant. -/
theorem dualCarrierBasis_det_carrierInDualBasis (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) :
    (L.dualCarrierBasis b).det ((↑) ∘ L.carrierInDualBasis b) = L.gramDet b := by
  rw [Basis.det_apply, L.dualCarrierBasis_toMatrix_carrierInDualBasis b, L.gramDet_def]

open Classical in
/-- The discriminant group has cardinality equal to the absolute value of the Gram determinant in
any carrier basis. -/
theorem natCard_discriminantGroup_eq_natAbs_gramDet (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) :
    Nat.card L.DiscriminantGroup = (L.gramDet b).natAbs := by
  rw [← L.dualCarrierBasis_det_carrierInDualBasis b]
  exact (Submodule.natAbs_det_basis_change (L.dualCarrierBasis b) L.carrierInDual
    (L.carrierInDualBasis b)).symm

/-- **The order of the discriminant group is the lattice discriminant.** -/
theorem natCard_discriminantGroup (L : IntegralLattice V) [L.IsNondegenerate] :
    Nat.card L.DiscriminantGroup = L.discriminant := by
  classical
  rw [L.natCard_discriminantGroup_eq_natAbs_gramDet (Module.Free.chooseBasis ℤ L),
    L.discriminant_eq_natAbs_gramDet (Module.Free.chooseBasis ℤ L)]

/-- **Vectors pairing into `pℤ` are divisible by `p`** when `p` is prime to the discriminant: if
`p` divides the pairing of `v` with every lattice vector, then `v / p` lies in `L`. -/
theorem inv_smul_mem_carrier_of_forall_dvd (L : IntegralLattice V) [L.IsNondegenerate] {p : ℕ}
    [NeZero p] (hp : p.Coprime L.discriminant) {v : L}
    (hv : ∀ w : L, (p : ℤ) ∣ L.integralForm v w) :
    (p : ℚ)⁻¹ • (v : V) ∈ L.carrier := by
  have hp₀ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  -- The vector `v / p` lies in the dual lattice, and its class in the discriminant group has
  -- order dividing both `p` and the order `|det L|` of that group.
  have hdual : (p : ℚ)⁻¹ • (v : V) ∈ L.dualCarrier := by
    rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    obtain ⟨k, hk⟩ := hv ⟨y, hy⟩
    refine Submodule.mem_one.mpr ⟨k, ?_⟩
    rw [eq_intCast, map_smul, LinearMap.smul_apply, smul_eq_mul, ← L.integralForm_cast v ⟨y, hy⟩,
      hk]
    push_cast
    field_simp
  set x : L.DiscriminantGroup := Submodule.Quotient.mk ⟨_, hdual⟩
  have hpx : p • x = 0 := by
    rw [← Submodule.Quotient.mk_smul, discriminantGroup_mk_eq_zero_iff,
      Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℚ]
    simpa only [smul_smul, mul_inv_cancel₀ hp₀, one_smul] using v.2
  have horder : addOrderOf x = 1 := Nat.eq_one_of_dvd_coprimes hp
    (addOrderOf_dvd_of_nsmul_eq_zero hpx)
    ((addOrderOf_dvd_natCard x).trans (L.natCard_discriminantGroup).dvd)
  exact (L.discriminantGroup_mk_eq_zero_iff _).mp (AddMonoid.addOrderOf_eq_one_iff.mp horder)

open Classical in
/-- The discriminant group of a lattice constructed from a nonsingular integral symmetric matrix
has cardinality equal to the absolute value of that matrix's determinant. -/
@[simp]
theorem natCard_discriminantGroup_ofGramMatrix {ι : Type v} [Fintype ι]
    (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    Nat.card (ofGramMatrix b G hG).DiscriminantGroup = G.det.natAbs := by
  have : (ofGramMatrix b G hG).IsNondegenerate :=
    isNondegenerate_ofGramMatrix b G hG hdet
  rw [natCard_discriminantGroup, discriminant_ofGramMatrix]

end TauCeti.IntegralLattice
