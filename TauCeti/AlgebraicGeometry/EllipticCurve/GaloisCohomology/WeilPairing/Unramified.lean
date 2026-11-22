/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Unramified
import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# Unramified local Tate duality for elliptic torsion and isogeny kernels

Let `K` be a finite extension of `ℚ_p` (`TauCeti.FinitePadicExtension K p`). Transporting Milne's
unramified local duality theorem (`TauCeti.ClassFieldTheory.unramifiedH1_eq_ker_compl₂_dualityMap1`)
along the Galois module isomorphisms given by the Weil pairing
(`WeierstrassCurve.torsionCoeffWeilDual_bijective`) and the isogeny Weil pairing
(`TauCeti.Isogeny.kerCoeffWeilDual_bijective`) yields exact unramified duality for elliptic
curves and isogenies when `p ∤ m` (respectively `p ∤ deg φ`): `H¹_ur(G_K, E[m])` is its own
exact annihilator under `W.localTateWeilPairing`, and `H¹_ur(G_K, E₁[φ])` and
`H¹_ur(G_K, E₂[φ̂])` are exact mutual annihilators under `φ.localTateKerWeilPairing`. (Over any
nonarchimedean local field, the general isotropy/orthogonality statements live in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/Orthogonality.lean`.)

Over a number field, combined with `TauCeti.Isogeny.range_kummerMap_eq_unramifiedKerCohomology`,
this identifies the local conditions of `Sel_φ` and `Sel_φ̂` at finite places away from `deg φ`
where the base-changed equations of both curves are integral over `𝒪[K_v]` with elliptic integral
models (unit discriminant) with a pair of exact mutual annihilators in
`H¹(G_{K_v}, E₁[φ]) × H¹(G_{K_v}, E₂[φ̂])`, as required by the Poitou–Tate / Greenberg–Wiles
comparison of Selmer groups in Cassels' theorem.

## Main results

* `WeierstrassCurve.unramifiedTorsionCohomology_eq_ker_compl₂_localTateWeilPairing` and
  `mem_unramifiedTorsionCohomology_iff_forall_localTateWeilPairing_eq_zero`: `H¹_ur(G_K, E[m])` is
  its own exact annihilator over a finite extension of `ℚ_p` when `p ∤ m`.
* `TauCeti.Isogeny.unramifiedKerCohomology_eq_ker_compl₂_localTateKerWeilPairing`,
  `unramifiedKerCohomology_dual_eq_ker_flip_compl₂_localTateKerWeilPairing`,
  `mem_unramifiedKerCohomology_iff_forall_localTateKerWeilPairing_eq_zero`, and
  `mem_unramifiedKerCohomology_dual_iff_forall_localTateKerWeilPairing_eq_zero`: exact mutual
  annihilation of `H¹_ur(G_K, E₁[φ])` and `H¹_ur(G_K, E₂[φ̂])` over a finite extension of `ℚ_p`
  when `p ∤ deg φ`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Theorem 2.6 and Proposition 3.8.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public noncomputable section

/-! ### Unramified self-duality for `E[m]` -/

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory

section Padic

variable (p : ℕ) [Fact p.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]
  (W : WeierstrassCurve K) [W.IsElliptic] {m : ℕ}

/-- **Pointwise unramified self-duality for `E[m]`.** Over a finite extension `K` of `ℚ_p` with
`p ∤ m`, a class in `H¹(G_K, E[m])` is unramified if and only if its local Tate pairing with every
unramified class in `H¹(G_K, E[m])` vanishes. -/
theorem mem_unramifiedTorsionCohomology_iff_forall_localTateWeilPairing_eq_zero
    (hpm : ¬ p ∣ m) (a : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    a ∈ W.unramifiedTorsionCohomology m ↔
      ∀ b ∈ W.unramifiedTorsionCohomology m,
        W.localTateWeilPairing m (FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpm) a b =
          0 := by
  have hm := FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpm
  have : NeZero m := hm.neZero_natCast
  simp only [unramifiedTorsionCohomology_eq_unramifiedH1]
  exact mem_unramifiedH1_iff_forall_pairing_eq_zero p hpm
    (fun P : W.TorsionCoeff m ↦ AddSubgroup.torsionBy.nsmul P)
    (W.torsionCoeffWeilDual m hm) (W.torsionCoeffWeilDual_bijective m hm)
    (explicitH2MuEquivZMod K hm).toAddMonoidHom
    (explicitH2MuEquivZMod K hm).injective
    (W.localTateWeilPairing m hm)
    (fun x y ↦ by rw [localTateWeilPairing_apply, torsionH1WeilPairing_eq_dualityMap1,
      AddEquiv.coe_toAddMonoidHom]) a

/-- **`H¹_ur(G_K, E[m])` is its own exact annihilator under `localTateWeilPairing`** over a finite
extension `K` of `ℚ_p` when `p ∤ m`. -/
theorem unramifiedTorsionCohomology_eq_ker_compl₂_localTateWeilPairing (hpm : ¬ p ∣ m) :
    W.unramifiedTorsionCohomology m =
      ((W.localTateWeilPairing m (FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpm)).compl₂
        (W.unramifiedTorsionCohomology m).subtype).ker := by
  ext a
  rw [AddMonoidHom.mem_ker_compl₂_subtype_iff]
  exact W.mem_unramifiedTorsionCohomology_iff_forall_localTateWeilPairing_eq_zero p hpm a

end Padic

end WeierstrassCurve

/-! ### Unramified mutual duality for `E₁[φ]` and `E₂[φ̂]` -/

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology TauCeti.ClassFieldTheory Hom

section Padic

variable (p : ℕ) [Fact p.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **Pointwise unramified duality for `E₁[φ]`.** Over a finite extension `K` of `ℚ_p` with
`p ∤ deg φ`, a class in `H¹(G_K, E₁[φ])` is unramified if and only if its local Tate pairing with
every unramified class in `H¹(G_K, E₂[φ̂])` vanishes. -/
theorem mem_unramifiedKerCohomology_iff_forall_localTateKerWeilPairing_eq_zero
    (hpn : ¬ p ∣ φ.degree) (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    a ∈ φ.unramifiedKerCohomology ↔
      ∀ b ∈ φ.dual.unramifiedKerCohomology,
        φ.localTateKerWeilPairing (FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpn) a b =
          0 := by
  have hn := FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpn
  have : NeZero φ.degree := hn.neZero_natCast
  simp only [unramifiedKerCohomology_eq_unramifiedH1]
  exact mem_unramifiedH1_iff_forall_pairing_eq_zero p hpn
    φ.degree_nsmul_kerCoeff_eq_zero (φ.kerCoeffWeilDual hn) (φ.kerCoeffWeilDual_bijective hn)
    (explicitH2MuEquivZMod K hn).toAddMonoidHom
    (explicitH2MuEquivZMod K hn).injective
    (φ.localTateKerWeilPairing hn)
    (fun x y ↦ by rw [localTateKerWeilPairing_apply, kerH1WeilPairing_eq_dualityMap1,
      AddEquiv.coe_toAddMonoidHom]) a

/-- **`H¹_ur(G_K, E₁[φ])` is the exact left annihilator of `H¹_ur(G_K, E₂[φ̂])`** under
`localTateKerWeilPairing` over a finite extension `K` of `ℚ_p` when `p ∤ deg φ`. -/
theorem unramifiedKerCohomology_eq_ker_compl₂_localTateKerWeilPairing (hpn : ¬ p ∣ φ.degree) :
    φ.unramifiedKerCohomology =
      ((φ.localTateKerWeilPairing (FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpn)).compl₂
        φ.dual.unramifiedKerCohomology.subtype).ker := by
  ext a
  rw [AddMonoidHom.mem_ker_compl₂_subtype_iff]
  exact φ.mem_unramifiedKerCohomology_iff_forall_localTateKerWeilPairing_eq_zero p hpn a

/-- **Pointwise unramified duality for `E₂[φ̂]`.** Over a finite extension `K` of `ℚ_p` with
`p ∤ deg φ`, a class in `H¹(G_K, E₂[φ̂])` is unramified if and only if every unramified class in
`H¹(G_K, E₁[φ])` pairs to zero with it under `localTateKerWeilPairing`. -/
theorem mem_unramifiedKerCohomology_dual_iff_forall_localTateKerWeilPairing_eq_zero
    (hpn : ¬ p ∣ φ.degree) (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    b ∈ φ.dual.unramifiedKerCohomology ↔
      ∀ a ∈ φ.unramifiedKerCohomology,
        φ.localTateKerWeilPairing (FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpn) a b =
          0 := by
  have hn := FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpn
  have : NeZero φ.degree := hn.neZero_natCast
  simp only [unramifiedKerCohomology_eq_unramifiedH1]
  exact mem_unramifiedH1_right_iff_forall_pairing_eq_zero p hpn
    φ.degree_nsmul_kerCoeff_eq_zero (φ.kerCoeffWeilDual hn) (φ.kerCoeffWeilDual_bijective hn)
    (explicitH2MuEquivZMod K hn).toAddMonoidHom
    (explicitH2MuEquivZMod K hn).injective
    (φ.localTateKerWeilPairing hn)
    (fun x y ↦ by rw [localTateKerWeilPairing_apply, kerH1WeilPairing_eq_dualityMap1,
      AddEquiv.coe_toAddMonoidHom]) b

/-- **`H¹_ur(G_K, E₂[φ̂])` is the exact right annihilator of `H¹_ur(G_K, E₁[φ])`** under
`localTateKerWeilPairing` over a finite extension `K` of `ℚ_p` when `p ∤ deg φ`. -/
theorem unramifiedKerCohomology_dual_eq_ker_flip_compl₂_localTateKerWeilPairing
    (hpn : ¬ p ∣ φ.degree) :
    φ.dual.unramifiedKerCohomology =
      ((φ.localTateKerWeilPairing
          (FinitePadicExtension.isUnit_natCast_of_not_dvd K p hpn)).flip.compl₂
        φ.unramifiedKerCohomology.subtype).ker := by
  ext b
  rw [AddMonoidHom.mem_ker_compl₂_subtype_iff]
  simp_rw [AddMonoidHom.flip_apply]
  exact φ.mem_unramifiedKerCohomology_dual_iff_forall_localTateKerWeilPairing_eq_zero p hpn b

end Padic

end TauCeti.Isogeny
