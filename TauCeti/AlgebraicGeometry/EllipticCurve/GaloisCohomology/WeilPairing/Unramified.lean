/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Unramified
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Local
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Unramified
import TauCeti.Algebra.Module.ZMod.Annihilator
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Finiteness
import TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup

/-!
# Unramified local Tate duality for elliptic torsion and isogeny kernels

Let `K` be a nonarchimedean local field. Transporting Milne's unramified local duality theorem
(`TauCeti.ClassFieldTheory.unramifiedH1_eq_ker_compl₂_dualityMap1`) along the Galois
module isomorphisms given by the Weil pairing (`WeierstrassCurve.torsionCoeffWeilDual_bijective`)
and the isogeny Weil pairing (`TauCeti.Isogeny.kerCoeffWeilDual_bijective`) yields unramified
duality for elliptic curves and isogenies:

1. **Over any nonarchimedean local field `K`**, when the multiplier `m` is invertible in `K`,
   `H¹_ur(G_K, E[m])` is isotropic for `W.torsionH1WeilPairing` and `W.localTateWeilPairing`
   (the isogeny orthogonality counterparts `kerH1WeilPairing_eq_zero_of_mem_unramifiedKerCohomology`
   and `localTateKerWeilPairing_eq_zero_of_mem_unramifiedKerCohomology` live in
   `TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/WeilPairing/Orthogonality.lean`).
2. **Over a finite extension `K` of `ℚ_p`** (`TauCeti.FinitePadicExtension K p`), when `p ∤ m`
   (respectively `p ∤ deg φ`), `H¹_ur(G_K, E[m])` is its own exact annihilator under
   `W.localTateWeilPairing`, and `H¹_ur(G_K, E₁[φ])` and `H¹_ur(G_K, E₂[φ̂])` are exact mutual
   annihilators under `φ.localTateKerWeilPairing`.

Combined with `TauCeti.Isogeny.range_kummerMap_eq_unramifiedKerCohomology`, this identifies the
local conditions of `Sel_φ` and `Sel_φ̂` at almost every finite place with a pair of exact mutual
annihilators in `H¹(G_{K_v}, E₁[φ]) × H¹(G_{K_v}, E₂[φ̂])`, as required by the Poitou–Tate /
Greenberg–Wiles comparison of Selmer groups in Cassels' theorem.

## Main results

* `WeierstrassCurve.torsionH1WeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology` and
  `localTateWeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology`: isotropy of
  `H¹_ur(G_K, E[m])` over any nonarchimedean local field.
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

section General

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (W : WeierstrassCurve K) [W.IsElliptic]
  {m : ℕ} (hm : IsUnit (m : K))

/-- **Unramified `m`-torsion cohomology is isotropic for the Weil cup product** over any
nonarchimedean local field in which `m` is invertible. -/
theorem torsionH1WeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology
    {a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)}
    (ha : a ∈ W.unramifiedTorsionCohomology m) (hb : b ∈ W.unramifiedTorsionCohomology m) :
    W.torsionH1WeilPairing m hm a b = 0 := by
  have : NeZero m := NeZero.of_neZero_natCast K (h := ⟨hm.ne_zero⟩)
  rw [unramifiedTorsionCohomology_eq_unramifiedH1] at ha hb
  rw [torsionH1WeilPairing_eq_dualityMap1]
  exact dualityMap1_kummerCoeff_eq_zero_of_mem_unramifiedH1 ha
    ((W.torsionCoeffWeilDual m hm).explicitCoeff1_mem_unramifiedH1
      continuous_of_discreteTopology hb)

/-- **Unramified `m`-torsion cohomology is isotropic for the local Tate pairing** over any
nonarchimedean local field in which `m` is invertible. -/
theorem localTateWeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology
    {a b : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)}
    (ha : a ∈ W.unramifiedTorsionCohomology m) (hb : b ∈ W.unramifiedTorsionCohomology m) :
    W.localTateWeilPairing m hm a b = 0 := by
  rw [localTateWeilPairing_apply,
    W.torsionH1WeilPairing_eq_zero_of_mem_unramifiedTorsionCohomology hm ha hb, map_zero, map_zero]

end General

section Padic

variable (p : ℕ) [Fact p.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [FinitePadicExtension K p]
  (W : WeierstrassCurve K) [W.IsElliptic] {m : ℕ}

/-- **Pointwise unramified self-duality for `E[m]`.** Over a finite extension `K` of `ℚ_p` with
`p ∤ m`, a class in `H¹(G_K, E[m])` is unramified if and only if its local Tate pairing with every
unramified class in `H¹(G_K, E[m])` vanishes. -/
theorem mem_unramifiedTorsionCohomology_iff_forall_localTateWeilPairing_eq_zero
    (hm : IsUnit (m : K)) (hpm : ¬ p ∣ m)
    (a : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    a ∈ W.unramifiedTorsionCohomology m ↔
      ∀ b ∈ W.unramifiedTorsionCohomology m, W.localTateWeilPairing m hm a b = 0 := by
  have : NeZero m := NeZero.of_neZero_natCast K (h := ⟨hm.ne_zero⟩)
  let d := explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
    (W.torsionCoeffWeilDual m hm) continuous_of_discreteTopology
  have hd : Function.Bijective d :=
    explicitCoeff1_bijective _ _ (W.torsionCoeffWeilDual_bijective m hm)
  simp only [unramifiedTorsionCohomology_eq_unramifiedH1]
  rw [mem_unramifiedH1_iff_forall_dualityMap1_eq_zero p hpm
      (fun P : W.TorsionCoeff m ↦ AddSubgroup.torsionBy.nsmul P) a]
  refine ⟨fun h b hb ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [localTateWeilPairing_apply, torsionH1WeilPairing_eq_dualityMap1,
      h (d b) ((W.torsionCoeffWeilDual m hm).explicitCoeff1_mem_unramifiedH1 _ hb),
      map_zero, map_zero]
  · obtain ⟨b, rfl⟩ := hd.2 y
    have hb : b ∈ unramifiedH1 K (W.TorsionCoeff m) :=
      ((W.torsionCoeffWeilDual m hm).explicitCoeff1_mem_unramifiedH1_iff_of_bijective
        (W.torsionCoeffWeilDual_bijective m hm)).mp hy
    have h0 := h b hb
    rwa [localTateWeilPairing_apply, torsionH1WeilPairing_eq_dualityMap1,
      AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff] at h0

/-- **`H¹_ur(G_K, E[m])` is its own exact annihilator under `localTateWeilPairing`** over a finite
extension `K` of `ℚ_p` when `p ∤ m`. -/
theorem unramifiedTorsionCohomology_eq_ker_compl₂_localTateWeilPairing
    (hm : IsUnit (m : K)) (hpm : ¬ p ∣ m) :
    W.unramifiedTorsionCohomology m =
      ((W.localTateWeilPairing m hm).compl₂ (W.unramifiedTorsionCohomology m).subtype).ker := by
  ext a
  simp only [W.mem_unramifiedTorsionCohomology_iff_forall_localTateWeilPairing_eq_zero p hm hpm a,
    AddMonoidHom.mem_ker, AddMonoidHom.ext_iff, AddMonoidHom.compl₂_apply,
    AddMonoidHom.zero_apply, Subtype.forall, AddSubgroup.subtype_apply]

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
    (hn : IsUnit (φ.degree : K)) (hpn : ¬ p ∣ φ.degree)
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    a ∈ φ.unramifiedKerCohomology ↔
      ∀ b ∈ φ.dual.unramifiedKerCohomology, φ.localTateKerWeilPairing hn a b = 0 := by
  have : NeZero φ.degree := NeZero.of_neZero_natCast K (h := ⟨hn.ne_zero⟩)
  let d := explicitCoeff1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff
    (φ.kerCoeffWeilDual hn) continuous_of_discreteTopology
  have hd : Function.Bijective d := explicitCoeff1_bijective _ _ (φ.kerCoeffWeilDual_bijective hn)
  simp only [unramifiedKerCohomology_eq_unramifiedH1]
  rw [mem_unramifiedH1_iff_forall_dualityMap1_eq_zero p hpn
      φ.degree_nsmul_kerCoeff_eq_zero a]
  refine ⟨fun h b hb ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [localTateKerWeilPairing_apply, kerH1WeilPairing_eq_dualityMap1,
      h (d b) ((φ.kerCoeffWeilDual hn).explicitCoeff1_mem_unramifiedH1 _ hb),
      map_zero, map_zero]
  · obtain ⟨b, rfl⟩ := hd.2 y
    have hb : b ∈ unramifiedH1 K (ofIsogeny φ.dual).KerCoeff :=
      ((φ.kerCoeffWeilDual hn).explicitCoeff1_mem_unramifiedH1_iff_of_bijective
        (φ.kerCoeffWeilDual_bijective hn)).mp hy
    have h0 := h b hb
    rwa [localTateKerWeilPairing_apply, kerH1WeilPairing_eq_dualityMap1,
      AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff] at h0

/-- **`H¹_ur(G_K, E₁[φ])` is the exact left annihilator of `H¹_ur(G_K, E₂[φ̂])`** under
`localTateKerWeilPairing` over a finite extension `K` of `ℚ_p` when `p ∤ deg φ`. -/
theorem unramifiedKerCohomology_eq_ker_compl₂_localTateKerWeilPairing
    (hn : IsUnit (φ.degree : K)) (hpn : ¬ p ∣ φ.degree) :
    φ.unramifiedKerCohomology =
      ((φ.localTateKerWeilPairing hn).compl₂ φ.dual.unramifiedKerCohomology.subtype).ker := by
  ext a
  simp only [φ.mem_unramifiedKerCohomology_iff_forall_localTateKerWeilPairing_eq_zero p hn hpn a,
    AddMonoidHom.mem_ker, AddMonoidHom.ext_iff, AddMonoidHom.compl₂_apply,
    AddMonoidHom.zero_apply, Subtype.forall, AddSubgroup.subtype_apply]

/-- **`H¹_ur(G_K, E₂[φ̂])` is the exact right annihilator of `H¹_ur(G_K, E₁[φ])`** under
`localTateKerWeilPairing` over a finite extension `K` of `ℚ_p` when `p ∤ deg φ`. -/
theorem unramifiedKerCohomology_dual_eq_ker_flip_compl₂_localTateKerWeilPairing
    (hn : IsUnit (φ.degree : K)) (hpn : ¬ p ∣ φ.degree) :
    φ.dual.unramifiedKerCohomology =
      ((φ.localTateKerWeilPairing hn).flip.compl₂ φ.unramifiedKerCohomology.subtype).ker := by
  have : NeZero φ.degree := NeZero.of_neZero_natCast K (h := ⟨hn.ne_zero⟩)
  have hdeg_dual : φ.dual.degree = φ.degree := φ.degree_dual
  have hdual_nsmul : ∀ P : (ofIsogeny φ.dual).KerCoeff, φ.degree • P = 0 := fun P ↦ by
    rw [← hdeg_dual]
    exact φ.dual.degree_nsmul_kerCoeff_eq_zero P
  have : Finite (ofIsogeny φ.dual).KerCoeff :=
    (ofIsogeny φ.dual).finite_kerCoeff (ofIsogeny_ne_zero φ.dual)
  have : Finite (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :=
    (isTopologicallyFinitelyGenerated_absoluteGaloisGroup p K).finite_H1
  rw [φ.unramifiedKerCohomology_eq_ker_compl₂_localTateKerWeilPairing p hn hpn]
  exact ((φ.localTateKerWeilPairing hn).ker_flip_compl₂_subtype_ker_compl₂_subtype_zmod
    (φ.localTateKerWeilPairing_bijective hn)
    (nsmul_H1_eq_zero (G := AbsoluteGaloisGroup K) hdual_nsmul)
    φ.dual.unramifiedKerCohomology).symm

/-- **Pointwise unramified duality for `E₂[φ̂]`.** Over a finite extension `K` of `ℚ_p` with
`p ∤ deg φ`, a class in `H¹(G_K, E₂[φ̂])` is unramified if and only if every unramified class in
`H¹(G_K, E₁[φ])` pairs to zero with it under `localTateKerWeilPairing`. -/
theorem mem_unramifiedKerCohomology_dual_iff_forall_localTateKerWeilPairing_eq_zero
    (hn : IsUnit (φ.degree : K)) (hpn : ¬ p ∣ φ.degree)
    (b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff) :
    b ∈ φ.dual.unramifiedKerCohomology ↔
      ∀ a ∈ φ.unramifiedKerCohomology, φ.localTateKerWeilPairing hn a b = 0 := by
  conv_lhs =>
    rw [φ.unramifiedKerCohomology_dual_eq_ker_flip_compl₂_localTateKerWeilPairing p hn hpn]
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.ext_iff, AddMonoidHom.compl₂_apply,
    AddMonoidHom.zero_apply, AddMonoidHom.flip_apply, Subtype.forall, AddSubgroup.subtype_apply]

end Padic

end TauCeti.Isogeny
