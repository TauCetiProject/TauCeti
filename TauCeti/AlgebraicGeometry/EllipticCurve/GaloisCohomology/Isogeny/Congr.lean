/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Descent

/-!
# Congruence of kernel coefficient modules and their first cohomology

Algebraic identities between morphisms of elliptic curves, such as
`φ.dual.baseChange L = (φ.baseChange L).dual` and `φ.dual.dual = φ`, hold only propositionally.
Transporting kernel points or cohomology classes across such equalities with `Eq.rec` obscures
their underlying coordinates in `W₁.PointCoeff`.

For an equality `h : f = g` of morphisms `f, g : W₁ → W₂` over `K`, this file constructs an
explicit `G_K`-equivariant additive equivalence `TauCeti.Isogeny.Hom.kerCoeffCongr h` between
`f.KerCoeff` and `g.KerCoeff` that leaves the ambient point in `W₁.PointCoeff` definitionally
unchanged, together with the induced equivalence `TauCeti.Isogeny.Hom.kerH1Congr h` on first
continuous Galois cohomology. Because the ambient point is unchanged, `kerH1Congr` commutes with
the map to point cohomology `H¹(G_K, E₁)` and therefore preserves the kernel cutting out the
Selmer local condition.

## Main definitions

* `TauCeti.Isogeny.Hom.kerCoeffCongr`: the additive equivalence `E₁(Kˢ)[f] ≃+ E₁(Kˢ)[g]` for
  `h : f = g`, preserving the underlying point in `E₁(Kˢ)` definitionally.
* `TauCeti.Isogeny.Hom.kerCoeffCongrHom`: the corresponding `G_K`-equivariant homomorphism.
* `TauCeti.Isogeny.Hom.kerH1Congr`: the induced additive equivalence
  `H¹(G_K, E₁[f]) ≃+ H¹(G_K, E₁[g])`.

## Main results

* `TauCeti.Isogeny.Hom.coe_kerCoeffCongr`: `kerCoeffCongr` preserves the underlying point in
  `W₁.PointCoeff`.
* `TauCeti.Isogeny.Hom.explicitCoeff1_kerCoeffIncl_kerH1Congr` and
  `TauCeti.Isogeny.Hom.mem_ker_explicitCoeff1_kerCoeffIncl_kerH1Congr_iff`: `kerH1Congr` commutes
  with `H¹(G_K, E₁[f]) → H¹(G_K, E₁)` and preserves its kernel.
* `TauCeti.Isogeny.kerH1Congr_kummerMap`: compatibility with the Kummer map.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

open WeierstrassCurve TauCeti.ContCohomology

namespace TauCeti.Isogeny.Hom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Congruence of kernel coefficient modules**: an equality `f = g` of morphisms `W₁ → W₂`
identifies `E₁(Kˢ)[f]` with `E₁(Kˢ)[g]` without altering the underlying point in `E₁(Kˢ)`. -/
def kerCoeffCongr {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g) :
    f.KerCoeff ≃+ g.KerCoeff :=
  AddEquiv.addSubgroupCongr
    (congrArg (fun φ : Hom W₁.toAffine W₂.toAffine ↦
      (φ.pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker) h)

/-- `kerCoeffCongr` leaves the underlying point in `W₁.PointCoeff` unchanged. -/
@[simp]
theorem coe_kerCoeffCongr {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g) (P : f.KerCoeff) :
    (kerCoeffCongr h P : W₁.PointCoeff) = P :=
  (rfl)

/-- The inverse of `kerCoeffCongr h` is `kerCoeffCongr h.symm`. -/
@[simp]
theorem kerCoeffCongr_symm {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g) :
    (kerCoeffCongr h).symm = kerCoeffCongr h.symm :=
  (rfl)

/-- Congruence along reflexivity is the identity equivalence. -/
@[simp]
theorem kerCoeffCongr_refl (f : Hom W₁.toAffine W₂.toAffine) :
    kerCoeffCongr (rfl : f = f) = AddEquiv.refl _ :=
  (rfl)

/-- Congruences of kernel coefficient modules compose along transitivity. -/
@[simp]
theorem kerCoeffCongr_trans {f g k : Hom W₁.toAffine W₂.toAffine} (h₁ : f = g) (h₂ : g = k) :
    (kerCoeffCongr h₁).trans (kerCoeffCongr h₂) = kerCoeffCongr (h₁.trans h₂) :=
  (rfl)

/-- Applying congruences of kernel coefficient modules sequentially composes along transitivity. -/
@[simp]
theorem kerCoeffCongr_kerCoeffCongr {f g k : Hom W₁.toAffine W₂.toAffine}
    (h₁ : f = g) (h₂ : g = k) (P : f.KerCoeff) :
    kerCoeffCongr h₂ (kerCoeffCongr h₁ P) = kerCoeffCongr (h₁.trans h₂) P :=
  (rfl)

/-- `kerCoeffCongr` is `G_K`-equivariant. -/
@[simp]
theorem kerCoeffCongr_smul {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g)
    (σ : AbsoluteGaloisGroup K) (P : f.KerCoeff) :
    kerCoeffCongr h (σ • P) = σ • kerCoeffCongr h P :=
  Subtype.ext (by simp)

/-- `kerCoeffCongr` bundled as a `G_K`-equivariant additive homomorphism. -/
def kerCoeffCongrHom {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g) :
    f.KerCoeff →+[AbsoluteGaloisGroup K] g.KerCoeff :=
  { (kerCoeffCongr h).toAddMonoidHom with map_smul' := kerCoeffCongr_smul h }

/-- Applying `kerCoeffCongrHom` evaluates `kerCoeffCongr`. -/
@[simp]
theorem kerCoeffCongrHom_apply {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g) (P : f.KerCoeff) :
    kerCoeffCongrHom h P = kerCoeffCongr h P :=
  (rfl)

/-- `kerCoeffCongrHom` along reflexivity is the identity `G_K`-equivariant homomorphism. -/
@[simp]
theorem kerCoeffCongrHom_refl (f : Hom W₁.toAffine W₂.toAffine) :
    kerCoeffCongrHom (rfl : f = f) = DistribMulActionHom.id _ := by
  ext
  simp

/-- Equivariant kernel congruences compose along transitivity. -/
@[simp]
theorem kerCoeffCongrHom_comp {f g k : Hom W₁.toAffine W₂.toAffine} (h₁ : f = g) (h₂ : g = k) :
    (kerCoeffCongrHom h₂).comp (kerCoeffCongrHom h₁) = kerCoeffCongrHom (h₁.trans h₂) := by
  ext
  simp

/-- `kerCoeffCongrHom` commutes with the inclusions into `W₁.PointCoeff`. -/
@[simp]
theorem kerCoeffIncl_comp_kerCoeffCongrHom {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g) :
    g.kerCoeffIncl.comp (kerCoeffCongrHom h) = f.kerCoeffIncl := by
  ext P
  simp

/-- **Congruence on first cohomology of kernels**: an equality `f = g` of morphisms `W₁ → W₂`
induces an additive equivalence `H¹(G_K, E₁[f]) ≃+ H¹(G_K, E₁[g])`. -/
def kerH1Congr {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g) :
    H1 (AbsoluteGaloisGroup K) f.KerCoeff ≃+ H1 (AbsoluteGaloisGroup K) g.KerCoeff :=
  explicitCoeff1Equiv _ _ (kerCoeffCongr h) continuous_of_discreteTopology
    continuous_of_discreteTopology (kerCoeffCongr_smul h)

/-- `kerH1Congr` acts as the coefficient map of `kerCoeffCongrHom`. -/
theorem kerH1Congr_apply {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g)
    (c : H1 (AbsoluteGaloisGroup K) f.KerCoeff) :
    kerH1Congr h c = explicitCoeff1 _ _ (kerCoeffCongrHom h) continuous_of_discreteTopology c := by
  rw [kerH1Congr, explicitCoeff1Equiv_apply]
  rfl

/-- Congruence on `H¹` along reflexivity is the identity equivalence. -/
@[simp]
theorem kerH1Congr_refl (f : Hom W₁.toAffine W₂.toAffine) :
    kerH1Congr (rfl : f = f) = AddEquiv.refl _ := by
  ext c
  rw [kerH1Congr_apply]
  exact (congrArg (fun φ => explicitCoeff1 _ _ φ continuous_of_discreteTopology c)
    (kerCoeffCongrHom_refl f)).trans (by simp)

/-- The inverse of `kerH1Congr h` is `kerH1Congr h.symm`. -/
@[simp]
theorem kerH1Congr_symm {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g) :
    (kerH1Congr h).symm = kerH1Congr h.symm := by
  subst h
  simp

/-- Congruences on `H¹` compose along transitivity. -/
@[simp]
theorem kerH1Congr_trans {f g k : Hom W₁.toAffine W₂.toAffine} (h₁ : f = g) (h₂ : g = k) :
    (kerH1Congr h₁).trans (kerH1Congr h₂) = kerH1Congr (h₁.trans h₂) := by
  ext c
  rw [AddEquiv.trans_apply, kerH1Congr_apply, kerH1Congr_apply, kerH1Congr_apply,
    ← AddMonoidHom.comp_apply, ← explicitCoeff1_comp]
  exact congrArg (fun φ => explicitCoeff1 _ _ φ continuous_of_discreteTopology c)
    (kerCoeffCongrHom_comp h₁ h₂)

/-- Applying congruences on `H¹` sequentially composes along transitivity. -/
@[simp]
theorem kerH1Congr_kerH1Congr {f g k : Hom W₁.toAffine W₂.toAffine}
    (h₁ : f = g) (h₂ : g = k) (c : H1 (AbsoluteGaloisGroup K) f.KerCoeff) :
    kerH1Congr h₂ (kerH1Congr h₁ c) = kerH1Congr (h₁.trans h₂) c :=
  DFunLike.congr_fun (kerH1Congr_trans h₁ h₂) c

/-- `kerH1Congr` commutes with the map `H¹(G_K, E₁[f]) → H¹(G_K, E₁)` induced by the kernel
inclusion. -/
@[simp]
theorem explicitCoeff1_kerCoeffIncl_kerH1Congr {f g : Hom W₁.toAffine W₂.toAffine} (h : f = g)
    (c : H1 (AbsoluteGaloisGroup K) f.KerCoeff) :
    explicitCoeff1 _ _ g.kerCoeffIncl continuous_of_discreteTopology (kerH1Congr h c) =
      explicitCoeff1 _ _ f.kerCoeffIncl continuous_of_discreteTopology c := by
  rw [kerH1Congr_apply, ← AddMonoidHom.comp_apply, ← explicitCoeff1_comp]
  exact congrArg (fun φ => explicitCoeff1 _ _ φ continuous_of_discreteTopology c)
    (kerCoeffIncl_comp_kerCoeffCongrHom h)

/-- `kerH1Congr` preserves membership in the kernel of `H¹(G_K, E₁[f]) → H¹(G_K, E₁)`. -/
theorem mem_ker_explicitCoeff1_kerCoeffIncl_kerH1Congr_iff {f g : Hom W₁.toAffine W₂.toAffine}
    (h : f = g) {c : H1 (AbsoluteGaloisGroup K) f.KerCoeff} :
    kerH1Congr h c ∈
        (explicitCoeff1 _ _ g.kerCoeffIncl continuous_of_discreteTopology).ker ↔
      c ∈ (explicitCoeff1 _ _ f.kerCoeffIncl continuous_of_discreteTopology).ker := by
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, explicitCoeff1_kerCoeffIncl_kerH1Congr]

end TauCeti.Isogeny.Hom

namespace TauCeti.Isogeny

open Hom (ofIsogeny kerH1Congr)

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- Transporting a Kummer class along an equality of separable isogenies yields the Kummer class
of the target isogeny. -/
-- Apply before the simplifier unfolds the Kummer maps into connecting maps.
@[simp↓]
theorem kerH1Congr_kummerMap {φ ψ : Isogeny W₁.toAffine W₂.toAffine}
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₁.toAffine.FunctionField]
    [DecidableEq K] (h : ofIsogeny φ = ofIsogeny ψ) (P : W₂.toAffine.Point) :
    kerH1Congr h (φ.kummerMap P) = ψ.kummerMap P := by
  obtain rfl := Hom.ofIsogeny_injective h
  simp

end TauCeti.Isogeny

end
