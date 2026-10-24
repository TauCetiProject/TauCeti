/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Descent
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
-- Proof-only: `Point.cast_some`, the coordinates of a point transported along `AddEquiv.cast`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Restriction of the Galois cohomology of an elliptic curve along a field extension

Let `W` be a Weierstrass curve over a field `K`, let `L/K` be an arbitrary field extension, and
let `τ : Kˢ →ₐ[K] Lˢ` be a `K`-embedding of separable closures. Applying `τ` to coordinates maps
the points of `W` over `Kˢ` to the points of `W⁄L` over `Lˢ`,

```text
W.pointCoeffBaseChange τ : E(Kˢ) → E(Lˢ),
```

and this map is equivariant along the induced map of absolute Galois groups
`TauCeti.absoluteGaloisGroupMap τ : G_L → G_K` (`WeierstrassCurve.pointCoeffBaseChange_smul`). It
therefore induces restriction maps

```text
W.pointRes τ : H¹(G_K, E(Kˢ)) → H¹(G_L, E(Lˢ)),
W.torsionRes τ m : H¹(G_K, E(Kˢ)[m]) → H¹(G_L, E(Lˢ)[m]),
```

which commute with the map induced by the inclusion `E[m] → E`
(`WeierstrassCurve.pointRes_torsionCoeffIncl`). When `L` is a completion `K_v` of a global field,
these are the localisation maps at `v`, out of which the Selmer and Shafarevich–Tate groups are
cut.

The group and coordinate maps depend on `τ`, but their induced cohomology maps do not:
`pointRes_eq_pointRes` and `torsionRes_eq_torsionRes` in
`TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/EmbeddingIndependence.lean` prove
independence of this choice.

The main result is that restriction is compatible with the Kummer maps
(`WeierstrassCurve.torsionRes_kummerMap`): the restriction of the Kummer class of `P ∈ E(K)` is
the Kummer class over `L` of the image of `P` in `E(L)`. This is what lets the image of a
local Kummer map serve as the local condition at `L` of the `m`-Selmer group.

## Main definitions

* `WeierstrassCurve.pointCoeffBaseChange`: the equivariant map `E(Kˢ) → E(Lˢ)` along `τ`.
* `WeierstrassCurve.torsionCoeffBaseChange`: its restriction `E(Kˢ)[m] → E(Lˢ)[m]`.
* `WeierstrassCurve.pointRes`: restriction `H¹(G_K, E(Kˢ)) → H¹(G_L, E(Lˢ))`.
* `WeierstrassCurve.torsionRes`: restriction `H¹(G_K, E(Kˢ)[m]) → H¹(G_L, E(Lˢ)[m])`.

## Main results

* `WeierstrassCurve.pointCoeffBaseChange_smul`: `pointCoeffBaseChange τ` is equivariant along
  `absoluteGaloisGroupMap τ`.
* `WeierstrassCurve.pointCoeffBaseChange_basePointCoeff`: on points of `E(K)` it is base change
  to `L`.
* `WeierstrassCurve.pointCoeffBaseChange_pointCoeffBaseChange`,
  `WeierstrassCurve.torsionCoeffBaseChange_torsionCoeffBaseChange`: the maps compose in a tower
  `K → L → M`, up to the identification of `(W⁄L)⁄M` with `W⁄M`.
* `WeierstrassCurve.pointCoeffBaseChange_bijective`,
  `WeierstrassCurve.torsionCoeffBaseChange_bijective`: the coordinate maps along a bijective
  embedding of separable closures are bijective.
* `WeierstrassCurve.forall_smul_eq_torsionCoeff_baseChange`: along a bijective embedding,
  `G_L` acts trivially on `E(Lˢ)[m]` once it acts trivially on `E(Kˢ)[m]`.
* `WeierstrassCurve.pointRes_torsionCoeffIncl`: restriction commutes with
  `H¹(G, E[m]) → H¹(G, E)`.
* `WeierstrassCurve.torsionRes_kummerMap`: restriction commutes with the Kummer maps.

## Implementation notes

The restriction maps follow the pullback of the Kummer classes of the multiplicative group along
an arbitrary field extension, `TauCeti.kummerCoeffBaseChange` and `TauCeti.explicitMap1_kummerMap`
in `TauCeti/FieldTheory/GaloisCohomology/Kummer.lean`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] (W : WeierstrassCurve K)
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-! ### The map on points over the separable closures -/

/-- Applying `τ` to the coordinates of a nonsingular point of `W` over `Kˢ` gives a nonsingular
point of `W⁄L` over `Lˢ`. -/
theorem nonsingular_baseChange_separableClosure {x y : SeparableClosure K}
    (h : (W⁄(SeparableClosure K)).toAffine.Nonsingular x y) :
    ((W⁄L)⁄(SeparableClosure L)).toAffine.Nonsingular (τ x) (τ y) :=
  (show (W⁄L)⁄(SeparableClosure L) = W⁄(SeparableClosure L) from
    W.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm ▸
    (W.toAffine.baseChange_nonsingular (S := K) (f := τ) τ.injective x y).2 h

open scoped Classical in
/-- **The map `E(Kˢ) → E(Lˢ)` along an embedding `τ : Kˢ →ₐ[K] Lˢ`** of separable closures: it
applies `τ` to the coordinates of a point. -/
def pointCoeffBaseChange : W.PointCoeff →+ (W⁄L).PointCoeff :=
  (W⁄L).pointCoeffEquiv.toAddMonoidHom.comp <|
    (AddEquiv.cast (M := fun V : WeierstrassCurve (SeparableClosure L) => V.toAffine.Point)
      (show (W⁄L)⁄(SeparableClosure L) = W⁄(SeparableClosure L) from
        W.map_baseChange
          (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm).toAddMonoidHom.comp <|
    (Affine.Point.map (W' := W.toAffine) τ).comp W.pointCoeffEquiv.symm.toAddMonoidHom

open scoped Classical in
/-- On points over the separable closures, coefficient base change is the coordinate map,
with the canonical identification of the iterated base change. -/
theorem pointCoeffEquiv_symm_pointCoeffBaseChange (P : W.PointCoeff) :
    (W⁄L).pointCoeffEquiv.symm (W.pointCoeffBaseChange τ P) =
      AddEquiv.cast (M := fun V : WeierstrassCurve (SeparableClosure L) ↦ V.toAffine.Point)
        (show (W⁄L)⁄(SeparableClosure L) = W⁄(SeparableClosure L) from
          W.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm
        (Affine.Point.map τ (W.pointCoeffEquiv.symm P)) := by
  simp only [pointCoeffBaseChange, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply]

open scoped Classical in
/-- `pointCoeffBaseChange τ` applies `τ` to both coordinates of an affine point. -/
@[simp]
theorem pointCoeffBaseChange_pointCoeffEquiv_some {x y : SeparableClosure K}
    (h : (W⁄(SeparableClosure K)).toAffine.Nonsingular x y) :
    W.pointCoeffBaseChange τ (W.pointCoeffEquiv (.some x y h)) =
      (W⁄L).pointCoeffEquiv (.some _ _ (W.nonsingular_baseChange_separableClosure τ h)) := by
  simp only [pointCoeffBaseChange, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, Affine.Point.map_some, AddEquiv.cast_apply]
  rw [Affine.Point.cast_some (show (W⁄L)⁄(SeparableClosure L) = W⁄(SeparableClosure L) from
    W.map_baseChange (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm]

open scoped Classical in
/-- **`pointCoeffBaseChange τ` is equivariant** along `absoluteGaloisGroupMap τ : G_L → G_K`. -/
@[simp]
theorem pointCoeffBaseChange_smul (g : AbsoluteGaloisGroup L) (P : W.PointCoeff) :
    W.pointCoeffBaseChange τ (absoluteGaloisGroupMap τ g • P) = g • W.pointCoeffBaseChange τ P := by
  obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, smul_zero, map_zero, smul_zero]
  · rw [smul_pointCoeffEquiv, Affine.Point.map_some, pointCoeffBaseChange_pointCoeffEquiv_some,
      pointCoeffBaseChange_pointCoeffEquiv_some, smul_pointCoeffEquiv, Affine.Point.map_some]
    simp only [AlgEquiv.coe_toAlgHom, absoluteGaloisGroupMap_commutes]

open scoped Classical in
/-- Precomposing an embedding by a Galois automorphism composes the coordinate map with
the same automorphism's action on points. -/
theorem pointCoeffBaseChange_comp (σ : AbsoluteGaloisGroup K) (P : W.PointCoeff) :
    W.pointCoeffBaseChange (τ.comp σ.toAlgHom) P = W.pointCoeffBaseChange τ (σ • P) := by
  obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, map_zero, smul_zero]
  · rw [smul_pointCoeffEquiv, Affine.Point.map_some,
      pointCoeffBaseChange_pointCoeffEquiv_some, pointCoeffBaseChange_pointCoeffEquiv_some]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

variable [DecidableEq K] [DecidableEq L] in
/-- **On points of `E(K)`, `pointCoeffBaseChange τ` is base change to `L`**: the image in `E(Lˢ)`
of a point of `E(K)` is the image of its base change in `E(L)`. -/
@[simp]
theorem pointCoeffBaseChange_basePointCoeff (P : W.toAffine.Point) :
    W.pointCoeffBaseChange τ (W.basePointCoeff P) =
      (W⁄L).basePointCoeff (W.toAffine.pointMap L P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero, map_zero]
  · rw [basePointCoeff_some, Affine.pointMap_some, basePointCoeff_some]
    -- The certificates `basePointCoeff_some` produces are stated against `W` rather than `W⁄K`,
    -- so they only typecheck after unfolding; abstracting them lets the coordinate lemma fire.
    generalize_proofs h₁ h₂
    rw [pointCoeffBaseChange_pointCoeffEquiv_some]
    simp only [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-! ### The map on `m`-torsion -/

variable (m : ℕ)

/-- **The map `E(Kˢ)[m] → E(Lˢ)[m]`** along `τ`, the restriction of `pointCoeffBaseChange τ`. -/
def torsionCoeffBaseChange : W.TorsionCoeff m →+ (W⁄L).TorsionCoeff m :=
  ((W.pointCoeffBaseChange τ).comp (AddSubgroup.torsionBy W.PointCoeff m).subtype).codRestrict _
    fun P => by
      rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.comp_apply, ← map_nsmul,
        AddSubgroup.coe_subtype, AddSubgroup.torsionBy.nsmul_iff.1 P.2, map_zero]

@[simp]
theorem coe_torsionCoeffBaseChange (P : W.TorsionCoeff m) :
    (W.torsionCoeffBaseChange τ m P : (W⁄L).PointCoeff) = W.pointCoeffBaseChange τ P :=
  (rfl)

/-- **`torsionCoeffBaseChange τ m` is equivariant** along `absoluteGaloisGroupMap τ : G_L → G_K`. -/
@[simp]
theorem torsionCoeffBaseChange_smul (g : AbsoluteGaloisGroup L) (P : W.TorsionCoeff m) :
    W.torsionCoeffBaseChange τ m (absoluteGaloisGroupMap τ g • P) =
      g • W.torsionCoeffBaseChange τ m P :=
  Subtype.ext <| by
    rw [coe_torsionCoeffBaseChange, coe_smul_torsionCoeff, coe_smul_torsionCoeff,
      coe_torsionCoeffBaseChange, pointCoeffBaseChange_smul]

/-- Precomposing an embedding by a Galois automorphism composes its map on torsion points
with the same automorphism's action. -/
theorem torsionCoeffBaseChange_comp (σ : AbsoluteGaloisGroup K) (m : ℕ)
    (P : W.TorsionCoeff m) :
    W.torsionCoeffBaseChange (τ.comp σ.toAlgHom) m P =
      W.torsionCoeffBaseChange τ m (σ • P) := by
  apply Subtype.ext
  rw [coe_torsionCoeffBaseChange, coe_torsionCoeffBaseChange, coe_smul_torsionCoeff,
    pointCoeffBaseChange_comp]

/-! ### Bijectivity along a bijective embedding -/

variable {τ} in
open scoped Classical in
/-- **Along a bijective embedding of separable closures, `E(Kˢ) → E(Lˢ)` is bijective.** -/
theorem pointCoeffBaseChange_bijective (hτ : Function.Bijective τ) :
    Function.Bijective (W.pointCoeffBaseChange τ) := by
  let e : SeparableClosure K ≃ₐ[K] SeparableClosure L := AlgEquiv.ofBijective τ hτ
  -- The point map along `τ` is injective, with right inverse the point map along `e.symm`.
  have hmap : Function.Bijective (Affine.Point.map (W' := W.toAffine) τ) := by
    refine ⟨Affine.Point.map_injective _, fun Q ↦ ⟨Affine.Point.map e.symm.toAlgHom Q, ?_⟩⟩
    rcases Q with _ | ⟨x, y, h⟩
    · rfl
    · simp only [Affine.Point.map_some]
      congr <;> exact e.apply_symm_apply _
  simp only [pointCoeffBaseChange, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom]
  exact (W⁄L).pointCoeffEquiv.bijective.comp <| (AddEquiv.cast _).bijective.comp <|
    hmap.comp W.pointCoeffEquiv.symm.bijective

variable {τ} in
/-- **Along a bijective embedding of separable closures, `E(Kˢ)[m] → E(Lˢ)[m]` is bijective.** -/
theorem torsionCoeffBaseChange_bijective (hτ : Function.Bijective τ) :
    Function.Bijective (W.torsionCoeffBaseChange τ m) := by
  -- `torsionCoeffBaseChange τ m` is the transport of `m`-torsion along `pointCoeffBaseChange τ`.
  let e := AddEquiv.ofBijective (W.pointCoeffBaseChange τ) (W.pointCoeffBaseChange_bijective hτ)
  have h : ⇑(W.torsionCoeffBaseChange τ m) = e.torsionByCongr m := funext fun _ ↦ Subtype.ext <| by
    rw [coe_torsionCoeffBaseChange, AddEquiv.torsionByCongr_apply_coe, AddEquiv.ofBijective_apply]
  exact h ▸ (e.torsionByCongr m).bijective

variable {τ} in
/-- **Rational `m`-torsion descends along a bijective embedding of separable closures**: if `G_L`
acts trivially on `E(Kˢ)[m]` through `absoluteGaloisGroupMap τ`, then it acts trivially on
`E(Lˢ)[m]`. -/
theorem forall_smul_eq_torsionCoeff_baseChange (hτ : Function.Bijective τ)
    (h : ∀ (g : AbsoluteGaloisGroup L) (Q : W.TorsionCoeff m), absoluteGaloisGroupMap τ g • Q = Q)
    (g : AbsoluteGaloisGroup L) (P : (W⁄L).TorsionCoeff m) : g • P = P := by
  obtain ⟨Q, rfl⟩ := (W.torsionCoeffBaseChange_bijective m hτ).2 P
  rw [← W.torsionCoeffBaseChange_smul, h]

/-! ### Towers of extensions

The identification of `(W⁄L)⁄M` with `W⁄M` is Mathlib's `WeierstrassCurve.map_baseChange` at
`IsScalarTower.toAlgHom K L M`, whose underlying ring homomorphism is `algebraMap L M`; the `show`
in the statements below only restates it in terms of base change. -/

section Tower

variable {M : Type*} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  (τ' : SeparableClosure L →ₐ[L] SeparableClosure M)
  (τ'' : SeparableClosure K →ₐ[K] SeparableClosure M)

open scoped Classical in
/-- **The coordinate maps compose in a tower** `K → L → M`: if `τ'' : Kˢ → Mˢ` is the composite of
`τ : Kˢ → Lˢ` and `τ' : Lˢ → Mˢ`, mapping `E(Kˢ) → E(Lˢ) → E(Mˢ)` along `τ` and `τ'` is mapping
along `τ''`, followed by the identification of `(W⁄L)⁄M` with `W⁄M`. -/
theorem pointCoeffBaseChange_pointCoeffBaseChange (hτ : ∀ x, τ'' x = τ' (τ x))
    (P : W.PointCoeff) :
    (W⁄L).pointCoeffBaseChange τ' (W.pointCoeffBaseChange τ P) =
      AddEquiv.cast (M := PointCoeff) (show (W⁄L)⁄M = W⁄M from
        W.map_baseChange (IsScalarTower.toAlgHom K L M)).symm
        (W.pointCoeffBaseChange τ'' P) := by
  obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, map_zero]
  · rw [pointCoeffBaseChange_pointCoeffEquiv_some, pointCoeffBaseChange_pointCoeffEquiv_some,
      pointCoeffBaseChange_pointCoeffEquiv_some, cast_pointCoeffEquiv_some]
    simp only [hτ]

/-- **The maps on `m`-torsion compose in a tower** `K → L → M`, as in
`WeierstrassCurve.pointCoeffBaseChange_pointCoeffBaseChange`. -/
theorem torsionCoeffBaseChange_torsionCoeffBaseChange (hτ : ∀ x, τ'' x = τ' (τ x)) (m : ℕ)
    (P : W.TorsionCoeff m) :
    (W⁄L).torsionCoeffBaseChange τ' m (W.torsionCoeffBaseChange τ m P) =
      AddEquiv.cast (M := fun V : WeierstrassCurve M ↦ V.TorsionCoeff m)
        (show (W⁄L)⁄M = W⁄M from
          W.map_baseChange (IsScalarTower.toAlgHom K L M)).symm
        (W.torsionCoeffBaseChange τ'' m P) :=
  Subtype.ext <| by
    rw [coe_torsionCoeffBaseChange, coe_torsionCoeffBaseChange, coe_cast_torsionCoeff,
      coe_torsionCoeffBaseChange, pointCoeffBaseChange_pointCoeffBaseChange W τ τ' τ'' hτ]

end Tower

/-! ### Restriction on first cohomology -/

/-- **Restriction `H¹(G_K, E(Kˢ)) → H¹(G_L, E(Lˢ))`** along `τ`: pullback along the compatible
pair `(absoluteGaloisGroupMap τ, pointCoeffBaseChange τ)`. -/
def pointRes :
    H1 (AbsoluteGaloisGroup K) W.PointCoeff →+ H1 (AbsoluteGaloisGroup L) (W⁄L).PointCoeff :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (W.pointCoeffBaseChange τ)
    continuous_of_discreteTopology (W.pointCoeffBaseChange_smul τ)

/-- `pointRes τ` is the pullback along `(absoluteGaloisGroupMap τ, pointCoeffBaseChange τ)`. -/
theorem pointRes_eq_explicitMap1 :
    W.pointRes τ = explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (W.pointCoeffBaseChange τ)
      continuous_of_discreteTopology (W.pointCoeffBaseChange_smul τ) :=
  (rfl)

/-- **Restriction `H¹(G_K, E(Kˢ)[m]) → H¹(G_L, E(Lˢ)[m])`** along `τ`: pullback along the
compatible pair `(absoluteGaloisGroupMap τ, torsionCoeffBaseChange τ m)`. -/
def torsionRes :
    H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) →+
      H1 (AbsoluteGaloisGroup L) ((W⁄L).TorsionCoeff m) :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (W.torsionCoeffBaseChange τ m)
    continuous_of_discreteTopology (W.torsionCoeffBaseChange_smul τ m)

/-- `torsionRes τ m` is the pullback along
`(absoluteGaloisGroupMap τ, torsionCoeffBaseChange τ m)`. -/
theorem torsionRes_eq_explicitMap1 :
    W.torsionRes τ m =
      explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (W.torsionCoeffBaseChange τ m)
        continuous_of_discreteTopology (W.torsionCoeffBaseChange_smul τ m) :=
  (rfl)

/-- **Restriction commutes with `H¹(G, E[m]) → H¹(G, E)`**, the map induced by the inclusion
`E[m] → E`. -/
@[simp]
theorem pointRes_torsionCoeffIncl (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m)) :
    W.pointRes τ (explicitCoeff1 _ _ (W.torsionCoeffIncl m) continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ ((W⁄L).torsionCoeffIncl m) continuous_of_discreteTopology
        (W.torsionRes τ m c) := by
  rw [explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1, pointRes, torsionRes]
  exact explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (by ext; simp) c

/-! ### Compatibility with the Kummer maps -/

variable [DecidableEq K] [DecidableEq L] [W.IsElliptic] {m} (hm : IsUnit (m : K))

/-- **Restriction carries Kummer classes to Kummer classes**: the restriction to `L` of the Kummer
class of `P ∈ E(K)` is the Kummer class of the image of `P` in `E(L)`. -/
theorem torsionRes_kummerMap (P : W.toAffine.Point) :
    W.torsionRes τ m (W.kummerMap m hm P) =
      (W⁄L).kummerMap m (by simpa using hm.map (algebraMap K L)) (W.toAffine.pointMap L P) := by
  obtain ⟨Q, hQ⟩ := (W.kummerShortExact m hm).proj_surjective (W.basePointCoeff P)
  rw [kummerShortExact_proj, nsmulAddMonoidHom_apply] at hQ
  have hQ' : m • W.pointCoeffBaseChange τ Q = (W⁄L).basePointCoeff (W.toAffine.pointMap L P) := by
    rw [← map_nsmul, hQ, pointCoeffBaseChange_basePointCoeff]
  rw [kummerMap_eq_H1pi hm hQ, kummerMap_eq_H1pi _ hQ', torsionRes, H1pi,
    QuotientAddGroup.mk'_apply, explicitMap1_mk]
  congr 1
  refine Subtype.ext <| funext fun g => Subtype.ext ?_
  rw [cocyclesMap1_apply, coe_torsionCoeffBaseChange, coe_kummerCocycle, coe_kummerCocycle, map_sub,
    pointCoeffBaseChange_smul]

end WeierstrassCurve
