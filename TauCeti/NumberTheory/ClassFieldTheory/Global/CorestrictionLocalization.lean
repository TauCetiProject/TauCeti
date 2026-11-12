/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.OpenSubgroup
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LayerInvariant
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.Pullback

/-!
# Localization of corestricted idele classes

Let `K` be a number field, `U` an open subgroup of `G_K` with fixed field `F`, and `v` a place of
`K`. This file computes the localization at `v` of the corestriction to `G_K` of a class
`x ∈ H²(U, I_{Kˢ})`. Classically, the invariant at `v` of a corestricted class is the sum of the
invariants of `x` at the places `w` of `F` above `v`:

```text
inv_v (cor_U^{G_K} x) = ∑_{w ∣ v} inv_w x.
```

This file proves the group-theoretic form of that formula, in which the places above `v` are
replaced by double cosets. Fix an embedding `τ : Kˢ → K_vˢ` of separable closures, with
decomposition map `φ_τ : G_{K_v} → G_K`. For a representative `s` of a double coset
`φ_τ(G_{K_v}) s U`, the conjugate embedding `τ ∘ s` gives the decomposition map
`φ_{τ ∘ s} = s⁻¹ φ_τ s`, which carries the open subgroup `φ_{τ ∘ s}⁻¹(U)` of `G_{K_v}` into `U`.
Pulling `x` back along it and along the coordinate `ideleCoeffComponent (τ ∘ s)` at `v` is the
localization of `x` along `τ ∘ s`; classically, the double cosets index the places `w` of `F`
above `v`, `φ_{τ ∘ s}⁻¹(U)` is the absolute Galois group of the completion `F_w`, and this is
the localization of `x` at `w`, but that identification is not made here. The Mackey formula
along the decomposition map (`TauCeti.ContCohomology.explicitMap2_explicitCor2_eq_sum`) gives

```text
loc_v (cor_U^{G_K} x) = ∑_{φ_τ(G_{K_v}) s U} cor (loc_{τ ∘ s} x),
```

the corestriction being from `φ_{τ ∘ s}⁻¹(U)` to `G_{K_v}`
(`ideleBrLocalization_explicitCor2`, and `ideleInfiniteBrLocalization_explicitCor2` at an infinite
place). The local invariant of an open subgroup of `G_{K_v}` is the invariant of its corestriction
(`TauCeti.ClassFieldTheory.subgroupInvMap`), so the invariant at `v` is the sum of the invariants
of the localizations (`invMap_ideleBrLocalization_explicitCor2`). For an idele layer `L/F` this
computes the local invariant `ideleLocalInvAt K L v` of its classes
(`ideleLocalInvAt_eq_sum_subgroupInvMap`).

## Main results

* `TauCeti.ClassFieldTheory.ideleBrLocalization_explicitCor2`,
  `TauCeti.ClassFieldTheory.ideleInfiniteBrLocalization_explicitCor2`: the localization of a
  corestricted class is the sum over the double cosets of the corestricted localizations.
* `TauCeti.ClassFieldTheory.invMap_ideleBrLocalization_explicitCor2`: the invariant at a finite
  place of a corestricted class is the sum of the invariants of its localizations.
* `TauCeti.ClassFieldTheory.ideleLocalInvAt_eq_sum_subgroupInvMap`: the local invariant at `v` of
  an idele-layer class is the sum of the invariants of its localizations along the conjugates of
  `τ`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.6) and
  (8.1.17).
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField ContCohomology

variable {K : Type} [Field K] [NumberField K]
  (U : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex]
  (hU : IsOpen (U : Set (AbsoluteGaloisGroup K)))

/-! ### Finite places -/

section Finite

variable {v : HeightOneSpectrum (𝓞 K)}
  (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (r : DoubleCoset.Quotient
    ((absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
      AbsoluteGaloisGroup K).range : Set (AbsoluteGaloisGroup K))
    (U : Set (AbsoluteGaloisGroup K)) → AbsoluteGaloisGroup K)
  (hr : ∀ D, DoubleCoset.mk (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
    AbsoluteGaloisGroup K).range U (r D) = D)

include hr in
/-- **The localization at a finite place of a corestricted idele class.** For an open subgroup `U`
of `G_K`, an embedding `τ : Kˢ → K_vˢ` and representatives `r D` of the double cosets
`φ_τ(G_{K_v}) \ G_K / U`, the localization at `v` of the corestriction of `x ∈ H²(U, I_{Kˢ})` is
the sum over the double cosets of the corestrictions, from `φ_{τ ∘ r D}⁻¹(U)` to `G_{K_v}`, of the
localizations of `x` along `τ ∘ r D`. -/
theorem ideleBrLocalization_explicitCor2 (x : H2 U (IdeleCoeff K)) :
    ideleBrLocalization v (explicitCor2 (AbsoluteGaloisGroup K) (IdeleCoeff K) U hU x) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient
        ((absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
          AbsoluteGaloisGroup K).range : Set (AbsoluteGaloisGroup K))
        (U : Set (AbsoluteGaloisGroup K)))
      ∑ D, unitsRepH2Equiv (v.adicCompletion K)
        (explicitCor2 (AbsoluteGaloisGroup (v.adicCompletion K)) (UnitsCoeff (v.adicCompletion K))
          (U.comap (absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
            SeparableClosure K)) : AbsoluteGaloisGroup (v.adicCompletion K) →*
              AbsoluteGaloisGroup K))
          (hU.preimage (absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
            SeparableClosure K))).continuous)
          (explicitMap2 U (IdeleCoeff K) _ (UnitsCoeff (v.adicCompletion K))
            ((absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
              SeparableClosure K))).subgroupComap U)
            (ideleCoeffComponent (τ.comp (r D : SeparableClosure K →ₐ[K] SeparableClosure K)))
            continuous_of_discreteTopology (fun y m ↦
              ContinuousMonoidHom.subgroupComap_smul _ U y m ▸ ideleCoeffComponent_smul _ y.1 m)
            x)) := by
  -- The statements are large, so the proof is a chain of `trans` rather than `rw`, whose closing
  -- `rfl` attempt on them exhausts the heartbeats.
  refine (ideleBrLocalization_apply τ _).trans <| (congrArg _ <|
    explicitMap2_explicitCor2_eq_sum (absoluteGaloisGroupMap τ) (ideleCoeffComponent τ)
      (ideleCoeffComponent_smul τ) U continuous_of_discreteTopology hU r hr
      (fun D ↦ absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K] SeparableClosure K)))
      (fun D h ↦ absoluteGaloisGroupMap_comp τ (r D) h) x).trans <|
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun D _ ↦ ?_)
  -- The coordinate along `τ ∘ s` is the coordinate along `τ` of the translate by `s`.
  have hco : (ideleCoeffComponent τ).comp (DistribSMul.toAddMonoidHom (IdeleCoeff K) (r D)) =
      ideleCoeffComponent (τ.comp (r D : SeparableClosure K →ₐ[K] SeparableClosure K)) :=
    AddMonoidHom.ext fun m ↦ (ideleCoeffComponent_comp τ (r D) m).symm
  simp only [hco]

include hr in
/-- **The invariant at a finite place of a corestricted idele class** is the sum, over the double
cosets `φ_τ(G_{K_v}) \ G_K / U`, of the invariants of the localizations of the class along the
conjugates `τ ∘ r D` of `τ`, each read by the local invariant of the open subgroup
`φ_{τ ∘ r D}⁻¹(U)` of `G_{K_v}`: classically, `inv_v (cor x) = ∑_{w ∣ v} inv_w x`. -/
theorem invMap_ideleBrLocalization_explicitCor2 (x : H2 U (IdeleCoeff K)) :
    invMap (v.adicCompletion K)
        (ideleBrLocalization v (explicitCor2 (AbsoluteGaloisGroup K) (IdeleCoeff K) U hU x)) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient
        ((absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
          AbsoluteGaloisGroup K).range : Set (AbsoluteGaloisGroup K))
        (U : Set (AbsoluteGaloisGroup K)))
      ∑ D, subgroupInvMap (v.adicCompletion K)
        (U.comap (absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
          SeparableClosure K)) : AbsoluteGaloisGroup (v.adicCompletion K) →*
            AbsoluteGaloisGroup K))
        (hU.preimage (absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
          SeparableClosure K))).continuous)
        (explicitMap2 U (IdeleCoeff K) _ (UnitsCoeff (v.adicCompletion K))
          ((absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
            SeparableClosure K))).subgroupComap U)
          (ideleCoeffComponent (τ.comp (r D : SeparableClosure K →ₐ[K] SeparableClosure K)))
          continuous_of_discreteTopology (fun y m ↦
            ContinuousMonoidHom.subgroupComap_smul _ U y m ▸ ideleCoeffComponent_smul _ y.1 m)
          x) := by
  refine (congrArg _ (ideleBrLocalization_explicitCor2 U hU τ r hr x)).trans <|
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun D _ ↦ ?_)
  exact (subgroupInvMap_apply _ _ _ _).symm

/-- **The local invariant of an idele-layer class**: for a layer `L/F` of the idele formation of
`K`, cut out by `V ◁ U`, the invariant at the finite place `v` of a class `x` is the sum, over the
double cosets `φ_τ(G_{K_v}) \ G_K / U`, of the invariants of the localizations along the conjugates
`τ ∘ r D` of `τ` of its inflation to `U`. -/
theorem ideleLocalInvAt_eq_sum_subgroupInvMap (L : NormalLayer (AbsoluteGaloisGroup K))
    (r : DoubleCoset.Quotient
      ((absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
        AbsoluteGaloisGroup K).range : Set (AbsoluteGaloisGroup K))
      (L.ground.toSubgroup : Set (AbsoluteGaloisGroup K)) → AbsoluteGaloisGroup K)
    (hr : ∀ D, DoubleCoset.mk (absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K).range
        L.ground.toSubgroup (r D) = D)
    (x : L.H (ideleFormation K) 2) :
    ideleLocalInvAt K L v x =
      letI := Fintype.ofFinite (DoubleCoset.Quotient
        ((absoluteGaloisGroupMap τ : AbsoluteGaloisGroup (v.adicCompletion K) →*
          AbsoluteGaloisGroup K).range : Set (AbsoluteGaloisGroup K))
        (L.ground.toSubgroup : Set (AbsoluteGaloisGroup K)))
      ∑ D, subgroupInvMap (v.adicCompletion K)
        (L.ground.toSubgroup.comap (absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
          SeparableClosure K)) : AbsoluteGaloisGroup (v.adicCompletion K) →*
            AbsoluteGaloisGroup K))
        (L.ground.isOpen.preimage (absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
          SeparableClosure K))).continuous)
        (explicitMap2 L.ground.toSubgroup (IdeleCoeff K) _ (UnitsCoeff (v.adicCompletion K))
          ((absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
            SeparableClosure K))).subgroupComap L.ground.toSubgroup)
          (ideleCoeffComponent (τ.comp (r D : SeparableClosure K →ₐ[K] SeparableClosure K)))
          continuous_of_discreteTopology (fun y m ↦
            ContinuousMonoidHom.subgroupComap_smul _ _ y m ▸ ideleCoeffComponent_smul _ y.1 m)
          (L.explicitInfl2 (ideleCoeffEquivIdeleFormation K)
            (ideleCoeffEquivIdeleFormation_smul K) x)) :=
  (ideleLocalInvAt_apply K L v x).trans <|
    (congrArg _ (congrArg _ (ideleLayerCorInfl_apply K L x))).trans <|
      invMap_ideleBrLocalization_explicitCor2 _ L.ground.isOpen τ r hr _

end Finite

/-! ### Infinite places -/

section Infinite

variable {w : InfinitePlace K} (τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion)
  (r : DoubleCoset.Quotient
    ((absoluteGaloisGroupMap τ : AbsoluteGaloisGroup w.Completion →*
      AbsoluteGaloisGroup K).range : Set (AbsoluteGaloisGroup K))
    (U : Set (AbsoluteGaloisGroup K)) → AbsoluteGaloisGroup K)
  (hr : ∀ D, DoubleCoset.mk (absoluteGaloisGroupMap τ : AbsoluteGaloisGroup w.Completion →*
    AbsoluteGaloisGroup K).range U (r D) = D)

include hr in
/-- **The localization at an infinite place of a corestricted idele class**: the archimedean
counterpart of `TauCeti.ClassFieldTheory.ideleBrLocalization_explicitCor2`. -/
theorem ideleInfiniteBrLocalization_explicitCor2 (x : H2 U (IdeleCoeff K)) :
    ideleInfiniteBrLocalization w (explicitCor2 (AbsoluteGaloisGroup K) (IdeleCoeff K) U hU x) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient
        ((absoluteGaloisGroupMap τ : AbsoluteGaloisGroup w.Completion →*
          AbsoluteGaloisGroup K).range : Set (AbsoluteGaloisGroup K))
        (U : Set (AbsoluteGaloisGroup K)))
      ∑ D, unitsRepH2Equiv w.Completion
        (explicitCor2 (AbsoluteGaloisGroup w.Completion) (UnitsCoeff w.Completion)
          (U.comap (absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
            SeparableClosure K)) : AbsoluteGaloisGroup w.Completion →* AbsoluteGaloisGroup K))
          (hU.preimage (absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
            SeparableClosure K))).continuous)
          (explicitMap2 U (IdeleCoeff K) _ (UnitsCoeff w.Completion)
            ((absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K]
              SeparableClosure K))).subgroupComap U)
            (ideleCoeffInfiniteComponent (τ.comp (r D : SeparableClosure K →ₐ[K]
              SeparableClosure K)))
            continuous_of_discreteTopology
            (fun y m ↦ ContinuousMonoidHom.subgroupComap_smul _ U y m ▸
              ideleCoeffInfiniteComponent_smul _ y.1 m) x)) := by
  refine (ideleInfiniteBrLocalization_apply τ _).trans <| (congrArg _ <|
    explicitMap2_explicitCor2_eq_sum (absoluteGaloisGroupMap τ) (ideleCoeffInfiniteComponent τ)
      (ideleCoeffInfiniteComponent_smul τ) U continuous_of_discreteTopology hU r hr
      (fun D ↦ absoluteGaloisGroupMap (τ.comp (r D : SeparableClosure K →ₐ[K] SeparableClosure K)))
      (fun D h ↦ absoluteGaloisGroupMap_comp τ (r D) h) x).trans <|
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun D _ ↦ ?_)
  -- The coordinate along `τ ∘ s` is the coordinate along `τ` of the translate by `s`.
  have hco :
      (ideleCoeffInfiniteComponent τ).comp (DistribSMul.toAddMonoidHom (IdeleCoeff K) (r D)) =
        ideleCoeffInfiniteComponent (τ.comp (r D : SeparableClosure K →ₐ[K] SeparableClosure K)) :=
    AddMonoidHom.ext fun m ↦ (ideleCoeffInfiniteComponent_comp τ (r D) m).symm
  simp only [hco]

end Infinite

end TauCeti.ClassFieldTheory
