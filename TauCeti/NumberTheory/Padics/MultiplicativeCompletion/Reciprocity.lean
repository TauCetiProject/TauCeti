/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.ArtinMap
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.ProfiniteCompletion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic

/-!
# Local reciprocity for the multiplicative p-adic completion

Let `L/K` be a finite extension, `L` a nonarchimedean local field of characteristic zero, and let
`V ≤ G_K` be the open subgroup fixing the copy `ι(L)` of `L` in a separable closure of `K`. Local
reciprocity identifies the multiplicative `p`-adic completion `A(L) = lim_m Lˣ/(Lˣ)^(p^m)` with
`V^ab(p)`, the maximal pro-`p` quotient of the topological abelianization of `V ≃ G_L`. The
construction identifies `A(L)` with the maximal pro-`p` quotient of the profinite completion of
`Lˣ`, applies the profinite-completion form of local reciprocity
`ClassFieldTheory.profiniteCompletionArtinEquiv`, and transports the result along `G_L ≃ V`.

When `L/K` is normal, `G_K ⧸ V ≃ Gal(L/K)` acts on both sides, and the identification is
equivariant. This is what lets statements about the class module `V^ab(p)` of the pair `V ◁ G_K`
be read as statements about the `Gal(L/K)`-module `A(L)`. Equivariance reduces, by density of
`Lˣ` in `A(L)`, to the naturality of the Artin map under the field automorphisms of `L`
(`ClassFieldTheory.artinMap_congr`).

## Main declarations

* `TauCeti.padicCompletionUnitsEquivAbsoluteGaloisGroupAbelianizationProP`: the isomorphism
  `A(L) ≃ₜ* G_L^ab(p)`, for Mathlib's absolute Galois group of `L`.
* `TauCeti.padicCompletionUnitsEquivAbelianizationProP`: the isomorphism `A(L) ≃ₜ* V^ab(p)`.
* `TauCeti.padicCompletionUnitsEquivAbelianizationProP_smul`: for normal `L/K`, it is equivariant
  for `Gal(L/K) ≃ G_K ⧸ V`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of
  (7.4.1).
-/

public section

noncomputable section

namespace TauCeti

open ClassFieldTheory

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L] [Algebra K L]

/-! ### Conjugating by an element of `G_K` -/

section Conj

variable [CharZero L]

/-- The automorphism `s⁻¹ ∘ g ∘ s` of `Lˢ`, where `s : Lˢ ≃ Kˢ` is the identification of
separable closures attached to `ι` and `g ∈ G_K`, read on `AlgebraicClosure L`, which is `Lˢ`
in characteristic zero. It extends `ι.restrictNormalHom g` (`conjAlgebraicClosure_algebraMap`). -/
private def conjAlgebraicClosure (ι : L →ₐ[K] SeparableClosure K) (g : AbsoluteGaloisGroup K) :
    AlgebraicClosure L ≃+* AlgebraicClosure L :=
  let a : SeparableClosure L ≃+* AlgebraicClosure L :=
    .ofBijective (algebraMap (SeparableClosure L) (AlgebraicClosure L))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  let s := separableClosureRingEquiv K L ι
  (a.symm.trans ((s.trans g.toRingEquiv).trans s.symm)).trans a

private theorem conjAlgebraicClosure_coe (ι : L →ₐ[K] SeparableClosure K)
    (g : AbsoluteGaloisGroup K) (w : SeparableClosure L) :
    conjAlgebraicClosure K L ι g w =
      ((separableClosureRingEquiv K L ι).symm (g (separableClosureRingEquiv K L ι w)) :
        AlgebraicClosure L) := by
  have ha (v : SeparableClosure L) : RingEquiv.ofBijective
      (algebraMap (SeparableClosure L) (AlgebraicClosure L))
      IsAlgClosed.algebraMap_bijective_of_isIntegral v = v := (rfl)
  simp only [conjAlgebraicClosure, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
  rw [← ha w, RingEquiv.symm_apply_apply, ha]

variable [Normal K L]

private theorem conjAlgebraicClosure_algebraMap (ι : L →ₐ[K] SeparableClosure K)
    (g : AbsoluteGaloisGroup K) (c : L) :
    conjAlgebraicClosure K L ι g (algebraMap L (AlgebraicClosure L) c) =
      algebraMap L (AlgebraicClosure L) (ι.restrictNormalHom g c) := by
  have hc (c : L) : algebraMap L (AlgebraicClosure L) c =
      (algebraMap L (SeparableClosure L) c : AlgebraicClosure L) :=
    IsScalarTower.algebraMap_apply L (SeparableClosure L) (AlgebraicClosure L) c
  rw [hc, conjAlgebraicClosure_coe, separableClosureRingEquiv_algebraMap,
    ← AlgHom.restrictNormalHom_commutes, separableClosureRingEquiv_symm_apply_eq_algebraMap, hc]

variable [FiniteDimensional K L] in
/-- If `σ' ∈ G_L` is the conjugate of `σ ∈ G_L` by `conjAlgebraicClosure K L ι g`, then their
images in `V = galoisSubgroup K L ι` are conjugate by `g`. -/
private theorem galoisSubgroupEquiv_eq_conjNormal (ι : L →ₐ[K] SeparableClosure K)
    (g : AbsoluteGaloisGroup K) (σ σ' : Field.absoluteGaloisGroup L)
    (h : ∀ y, conjAlgebraicClosure K L ι g (σ.toRingEquiv y) =
      σ'.toRingEquiv (conjAlgebraicClosure K L ι g y)) :
    galoisSubgroupEquiv K L ι (absoluteGaloisGroupRestrictEquiv L σ') =
      MulAut.conjNormal g (galoisSubgroupEquiv K L ι (absoluteGaloisGroupRestrictEquiv L σ)) := by
  set s := separableClosureRingEquiv K L ι
  -- On `Lˢ`, the restriction of `σ'` is `s⁻¹ ∘ g ∘ s ∘ σ ∘ s⁻¹ ∘ g⁻¹ ∘ s`.
  have hσ' (w : SeparableClosure L) : absoluteGaloisGroupRestrictEquiv L σ' (s.symm (g (s w))) =
      s.symm (g (s (absoluteGaloisGroupRestrictEquiv L σ w))) := by
    refine Subtype.ext ((coe_absoluteGaloisGroupRestrictEquiv_apply L σ' _).trans ?_)
    rw [← conjAlgebraicClosure_coe, ← conjAlgebraicClosure_coe]
    exact (h w).symm.trans (congrArg _ (coe_absoluteGaloisGroupRestrictEquiv_apply L σ w).symm)
  refine Subtype.ext <| AlgEquiv.ext fun y ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, g (s w) = y := ⟨s.symm (g⁻¹ y), by simp⟩
  rw [← s.apply_symm_apply (g (s w)), galoisSubgroupEquiv_apply_separableClosureRingEquiv, hσ',
    s.apply_symm_apply, s.apply_symm_apply, ← galoisSubgroupEquiv_apply_separableClosureRingEquiv]
  simp [s, MulAut.conjNormal_apply]

end Conj

/-! ### The reciprocity isomorphism -/

variable [FiniteDimensional K L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [CharZero L]

/-- **Local reciprocity for `A(L)`, absolute form.** The multiplicative `p`-adic completion
`A(L)` is the maximal pro-`p` quotient of the abelianized absolute Galois group `G_L^ab` of `L`:
it is the maximal pro-`p` quotient of the profinite completion of `Lˣ`, which local reciprocity
identifies with `G_L^ab` (`ClassFieldTheory.profiniteCompletionArtinEquiv`). -/
def padicCompletionUnitsEquivAbsoluteGaloisGroupAbelianizationProP :
    ↑(padicCompletionUnits p L) ≃ₜ*
      maximalProPQuotient p (Field.absoluteGaloisGroupAbelianization L) :=
  (maximalProPQuotientProfiniteCompletionEquivPadicCompletionUnits p L).symm.trans
    (maximalProPQuotient.congr (profiniteCompletionArtinEquiv L))

/-- The absolute form of local reciprocity for `A(L)` sends the class of a unit to the class of
its absolute Artin symbol. -/
@[simp]
theorem padicCompletionUnitsEquivAbsoluteGaloisGroupAbelianizationProP_of (x : Lˣ) :
    padicCompletionUnitsEquivAbsoluteGaloisGroupAbelianizationProP p L
        (padicCompletionUnitsOf p L x) =
      (artinMap L x : maximalProPQuotient p (Field.absoluteGaloisGroupAbelianization L)) := by
  simp [padicCompletionUnitsEquivAbsoluteGaloisGroupAbelianizationProP]

/-- The identification `G_L^ab ≃ₜ* V^ab` of topological abelianizations, where `V ≤ G_K` is the
subgroup fixing `ι(L)`, induced by `absoluteGaloisGroupRestrictEquiv L` and
`galoisSubgroupEquiv K L ι`. -/
private def absoluteGaloisGroupAbelianizationEquiv (ι : L →ₐ[K] SeparableClosure K) :
    Field.absoluteGaloisGroupAbelianization L ≃ₜ*
      TopologicalAbelianization (galoisSubgroup K L ι).toSubgroup :=
  ((absoluteGaloisGroupRestrictEquiv L).trans
    (galoisSubgroupEquiv K L ι)).topologicalAbelianizationCongr

/-- **Local reciprocity for `A(L)`.** If `V ≤ G_K` is the subgroup fixing the image of a finite
extension `L/K` under `ι : L →ₐ[K] Kˢ`, then the multiplicative `p`-adic completion `A(L)` of
`Lˣ` is canonically isomorphic to `V^ab(p)`, the maximal pro-`p` quotient of the topological
abelianization of `V`. -/
def padicCompletionUnitsEquivAbelianizationProP (ι : L →ₐ[K] SeparableClosure K) :
    ↑(padicCompletionUnits p L) ≃ₜ*
      abelianizationProP p (AbsoluteGaloisGroup K) (galoisSubgroup K L ι).toSubgroup :=
  (padicCompletionUnitsEquivAbsoluteGaloisGroupAbelianizationProP p L).trans
    (maximalProPQuotient.congr (absoluteGaloisGroupAbelianizationEquiv K L ι))

/-- On the dense image of `Lˣ`, local reciprocity for `A(L)` sends the class of a unit `x` to the
class of `σ_V`, where `σ ∈ G_L` represents the absolute Artin symbol of `x` and `σ_V ∈ V` is its
image under `G_L ≃ V`. -/
theorem padicCompletionUnitsEquivAbelianizationProP_of (ι : L →ₐ[K] SeparableClosure K)
    (x : Lˣ) (σ : Field.absoluteGaloisGroup L)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization L) = artinMap L x) :
    padicCompletionUnitsEquivAbelianizationProP p K L ι (padicCompletionUnitsOf p L x) =
      abelianizationProPMk p (AbsoluteGaloisGroup K) (galoisSubgroup K L ι).toSubgroup
        (galoisSubgroupEquiv K L ι (absoluteGaloisGroupRestrictEquiv L σ)) := by
  rw [padicCompletionUnitsEquivAbelianizationProP, ContinuousMulEquiv.trans_apply,
    padicCompletionUnitsEquivAbsoluteGaloisGroupAbelianizationProP_of, ← hσ]
  simp [absoluteGaloisGroupAbelianizationEquiv, abelianizationProPMk_apply]

/-! ### Equivariance -/

variable [Normal K L]

private theorem padicCompletionUnitsEquivAbelianizationProP_of_smul
    (ι : L →ₐ[K] SeparableClosure K) (g : AbsoluteGaloisGroup K) (x : Lˣ)
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
    [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L] :
    padicCompletionUnitsEquivAbelianizationProP p K L ι
        (padicCompletionUnitsAut p L K (ι.restrictNormalHom g)
          (padicCompletionUnitsOf p L x)) =
      (g : AbsoluteGaloisGroup K ⧸ (galoisSubgroup K L ι).toSubgroup) •
        padicCompletionUnitsEquivAbelianizationProP p K L ι
          (padicCompletionUnitsOf p L x) := by
  set τ := ι.restrictNormalHom g
  set e := conjAlgebraicClosure K L ι g
  have he_symm (c : L) : e.symm (algebraMap L (AlgebraicClosure L) c) =
      algebraMap L (AlgebraicClosure L) (τ.symm c) := by
    rw [RingEquiv.symm_apply_eq, conjAlgebraicClosure_algebraMap, τ.apply_symm_apply]
  -- Conjugating a representative `σ` of the Artin symbol of `x` by `e` gives a representative
  -- `σ'` of the Artin symbol of `τ x`, by naturality of the Artin map.
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (artinMap L x)
  let σ' : Field.absoluteGaloisGroup L :=
    AlgEquiv.ofRingEquiv (f := (e.symm.trans σ.toRingEquiv).trans e) fun c ↦ by
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply, he_symm]
      exact (congrArg e (AlgEquiv.commutes (R := L) σ _)).trans
        ((conjAlgebraicClosure_algebraMap K L ι g _).trans (congrArg _ (τ.apply_symm_apply c)))
  have hσσ' (y : AlgebraicClosure L) : e (σ.toRingEquiv y) = σ'.toRingEquiv (e y) := by
    simp [σ']
  have hArtin := artinMap_congr τ.toRingEquiv
    (τ.restrictScalars ℚ_[p]).continuous_of_valuativeExtension e
    (conjAlgebraicClosure_algebraMap K L ι g) x σ σ' hσσ' hσ
  rw [padicCompletionUnitsAut_of,
    padicCompletionUnitsEquivAbelianizationProP_of p K L ι _ σ' hArtin,
    padicCompletionUnitsEquivAbelianizationProP_of p K L ι x σ hσ, abelianizationProPMk_conj,
    galoisSubgroupEquiv_eq_conjNormal K L ι g σ σ' hσσ']

/-- **Equivariance of local reciprocity for `A(L)`.** Let `L/K` be a finite normal extension of
`p`-adic fields and `V ≤ G_K` the subgroup fixing `ι(L)`. For `g ∈ G_K`, the action of its
restriction `ι.restrictNormalHom g ∈ Gal(L/K)` on `A(L)` corresponds to the conjugation action of
the class of `g` in `G_K ⧸ V` on `V^ab(p)`. As `quotientFixingSubgroupFieldRangeEquiv K L ι`
sends the class of `g` to `ι.restrictNormalHom g`, this is equivariance for `Gal(L/K) ≃ G_K ⧸ V`.
-/
theorem padicCompletionUnitsEquivAbelianizationProP_smul
    (ι : L →ₐ[K] SeparableClosure K) (g : AbsoluteGaloisGroup K)
    (z : ↑(padicCompletionUnits p L))
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
    [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L] :
    padicCompletionUnitsEquivAbelianizationProP p K L ι
        (padicCompletionUnitsAut p L K (ι.restrictNormalHom g) z) =
      (g : AbsoluteGaloisGroup K ⧸ (galoisSubgroup K L ι).toSubgroup) •
        padicCompletionUnitsEquivAbelianizationProP p K L ι z := by
  let e := padicCompletionUnitsEquivAbelianizationProP p K L ι
  let q : AbsoluteGaloisGroup K ⧸ (galoisSubgroup K L ι).toSubgroup := g
  let _ : T2Space (abelianizationProP p (AbsoluteGaloisGroup K)
      (galoisSubgroup K L ι).toSubgroup) := e.symm.toHomeomorph.isEmbedding.t2Space
  have hleft : Continuous fun y ↦
      e (padicCompletionUnitsAut p L K (ι.restrictNormalHom g) y) :=
    e.continuous.comp (continuous_padicCompletionUnitsAut p L K (ι.restrictNormalHom g))
  have hright : Continuous fun y ↦ q • e y :=
    (continuous_const_smul q).comp e.continuous
  have heq := (denseRange_padicCompletionUnitsOf p L).equalizer hleft hright
    (funext fun x ↦ padicCompletionUnitsEquivAbelianizationProP_of_smul p K L ι g x)
  exact congrFun heq z

end TauCeti
