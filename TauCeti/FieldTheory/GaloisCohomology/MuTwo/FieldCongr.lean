/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.MapDegreeOne

/-!
# Mod-two Kummer classes of isomorphic fields

Let `e : K ≃+* L` be an isomorphism of fields in which `2` is invertible, with `K` and `L` in
independent universes; the main example is `K ≃+* ULift K`. The isomorphism induces the
continuous equivalence `e.absoluteGaloisGroupCongr : G_L ≃ₜ* G_K` of absolute Galois groups,
conjugation through the chosen identification `e.separableClosureCongr` of separable closures,
and hence the transport `TauCeti.trivialF2Map1Equiv` of `H¹(-, 𝔽₂)`. This file proves that this
transport carries Kummer classes to Kummer classes:

```text
trivialF2Map1Equiv e.absoluteGaloisGroupCongr (a) = (e a)     for a ∈ Kˣ.
```

On explicit cocycles this is the observation that if `α² = a` in `Kˢ`, then the image
`β` of `α` in `Lˢ` is a square root of `e a`, and `g ∈ G_L` fixes `β` exactly when its conjugate
in `G_K` fixes `α`, so the two `𝔽₂`-valued Kummer cocycles correspond under the compatible pair.

## Main results

* `RingEquiv.trivialF2Map1Equiv_kummerClass`: transport along a field isomorphism sends the Kummer
  class of `a` to the Kummer class of `e a`.
* `RingEquiv.trivialF2Map1Equiv_symm_kummerClass`: the inverse transport sends the Kummer class
  of `b ∈ Lˣ` to the Kummer class of `e⁻¹ b`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §5 and
  Ch. VI, §2: compatible pairs, and the Kummer sequence (6.2.1).
-/

public noncomputable section

open TauCeti TauCeti.ContCohomology

namespace RingEquiv

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]

attribute [local instance] TopRep.distribMulAction

/-- The trivial `𝔽₂` coefficients are a discrete module. -/
local instance continuousSMul_trivialF2_fieldCongr (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- A square root of `a` in `Kˢ` is carried by the chosen identification of separable closures to
a square root of `e a` in `Lˢ`. -/
private theorem units_map_separableClosureCongr_symm_pow (e : K ≃+* L) {a : Kˣ}
    {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    Units.map (e.separableClosureCongr.symm : SeparableClosure K →* SeparableClosure L) α ^ 2 =
      Units.map (algebraMap L (SeparableClosure L)).toMonoidHom
        (Units.map ((e : K →+* L) : K →* L) a) := by
  rw [← map_pow, hα]
  ext
  simp

/-- An automorphism of `Lˢ` fixes the transported square root exactly when its conjugate in
`G_K` fixes the original one. -/
private theorem absoluteGaloisGroupCongr_smul_eq_iff (e : K ≃+* L) (g : AbsoluteGaloisGroup L)
    (α : (SeparableClosure K)ˣ) :
    e.absoluteGaloisGroupCongr g • α = α ↔
      g • Units.map (e.separableClosureCongr.symm : SeparableClosure K →* SeparableClosure L) α =
        Units.map (e.separableClosureCongr.symm : SeparableClosure K →* SeparableClosure L) α := by
  simp only [Units.ext_iff, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass,
    absoluteGaloisGroupCongr_apply]
  rw [← e.separableClosureCongr.symm.injective.eq_iff, RingEquiv.symm_apply_apply]

variable [Invertible (2 : K)] [Invertible (2 : L)]

/-- **The mod-two Kummer cocycles of a square root and of its transport correspond** under the
compatible pair of `e.absoluteGaloisGroupCongr` and the identity of `𝔽₂`. -/
private theorem cocyclesMap1_kummerCocycleModTwo (e : K ≃+* L) {a : Kˣ}
    {α : (SeparableClosure K)ˣ}
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) :
    cocyclesMap1 (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V
        (AbsoluteGaloisGroup L) (trivialF2 (AbsoluteGaloisGroup L)).V e.absoluteGaloisGroupCongr
        trivialF2CoeffHom continuous_of_discreteTopology
        (trivialF2CoeffHom_smul
          ((e.absoluteGaloisGroupCongr : AbsoluteGaloisGroup L →ₜ* AbsoluteGaloisGroup K) :
            AbsoluteGaloisGroup L →* AbsoluteGaloisGroup K))
        (kummerCocycleModTwo K hα) =
      kummerCocycleModTwo L (units_map_separableClosureCongr_symm_pow e hα) := by
  refine Subtype.ext (funext fun g ↦ (trivialF2Equiv _).injective ?_)
  rw [kummerCocycleModTwo_apply, cocyclesMap1_apply]
  simp only [ContinuousMonoidHom.coe_coe, trivialF2CoeffHom_apply, AddEquiv.apply_symm_apply,
    kummerCocycleModTwo_apply]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd ((absoluteGaloisGroupCongr_smul_eq_iff e g α).mp h₁) h₂
  · exact absurd ((absoluteGaloisGroupCongr_smul_eq_iff e g α).mpr h₂) h₁
  · rfl

/-- **Kummer classes are natural in field isomorphisms**: for `e : K ≃+* L` with `K` and `L` in
independent universes, transport of `H¹(-, 𝔽₂)` along `G_L ≃ G_K` sends the Kummer class
`(a) ∈ H¹(G_K, 𝔽₂)` to the Kummer class `(e a) ∈ H¹(G_L, 𝔽₂)`. -/
@[simp]
theorem trivialF2Map1Equiv_kummerClass (e : K ≃+* L) (a : Kˣ) :
    trivialF2Map1Equiv e.absoluteGaloisGroupCongr (kummerClass a) =
      kummerClass (Units.map ((e : K →+* L) : K →* L) a) := by
  obtain ⟨α, hα⟩ := exists_pow_eq_units_map (isUnit_of_invertible (2 : K)) a
  rw [kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq K a α hα,
    kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq L _ _
      (units_map_separableClosureCongr_symm_pow e hα),
    trivialF2Map1Equiv_eqToHom, explicitH1AddEquivContinuousCohomology_continuousCohomologyMap1,
    kummerCocycleModTwoClass_def, kummerCocycleModTwoClass_def, explicitMap1_mk,
    cocyclesMap1_kummerCocycleModTwo]

/-- The inverse transport of `H¹(-, 𝔽₂)` sends the Kummer class of `b ∈ Lˣ` to the Kummer class
of `e⁻¹ b ∈ Kˣ`. -/
@[simp]
theorem trivialF2Map1Equiv_symm_kummerClass (e : K ≃+* L) (b : Lˣ) :
    trivialF2Map1Equiv e.absoluteGaloisGroupCongr.symm (kummerClass b) =
      kummerClass (Units.map ((e.symm : L →+* K) : L →* K) b) := by
  rw [← trivialF2Map1Equiv_symm, AddEquiv.symm_apply_eq, trivialF2Map1Equiv_kummerClass]
  congr
  ext
  simp

end RingEquiv
