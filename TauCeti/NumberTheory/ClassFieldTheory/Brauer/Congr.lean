/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension

/-!
# Transporting the cohomological Brauer group along a field isomorphism

A field isomorphism induces an additive equivalence between the cohomological Brauer groups.
The construction uses the existing identification of separable closures and their absolute
Galois groups, followed by change of groups and coefficients in continuous cohomology. In
particular, it allows the Brauer groups of archimedean completions to be compared with those
of the real and complex fields without changing the cohomology carrier.

This API supplies an additive identification using a chosen lift to separable closures. It does
not supply functoriality lemmas comparing the lifts chosen for different field isomorphisms.
For a supplied identification `a := brCongr e`, use `a.symm` for its inverse and `a.trans b`
for successive identifications. Their cancellation and application laws are
`AddEquiv.symm_apply_apply`, `AddEquiv.apply_symm_apply`, and `AddEquiv.trans_apply`.
The archimedean invariant is independent of this identification, as recorded by
`TauCeti.ClassFieldTheory.infiniteInvMap_eq_realInv_comp` in the archimedean module.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

/-- An isomorphism of fields supplies an additive equivalence of their cohomological Brauer
groups, using a chosen identification of separable closures. -/
def brCongr {K L : Type*} [Field K] [Field L] (e : K ≃+* L) : Br K ≃+ Br L := by
  letI : Algebra K L := e.toRingHom.toAlgebra
  let eA : K ≃ₐ[K] L := { e with commutes' := fun _ => rfl }
  let σ : L →ₐ[K] SeparableClosure K :=
    (Algebra.ofId K (SeparableClosure K)).comp eA.symm.toAlgHom
  have hrange : σ.fieldRange = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact IntermediateField.mem_bot.mpr ⟨e.symm y, rfl⟩
    · intro hx
      obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.mp hx
      exact ⟨e y, congrArg (algebraMap K (SeparableClosure K)) (eA.symm_apply_apply y)⟩
  let ψ := absoluteGaloisGroupEquivFixingSubgroup K L σ
  have htop : σ.fieldRange.fixingSubgroup = ⊤ := by simp [hrange]
  let f : AbsoluteGaloisGroup L →* AbsoluteGaloisGroup K :=
    σ.fieldRange.fixingSubgroup.subtype.comp ψ.toMonoidHom
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => ψ.injective (Subtype.ext h), fun g => ?_⟩
    have hg : g ∈ σ.fieldRange.fixingSubgroup := by rw [htop]; trivial
    exact ⟨ψ.symm ⟨g, hg⟩, by simp [f]⟩
  let φ₀ := MulEquiv.ofBijective f hf
  have hcont : Continuous φ₀ := continuous_subtype_val.comp ψ.continuous
  let φ : AbsoluteGaloisGroup L ≃ₜ* AbsoluteGaloisGroup K :=
    { φ₀ with
      continuous_toFun := hcont
      continuous_invFun := (Continuous.homeoOfEquivCompactToT2 hcont).symm.continuous }
  let c : UnitsCoeff L ≃+ UnitsCoeff K :=
    (Units.mapEquiv (separableClosureRingEquiv K L σ).toMulEquiv).toAdditive
  have hc (g : AbsoluteGaloisGroup L) (x : UnitsCoeff K) :
      c.symm (φ g • x) = g • c.symm x := by
    apply c.injective
    rw [c.apply_symm_apply]
    apply Additive.toMul.injective
    apply Units.ext
    -- The coefficient actions are evaluation by field automorphisms; taking values exposes
    -- the conjugation formula supplied by the absolute-Galois-group equivalence.
    change (φ g) (x.toMul : SeparableClosure K) =
      separableClosureRingEquiv K L σ
        (g ((separableClosureRingEquiv K L σ).symm (x.toMul : SeparableClosure K)))
    exact absoluteGaloisGroupEquivFixingSubgroup_apply K L σ g _
  exact (unitsRepH2Equiv K).symm.trans
    ((ContCohomology.explicitMap2Equiv (AbsoluteGaloisGroup K) (UnitsCoeff K)
      (AbsoluteGaloisGroup L) (UnitsCoeff L) φ c.symm
      continuous_of_discreteTopology continuous_of_discreteTopology hc).trans
        (unitsRepH2Equiv L))

end TauCeti.ClassFieldTheory
