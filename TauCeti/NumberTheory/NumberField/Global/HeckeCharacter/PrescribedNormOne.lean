/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Archimedean
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Residue
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology
import TauCeti.Topology.Algebra.Group.CharacterExtension

/-!
# Automorphic characters of norm-one ideles with prescribed local factors

The archimedean weight and the tame residue characters prescribe a continuous character
on the norm-one ideles with integral finite part. This prescription extends to an automorphic
character precisely when it is trivial on the principal points of this subgroup. In particular
the extension does not require any finiteness theorem for a norm-one ray class group.

The criterion is the norm-one analogue of the unit compatibility for algebraic Hecke
characters (A. Raghuram, *An introduction to the theory of algebraic Hecke characters*,
arXiv:2207.03399, §4). The norm-one formulation follows
`New.AutChar.exists_hasWeight_of_prod_eq_one` in `grh/src/Lib/ClassField/HeckeCharacter/Basic.lean`
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open IsDedekindDomain NumberField
open IsDedekindDomain.FiniteAdeleRing (integralUnits)

namespace TauCeti.GlobalNumberFields

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

local notation "U" => MonoidHom.ker (ContinuousMonoidHom.toMonoidHom
  (ideleNormMap (maximalRealSubfield E) E))

/-- Given a weight and a finite family of residue characters, there exists a continuous
character of the norm-one ideles that is trivial on principal norm-one ideles and has the
prescribed local product on integral ideles if and only if that product is trivial on
integral principal norm-one ideles. The weight uses the representative embeddings of the
infinite places. -/
theorem exists_normOneCharacter_iff (e : InfinitePlace E → ℤ)
    {S : Finset (HeightOneSpectrum (𝓞 E))}
    (ψ : (w : S) → (IsLocalRing.ResidueField (w.val.adicCompletionIntegers E))ˣ →* Circle) :
    (∃ μ : U →ₜ* Circle,
      (∀ x : U, x.val ∈ IdeleGroup.principalSubgroup (𝓞 E) E → μ x = 1) ∧
      ∀ (x : U) (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E),
        μ x = normOneWeightCharacter e x *
          ∏ w : S, ψ w (w.val.integralUnitsReduction ⟨_, hx⟩)) ↔
    ∀ (x : U) (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E),
      x.val ∈ IdeleGroup.principalSubgroup (𝓞 E) E →
      normOneWeightCharacter e x * ∏ w : S, ψ w (w.val.integralUnitsReduction ⟨_, hx⟩) = 1 := by
  classical
  constructor
  · rintro ⟨μ, hprincipal, hlocal⟩ x hx hp
    exact (hlocal x hx).symm.trans (hprincipal x hp)
  · intro h
    let F : U →* _ := (IdeleGroup.toFiniteIdele (𝓞 E) E).comp (Subgroup.subtype U)
    let H : Subgroup U := (integralUnits (𝓞 E) E).comap F
    let P : Subgroup U := (IdeleGroup.principalSubgroup (𝓞 E) E).comap (Subgroup.subtype U)
    have hF : Continuous F :=
      (IdeleGroup.continuous_toFiniteIdele (𝓞 E) E).comp continuous_subtypeVal
    have hH : IsOpen (H : Set U) := (isOpen_integralUnits (𝓞 E) E).preimage hF
    let g : H →* integralUnits (𝓞 E) E := (F.comp H.subtype).codRestrict _ Subtype.property
    have hg : Continuous g := (hF.comp continuous_subtypeVal).subtype_mk _
    let χw (w : S) : H →ₜ* Circle :=
      ⟨(ψ w).comp ((w.val.integralUnitsReduction).comp g),
        ((w.val.isLocallyConstant_integralUnitsReduction.comp_continuous hg).comp (ψ w)).continuous⟩
    let χ : H →ₜ* Circle :=
      ⟨(normOneWeightCharacter e).toMonoidHom.domRestrict H,
        (normOneWeightCharacter e).continuous.comp continuous_subtypeVal⟩ * ∏ w : S, χw w
    have hχ (x : H) : χ x = normOneWeightCharacter e x.val *
        ∏ w : S, ψ w (w.val.integralUnitsReduction (g x)) := by
      let ev : (H →ₜ* Circle) →* Circle := ⟨⟨fun k ↦ k x, rfl⟩, fun _ _ ↦ rfl⟩
      calc
        χ x = ev χ := (rfl)
        _ = _ := by
          simp only [χ, map_mul, map_prod]
          rfl
    let : DivisibleBy (Additive Circle) ℤ :=
      divisibleByOfSMulRightSurj _ _ fun {n} hn ↦ by
        let : NeZero n := ⟨hn⟩
        exact (Circle.isQuotientCoveringMap_zpow n).toIsQuotientMap.surjective
    obtain ⟨μ, hμ, hP⟩ := (χ.exists_domRestrict_eq_and_le_ker_iff (N := P) hH).mpr fun x hx ↦
      (hχ x).trans (h x.val x.property hx)
    refine ⟨μ, fun x hx ↦ hP hx, fun x hx ↦ ?_⟩
    exact (DFunLike.congr_fun hμ (⟨x, hx⟩ : H)).trans (hχ ⟨x, hx⟩)

end TauCeti.GlobalNumberFields
