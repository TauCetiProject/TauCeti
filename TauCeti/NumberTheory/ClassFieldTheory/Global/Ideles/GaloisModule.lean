/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Formation
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Every layer of the idele formation as a Galois module

Let `K` be a number field and `V ◁ U` a finite normal layer of the idele formation
`ideleFormation K`, whose ground subgroup `U` is any open subgroup of `G_K`. Let `E` be the fixed
field of `V`, let `F` be a field over which `E` is an algebra, and let
`e : U ⧸ V ≃* Gal(E/F)` send the class of each `u ∈ U` to the restriction of `u` to `E`.

The coefficient module `(I_{Kˢ})^V` of the layer is the idele group `I_E`, through
`ideleLevelEquiv`. This file proves that, along `e`, this identification intertwines the action of
`U ⧸ V` on the layer with the Galois action of `Gal(E/F)` on `I_E`
(`NormalLayer.ideleLevelEquiv_ρ`). Consequently the cohomology of the layer is the Galois
cohomology `Hⁿ(Gal(E/F), I_E)` in every degree (`NormalLayer.ideleCohomologyEquiv`).

This identification applies in particular to a prime-degree layer `V ◁ U`. It allows a class
constructed place by place in `H²(Gal(E/F), I_E)` to be read as a class of the idele formation,
which is the input required by the prime-degree step in the construction of the global invariant.

## Main results

* `TauCeti.ClassFieldTheory.NormalLayer.ideleLevelEquiv_ρ`: the identification of `I_E` with
  the coefficient module of the layer is equivariant along `e`.
* `TauCeti.ClassFieldTheory.NormalLayer.ideleCohomologyEquiv`: the cohomology of the layer is
  `Hⁿ(Gal(E/F), I_E)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

noncomputable section

open IntermediateField IsDedekindDomain NumberField
open scoped AdeleGaloisAction

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

variable {K : Type} [Field K] [NumberField K]

/-- The Galois action on the idele representation is transport through the corresponding
automorphism of the adele ring. -/
theorem idelesRep_ρ_apply {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
    (σ : Gal(E/F)) (a : (idelesRep F E).V) :
    (idelesRep F E).ρ σ a =
      .ofMul (Units.map (adeleEquiv E E σ.toRingEquiv).toMonoidHom
        (Additive.toMul (α := IdeleGroup (RingOfIntegers E) E) a)) :=
  (Rep.ofMulDistribMulAction_ρ_apply_apply (G := IdeleGroup (RingOfIntegers E) E) σ a).trans <|
    congrArg Additive.ofMul <| Units.ext <|
      (coe_idele_smul σ _).trans (adeleGaloisAction_apply F E σ _)

namespace NormalLayer

variable (L : NormalLayer (AbsoluteGaloisGroup K))
  {E : IntermediateField K (SeparableClosure K)} [NumberField E] {F : Type} [Field F]
  [Algebra F E] (hE : fixedField L.top.toSubgroup = E) {e : L.Gal ≃* Gal(E/F)}
  (he : ∀ (u : L.ground) (x : E),
    ((e u x : E) : SeparableClosure K) = (u : AbsoluteGaloisGroup K) x)

/-! ### The coefficient module -/

include he in
/-- **The coefficient module of a layer of the idele formation is `I_E` as a Galois module**:
if `E` is the fixed field of the top subgroup of the layer and `e : U ⧸ V ≃* Gal(E/F)` sends
the class of each `u` to its restriction to `E`, then `τ ∈ Gal(E/F)` acts on `I_E` as
`e⁻¹ τ` acts on the coefficient module `(I_{Kˢ})^V` of the layer, through
`ideleLevelEquiv`. -/
theorem ideleLevelEquiv_ρ (τ : Gal(E/F)) (a : (idelesRep F E).V) :
    ideleLevelEquiv hE ((idelesRep F E).ρ τ a) =
      (L.rep (ideleFormation K)).ρ (e.symm τ) (ideleLevelEquiv hE a) := by
  obtain ⟨γ, rfl⟩ := e.surjective τ
  rw [MulEquiv.symm_apply_apply]
  induction γ using QuotientGroup.induction_on with | H u =>
    rw [idelesRep_ρ_apply]
    exact Subtype.ext ((ideleLevelEquiv_units_map_adeleEquiv hE
      (u : AbsoluteGaloisGroup K) (e u).toRingEquiv (he u) (Additive.toMul a)).trans
        (L.rep_ρ_mk_apply_coe _ u _).symm)

/-! ### Cohomology -/

/-- **The cohomology of a layer of the idele formation is the Galois cohomology of the ideles**:
if `E` is the fixed field of the top subgroup of the layer and `e : U ⧸ V ≃* Gal(E/F)` sends
the class of each `u` to its restriction to `E`, then
`Hⁿ(U ⧸ V, (I_{Kˢ})^V) ≃ Hⁿ(Gal(E/F), I_E)` in every degree `n`. -/
def ideleCohomologyEquiv (n : ℕ) :
    L.H (ideleFormation K) n ≃+ groupCohomology (idelesRep F E) n :=
  (groupCohomology.mapIso e.symm (ideleLevelEquiv hE).toIntLinearEquiv
    (fun τ ↦ LinearMap.ext (L.ideleLevelEquiv_ρ hE he τ))
    n).toLinearEquiv.toAddEquiv.symm

/-- `ideleCohomologyEquiv` is the inverse of `groupCohomology.mapIso` along `e⁻¹` and
`ideleLevelEquiv`. -/
@[simp]
theorem ideleCohomologyEquiv_apply (n : ℕ) (x : L.H (ideleFormation K) n) :
    L.ideleCohomologyEquiv hE he n x =
      (groupCohomology.mapIso e.symm (ideleLevelEquiv hE).toIntLinearEquiv
        (fun τ ↦ LinearMap.ext (L.ideleLevelEquiv_ρ hE he τ)) n).inv x :=
  (rfl)

/-- The inverse of `ideleCohomologyEquiv` is `groupCohomology.mapIso` along `e⁻¹` and
`ideleLevelEquiv`. -/
@[simp]
theorem ideleCohomologyEquiv_symm_apply (n : ℕ)
    (x : groupCohomology (idelesRep F E) n) :
    (L.ideleCohomologyEquiv hE he n).symm x =
      (groupCohomology.mapIso e.symm (ideleLevelEquiv hE).toIntLinearEquiv
        (fun τ ↦ LinearMap.ext (L.ideleLevelEquiv_ρ hE he τ)) n).hom x :=
  (rfl)

end NormalLayer

end TauCeti.ClassFieldTheory
