/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.Level
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality

/-!
# Every layer of the idele-class formation as a Galois module

Let `K` be a number field and `V ◁ U` a finite normal layer of the idele-class formation
`globalFormation K`, whose ground subgroup `U` is any open subgroup of `G_K`. Let `E` be the fixed
field of `V`, a finite subextension of `Kˢ/K`, let `F` be a field over which `E` is an algebra,
and let `e : U ⧸ V ≃* Gal(E/F)` send the class of each `u ∈ U` to the restriction of `u`
to `E`. Such an `e` is unique when it exists, and it exists when `F` is the fixed field of `U`, by
the Galois correspondence for `Kˢ/K`.

The coefficient module `(C_{Kˢ})^V` of the layer is the idele class group `C_E` of `E`, through
`ideleClassLevelEquiv`. This file proves that, along `e`, this identification intertwines the
action of `U ⧸ V` on the layer with the Galois action of `Gal(E/F)` on `C_E`, the module of
`TauCeti.ClassFieldTheory.ideleClassRep F E` (`NormalLayer.ideleClassLevelEquiv_ρ`).
Consequently the cohomology of the layer is the Galois cohomology `Hⁿ(Gal(E/F), C_E)` in every
degree (`NormalLayer.ideleClassCohomologyEquiv`), its Tate cohomology is the Tate cohomology
`Hⁿ_T(Gal(E/F), C_E)` in every integer degree (`NormalLayer.ideleClassTateCohomologyIso`), and
its Herbrand quotient is `h(C_E)`, computed for the action of `Gal(E/F)`
(`NormalLayer.herbrandQuotient_rep_globalFormation`).

The reductions of `TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree` derive the
vanishing of `H¹` and the bound `#H² ∣ [U : V]` for a layer from the two fundamental inequalities
on all the layers of prime degree inside it, and the ground subgroups of those layers are proper
open subgroups of `G_K` in general. The Herbrand quotient of each such layer is the Herbrand
quotient of the idele classes of a cyclic extension `E/F` of number fields, which
`TauCeti.ClassFieldTheory.herbrandQuotient_ideleClassRep` reduces to the `S`-ideles and the
`S`-units of `E`.

## Main results

* `TauCeti.ClassFieldTheory.NormalLayer.ideleClassLevelEquiv_ρ`: the identification
  of `C_E` with the coefficient module of the layer is equivariant along `e`.
* `TauCeti.ClassFieldTheory.NormalLayer.isIntertwiningMap_ideleClassLevelEquiv`: the same
  statement in the form of a compatible pair, as taken by the change-of-group maps of cohomology.
* `TauCeti.ClassFieldTheory.NormalLayer.ideleClassCohomologyEquiv`: the cohomology of the layer is
  `Hⁿ(Gal(E/F), C_E)`.
* `TauCeti.ClassFieldTheory.NormalLayer.ideleClassTateCohomologyIso`: the Tate cohomology of the
  layer is `Hⁿ_T(Gal(E/F), C_E)`.
* `TauCeti.ClassFieldTheory.NormalLayer.herbrandQuotient_rep_globalFormation`: the Herbrand
  quotient of the layer is `h(C_E)`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §§4–5.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§2 and 4.
-/

public section

noncomputable section

open IntermediateField NumberField
open scoped AdeleGaloisAction

namespace TauCeti.ClassFieldTheory.NormalLayer

variable {K : Type} [Field K] [NumberField K] (L : NormalLayer (AbsoluteGaloisGroup K))
  {E : IntermediateField K (SeparableClosure K)} [NumberField E] {F : Type} [Field F]
  [Algebra F E] (hE : fixedField L.top.toSubgroup = E) {e : L.Gal ≃* Gal(E/F)}
  (he : ∀ (u : L.ground) (x : E),
    ((e u x : E) : SeparableClosure K) = (u : AbsoluteGaloisGroup K) x)

/-! ### The coefficient module -/

include he in
/-- **The coefficient module of a layer of the idele-class formation is `C_E` as a Galois
module**: if `E` is the fixed field of the top subgroup of the layer and `e : U ⧸ V ≃* Gal(E/F)`
sends the class of each `u` to its restriction to `E`, then `τ ∈ Gal(E/F)` acts on `C_E` as
`e⁻¹ τ` acts on the coefficient module `(C_{Kˢ})^V` of the layer, through `ideleClassLevelEquiv`. -/
theorem ideleClassLevelEquiv_ρ (τ : Gal(E/F)) (c : (ideleClassRep F E).V) :
    ideleClassLevelEquiv hE ((ideleClassRep F E).ρ τ c) =
      (L.rep (globalFormation K)).ρ (e.symm τ) (ideleClassLevelEquiv hE c) := by
  obtain ⟨γ, rfl⟩ := e.surjective τ
  rw [MulEquiv.symm_apply_apply]
  induction γ using QuotientGroup.induction_on with | H u => ?_
  obtain ⟨a, rfl⟩ : ∃ a : IdeleGroup (𝓞 E) E,
      (Additive.ofMul (a : IdeleClassGroup (𝓞 E) E) : (ideleClassRep F E).V) = c :=
    (QuotientGroup.mk_surjective (Additive.toMul c)).imp fun _ ha ↦ congrArg Additive.ofMul ha
  -- `e u` acts on the class of an idele `a` of `E` through the adele ring of `E`, which is how `u`
  -- acts on the class of `a` read as an idele of `Kˢ`.
  rw [ideleClassRep_ρ_mk]
  exact Subtype.ext ((ideleClassLevelEquiv_units_map_adeleEquiv hE (u : AbsoluteGaloisGroup K)
    (e u).toRingEquiv (he u) a).trans (L.rep_ρ_mk_apply_coe _ u _).symm)

include he in
/-- `ideleClassLevelEquiv` and the inverse of `e` form a compatible pair, in the form taken by the
change-of-group maps of Tate cohomology. -/
theorem isIntertwiningMap_ideleClassLevelEquiv :
    (ideleClassRep F E).ρ.IsIntertwiningMap
      ((L.rep (globalFormation K)).ρ.comp (e.symm : Gal(E/F) →* L.Gal))
      ((ideleClassLevelEquiv hE : (ideleClassRep F E).V ≃+ (L.rep (globalFormation K)).V)
        |>.toIntLinearEquiv.toLinearMap) :=
  ⟨L.ideleClassLevelEquiv_ρ hE he⟩

/-! ### Cohomology and the Herbrand quotient -/

/-- **The cohomology of a layer of the idele-class formation is the Galois cohomology of the
idele classes**: if `E` is the fixed field of the top subgroup of the layer and
`e : U ⧸ V ≃* Gal(E/F)` sends the class of each `u` to its restriction to `E`, then
`Hⁿ(U ⧸ V, (C_{Kˢ})^V) ≃ Hⁿ(Gal(E/F), C_E)` in every degree `n`. -/
def ideleClassCohomologyEquiv (n : ℕ) :
    L.H (globalFormation K) n ≃+ groupCohomology (ideleClassRep F E) n :=
  (groupCohomology.mapIso e.symm (ideleClassLevelEquiv hE).toIntLinearEquiv
    (fun τ ↦ LinearMap.ext (L.ideleClassLevelEquiv_ρ hE he τ))
    n).toLinearEquiv.toAddEquiv.symm

/-- `ideleClassCohomologyEquiv` is the inverse of the isomorphism `groupCohomology.mapIso` along
`e⁻¹` and `ideleClassLevelEquiv`. -/
@[simp]
theorem ideleClassCohomologyEquiv_apply (n : ℕ) (x : L.H (globalFormation K) n) :
    L.ideleClassCohomologyEquiv hE he n x =
      (groupCohomology.mapIso e.symm (ideleClassLevelEquiv hE).toIntLinearEquiv
        (fun τ ↦ LinearMap.ext (L.ideleClassLevelEquiv_ρ hE he τ)) n).inv x :=
  (rfl)

/-- The inverse of `ideleClassCohomologyEquiv` is the isomorphism `groupCohomology.mapIso` along
`e⁻¹` and `ideleClassLevelEquiv`. -/
@[simp]
theorem ideleClassCohomologyEquiv_symm_apply (n : ℕ)
    (x : groupCohomology (ideleClassRep F E) n) :
    (L.ideleClassCohomologyEquiv hE he n).symm x =
      (groupCohomology.mapIso e.symm (ideleClassLevelEquiv hE).toIntLinearEquiv
        (fun τ ↦ LinearMap.ext (L.ideleClassLevelEquiv_ρ hE he τ)) n).hom x :=
  (rfl)

variable [NumberField F]

/-- **The Tate cohomology of a layer of the idele-class formation is the Tate cohomology of the
idele classes**: if `E` is the fixed field of the top subgroup of the layer and
`e : U ⧸ V ≃* Gal(E/F)` sends the class of each `u` to its restriction to `E`, then
`Hⁿ_T(U ⧸ V, (C_{Kˢ})^V) ≅ Hⁿ_T(Gal(E/F), C_E)` in every integer degree `n`. -/
def ideleClassTateCohomologyIso (n : ℤ) :
    L.TateH (globalFormation K) n ≅ tateCohomology (ideleClassRep F E) n :=
  (TateCohomology.mapIso (L.isIntertwiningMap_ideleClassLevelEquiv hE he) n).symm

/-- The forward map of `ideleClassTateCohomologyIso` is the inverse of the isomorphism
`TateCohomology.mapIso` along `e⁻¹` and `ideleClassLevelEquiv`. -/
@[simp]
theorem ideleClassTateCohomologyIso_hom (n : ℤ) :
    (L.ideleClassTateCohomologyIso hE he n).hom =
      (TateCohomology.mapIso (L.isIntertwiningMap_ideleClassLevelEquiv hE he) n).inv :=
  (rfl)

/-- The inverse of `ideleClassTateCohomologyIso` is the isomorphism `TateCohomology.mapIso` along
`e⁻¹` and `ideleClassLevelEquiv`. -/
@[simp]
theorem ideleClassTateCohomologyIso_inv (n : ℤ) :
    (L.ideleClassTateCohomologyIso hE he n).inv =
      (TateCohomology.mapIso (L.isIntertwiningMap_ideleClassLevelEquiv hE he) n).hom :=
  (rfl)

include hE he in
/-- **The Herbrand quotient of a layer of the idele-class formation is that of the idele
classes**: if `E` is the fixed field of the top subgroup of the layer and `e : U ⧸ V ≃* Gal(E/F)`
sends the class of each `u` to its restriction to `E`, then the coefficient module of the layer has
Herbrand quotient `h(C_E)`, computed for the action of `Gal(E/F)`. -/
theorem herbrandQuotient_rep_globalFormation :
    TateCohomology.herbrandQuotient (L.rep (globalFormation K)) =
      TateCohomology.herbrandQuotient (ideleClassRep F E) := by
  have h :=
    TateCohomology.natCard_tateCohomology_eq (L.isIntertwiningMap_ideleClassLevelEquiv hE he)
  rw [TateCohomology.herbrandQuotient_def, TateCohomology.herbrandQuotient_def, h 0, h (-1)]

end TauCeti.ClassFieldTheory.NormalLayer
