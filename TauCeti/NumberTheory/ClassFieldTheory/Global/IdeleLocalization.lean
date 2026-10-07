/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.BaseChange
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Coefficients
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.FiniteAdele
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.InfiniteAdele
import Mathlib.RingTheory.DedekindDomain.Different
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Unramified
import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The localization of idele cohomology at a place

Let `K` be a number field, `v` a finite place of `K` with completion `K_v`, and `G_K`, `G_{K_v}`
the absolute Galois groups. A `K`-embedding `τ : Kˢ → K_vˢ` of separable closures picks out, for
every finite Galois subextension `E` of `Kˢ/K`, one place of `E` above `v`, together with an
embedding of its completion into `K_vˢ`. Reading the component of an idele of `E` at that place
in `K_vˢ` gives the **coordinate at `v`** of the ideles of `Kˢ`,

```text
ideleCoeffComponent τ : I_{Kˢ} → (K_vˢ)ˣ,
```

which is equivariant along the decomposition map `absoluteGaloisGroupMap τ : G_{K_v} → G_K`
(`ideleCoeffComponent_smul`) and restricts to `τ` on the principal ideles
(`ideleCoeffComponent_principalIdele`). It is built without topology on `K_vˢ`: the components above
`v` of an idele of `E` form a unit of `K_v ⊗[K] E` (`TauCeti.finiteAdeleSemilocalHom`), which
`a ⊗ x ↦ a τ(x)` maps to `K_vˢ`.

Pulling back along this compatible pair is the **localization of idele cohomology at `v`**,

```text
ideleBrLocalization v : H²(G_K, I_{Kˢ}) → Br K_v,
```

the component at `v` of a global idele class. It does not depend on `τ`
(`ideleBrLocalization_apply`): changing `τ` by `h ∈ G_K` changes the pair by the inner
automorphism of `h`, which acts trivially on cohomology. On the image of
`H²(G_K, (Kˢ)ˣ) = Br K` under the principal ideles it is the localization `Br K → Br K_v` of
global Brauer classes (`ideleBrLocalization_principalIdele`). As for a global Brauer class, only
finitely many of the localizations of a class of `H²(G_K, I_{Kˢ})` are nonzero
(`finite_setOfPred_ideleBrLocalization_ne_zero`), so the local invariants of an idele class have
a finite sum.

The same construction works at an infinite place `w` of `K`, with completion `K_w = ℝ` or `ℂ`:
the components above `w` of an idele of `E` form a unit of `K_w ⊗[K] E`
(`TauCeti.GlobalNumberFields.infiniteAdeleSemilocalHom`), and an embedding
`τ : Kˢ → K_wˢ` gives the coordinate `ideleCoeffInfiniteComponent τ : I_{Kˢ} → (K_wˢ)ˣ` and the
localization

```text
ideleInfiniteBrLocalization w : H²(G_K, I_{Kˢ}) → Br K_w,
```

with the same properties. Both are instances of one construction from the semi-local components
of adeles, which only uses that these components are natural in `E` and send `x ∈ E` to `1 ⊗ x`.

## Main definitions

* `TauCeti.ClassFieldTheory.ideleCoeffComponent τ`: the coordinate at `v` of the ideles of `Kˢ`
  along `τ`.
* `TauCeti.ClassFieldTheory.ideleBrLocalization v`: the localization
  `H²(G_K, I_{Kˢ}) → Br K_v`.
* `TauCeti.ClassFieldTheory.ideleCoeffInfiniteComponent τ`,
  `TauCeti.ClassFieldTheory.ideleInfiniteBrLocalization w`: the coordinate and the localization at
  an infinite place `w`.

## Main results

* `TauCeti.ClassFieldTheory.ideleCoeffComponent_smul`: the coordinate is equivariant along
  `G_{K_v} → G_K`.
* `TauCeti.ClassFieldTheory.ideleCoeffComponent_comp`: changing `τ` by `h ∈ G_K` precomposes the
  coordinate with the action of `h`.
* `TauCeti.ClassFieldTheory.ideleCoeffComponent_principalIdele`: on principal ideles the coordinate
  is `τ`.
* `TauCeti.ClassFieldTheory.ideleBrLocalization_apply`: the localization is the pullback along the
  pair of any `τ`.
* `TauCeti.ClassFieldTheory.ideleBrLocalization_principalIdele`: on principal idele classes the
  localization is `brBaseChange K K_v`.
* `TauCeti.ClassFieldTheory.ideleInfiniteBrLocalization_apply`,
  `TauCeti.ClassFieldTheory.ideleInfiniteBrLocalization_principalIdele`: the same two statements
  at an infinite place.
* `TauCeti.ClassFieldTheory.toMul_ideleCoeffComponent_ideleCoeffOf_eq_map_ideleFiniteCoord`: for
  `τ` extending an embedding of a completion `E_w` above `v`, the coordinate at `v` of an idele of
  `E` is its component at `w`.
* `TauCeti.ClassFieldTheory.finite_setOfPred_ideleBrLocalization_ne_zero`: a class has nonzero
  localization at only finitely many finite places.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (8.1.17).
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField ContCohomology
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

/-! ### Semi-local components of adeles

The construction is the same at finite and at infinite places: all it uses is the family of
semi-local components `𝔸_E → F ⊗[K] E` of the adeles of the finite Galois subextensions `E` of
`Kˢ/K`, for the completion `F` of `K` at the place, natural in `E`. -/

section Generic

variable (K) in
/-- Semi-local components of the adeles of the finite Galois subextensions of `Kˢ/K` in a field
`F` over `K`: a ring homomorphism `𝔸_E → F ⊗[K] E` for every `E`, sending `x ∈ E` to `1 ⊗ x` and
natural along inclusions and `K`-automorphisms. -/
private structure AdeleSemilocal (F : Type) [Field F] [Algebra K F] where
  /-- The semi-local component of an adele of `E`. -/
  hom (E : Ω) : AdeleRing (𝓞 E) E →+* F ⊗[K] E
  hom_algebraMap (E : Ω) (x : E) : hom E (algebraMap E _ x) = (1 : F) ⊗ₜ[K] x
  hom_adeleTransition {E E' : Ω} (h : E ≤ E') (a : AdeleRing (𝓞 E) E) :
    hom E' (adeleTransition h a) =
      Algebra.TensorProduct.map (AlgHom.id F F) (IntermediateField.inclusion h) (hom E a)
  hom_adeleGaloisAction (E : Ω) (σ : E ≃ₐ[K] E) (a : AdeleRing (𝓞 E) E) :
    hom E (GlobalNumberFields.adeleGaloisAction K E σ a) =
      Algebra.TensorProduct.map (AlgHom.id F F) (σ : E →ₐ[K] E) (hom E a)

variable {F : Type} [Field F] [Algebra K F]

/-- The `F`-algebra map `F ⊗[K] E → Fˢ`, `a ⊗ x ↦ a τ(x)`. -/
private def semilocalLift (τ : SeparableClosure K →ₐ[K] SeparableClosure F) (E : Ω) :
    F ⊗[K] E →ₐ[F] SeparableClosure F :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (τ.comp (IsScalarTower.toAlgHom K E (SeparableClosure K))) fun _ _ ↦ .all _ _

omit [NumberField K] in
@[simp]
private theorem semilocalLift_tmul (τ : SeparableClosure K →ₐ[K] SeparableClosure F) (E : Ω)
    (a : F) (x : E) :
    semilocalLift τ E (a ⊗ₜ x) =
      algebraMap F (SeparableClosure F) a * τ (x : SeparableClosure K) := by
  simp [semilocalLift]

/-- The coordinate along `τ` of an adele of `E`: its semi-local component, mapped to `Fˢ` by
`semilocalLift`. -/
private def adeleComponent (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F) (E : Ω) :
    AdeleRing (𝓞 E) E →+* SeparableClosure F :=
  (semilocalLift τ E).toRingHom.comp (P.hom E)

private theorem adeleComponent_apply (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F) (E : Ω) (a : AdeleRing (𝓞 E) E) :
    adeleComponent P τ E a = semilocalLift τ E (P.hom E a) :=
  (rfl)

/-- The coordinate is compatible with the extension maps of adeles. -/
private theorem adeleComponent_adeleTransition (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F) {E E' : Ω} (h : E ≤ E')
    (a : AdeleRing (𝓞 E) E) :
    adeleComponent P τ E' (adeleTransition h a) = adeleComponent P τ E a := by
  rw [adeleComponent_apply, adeleComponent_apply, P.hom_adeleTransition, ← AlgHom.comp_apply]
  congr 1
  ext x
  -- The inclusion `E → E'` does not move `x` in `Kˢ`.
  simp

/-- Acting on an adele of `E` by `h ∈ G_K` and then taking the coordinate along `τ` is taking the
coordinate along `τ ∘ h`. -/
private theorem adeleComponent_adeleGaloisAction (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (h : AbsoluteGaloisGroup K) (E : Ω) (a : AdeleRing (𝓞 E) E) :
    adeleComponent P τ E (GlobalNumberFields.adeleGaloisAction K E (h.restrictNormal E) a) =
      adeleComponent P (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) E a := by
  rw [adeleComponent_apply, adeleComponent_apply, P.hom_adeleGaloisAction, ← AlgHom.comp_apply]
  congr 1
  ext x
  simp [AlgEquiv.restrictNormal_apply]

/-- Composing `τ` with `g ∈ G_F` composes the coordinate with `g`. -/
private theorem adeleComponent_comp_left (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (g : AbsoluteGaloisGroup F) (E : Ω) (a : AdeleRing (𝓞 E) E) :
    adeleComponent P (((g : SeparableClosure F →ₐ[F] SeparableClosure F).restrictScalars K).comp τ)
      E a = g (adeleComponent P τ E a) := by
  rw [adeleComponent_apply, adeleComponent_apply, ← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply]
  congr 1
  ext x
  simp

/-- The coordinate along `τ` of the ideles of `Kˢ`. -/
private def ideleComponent (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F) :
    IdeleCoeff K →+ UnitsCoeff F :=
  IdeleCoeff.lift K (fun E ↦ (Units.map (adeleComponent P τ E).toMonoidHom).toAdditive)
    fun E E' h a ↦ Additive.toMul.injective (Units.ext (by simp [adeleComponent_adeleTransition]))

private theorem toMul_ideleComponent_ideleCoeffOf (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F) (E : Ω) (a : IdeleGroup (𝓞 E) E) :
    ((ideleComponent P τ (ideleCoeffOf K E (.ofMul a))).toMul : SeparableClosure F) =
      adeleComponent P τ E a := by
  simp [ideleComponent, IdeleCoeff.lift_ideleCoeffOf]

private theorem ideleComponent_comp (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (h : AbsoluteGaloisGroup K) (x : IdeleCoeff K) :
    ideleComponent P (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) x =
      ideleComponent P τ (h • x) := by
  obtain ⟨E, a, rfl⟩ := exists_ideleCoeffOf_eq x
  refine Additive.toMul.injective (Units.ext ?_)
  simp [smul_ideleCoeffOf, toMul_ideleComponent_ideleCoeffOf, adeleComponent_adeleGaloisAction]

private theorem ideleComponent_smul (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (g : AbsoluteGaloisGroup F) (x : IdeleCoeff K) :
    ideleComponent P τ (absoluteGaloisGroupMap τ g • x) = g • ideleComponent P τ x := by
  rw [← ideleComponent_comp]
  have hτ : τ.comp (absoluteGaloisGroupMap τ g : SeparableClosure K →ₐ[K] SeparableClosure K) =
      ((g : SeparableClosure F →ₐ[F] SeparableClosure F).restrictScalars K).comp τ :=
    AlgHom.ext fun y ↦ absoluteGaloisGroupMap_commutes τ g y
  obtain ⟨E, a, rfl⟩ := exists_ideleCoeffOf_eq x
  refine Additive.toMul.injective (Units.ext ?_)
  rw [hτ]
  simp [toMul_ideleComponent_ideleCoeffOf, adeleComponent_comp_left, Additive.toMul_smul,
    AlgEquiv.smul_units_def]

private theorem ideleComponent_principalIdele (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (x : UnitsCoeff K) :
    ideleComponent P τ (principalIdele K x) = unitsCoeffBaseChange τ x := by
  -- `x` is a unit of the finite Galois subextension it generates.
  let E : Ω := FiniteGaloisIntermediateField.adjoin K {(x.toMul : SeparableClosure K)}
  have hx : (x.toMul : SeparableClosure K) ∈ (E : IntermediateField K (SeparableClosure K)) :=
    FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  let u : Eˣ := Units.mk0 ⟨x.toMul, hx⟩ fun h ↦ x.toMul.ne_zero (congrArg Subtype.val h)
  have hxu : x = .ofMul (Units.map (algebraMap E (SeparableClosure K)).toMonoidHom u) :=
    Additive.toMul.injective (Units.ext rfl)
  refine Additive.toMul.injective (Units.ext ?_)
  rw [hxu, principalIdele_ofMul_map_algebraMap]
  simp [toMul_ideleComponent_ideleCoeffOf, adeleComponent_apply, P.hom_algebraMap]

/-- The localization `H²(G_K, I_{Kˢ}) → Br F` along the semi-local components `P`. -/
private def semilocalBrLocalization (P : AdeleSemilocal K F) :
    H2 (AbsoluteGaloisGroup K) (IdeleCoeff K) →+ Br F :=
  (unitsRepH2Equiv F : H2 (AbsoluteGaloisGroup F) (UnitsCoeff F) →+ Br F).comp
    (explicitMap2 (AbsoluteGaloisGroup K) (IdeleCoeff K) (AbsoluteGaloisGroup F) (UnitsCoeff F)
      (absoluteGaloisGroupMap IsSepClosed.lift) (ideleComponent P IsSepClosed.lift)
      continuous_of_discreteTopology (ideleComponent_smul P IsSepClosed.lift))

private theorem semilocalBrLocalization_apply (P : AdeleSemilocal K F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    semilocalBrLocalization P x =
      unitsRepH2Equiv F (explicitMap2 (AbsoluteGaloisGroup K) (IdeleCoeff K)
        (AbsoluteGaloisGroup F) (UnitsCoeff F) (absoluteGaloisGroupMap τ) (ideleComponent P τ)
        continuous_of_discreteTopology (ideleComponent_smul P τ) x) := by
  rw [semilocalBrLocalization,
    explicitMap2_absoluteGaloisGroupMap_eq K F (fun τ ↦ ideleComponent P τ)
    (ideleComponent_smul P) (ideleComponent_comp P) IsSepClosed.lift τ,
    AddMonoidHom.comp_apply, AddMonoidHom.coe_ofClass]

private theorem semilocalBrLocalization_principalIdele (P : AdeleSemilocal K F)
    (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    semilocalBrLocalization P (explicitCoeff2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (principalIdele K) continuous_of_discreteTopology x) =
      brBaseChange K F (unitsRepH2Equiv K x) := by
  let τ : SeparableClosure K →ₐ[K] SeparableClosure F := IsSepClosed.lift
  -- Pulling back along the principal ideles and then along the pair of `τ` is pulling back along
  -- the composite pair, which is `(absoluteGaloisGroupMap τ, unitsCoeffBaseChange τ)`.
  have hcomp := DFunLike.congr_fun (explicitMap2_comp (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup K) (IdeleCoeff K) (ContinuousMonoidHom.id _)
    (principalIdele K : UnitsCoeff K →+ IdeleCoeff K) continuous_of_discreteTopology
    (fun g m ↦ map_smul (principalIdele K) g m) (AbsoluteGaloisGroup F) (UnitsCoeff F)
    (absoluteGaloisGroupMap τ) (ideleComponent P τ) continuous_of_discreteTopology
    (ideleComponent_smul P τ)) x
  have hpair := explicitMap2_congr_of_eq (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup F) (UnitsCoeff F)
    ((ContinuousMonoidHom.id _).comp (absoluteGaloisGroupMap τ)) (absoluteGaloisGroupMap τ)
    ((ideleComponent P τ).comp (principalIdele K : UnitsCoeff K →+ IdeleCoeff K))
    (unitsCoeffBaseChange τ) (hf := continuous_of_discreteTopology)
    (hq := continuous_of_discreteTopology) (hψ := unitsCoeffBaseChange_smul τ)
    (hφ := fun g m ↦ by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ContinuousMonoidHom.comp_toFun]
      exact (congrArg (ideleComponent P τ) (map_smul (principalIdele K) _ m)).trans
        (ideleComponent_smul P τ g _))
    (ContinuousMonoidHom.ext fun _ ↦ rfl)
    (AddMonoidHom.ext fun y ↦ ideleComponent_principalIdele P τ y)
  rw [semilocalBrLocalization_apply P τ, brBaseChange_apply K _ τ, AddEquiv.symm_apply_apply,
    explicitCoeff2_eq_explicitMap2]
  exact congrArg _ (hcomp.symm.trans (DFunLike.congr_fun hpair x))

end Generic

/-! ### The localization at a finite place -/

section Finite

/-- The semi-local components above a finite place `v` of the finite parts of adeles. -/
private def finiteAdeleSemilocal (v : HeightOneSpectrum (𝓞 K)) :
    AdeleSemilocal K (v.adicCompletion K) where
  hom E := (finiteAdeleSemilocalHom E v).comp (RingHom.snd (InfiniteAdeleRing E) _)
  hom_algebraMap E x := finiteAdeleSemilocalHom_algebraMap x
  hom_adeleTransition {E E'} h a := by
    let := (IntermediateField.inclusion h).toRingHom.toAlgebra
    have : IsScalarTower K E E' := .of_algebraMap_eq fun _ ↦ rfl
    -- With this `Algebra E E'` instance, `algebraMap E E'` is the inclusion `E → E'`.
    rw [show IntermediateField.inclusion h = IsScalarTower.toAlgHom K E E' from
      AlgHom.ext fun _ ↦ rfl]
    -- `hom E'` is the semi-local component of the finite part `a.2`.
    exact (congrArg (finiteAdeleSemilocalHom E' v) (adeleTransition_snd h a)).trans
      (finiteAdeleSemilocalHom_finiteAdeleExtension v a.2)
  hom_adeleGaloisAction E σ a := by
    have ha : (GlobalNumberFields.adeleGaloisAction K E σ a).2 =
        GlobalNumberFields.finiteAdeleEquiv E E σ.toRingEquiv a.2 := by
      rw [GlobalNumberFields.adeleGaloisAction_apply, GlobalNumberFields.adeleEquiv_snd]
    exact (congrArg (finiteAdeleSemilocalHom E v) ha).trans
      (finiteAdeleSemilocalHom_finiteAdeleEquiv v σ a.2)

variable (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

/-- **The coordinate at `v` of the ideles of `Kˢ`** along a `K`-embedding
`τ : Kˢ →ₐ[K] K_vˢ` of separable closures: an idele `a` of a finite Galois subextension `E` of
`Kˢ/K` goes to the image of its components above `v`, read in `K_v ⊗[K] E`, under the
`K_v`-algebra map `a ⊗ x ↦ a τ(x)` to `K_vˢ` (`toMul_ideleCoeffComponent_ideleCoeffOf`). A ring
homomorphism from `K_v ⊗[K] E ≃ ∏_{w ∣ v} E_w` to a field factors through a single factor `E_w`,
so this reads the component of the idele at one place `w` of `E` above `v`, embedded in
`K_vˢ`. -/
def ideleCoeffComponent : IdeleCoeff K →+ UnitsCoeff (v.adicCompletion K) :=
  ideleComponent (finiteAdeleSemilocal v) τ

/-- **The coordinate at `v` of an idele of `E`**: the image of its components above `v`, read in
`K_v ⊗[K] E`, under `a ⊗ x ↦ a τ(x)`. -/
theorem toMul_ideleCoeffComponent_ideleCoeffOf (E : Ω) (a : IdeleGroup (𝓞 E) E) :
    ((ideleCoeffComponent τ (ideleCoeffOf K E (.ofMul a))).toMul :
      SeparableClosure (v.adicCompletion K)) =
      Algebra.TensorProduct.lift (Algebra.ofId _ _)
        (τ.comp (IsScalarTower.toAlgHom K E (SeparableClosure K))) (fun _ _ ↦ .all _ _)
        (finiteAdeleSemilocalHom E v (a : AdeleRing (𝓞 E) E).2) :=
  toMul_ideleComponent_ideleCoeffOf (finiteAdeleSemilocal v) τ E a

/-- **Changing the embedding by an automorphism** `h` of `Kˢ` precomposes the coordinate at `v`
with the action of `h` on the ideles. -/
theorem ideleCoeffComponent_comp (h : AbsoluteGaloisGroup K) (x : IdeleCoeff K) :
    ideleCoeffComponent (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) x =
      ideleCoeffComponent τ (h • x) :=
  ideleComponent_comp (finiteAdeleSemilocal v) τ h x

/-- **The coordinate at `v` is equivariant** along the decomposition map
`absoluteGaloisGroupMap τ : G_{K_v} → G_K`. -/
theorem ideleCoeffComponent_smul (g : AbsoluteGaloisGroup (v.adicCompletion K)) (x : IdeleCoeff K) :
    ideleCoeffComponent τ (absoluteGaloisGroupMap τ g • x) = g • ideleCoeffComponent τ x :=
  ideleComponent_smul (finiteAdeleSemilocal v) τ g x

/-- **On principal ideles the coordinate at `v` is `τ`**: the coordinate of the principal idele
of a unit `x` of `Kˢ` is `τ x`. -/
@[simp]
theorem ideleCoeffComponent_principalIdele (x : UnitsCoeff K) :
    ideleCoeffComponent τ (principalIdele K x) = unitsCoeffBaseChange τ x :=
  ideleComponent_principalIdele (finiteAdeleSemilocal v) τ x

variable (v) in
/-- **The localization of idele cohomology at a finite place** `v`,
`H²(G_K, I_{Kˢ}) → Br K_v`: the pullback along the decomposition map
`G_{K_v} → G_K` and the coordinate at `v` of the ideles (`ideleCoeffComponent`) of an embedding of
separable closures `Kˢ → K_vˢ`, followed by the identification of `H²(G_{K_v}, (K_vˢ)ˣ)` with
`Br K_v`. It does not depend on the embedding (`ideleBrLocalization_apply`). -/
def ideleBrLocalization : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K) →+ Br (v.adicCompletion K) :=
  semilocalBrLocalization (finiteAdeleSemilocal v)

/-- **The localization of idele cohomology is the pullback along any embedding** `τ` of separable
closures, through the decomposition map of `τ` and the coordinate at `v` along `τ`. -/
theorem ideleBrLocalization_apply (x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    ideleBrLocalization v x =
      unitsRepH2Equiv (v.adicCompletion K)
        (explicitMap2 (AbsoluteGaloisGroup K) (IdeleCoeff K)
          (AbsoluteGaloisGroup (v.adicCompletion K)) (UnitsCoeff (v.adicCompletion K))
          (absoluteGaloisGroupMap τ) (ideleCoeffComponent τ) continuous_of_discreteTopology
          (ideleCoeffComponent_smul τ) x) :=
  semilocalBrLocalization_apply (finiteAdeleSemilocal v) τ x

/-- **On principal idele classes, the localization is the localization of Brauer classes**: the
class in `H²(G_K, I_{Kˢ})` of a Brauer class `x ∈ Br K = H²(G_K, (Kˢ)ˣ)`, along the principal
ideles, localizes at `v` to the base change of `x` to `K_v`. -/
theorem ideleBrLocalization_principalIdele (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    ideleBrLocalization v (explicitCoeff2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (principalIdele K) continuous_of_discreteTopology x) =
      brBaseChange K (v.adicCompletion K) (unitsRepH2Equiv K x) :=
  semilocalBrLocalization_principalIdele (finiteAdeleSemilocal v) x

end Finite

/-! ### The localization at an infinite place -/

section Infinite

variable {w : InfinitePlace K}

/-- The semi-local components above an infinite place `w` of the infinite parts of adeles. -/
private def infiniteAdeleSemilocal (w : InfinitePlace K) : AdeleSemilocal K w.Completion where
  hom E := (GlobalNumberFields.infiniteAdeleSemilocalHom E w).comp
    (RingHom.fst _ (FiniteAdeleRing (𝓞 E) E))
  hom_algebraMap E x := GlobalNumberFields.infiniteAdeleSemilocalHom_algebraMap x
  hom_adeleTransition {E E'} h a := by
    let := (IntermediateField.inclusion h).toRingHom.toAlgebra
    have : IsScalarTower K E E' := .of_algebraMap_eq fun _ ↦ rfl
    -- With this `Algebra E E'` instance, `algebraMap E E'` is the inclusion `E → E'`.
    rw [show IntermediateField.inclusion h = IsScalarTower.toAlgHom K E E' from
      AlgHom.ext fun _ ↦ rfl]
    -- `hom E'` is the semi-local component of the infinite part `a.1`.
    exact (congrArg (GlobalNumberFields.infiniteAdeleSemilocalHom E' w)
      (adeleTransition_fst h a)).trans
      (GlobalNumberFields.infiniteAdeleSemilocalHom_infiniteAdeleExtension w a.1)
  hom_adeleGaloisAction E σ a := by
    have ha : (GlobalNumberFields.adeleGaloisAction K E σ a).1 =
        GlobalNumberFields.infiniteAdeleEquiv E E σ.toRingEquiv a.1 := by
      rw [GlobalNumberFields.adeleGaloisAction_apply, GlobalNumberFields.adeleEquiv_fst]
    exact (congrArg (GlobalNumberFields.infiniteAdeleSemilocalHom E w) ha).trans
      (GlobalNumberFields.infiniteAdeleSemilocalHom_infiniteAdeleEquiv w σ a.1)

variable (τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion)

/-- **The coordinate at an infinite place `w` of the ideles of `Kˢ`** along a `K`-embedding
`τ : Kˢ →ₐ[K] K_wˢ` of separable closures: an idele `a` of a finite Galois subextension `E` of
`Kˢ/K` goes to the image of its components above `w`, read in `K_w ⊗[K] E`, under the
`K_w`-algebra map `a ⊗ x ↦ a τ(x)` to `K_wˢ` (`toMul_ideleCoeffInfiniteComponent_ideleCoeffOf`).
It reads the component of the idele at one place of `E` above `w`, embedded in `K_wˢ`. -/
def ideleCoeffInfiniteComponent : IdeleCoeff K →+ UnitsCoeff w.Completion :=
  ideleComponent (infiniteAdeleSemilocal w) τ

/-- **The coordinate at `w` of an idele of `E`**: the image of its components above `w`, read in
`K_w ⊗[K] E`, under `a ⊗ x ↦ a τ(x)`. -/
theorem toMul_ideleCoeffInfiniteComponent_ideleCoeffOf (E : Ω) (a : IdeleGroup (𝓞 E) E) :
    ((ideleCoeffInfiniteComponent τ (ideleCoeffOf K E (.ofMul a))).toMul :
      SeparableClosure w.Completion) =
      Algebra.TensorProduct.lift (Algebra.ofId _ _)
        (τ.comp (IsScalarTower.toAlgHom K E (SeparableClosure K))) (fun _ _ ↦ .all _ _)
        (GlobalNumberFields.infiniteAdeleSemilocalHom E w (a : AdeleRing (𝓞 E) E).1) :=
  toMul_ideleComponent_ideleCoeffOf (infiniteAdeleSemilocal w) τ E a

/-- **Changing the embedding by an automorphism** `h` of `Kˢ` precomposes the coordinate at `w`
with the action of `h` on the ideles. -/
theorem ideleCoeffInfiniteComponent_comp (h : AbsoluteGaloisGroup K) (x : IdeleCoeff K) :
    ideleCoeffInfiniteComponent (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) x =
      ideleCoeffInfiniteComponent τ (h • x) :=
  ideleComponent_comp (infiniteAdeleSemilocal w) τ h x

/-- **The coordinate at `w` is equivariant** along the decomposition map
`absoluteGaloisGroupMap τ : G_{K_w} → G_K`. -/
theorem ideleCoeffInfiniteComponent_smul (g : AbsoluteGaloisGroup w.Completion)
    (x : IdeleCoeff K) :
    ideleCoeffInfiniteComponent τ (absoluteGaloisGroupMap τ g • x) =
      g • ideleCoeffInfiniteComponent τ x :=
  ideleComponent_smul (infiniteAdeleSemilocal w) τ g x

/-- **On principal ideles the coordinate at `w` is `τ`**: the coordinate of the principal idele
of a unit `x` of `Kˢ` is `τ x`. -/
@[simp]
theorem ideleCoeffInfiniteComponent_principalIdele (x : UnitsCoeff K) :
    ideleCoeffInfiniteComponent τ (principalIdele K x) = unitsCoeffBaseChange τ x :=
  ideleComponent_principalIdele (infiniteAdeleSemilocal w) τ x

variable (w) in
/-- **The localization of idele cohomology at an infinite place** `w`,
`H²(G_K, I_{Kˢ}) → Br K_w`: the pullback along the decomposition map `G_{K_w} → G_K` and the
coordinate at `w` of the ideles (`ideleCoeffInfiniteComponent`) of an embedding of separable
closures `Kˢ → K_wˢ`, followed by the identification of `H²(G_{K_w}, (K_wˢ)ˣ)` with `Br K_w`. It
does not depend on the embedding (`ideleInfiniteBrLocalization_apply`). -/
def ideleInfiniteBrLocalization : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K) →+ Br w.Completion :=
  semilocalBrLocalization (infiniteAdeleSemilocal w)

/-- **The localization of idele cohomology at `w` is the pullback along any embedding** `τ` of
separable closures, through the decomposition map of `τ` and the coordinate at `w` along `τ`. -/
theorem ideleInfiniteBrLocalization_apply (x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    ideleInfiniteBrLocalization w x =
      unitsRepH2Equiv w.Completion
        (explicitMap2 (AbsoluteGaloisGroup K) (IdeleCoeff K) (AbsoluteGaloisGroup w.Completion)
          (UnitsCoeff w.Completion) (absoluteGaloisGroupMap τ) (ideleCoeffInfiniteComponent τ)
          continuous_of_discreteTopology (ideleCoeffInfiniteComponent_smul τ) x) :=
  semilocalBrLocalization_apply (infiniteAdeleSemilocal w) τ x

/-- **On principal idele classes, the localization at `w` is the localization of Brauer
classes**: the class in `H²(G_K, I_{Kˢ})` of a Brauer class `x ∈ Br K`, along the principal
ideles, localizes at `w` to the base change of `x` to `K_w`. -/
theorem ideleInfiniteBrLocalization_principalIdele
    (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    ideleInfiniteBrLocalization w (explicitCoeff2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (principalIdele K) continuous_of_discreteTopology x) =
      brBaseChange K w.Completion (unitsRepH2Equiv K x) :=
  semilocalBrLocalization_principalIdele (infiniteAdeleSemilocal w) x

end Infinite

/-! ### Finite support

A class of `H²(G_K, I_{Kˢ})` is represented by a cocycle with finitely many values, all ideles of
one finite Galois subextension `E` of `Kˢ/K`. At a place `w` of `E` that is unramified over `K` and
at which all these ideles are units, choose the embedding `τ` of separable closures through the
completion `E_w`: the coordinate along `τ` is then the component at `w`
(`toMul_ideleCoeffComponent_ideleCoeffOf_eq_map_ideleFiniteCoord`), so the localization at the
place `v` below `w` is inflated from a cocycle of the unramified layer `E_w/K_v` with values in its
units of valuation one, and vanishes (`mk_eq_zero_of_forall_mem_unitFiltration_zero`). -/

section FiniteSupport

open scoped AdicCompletionExtension

/-- **The coordinate at `v` through a completion of `E`.** If the embedding `τ : Kˢ → K_vˢ` agrees
on a finite Galois subextension `E` with an embedding `τ'` of the completion `E_w` at a place `w`
of `E` above `v`, then the coordinate at `v` along `τ` of an idele of `E` is its component at `w`,
embedded in `K_vˢ` by `τ'`. -/
theorem toMul_ideleCoeffComponent_ideleCoeffOf_eq_map_ideleFiniteCoord {E : Ω}
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (τ' : w.adicCompletion E →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : E, τ x = τ' (algebraMap E (w.adicCompletion E) x)) (a : IdeleGroup (𝓞 E) E) :
    (ideleCoeffComponent τ (ideleCoeffOf K E (.ofMul a))).toMul =
      Units.map (τ' : w.adicCompletion E →* SeparableClosure (v.adicCompletion K))
        (w.ideleFiniteCoord a) := by
  refine Units.ext ?_
  rw [toMul_ideleCoeffComponent_ideleCoeffOf, Units.coe_map, MonoidHom.coe_ofClass,
    HeightOneSpectrum.coe_ideleFiniteCoord]
  -- The map `K_v ⊗[K] E → K_vˢ`, `a ⊗ x ↦ a τ(x)`, is `τ'` after projecting to the factor `E_w`.
  have h : Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (τ.comp (IsScalarTower.toAlgHom K E (SeparableClosure K))) (fun _ _ ↦ .all _ _) =
      τ'.comp ((Pi.evalAlgHom _ _ ⟨w, inferInstance⟩).comp (semilocalEquiv E v).toAlgHom) := by
    refine Algebra.TensorProduct.ext' fun b x ↦ ?_
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
      IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom, semilocalEquiv_tmul, Pi.evalAlgHom_apply,
      map_mul, AlgHom.commutes, IntermediateField.algebraMap_apply, ← hτ]
  rw [h]
  simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply,
    semilocalEquiv_finiteAdeleSemilocalHom, Pi.evalAlgHom_apply]

/-- Two elements of `G_{K_v}` with the same restriction to `τ'(E_w)` have images in `G_K` with the
same restriction to `E`, for an embedding `τ` of `Kˢ` extending `τ'` on `E`. -/
private theorem absoluteGaloisGroupMap_inv_mul_mem_fixingSubgroup {E : Ω}
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (τ' : w.adicCompletion E →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : E, τ x = τ' (algebraMap E (w.adicCompletion E) x))
    {g g' : AbsoluteGaloisGroup (v.adicCompletion K)}
    (hgg' : τ'.restrictNormalHom g = τ'.restrictNormalHom g') :
    (absoluteGaloisGroupMap τ g)⁻¹ * absoluteGaloisGroupMap τ g' ∈
      (E : IntermediateField K (SeparableClosure K)).fixingSubgroup := by
  have hE (g : AbsoluteGaloisGroup (v.adicCompletion K)) (x : E) :
      τ (absoluteGaloisGroupMap τ g x) =
        τ' (τ'.restrictNormalHom g (algebraMap E (w.adicCompletion E) x)) := by
    rw [absoluteGaloisGroupMap_commutes, hτ, AlgHom.restrictNormalHom_commutes]
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
  exact τ.injective ((hE g' ⟨x, hx⟩).trans ((congrArg _ (by rw [hgg'])).trans (hE g ⟨x, hx⟩).symm))

/-- The cocycle pulled back from `z` along the pair of `τ` is read off `Gal(E_w/K_v)` through `τ'`,
if the values of `z` are the ideles `a` of `E`, `τ` extends `τ'` on `E`, and `u` reads the
components at `w` of the `a`. -/
private theorem cocyclesMap2_ideleCoeffComponent_apply {E : Ω}
    {U : OpenNormalSubgroup (AbsoluteGaloisGroup K)} (z : Z2 (AbsoluteGaloisGroup K) (IdeleCoeff K))
    (a : (AbsoluteGaloisGroup K ⧸ U.toSubgroup) × (AbsoluteGaloisGroup K ⧸ U.toSubgroup) →
      IdeleGroup (𝓞 E) E)
    (ha : ∀ g h : AbsoluteGaloisGroup K, ideleCoeffOf K E (.ofMul (a (g, h))) = z.1 (g, h))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (τ' : w.adicCompletion E →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : E, τ x = τ' (algebraMap E (w.adicCompletion E) x))
    (u : Gal(w.adicCompletion E/v.adicCompletion K) × Gal(w.adicCompletion E/v.adicCompletion K) →
      (w.adicCompletion E)ˣ)
    (hu : ∀ g h : AbsoluteGaloisGroup (v.adicCompletion K),
      u (τ'.restrictNormalHom g, τ'.restrictNormalHom h) =
        w.ideleFiniteCoord (a ((absoluteGaloisGroupMap τ g : AbsoluteGaloisGroup K),
          (absoluteGaloisGroupMap τ h : AbsoluteGaloisGroup K))))
    (g h : AbsoluteGaloisGroup (v.adicCompletion K)) :
    ((cocyclesMap2 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (AbsoluteGaloisGroup (v.adicCompletion K)) (UnitsCoeff (v.adicCompletion K))
      (absoluteGaloisGroupMap τ) (ideleCoeffComponent τ) continuous_of_discreteTopology
      (ideleCoeffComponent_smul τ) z).1 (g, h) : UnitsCoeff _) =
      embeddedUnitsEquivInvariants _ _ τ'
        (.ofMul (u (τ'.restrictNormalHom g, τ'.restrictNormalHom h))) := by
  rw [cocyclesMap2_apply]
  refine (congrArg (ideleCoeffComponent τ) (ha _ _).symm).trans (Additive.toMul.injective ?_)
  refine (toMul_ideleCoeffComponent_ideleCoeffOf_eq_map_ideleFiniteCoord w τ' τ hτ _).trans ?_
  rw [embeddedUnitsEquivInvariants_apply, toMul_coe_embeddedUnitsInvariants]
  exact congrArg (Units.map _) (hu g h).symm

/-- The localization at `v` of the class of a cocycle `z` vanishes if `z` factors through
`G_K ⧸ U`, its values are the ideles `a` of a finite Galois subextension `E` fixed by `U`, and
some place `w` of `E` above `v` is unramified over `K` with all the `a` units at `w`; here `τ`
is an embedding of separable closures extending an embedding `τ'` of `E_w` on `E`. -/
private theorem ideleBrLocalization_eq_zero_of_isUnramified {E : Ω}
    {U : OpenNormalSubgroup (AbsoluteGaloisGroup K)}
    (hU : (E : IntermediateField K (SeparableClosure K)).fixingSubgroup ≤ U.toSubgroup)
    (z : Z2 (AbsoluteGaloisGroup K) (IdeleCoeff K))
    (a : (AbsoluteGaloisGroup K ⧸ U.toSubgroup) × (AbsoluteGaloisGroup K ⧸ U.toSubgroup) →
      IdeleGroup (𝓞 E) E)
    (ha : ∀ g h : AbsoluteGaloisGroup K, ideleCoeffOf K E (.ofMul (a (g, h))) = z.1 (g, h))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    [IsUnramified (v.adicCompletion K) (w.adicCompletion E)]
    (hw : ∀ q, Valued.v ((a q : AdeleRing (𝓞 E) E).2 w) = 1)
    (τ' : w.adicCompletion E →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (hτ : ∀ x : E, τ x = τ' (algebraMap E (w.adicCompletion E) x)) :
    ideleBrLocalization v (z : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) = 0 := by
  -- The pulled-back cocycle on `G_{K_v}` is read off `Gal(E_w/K_v)`: its value at `(g, h)` is the
  -- component at `w` of `a` at the classes of the images of any lifts of `g|_{E_w}`, `h|_{E_w}`.
  let lift := Function.surjInv τ'.restrictNormalHom_surjective
  have hlift (g : AbsoluteGaloisGroup (v.adicCompletion K)) :
      ((absoluteGaloisGroupMap τ (lift (τ'.restrictNormalHom g)) : AbsoluteGaloisGroup K) :
        AbsoluteGaloisGroup K ⧸ U.toSubgroup) =
        (absoluteGaloisGroupMap τ g : AbsoluteGaloisGroup K) :=
    QuotientGroup.eq.2 (hU (absoluteGaloisGroupMap_inv_mul_mem_fixingSubgroup w τ' τ hτ
      (Function.surjInv_eq _ _)))
  refine (ideleBrLocalization_apply τ _).trans ?_
  refine (congrArg (unitsRepH2Equiv (v.adicCompletion K))
    (explicitMap2_mk (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (AbsoluteGaloisGroup (v.adicCompletion K)) (UnitsCoeff (v.adicCompletion K))
      (absoluteGaloisGroupMap τ) (ideleCoeffComponent τ) continuous_of_discreteTopology
      (ideleCoeffComponent_smul τ) z)).trans ?_
  let u : Gal(w.adicCompletion E/v.adicCompletion K) × Gal(w.adicCompletion E/v.adicCompletion K) →
      (w.adicCompletion E)ˣ := fun p ↦ w.ideleFiniteCoord
    (a ((absoluteGaloisGroupMap τ (lift p.1) : AbsoluteGaloisGroup K),
      (absoluteGaloisGroupMap τ (lift p.2) : AbsoluteGaloisGroup K)))
  rw [mk_eq_zero_of_forall_mem_unitFiltration_zero _ _ τ' _ u
    (fun _ ↦ (HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff w).2
      (by rw [HeightOneSpectrum.coe_ideleFiniteCoord, hw]))
    (cocyclesMap2_ideleCoeffComponent_apply z a ha w τ' τ hτ u fun g h ↦ by
      simp only [u, hlift]), map_zero]

/-- **The localization of idele cohomology is finitely supported**: a class of `H²(G_K, I_{Kˢ})`
has nonzero localization `ideleBrLocalization v` at only finitely many finite places `v`. -/
theorem finite_setOfPred_ideleBrLocalization_ne_zero
    (x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    {v : HeightOneSpectrum (𝓞 K) | ideleBrLocalization v x ≠ 0}.Finite := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
  -- `z` factors through `G_K ⧸ U`, and its finitely many values are ideles of a finite Galois
  -- subextension `E` of `Kˢ` whose fixing subgroup lies in `U`.
  obtain ⟨U, c, hc⟩ := exists_openNormalSubgroup_descendZ2 z
  have : Finite (AbsoluteGaloisGroup K ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ U.isOpen
  have : Fintype (AbsoluteGaloisGroup K ⧸ U.toSubgroup) := .ofFinite _
  obtain ⟨E₀, _, _, hE₀⟩ := exists_galoisOpenNormalSubgroup_eq U
  choose F a ha using fun q ↦ exists_ideleCoeffOf_eq (K := K) (c.1 q : IdeleCoeff K)
  let E : Ω := ⟨E₀⟩ ⊔ Finset.univ.sup F
  have hFE (q) : F q ≤ E := le_sup_of_le_right (Finset.le_sup (Finset.mem_univ q))
  have hU : (E : IntermediateField K (SeparableClosure K)).fixingSubgroup ≤ U.toSubgroup := by
    rw [← hE₀, galoisOpenNormalSubgroup_toSubgroup, IntermediateField.fieldRange_val]
    exact IntermediateField.fixingSubgroup_le (le_sup_left (a := (⟨E₀⟩ : Ω)))
  let b q : IdeleGroup (𝓞 E) E := ideleTransition K (F q) E (hFE q) (a q)
  have hb (g h : AbsoluteGaloisGroup K) : ideleCoeffOf K E (.ofMul (b (g, h))) = z.1 (g, h) :=
    ((ideleCoeffOf_ideleTransition _ _).trans (ha _)).trans (hc g h)
  -- The places of `E` that ramify over `K` or at which a value of `b` is not a unit.
  let bad : Set (HeightOneSpectrum (𝓞 E)) :=
    {w | w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 E)} ∪
      ⋃ q, {w | Valued.v ((b q : AdeleRing (𝓞 E) E).2 w) ≠ 1}
  have hbad : bad.Finite := by
    refine (Ideal.finite_factors differentIdeal_ne_bot).union (Set.finite_iUnion fun q ↦ ?_)
    exact Filter.eventually_cofinite.1 (FiniteAdeleRing.isUnit_iff.1
      ((b q).isUnit.map (RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)))).2
  -- The localization vanishes at every place below none of them.
  refine (hbad.image (HeightOneSpectrum.under (𝓞 K))).subset fun v hv ↦ ?_
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E) v
  by_contra hvS
  have hw : w ∉ bad := fun h ↦ hvS ⟨w, h, rfl⟩
  simp only [bad, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
    not_not] at hw
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := not_dvd_differentIdeal_iff.1 hw.1
  have : IsUnramified ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion E) :=
    HeightOneSpectrum.isUnramified_adicCompletion_of_isUnramifiedAt _ w
  -- An embedding `τ' : E_w → K_vˢ`, and an embedding `τ : Kˢ → K_vˢ` extending it on `E`.
  let τ' : w.adicCompletion E →ₐ[(w.under (𝓞 K)).adicCompletion K]
      SeparableClosure ((w.under (𝓞 K)).adicCompletion K) := IsSepClosed.lift
  obtain ⟨τ, hτ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K)
    E.toIntermediateField (E := SeparableClosure K)
    (M := SeparableClosure ((w.under (𝓞 K)).adicCompletion K))
    ((τ'.restrictScalars K).comp (IsScalarTower.toAlgHom K E (w.adicCompletion E)))
  exact hv (ideleBrLocalization_eq_zero_of_isUnramified hU z b hb w hw.2 τ' τ
    fun x ↦ congrArg (fun φ : E →ₐ[K] _ ↦ φ x) hτ)

end FiniteSupport

end TauCeti.ClassFieldTheory
