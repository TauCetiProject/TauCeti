/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.BaseChange
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Coefficients
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.FiniteAdele

/-!
# The localization of idele cohomology at a finite place

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
global Brauer classes (`ideleBrLocalization_principalIdele`).

## Main definitions

* `TauCeti.ClassFieldTheory.ideleCoeffComponent τ`: the coordinate at `v` of the ideles of `Kˢ`
  along `τ`.
* `TauCeti.ClassFieldTheory.ideleBrLocalization v`: the localization
  `H²(G_K, I_{Kˢ}) → Br K_v`.

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

/-! ### The coordinate at a finite place -/

section Coordinate

variable (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

/-- The `K_v`-algebra map `K_v ⊗[K] E → K_vˢ`, `a ⊗ x ↦ a τ(x)`. -/
private def semilocalLift (E : Ω) :
    v.adicCompletion K ⊗[K] E →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (τ.comp (IsScalarTower.toAlgHom K E (SeparableClosure K))) fun _ _ ↦ .all _ _

@[simp]
private theorem semilocalLift_tmul (E : Ω) (a : v.adicCompletion K) (x : E) :
    semilocalLift τ E (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (SeparableClosure (v.adicCompletion K)) a *
        τ (x : SeparableClosure K) := by
  simp [semilocalLift]

/-- The coordinate at `v` along `τ` of an adele of `E`: its components above `v`, mapped to
`K_vˢ` by `semilocalLift`. -/
private def adeleComponent (E : Ω) : AdeleRing (𝓞 E) E →+* SeparableClosure (v.adicCompletion K) :=
  (semilocalLift τ E).toRingHom.comp
    ((finiteAdeleSemilocalHom E v).comp (RingHom.snd (InfiniteAdeleRing E) _))

private theorem adeleComponent_apply (E : Ω) (a : AdeleRing (𝓞 E) E) :
    adeleComponent τ E a = semilocalLift τ E (finiteAdeleSemilocalHom E v a.2) :=
  (rfl)

/-- The coordinate at `v` is compatible with the extension maps of adeles. -/
private theorem adeleComponent_adeleTransition {E E' : Ω} (h : E ≤ E') (a : AdeleRing (𝓞 E) E) :
    adeleComponent τ E' (adeleTransition h a) = adeleComponent τ E a := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E E' := .of_algebraMap_eq fun _ ↦ rfl
  rw [adeleComponent_apply, adeleComponent_apply, adeleTransition_snd,
    finiteAdeleSemilocalHom_finiteAdeleExtension, ← AlgHom.comp_apply]
  congr 1
  ext x
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, semilocalLift_tmul]
  -- The algebra map `E → E'` is the inclusion, which does not move `x` in `Kˢ`.
  rw [show ((IsScalarTower.toAlgHom K E E' x : E') : SeparableClosure K) = x from
    IntermediateField.coe_inclusion h x, AlgHom.id_apply]

/-- Acting on an adele of `E` by `h ∈ G_K` and then taking the coordinate along `τ` is taking the
coordinate along `τ ∘ h`. -/
private theorem adeleComponent_adeleGaloisAction (h : AbsoluteGaloisGroup K) (E : Ω)
    (a : AdeleRing (𝓞 E) E) :
    adeleComponent τ E (GlobalNumberFields.adeleGaloisAction K E (h.restrictNormal E) a) =
      adeleComponent (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) E a := by
  rw [adeleComponent_apply, adeleComponent_apply, GlobalNumberFields.adeleGaloisAction_apply,
    GlobalNumberFields.adeleEquiv_snd, finiteAdeleSemilocalHom_finiteAdeleEquiv,
    ← AlgHom.comp_apply]
  congr 1
  ext x
  simp [AlgEquiv.restrictNormal_apply]

/-- Composing `τ` with `g ∈ G_{K_v}` composes the coordinate with `g`. -/
private theorem adeleComponent_comp_left (g : AbsoluteGaloisGroup (v.adicCompletion K)) (E : Ω)
    (a : AdeleRing (𝓞 E) E) :
    adeleComponent (((g : SeparableClosure (v.adicCompletion K) →ₐ[v.adicCompletion K]
      SeparableClosure (v.adicCompletion K)).restrictScalars K).comp τ) E a =
        g (adeleComponent τ E a) := by
  rw [adeleComponent_apply, adeleComponent_apply, ← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply]
  congr 1
  ext x
  simp

/-- **The coordinate at `v` of the ideles of `Kˢ`** along a `K`-embedding
`τ : Kˢ →ₐ[K] K_vˢ` of separable closures: an idele `a` of a finite Galois subextension `E` of
`Kˢ/K` goes to the image of its components above `v`, read in `K_v ⊗[K] E`, under the
`K_v`-algebra map `a ⊗ x ↦ a τ(x)` to `K_vˢ` (`toMul_ideleCoeffComponent_ideleCoeffOf`). A ring
homomorphism from `K_v ⊗[K] E ≃ ∏_{w ∣ v} E_w` to a field factors through a single factor `E_w`,
so this reads the component of the idele at one place `w` of `E` above `v`, embedded in
`K_vˢ`. -/
def ideleCoeffComponent : IdeleCoeff K →+ UnitsCoeff (v.adicCompletion K) :=
  IdeleCoeff.lift K (fun E ↦ (Units.map (adeleComponent τ E).toMonoidHom).toAdditive)
    fun E E' h a ↦ Additive.toMul.injective (Units.ext (by simp [adeleComponent_adeleTransition]))

private theorem toMul_ideleCoeffComponent_ideleCoeffOf' (E : Ω) (a : IdeleGroup (𝓞 E) E) :
    ((ideleCoeffComponent τ (ideleCoeffOf K E (.ofMul a))).toMul :
      SeparableClosure (v.adicCompletion K)) = adeleComponent τ E a := by
  simp [ideleCoeffComponent, IdeleCoeff.lift_ideleCoeffOf]

/-- **The coordinate at `v` of an idele of `E`**: the image of its components above `v`, read in
`K_v ⊗[K] E`, under `a ⊗ x ↦ a τ(x)`. -/
theorem toMul_ideleCoeffComponent_ideleCoeffOf (E : Ω) (a : IdeleGroup (𝓞 E) E) :
    ((ideleCoeffComponent τ (ideleCoeffOf K E (.ofMul a))).toMul :
      SeparableClosure (v.adicCompletion K)) =
      Algebra.TensorProduct.lift (Algebra.ofId _ _)
        (τ.comp (IsScalarTower.toAlgHom K E (SeparableClosure K))) (fun _ _ ↦ .all _ _)
        (finiteAdeleSemilocalHom E v (a : AdeleRing (𝓞 E) E).2) :=
  toMul_ideleCoeffComponent_ideleCoeffOf' τ E a

/-- **Changing the embedding by an automorphism** `h` of `Kˢ` precomposes the coordinate at `v`
with the action of `h` on the ideles. -/
theorem ideleCoeffComponent_comp (h : AbsoluteGaloisGroup K) (x : IdeleCoeff K) :
    ideleCoeffComponent (τ.comp (h : SeparableClosure K →ₐ[K] SeparableClosure K)) x =
      ideleCoeffComponent τ (h • x) := by
  obtain ⟨E, a, rfl⟩ := exists_ideleCoeffOf_eq x
  refine Additive.toMul.injective (Units.ext ?_)
  simp [smul_ideleCoeffOf, toMul_ideleCoeffComponent_ideleCoeffOf',
    adeleComponent_adeleGaloisAction]

/-- **The coordinate at `v` is equivariant** along the decomposition map
`absoluteGaloisGroupMap τ : G_{K_v} → G_K`. -/
theorem ideleCoeffComponent_smul (g : AbsoluteGaloisGroup (v.adicCompletion K)) (x : IdeleCoeff K) :
    ideleCoeffComponent τ (absoluteGaloisGroupMap τ g • x) = g • ideleCoeffComponent τ x := by
  rw [← ideleCoeffComponent_comp]
  have hτ : τ.comp (absoluteGaloisGroupMap τ g : SeparableClosure K →ₐ[K] SeparableClosure K) =
      ((g : SeparableClosure (v.adicCompletion K) →ₐ[v.adicCompletion K]
        SeparableClosure (v.adicCompletion K)).restrictScalars K).comp τ :=
    AlgHom.ext fun y ↦ absoluteGaloisGroupMap_commutes τ g y
  obtain ⟨E, a, rfl⟩ := exists_ideleCoeffOf_eq x
  refine Additive.toMul.injective (Units.ext ?_)
  rw [hτ]
  simp [toMul_ideleCoeffComponent_ideleCoeffOf', adeleComponent_comp_left, Additive.toMul_smul,
    AlgEquiv.smul_units_def]

/-- **On principal ideles the coordinate at `v` is `τ`**: the coordinate of the principal idele
of a unit `x` of `Kˢ` is `τ x`. -/
@[simp]
theorem ideleCoeffComponent_principalIdele (x : UnitsCoeff K) :
    ideleCoeffComponent τ (principalIdele K x) = unitsCoeffBaseChange τ x := by
  -- `x` is a unit of the finite Galois subextension it generates.
  let E : Ω := FiniteGaloisIntermediateField.adjoin K {(x.toMul : SeparableClosure K)}
  have hx : (x.toMul : SeparableClosure K) ∈ (E : IntermediateField K (SeparableClosure K)) :=
    FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  let u : Eˣ := Units.mk0 ⟨x.toMul, hx⟩ fun h ↦ x.toMul.ne_zero (congrArg Subtype.val h)
  have hxu : x = .ofMul (Units.map (algebraMap E (SeparableClosure K)).toMonoidHom u) :=
    Additive.toMul.injective (Units.ext rfl)
  refine Additive.toMul.injective (Units.ext ?_)
  rw [hxu, principalIdele_ofMul_map_algebraMap]
  simp [toMul_ideleCoeffComponent_ideleCoeffOf', adeleComponent_apply,
    finiteAdeleSemilocalHom_algebraMap]

end Coordinate

/-! ### The localization of idele cohomology -/

variable (v) in
/-- **The localization of idele cohomology at a finite place** `v`,
`H²(G_K, I_{Kˢ}) → Br K_v`: the pullback along the decomposition map
`G_{K_v} → G_K` and the coordinate at `v` of the ideles (`ideleCoeffComponent`) of an embedding of
separable closures `Kˢ → K_vˢ`, followed by the identification of `H²(G_{K_v}, (K_vˢ)ˣ)` with
`Br K_v`. It does not depend on the embedding (`ideleBrLocalization_apply`). -/
def ideleBrLocalization : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K) →+ Br (v.adicCompletion K) :=
  (unitsRepH2Equiv (v.adicCompletion K) :
      H2 (AbsoluteGaloisGroup (v.adicCompletion K)) (UnitsCoeff (v.adicCompletion K)) →+
        Br (v.adicCompletion K)).comp
    (explicitMap2 (AbsoluteGaloisGroup K) (IdeleCoeff K) (AbsoluteGaloisGroup (v.adicCompletion K))
      (UnitsCoeff (v.adicCompletion K)) (absoluteGaloisGroupMap IsSepClosed.lift)
      (ideleCoeffComponent IsSepClosed.lift) continuous_of_discreteTopology
      (ideleCoeffComponent_smul IsSepClosed.lift))

/-- **The localization of idele cohomology is the pullback along any embedding** `τ` of separable
closures, through the decomposition map of `τ` and the coordinate at `v` along `τ`. -/
theorem ideleBrLocalization_apply
    (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (x : H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    ideleBrLocalization v x =
      unitsRepH2Equiv (v.adicCompletion K)
        (explicitMap2 (AbsoluteGaloisGroup K) (IdeleCoeff K)
          (AbsoluteGaloisGroup (v.adicCompletion K)) (UnitsCoeff (v.adicCompletion K))
          (absoluteGaloisGroupMap τ) (ideleCoeffComponent τ) continuous_of_discreteTopology
          (ideleCoeffComponent_smul τ) x) := by
  rw [ideleBrLocalization, explicitMap2_absoluteGaloisGroupMap_eq K (v.adicCompletion K)
    (fun τ ↦ ideleCoeffComponent τ) ideleCoeffComponent_smul ideleCoeffComponent_comp
    IsSepClosed.lift τ,
    AddMonoidHom.comp_apply, AddMonoidHom.coe_ofClass]

/-- **On principal idele classes, the localization is the localization of Brauer classes**: the
class in `H²(G_K, I_{Kˢ})` of a Brauer class `x ∈ Br K = H²(G_K, (Kˢ)ˣ)`, along the principal
ideles, localizes at `v` to the base change of `x` to `K_v`. -/
theorem ideleBrLocalization_principalIdele (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    ideleBrLocalization v (explicitCoeff2 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (principalIdele K) continuous_of_discreteTopology x) =
      brBaseChange K (v.adicCompletion K) (unitsRepH2Equiv K x) := by
  let τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K) := IsSepClosed.lift
  -- Pulling back along the principal ideles and then along the pair of `τ` is pulling back along
  -- the composite pair, which is `(absoluteGaloisGroupMap τ, unitsCoeffBaseChange τ)`.
  have hcomp := DFunLike.congr_fun (explicitMap2_comp (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup K) (IdeleCoeff K) (ContinuousMonoidHom.id _)
    (principalIdele K : UnitsCoeff K →+ IdeleCoeff K) continuous_of_discreteTopology
    (fun g m ↦ map_smul (principalIdele K) g m) (AbsoluteGaloisGroup (v.adicCompletion K))
    (UnitsCoeff (v.adicCompletion K)) (absoluteGaloisGroupMap τ) (ideleCoeffComponent τ)
    continuous_of_discreteTopology (ideleCoeffComponent_smul τ)) x
  have hpair := explicitMap2_congr_of_eq (AbsoluteGaloisGroup K) (UnitsCoeff K)
    (AbsoluteGaloisGroup (v.adicCompletion K)) (UnitsCoeff (v.adicCompletion K))
    ((ContinuousMonoidHom.id _).comp (absoluteGaloisGroupMap τ)) (absoluteGaloisGroupMap τ)
    ((ideleCoeffComponent τ).comp (principalIdele K : UnitsCoeff K →+ IdeleCoeff K))
    (unitsCoeffBaseChange τ) (hf := continuous_of_discreteTopology)
    (hq := continuous_of_discreteTopology) (hψ := unitsCoeffBaseChange_smul τ)
    (hφ := fun g m ↦ by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ContinuousMonoidHom.comp_toFun]
      exact (congrArg (ideleCoeffComponent τ) (map_smul (principalIdele K) _ m)).trans
        (ideleCoeffComponent_smul τ g _))
    (ContinuousMonoidHom.ext fun _ ↦ rfl)
    (AddMonoidHom.ext fun y ↦ ideleCoeffComponent_principalIdele τ y)
  rw [ideleBrLocalization_apply τ, brBaseChange_apply K _ τ, AddEquiv.symm_apply_apply,
    explicitCoeff2_eq_explicitMap2]
  exact congrArg _ (hcomp.symm.trans (DFunLike.congr_fun hpair x))

end TauCeti.ClassFieldTheory
