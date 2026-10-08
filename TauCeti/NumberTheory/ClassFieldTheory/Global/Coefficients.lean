/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import TauCeti.Algebra.GroupAction.QuotientAddGroup
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.FieldTheory.GaloisCohomology.Coefficients
public import TauCeti.NumberTheory.NumberField.FiniteGaloisIntermediateField
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisDescent

/-!
# The ideles and idele classes of a separable closure of a number field

Let `K` be a number field with separable closure `Kˢ` and absolute Galois group
`G_K = Gal(Kˢ/K)`. This file builds the two discrete `G_K`-modules on which the global class
formations are built: the **ideles of `Kˢ`**,

```text
I_{Kˢ} = colim_E I_E,
```

the direct limit of the idele groups of the finite Galois subextensions `E` of `Kˢ/K` along the
extension maps `I_E → I_{E'}` for `E ≤ E'`, and the **idele classes** `C_{Kˢ} = I_{Kˢ} / (Kˢ)ˣ`,
the quotient by the principal ideles. Both are written additively, as `IdeleCoeff K` and
`IdeleClassCoeff K`, in the same way as `TauCeti.UnitsCoeff K` writes `(Kˢ)ˣ`.

An element `g ∈ G_K` acts on `I_E` through its restriction to `Gal(E/K)` and the Galois action
`TauCeti.GlobalNumberFields.adeleGaloisAction` on adeles. These actions commute with the extension
maps (`adeleTransition_adeleGaloisAction`), so they pass to the direct limit. The ideles of `E` are
fixed by the open subgroup of `G_K` fixing `E` (`smul_ideleCoeffOf_of_mem_fixingSubgroup`), so
both modules are discrete with open point stabilizers.

Conversely, the ideles of `E` embed in `I_{Kˢ}` (`ideleCoeffOf_injective`) and are exactly the
ideles of `Kˢ` fixed by the subgroup `G_E` of `G_K` fixing `E` (`mem_range_ideleCoeffOf_iff`):
`(I_{Kˢ})^{G_E} = I_E`. A fixed idele is defined over a larger finite Galois subextension `E'`;
every element of `Gal(E'/E)` lifts to `G_E`, so it is fixed by `Gal(E'/E)` and descends to `E` by
Galois descent for the ideles of number fields
(`TauCeti.GlobalNumberFields.mem_range_ideleExtension_iff`).

A unit of `Kˢ` lies in a finite Galois subextension `E`, and its principal idele in `I_E` does not
depend on the choice of `E`; this is the equivariant embedding `principalIdele : (Kˢ)ˣ → I_{Kˢ}`
(`principalIdele_ofMul_map_algebraMap`, `principalIdele_injective`). The sequence

```text
0 → (Kˢ)ˣ → I_{Kˢ} → C_{Kˢ} → 0
```

is exact by `principalIdele_injective`, `ideleClassMk_eq_zero_iff` and
`ideleClassMk_surjective`.

## Main definitions

* `TauCeti.ClassFieldTheory.adeleTransition`, `ideleTransition`: the extension maps of adeles and
  ideles along an inclusion of finite Galois subextensions of `Kˢ/K`.
* `TauCeti.ClassFieldTheory.IdeleCoeff K`: the ideles of `Kˢ`, written additively.
* `TauCeti.ClassFieldTheory.ideleCoeffOf E`: the ideles of `E` as ideles of `Kˢ`.
* `TauCeti.ClassFieldTheory.IdeleCoeff.lift`: the homomorphism out of the ideles of `Kˢ` induced
  by compatible homomorphisms out of the ideles of the finite Galois subextensions.
* `TauCeti.ClassFieldTheory.principalIdele K`: the principal ideles `(Kˢ)ˣ → I_{Kˢ}`.
* `TauCeti.ClassFieldTheory.IdeleClassCoeff K`: the idele classes of `Kˢ`, written additively.
* `TauCeti.ClassFieldTheory.ideleClassMk K`: the quotient map `I_{Kˢ} → C_{Kˢ}`.
* `TauCeti.ClassFieldTheory.IdeleClassCoeff.lift`: the homomorphism out of the idele classes of
  `Kˢ` induced by a homomorphism out of the ideles of `Kˢ` vanishing on the principal ideles.

## Main results

* `TauCeti.ClassFieldTheory.exists_ideleCoeffOf_eq`: every idele of `Kˢ` comes from some `I_E`.
* `TauCeti.ClassFieldTheory.smul_ideleCoeffOf`: the action of `G_K` on the ideles of `E`.
* `TauCeti.ClassFieldTheory.ideleCoeffOf_injective`: the ideles of `E` embed in the ideles of
  `Kˢ`.
* `TauCeti.ClassFieldTheory.mem_range_ideleCoeffOf_iff`: **Galois descent**, an idele of `Kˢ` is
  an idele of `E` exactly when it is fixed by the subgroup of `G_K` fixing `E`.
* `TauCeti.ClassFieldTheory.principalIdele_injective`: the principal ideles embed `(Kˢ)ˣ`.

## Implementation notes

The direct limit is indexed by `FiniteGaloisIntermediateField K (SeparableClosure K)`, the finite
*Galois* subextensions. Each of them is stable under `G_K`, so `G_K` acts on every level separately
and on the direct limit through Mathlib's `DirectLimit` instances; indexing by all finite
subextensions would instead move `I_E` to `I_{g E}`. Both the transition maps and the level actions
are continuous ring homomorphisms of adele rings, and identities between their composites are
proved by `NumberField.AdeleRing.ringHom_ext`, from their values on the diagonal field and on the
idempotent `(1, 0)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1 and §2.
-/

public section

noncomputable section

open NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)

/-! ### The transition maps -/

/-- The extension map of adele rings `𝔸_E → 𝔸_{E'}` along an inclusion `E ≤ E'` of finite
Galois subextensions of `Kˢ/K`. -/
def adeleTransition {E E' : Ω} (h : E ≤ E') : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 E') E' :=
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  adeleExtension (𝓞 E) E (𝓞 E') E'

/-- The extension map of adele rings along `E ≤ E'` is the extension map of adeles along the
inclusion `E → E'`. -/
theorem adeleTransition_apply {E E' : Ω} (h : E ≤ E') (a : AdeleRing (𝓞 E) E) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    adeleTransition h a = adeleExtension (𝓞 E) E (𝓞 E') E' a :=
  (rfl)

/-- The extension map of adele rings is continuous. -/
theorem continuous_adeleTransition {E E' : Ω} (h : E ≤ E') :
    Continuous (adeleTransition h) := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact continuous_adeleExtension (𝓞 E) E (𝓞 E') E'

/-- The extension map of adele rings extends the inclusion `E ≤ E'` on the diagonal fields. -/
@[simp]
theorem adeleTransition_algebraMap {E E' : Ω} (h : E ≤ E') (x : E) :
    adeleTransition h (algebraMap E _ x) =
      algebraMap E' _ (IntermediateField.inclusion h x) := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact adeleExtension_algebraMap (𝓞 E) E (𝓞 E') E' x

/-- The infinite component of the extension of an adele is the extension of its infinite
component. -/
theorem adeleTransition_fst {E E' : Ω} (h : E ≤ E') (a : AdeleRing (𝓞 E) E) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    (adeleTransition h a).1 = infiniteAdeleExtension E E' a.1 := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact adeleExtension_fst (B := 𝓞 E') (L := E') a

/-- The finite component of the extension of an adele is the extension of its finite
component. -/
theorem adeleTransition_snd {E E' : Ω} (h : E ≤ E') (a : AdeleRing (𝓞 E) E) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    (adeleTransition h a).2 = IsDedekindDomain.finiteAdeleExtension (𝓞 E) E (𝓞 E') E' a.2 := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact adeleExtension_snd (B := 𝓞 E') (L := E') a

/-- The extension map of adele rings preserves the idempotent `(1, 0)`. -/
private theorem adeleTransition_fst_snd {E E' : Ω} (h : E ≤ E') {a : AdeleRing (𝓞 E) E}
    (h₁ : a.1 = 1) (h₂ : a.2 = 0) :
    (adeleTransition h a).1 = 1 ∧ (adeleTransition h a).2 = 0 := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact ⟨(adeleExtension_fst (B := 𝓞 E') (L := E') a).trans (by rw [h₁, map_one]),
    (adeleExtension_snd (B := 𝓞 E') (L := E') a).trans (by rw [h₂, map_zero])⟩

/-- The Galois action on adeles preserves the idempotent `(1, 0)`. -/
private theorem adeleGaloisAction_fst_snd (E : Ω) (σ : E ≃ₐ[K] E) {a : AdeleRing (𝓞 E) E}
    (h₁ : a.1 = 1) (h₂ : a.2 = 0) :
    (GlobalNumberFields.adeleGaloisAction K E σ a).1 = 1 ∧
      (GlobalNumberFields.adeleGaloisAction K E σ a).2 = 0 := by
  simp [GlobalNumberFields.adeleGaloisAction_apply, h₁, h₂]

/-- The extension map along `E ≤ E` is the identity. -/
@[simp]
theorem adeleTransition_self (E : Ω) : adeleTransition (le_refl E) = RingHom.id _ :=
  AdeleRing.ringHom_ext _ _ (continuous_adeleTransition _) continuous_id
    (fun x ↦ by rw [adeleTransition_algebraMap]; rfl) fun _ h₁ h₂ ↦
      Prod.ext ((adeleTransition_fst_snd _ h₁ h₂).1.trans h₁.symm)
        ((adeleTransition_fst_snd _ h₁ h₂).2.trans h₂.symm)

/-- The extension maps compose along a tower `E ≤ E' ≤ E''`. -/
@[simp]
theorem adeleTransition_comp {E E' E'' : Ω} (h : E ≤ E') (h' : E' ≤ E'') :
    (adeleTransition h').comp (adeleTransition h) = adeleTransition (h.trans h') :=
  AdeleRing.ringHom_ext _ _
    ((continuous_adeleTransition _).comp (continuous_adeleTransition _))
    (continuous_adeleTransition _)
    (fun x ↦ by simp only [RingHom.comp_apply, adeleTransition_algebraMap]; rfl) fun _ h₁ h₂ ↦
      have h₁' := adeleTransition_fst_snd h h₁ h₂
      Prod.ext ((adeleTransition_fst_snd h' h₁'.1 h₁'.2).1.trans
          (adeleTransition_fst_snd (h.trans h') h₁ h₂).1.symm)
        ((adeleTransition_fst_snd h' h₁'.1 h₁'.2).2.trans
          (adeleTransition_fst_snd (h.trans h') h₁ h₂).2.symm)

/-- **The extension maps are Galois equivariant**: for `g ∈ G_K`, extending from `E` to `E'` and
then acting by the restriction of `g` to `E'` is acting by the restriction of `g` to `E` and
then extending. -/
theorem adeleTransition_adeleGaloisAction {E E' : Ω} (h : E ≤ E') (g : AbsoluteGaloisGroup K)
    (a : AdeleRing (𝓞 E) E) :
    adeleTransition h (GlobalNumberFields.adeleGaloisAction K E (g.restrictNormal E) a) =
      GlobalNumberFields.adeleGaloisAction K E' (g.restrictNormal E') (adeleTransition h a) := by
  refine RingHom.congr_fun (AdeleRing.ringHom_ext (f := (adeleTransition h).comp
      (GlobalNumberFields.adeleGaloisAction K E (g.restrictNormal E)).toRingHom)
    (g := (GlobalNumberFields.adeleGaloisAction K E' (g.restrictNormal E')).toRingHom.comp
      (adeleTransition h)) (𝓞 E) E
    ((continuous_adeleTransition _).comp (GlobalNumberFields.continuous_adeleGaloisAction _ _ _))
    ((GlobalNumberFields.continuous_adeleGaloisAction _ _ _).comp (continuous_adeleTransition _))
    (fun x ↦ ?_) fun _ h₁ h₂ ↦ ?_) a
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      GlobalNumberFields.adeleGaloisAction_algebraMap, adeleTransition_algebraMap]
    congr 1
    apply Subtype.ext
    simp [AlgEquiv.restrictNormal_apply]
  · have l := adeleGaloisAction_fst_snd E (g.restrictNormal E) h₁ h₂
    have r := adeleTransition_fst_snd h h₁ h₂
    exact Prod.ext ((adeleTransition_fst_snd h l.1 l.2).1.trans
        (adeleGaloisAction_fst_snd E' (g.restrictNormal E') r.1 r.2).1.symm)
      ((adeleTransition_fst_snd h l.1 l.2).2.trans
        (adeleGaloisAction_fst_snd E' (g.restrictNormal E') r.1 r.2).2.symm)

variable (K) in
/-- **The action of `G_K` on the ideles of a finite Galois subextension `E`**, through the
restriction `G_K → Gal(E/K)` and the Galois action on adeles. It is a definition rather than an
instance, so that it does not compete with other actions on idele groups; it is the action for
which the transition maps of ideles are equivariant. See note [reducible non-instances]. -/
abbrev ideleGroupMulDistribMulAction (E : Ω) :
    MulDistribMulAction (AbsoluteGaloisGroup K) (IdeleGroup (𝓞 E) E) :=
  letI : MulSemiringAction (AbsoluteGaloisGroup K) (AdeleRing (𝓞 E) E) :=
    MulSemiringAction.compHom _
      ((GlobalNumberFields.adeleGaloisAction K E).comp (AlgEquiv.restrictNormalHom E))
  Units.mulDistribMulActionRight

attribute [local instance high] ideleGroupMulDistribMulAction

/-- In `ideleGroupMulDistribMulAction`, `g ∈ G_K` acts on the underlying adele of an idele of `E`
by the Galois action of its restriction to `Gal(E/K)`. -/
theorem coe_ideleGroupMulDistribMulAction_smul (E : Ω) (g : AbsoluteGaloisGroup K)
    (a : IdeleGroup (𝓞 E) E) :
    ((g • a : IdeleGroup (𝓞 E) E) : AdeleRing (𝓞 E) E) =
      GlobalNumberFields.adeleGaloisAction K E (g.restrictNormal E) a :=
  (rfl)

variable (K) in
/-- The extension map of ideles `I_E → I_{E'}` along an inclusion `E ≤ E'` of finite Galois
subextensions, as a `G_K`-equivariant homomorphism. These are the transition maps of the direct
system whose limit is `IdeleCoeff K`. -/
def ideleTransition (E E' : Ω) (h : E ≤ E') :
    IdeleGroup (𝓞 E) E →*[AbsoluteGaloisGroup K] IdeleGroup (𝓞 E') E' where
  toMonoidHom :=
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    GlobalNumberFields.ideleExtension E E'
  map_smul' g a := by
    let := (IntermediateField.inclusion h).toRingHom.toAlgebra
    apply Units.ext
    simp only [MonoidHom.id_apply, MonoidHom.toOneHom_coe, OneHom.toFun_eq_coe,
      coe_ideleGroupMulDistribMulAction_smul, GlobalNumberFields.coe_ideleExtension]
    exact adeleTransition_adeleGaloisAction h g a

/-- The underlying adele of the extension of an idele is the extension of its underlying adele. -/
@[simp]
theorem coe_ideleTransition {E E' : Ω} (h : E ≤ E') (a : IdeleGroup (𝓞 E) E) :
    (ideleTransition K E E' h a : AdeleRing (𝓞 E') E') = adeleTransition h a := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact GlobalNumberFields.coe_ideleExtension E E' a

/-- The extension of a principal idele is the principal idele of the same field element. -/
theorem ideleTransition_unitEmbedding {E E' : Ω} (h : E ≤ E') (u : Eˣ) :
    ideleTransition K E E' h (IdeleGroup.unitEmbedding (𝓞 E) E u) =
      IdeleGroup.unitEmbedding (𝓞 E') E' (Units.map (IntermediateField.inclusion h) u) := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  exact GlobalNumberFields.ideleExtension_unitEmbedding E E' u

/-- The idele groups of the finite Galois subextensions of `Kˢ/K` form a directed system along
the extension maps. -/
instance : DirectedSystem (fun E : Ω ↦ IdeleGroup (𝓞 E) E) (ideleTransition K · · ·) where
  map_self _ a := Units.ext <| by rw [coe_ideleTransition, adeleTransition_self]; rfl
  map_map _ _ _ h h' a := Units.ext <| by
    rw [coe_ideleTransition, coe_ideleTransition, coe_ideleTransition,
      ← adeleTransition_comp h h', RingHom.comp_apply]

/-! ### The ideles of the separable closure -/

variable (K) in
/-- **The ideles of `Kˢ`**, written additively: the direct limit of the idele groups of the
finite Galois subextensions of `Kˢ/K` along the extension maps. Its elements are read through
`ideleCoeffOf` (`exists_ideleCoeffOf_eq`). -/
def IdeleCoeff : Type _ :=
  Additive (DirectLimit (fun E : Ω ↦ IdeleGroup (𝓞 E) E) (ideleTransition K))

instance : AddCommGroup (IdeleCoeff K) :=
  inferInstanceAs (AddCommGroup (Additive (DirectLimit _ (ideleTransition K))))

-- The action is assembled from Mathlib's `DirectLimit` instance by name: instance search for the
-- family of level actions it needs does not terminate within the default budget.
instance : DistribMulAction (AbsoluteGaloisGroup K) (IdeleCoeff K) :=
  letI : MulDistribMulAction (AbsoluteGaloisGroup K)
      (DirectLimit (fun E : Ω ↦ IdeleGroup (𝓞 E) E) (ideleTransition K)) :=
    DirectLimit.instMulDistribMulActionOfMulActionHomClass
  inferInstanceAs (DistribMulAction (AbsoluteGaloisGroup K)
    (Additive (DirectLimit (fun E : Ω ↦ IdeleGroup (𝓞 E) E) (ideleTransition K))))

instance : TopologicalSpace (IdeleCoeff K) := ⊥

instance : DiscreteTopology (IdeleCoeff K) := ⟨rfl⟩

variable (K) in
/-- The canonical map from the ideles of `E` to the direct limit, multiplicatively. -/
private def ideleLimitOf (E : Ω) :
    IdeleGroup (𝓞 E) E →* DirectLimit (fun E : Ω ↦ IdeleGroup (𝓞 E) E) (ideleTransition K) where
  toFun a := ⟦⟨E, a⟩⟧
  map_one' :=
    (DirectLimit.one_def (G := fun E : Ω ↦ IdeleGroup (𝓞 E) E) (f := ideleTransition K) E).symm
  map_mul' a b :=
    (DirectLimit.mul_def (G := fun E : Ω ↦ IdeleGroup (𝓞 E) E) (f := ideleTransition K) E a b).symm

variable (K) in
/-- **The ideles of a finite Galois subextension `E` as ideles of `Kˢ`**, written additively. -/
def ideleCoeffOf (E : Ω) : Additive (IdeleGroup (𝓞 E) E) →+ IdeleCoeff K :=
  (ideleLimitOf K E).toAdditive

/-- An idele of `E` and its extension to `E'` are the same idele of `Kˢ`. -/
@[simp]
theorem ideleCoeffOf_ideleTransition {E E' : Ω} (h : E ≤ E') (a : IdeleGroup (𝓞 E) E) :
    ideleCoeffOf K E' (.ofMul (ideleTransition K E E' h a)) = ideleCoeffOf K E (.ofMul a) :=
  congrArg Additive.ofMul
    (DirectLimit.mk_apply (F := fun E : Ω ↦ IdeleGroup (𝓞 E) E) (f := ideleTransition K) E E' a h)

/-- **Every idele of `Kˢ` is an idele of a finite Galois subextension.** -/
theorem exists_ideleCoeffOf_eq (x : IdeleCoeff K) :
    ∃ (E : Ω) (a : IdeleGroup (𝓞 E) E), ideleCoeffOf K E (.ofMul a) = x := by
  obtain ⟨E, a, ha⟩ := DirectLimit.exists_eq_mk (ideleTransition K) (Additive.toMul x)
  exact ⟨E, a, congrArg Additive.ofMul ha.symm⟩

/-- An idele of `E` vanishes in the ideles of `Kˢ` exactly when its extension to some larger
finite Galois subextension is trivial. -/
theorem ideleCoeffOf_eq_zero_iff {E : Ω} {a : IdeleGroup (𝓞 E) E} :
    ideleCoeffOf K E (.ofMul a) = 0 ↔ ∃ (E' : Ω) (h : E ≤ E'), ideleTransition K E E' h a = 1 :=
  Additive.toMul.injective.eq_iff.symm.trans
    (DirectLimit.exists_eq_one (G := fun E : Ω ↦ IdeleGroup (𝓞 E) E) (f := ideleTransition K)
      ⟨E, a⟩)

/-- Two homomorphisms out of the ideles of `Kˢ` agree once they agree on the ideles of every
finite Galois subextension. -/
@[ext]
theorem IdeleCoeff.hom_ext {M : Type*} [AddMonoid M] {φ ψ : IdeleCoeff K →+ M}
    (h : ∀ E : Ω, φ.comp (ideleCoeffOf K E) = ψ.comp (ideleCoeffOf K E)) : φ = ψ := by
  ext x
  obtain ⟨E, a, rfl⟩ := exists_ideleCoeffOf_eq x
  exact DFunLike.congr_fun (h E) (.ofMul a)

variable (K) in
/-- **The universal property of the ideles of `Kˢ`**: homomorphisms out of the ideles of the
finite Galois subextensions of `Kˢ/K` that are compatible with the extension maps induce a
homomorphism out of the ideles of `Kˢ` (`IdeleCoeff.lift_ideleCoeffOf`). -/
def IdeleCoeff.lift {M : Type*} [AddCommMonoid M]
    (φ : ∀ E : Ω, Additive (IdeleGroup (𝓞 E) E) →+ M)
    (hφ : ∀ (E E' : Ω) (h : E ≤ E') (a : IdeleGroup (𝓞 E) E),
      φ E' (.ofMul (ideleTransition K E E' h a)) = φ E (.ofMul a)) :
    IdeleCoeff K →+ M :=
  MonoidHom.toAdditiveLeft
    { toFun := DirectLimit.lift (ideleTransition K)
        (fun E a ↦ AddMonoidHom.toMultiplicativeRight (φ E) a)
        fun E E' h a ↦ congrArg Multiplicative.ofAdd (hφ E E' h a).symm
      map_one' := DirectLimit.lift_one (fun E ↦ AddMonoidHom.toMultiplicativeRight (φ E)) _
      map_mul' := DirectLimit.lift_mul (fun E ↦ AddMonoidHom.toMultiplicativeRight (φ E)) _ }

/-- The homomorphism induced by compatible homomorphisms out of the ideles of the finite Galois
subextensions restricts to each of them on the ideles of that subextension. -/
@[simp]
theorem IdeleCoeff.lift_ideleCoeffOf {M : Type*} [AddCommMonoid M]
    (φ : ∀ E : Ω, Additive (IdeleGroup (𝓞 E) E) →+ M) (hφ) (E : Ω)
    (a : Additive (IdeleGroup (𝓞 E) E)) :
    IdeleCoeff.lift K φ hφ (ideleCoeffOf K E a) = φ E a := by
  -- A bare `rfl` would make this a `dsimp` lemma, which needs the carrier definitions exposed.
  unfold IdeleCoeff.lift
  rfl

/-- **The Galois action on the ideles of `Kˢ`**: `g ∈ G_K` acts on the ideles of `E` through its
restriction to `Gal(E/K)`. -/
@[simp]
theorem smul_ideleCoeffOf (g : AbsoluteGaloisGroup K) (E : Ω) (a : IdeleGroup (𝓞 E) E) :
    g • ideleCoeffOf K E (.ofMul a) = ideleCoeffOf K E
      (.ofMul (Units.map (GlobalNumberFields.adeleGaloisAction K E (g.restrictNormal E)) a)) :=
  (rfl)

/-- The subgroup of `G_K` fixing `E` fixes the ideles of `E`. -/
theorem smul_ideleCoeffOf_of_mem_fixingSubgroup {g : AbsoluteGaloisGroup K} {E : Ω}
    (hg : g ∈ (E : IntermediateField K (SeparableClosure K)).fixingSubgroup)
    (a : IdeleGroup (𝓞 E) E) : g • ideleCoeffOf K E (.ofMul a) = ideleCoeffOf K E (.ofMul a) := by
  have h1 : g.restrictNormal E = 1 :=
    (AlgEquiv.restrictNormal_eq_one_iff _ g).2 fun x hx ↦ hg ⟨x, hx⟩
  rw [smul_ideleCoeffOf, h1, map_one]
  rfl

/-- **The ideles of `Kˢ` are a discrete `G_K`-module**: the stabilizer of an idele of `E`
contains the open subgroup fixing `E`. -/
instance : ContinuousSMul (AbsoluteGaloisGroup K) (IdeleCoeff K) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun x ↦ ?_
  obtain ⟨E, a, rfl⟩ := exists_ideleCoeffOf_eq x
  exact Subgroup.isOpen_mono (fun g hg ↦ smul_ideleCoeffOf_of_mem_fixingSubgroup hg a)
    (E : IntermediateField K (SeparableClosure K)).fixingSubgroup_isOpen

/-! ### Galois descent for the ideles of `Kˢ` -/

/-- The extension map of ideles along an inclusion of finite Galois subextensions of `Kˢ/K` is
injective. -/
theorem ideleTransition_injective {E E' : Ω} (h : E ≤ E') :
    Function.Injective (ideleTransition K E E' h) := fun a b hab ↦ by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  refine GlobalNumberFields.ideleExtension_injective E E' (Units.ext ?_)
  rw [GlobalNumberFields.coe_ideleExtension, GlobalNumberFields.coe_ideleExtension,
    ← adeleTransition_apply, ← adeleTransition_apply, ← coe_ideleTransition,
    ← coe_ideleTransition, hab]

/-- **The ideles of a finite Galois subextension `E` embed in the ideles of `Kˢ`.** -/
theorem ideleCoeffOf_injective (E : Ω) : Function.Injective (ideleCoeffOf K E) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  obtain ⟨E', h, h1⟩ := ideleCoeffOf_eq_zero_iff.1 ha
  exact Additive.toMul.injective (ideleTransition_injective h (h1.trans (map_one _).symm))

/-- An idele of a finite Galois subextension `E'` that is fixed by the subgroup of `G_K` fixing
a smaller `E` is fixed by `Gal(E'/E)`. -/
private theorem adeleGaloisAction_eq_self {E E' : Ω} (h : E ≤ E') {a : IdeleGroup (𝓞 E') E'}
    (ha : ∀ g ∈ (E : IntermediateField K (SeparableClosure K)).fixingSubgroup,
      g • ideleCoeffOf K E' (.ofMul a) = ideleCoeffOf K E' (.ofMul a)) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ∀ σ : E' ≃ₐ[E] E', GlobalNumberFields.adeleGaloisAction E E' σ a = a := by
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro σ
  -- Lift `σ` to an element `g` of `G_K`; it fixes `E`, because `σ` does.
  set g := (σ.restrictScalars K).liftNormal (SeparableClosure K)
  have hg : g.restrictNormal E' = σ.restrictScalars K := AlgEquiv.restrict_liftNormal _ _
  have hgE : g ∈ (E : IntermediateField K (SeparableClosure K)).fixingSubgroup := by
    rintro ⟨y, hy⟩
    have := AlgEquiv.restrictNormal_commutes g E' (IntermediateField.inclusion h ⟨y, hy⟩)
    rw [hg, AlgEquiv.restrictScalars_apply] at this
    exact this.symm.trans (congrArg Subtype.val (σ.commutes ⟨y, hy⟩))
  have hfix := ha g hgE
  rw [smul_ideleCoeffOf] at hfix
  have hfix := congrArg Units.val (Additive.ofMul.injective (ideleCoeffOf_injective E' hfix))
  rw [Units.coe_map, MonoidHom.coe_ofClass, hg, GlobalNumberFields.adeleGaloisAction_apply] at hfix
  rwa [AlgEquiv.toRingEquiv_restrictScalars, ← GlobalNumberFields.adeleGaloisAction_apply] at hfix

/-- **Galois descent for the ideles of `Kˢ`**: an idele of `Kˢ` is an idele of the finite Galois
subextension `E` exactly when it is fixed by the subgroup of `G_K` fixing `E`. -/
theorem mem_range_ideleCoeffOf_iff {E : Ω} {x : IdeleCoeff K} :
    x ∈ (ideleCoeffOf K E).range ↔
      ∀ g ∈ (E : IntermediateField K (SeparableClosure K)).fixingSubgroup, g • x = x := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨a, rfl⟩ g hg
    exact smul_ideleCoeffOf_of_mem_fixingSubgroup hg a.toMul
  -- Write `x` as an idele of a finite Galois subextension `E'` containing `E`.
  obtain ⟨E₀, a₀, rfl⟩ := exists_ideleCoeffOf_eq x
  have h : E ≤ E ⊔ E₀ := le_sup_left
  rw [← ideleCoeffOf_ideleTransition (le_sup_right : E₀ ≤ E ⊔ E₀)] at hx ⊢
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E ↥(E ⊔ E₀) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsGalois E ↥(E ⊔ E₀) := IsGalois.tower_top_of_isGalois K E _
  obtain ⟨b, hb⟩ := (GlobalNumberFields.mem_range_ideleExtension_iff E ↥(E ⊔ E₀)).2
    (adeleGaloisAction_eq_self h hx)
  refine ⟨.ofMul b, ?_⟩
  rw [← ideleCoeffOf_ideleTransition h, ← hb]
  refine congrArg (fun c ↦ ideleCoeffOf K _ (.ofMul c)) (Units.ext ?_)
  rw [coe_ideleTransition, adeleTransition_apply, GlobalNumberFields.coe_ideleExtension]

/-! ### The principal ideles -/

/-- The principal ideles of two units of finite Galois subextensions agree in the ideles of `Kˢ`
when the units agree in `Kˢ`. -/
private theorem ideleCoeffOf_unitEmbedding_eq {E E' : Ω} {u : Eˣ} {u' : E'ˣ}
    (h : ((u : E) : SeparableClosure K) = (u' : E')) :
    ideleCoeffOf K E (.ofMul (IdeleGroup.unitEmbedding (𝓞 E) E u)) =
      ideleCoeffOf K E' (.ofMul (IdeleGroup.unitEmbedding (𝓞 E') E' u')) := by
  rw [← ideleCoeffOf_ideleTransition (le_sup_left : E ≤ E ⊔ E'),
    ← ideleCoeffOf_ideleTransition (le_sup_right : E' ≤ E ⊔ E'),
    ideleTransition_unitEmbedding, ideleTransition_unitEmbedding]
  congr 3
  exact Units.ext (Subtype.ext h)

/-- A unit of `Kˢ` lying in `E`, as a unit of `E`. -/
private def unitOfMem (E : Ω) (x : UnitsCoeff K)
    (hx : (x.toMul : SeparableClosure K) ∈ (E : IntermediateField K (SeparableClosure K))) : Eˣ :=
  Units.mk0 ⟨x.toMul, hx⟩ fun h ↦ x.toMul.ne_zero (congrArg Subtype.val h)

variable (K) in
/-- The principal idele of a unit of `Kˢ` lying in `E`, computed in the ideles of `E`. -/
private def principalIdeleAt (E : Ω) (x : UnitsCoeff K)
    (hx : (x.toMul : SeparableClosure K) ∈ (E : IntermediateField K (SeparableClosure K))) :
    IdeleCoeff K :=
  ideleCoeffOf K E (.ofMul (IdeleGroup.unitEmbedding (𝓞 E) E (unitOfMem E x hx)))

omit [NumberField K] in
private theorem unitOfMem_zero (E : Ω) : unitOfMem E 0 (one_mem _) = 1 :=
  Units.ext (Subtype.ext rfl)

omit [NumberField K] in
private theorem unitOfMem_add (E : Ω) {x y : UnitsCoeff K} (hx hy) :
    unitOfMem E (x + y) (mul_mem hx hy) = unitOfMem E x hx * unitOfMem E y hy :=
  Units.ext (Subtype.ext rfl)

private theorem principalIdeleAt_zero (E : Ω) : principalIdeleAt K E 0 (one_mem _) = 0 := by
  rw [principalIdeleAt, unitOfMem_zero, map_one, ofMul_one, map_zero]

private theorem principalIdeleAt_add (E : Ω) {x y : UnitsCoeff K} (hx hy) :
    principalIdeleAt K E (x + y) (mul_mem hx hy) =
      principalIdeleAt K E x hx + principalIdeleAt K E y hy := by
  rw [principalIdeleAt, unitOfMem_add, map_mul, ofMul_mul, map_add, principalIdeleAt,
    principalIdeleAt]

private theorem principalIdeleAt_eq {E E' : Ω} (x : UnitsCoeff K) (hx hx') :
    principalIdeleAt K E x hx = principalIdeleAt K E' x hx' :=
  ideleCoeffOf_unitEmbedding_eq rfl

private theorem mem_adjoin (x : UnitsCoeff K) :
    (x.toMul : SeparableClosure K) ∈ ((FiniteGaloisIntermediateField.adjoin K
      {(x.toMul : SeparableClosure K)} : Ω) : IntermediateField K (SeparableClosure K)) :=
  FiniteGaloisIntermediateField.subset_adjoin K _ rfl

variable (K) in
/-- **The principal ideles of `Kˢ`**: a unit `x` of `Kˢ` lies in a finite Galois subextension `E`
and is sent to its principal idele in the ideles of `E`, independently of `E`
(`principalIdele_ofMul_map_algebraMap`). This is the `G_K`-equivariant embedding
`(Kˢ)ˣ → I_{Kˢ}` (`principalIdele_injective`). -/
def principalIdele : UnitsCoeff K →+[AbsoluteGaloisGroup K] IdeleCoeff K where
  toFun x := principalIdeleAt K _ x (mem_adjoin x)
  map_zero' := (principalIdeleAt_eq (E' := ⊥) 0 _ (one_mem _)).trans (principalIdeleAt_zero ⊥)
  map_add' x y := by
    let E : Ω := FiniteGaloisIntermediateField.adjoin K {(x.toMul : SeparableClosure K)} ⊔
      FiniteGaloisIntermediateField.adjoin K {(y.toMul : SeparableClosure K)}
    have hx : (x.toMul : SeparableClosure K) ∈ (E : IntermediateField K (SeparableClosure K)) :=
      (le_sup_left : _ ≤ E) (mem_adjoin x)
    have hy : (y.toMul : SeparableClosure K) ∈ (E : IntermediateField K (SeparableClosure K)) :=
      (le_sup_right : _ ≤ E) (mem_adjoin y)
    rw [principalIdeleAt_eq (E' := E) x _ hx, principalIdeleAt_eq (E' := E) y _ hy,
      principalIdeleAt_eq (E' := E) (x + y) _ (mul_mem hx hy), principalIdeleAt_add]
  map_smul' g x := by
    let E : Ω := FiniteGaloisIntermediateField.adjoin K {(x.toMul : SeparableClosure K)}
    have hgx : ((g • x).toMul : SeparableClosure K) =
        (g.restrictNormal E ⟨x.toMul, mem_adjoin x⟩ : SeparableClosure K) := by
      rw [AlgEquiv.restrictNormal_apply, Additive.toMul_smul, AlgEquiv.smul_units_def,
        Units.coe_map, MonoidHom.coe_ofClass]
    have hgx' : ((g • x).toMul : SeparableClosure K) ∈
        (E : IntermediateField K (SeparableClosure K)) := hgx ▸ SetLike.coe_mem _
    rw [MonoidHom.id_apply, principalIdeleAt_eq (E' := E) (g • x) _ hgx', principalIdeleAt,
      principalIdeleAt, smul_ideleCoeffOf]
    congr 2
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass, IdeleGroup.val_unitEmbedding_apply,
      GlobalNumberFields.adeleGaloisAction_algebraMap]
    congr 1
    exact Subtype.ext hgx

private theorem principalIdele_eq_ideleCoeffOf (E : Ω) (x : UnitsCoeff K) (hx) :
    principalIdele K x =
      ideleCoeffOf K E (.ofMul (IdeleGroup.unitEmbedding (𝓞 E) E (unitOfMem E x hx))) :=
  principalIdeleAt_eq x _ hx

/-- **The principal idele of a unit of a finite Galois subextension `E`** is its principal idele
in the ideles of `E`. -/
theorem principalIdele_ofMul_map_algebraMap (E : Ω) (u : Eˣ) :
    principalIdele K (.ofMul (Units.map (algebraMap E (SeparableClosure K)).toMonoidHom u)) =
      ideleCoeffOf K E (.ofMul (IdeleGroup.unitEmbedding (𝓞 E) E u)) := by
  rw [principalIdele_eq_ideleCoeffOf E
    (.ofMul (Units.map (algebraMap E (SeparableClosure K)).toMonoidHom u)) (u : E).property]
  congr 3
  exact Units.ext (Subtype.ext rfl)

/-- **The principal ideles embed `(Kˢ)ˣ` in the ideles of `Kˢ`**: a field element is a unit of
some adele ring only through its diagonal image, which is injective. -/
theorem principalIdele_injective : Function.Injective (principalIdele K) := by
  refine (injective_iff_map_eq_zero (principalIdele K)).2 fun x hx ↦ ?_
  let E : Ω := FiniteGaloisIntermediateField.adjoin K {(x.toMul : SeparableClosure K)}
  rw [principalIdele_eq_ideleCoeffOf E x (mem_adjoin x)] at hx
  obtain ⟨E', hEE', h1⟩ := ideleCoeffOf_eq_zero_iff.1 hx
  rw [ideleTransition_unitEmbedding, ← map_one (IdeleGroup.unitEmbedding (𝓞 E') E')] at h1
  have h2 := congrArg (fun u : IdeleGroup (𝓞 E') E' ↦ (u : AdeleRing (𝓞 E') E')) h1
  simp only [IdeleGroup.val_unitEmbedding_apply] at h2
  exact Additive.toMul.injective (Units.ext
    (congrArg Subtype.val ((AdeleRing.algebraMap_injective (𝓞 E') E') h2)))

/-- The principal ideles form a `G_K`-stable subgroup of the ideles of `Kˢ`. -/
theorem smul_mem_range_principalIdele (g : AbsoluteGaloisGroup K) (x : IdeleCoeff K)
    (hx : x ∈ (principalIdele K).toAddMonoidHom.range) :
    g • x ∈ (principalIdele K).toAddMonoidHom.range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨g • y, map_smul (principalIdele K) g y⟩

/-! ### The idele classes of the separable closure -/

variable (K) in
/-- **The idele classes of `Kˢ`**, written additively: the ideles of `Kˢ` modulo the principal
ideles. Its elements are read through `ideleClassMk` (`ideleClassMk_surjective`). -/
def IdeleClassCoeff : Type _ :=
  IdeleCoeff K ⧸ (principalIdele K).toAddMonoidHom.range

instance : AddCommGroup (IdeleClassCoeff K) :=
  inferInstanceAs (AddCommGroup (IdeleCoeff K ⧸ (principalIdele K).toAddMonoidHom.range))

instance : DistribMulAction (AbsoluteGaloisGroup K) (IdeleClassCoeff K) :=
  letI := AddSubgroup.quotientDistribMulAction (principalIdele K).toAddMonoidHom.range
    smul_mem_range_principalIdele
  inferInstanceAs (DistribMulAction (AbsoluteGaloisGroup K)
    (IdeleCoeff K ⧸ (principalIdele K).toAddMonoidHom.range))

instance : TopologicalSpace (IdeleClassCoeff K) := ⊥

instance : DiscreteTopology (IdeleClassCoeff K) := ⟨rfl⟩

variable (K) in
/-- The `G_K`-equivariant quotient map from the ideles of `Kˢ` to its idele classes. -/
def ideleClassMk : IdeleCoeff K →+[AbsoluteGaloisGroup K] IdeleClassCoeff K where
  __ := QuotientAddGroup.mk' (principalIdele K).toAddMonoidHom.range
  map_smul' g x :=
    (AddSubgroup.quotientDistribMulAction_smul_mk _ smul_mem_range_principalIdele g x).symm

/-- Every idele class of `Kˢ` is the class of an idele. -/
theorem ideleClassMk_surjective : Function.Surjective (ideleClassMk K) :=
  QuotientAddGroup.mk'_surjective (principalIdele K).toAddMonoidHom.range

/-- **The kernel of the quotient map is the principal ideles.** -/
theorem ideleClassMk_eq_zero_iff {x : IdeleCoeff K} :
    ideleClassMk K x = 0 ↔ ∃ y, principalIdele K y = x :=
  QuotientAddGroup.eq_zero_iff (N := (principalIdele K).toAddMonoidHom.range) x

/-- The class of a principal idele vanishes. -/
@[simp]
theorem ideleClassMk_principalIdele (y : UnitsCoeff K) : ideleClassMk K (principalIdele K y) = 0 :=
  ideleClassMk_eq_zero_iff.2 ⟨y, rfl⟩

variable (K) in
/-- **The universal property of the idele classes of `Kˢ`**: a homomorphism out of the ideles of
`Kˢ` vanishing on the principal ideles induces a homomorphism out of the idele classes
(`IdeleClassCoeff.lift_ideleClassMk`). -/
def IdeleClassCoeff.lift {M : Type*} [AddCommGroup M] (φ : IdeleCoeff K →+ M)
    (hφ : ∀ y, φ (principalIdele K y) = 0) : IdeleClassCoeff K →+ M :=
  QuotientAddGroup.lift _ φ fun _ ⟨y, hy⟩ ↦ hy ▸ hφ y

/-- The homomorphism induced on the idele classes of `Kˢ` sends the class of an idele to the
value of the original homomorphism on it. -/
@[simp]
theorem IdeleClassCoeff.lift_ideleClassMk {M : Type*} [AddCommGroup M] (φ : IdeleCoeff K →+ M)
    (hφ) (x : IdeleCoeff K) : IdeleClassCoeff.lift K φ hφ (ideleClassMk K x) = φ x :=
  QuotientAddGroup.lift_mk' _ _ x

/-- Two homomorphisms out of the idele classes of `Kˢ` agree once they agree on the classes of
ideles. -/
@[ext]
theorem IdeleClassCoeff.hom_ext {M : Type*} [AddMonoid M] {φ ψ : IdeleClassCoeff K →+ M}
    (h : φ.comp (ideleClassMk K).toAddMonoidHom = ψ.comp (ideleClassMk K).toAddMonoidHom) :
    φ = ψ :=
  QuotientAddGroup.addMonoidHom_ext _ h

/-- **The idele classes of `Kˢ` are a discrete `G_K`-module**: the stabilizer of the class of an
idele contains the stabilizer of the idele. -/
instance : ContinuousSMul (AbsoluteGaloisGroup K) (IdeleClassCoeff K) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun x ↦ ?_
  obtain ⟨x, rfl⟩ := ideleClassMk_surjective x
  refine Subgroup.isOpen_mono (fun g (hg : g • x = x) ↦ ?_)
    (continuousSMul_iff_stabilizer_isOpen.1 inferInstance x)
  rw [MulAction.mem_stabilizer_iff, ← map_smul, hg]

end TauCeti.ClassFieldTheory
