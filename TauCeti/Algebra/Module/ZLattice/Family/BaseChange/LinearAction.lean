/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.LinearAction

/-!
# Equivariant base change of linear actions on families of tori

Let a monoid `Γ` act on `Y` and lift to the family of tori `(Y × E)/Λ` of a period family
`P : Y → (Λ →ₗ[ℤ] E)` through an additive cocycle `R : Γ → Y → E →+ E` and a lattice
representation `ρ : Representation ℤ Γ Λ` (`TauCeti.torusFamilyLinearMulAction`). Given a
monoid homomorphism `σ : Γ' →* Γ`, an action of `Γ'` on `Z`, and a `σ`-equivariant map
`f : Z → Y` (`f (g • z) = σ g • f z`), pulling the cocycle back to `(g, z) ↦ R (σ g) (f z)` and
the representation back to `ρ.comp σ` equips the pulled-back period family `P ∘ f` with an
equivariant linear action of `Γ'`.

The canonical base-change map `[z, v] ↦ [f z, v]` (`TauCeti.torusFamilyBaseChangeMap`) is
`σ`-equivariant for these actions (`TauCeti.torusFamilyBaseChangeMap_linearSMul`), packaged as
`TauCeti.torusFamilyLinearBaseChangeHom`. This construction is functorial in `(σ, f)` and, for
groups `Γ` and `Γ'`, induces a map of second quotients `((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` lying
over `Z/Γ' → Y/Γ` (`TauCeti.orbitRelQuotientMap_torusFamilyLinearProjection_comp_baseChange`).

## Main definitions

* `TauCeti.torusFamilyLinearBaseChangeHom`: the `σ`-equivariant base-change map
  `(Z × E)/Λ →ₑ[σ] (Y × E)/Λ` for linear actions on families of tori.

## Main results

* `TauCeti.linearCocycle_baseChange_one`, `TauCeti.linearCocycle_baseChange_mul`,
  `TauCeti.period_baseChange_equivariant`: the pulled-back cocycle and representation satisfy
  the cocycle and period-equivariance laws on `Z`.
* `TauCeti.torusFamilyBaseChangeMap_linearSMul`: `torusFamilyBaseChangeMap P f` is
  `σ`-equivariant.
* `TauCeti.torusFamilyLinearBaseChangeHom_id`, `TauCeti.torusFamilyLinearBaseChangeHom_comp`:
  functoriality of equivariant base change.
* `TauCeti.continuousConstSMul_torusFamilyBaseChangeLinearMulAction`: continuity of the
  pulled-back linear action on `(Z × E)/Λ`.
* `TauCeti.orbitRelQuotientMap_torusFamilyLinearProjection_comp_baseChange`: the descended
  map of second quotients commutes with the descended family projections.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices, and the actions of discrete groups on them).
-/

public section

open Function

namespace TauCeti

variable {Y Z W Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]

section Monoid

variable {Γ Γ' Γ'' : Type*} [Monoid Γ] [Monoid Γ'] [Monoid Γ'']

/-- Pulling a linear cocycle `R` back along a monoid homomorphism `σ : Γ' →* Γ` and a map
`f : Z → Y` preserves the identity cocycle law. -/
theorem linearCocycle_baseChange_one (R : Γ → Y → E →+ E)
    (hone : ∀ (y : Y) (v : E), R 1 y v = v) (σ : Γ' →* Γ) (f : Z → Y)
    (z : Z) (v : E) : R (σ 1) (f z) v = v := by
  rw [map_one, hone]

variable [MulAction Γ Y] [MulAction Γ' Z] [MulAction Γ'' W]

/-- Pulling a linear cocycle `R` back along `σ : Γ' →* Γ` and a `σ`-equivariant map `f : Z → Y`
preserves the multiplication cocycle law. -/
theorem linearCocycle_baseChange_mul (R : Γ → Y → E →+ E)
    (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
    (σ : Γ' →* Γ) {f : Z → Y} (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (g h : Γ') (z : Z) (v : E) :
    R (σ (g * h)) (f z) v = R (σ g) (f (h • z)) (R (σ h) (f z) v) := by
  rw [map_mul, hmul, hf]

/-- Pulling an equivariant period family `P` back along `σ : Γ' →* Γ` and a `σ`-equivariant map
`f : Z → Y` gives an equivariant period family `P ∘ f` for `ρ.comp σ` and `(g, z) ↦ R (σ g) (f z)`.
-/
theorem period_baseChange_equivariant (R : Γ → Y → E →+ E) (P : Y → Λ →ₗ[ℤ] E)
    (ρ : Representation ℤ Γ Λ)
    (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
    (σ : Γ' →* Γ) {f : Z → Y} (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (g : Γ') (z : Z) (l : Λ) :
    (P ∘ f) (g • z) ((ρ.comp σ) g l) = R (σ g) (f z) ((P ∘ f) z l) := by
  simp only [comp_apply, MonoidHom.comp_apply, hf, hP]

variable (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))

/-- On the covering product spaces, `Prod.map f id : Z × E → Y × E` is `σ`-equivariant for the
lifted linear cocycle actions. -/
theorem linearCocycleMulAction_prodMap_smul (σ : Γ' →* Γ) {f : Z → Y}
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) (g : Γ') (p : Z × E) :
    letI := linearCocycleMulAction R hone hmul
    letI := linearCocycleMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf)
    Prod.map f id (g • p) = σ g • Prod.map f id p := by
  let _ := linearCocycleMulAction R hone hmul
  let _ := linearCocycleMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf)
  simp [hf]

variable (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))

/-- **Equivariance of base change for linear actions.** For a `σ`-equivariant map `f : Z → Y`,
`torusFamilyBaseChangeMap P f` intertwines the pulled-back linear action of `Γ'` on `(Z × E)/Λ`
with the linear action of `Γ` on `(Y × E)/Λ`. -/
@[simp] theorem torusFamilyBaseChangeMap_linearSMul (σ : Γ' →* Γ) {f : Z → Y}
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) (g : Γ')
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
    torusFamilyBaseChangeMap P f (g • x) = σ g • torusFamilyBaseChangeMap P f x := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  let _ := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
  induction x using Quotient.inductionOn with | h p =>
    rcases p with ⟨z, v⟩
    simp [hf]

/-- The `σ`-equivariant base-change map `(Z × E)/Λ →ₑ[σ] (Y × E)/Λ` between families of tori
carrying linear actions. -/
def torusFamilyLinearBaseChangeHom (σ : Γ' →* Γ) (f : Z → Y)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
    AddAction.orbitRel.Quotient Λ (Z × E) →ₑ[σ] AddAction.orbitRel.Quotient Λ (Y × E) :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  letI := torusFamilyLinearMulAction R hone hmul P ρ hP
  letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
  { toFun := torusFamilyBaseChangeMap P f
    map_smul' := torusFamilyBaseChangeMap_linearSMul R hone hmul P ρ hP σ hf }

/-- The underlying function of `torusFamilyLinearBaseChangeHom` is `torusFamilyBaseChangeMap`. -/
@[simp] theorem coe_torusFamilyLinearBaseChangeHom (σ : Γ' →* Γ) (f : Z → Y)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
    ⇑(torusFamilyLinearBaseChangeHom R hone hmul P ρ hP σ f hf) =
      torusFamilyBaseChangeMap P f := (rfl)

/-- Applying `torusFamilyLinearBaseChangeHom` applies `torusFamilyBaseChangeMap`. -/
@[simp] theorem torusFamilyLinearBaseChangeHom_apply (σ : Γ' →* Γ) (f : Z → Y)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
    torusFamilyLinearBaseChangeHom R hone hmul P ρ hP σ f hf x =
      torusFamilyBaseChangeMap P f x := (rfl)

/-- Equivariant base change along the identity homomorphism and the identity map is the identity
`MulActionHom`. -/
@[simp] theorem torusFamilyLinearBaseChangeHom_id :
    letI := periodAddAction P
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    (torusFamilyLinearBaseChangeHom R hone hmul P ρ hP (MonoidHom.id Γ) id
      fun _ _ ↦ rfl).ofEq MonoidHom.coe_id = MulActionHom.id Γ := by
  let _ := periodAddAction P
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  ext x
  exact torusFamilyBaseChangeMap_id P x

/-- Equivariant linear base-change homomorphisms compose in the same order as the base maps and
monoid homomorphisms. -/
theorem torusFamilyLinearBaseChangeHom_comp (σ : Γ' →* Γ) (τ : Γ'' →* Γ') (f : Z → Y)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) (f' : W → Z)
    (hf' : ∀ (g : Γ'') (w : W), f' (g • w) = τ g • f' w) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := periodAddAction (P ∘ (f ∘ f'))
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
    letI := torusFamilyLinearMulAction (fun g w ↦ R ((σ.comp τ) g) ((f ∘ f') w))
      (linearCocycle_baseChange_one R hone (σ.comp τ) (f ∘ f'))
      (linearCocycle_baseChange_mul R hmul (σ.comp τ)
        fun g w ↦ by simp only [comp_apply, MonoidHom.comp_apply, hf', hf])
      (P ∘ (f ∘ f')) (ρ.comp (σ.comp τ))
      (period_baseChange_equivariant R P ρ hP (σ.comp τ)
        fun g w ↦ by simp only [comp_apply, MonoidHom.comp_apply, hf', hf])
    letI : CompTriple ⇑τ ⇑σ ⇑(σ.comp τ) := ⟨rfl⟩
    (torusFamilyLinearBaseChangeHom R hone hmul P ρ hP σ f hf).comp
      (torusFamilyLinearBaseChangeHom (fun g z ↦ R (σ g) (f z))
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hP σ hf) τ f' hf') =
      torusFamilyLinearBaseChangeHom R hone hmul P ρ hP (σ.comp τ) (f ∘ f')
        (fun g w ↦ by simp only [comp_apply, MonoidHom.comp_apply, hf', hf]) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := periodAddAction (P ∘ (f ∘ f'))
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  let _ := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
  let _ := torusFamilyLinearMulAction (fun g w ↦ R ((σ.comp τ) g) ((f ∘ f') w))
    (linearCocycle_baseChange_one R hone (σ.comp τ) (f ∘ f'))
    (linearCocycle_baseChange_mul R hmul (σ.comp τ)
      fun g w ↦ by simp only [comp_apply, MonoidHom.comp_apply, hf', hf])
    (P ∘ (f ∘ f')) (ρ.comp (σ.comp τ))
    (period_baseChange_equivariant R P ρ hP (σ.comp τ)
      fun g w ↦ by simp only [comp_apply, MonoidHom.comp_apply, hf', hf])
  let _ : CompTriple ⇑τ ⇑σ ⇑(σ.comp τ) := ⟨rfl⟩
  ext x
  exact torusFamilyBaseChangeMap_comp P f f' x

omit [Monoid Γ''] [MulAction Γ'' W] in
/-- If `Γ'` acts continuously on `Z`, `f : Z → Y` is continuous and `σ`-equivariant, and each
linear evaluation `(y, v) ↦ R g y v` is continuous, then the pulled-back linear action of `Γ'` on
`(Z × E)/Λ` acts by continuous maps. -/
theorem continuousConstSMul_torusFamilyBaseChangeLinearMulAction
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace E] [ContinuousConstSMul Γ' Z]
    (σ : Γ' →* Γ) {f : Z → Y} (hf_cont : Continuous f)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hR : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2) :
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
    ContinuousConstSMul Γ' (AddAction.orbitRel.Quotient Λ (Z × E)) :=
  continuousConstSMul_torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
    fun g ↦ (hR (σ g)).comp (hf_cont.prodMap continuous_id)

end Monoid

section Group

variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] [MulAction Γ Y] [MulAction Γ' Z]
  (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))

/-- **Naturality of the descended projection for linear actions.** For group actions and a
`σ`-equivariant base map `f : Z → Y`, the map of second quotients
`((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` induced by `torusFamilyLinearBaseChangeHom` forms a commutative
square with the descended family projections to `Z/Γ'` and `Y/Γ`. -/
theorem orbitRelQuotientMap_torusFamilyLinearProjection_comp_baseChange
    (σ : Γ' →* Γ) (f : Z → Y) (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyLinearMulAction R hone hmul P ρ hP
    letI := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
    MulActionHom.orbitRelQuotientMap
        (⟨torusFamilyProjection P, torusFamilyProjection_smul R hone hmul P ρ hP⟩ :
          AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y) ∘
      MulActionHom.orbitRelQuotientMap
        (torusFamilyLinearBaseChangeHom R hone hmul P ρ hP σ f hf) =
      MulActionHom.orbitRelQuotientMap (σ := σ) ⟨f, hf⟩ ∘
        MulActionHom.orbitRelQuotientMap
          (⟨torusFamilyProjection (P ∘ f),
            torusFamilyProjection_smul (fun g z ↦ R (σ g) (f z))
              (linearCocycle_baseChange_one R hone σ f)
              (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
              (period_baseChange_equivariant R P ρ hP σ hf)⟩ :
            AddAction.orbitRel.Quotient Λ (Z × E) →[Γ'] Z) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyLinearMulAction R hone hmul P ρ hP
  let _ := torusFamilyLinearMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
  funext q
  induction q using Quotient.ind with | _ x =>
    simp only [comp_apply, MulActionHom.orbitRelQuotientMap_mk,
      torusFamilyLinearBaseChangeHom_apply]
    exact congrArg (Quotient.mk _) (torusFamilyProjection_baseChangeMap P f x)

end Group

end TauCeti
