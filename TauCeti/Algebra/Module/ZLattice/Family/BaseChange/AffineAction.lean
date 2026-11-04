/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.AffineAction
public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.LinearAction
public import TauCeti.Algebra.Module.ZLattice.Family.Stabilizer
public import TauCeti.Topology.Algebra.GroupAction.FreeLocus
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# Equivariant base change of affine actions on families of tori

Let a monoid `Γ` act on `Y` and act on the family of tori `(Y × E)/Λ` of a period family
`P : Y → (Λ →ₗ[ℤ] E)` by the affine action `g • [y, v] = R g y v +ᵥ b g y`
(`TauCeti.torusFamilyAffineMulAction`), where `b g y` is a point of `(Y × E)/Λ` lying over
`g • y`. Given a monoid homomorphism `σ : Γ' →* Γ`, an action of `Γ'` on `Z`, and a
`σ`-equivariant map `f : Z → Y` (`f (g • z) = σ g • f z`), this file pulls the affine action back
to the period family `P ∘ f` over `Z`.

Because the translation section `b g` takes values in the torus family `(Y × E)/Λ` rather than in
the covering vector space `E`, pulling `b` back cannot be written by composing a vector lift with
`f`. Instead, for each `g : Γ'` and `z : Z`, the point `b (σ g) (f z)` lies over
`σ g • f z = f (g • z)`, so the algebraic pullback equivalence `TauCeti.torusFamilyBaseChangeEquiv`
lifts `(g • z, b (σ g) (f z))` to a unique point
`TauCeti.torusFamilyBaseChangeTranslation P f σ hf b hb g z` of `(Z × E)/Λ` lying over `g • z` and
mapping to `b (σ g) (f z)` in `(Y × E)/Λ`. No vector-space lift is chosen.

With this pulled-back translation section:

* `TauCeti.torusFamilyBaseChangeMap_affineMap` shows that `torusFamilyBaseChangeMap P f`
  intertwines the affine maps of `g` and `σ g`;
* `TauCeti.torusFamilyBaseChangeTranslation_one` and
  `TauCeti.torusFamilyBaseChangeTranslation_mul` verify the translation cocycle laws on `(Z × E)/Λ`
  from those on `(Y × E)/Λ`, equipping `(Z × E)/Λ` with `TauCeti.torusFamilyAffineMulAction` and
  giving the `σ`-equivariant map `TauCeti.torusFamilyAffineBaseChangeHom`;
* `TauCeti.continuous_torusFamilyBaseChangeTranslation` and
  `TauCeti.continuousConstSMul_torusFamilyBaseChangeAffineMulAction` transfer continuity through
  the topological pullback homeomorphism `TauCeti.torusFamilyBaseChangeHomeomorph`;
* over a base fixed point `g • z = z`, `TauCeti.torusFamilyFiberLinearPart_baseChange` and
  `TauCeti.torusFamilyFiberTranslationPart_baseChange` identify the fibrewise linear and
  translation parts on the fibre over `z` with those of `σ g` on the fibre over `f z`, so freeness
  of the total-space action transfers whenever `σ` has trivial kernel on base stabilizers
  (`TauCeti.isCancelSMul_torusFamilyBaseChangeAffineMulAction`);
* on the second quotients `((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ`, the induced map commutes with the
  descended projections (`TauCeti.orbitRelQuotientMap_torusFamilyAffineProjection_comp_baseChange`),
  is injective for injective `f` satisfying the orbit-slice condition
  (`TauCeti.orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_injective`), and is an open
  embedding when `f` is an open embedding
  (`TauCeti.isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom`), in particular for
  restriction to `TauCeti.freeLocus Γ Y`
  (`TauCeti.isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_freeLocus`).

## Main definitions

* `TauCeti.torusFamilyBaseChangeTranslation`: pullback of a torus-valued translation section along
  an equivariant base map, defined without vector lifts.
* `TauCeti.torusFamilyAffineBaseChangeHom`: the `σ`-equivariant base-change map
  `(Z × E)/Λ →ₑ[σ] (Y × E)/Λ` for affine actions on families of tori.

## Main results

* `TauCeti.torusFamilyBaseChangeTranslation_one`, `TauCeti.torusFamilyBaseChangeTranslation_mul`:
  the pulled-back translation section satisfies the affine cocycle laws.
* `TauCeti.torusFamilyBaseChangeMap_affineMap`, `TauCeti.torusFamilyBaseChangeMap_affineSMul`,
  `TauCeti.torusFamilyBaseChangeAffineMap_id`, `TauCeti.torusFamilyBaseChangeAffineMap_comp`:
  equivariance and functoriality of base change for affine actions.
* `TauCeti.continuous_torusFamilyBaseChangeTranslation`,
  `TauCeti.continuousConstSMul_torusFamilyBaseChangeAffineMulAction`: continuity of the pulled-back
  translation section and affine action.
* `TauCeti.torusFamilyFiberLinearPart_baseChange`,
  `TauCeti.torusFamilyFiberTranslationPart_baseChange`,
  `TauCeti.isCancelSMul_torusFamilyBaseChangeAffineMulAction`: compatibility with fibrewise
  stabilizer data and transfer of total-space freeness.
* `TauCeti.orbitRelQuotientMap_torusFamilyAffineProjection_comp_baseChange`,
  `TauCeti.orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_injective`,
  `TauCeti.isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom`,
  `TauCeti.isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_freeLocus`: descent
  to the second quotients, open embeddings of equivariant open slices, and restriction to the free
  locus.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices, and the actions of discrete groups on them).
-/

public section

open Function Set Topology

namespace TauCeti

variable {Y Z W Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]

/-! ### Pulling back torus-valued translation sections -/

section Translation

variable {Γ Γ' : Type*} [SMul Γ Y] [SMul Γ' Z] (P : Y → Λ →ₗ[ℤ] E)

/-- **Pullback of a torus-valued translation section.** Given a map `f : Z → Y` intertwining
actions along `σ : Γ' → Γ` (`f (g • z) = σ g • f z`) and a family of sections `b g` of
`(Y × E)/Λ → Y` with `b g y` lying over `g • y`, the point `b (σ g) (f z)` lies over
`σ g • f z = f (g • z)`. The algebraic pullback equivalence `TauCeti.torusFamilyBaseChangeEquiv`
therefore lifts `(g • z, b (σ g) (f z))` to a unique point of `(Z × E)/Λ` over `g • z`, without
choosing vector representatives in `E`. -/
def torusFamilyBaseChangeTranslation (f : Z → Y) (σ : Γ' → Γ)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (g : Γ') (z : Z) :
    letI := periodAddAction (P ∘ f)
    AddAction.orbitRel.Quotient Λ (Z × E) :=
  (torusFamilyBaseChangeEquiv P f).symm
    ⟨(g • z, b (σ g) (f z)), (hb (σ g) (f z)).trans (hf g z).symm⟩

/-- The pulled-back translation section at `(g, z)` lies in the fibre over `g • z`. -/
@[simp] theorem torusFamilyProjection_baseChangeTranslation (f : Z → Y) (σ : Γ' → Γ)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (g : Γ') (z : Z) :
    torusFamilyProjection (P ∘ f) (torusFamilyBaseChangeTranslation P f σ hf b hb g z) = g • z :=
  torusFamilyProjection_baseChangeEquiv_symm P f _

/-- Applying `torusFamilyBaseChangeMap P f` to the pulled-back translation section at `(g, z)`
recovers `b (σ g) (f z)`. -/
@[simp] theorem torusFamilyBaseChangeMap_baseChangeTranslation (f : Z → Y) (σ : Γ' → Γ)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (g : Γ') (z : Z) :
    torusFamilyBaseChangeMap P f (torusFamilyBaseChangeTranslation P f σ hf b hb g z) =
      b (σ g) (f z) :=
  torusFamilyBaseChangeMap_baseChangeEquiv_symm P f _

/-- A point of `(Z × E)/Λ` equals `torusFamilyBaseChangeTranslation P f σ hf b hb g z` if and only
if it lies over `g • z` and maps to `b (σ g) (f z)` in `(Y × E)/Λ`. -/
theorem eq_torusFamilyBaseChangeTranslation_iff (f : Z → Y) (σ : Γ' → Γ)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (g : Γ') (z : Z)
    {x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)} :
    x = torusFamilyBaseChangeTranslation P f σ hf b hb g z ↔
      torusFamilyProjection (P ∘ f) x = g • z ∧
        torusFamilyBaseChangeMap P f x = b (σ g) (f z) :=
  eq_torusFamilyBaseChangeEquiv_symm_iff P f _

/-- If `β` represents `b (σ g) (f z)` over `σ g • f z`, then `β` also represents the pulled-back
translation section at `(g, z)` over `g • z`. -/
theorem torusFamilyBaseChangeTranslation_eq_mk_of_eq (f : Z → Y) (σ : Γ' → Γ)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    {g : Γ'} {z : Z} {β : E}
    (hβ : b (σ g) (f z) = Quotient.mk _ (σ g • f z, β)) :
    letI := periodAddAction (P ∘ f)
    torusFamilyBaseChangeTranslation P f σ hf b hb g z = Quotient.mk _ (g • z, β) :=
  ((eq_torusFamilyBaseChangeTranslation_iff P f σ hf b hb g z).2
    ⟨torusFamilyProjection_mk (P ∘ f) (g • z, β), by
      rw [torusFamilyBaseChangeMap_mk, hf, hβ]⟩).symm

/-- Pulling back the zero translation section gives the zero translation section. -/
@[simp] theorem torusFamilyBaseChangeTranslation_zero (f : Z → Y) (σ : Γ' → Γ)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) (g : Γ') (z : Z) :
    letI := periodAddAction (P ∘ f)
    torusFamilyBaseChangeTranslation P f σ hf
      (fun g y ↦ Quotient.mk _ (g • y, 0))
      (fun g y ↦ torusFamilyProjection_mk P (g • y, 0)) g z =
      Quotient.mk _ (g • z, 0) :=
  torusFamilyBaseChangeTranslation_eq_mk_of_eq P f σ hf _ _ rfl

/-- Pulling back a translation section along the identity maps recovers the section. -/
@[simp] theorem torusFamilyBaseChangeTranslation_id
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (g : Γ) (y : Y) :
    torusFamilyBaseChangeTranslation P id id (fun _ _ ↦ rfl) b hb g y = b g y :=
  ((eq_torusFamilyBaseChangeTranslation_iff P id id (fun _ _ ↦ rfl) b hb g y).2
    ⟨hb g y, torusFamilyBaseChangeMap_id P (b g y)⟩).symm

/-- Pulling a translation section back twice agrees with pulling it back along the composite maps.
-/
theorem torusFamilyBaseChangeTranslation_comp {Γ'' : Type*} [SMul Γ'' W]
    (f : Z → Y) (σ : Γ' → Γ) (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (f' : W → Z) (τ : Γ'' → Γ') (hf' : ∀ (g : Γ'') (w : W), f' (g • w) = τ g • f' w)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (g : Γ'') (w : W) :
    torusFamilyBaseChangeTranslation (P ∘ f) f' τ hf'
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb) g w =
      torusFamilyBaseChangeTranslation P (f ∘ f') (σ ∘ τ)
        (fun g w ↦ by simp only [comp_apply, hf', hf]) b hb g w :=
  (eq_torusFamilyBaseChangeTranslation_iff P (f ∘ f') (σ ∘ τ)
    (fun g w ↦ by simp only [comp_apply, hf', hf]) b hb g w).2
    ⟨torusFamilyProjection_baseChangeTranslation (P ∘ f) f' τ hf' _ _ g w, by
      rw [← torusFamilyBaseChangeMap_comp P f f',
        torusFamilyBaseChangeMap_baseChangeTranslation,
        torusFamilyBaseChangeMap_baseChangeTranslation]
      rfl⟩

end Translation

/-! ### Affine maps and cocycle laws under equivariant base change -/

section Monoid

variable {Γ Γ' : Type*} [Monoid Γ] [Monoid Γ'] [MulAction Γ Y] [MulAction Γ' Z]
  (P : Y → Λ →ₗ[ℤ] E)
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)

/-- If `b 1 y` is the zero `[y, 0]` of the fibre over `y`, then the pulled-back translation section
at `1` is the zero `[z, 0]` of the fibre over `z`. -/
theorem torusFamilyBaseChangeTranslation_one (σ : Γ' →* Γ) {f : Z → Y}
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0)) (z : Z) :
    letI := periodAddAction (P ∘ f)
    torusFamilyBaseChangeTranslation P f σ hf b hb 1 z = Quotient.mk _ (z, 0) := by
  have h1 := torusFamilyBaseChangeTranslation_eq_mk_of_eq P f σ hf b hb (g := 1) (z := z)
    (β := 0) (by rw [map_one, one_smul, hbone])
  rwa [one_smul] at h1

variable (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))

/-- **Equivariance of base change for affine maps.** For a `σ`-equivariant base map `f : Z → Y`,
`torusFamilyBaseChangeMap P f` intertwines the pulled-back affine map of `g` on `(Z × E)/Λ` with
the affine map of `σ g` on `(Y × E)/Λ`. -/
@[simp] theorem torusFamilyBaseChangeMap_affineMap (σ : Γ' →* Γ) {f : Z → Y}
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) (g : Γ')
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    torusFamilyBaseChangeMap P f
      (torusFamilyAffineMap (fun g z ↦ R (σ g) (f z)) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hP σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb) g x) =
      torusFamilyAffineMap R P ρ hP b hb (σ g) (torusFamilyBaseChangeMap P f x) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyTranslationAddAction P
  let _ := torusFamilyTranslationAddAction (P ∘ f)
  induction x using Quotient.ind with | _ p =>
    rcases p with ⟨z, v⟩
    rw [torusFamilyAffineMap_mk, torusFamilyBaseChangeMap_vadd,
      torusFamilyBaseChangeMap_baseChangeTranslation, torusFamilyBaseChangeMap_mk,
      torusFamilyAffineMap_mk]

omit [Monoid Γ'] [MulAction Γ' Z] in
/-- Pulling the affine maps back along `(MonoidHom.id Γ, id)` recovers the original affine maps. -/
theorem torusFamilyBaseChangeAffineMap_id (g : Γ)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    torusFamilyAffineMap (fun g y ↦ R (MonoidHom.id Γ g) (id y)) (P ∘ id) (ρ.comp (MonoidHom.id Γ))
      (period_baseChange_equivariant R P ρ hP (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (torusFamilyBaseChangeTranslation P id (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      (torusFamilyProjection_baseChangeTranslation P id (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      g x = torusFamilyAffineMap R P ρ hP b hb g x := by
  let _ := periodAddAction P
  let _ := torusFamilyTranslationAddAction P
  induction x using Quotient.ind with | _ p =>
    rcases p with ⟨y, v⟩
    rw [torusFamilyAffineMap_mk, torusFamilyAffineMap_mk]
    exact congrArg (R g y v +ᵥ ·) (torusFamilyBaseChangeTranslation_id P b hb g y)

/-- Pulling the affine maps back along `f'` after `f` agrees with pulling them back along `f ∘ f'`.
-/
theorem torusFamilyBaseChangeAffineMap_comp {Γ'' : Type*} [Monoid Γ''] [MulAction Γ'' W]
    (σ : Γ' →* Γ) {f : Z → Y} (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (τ : Γ'' →* Γ') {f' : W → Z} (hf' : ∀ (g : Γ'') (w : W), f' (g • w) = τ g • f' w)
    (g : Γ'')
    (x : letI := periodAddAction (P ∘ (f ∘ f')); AddAction.orbitRel.Quotient Λ (W × E)) :
    torusFamilyAffineMap (fun g w ↦ R (σ (τ g)) (f (f' w))) ((P ∘ f) ∘ f') ((ρ.comp σ).comp τ)
      (period_baseChange_equivariant (fun g z ↦ R (σ g) (f z)) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hP σ hf) τ hf')
      (torusFamilyBaseChangeTranslation (P ∘ f) f' τ hf'
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb))
      (torusFamilyProjection_baseChangeTranslation (P ∘ f) f' τ hf' _ _) g x =
      torusFamilyAffineMap (fun g w ↦ R ((σ.comp τ) g) ((f ∘ f') w)) (P ∘ (f ∘ f'))
        (ρ.comp (σ.comp τ))
        (period_baseChange_equivariant R P ρ hP (σ.comp τ)
          fun g w ↦ by simp only [comp_apply, MonoidHom.comp_apply, hf', hf])
        (torusFamilyBaseChangeTranslation P (f ∘ f') (σ.comp τ)
          (fun g w ↦ by simp only [comp_apply, MonoidHom.comp_apply, hf', hf]) b hb)
        (torusFamilyProjection_baseChangeTranslation P (f ∘ f') (σ.comp τ) _ b hb) g x := by
  let _ := periodAddAction (P ∘ (f ∘ f'))
  let _ := torusFamilyTranslationAddAction (P ∘ (f ∘ f'))
  induction x using Quotient.ind with | _ p =>
    rcases p with ⟨w, v⟩
    rw [torusFamilyAffineMap_mk, torusFamilyAffineMap_mk]
    exact congrArg (R (σ (τ g)) (f (f' w)) v +ᵥ ·)
      (torusFamilyBaseChangeTranslation_comp P f σ hf f' τ hf' b hb g w)

/-- Pulling an affine translation cocycle `b` back along `σ : Γ' →* Γ` and a `σ`-equivariant map
`f : Z → Y` preserves the multiplication cocycle law `b' (g * h) z = g · b' h z`. -/
theorem torusFamilyBaseChangeTranslation_mul (σ : Γ' →* Γ) {f : Z → Y}
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hP b hb g (b h y))
    (g h : Γ') (z : Z) :
    torusFamilyBaseChangeTranslation P f σ hf b hb (g * h) z =
      torusFamilyAffineMap (fun g z ↦ R (σ g) (f z)) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hP σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb) g
        (torusFamilyBaseChangeTranslation P f σ hf b hb h z) :=
  ((eq_torusFamilyBaseChangeTranslation_iff P f σ hf b hb (g * h) z).2
    ⟨by rw [torusFamilyProjection_affineMap, torusFamilyProjection_baseChangeTranslation,
          mul_smul],
     by rw [torusFamilyBaseChangeMap_affineMap,
          torusFamilyBaseChangeMap_baseChangeTranslation, map_mul, hbmul]⟩).symm

variable (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hP b hb g (b h y))

/-- **Equivariance of base change for affine actions.** For a `σ`-equivariant map `f : Z → Y`,
`torusFamilyBaseChangeMap P f` intertwines the pulled-back affine action of `Γ'` on `(Z × E)/Λ`
with the affine action of `Γ` on `(Y × E)/Λ`. -/
theorem torusFamilyBaseChangeMap_affineSMul (σ : Γ' →* Γ) {f : Z → Y}
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) (g : Γ')
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    torusFamilyBaseChangeMap P f (g • x) = σ g • torusFamilyBaseChangeMap P f x := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
  rw [torusFamilyAffineMulAction_smul, torusFamilyAffineMulAction_smul,
    torusFamilyBaseChangeMap_affineMap]

/-- The `σ`-equivariant base-change map `(Z × E)/Λ →ₑ[σ] (Y × E)/Λ` between families of tori
carrying affine actions. -/
def torusFamilyAffineBaseChangeHom (σ : Γ' →* Γ) (f : Z → Y)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    AddAction.orbitRel.Quotient Λ (Z × E) →ₑ[σ] AddAction.orbitRel.Quotient Λ (Y × E) :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
  { toFun := torusFamilyBaseChangeMap P f
    map_smul' := torusFamilyBaseChangeMap_affineSMul P b hb R ρ hP hone hmul hbone hbmul σ hf }

/-- The underlying function of `torusFamilyAffineBaseChangeHom` is `torusFamilyBaseChangeMap`. -/
@[simp] theorem coe_torusFamilyAffineBaseChangeHom (σ : Γ' →* Γ) (f : Z → Y)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    ⇑(torusFamilyAffineBaseChangeHom P b hb R ρ hP hone hmul hbone hbmul σ f hf) =
      torusFamilyBaseChangeMap P f := (rfl)

/-- Applying `torusFamilyAffineBaseChangeHom` applies `torusFamilyBaseChangeMap`. -/
@[simp] theorem torusFamilyAffineBaseChangeHom_apply (σ : Γ' →* Γ) (f : Z → Y)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (x : letI := periodAddAction (P ∘ f); AddAction.orbitRel.Quotient Λ (Z × E)) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    torusFamilyAffineBaseChangeHom P b hb R ρ hP hone hmul hbone hbmul σ f hf x =
      torusFamilyBaseChangeMap P f x := (rfl)

end Monoid

/-! ### Topology of the pulled-back affine action -/

section Topology

variable [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace E] [ContinuousAdd E]

/-- **Continuity of the pulled-back translation section.** When the period family `P`, the base map
`f`, the action of `g` on `Z`, and the translation section `b (σ g)` are continuous, the
pulled-back translation section `torusFamilyBaseChangeTranslation P f σ hf b hb g` is continuous.
No vector lift of `b` is needed. -/
theorem continuous_torusFamilyBaseChangeTranslation {Γ Γ' : Type*} [SMul Γ Y] [SMul Γ' Z]
    (P : Y → Λ →ₗ[ℤ] E) (hcont : ∀ l, Continuous fun y ↦ P y l) {f : Z → Y}
    (hf_cont : Continuous f) (σ : Γ' → Γ)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    {g : Γ'} (hg : Continuous (g • · : Z → Z)) (hbc : Continuous (b (σ g))) :
    Continuous (torusFamilyBaseChangeTranslation P f σ hf b hb g) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  have hsub : Continuous fun z : Z ↦
      (⟨(g • z, b (σ g) (f z)), (hb (σ g) (f z)).trans (hf g z).symm⟩ :
        {r : Z × AddAction.orbitRel.Quotient Λ (Y × E) |
          torusFamilyProjection P r.2 = f r.1}) :=
    (hg.prodMk (hbc.comp hf_cont)).subtype_mk _
  exact ((torusFamilyBaseChangeHomeomorph P f hcont hf_cont).symm.continuous.comp hsub).congr
    fun z ↦ by
      simp [torusFamilyBaseChangeTranslation,
        coe_torusFamilyBaseChangeHomeomorph_symm P f hcont hf_cont]

/-- **Continuity of the pulled-back affine action.** If `Γ'` acts continuously on `Z`, `f : Z → Y`
is continuous and `σ`-equivariant, and the period family `P`, linear evaluations `R`, and
translation sections `b` on `Y` are continuous, then the pulled-back affine action of `Γ'` on
`(Z × E)/Λ` is continuous in the family point. -/
theorem continuousConstSMul_torusFamilyBaseChangeAffineMulAction
    {Γ Γ' : Type*} [Monoid Γ] [Monoid Γ'] [MulAction Γ Y] [MulAction Γ' Z]
    [ContinuousConstSMul Γ' Z]
    (R : Γ → Y → E →+ E) (hone : ∀ (y : Y) (v : E), R 1 y v = v)
    (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
    (P : Y → Λ →ₗ[ℤ] E) (hcont : ∀ l, Continuous fun y ↦ P y l)
    (ρ : Representation ℤ Γ Λ)
    (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
    (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hP b hb g (b h y))
    (σ : Γ' →* Γ) {f : Z → Y} (hf_cont : Continuous f)
    (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hR : ∀ g : Γ, Continuous fun p : Y × E ↦ R g p.1 p.2)
    (hbc : ∀ g : Γ, Continuous (b g)) :
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    ContinuousConstSMul Γ' (AddAction.orbitRel.Quotient Λ (Z × E)) :=
  continuousConstSMul_torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    (fun l ↦ (hcont l).comp hf_cont)
    (fun g ↦ (hR (σ g)).comp (hf_cont.prodMap continuous_id))
    (fun g ↦ continuous_torusFamilyBaseChangeTranslation P hcont hf_cont σ hf b hb
      (continuous_const_smul g) (hbc (σ g)))

end Topology

/-! ### Base stabilizers, total-space freeness, and second quotients -/

section Group

variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] [MulAction Γ Y] [MulAction Γ' Z]

/-- Over a fixed point `g • z = z`, the fibrewise translation part of the pulled-back section at
`z` equals the fibrewise translation part of `b` for `σ g` at `f z`. -/
@[simp] theorem torusFamilyFiberTranslationPart_baseChange (P : Y → Λ →ₗ[ℤ] E)
    (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
    (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
    (σ : Γ' → Γ) {f : Z → Y} (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    {g : Γ'} {z : Z} (hz : g • z = z) :
    torusFamilyFiberTranslationPart (P ∘ f)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb) hz =
      torusFamilyFiberTranslationPart P b hb ((hf g z).symm.trans (congrArg f hz)) := by
  apply torusFamilyFiberMap_injective P (f z)
  rw [← torusFamilyBaseChangeMap_fiberMap P f z,
    torusFamilyFiberMap_fiberTranslationPart,
    torusFamilyBaseChangeMap_baseChangeTranslation,
    torusFamilyFiberMap_fiberTranslationPart]

variable (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))

/-- Over a fixed point `g • z = z`, the fibrewise linear part of the pulled-back cocycle on the
fibre over `z` equals the fibrewise linear part of `R` for `σ g` on the fibre over `f z`. -/
@[simp] theorem torusFamilyFiberLinearPart_baseChange
    (σ : Γ' →* Γ) {f : Z → Y} (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    {g : Γ'} {z : Z} (hz : g • z = z) :
    torusFamilyFiberLinearPart (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf) hz =
      torusFamilyFiberLinearPart R hone hmul P ρ hP ((hf g z).symm.trans (congrArg f hz)) := by
  ext x
  induction x using Quotient.ind with | _ v =>
    rw [torusFamilyFiberLinearPart_mk]
    exact (torusFamilyFiberLinearPart_mk R hone hmul P ρ hP
      ((hf g z).symm.trans (congrArg f hz)) v).symm

variable (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hP b hb g (b h y))

/-- **Transfer of total-space freeness under equivariant base change.** If the affine action of
`Γ` on `(Y × E)/Λ` is free (`IsCancelSMul`) and `σ : Γ' →* Γ` has trivial kernel on every base
stabilizer in `Z` (for instance when `σ` is injective, or when `Γ'` acts freely on `Z`), then the
pulled-back affine action of `Γ'` on `(Z × E)/Λ` is also free, even when the base actions have
fixed points. -/
theorem isCancelSMul_torusFamilyBaseChangeAffineMulAction
    (σ : Γ' →* Γ) {f : Z → Y} (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hfree : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
    (hker : ∀ (z : Z) (g : Γ'), g • z = z → σ g = 1 → g = 1) :
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    IsCancelSMul Γ' (AddAction.orbitRel.Quotient Λ (Z × E)) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun g x hx ↦ ?_
  have hz : g • torusFamilyProjection (P ∘ f) x = torusFamilyProjection (P ∘ f) x :=
    torusFamilyAffineMulAction_stabilizer_le _ _ _ (P ∘ f) _ _ _ _ _ _ x hx
  have hmap : σ g • torusFamilyBaseChangeMap P f x = torusFamilyBaseChangeMap P f x := by
    rw [← torusFamilyBaseChangeMap_affineSMul P b hb R ρ hP hone hmul hbone hbmul σ hf, hx]
  exact hker _ g hz (isCancelSMul_iff_eq_one_of_smul_eq.1 hfree (σ g) _ hmap)

/-- **Naturality of the descended projection for affine actions.** For group actions and a
`σ`-equivariant base map `f : Z → Y`, the map of second quotients
`((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` induced by `torusFamilyAffineBaseChangeHom` forms a commutative
square with the descended family projections to `Z/Γ'` and `Y/Γ`. -/
theorem orbitRelQuotientMap_torusFamilyAffineProjection_comp_baseChange
    (σ : Γ' →* Γ) (f : Z → Y) (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    MulActionHom.orbitRelQuotientMap
        (⟨torusFamilyProjection P, fun g x ↦ by
          rw [torusFamilyAffineMulAction_smul, torusFamilyProjection_affineMap]; rfl⟩ :
          AddAction.orbitRel.Quotient Λ (Y × E) →[Γ] Y) ∘
      MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineBaseChangeHom P b hb R ρ hP hone hmul hbone hbmul σ f hf) =
      MulActionHom.orbitRelQuotientMap (σ := σ) ⟨f, hf⟩ ∘
        MulActionHom.orbitRelQuotientMap
          (⟨torusFamilyProjection (P ∘ f), fun g x ↦ by
            rw [torusFamilyAffineMulAction_smul, torusFamilyProjection_affineMap]; rfl⟩ :
            AddAction.orbitRel.Quotient Λ (Z × E) →[Γ'] Z) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
  funext q
  induction q using Quotient.ind with | _ x =>
    simp only [comp_apply, MulActionHom.orbitRelQuotientMap_mk,
      torusFamilyAffineBaseChangeHom_apply]
    exact congrArg (Quotient.mk _) (torusFamilyProjection_baseChangeMap P f x)

/-- **Injectivity on second quotients for equivariant slices.** If `f : Z → Y` is injective and
`σ`-equivariant, and every `g : Γ` relating two points in `f '' univ` lies in `range σ` (which
holds automatically when `σ` is surjective, e.g. for a `Γ`-invariant subset, or when `Z` is a
slice for a subgroup `Γ' ≤ Γ`), then the induced map of second quotients
`((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` is injective. -/
theorem orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_injective
    (σ : Γ' →* Γ) {f : Z → Y} (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hf_inj : Injective f)
    (hslice : ∀ (g : Γ) (z₁ z₂ : Z), g • f z₂ = f z₁ → ∃ g' : Γ', σ g' = g) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    Injective (MulActionHom.orbitRelQuotientMap
      (torusFamilyAffineBaseChangeHom P b hb R ρ hP hone hmul hbone hbmul σ f hf)) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
  intro q₁ q₂ h
  induction q₁ using Quotient.ind with | _ x₁ =>
  induction q₂ using Quotient.ind with | _ x₂ =>
  rw [MulActionHom.orbitRelQuotientMap_mk, MulActionHom.orbitRelQuotientMap_mk] at h
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact h))
  -- Projecting `g • φ x₂ = φ x₁` to `Y` places `g` in `range σ` via the slice condition.
  have hbase : g • f (torusFamilyProjection (P ∘ f) x₂) = f (torusFamilyProjection (P ∘ f) x₁) := by
    have hp := congrArg (torusFamilyProjection P) hg
    simpa [torusFamilyProjection_baseChangeMap] using hp
  obtain ⟨g', rfl⟩ := hslice g _ _ hbase
  have hx : g' • x₂ = x₁ := torusFamilyBaseChangeMap_injective P f hf_inj <| by
    rw [torusFamilyBaseChangeMap_affineSMul P b hb R ρ hP hone hmul hbone hbmul σ hf]
    exact hg
  exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g', hx⟩))

/-- **Open embeddings on second quotients for equivariant open slices.** For a continuous period
family `P` whose affine `Γ`-action acts by continuous maps on `(Y × E)/Λ`, a `σ`-equivariant open
embedding `f : Z → Y` satisfying the orbit-slice condition induces an open embedding
`((Z × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` of the second quotients. -/
theorem isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace E] [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hsmul : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
      ContinuousConstSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))
    (σ : Γ' →* Γ) {f : Z → Y} (hf : ∀ (g : Γ') (z : Z), f (g • z) = σ g • f z)
    (hf_open : IsOpenEmbedding f)
    (hslice : ∀ (g : Γ) (z₁ z₂ : Z), g • f z₂ = f z₁ → ∃ g' : Γ', σ g' = g) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hP σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
    IsOpenEmbedding (MulActionHom.orbitRelQuotientMap
      (torusFamilyAffineBaseChangeHom P b hb R ρ hP hone hmul hbone hbmul σ f hf)) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyAffineMulAction (fun g z ↦ R (σ g) (f z))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hP σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_one P b hb σ hf hbone)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP σ hf hbmul)
  have := hsmul
  let φ := torusFamilyAffineBaseChangeHom P b hb R ρ hP hone hmul hbone hbmul σ f hf
  have hφ_cont : Continuous (MulActionHom.orbitRelQuotientMap φ) := by
    rw [isQuotientMap_quotient_mk'.continuous_iff]
    exact MulActionHom.orbitRelQuotientMap_comp_mk φ ▸
      continuous_quot_mk.comp (continuous_torusFamilyBaseChangeMap P f hf_open.continuous)
  refine .of_continuous_injective_isOpenMap hφ_cont
    (orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_injective R hone hmul P ρ hP b hb hbone
      hbmul σ hf hf_open.injective hslice) fun U hU ↦ ?_
  -- Push `U` up to `(Z × E)/Λ`, across the open base-change map, and down to `((Y × E)/Λ)/Γ`.
  rw [← Quotient.mk_surjective.image_preimage U, ← image_comp,
    MulActionHom.orbitRelQuotientMap_comp_mk, image_comp]
  exact isOpenMap_quotient_mk'_mul _
    (isOpenMap_torusFamilyBaseChangeMap P f hcont hf_open.isOpenMap _
      (hU.preimage continuous_quot_mk))

omit [Group Γ'] [MulAction Γ' Z] in
/-- **Open embedding of the unramified second quotient into the full second quotient.** For a
properly discontinuous continuous action of `Γ` on a locally compact Hausdorff space `Y` and a
continuous period family `P` whose affine `Γ`-action acts by continuous maps on `(Y × E)/Λ`, the
second quotient `((freeLocus Γ Y × E)/Λ)/Γ` over the free locus embeds as an open subset into
`((Y × E)/Λ)/Γ`. Neither manifold structure nor freeness on `Y` or `(Y × E)/Λ` is required. -/
theorem isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom_freeLocus
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y]
    [TopologicalSpace E] [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hsmul : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
      ContinuousConstSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E))) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ (Subtype.val : freeLocus Γ Y → Y))
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyAffineMulAction
      (fun g (z : freeLocus Γ Y) ↦ R (MonoidHom.id Γ g) (z : Y))
      (linearCocycle_baseChange_one R hone (MonoidHom.id Γ) Subtype.val)
      (linearCocycle_baseChange_mul R hmul (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (P ∘ (Subtype.val : freeLocus Γ Y → Y)) (ρ.comp (MonoidHom.id Γ))
      (period_baseChange_equivariant R P ρ hP (MonoidHom.id Γ) fun _ _ ↦ rfl)
      (torusFamilyBaseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y) (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) b hb)
      (torusFamilyProjection_baseChangeTranslation P (Subtype.val : freeLocus Γ Y → Y)
        (MonoidHom.id Γ) (fun _ _ ↦ rfl) b hb)
      (torusFamilyBaseChangeTranslation_one P b hb (MonoidHom.id Γ) (fun _ _ ↦ rfl) hbone)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hP (MonoidHom.id Γ)
        (fun _ _ ↦ rfl) hbmul)
    IsOpenEmbedding (MulActionHom.orbitRelQuotientMap
      (torusFamilyAffineBaseChangeHom P b hb R ρ hP hone hmul hbone hbmul
        (MonoidHom.id Γ) (Subtype.val : freeLocus Γ Y → Y) fun _ _ ↦ rfl)) :=
  isOpenEmbedding_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom R hone hmul P ρ hP b hb
    hbone hbmul hcont hsmul (MonoidHom.id Γ) (fun _ _ ↦ rfl)
    (isOpen_freeLocus Γ Y).isOpenEmbedding_subtypeVal fun g _ _ _ ↦ ⟨g, rfl⟩

end Group

end TauCeti
