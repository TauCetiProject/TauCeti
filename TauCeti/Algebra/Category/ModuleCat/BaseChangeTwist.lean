/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Pseudofunctor
public import TauCeti.Algebra.Category.ModuleCat.Twist
public import TauCeti.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
# Equivariance of coefficient base change for twisting actions

Fix a commutative ring `k`, a `k`-algebra `Λ` and a morphism `f : R ⟶ S` of commutative
`k`-algebras, and let a monoid `H` act by ring automorphisms on `R ⊗[k] Λ` and on `S ⊗[k] Λ`,
through `aR` and `aS`. Twisting a module by `h : H` restricts its scalars along the inverse
automorphism (`MonoidHom.restrictScalarsMonoidalLeftAction`). Assume that

* `aR h` fixes the coefficients `R` and `aS h` fixes the coefficients `S`, and
* `f ⊗ id : R ⊗[k] Λ → S ⊗[k] Λ` intertwines the actions:
  `(f ⊗ id) (aR h x) = aS h ((f ⊗ id) x)`.

Then base change `CommAlgCat.moduleCatBaseChange Λ f`, `M ↦ S ⊗[R] M`, commutes with twisting.
The first assumption makes the twist `T_h M` the same `R`-module as `M`, so that `S ⊗[R] T_h M`
and `T_h (S ⊗[R] M)` have the same underlying group `S ⊗[R] M`; the second makes the identity of
`S ⊗[R] M` linear over `S ⊗[k] Λ` between them.

* `CommAlgCat.moduleCatBaseChangeLeftLinear`: base change along `f` is left-linear (equivariant)
  for the twisting actions of `H`, in the sense of Mathlib's `Functor.LeftLinear`. Its lineators
  are the identity on tensors (`CommAlgCat.moduleCatBaseChangeLeftLinear_μₗ_hom_tmul` and
  `CommAlgCat.moduleCatBaseChangeLeftLinear_δₗ_hom_tmul`), and the axioms of a left-linear
  functor are the unit and product diagrams of the commuting isomorphisms
  `T_h ⋙ B_f ≅ B_f ⋙ T_h`, packaged by `Functor.commActionLeftIso` in
  `TauCeti.CategoryTheory.Monoidal.Action.StrongTrans`.
* `CommAlgCat.isLeftLinear_moduleCatBaseChangeId_hom` and
  `CommAlgCat.isLeftLinear_moduleCatBaseChangeComp_hom`: the unit comparison `R ⊗[R] M ≅ M` and
  the composition comparison `T ⊗[R] M ≅ T ⊗[S] (S ⊗[R] M)` of the base-change pseudofunctor
  `CommAlgCat.moduleCatBaseChangePseudofunctor` are equivariant. So the commuting isomorphisms
  are compatible with the coherence of base change, not only with each base change separately.

The symmetry group may itself depend on the coefficients, as for the loop groups `G(R((t)))`,
which map to `G(S((t)))` along `f`. One then applies these results with `aS` precomposed with
that monoid homomorphism, so that `h` acts on base changes through its image.

## Implementation notes

A twisted module has the same underlying abelian group as the module. The private helper
`twistElem` views an element in a twist with the twisted type, so that the elementwise proofs of
the coherence diagrams rewrite type-correct terms. The lineators follow
`RingHom.leftLinearRestrictScalars`, whose lineators are identities as well.

## References

* Edward Frenkel and Dennis Gaitsgory, *Local geometric Langlands correspondence and affine
  Kac–Moody algebras*, in *Algebraic Geometry and Number Theory*, Progress in Mathematics 253,
  Birkhäuser, 2006: categories of modules over a varying commutative base, their base change and
  the loop group actions on them.
* Edward Frenkel, [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  §1.3: twisting categories of modules by automorphisms.
-/

public section

open CategoryTheory MonoidalCategory MonoidalLeftAction
open scoped TensorProduct ModuleCat.Algebra

universe w v u

namespace CommAlgCat

variable {k : Type w} [CommRing k] {Λ : Type v} [Ring Λ] [Algebra k Λ]

variable {R S : CommAlgCat.{u} k} {H : Type*} [Monoid H]

section TwistElem

variable {A : Type*} [Ring A] (a : H →* RingAut A)

/-- An element of an `A`-module, viewed in its twist by `c`. The twist has the same underlying
abelian group, so this is the identity; it records the type, so that the rewriting lemmas below
stay type-correct. -/
private def twistElem (c : Discrete H) {X : ModuleCat.{u} A} (x : X) :
    letI := a.restrictScalarsMonoidalLeftAction.{u}
    ↑(c ⊙ₗ X : ModuleCat.{u} A) :=
  x

private lemma twistElem_add (c : Discrete H) {X : ModuleCat.{u} A} (x y : X) :
    twistElem a c (x + y) = twistElem a c x + twistElem a c y :=
  rfl

private lemma exists_twistElem_eq (c : Discrete H) {X : ModuleCat.{u} A}
    (x : letI := a.restrictScalarsMonoidalLeftAction.{u}; ↑(c ⊙ₗ X : ModuleCat.{u} A)) :
    ∃ y : X, twistElem a c y = x :=
  ⟨x, rfl⟩

private lemma actionHomRight_hom_twistElem (c : Discrete H) {X Y : ModuleCat.{u} A} (g : X ⟶ Y)
    (x : X) :
    letI := a.restrictScalarsMonoidalLeftAction.{u}
    (c ⊴ₗ g).hom (twistElem a c x) = twistElem a c (g.hom x) :=
  rfl

private lemma actionAssocIso_hom_twistElem (c c' : Discrete H) {X : ModuleCat.{u} A} (x : X) :
    letI := a.restrictScalarsMonoidalLeftAction.{u}
    (αₗ c c' X).hom.hom (twistElem a (c ⊗ c') x) = twistElem a c (twistElem a c' x) :=
  rfl

private lemma actionAssocIso_inv_twistElem (c c' : Discrete H) {X : ModuleCat.{u} A} (x : X) :
    letI := a.restrictScalarsMonoidalLeftAction.{u}
    (αₗ c c' X).inv.hom (twistElem a c (twistElem a c' x)) = twistElem a (c ⊗ c') x :=
  rfl

private lemma actionUnitIso_hom_twistElem {X : ModuleCat.{u} A} (x : X) :
    letI := a.restrictScalarsMonoidalLeftAction.{u}
    (λₗ[Discrete H] X).hom.hom (twistElem a (𝟙_ (Discrete H)) x) = x :=
  rfl

private lemma actionUnitIso_inv_twistElem {X : ModuleCat.{u} A} (x : X) :
    letI := a.restrictScalarsMonoidalLeftAction.{u}
    (λₗ[Discrete H] X).inv.hom x = twistElem a (𝟙_ (Discrete H)) x :=
  rfl

end TwistElem

section Twist

variable {aR : H →* RingAut (R ⊗[k] Λ)} {aS : H →* RingAut (S ⊗[k] Λ)} {f : R ⟶ S}
  (hR : ∀ h r, aR h (algebraMap R (R ⊗[k] Λ) r) = algebraMap R (R ⊗[k] Λ) r)
  (hS : ∀ h s, aS h (algebraMap S (S ⊗[k] Λ) s) = algebraMap S (S ⊗[k] Λ) s)
  (hf : ∀ h x, Algebra.TensorProduct.map f.hom (AlgHom.id k Λ) (aR h x) =
    aS h (Algebra.TensorProduct.map f.hom (AlgHom.id k Λ) x))

include hR in
/-- Twisting by an automorphism fixing `R` does not change the `R`-module structure. -/
private def twistLinearEquiv (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ)) :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    M ≃ₗ[R] ↑(c ⊙ₗ M : ModuleCat.{u} (R ⊗[k] Λ)) where
  toFun := twistElem aR c
  invFun x := x
  map_add' := twistElem_add aR c
  map_smul' r x := by
    -- `r` acts on the twist as `(aR c)⁻¹ (algebraMap R _ r) = algebraMap R _ r` acts on `M`.
    change algebraMap R (R ⊗[k] Λ) r • x = (aR c.as).symm (algebraMap R (R ⊗[k] Λ) r) • x
    rw [(RingEquiv.symm_apply_eq _).2 (hR c.as r).symm]
  left_inv _ := rfl
  right_inv _ := rfl

include hS hf in
private lemma symm_tmul (h : H) (s : S) (l : Λ) :
    (aS h).symm (s ⊗ₜ[k] l) = algebraMap S (S ⊗[k] Λ) s *
      Algebra.TensorProduct.map f.hom (AlgHom.id k Λ) ((aR h).symm (1 ⊗ₜ[k] l)) := by
  have hs : (aS h).symm (algebraMap S (S ⊗[k] Λ) s) = algebraMap S (S ⊗[k] Λ) s :=
    (RingEquiv.symm_apply_eq _).2 (hS h s).symm
  have hl : (aS h).symm (Algebra.TensorProduct.map f.hom (AlgHom.id k Λ) (1 ⊗ₜ[k] l)) =
      Algebra.TensorProduct.map f.hom (AlgHom.id k Λ) ((aR h).symm (1 ⊗ₜ[k] l)) := by
    rw [RingEquiv.symm_apply_eq, ← hf, RingEquiv.apply_symm_apply]
  rw [← hs, ← hl, ← map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The identity of `S ⊗[R] M`, from the base change of `M` to the base change of its twist. -/
private noncomputable def twistAddEquiv (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ)) :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    (moduleCatBaseChange Λ f).obj M ≃+ (moduleCatBaseChange Λ f).obj (c ⊙ₗ M) :=
  letI := f.hom.toRingHom.toAlgebra
  ((twistLinearEquiv hR c M).lTensor S).toAddEquiv

private lemma twistAddEquiv_tmul (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ)) (s : S) (m : M) :
    twistAddEquiv (f := f) hR c M (moduleCatBaseChangeTmul Λ f s m) =
      moduleCatBaseChangeTmul Λ f s (twistElem aR c m) :=
  -- Both sides are the raw tensor `s ⊗ m`, since `twistLinearEquiv` is the identity.
  (congrArg _ (moduleCatBaseChangeTmul_def Λ f s m)).trans
    (moduleCatBaseChangeTmul_def Λ f s (twistElem aR c m)).symm

include hS hf in
private lemma twistAddEquiv_smul (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ)) (t : S ⊗[k] Λ)
    (x : (moduleCatBaseChange Λ f).obj M) :
    twistAddEquiv hR c M ((aS c.as).symm t • x) = t • twistAddEquiv hR c M x := by
  induction t using TensorProduct.inductionOn with
  | tmul s l =>
    induction x using moduleCatBaseChange_obj_inductionOn with
    | tmul s' m =>
      rw [symm_tmul hS hf, mul_smul, tensorProductMap_smul_moduleCatBaseChangeTmul,
        algebraMap_smul_moduleCatBaseChangeTmul, twistAddEquiv_tmul, twistAddEquiv_tmul,
        tmul_smul_moduleCatBaseChangeTmul]
      -- `1 ⊗ l` acts on the twist of `M` as `(aR c)⁻¹ (1 ⊗ l)` acts on `M`.
      rfl
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  | add t t' ht ht' => rw [map_add, add_smul, map_add, ht, ht', add_smul]

include hS hf in
/-- The identity of `S ⊗[R] M` intertwines the twist of the base change by `c` with the base
change of the twist by `c`. -/
private noncomputable def baseChangeTwistEquiv (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ)) :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    letI := aS.restrictScalarsMonoidalLeftAction.{u}
    ↑(c ⊙ₗ (moduleCatBaseChange Λ f).obj M : ModuleCat.{u} (S ⊗[k] Λ)) ≃ₗ[S ⊗[k] Λ]
      (moduleCatBaseChange Λ f).obj (c ⊙ₗ M) :=
  { twistAddEquiv hR c M with
    -- `t` acts on the twist of the base change as `(aS c)⁻¹ t` acts on the base change.
    map_smul' t x := twistAddEquiv_smul hR hS hf c M t x }

private lemma baseChangeTwistEquiv_twistElem (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ))
    (s : S) (m : M) :
    baseChangeTwistEquiv hR hS hf c M (twistElem aS c (moduleCatBaseChangeTmul Λ f s m)) =
      moduleCatBaseChangeTmul Λ f s (twistElem aR c m) :=
  twistAddEquiv_tmul hR c M s m

private lemma baseChangeTwistEquiv_symm_tmul (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ))
    (s : S) (m : M) :
    (baseChangeTwistEquiv hR hS hf c M).symm (moduleCatBaseChangeTmul Λ f s (twistElem aR c m)) =
      twistElem aS c (moduleCatBaseChangeTmul Λ f s m) :=
  (LinearEquiv.symm_apply_eq _).2 (baseChangeTwistEquiv_twistElem hR hS hf c M s m).symm

/-- A morphism out of the twist of a base change is determined by its values on the twisted
tensors `s ⊗ m`. -/
private lemma twist_moduleCatBaseChange_hom_ext (c : Discrete H) {M : ModuleCat.{u} (R ⊗[k] Λ)}
    {P : ModuleCat.{u} (S ⊗[k] Λ)}
    {g₁ g₂ : letI := aS.restrictScalarsMonoidalLeftAction.{u}
      c ⊙ₗ (moduleCatBaseChange Λ f).obj M ⟶ P}
    (h : ∀ (s : S) (m : M), g₁.hom (twistElem aS c (moduleCatBaseChangeTmul Λ f s m)) =
      g₂.hom (twistElem aS c (moduleCatBaseChangeTmul Λ f s m))) :
    g₁ = g₂ := by
  ext x
  obtain ⟨x, rfl⟩ := exists_twistElem_eq aS c x
  induction x using moduleCatBaseChange_obj_inductionOn with
  | tmul s m => exact h s m
  | add x y hx hy => rw [twistElem_add, map_add, map_add, hx, hy]

include hS hf in
/-- The comparison `c ⊙ₗ B M ≅ B (c ⊙ₗ M)` of `baseChangeTwistEquiv` in `ModuleCat`. -/
private noncomputable def baseChangeTwistIso (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ)) :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    letI := aS.restrictScalarsMonoidalLeftAction.{u}
    c ⊙ₗ (moduleCatBaseChange Λ f).obj M ≅ (moduleCatBaseChange Λ f).obj (c ⊙ₗ M) :=
  (baseChangeTwistEquiv hR hS hf c M).toModuleIso

private lemma baseChangeTwistIso_hom_twistElem (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ))
    (s : S) (m : M) :
    (baseChangeTwistIso hR hS hf c M).hom.hom
        (twistElem aS c (moduleCatBaseChangeTmul Λ f s m)) =
      moduleCatBaseChangeTmul Λ f s (twistElem aR c m) :=
  baseChangeTwistEquiv_twistElem hR hS hf c M s m

private lemma baseChangeTwistIso_inv_tmul (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ))
    (s : S) (m : M) :
    (baseChangeTwistIso hR hS hf c M).inv.hom
        (moduleCatBaseChangeTmul Λ f s (twistElem aR c m)) =
      twistElem aS c (moduleCatBaseChangeTmul Λ f s m) :=
  baseChangeTwistEquiv_symm_tmul hR hS hf c M s m

include hS hf in
/-- Base change along `f` is equivariant for the twisting actions. -/
@[instance_reducible]
noncomputable def moduleCatBaseChangeLeftLinear :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    letI := aS.restrictScalarsMonoidalLeftAction.{u}
    (moduleCatBaseChange Λ f).LeftLinear (Discrete H) :=
  letI := aR.restrictScalarsMonoidalLeftAction.{u}
  letI := aS.restrictScalarsMonoidalLeftAction.{u}
  { μₗ c M := (baseChangeTwistIso hR hS hf c M).hom
    δₗ c M := (baseChangeTwistIso hR hS hf c M).inv
    μₗ_naturality_left {c c'} g M := by
      obtain ⟨c⟩ := c
      obtain ⟨c'⟩ := c'
      obtain rfl : c = c' := Discrete.eq_of_hom g
      obtain rfl : g = 𝟙 _ := Subsingleton.elim _ _
      simp
    μₗ_naturality_right c M M' φ := twist_moduleCatBaseChange_hom_ext c fun s m ↦ by
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, actionHomRight_hom_twistElem,
        moduleCatBaseChange_map_hom_tmul, baseChangeTwistIso_hom_twistElem]
    μₗ_associativity c c' M := twist_moduleCatBaseChange_hom_ext (c ⊗ c') fun s m ↦ by
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, actionAssocIso_hom_twistElem,
        actionHomRight_hom_twistElem, moduleCatBaseChange_map_hom_tmul,
        baseChangeTwistIso_hom_twistElem]
    μₗ_unitality M := twist_moduleCatBaseChange_hom_ext (𝟙_ (Discrete H)) fun s m ↦ by
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, actionUnitIso_hom_twistElem,
        moduleCatBaseChange_map_hom_tmul, baseChangeTwistIso_hom_twistElem]
    δₗ_naturality_left {c c'} g M := by
      obtain ⟨c⟩ := c
      obtain ⟨c'⟩ := c'
      obtain rfl : c = c' := Discrete.eq_of_hom g
      obtain rfl : g = 𝟙 _ := Subsingleton.elim _ _
      simp
    δₗ_naturality_right c M M' φ := moduleCatBaseChange_hom_ext Λ f fun n ↦ by
      obtain ⟨m, rfl⟩ := exists_twistElem_eq aR c n
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, actionHomRight_hom_twistElem,
        moduleCatBaseChange_map_hom_tmul, baseChangeTwistIso_inv_tmul]
    δₗ_associativity c c' M := moduleCatBaseChange_hom_ext Λ f fun n ↦ by
      obtain ⟨m, rfl⟩ := exists_twistElem_eq aR (c ⊗ c') n
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, actionAssocIso_hom_twistElem,
        actionHomRight_hom_twistElem, moduleCatBaseChange_map_hom_tmul,
        baseChangeTwistIso_inv_tmul]
    δₗ_unitality_inv M := moduleCatBaseChange_hom_ext Λ f fun m ↦ by
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, actionUnitIso_inv_twistElem,
        moduleCatBaseChange_map_hom_tmul, baseChangeTwistIso_inv_tmul]
    μₗ_comp_δₗ c M := (baseChangeTwistIso hR hS hf c M).hom_inv_id
    δₗ_comp_μₗ c M := (baseChangeTwistIso hR hS hf c M).inv_hom_id }

open Functor.LaxLeftLinear Functor.OplaxLeftLinear

private lemma μₗ_hom_twistElem (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ)) (s : S) (m : M) :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    letI := aS.restrictScalarsMonoidalLeftAction.{u}
    letI := moduleCatBaseChangeLeftLinear hR hS hf
    (μₗ (moduleCatBaseChange Λ f) c M).hom (twistElem aS c (moduleCatBaseChangeTmul Λ f s m)) =
      moduleCatBaseChangeTmul Λ f s (twistElem aR c m) :=
  baseChangeTwistIso_hom_twistElem hR hS hf c M s m

/-- The lax lineators of `CommAlgCat.moduleCatBaseChangeLeftLinear` are the identity on tensors:
`s ⊗ m` in the twist of `S ⊗[R] M` goes to `s ⊗ m` in the base change of the twist of `M`. -/
@[simp]
lemma moduleCatBaseChangeLeftLinear_μₗ_hom_tmul (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ))
    (s : S) (m : M) :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    letI := aS.restrictScalarsMonoidalLeftAction.{u}
    letI := moduleCatBaseChangeLeftLinear hR hS hf
    (μₗ (moduleCatBaseChange Λ f) c M).hom (moduleCatBaseChangeTmul Λ f s m) =
      moduleCatBaseChangeTmul Λ f (N := (c ⊙ₗ M : ModuleCat.{u} (R ⊗[k] Λ))) s m :=
  baseChangeTwistIso_hom_twistElem hR hS hf c M s m

/-- The oplax lineators of `CommAlgCat.moduleCatBaseChangeLeftLinear` are the identity on
tensors. -/
@[simp]
lemma moduleCatBaseChangeLeftLinear_δₗ_hom_tmul (c : Discrete H) (M : ModuleCat.{u} (R ⊗[k] Λ))
    (s : S) (m : M) :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    letI := aS.restrictScalarsMonoidalLeftAction.{u}
    letI := moduleCatBaseChangeLeftLinear hR hS hf
    (δₗ (moduleCatBaseChange Λ f) c M).hom
        (moduleCatBaseChangeTmul Λ f (N := (c ⊙ₗ M : ModuleCat.{u} (R ⊗[k] Λ))) s m) =
      moduleCatBaseChangeTmul Λ f s m :=
  baseChangeTwistIso_inv_tmul hR hS hf c M s m

end Twist

section Comparison

variable {aR : H →* RingAut (R ⊗[k] Λ)}
  (hR : ∀ h r, aR h (algebraMap R (R ⊗[k] Λ) r) = algebraMap R (R ⊗[k] Λ) r)

include hR in
private lemma twistElem_smul (c : Discrete H) {M : ModuleCat.{u} (R ⊗[k] Λ)} (r : R) (m : M) :
    twistElem aR c (r • m) = r • twistElem aR c m :=
  (twistLinearEquiv hR c M).map_smul r m

/-- The unit comparison `S ⊗[R] M ≅ M` along `𝟙 R`, `r ⊗ m ↦ r • m`, is equivariant for the
twisting action. -/
lemma isLeftLinear_moduleCatBaseChangeId_hom :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    letI := moduleCatBaseChangeLeftLinear (f := 𝟙 R) hR hR fun h x ↦ by simp
    NatTrans.IsLeftLinear (moduleCatBaseChangeId Λ R).hom (Discrete H) :=
  letI := aR.restrictScalarsMonoidalLeftAction.{u}
  letI := moduleCatBaseChangeLeftLinear (f := 𝟙 R) hR hR fun h x ↦ by simp
  ⟨fun c M ↦ twist_moduleCatBaseChange_hom_ext c fun r m ↦ by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.LaxLeftLinear.id_μₗ,
      ModuleCat.hom_id, LinearMap.id_apply, actionHomRight_hom_twistElem, μₗ_hom_twistElem,
      moduleCatBaseChangeId_hom_app_hom_tmul, twistElem_smul hR]⟩

variable {T : CommAlgCat.{u} k} {aS : H →* RingAut (S ⊗[k] Λ)} {aT : H →* RingAut (T ⊗[k] Λ)}
  (hS : ∀ h s, aS h (algebraMap S (S ⊗[k] Λ) s) = algebraMap S (S ⊗[k] Λ) s)
  (hT : ∀ h t, aT h (algebraMap T (T ⊗[k] Λ) t) = algebraMap T (T ⊗[k] Λ) t)
  {f : R ⟶ S} {g : S ⟶ T}
  (hf : ∀ h x, Algebra.TensorProduct.map f.hom (AlgHom.id k Λ) (aR h x) =
    aS h (Algebra.TensorProduct.map f.hom (AlgHom.id k Λ) x))
  (hg : ∀ h x, Algebra.TensorProduct.map g.hom (AlgHom.id k Λ) (aS h x) =
    aT h (Algebra.TensorProduct.map g.hom (AlgHom.id k Λ) x))

/-- The composition comparison `T ⊗[R] M ≅ T ⊗[S] (S ⊗[R] M)` along `f ≫ g = fg`,
`t ⊗ m ↦ t ⊗ (1 ⊗ m)`, is equivariant for the twisting actions. -/
lemma isLeftLinear_moduleCatBaseChangeComp_hom (fg : R ⟶ T) (hfg : f ≫ g = fg) :
    letI := aR.restrictScalarsMonoidalLeftAction.{u}
    letI := aS.restrictScalarsMonoidalLeftAction.{u}
    letI := aT.restrictScalarsMonoidalLeftAction.{u}
    letI := moduleCatBaseChangeLeftLinear hR hS hf
    letI := moduleCatBaseChangeLeftLinear hS hT hg
    letI := moduleCatBaseChangeLeftLinear (f := fg) hR hT fun h x ↦ by
      rw [tensorProductMap_comp_apply Λ hfg, tensorProductMap_comp_apply Λ hfg, hf, hg]
    NatTrans.IsLeftLinear (moduleCatBaseChangeComp Λ f g fg hfg).hom (Discrete H) :=
  letI := aR.restrictScalarsMonoidalLeftAction.{u}
  letI := aS.restrictScalarsMonoidalLeftAction.{u}
  letI := aT.restrictScalarsMonoidalLeftAction.{u}
  letI := moduleCatBaseChangeLeftLinear hR hS hf
  letI := moduleCatBaseChangeLeftLinear hS hT hg
  letI := moduleCatBaseChangeLeftLinear (f := fg) hR hT fun h x ↦ by
    rw [tensorProductMap_comp_apply Λ hfg, tensorProductMap_comp_apply Λ hfg, hf, hg]
  ⟨fun c M ↦ twist_moduleCatBaseChange_hom_ext c fun t m ↦ by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.LaxLeftLinear.comp_μₗ]
    rw [μₗ_hom_twistElem (f := fg) hR hT, moduleCatBaseChangeComp_hom_app_hom_tmul,
      actionHomRight_hom_twistElem, moduleCatBaseChangeComp_hom_app_hom_tmul,
      μₗ_hom_twistElem hS hT hg, moduleCatBaseChange_map_hom_tmul, μₗ_hom_twistElem hR hS hf]⟩

end Comparison

end CommAlgCat
