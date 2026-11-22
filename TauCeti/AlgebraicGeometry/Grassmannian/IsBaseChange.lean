/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.AlgebraicGeometry.Scheme.AffinePoints

/-!
# The Grassmannian scheme along a base change of modules

Let `R → R'` be a map of commutative rings, `M` an `R`-module, `M'` an `R'`-module and
`f : M →ₗ[R] M'` an `R`-linear map exhibiting `M'` as the base change of `M` to `R'`
(`IsBaseChange R' f`). This file constructs the morphism of Grassmannian schemes
`Module.Grassmannian.isBaseChangeHom hf : G(k, M') ⟶ G(k, M)` over `Spec R' ⟶ Spec R` and proves
that it exhibits `G(k, M')` as the fibre product `Spec R' ×_{Spec R} G(k, M)`
(`Module.Grassmannian.isPullback_isBaseChangeHom`). These morphisms compose
(`Module.Grassmannian.isBaseChangeHom_comp`).

`Module.Grassmannian.baseChangeHom` treats the base change `R' ⊗[R] M` itself. The present form,
for any `M'` with a base-change map, is the one needed to glue the Grassmannians of the modules of
sections of a quasi-coherent sheaf over the affine opens of a scheme
(`TauCeti.AlgebraicGeometry.Grassmannian.Relative`): for affine opens `V ≤ U`, the sections over
`V` are a base change of the sections over `U` along restriction, but they are not the tensor
product `Γ(V, 𝒪) ⊗ Γ(U, E)` itself.

For an `R'`-algebra `A`, the map `f` induces an `A`-linear isomorphism
`A ⊗[R'] M' ≃ A ⊗[R] M` sending `a ⊗ f m` to `a ⊗ m`
(`Module.Grassmannian.isBaseChangeLinearEquiv`), and transport along it identifies the points of
the two Grassmannians over `A` (`Module.Grassmannian.isBaseChangeEquiv`), naturally in `A`.
Composing with the classifying morphisms of `Module.Grassmannian.schemeHomEquiv` gives a natural
map on affine points, which is composition with a unique morphism of schemes
(`AlgebraicGeometry.Scheme.homOfAffinePoints`).

## Main definitions

* `Module.Grassmannian.isBaseChangeLinearEquiv hf A`: the isomorphism `A ⊗[R'] M' ≃ A ⊗[R] M`.
* `Module.Grassmannian.isBaseChangeEquiv hf`: the induced bijection
  `G(k, A ⊗[R'] M'; A) ≃ G(k, A ⊗[R] M; A)`.
* `Module.Grassmannian.isBaseChangeHom hf k`: the morphism `G(k, M') ⟶ G(k, M)`.

## Main results

* `Module.Grassmannian.isBaseChangeEquiv_map`: the bijection on points is natural in `A`.
* `Module.Grassmannian.toSchemeHom_comp_isBaseChangeHom`: the morphism on points.
* `Module.Grassmannian.isPullback_isBaseChangeHom`: **base change**; `G(k, M')` is the fibre
  product of `G(k, M)` and `Spec R'` over `Spec R`.
* `Module.Grassmannian.isBaseChangeHom_comp`: the morphisms for two successive base changes
  compose to the morphism for the composite base change.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {M M' : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] [Module R M']
  [IsScalarTower R R' M'] {f : M →ₗ[R] M'} (hf : IsBaseChange R' f)

section Points

variable (A : Type u) [CommRing A] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A]

/-- For a base change `f : M → M'` along `R → R'` and an `R'`-algebra `A`, the `A`-linear
isomorphism `A ⊗[R'] M' ≃ A ⊗[R] M` sending `a ⊗ f m` to `a ⊗ m`
(`Module.Grassmannian.isBaseChangeLinearEquiv_tmul`). -/
noncomputable def isBaseChangeLinearEquiv : A ⊗[R'] M' ≃ₗ[A] A ⊗[R] M :=
  (AlgebraTensorModule.congr (LinearEquiv.refl A A) hf.equiv.symm).trans
    (AlgebraTensorModule.cancelBaseChange R R' A A M)

@[simp]
theorem isBaseChangeLinearEquiv_tmul (a : A) (m : M) :
    isBaseChangeLinearEquiv hf A (a ⊗ₜ f m) = a ⊗ₜ m := by
  simp [isBaseChangeLinearEquiv]

include hf in
omit [Algebra R A] [IsScalarTower R R' A] in
/-- A property of the elements of `A ⊗[R'] M'` which is closed under addition holds as soon as it
holds on the tensors `a ⊗ f m`, since `M'` is generated over `R'` by the image of `f`. -/
theorem _root_.IsBaseChange.forall_tmul {motive : A ⊗[R'] M' → Prop}
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (tmul : ∀ (a : A) (m : M), motive (a ⊗ₜ f m)) (x : A ⊗[R'] M') : motive x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact add x y hx hy
  | tmul a m' =>
    induction m' using hf.inductionOn generalizing a with
    | tmul m => exact tmul a m
    | smul s n h => rw [← smul_tmul]; exact h _
    | add n₁ n₂ h₁ h₂ => rw [tmul_add]; exact add _ _ (h₁ a) (h₂ a)

/-- **Points of the Grassmannian along a base change.** For a base change `f : M → M'` along
`R → R'` and an `R'`-algebra `A`, the points of the Grassmannian of `M'` over `A` are the points
of the Grassmannian of `M` over `A`, through the isomorphism `A ⊗[R'] M' ≃ A ⊗[R] M`. This
bijection is natural in `A` (`Module.Grassmannian.isBaseChangeEquiv_map`). -/
noncomputable def isBaseChangeEquiv {k : ℕ} : G(k, A ⊗[R'] M'; A) ≃ G(k, A ⊗[R] M; A) :=
  (isBaseChangeLinearEquiv hf A).grassmannianCongr

variable {A}

@[simp]
theorem toSubmodule_isBaseChangeEquiv {k : ℕ} (N : G(k, A ⊗[R'] M'; A)) :
    (isBaseChangeEquiv hf A N).toSubmodule =
      N.toSubmodule.map (isBaseChangeLinearEquiv hf A).toLinearMap :=
  LinearEquiv.toSubmodule_grassmannianCongr_apply _ N

variable {B : Type u} [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]

/-- **Naturality of `isBaseChangeEquiv`.** Base change of points along an `R'`-algebra map
`g : A → B` corresponds to base change along `g` as an `R`-algebra map. -/
theorem isBaseChangeEquiv_map {k : ℕ} (g : A →ₐ[R'] B) (N : G(k, A ⊗[R'] M'; A)) :
    isBaseChangeEquiv hf B (map g N) = map (g.restrictScalars R) (isBaseChangeEquiv hf A N) := by
  ext : 1
  simp only [toSubmodule_isBaseChangeEquiv, map_toSubmodule_eq_span, Submodule.map_span,
    Submodule.map_coe, ← Set.image_comp]
  refine congrArg _ (Set.image_congr' rfl fun x ↦ ?_)
  induction x using hf.forall_tmul A with
  | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  | tmul a m => simp

end Points

section Scheme

variable (k : ℕ)

/-- The morphism `Spec A ⟶ G(k, M)` over `Spec R` classifying the point of `G(k, A ⊗[R] M; A)`
which corresponds to a morphism `Spec A ⟶ G(k, M')` over `Spec R'`. The algebra structures on `A`
are explicit arguments, so that `isBaseChangeAux_congr` can compare different choices. -/
private noncomputable def isBaseChangeAux (A : Type u) [CommRing A] (_ : Algebra R' A)
    (_ : Algebra R A) (_ : IsScalarTower R R' A) (a : Spec (.of A) ⟶ scheme R' M' k)
    (ha : a ≫ toSpec R' M' k = Spec.map (CommRingCat.ofHom (algebraMap R' A))) :
    Spec (.of A) ⟶ scheme R M k :=
  toSchemeHom (isBaseChangeEquiv hf A ((schemeHomEquiv R' M' k A).symm ⟨a, ha⟩))

-- `isBaseChangeAux` depends on the algebra structures on `A` only through their equality class.
private lemma isBaseChangeAux_congr (A : Type u) [CommRing A] (iR' jR' : Algebra R' A)
    (iR jR : Algebra R A)
    (t : @IsScalarTower R R' A _ (@Algebra.toSMul _ _ _ _ iR') (@Algebra.toSMul _ _ _ _ iR))
    (t' : @IsScalarTower R R' A _ (@Algebra.toSMul _ _ _ _ jR') (@Algebra.toSMul _ _ _ _ jR))
    (h' : iR' = jR') (h : iR = jR) (a : Spec (.of A) ⟶ scheme R' M' k) (ha ha') :
    isBaseChangeAux hf k A iR' iR t a ha = isBaseChangeAux hf k A jR' jR t' a ha' := by
  subst h' h
  rfl

/-- The morphism of affine points underlying `isBaseChangeHom`: the algebra structure of `A` over
`R'` is read off from the composite `Spec A ⟶ G(k, M') ⟶ Spec R'`. -/
private noncomputable def isBaseChangePoint {A : CommRingCat.{u}}
    (a : Spec A ⟶ scheme R' M' k) : Spec A ⟶ scheme R M k :=
  let φ : R' →+* A := (Spec.preimage (a ≫ toSpec R' M' k)).hom
  letI := φ.toAlgebra
  letI : Algebra R A := (φ.comp (algebraMap R R')).toAlgebra
  isBaseChangeAux hf k A ‹_› ‹_› (.of_algebraMap_eq' rfl) a (Spec.map_preimage _).symm

variable {k}

/-- `isBaseChangePoint` computed with any algebra structures on `A` compatible with the
morphism. -/
private lemma isBaseChangePoint_eq (A : Type u) [CommRing A] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (a : Spec (.of A) ⟶ scheme R' M' k)
    (ha : a ≫ toSpec R' M' k = Spec.map (CommRingCat.ofHom (algebraMap R' A))) :
    isBaseChangePoint hf k a = isBaseChangeAux hf k A ‹_› ‹_› ‹_› a ha := by
  have hφ : (Spec.preimage (a ≫ toSpec R' M' k)).hom = algebraMap R' A := by
    rw [ha, Spec.preimage_map, CommRingCat.hom_ofHom]
  refine isBaseChangeAux_congr hf k A _ _ _ _ _ ‹_› ?_ ?_ a _ _
  · exact Algebra.algebra_ext _ _ fun r ↦ DFunLike.congr_fun hφ r
  · refine Algebra.algebra_ext _ _ fun r ↦ ?_
    rw [IsScalarTower.algebraMap_apply R R' A]
    exact DFunLike.congr_fun hφ _

variable {A : Type u} [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]

private lemma isBaseChangePoint_toSchemeHom (N : G(k, A ⊗[R'] M'; A)) :
    isBaseChangePoint hf k (toSchemeHom N) = toSchemeHom (isBaseChangeEquiv hf A N) := by
  rw [isBaseChangePoint_eq hf A _ (toSchemeHom_toSpec N), isBaseChangeAux]
  congr 2
  exact (Equiv.symm_apply_eq _).2 (Subtype.ext (coe_schemeHomEquiv_apply N).symm)

/-- `isBaseChangePoint` is natural in the affine scheme. -/
private lemma isBaseChangePoint_comp {B C : CommRingCat.{u}} (ψ : Spec C ⟶ Spec B)
    (a : Spec B ⟶ scheme R' M' k) :
    isBaseChangePoint hf k (ψ ≫ a) = ψ ≫ isBaseChangePoint hf k a := by
  -- give `B` and `C` the algebra structures over `R'` read off from `a` and `ψ ≫ a`; with them,
  -- `algebraMap R' B` is `φ` by definition, and `χ` is an `R'`-algebra map `χ'`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R' M' k)
  obtain ⟨χ, rfl⟩ := Spec.map_surjective ψ
  let _ : Algebra R' B := φ.hom.toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  let _ : Algebra R' C := (χ.hom.comp φ.hom).toAlgebra
  let _ : Algebra R C := ((χ.hom.comp φ.hom).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' C := .of_algebraMap_eq' rfl
  let χ' : B →ₐ[R'] C := { χ.hom with commutes' := fun _ ↦ rfl }
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  have h : Spec.map χ ≫ toSchemeHom N = toSchemeHom (map χ' N) := (toSchemeHom_map χ' N).symm
  rw [h, isBaseChangePoint_toSchemeHom, isBaseChangePoint_toSchemeHom, isBaseChangeEquiv_map,
    toSchemeHom_map]
  -- `χ'.restrictScalars R` has underlying ring map `χ`
  rfl

variable (k) in
/-- **The Grassmannian along a base change of modules.** For a base change `f : M → M'` along
`R → R'`, the morphism `G(k, M') ⟶ G(k, M)` which sends the point classifying `N` over an
`R'`-algebra `A` to the point classifying its image under `A ⊗[R'] M' ≃ A ⊗[R] M`
(`Module.Grassmannian.toSchemeHom_comp_isBaseChangeHom`). Together with the structure morphism of
`G(k, M')`, it exhibits `G(k, M')` as the base change of `G(k, M)` to `Spec R'`
(`Module.Grassmannian.isPullback_isBaseChangeHom`). -/
noncomputable def isBaseChangeHom : scheme R' M' k ⟶ scheme R M k :=
  Scheme.homOfAffinePoints (isBaseChangePoint hf k) (isBaseChangePoint_comp hf)

variable (k) in
/-- `isBaseChangeHom` depends on the base change map only through its value: two equal maps give
the same morphism, whichever proofs of the base change property are used. -/
theorem isBaseChangeHom_congr {f' : M →ₗ[R] M'} (hf' : IsBaseChange R' f') (h : f = f') :
    isBaseChangeHom hf k = isBaseChangeHom hf' k := by
  subst h
  rfl

/-- **`isBaseChangeHom` on points.** The morphism classifying `N` over an `R'`-algebra `A`,
composed with `isBaseChangeHom`, classifies the image of `N` in `G(k, A ⊗[R] M; A)`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_isBaseChangeHom (N : G(k, A ⊗[R'] M'; A)) :
    toSchemeHom N ≫ isBaseChangeHom hf k = toSchemeHom (isBaseChangeEquiv hf A N) :=
  (Scheme.comp_homOfAffinePoints _ _ _).trans (isBaseChangePoint_toSchemeHom hf N)

variable (k) in
/-- `isBaseChangeHom` lies over `Spec R' ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem isBaseChangeHom_toSpec :
    isBaseChangeHom hf k ≫ toSpec R M k =
      toSpec R' M' k ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ ?_
  -- make `B` an `R'`-algebra through `a`, so that `a` classifies a point over `B`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R' M' k)
  let _ : Algebra R' B := φ.hom.toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  rw [toSchemeHom_comp_isBaseChangeHom_assoc, toSchemeHom_toSpec, toSchemeHom_toSpec_assoc,
    ← Spec.map_comp]
  -- `algebraMap R B` is `φ ∘ algebraMap R R'` by definition
  rfl

variable (k) in
/-- **Base change of the Grassmannian scheme along a base change of modules.** For a base change
`f : M → M'` along `R → R'`, the Grassmannian `G(k, M')` over `Spec R'` is the fibre product of
`G(k, M) ⟶ Spec R` and `Spec R' ⟶ Spec R`, with projections `isBaseChangeHom` and the structure
morphism. -/
theorem isPullback_isBaseChangeHom :
    IsPullback (isBaseChangeHom hf k) (toSpec R' M' k) (toSpec R M k)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  refine Scheme.isPullback_of_forall_spec (isBaseChangeHom_toSpec hf k) fun B a b hab ↦ ?_
  -- `b` makes `B` an `R'`-algebra, and `a` classifies a point of `G(k, B ⊗[R] M; B)`
  obtain ⟨φ, rfl⟩ := Spec.map_surjective b
  let _ : Algebra R' B := φ.hom.toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' B := .of_algebraMap_eq' rfl
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a (hab.trans (Spec.map_comp _ _).symm)
  refine ⟨toSchemeHom ((isBaseChangeEquiv hf B).symm N), ⟨by simp, toSchemeHom_toSpec _⟩, ?_⟩
  rintro c ⟨hc₁, hc₂⟩
  obtain ⟨N', rfl⟩ := exists_toSchemeHom_eq (A := B) c hc₂
  rw [toSchemeHom_comp_isBaseChangeHom] at hc₁
  rw [← toSchemeHom_injective hc₁, Equiv.symm_apply_apply]

section Comp

variable {R'' M'' : Type u} [CommRing R''] [Algebra R' R''] [Algebra R R'']
  [IsScalarTower R R' R''] [AddCommGroup M''] [Module R'' M''] [Module R' M''] [Module R M'']
  [IsScalarTower R' R'' M''] [IsScalarTower R R'' M''] [IsScalarTower R R' M''] {g : M' →ₗ[R'] M''}
  (hg : IsBaseChange R'' g)

/-- **Composition of `isBaseChangeHom`.** For base changes `f : M → M'` along `R → R'` and
`g : M' → M''` along `R' → R''`, the composite of the morphisms `G(k, M'') ⟶ G(k, M')` and
`G(k, M') ⟶ G(k, M)` is the morphism of the composite base change `g ∘ f` along `R → R''`. -/
theorem isBaseChangeHom_comp (hgf : IsBaseChange R'' (g.restrictScalars R ∘ₗ f)) :
    isBaseChangeHom hg k ≫ isBaseChangeHom hf k = isBaseChangeHom hgf k := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ ?_
  -- make `B` an algebra over `R''`, `R'` and `R` through `a`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R'' M'' k)
  let _ : Algebra R'' B := φ.hom.toAlgebra
  let _ : Algebra R' B := (φ.hom.comp (algebraMap R' R'')).toAlgebra
  let _ : Algebra R B := (φ.hom.comp (algebraMap R R'')).toAlgebra
  have : IsScalarTower R' R'' B := .of_algebraMap_eq' rfl
  have : IsScalarTower R R'' B := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' B := .of_algebraMap_eq' <| by
    change φ.hom.comp (algebraMap R R'') = (φ.hom.comp (algebraMap R' R'')).comp (algebraMap R R')
    rw [IsScalarTower.algebraMap_eq R R' R'', RingHom.comp_assoc]
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  rw [toSchemeHom_comp_isBaseChangeHom_assoc, toSchemeHom_comp_isBaseChangeHom,
    toSchemeHom_comp_isBaseChangeHom]
  congr 1
  ext : 1
  simp only [toSubmodule_isBaseChangeEquiv, ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun x ↦ ?_
  induction x using hg.forall_tmul B with
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply, map_add] at hx hy ⊢
    rw [hx, hy]
  | tmul b m' =>
    induction m' using hf.inductionOn generalizing b with
    | tmul m =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        isBaseChangeLinearEquiv_tmul]
      exact (isBaseChangeLinearEquiv_tmul hgf B b m).symm
    | smul s n h =>
      rw [map_smul, ← smul_tmul]
      exact h _
    | add n₁ n₂ h₁ h₂ =>
      rw [map_add, tmul_add, map_add, map_add, h₁, h₂]

end Comp

end Scheme

end Module.Grassmannian
