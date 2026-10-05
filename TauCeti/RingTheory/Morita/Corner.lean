/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Basic
public import TauCeti.RingTheory.Idempotents.Module
public import TauCeti.RingTheory.TwoSidedIdeal.Span

/-!
# Morita equivalence with the corner ring of a full idempotent

Let `e` be an idempotent of a ring `A`, and let `eAe` be its corner ring
(`IsIdempotentElem.Corner`), the ring of elements `e * a * e`, with unit `e`. Every `A`-module `M`
has a piece `eM = e • M` (written `e • (⊤ : Submodule ℤ M)`, as in
`TauCeti.RingTheory.Idempotents.Module`), which is a module over `eAe`. This defines the
**corner functor**

`IsIdempotentElem.cornerFunctor : ModuleCat A ⥤ ModuleCat eAe`,  `M ↦ eM`.

In the other direction, `eA` is a left `eAe`-module and a right `A`-module, so for an
`eAe`-module `N` the homomorphisms `Hom_{eAe}(eA, N)` form an `A`-module, `A` acting by right
multiplication on `eA`. This is the **coinduction functor**
`IsIdempotentElem.cornerCoindFunctor : ModuleCat eAe ⥤ ModuleCat A`.

The composite `N ↦ e Hom_{eAe}(eA, N)` is always isomorphic to the identity, by evaluation at `e`
(`IsIdempotentElem.smulTopCoindEquiv`). The other composite `M ↦ Hom_{eAe}(eA, eM)` receives the
action map `m ↦ (x ↦ x • m)` (`IsIdempotentElem.smulTopActionHom`), and this map is bijective as
soon as `e` is **full**, that is, generates `A` as a two-sided ideal, `AeA = A`: writing
`1 = ∑ aᵢ e bᵢ`, an element killed by `eA` is killed by `1`, and a homomorphism `f : eA → eM` is
the action of `∑ aᵢ • f(e bᵢ)`. So for a full idempotent the two functors are mutually inverse
equivalences (`IsIdempotentElem.cornerEquivalence`), and the corner functor is linear over any
commutative semiring `R` over which `A` is an algebra. This is the Morita equivalence between `A`
and `eAe`, in Mathlib's sense (`IsIdempotentElem.moritaEquivalenceCorner`).

Fullness is the hypothesis that makes the corner ring see every module. It is the hypothesis
used to reduce a finite-dimensional algebra to a **basic** one: there the idempotent is the sum of
one primitive idempotent for each isomorphism class of simple modules, which is full and has a
basic corner ring. That such an idempotent exists is not proved in this file.

## Main definitions

* `IsIdempotentElem.cornerFunctor`: the functor `M ↦ eM` from `A`-modules to `eAe`-modules.
* `IsIdempotentElem.cornerCoindFunctor`: the functor `N ↦ Hom_{eAe}(eA, N)` back.
* `IsIdempotentElem.cornerEquivalence`: for a full idempotent, the two functors form an equivalence
  of categories.
* `IsIdempotentElem.moritaEquivalenceCorner`: for a full idempotent of an `R`-algebra `A`, the
  Morita equivalence between `A` and `eAe` as `R`-algebras.

## Main results

* `IsIdempotentElem.smulTopActionHom_injective` and
  `IsIdempotentElem.smulTopActionHom_surjective`: for a full idempotent, the action map
  `M → Hom_{eAe}(eA, eM)` is bijective.
* `IsIdempotentElem.isMoritaEquivalent_corner`: **a ring is Morita equivalent to the corner ring of
  any full idempotent.**

## Implementation notes

The inverse functor is built from homomorphisms out of `eA` rather than from the tensor product
`Ae ⊗_{eAe} N`, which would need tensor products over the noncommutative ring `eAe`. The two
functors are given `@[expose]` so that their objects can be read as the pieces `eM` and the spaces
of homomorphisms `Hom_{eAe}(eA, N)`, on which the action lemmas of this file are stated. The
equivalence is built with `CategoryTheory.Equivalence.mk'`, so that its unit and counit are exactly
`IsIdempotentElem.cornerUnitIso` and `IsIdempotentElem.cornerCounitIso`, and is given `@[expose]`
so that this identification can be stated. The types of the unit and counit depend on the
equivalence's functor and inverse: without exposure, the public statements of
`IsIdempotentElem.cornerEquivalence_unitIso` and `IsIdempotentElem.cornerEquivalence_counitIso`
cannot identify those types with the ones of the supplied natural isomorphisms. The functor and
inverse projection equalities alone do not supply this definitional equality during elaboration.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189, §18 (Morita
  theory, full idempotents).
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Section I.6 (basic algebras).
-/

public section

open CategoryTheory
open scoped Pointwise

universe w v u

namespace IsIdempotentElem

variable {A : Type u} [Ring A] {e : A} (he : IsIdempotentElem e)

/-! ### The bimodule `eA` -/

/-- The idempotent `e`, as an element of the piece `eA` of the regular module. -/
def smulTopGen : ↥(e • (⊤ : Submodule ℤ A)) :=
  ⟨e, he.mem_smul_top_iff_smul_eq_self.2 he.eq⟩

@[simp]
theorem coe_smulTopGen : (he.smulTopGen : A) = e := (rfl)

/-- Right multiplication by `a` on `eA`, a homomorphism of modules over the corner ring `eAe`. It
makes `eA` a right `A`-module. -/
def smulTopMulRight (a : A) :
    ↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] ↥(e • (⊤ : Submodule ℤ A)) where
  toFun x := ⟨x.1 * a, he.mem_smul_top_iff_smul_eq_self.2 (by
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul e x.1, he.smul_eq_self_of_mem_smul_top x.2])⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 a)
  map_smul' b x := Subtype.ext (mul_assoc b.1 x.1 a)

@[simp]
theorem coe_smulTopMulRight_apply (a : A) (x : ↥(e • (⊤ : Submodule ℤ A))) :
    (he.smulTopMulRight a x : A) = x * a := (rfl)

@[simp]
theorem smulTopMulRight_one : he.smulTopMulRight 1 = LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext (mul_one x.1)

theorem smulTopMulRight_mul (a a' : A) :
    he.smulTopMulRight (a * a') = he.smulTopMulRight a' ∘ₗ he.smulTopMulRight a :=
  LinearMap.ext fun x ↦ Subtype.ext (mul_assoc x.1 a a').symm

@[simp]
theorem smulTopMulRight_zero : he.smulTopMulRight 0 = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext (mul_zero x.1)

@[simp]
theorem smulTopMulRight_add (a a' : A) :
    he.smulTopMulRight (a + a') = he.smulTopMulRight a + he.smulTopMulRight a' :=
  LinearMap.ext fun x ↦ Subtype.ext (mul_add x.1 a a')

@[simp]
theorem smulTopMulRight_neg (a : A) : he.smulTopMulRight (-a) = -he.smulTopMulRight a :=
  LinearMap.ext fun x ↦ Subtype.ext (mul_neg x.1 a)

/-- The element `x * e` of the corner ring attached to an element `x` of `eA`. -/
def smulTopToCorner : ↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] he.Corner where
  toFun x := ⟨x.1 * e, (Subsemigroup.mem_corner_iff he).2
    ⟨by rw [← mul_assoc, ← smul_eq_mul e x.1, he.smul_eq_self_of_mem_smul_top x.2],
      by rw [mul_assoc, he.eq]⟩⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 e)
  map_smul' b x := Subtype.ext (mul_assoc b.1 x.1 e)

@[simp]
theorem val_smulTopToCorner_apply (x : ↥(e • (⊤ : Submodule ℤ A))) :
    (he.smulTopToCorner x).1 = x * e := (rfl)

/-! ### Homomorphisms out of `eA` as an `A`-module -/

section Coind

variable {N : Type v} [AddCommGroup N] [Module he.Corner N]

/-- `A` acts on `Hom_{eAe}(eA, N)` through right multiplication on `eA`. -/
instance instSMulSmulTopLinearMap : SMul A (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N) where
  smul a f := f ∘ₗ he.smulTopMulRight a

theorem smul_smulTop_linearMap_def (a : A) (f : ↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N) :
    a • f = f ∘ₗ he.smulTopMulRight a := (rfl)

@[simp]
theorem smul_smulTop_linearMap_apply (a : A) (f : ↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N)
    (x : ↥(e • (⊤ : Submodule ℤ A))) : (a • f) x = f (he.smulTopMulRight a x) := (rfl)

/-- **`Hom_{eAe}(eA, N)` is an `A`-module**, `A` acting by right multiplication on `eA`. -/
instance instModuleSmulTopLinearMap : Module A (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N) where
  one_smul f := by rw [smul_smulTop_linearMap_def, smulTopMulRight_one, LinearMap.comp_id]
  mul_smul a a' f := by
    simp only [smul_smulTop_linearMap_def, smulTopMulRight_mul, LinearMap.comp_assoc]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul a a' f := by
    simp only [smul_smulTop_linearMap_def, smulTopMulRight_add, LinearMap.comp_add]
  zero_smul f := by
    simp only [smul_smulTop_linearMap_def, smulTopMulRight_zero, LinearMap.comp_zero]

end Coind

/-! ### The two functors -/

/-- **The corner functor** `M ↦ eM`, from modules over `A` to modules over the corner ring
`eAe`. -/
@[expose] def cornerFunctor : ModuleCat.{v} A ⥤ ModuleCat.{v} he.Corner where
  obj M := ModuleCat.of he.Corner ↥(e • (⊤ : Submodule ℤ M))
  map f := ModuleCat.ofHom
    { toFun := TauCeti.smulTopMap ℤ e f.hom
      map_add' := map_add _
      map_smul' := fun _ _ ↦ Subtype.ext (by simp) }

/-- **The coinduction functor** `N ↦ Hom_{eAe}(eA, N)`, from modules over the corner ring `eAe`
to modules over `A`. -/
@[expose] def cornerCoindFunctor : ModuleCat.{max u v} he.Corner ⥤ ModuleCat.{max u v} A where
  obj N := ModuleCat.of A (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N)
  map g := ModuleCat.ofHom
    { toFun := fun f ↦ g.hom ∘ₗ f
      map_add' := fun f f' ↦ LinearMap.comp_add f f' g.hom
      map_smul' := fun _ _ ↦ rfl }

@[simp]
theorem cornerFunctor_obj (M : ModuleCat.{v} A) :
    he.cornerFunctor.obj M = ModuleCat.of he.Corner ↥(e • (⊤ : Submodule ℤ M)) :=
  (rfl)

@[simp]
theorem cornerCoindFunctor_obj (N : ModuleCat.{max u v} he.Corner) :
    he.cornerCoindFunctor.obj N =
      ModuleCat.of A (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N) :=
  (rfl)

@[simp]
theorem coe_cornerFunctor_map_hom_apply {M N : ModuleCat.{v} A} (f : M ⟶ N)
    (x : ↥(e • (⊤ : Submodule ℤ M))) :
    ((he.cornerFunctor.map f).hom x).1 = f.hom x :=
  TauCeti.coe_smulTopMap_apply e f.hom x

@[simp]
theorem cornerCoindFunctor_map_hom_apply {N N' : ModuleCat.{max u v} he.Corner} (g : N ⟶ N')
    (f : ↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N) :
    ((he.cornerCoindFunctor.map g).hom f : ↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N') =
      g.hom ∘ₗ f :=
  (rfl)

/-! ### The counit: `e Hom_{eAe}(eA, N) ≅ N` -/

section Counit

variable (N : Type v) [AddCommGroup N] [Module he.Corner N]

/-- **Evaluation at `e` identifies `e Hom_{eAe}(eA, N)` with `N`**, for every idempotent `e`. The
inverse sends `n` to the homomorphism `x ↦ (x * e) • n`. -/
def smulTopCoindEquiv :
    ↥(e • (⊤ : Submodule ℤ (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N))) ≃ₗ[he.Corner] N where
  toFun f := f.1 he.smulTopGen
  map_add' _ _ := rfl
  map_smul' b f := by
    rw [RingHom.id_apply, ← f.1.map_smul, Corner.coe_smul, smul_smulTop_linearMap_apply]
    congr 1
    exact Subtype.ext (by simp)
  invFun n := ⟨LinearMap.toSpanSingleton he.Corner N n ∘ₗ he.smulTopToCorner,
    he.mem_smul_top_iff_smul_eq_self.2 (by
      ext x
      simp only [smul_smulTop_linearMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply]
      congr 1
      exact Subtype.ext (by simp [val_smulTopToCorner_apply, mul_assoc, he.eq]))⟩
  left_inv f := by
    refine Subtype.ext (LinearMap.ext fun x ↦ ?_)
    conv_rhs => rw [← he.smul_eq_self_of_mem_smul_top f.2]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply,
      ← f.1.map_smul, smul_smulTop_linearMap_apply]
    congr 1
    exact Subtype.ext (by simp [val_smulTopToCorner_apply, mul_assoc, he.eq])
  right_inv n := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply]
    convert one_smul he.Corner n
    exact Subtype.ext (by simp [val_smulTopToCorner_apply, he.eq])

@[simp]
theorem smulTopCoindEquiv_apply
    (f : ↥(e • (⊤ : Submodule ℤ (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N)))) :
    he.smulTopCoindEquiv N f = f.1 he.smulTopGen := (rfl)

@[simp]
theorem smulTopCoindEquiv_symm_apply_coe_apply (n : N) (x : ↥(e • (⊤ : Submodule ℤ A))) :
    ((he.smulTopCoindEquiv N).symm n).1 x = he.smulTopToCorner x • n := (rfl)

end Counit

/-! ### The unit: `M ≅ Hom_{eAe}(eA, eM)` for a full idempotent -/

section Unit

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- The action of `eA` on an `A`-module `M`, as an `A`-linear map `M → Hom_{eAe}(eA, eM)`. -/
def smulTopActionHom :
    M →ₗ[A] (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] ↥(e • (⊤ : Submodule ℤ M))) where
  toFun m :=
    { toFun := fun x ↦ ⟨x.1 • m, TauCeti.smul_mem_smul_top_of_mul_eq_self
        (he.smul_eq_self_of_mem_smul_top x.2) m⟩
      map_add' := fun x y ↦ Subtype.ext (add_smul x.1 y.1 m)
      map_smul' := fun b x ↦ Subtype.ext (mul_smul b.1 x.1 m) }
  map_add' m m' := LinearMap.ext fun x ↦ Subtype.ext (smul_add x.1 m m')
  map_smul' a m := LinearMap.ext fun x ↦ Subtype.ext (mul_smul x.1 a m).symm

@[simp]
theorem coe_smulTopActionHom_apply_apply (m : M) (x : ↥(e • (⊤ : Submodule ℤ A))) :
    (he.smulTopActionHom M m x : M) = x.1 • m := (rfl)

variable {M}

variable (hfull : TwoSidedIdeal.span {e} = ⊤)
include hfull

/-- For a full idempotent `e`, an element of an `A`-module killed by `eA` is zero. -/
theorem smulTopActionHom_injective : Function.Injective (he.smulTopActionHom M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  -- The elements of `A` killing `m` form an additive subgroup containing every `a * e * b`.
  simpa only [SetLike.mem_coe, AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe,
    LinearMap.toSpanSingleton_apply, one_smul] using
    (TauCeti.TwoSidedIdeal.coe_span_subset_addSubgroup_iff
      (H := (LinearMap.toSpanSingleton A M m).toAddMonoidHom.ker)).2 (by
      intro a x hx b
      rw [Set.mem_singleton_iff.1 hx]
      have h := congrArg Subtype.val
        (LinearMap.congr_fun hm ⟨e * b, Submodule.smul_mem_pointwise_smul b e ⊤ trivial⟩)
      rw [coe_smulTopActionHom_apply_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero] at h
      simp [mul_assoc, mul_smul, h]) (hfull ▸ trivial : (1 : A) ∈ TwoSidedIdeal.span {e})

/-- For a full idempotent `e`, every homomorphism `eA → eM` of modules over the corner ring is the
action of an element of `M`. -/
theorem smulTopActionHom_surjective : Function.Surjective (he.smulTopActionHom M) := by
  intro f
  -- The `z : A` for which `x ↦ f (x * z)` is the action of an element of `M` form an additive
  -- subgroup of `A`; it contains every `a * e * b`, hence `1`.
  let H : AddSubgroup A :=
    { carrier := {z | ∃ m : M, ∀ x, x.1 • m = (f (he.smulTopMulRight z x) : M)}
      zero_mem' := ⟨0, fun x ↦ by simp⟩
      add_mem' := by
        rintro z z' ⟨m, hm⟩ ⟨m', hm'⟩
        exact ⟨m + m', fun x ↦ by simp [hm, hm']⟩
      neg_mem' := by
        rintro z ⟨m, hm⟩
        exact ⟨-m, fun x ↦ by simp [hm]⟩ }
  obtain ⟨m, hm⟩ := (TauCeti.TwoSidedIdeal.coe_span_subset_addSubgroup_iff (H := H)).2 (by
    intro a x hx b
    rw [Set.mem_singleton_iff.1 hx]
    let y : ↥(e • (⊤ : Submodule ℤ M)) := f ⟨e * b, Submodule.smul_mem_pointwise_smul b e ⊤ trivial⟩
    refine ⟨a • (y : M), fun x ↦ ?_⟩
    -- `x * a • y = (x * a * e) • y`, and `x * a * e` lies in the corner ring.
    rw [← mul_smul, ← he.smul_eq_self_of_mem_smul_top y.2, ← mul_smul]
    have hxy : (x.1 * a * e) • (y : M) =
        ((he.smulTopToCorner (he.smulTopMulRight a x) • y : ↥(e • (⊤ : Submodule ℤ M))) : M) := by
      rw [Corner.coe_smul, val_smulTopToCorner_apply, coe_smulTopMulRight_apply]
    rw [hxy, ← f.map_smul]
    exact congrArg (fun z ↦ (f z : M))
      (Subtype.ext (by simp [val_smulTopToCorner_apply, mul_assoc, ← mul_assoc e e, he.eq])))
    (hfull ▸ trivial : (1 : A) ∈ TwoSidedIdeal.span {e})
  exact ⟨m, LinearMap.ext fun x ↦ Subtype.ext (by
    simpa only [coe_smulTopActionHom_apply_apply, smulTopMulRight_one, LinearMap.id_coe, id_eq]
      using hm x)⟩

end Unit

/-! ### The equivalence -/

/-- The counit of the corner equivalence, `e Hom_{eAe}(eA, N) ≅ N`, natural in `N`. -/
def cornerCounitIso :
    he.cornerCoindFunctor ⋙ he.cornerFunctor ≅ 𝟭 (ModuleCat.{max u v} he.Corner) :=
  NatIso.ofComponents (fun N ↦ (he.smulTopCoindEquiv N).toModuleIso) fun g ↦
    ModuleCat.hom_ext (LinearMap.ext fun f ↦ LinearMap.congr_fun
      (he.coe_cornerFunctor_map_hom_apply (he.cornerCoindFunctor.map g) f) he.smulTopGen)

@[simp]
theorem cornerCounitIso_hom_app_hom_apply (N : ModuleCat.{max u v} he.Corner)
    (f : ↥(e • (⊤ : Submodule ℤ (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N)))) :
    (ModuleCat.Hom.hom (A := he.cornerFunctor.obj (he.cornerCoindFunctor.obj N)) (B := N)
      (he.cornerCounitIso.hom.app N)) f = f.1 he.smulTopGen :=
  (rfl)

@[simp]
theorem cornerCounitIso_inv_app_hom_apply (N : ModuleCat.{max u v} he.Corner) (n : N) :
    (ModuleCat.Hom.hom (A := N) (B := he.cornerFunctor.obj (he.cornerCoindFunctor.obj N))
      (he.cornerCounitIso.inv.app N)) n = (he.smulTopCoindEquiv N).symm n :=
  (rfl)

/-- The unit of the corner equivalence, `M ≅ Hom_{eAe}(eA, eM)`, natural in `M`, for a full
idempotent `e`. -/
noncomputable def cornerUnitIso (hfull : TwoSidedIdeal.span {e} = ⊤) :
    𝟭 (ModuleCat.{max u v} A) ≅ he.cornerFunctor ⋙ he.cornerCoindFunctor :=
  NatIso.ofComponents (fun M ↦ (LinearEquiv.ofBijective (he.smulTopActionHom M)
    ⟨he.smulTopActionHom_injective hfull, he.smulTopActionHom_surjective hfull⟩).toModuleIso)
    fun f ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ LinearMap.ext fun x ↦ Subtype.ext
      ((he.coe_cornerFunctor_map_hom_apply f _).trans (f.hom.map_smul x.1 m)).symm)

@[simp]
theorem cornerUnitIso_hom_app_hom_apply (hfull : TwoSidedIdeal.span {e} = ⊤)
    (M : ModuleCat.{max u v} A) (m : M) :
    (ModuleCat.Hom.hom (A := M) (B := he.cornerCoindFunctor.obj (he.cornerFunctor.obj M))
      ((he.cornerUnitIso hfull).hom.app M)) m = he.smulTopActionHom M m :=
  (rfl)

/-- **A full idempotent `e` makes the module categories of `A` and of its corner ring `eAe`
equivalent**: the corner functor `M ↦ eM` is an equivalence, with inverse
`N ↦ Hom_{eAe}(eA, N)`, unit `IsIdempotentElem.cornerUnitIso` and counit
`IsIdempotentElem.cornerCounitIso`. -/
@[expose] noncomputable def cornerEquivalence (hfull : TwoSidedIdeal.span {e} = ⊤) :
    ModuleCat.{max u v} A ≌ ModuleCat.{max u v} he.Corner :=
  .mk' he.cornerFunctor he.cornerCoindFunctor (he.cornerUnitIso hfull) he.cornerCounitIso
    fun M ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ Subtype.ext <|
      -- Both sides send `m ∈ eM` to `e • m = m`.
      (congrArg Subtype.val (he.cornerCounitIso_hom_app_hom_apply (he.cornerFunctor.obj M)
        ((he.cornerFunctor.map ((he.cornerUnitIso hfull).hom.app M)).hom m))).trans <|
      (congrArg (fun f : ↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] ↥(e • (⊤ : Submodule ℤ M)) ↦
        (f he.smulTopGen : M))
        ((he.coe_cornerFunctor_map_hom_apply ((he.cornerUnitIso hfull).hom.app M) m).trans
          (he.cornerUnitIso_hom_app_hom_apply hfull M m.1))).trans <|
      (he.coe_smulTopActionHom_apply_apply M m.1 he.smulTopGen).trans <|
      (congrArg (· • m.1) he.coe_smulTopGen).trans <|
      (he.smul_eq_self_of_mem_smul_top m.2).trans
      (congrArg Subtype.val (ModuleCat.id_apply _ m)).symm)

@[simp]
theorem cornerEquivalence_functor (hfull : TwoSidedIdeal.span {e} = ⊤) :
    (he.cornerEquivalence hfull).functor = he.cornerFunctor :=
  (rfl)

@[simp]
theorem cornerEquivalence_inverse (hfull : TwoSidedIdeal.span {e} = ⊤) :
    (he.cornerEquivalence hfull).inverse = he.cornerCoindFunctor :=
  (rfl)

@[simp]
theorem cornerEquivalence_unitIso (hfull : TwoSidedIdeal.span {e} = ⊤) :
    (he.cornerEquivalence hfull).unitIso = he.cornerUnitIso hfull :=
  (rfl)

@[simp]
theorem cornerEquivalence_counitIso (hfull : TwoSidedIdeal.span {e} = ⊤) :
    (he.cornerEquivalence hfull).counitIso = he.cornerCounitIso :=
  (rfl)

section Linear

variable (R : Type w) [CommSemiring R] [Algebra R A]

open scoped ModuleCat.Algebra

/-- The corner functor is linear over any commutative semiring `R` over which `A` is an algebra. -/
instance : he.cornerFunctor.{v}.Linear R where
  map_smul f r := ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext <|
    (he.coe_cornerFunctor_map_hom_apply (r • f) x).trans
      ((congrArg (algebraMap R A r • ·) (he.coe_cornerFunctor_map_hom_apply f x).symm).trans
        (he.coe_algebraMap_corner_smul r ((he.cornerFunctor.map f).hom x)).symm))

/-- **Morita equivalence with the corner ring of a full idempotent**: for a full idempotent `e`
of an `R`-algebra `A`, the corner functor `M ↦ eM` is an `R`-linear equivalence between the
module categories of `A` and of `eAe`. -/
noncomputable def moritaEquivalenceCorner (hfull : TwoSidedIdeal.span {e} = ⊤) :
    MoritaEquivalence R A he.Corner where
  eqv := he.cornerEquivalence.{u, u} hfull
  linear := inferInstanceAs (he.cornerFunctor.{u}.Linear R)

@[simp]
theorem moritaEquivalenceCorner_eqv (hfull : TwoSidedIdeal.span {e} = ⊤) :
    (he.moritaEquivalenceCorner R hfull).eqv = he.cornerEquivalence.{u, u} hfull :=
  (rfl)

/-- **A ring is Morita equivalent to the corner ring of any full idempotent.** -/
theorem isMoritaEquivalent_corner (hfull : TwoSidedIdeal.span {e} = ⊤) :
    IsMoritaEquivalent R A he.Corner :=
  ⟨⟨he.moritaEquivalenceCorner R hfull⟩⟩

end Linear

end IsIdempotentElem
