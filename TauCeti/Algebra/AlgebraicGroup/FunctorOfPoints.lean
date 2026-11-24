/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Convolution groups of algebra homomorphisms out of a Hopf algebra

For an arbitrary Hopf algebra `H` over `R` and a commutative `R`-algebra `A`, the convolution
monoid of `R`-algebra homomorphisms `H →ₐ[R] A` is a **group**, with inverse `f ↦ f ∘ S`,
where `S` is the antipode of `H`. The source `H` need only be a Hopf algebra; it is *not*
required to be commutative.

Mathlib already constructs the convolution `Monoid` on `WithConv (H →ₐ[R] A)` for `H` a
bialgebra (`Mathlib/RingTheory/Bialgebra/Convolution.lean`): multiplication is the
convolution product `(f * g)(h) = ∑ f(h₍₁₎) * g(h₍₂₎)` and the unit is
`algebraMap ∘ ε`.
What is added here is the **inverse** and hence the **group** structure, available exactly
when `H` carries an antipode `S`: the inverse of `f` is `f ∘ S`.
Mathlib's `AlgHom.convInv` and `AlgHom.convGroup` additionally assume that the source is
commutative and the value algebra is a bialgebra; the constructions here remove those requirements.

The construction is functorial in the value algebra: post-composition with an `R`-algebra
homomorphism `φ : A →ₐ[R] B` gives a monoid homomorphism `mapValue φ` between the convolution
monoids, preserving identities and composition. This part needs only the bialgebra structure
on `H` (the convolution monoid), so it lives in its own `Bialgebra` section.

## Application: affine group schemes

When `H` is moreover *commutative*, `Spec H` is an affine group scheme, and the above is
the group structure on its functor of points `A ↦ (H →ₐ[R] A)`, with functoriality in
`A` realizing the `R-Alg ⥤ Grp` structure, where the counit is the identity and `f ∘ S` is
the inverse.

## Main results

* `WithConv.algHom_inv_apply`: pointwise, the convolution inverse of `f` sends `h` to `f (S h)`.
* `AlgHom.convGroupOfSemiring`, `AlgHom.convCommGroupOfSemiring`: for `H` a Hopf algebra over `R`
  and `A` a commutative `R`-algebra, `WithConv (H →ₐ[R] A)` is a group, commutative when `H`
  is cocommutative.
* `AlgHom.mapValue`: post-composition with `φ : A →ₐ[R] B` as a monoid homomorphism of
  convolution monoids, with `AlgHom.ofConv_comp_mapValue` describing it on underlying
  homomorphisms, `AlgHom.mapValue_id`, `AlgHom.mapValue_comp` recording its
  functoriality in the value algebra, `AlgHom.mapValue_injective` recording that it loses no
  information when `φ` does not, and `AlgHom.range_mapValue` describing its image.
* `AlgHom.mem_mrange_mapValue_iff_mapValue_eq_mapValue`: points preserve equalizers; when an
  injective `φ` maps onto the equalizer of `ψ₁` and `ψ₂`, the points coming from the source of `φ`
  are those on which `mapValue ψ₁` and `mapValue ψ₂` agree.
* `AlgHom.mem_mrange_mapValue_iff_mapValue_eq`: when the image of an injective `φ` is the fixed
  ring of an endomorphism `τ`, the points coming from the source of `φ` are those fixed by
  `mapValue τ`.
* `AlgEquiv.mapValueMulEquiv`: an isomorphism of value algebras induces an isomorphism of
  convolution monoids.
* `AlgHom.prodValueMulEquiv`: convolution points valued in `A × B` split multiplicatively
  into factor points.
* `AlgHom.piValueMulEquiv`: points valued in a product of commutative algebras are families of
  points valued in the factors.
* `AlgHom.mapValue_mapValue_ofId`: extending a base-valued point to `A` and then mapping it along
  `φ : A →ₐ[R] B` extends it to `B`.

## References

The convolution monoid on algebra homomorphisms builds on Mathlib's convolution monoid of
Yaël Dillies and Michał Mrugała, and the Hopf convolution algebra developed by
Yaël Dillies, Michał Mrugała, and Yunzhou Xie.
-/

public section

open _root_.Coalgebra HopfAlgebra TensorProduct WithConv

namespace AlgHom

variable {R H A : Type*} [CommSemiring R]

section Hopf

variable [Semiring H] [_root_.HopfAlgebra R H] [CommSemiring A] [Algebra R A]

/-- Precomposition of an algebra homomorphism `f : H →ₐ[R] A` with the antipode `S` of
`H`, as an `R`-algebra homomorphism `H →ₐ[R] A`. Its underlying linear map is
`f.toLinearMap ∘ₗ HopfAlgebra.antipode R`. This is well-defined even when `H` is
noncommutative: `S` is an antihomomorphism (`HopfAlgebra.antipode_mul_antidistrib`), and `A` is
commutative, so `f ∘ S` is a homomorphism. The construction composes
`HopfAlgebra.antipodeAlgHomOp` with `AlgHom.fromOpposite`. -/
noncomputable def antipodeComp (f : H →ₐ[R] A) : H →ₐ[R] A :=
  (f.fromOpposite fun x y => Commute.all (f x) (f y)).comp (HopfAlgebra.antipodeAlgHomOp R H)

/-- Evaluation of `antipodeComp f` at an element `h : H` is `f (S h)`. -/
@[simp]
lemma antipodeComp_apply (f : H →ₐ[R] A) (h : H) :
    antipodeComp f h = f (antipode R h) := (rfl)

/-- The underlying linear map of `antipodeComp f` is `f.toLinearMap ∘ₗ antipode R`. -/
@[simp]
lemma toLinearMap_antipodeComp (f : H →ₐ[R] A) :
    (antipodeComp f).toLinearMap = f.toLinearMap ∘ₗ antipode R :=
  LinearMap.ext (antipodeComp_apply f)

/-- The convolution inverse of an `R`-algebra homomorphism `f : H →ₐ[R] A` out of a Hopf
algebra is `f ∘ S`, where `S` is the antipode. The source need only be a semiring, so it can be
noncommutative, and the commutative value algebra `A` need not be a bialgebra. -/
noncomputable instance convInvOfSemiring : Inv (WithConv (H →ₐ[R] A)) where
  inv f := toConv (antipodeComp f.ofConv)

/-- The convolution inverse of `f` is `f ∘ S`, where `S` is the antipode:
`f⁻¹ = toConv (antipodeComp f.ofConv)`. -/
lemma _root_.WithConv.algHom_inv_def (f : WithConv (H →ₐ[R] A)) :
    f⁻¹ = toConv (antipodeComp f.ofConv) := rfl

/-- Pointwise, the convolution inverse of `f` sends `h` to `f (S h)`, where `S` is the
antipode. -/
@[simp]
lemma _root_.WithConv.algHom_inv_apply (f : WithConv (H →ₐ[R] A)) (h : H) :
    f⁻¹ h = f.ofConv (antipode R h) := by
  -- `algHom_inv_def` exposes `toConv (antipodeComp f.ofConv)`; under the coercion from `WithConv`,
  -- `(toConv g) h` evaluates as `g h`.
  rw [WithConv.algHom_inv_def, AlgHom.antipodeComp_apply]

/-- For a Hopf algebra `H` over `R` and a commutative `R`-algebra `A`, the convolution
monoid of `R`-algebra homomorphisms `H →ₐ[R] A` is a group, with inverse `f ↦ f ∘ S`. When
`H` is moreover commutative, `Spec H` is an affine group scheme and this is the group
structure on its functor of points evaluated at `A`. -/
noncomputable instance convGroupOfSemiring : Group (WithConv (H →ₐ[R] A)) where
  inv_mul_cancel f := by
    -- Pass to linear maps to use the Sweedler formula for convolution.
    refine WithConv.ofConv_injective (AlgHom.toLinearMap_injective (WithConv.toConv_injective ?_))
    rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne, algHom_inv_def, toConv_ofConv,
      AlgHom.toLinearMap_antipodeComp]
    ext h
    rw [(ℛ R h).convMul_apply]
    simp only [LinearMap.comp_apply, AlgHom.coe_toLinearMap, LinearMap.convOne_apply,
      ← map_mul, ← map_sum, sum_antipode_mul_eq_algebraMap_counit, AlgHom.commutes]

end Hopf

section Bialgebra

variable [Semiring H] [_root_.Bialgebra R H] [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Functoriality of `A ↦ (H →ₐ[R] A)` in the value algebra: an `R`-algebra homomorphism
`φ : A →ₐ[R] B` induces, by post-composition, a monoid homomorphism between the convolution
monoids. This needs only the bialgebra structure on `H`. When `H` is moreover a Hopf algebra,
these convolution monoids are the convolution groups (`convGroupOfSemiring`); a `MonoidHom`
between groups is automatically a group homomorphism, so no separate construction is needed
there. -/
noncomputable def mapValue (φ : A →ₐ[R] B) :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] B) where
  toFun f := toConv (φ.comp f.ofConv)
  map_one' := by simp [AlgHom.convOne_def, ← AlgHom.comp_assoc]
  map_mul' f g := by simp [AlgHom.comp_convMul_distrib]

/-- `mapValue φ` acts pointwise by post-composition: `(mapValue φ f) = φ ∘ f`. -/
@[simp]
lemma mapValue_apply (φ : A →ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    mapValue φ f = toConv (φ.comp f.ofConv) := (rfl)

/-- On underlying homomorphisms, `mapValue φ` is post-composition with `φ`, as functions. -/
lemma ofConv_comp_mapValue (φ : A →ₐ[R] B) :
    ofConv ∘ mapValue (H := H) φ = (fun f : H →ₐ[R] A ↦ φ.comp f) ∘ ofConv := by
  ext f h
  simp

/-- `mapValue` preserves the identity: `mapValue (𝟙 A)` is the identity monoid homomorphism. -/
@[simp]
lemma mapValue_id :
    mapValue (H := H) (AlgHom.id R A) = MonoidHom.id (WithConv (H →ₐ[R] A)) := by
  ext f : 1
  simp

/-- An injective homomorphism of value algebras induces an injective map on points: a point is
determined by its values. -/
lemma mapValue_injective {φ : A →ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapValue (H := H) φ) := by
  intro f g hfg
  rw [mapValue_apply, mapValue_apply] at hfg
  refine WithConv.ofConv_injective (AlgHom.ext fun h => hφ ?_)
  exact DFunLike.congr_fun (WithConv.toConv_injective hfg) h

/-- The image of `mapValue φ` consists of the points whose underlying homomorphisms factor
through `φ`. -/
lemma range_mapValue (φ : A →ₐ[R] B) :
    Set.range (mapValue (H := H) φ) = ofConv ⁻¹' Set.range fun f : H →ₐ[R] A ↦ φ.comp f := by
  ext f
  refine ⟨?_, fun ⟨g, hg⟩ => ⟨toConv g, ?_⟩⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.ofConv, by simp⟩
  · simp [hg]

/-- For an injective homomorphism `φ` of value algebras, a point comes from a point valued in the
source of `φ` exactly when each of its values lies in the range of `φ`. -/
lemma mem_mrange_mapValue_iff {φ : A →ₐ[R] B} (hφ : Function.Injective φ)
    {f : WithConv (H →ₐ[R] B)} :
    f ∈ MonoidHom.mrange (mapValue (H := H) φ) ↔ ∀ h, f.ofConv h ∈ φ.range := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨g, rfl⟩ h
    rw [mapValue_apply, ofConv_toConv]
    exact φ.mem_range_self _
  · -- The values lie in the range of `φ`; invert `φ` there.
    refine ⟨toConv ((AlgEquiv.ofInjective φ hφ).symm.toAlgHom.comp (f.ofConv.codRestrict _ hf)),
      WithConv.ofConv_injective (AlgHom.ext fun h => ?_)⟩
    simp [← AlgEquiv.ofInjective_apply _ hφ]

variable {C : Type*} [CommSemiring C] [Algebra R C]

/-- **Points preserve equalizers.** When an injective `φ : A →ₐ[R] B` maps onto the equalizer of
`ψ₁ ψ₂ : B →ₐ[R] C`, a point comes from a point valued in `A` exactly when its two images under
`mapValue ψ₁` and `mapValue ψ₂` agree. -/
lemma mem_mrange_mapValue_iff_mapValue_eq_mapValue {φ : A →ₐ[R] B} (hφ : Function.Injective φ)
    {ψ₁ ψ₂ : B →ₐ[R] C} (hψ : {b | ψ₁ b = ψ₂ b} = Set.range φ) {f : WithConv (H →ₐ[R] B)} :
    f ∈ MonoidHom.mrange (mapValue (H := H) φ) ↔ mapValue ψ₁ f = mapValue ψ₂ f := by
  simp [mem_mrange_mapValue_iff hφ, AlgHom.ext_iff, ← SetLike.mem_coe, ← hψ]

/-- When the image of an injective `φ : A →ₐ[R] B` is exactly the set of fixed points of an
endomorphism `τ` of `B`, a point comes from a point valued in `A` exactly when it is fixed by
`mapValue τ`: descent of points along an extension of coefficients whose fixed ring is the base. -/
lemma mem_mrange_mapValue_iff_mapValue_eq {φ : A →ₐ[R] B} (hφ : Function.Injective φ)
    {τ : B →ₐ[R] B} (hτ : {b | τ b = b} = Set.range φ) {f : WithConv (H →ₐ[R] B)} :
    f ∈ MonoidHom.mrange (mapValue (H := H) φ) ↔ mapValue τ f = f := by
  rw [mem_mrange_mapValue_iff_mapValue_eq_mapValue hφ (ψ₂ := AlgHom.id R B) hτ, mapValue_id,
    MonoidHom.id_apply]

/-- `mapValue` preserves composition: `mapValue (ψ ∘ φ) = mapValue ψ ∘ mapValue φ`. -/
lemma mapValue_comp (ψ : B →ₐ[R] C) (φ : A →ₐ[R] B) :
    mapValue (H := H) (ψ.comp φ) = (mapValue ψ).comp (mapValue φ) := by
  ext f : 1
  simp [AlgHom.comp_assoc]

/-- Extending a base-valued point to `A` and then mapping it along `φ : A →ₐ[R] B` extends it to
`B`. -/
lemma mapValue_mapValue_ofId (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] R)) :
    mapValue φ (mapValue (Algebra.ofId R A) g) = mapValue (Algebra.ofId R B) g := by
  rw [← MonoidHom.comp_apply, ← mapValue_comp, Algebra.comp_ofId]

/-- An isomorphism `e : A ≃ₐ[R] B` of value algebras induces, by post-composition, an
isomorphism of convolution monoids, with inverse induced by `e.symm`. -/
noncomputable def _root_.AlgEquiv.mapValueMulEquiv (e : A ≃ₐ[R] B) :
    WithConv (H →ₐ[R] A) ≃* WithConv (H →ₐ[R] B) where
  toFun := mapValue (e : A →ₐ[R] B)
  invFun := mapValue (e.symm : B →ₐ[R] A)
  left_inv f := by
    rw [← MonoidHom.comp_apply, ← mapValue_comp, AlgEquiv.symm_comp, mapValue_id,
      MonoidHom.id_apply]
  right_inv f := by
    rw [← MonoidHom.comp_apply, ← mapValue_comp, AlgEquiv.comp_symm, mapValue_id,
      MonoidHom.id_apply]
  map_mul' := map_mul _

@[simp]
lemma _root_.AlgEquiv.mapValueMulEquiv_apply (e : A ≃ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    e.mapValueMulEquiv f = mapValue (e : A →ₐ[R] B) f := (rfl)

@[simp]
lemma _root_.AlgEquiv.mapValueMulEquiv_symm_apply (e : A ≃ₐ[R] B) (f : WithConv (H →ₐ[R] B)) :
    e.mapValueMulEquiv.symm f = mapValue (e.symm : B →ₐ[R] A) f := (rfl)

end Bialgebra

section Pi

variable [Semiring H] [_root_.Bialgebra R H] {ι : Type*} {B : ι → Type*}
  [∀ i, CommSemiring (B i)] [∀ i, Algebra R (B i)]

/-- **Points valued in a product.** A point valued in a product `∀ i, B i` of commutative
algebras is the family of its components, as an isomorphism of convolution monoids. Its inverse
is Mathlib's `AlgHom.pi`. -/
noncomputable def piValueMulEquiv :
    WithConv (H →ₐ[R] ∀ i, B i) ≃* ∀ i, WithConv (H →ₐ[R] B i) where
  toFun f i := mapValue (Pi.evalAlgHom R B i) f
  invFun g := toConv (AlgHom.pi fun i ↦ (g i).ofConv)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' f g := funext fun i ↦ map_mul (mapValue (Pi.evalAlgHom R B i)) f g

@[simp]
lemma piValueMulEquiv_apply (f : WithConv (H →ₐ[R] ∀ i, B i)) (i : ι) (h : H) :
    (piValueMulEquiv f i).ofConv h = f.ofConv h i := (rfl)

@[simp]
lemma piValueMulEquiv_symm_apply (g : ∀ i, WithConv (H →ₐ[R] B i)) (h : H) (i : ι) :
    (piValueMulEquiv.symm g).ofConv h i = (g i).ofConv h := (rfl)

end Pi

section BialgebraProd

variable [Semiring H] [_root_.Bialgebra R H] [CommSemiring A] [Algebra R A]
variable {B C : Type*} [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C]

/-- Convolution points of a bialgebra `H` valued in `A × B` split multiplicatively into `A`-valued
and `B`-valued points via the coordinate projections. -/
noncomputable def prodValueMulEquiv :
    WithConv (H →ₐ[R] A × B) ≃* WithConv (H →ₐ[R] A) × WithConv (H →ₐ[R] B) where
  toFun x := (mapValue (AlgHom.fst R A B) x, mapValue (AlgHom.snd R A B) x)
  invFun p := toConv (p.1.ofConv.prod p.2.ofConv)
  left_inv x := WithConv.ext <| by ext h <;> simp
  right_inv p := by ext h <;> simp
  map_mul' := ((mapValue (H := H) (AlgHom.fst R A B)).prod
    (mapValue (H := H) (AlgHom.snd R A B))).map_mul

/-- The first component of `prodValueMulEquiv` is induced by `AlgHom.fst`. -/
@[simp]
theorem prodValueMulEquiv_apply_fst (x : WithConv (H →ₐ[R] A × B)) :
    (prodValueMulEquiv x).1 = mapValue (AlgHom.fst R A B) x := (rfl)

/-- The second component of `prodValueMulEquiv` is induced by `AlgHom.snd`. -/
@[simp]
theorem prodValueMulEquiv_apply_snd (x : WithConv (H →ₐ[R] A × B)) :
    (prodValueMulEquiv x).2 = mapValue (AlgHom.snd R A B) x := (rfl)

/-- The inverse of `prodValueMulEquiv` assembles two factor points via `AlgHom.prod`. -/
@[simp]
theorem ofConv_prodValueMulEquiv_symm (p : WithConv (H →ₐ[R] A) × WithConv (H →ₐ[R] B)) :
    ((prodValueMulEquiv (R := R) (H := H) (A := A) (B := B)).symm p).ofConv =
      p.1.ofConv.prod p.2.ofConv := (rfl)

/-- Evaluating `prodValueMulEquiv.symm p` at `h : H` pairs the two factor evaluations. -/
theorem prodValueMulEquiv_symm_apply_ofConv
    (p : WithConv (H →ₐ[R] A) × WithConv (H →ₐ[R] B)) (h : H) :
    ((prodValueMulEquiv (R := R) (H := H) (A := A) (B := B)).symm p).ofConv h =
      (p.1.ofConv h, p.2.ofConv h) := (rfl)

/-- Projecting `prodValueMulEquiv.symm p` onto the first factor recovers `p.1`. -/
theorem mapValue_fst_prodValueMulEquiv_symm (p : WithConv (H →ₐ[R] A) × WithConv (H →ₐ[R] B)) :
    mapValue (AlgHom.fst R A B) (prodValueMulEquiv.symm p) = p.1 := by
  simpa only [prodValueMulEquiv_apply_fst] using
    congrArg Prod.fst (prodValueMulEquiv.apply_symm_apply p)

/-- Projecting `prodValueMulEquiv.symm p` onto the second factor recovers `p.2`. -/
theorem mapValue_snd_prodValueMulEquiv_symm (p : WithConv (H →ₐ[R] A) × WithConv (H →ₐ[R] B)) :
    mapValue (AlgHom.snd R A B) (prodValueMulEquiv.symm p) = p.2 := by
  simpa only [prodValueMulEquiv_apply_snd] using
    congrArg Prod.snd (prodValueMulEquiv.apply_symm_apply p)

/-- `prodValueMulEquiv` sends `mapValue (φ.prod ψ) x` to `(mapValue φ x, mapValue ψ x)`. -/
theorem prodValueMulEquiv_mapValue_prod (φ : C →ₐ[R] A) (ψ : C →ₐ[R] B)
    (x : WithConv (H →ₐ[R] C)) :
    prodValueMulEquiv (mapValue (φ.prod ψ) x) = (mapValue φ x, mapValue ψ x) := by ext <;> simp

end BialgebraProd
section CommHopf

variable [Semiring H] [_root_.HopfAlgebra R H] [IsCocomm R H] [CommSemiring A] [Algebra R A]

/-- When `H` is moreover cocommutative, the convolution group of `R`-algebra homomorphisms
`H →ₐ[R] A` is abelian. -/
noncomputable instance convCommGroupOfSemiring : CommGroup (WithConv (H →ₐ[R] A)) where
  mul_comm := mul_comm

end CommHopf

end AlgHom
