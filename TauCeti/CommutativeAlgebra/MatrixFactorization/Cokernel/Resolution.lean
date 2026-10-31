/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.GorensteinProjective
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Matrix factorizations from projective resolutions of length one

Let `w` be an element of a commutative ring `S` and put `R = S/(w)`. Eisenbud's construction
turns a projective resolution of length one over `S`

`0 → P --f--> Q --g--> M → 0`

of an `R`-module `M` into a matrix factorization of `w`. Since `w` kills `M`, multiplication by
`w` on `Q` lands in the image of the injective map `f`, so it factors uniquely as `f ∘ d₁`; then
`(P --f--> Q --d₁--> P)` is a matrix factorization of `w`
(`TauCeti.MatrixFactorization.ofInjective`), and the cokernel of its reduction modulo `w` is `M`
(`TauCeti.MatrixFactorization.quotientCokernelIsoOfExact`).

Conversely, the cokernel of the reduction modulo `w` of any finite-projective matrix factorization
`X` is the quotient of the odd component `X₁` by the image of `d₀`
(`TauCeti.MatrixFactorization.exact_d₀_quotientCokernelπ`), and `d₀` is injective when `w` is a
non-zero-divisor. So for a non-zero-divisor `w`, the `R`-modules arising as such cokernels are
exactly those with a resolution of length one by finitely generated projective `S`-modules
(`TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff`). Over a Noetherian ring `S`, these
are exactly the finitely generated `R`-modules of projective dimension at most one over `S`
(`TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE`). In
particular every such module is Gorenstein-projective over `R`
(`TauCeti.MatrixFactorization.isGorensteinProjective_of_exact`).

No regularity hypothesis is used. When `S` has finite global dimension, every
Gorenstein-projective `R`-module is a high syzygy and hence has projective dimension at most one
over `S`; that step, which gives essential surjectivity of the cokernel functor onto the stable
category of Gorenstein-projective `R`-modules, is not made here.

## Main definitions

* `TauCeti.MatrixFactorization.ofInjective`: the matrix factorization `P --f--> Q --d₁--> P` of an
  injective map `f` between finitely generated projective modules whose cokernel is killed by `w`.
* `TauCeti.MatrixFactorization.quotientCokernelπ`: the surjection `y ↦ [1 ⊗ y]` from the odd
  component onto the cokernel of the reduction modulo `w`.
* `TauCeti.MatrixFactorization.quotientCokernelIsoOfExact`: the cokernel of the reduction of the
  matrix factorization of a resolution `0 → P → Q → M → 0` is `M`.

## Main results

* `TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff`: for a non-zero-divisor `w`, an
  `S/(w)`-module is the cokernel of the reduction of a matrix factorization exactly when it has a
  resolution of length one by finitely generated projective `S`-modules.
* `TauCeti.MatrixFactorization.quotientGorensteinProjectiveCokernel_essImage_iff`: the same
  description of the essential image of the cokernel functor to Gorenstein-projective modules.
* `TauCeti.MatrixFactorization.exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE`: over a
  Noetherian ring, a finitely generated `S/(w)`-module is such a cokernel exactly when its
  projective dimension over `S` is at most one.
* `TauCeti.MatrixFactorization.isGorensteinProjective_of_exact` and
  `TauCeti.MatrixFactorization.isGorensteinProjective_of_hasProjectiveDimensionLE`: such modules
  are Gorenstein-projective over `S/(w)`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5: the matrix factorization
  attached to an `S`-free resolution of length one of a module over `S/(w)`.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings

variable {S : Type u} [CommRing S] {w : S}

/-! ### The matrix factorization of an injective map -/

section OfInjective

variable {P Q : FGModuleCat.{u} S} [Module.Projective S P] [Module.Projective S Q]
  (f : P ⟶ Q) (hf : Function.Injective f.hom.hom)
  (hw : ∀ y : Q, w • y ∈ LinearMap.range f.hom.hom)

/-- **Eisenbud's matrix factorization.** An injective map `f : P → Q` of finitely generated
projective modules whose cokernel is killed by `w` is the even-to-odd differential of a unique
matrix factorization `P --f--> Q --d₁--> P` of `w`: multiplication by `w` on `Q` lands in the
image of `f`, and `d₁` is its quotient by `f`
(`TauCeti.MatrixFactorization.ofInjective_obj_d₁_eq_iff`). -/
@[expose] def ofInjective : MatrixFactorization S w :=
  let d₁ : Q ⟶ P := ObjectProperty.homMk <| ModuleCat.ofHom <|
    (LinearEquiv.ofInjective f.hom.hom hf).symm.toLinearMap ∘ₗ
      (w • LinearMap.id : Q →ₗ[S] Q).codRestrict _ hw
  have hd₁ (y : Q) : f.hom.hom (d₁.hom.hom y) = w • y := by
    simp [d₁]
  ofCurvedDuplex
    { X₀ := P
      X₁ := Q
      d₀ := f
      d₁ := d₁
      d₀_comp_d₁ := by
        ext x
        apply hf
        simp [hd₁]
      d₁_comp_d₀ := by
        ext y
        simp [hd₁] }
    ‹_› ‹_›

@[simp] theorem ofInjective_obj_X₀ : (ofInjective f hf hw).obj.X₀ = P := rfl

@[simp] theorem ofInjective_obj_X₁ : (ofInjective f hf hw).obj.X₁ = Q := rfl

@[simp] theorem ofInjective_obj_d₀ : (ofInjective f hf hw).obj.d₀ = f := rfl

/-- The odd-to-even differential of `ofInjective` is characterized by `f ∘ d₁ = w`. -/
theorem ofInjective_obj_d₁_eq_iff (d : Q ⟶ P) :
    (ofInjective f hf hw).obj.d₁ = d ↔ d ≫ f = w • 𝟙 Q := by
  refine ⟨fun h ↦ h ▸ (ofInjective f hf hw).obj.d₁_comp_d₀, fun h ↦ ?_⟩
  ext y
  apply hf
  have hd : f.hom.hom (d.hom.hom y) = w • y := congrArg (fun k ↦ k.hom.hom y) h
  exact (d₁_comp_d₀_apply (ofInjective f hf hw) y).trans hd.symm

end OfInjective

/-! ### The cokernel of the reduction as a quotient of the odd component -/

/-- The `S`-linear surjection `y ↦ [1 ⊗ y]` from the odd component onto the cokernel of the
reduction modulo `w`, viewed as an `S`-module. Its kernel is the image of `d₀`
(`TauCeti.MatrixFactorization.exact_d₀_quotientCokernelπ`). -/
def quotientCokernelπ (X : MatrixFactorization S w) :
    X.obj.X₁.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj
      (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  (ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).unit.app
      X.obj.X₁.obj ≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map
      (cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X))

/-- On elements, `quotientCokernelπ` sends `y` to the class of `1 ⊗ y`. -/
theorem quotientCokernelπ_apply (X : MatrixFactorization S w) (y : X.obj.X₁) :
    quotientCokernelπ X y =
      cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)
        ((1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, Ideal.Quotient.mk (Ideal.span {w})] y) :=
  (rfl)

/-- Every element of the cokernel of the reduction is the class of `1 ⊗ y` for some `y`. -/
theorem quotientCokernelπ_surjective (X : MatrixFactorization S w) :
    Function.Surjective (quotientCokernelπ X) := by
  intro m
  obtain ⟨z, rfl⟩ :=
    cokernelπ_surjective ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X) m
  obtain ⟨y, rfl⟩ := TensorProduct.exists_one_tmul_eq (Ideal.span {w}) z
  exact ⟨y, quotientCokernelπ_apply X y⟩

/-- The kernel of `y ↦ [1 ⊗ y]` is the image of `d₀`: if `1 ⊗ y = d₀' (1 ⊗ x)`, then
`y - d₀ x = w y' = d₀ (d₁ y')`. -/
theorem quotientCokernelπ_eq_zero_iff (X : MatrixFactorization S w) (y : X.obj.X₁) :
    quotientCokernelπ X y = 0 ↔ y ∈ LinearMap.range X.obj.d₀.hom.hom := by
  rw [quotientCokernelπ_apply]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (exact_d₀_cokernelπ _ _).1 h
    obtain ⟨x, rfl⟩ := TensorProduct.exists_one_tmul_eq (M := X.obj.X₀) (Ideal.span {w}) z
    have : (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] (y - X.obj.d₀.hom.hom x) = 0 := by
      rw [TensorProduct.tmul_sub]
      exact sub_eq_zero.2 hz.symm
    obtain ⟨y', hy'⟩ := (TensorProduct.one_tmul_eq_zero_iff_exists_smul_eq w _).1 this
    refine ⟨x + X.obj.d₁.hom.hom y', ?_⟩
    rw [map_add, d₁_comp_d₀_apply, hy', add_sub_cancel]
  · rintro ⟨x, rfl⟩
    exact (exact_d₀_cokernelπ _ _).2
      ⟨(1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, Ideal.Quotient.mk (Ideal.span {w})] x, rfl⟩

/-- The even differential and `y ↦ [1 ⊗ y]` form an exact pair: the cokernel of the reduction
modulo `w` is the cokernel of `d₀` over `S`. -/
theorem exact_d₀_quotientCokernelπ (X : MatrixFactorization S w) :
    Function.Exact X.obj.d₀.hom.hom (quotientCokernelπ X).hom :=
  fun y ↦ (quotientCokernelπ_eq_zero_iff X y).trans Iff.rfl

/-- `y ↦ [1 ⊗ y]` is natural with respect to morphisms of matrix factorizations. -/
theorem quotientCokernelπ_naturality_apply {X Y : MatrixFactorization S w} (g : X ⟶ Y)
    (y : X.obj.X₁) :
    (cokernelFunctor.map ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g)).hom
        (quotientCokernelπ X y) = quotientCokernelπ Y (g.hom.f₁.hom y) :=
  cokernelπ_naturality_apply ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g) _

/-! ### The cokernel of a resolution of length one -/

section Resolution

variable {P Q : FGModuleCat.{u} S} {M : ModuleCat.{u} (S ⧸ Ideal.span {w})}
  {f : P ⟶ Q} {g : Q.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M}

/-- If `P --f--> Q --g--> M` is exact and `M` is a module over `S/(w)`, then `w` kills the
cokernel of `f`. -/
theorem smul_mem_range_of_exact (hfg : Function.Exact f.hom.hom g.hom) (y : Q) :
    w • y ∈ LinearMap.range f.hom.hom := by
  refine (hfg _).1 ?_
  rw [map_smul, ModuleCat.restrictScalars.smul_def, Ideal.Quotient.mk_singleton_self, zero_smul]
  rfl

variable [Module.Projective S P] [Module.Projective S Q]

/-- The map from the cokernel of the reduction of `ofInjective f` to `M` induced by `g`: the
adjoint `S/(w) ⊗ Q → M` of `g` kills the reduction of `f`. -/
private def quotientCokernelDesc (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) :
    (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
      (ofInjective f hf (smul_mem_range_of_exact hfg)))).obj ⟶ M :=
  (isColimitCokernelπ _).desc (CokernelCofork.ofπ
    (((ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv
      _ _).symm g) (by
      have hfg₀ : f.hom ≫ g = 0 := by
        ext y
        exact hfg.apply_apply_eq_zero y
      -- The reduction of `f` is its scalar extension, and the adjunction is natural.
      change (ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {w}))).map f.hom ≫ _ = 0
      rw [← Adjunction.homEquiv_naturality_left_symm, hfg₀, Equiv.symm_apply_eq,
        Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]))

private theorem cokernelπ_quotientCokernelDesc (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) :
    cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
        (ofInjective f hf (smul_mem_range_of_exact hfg))) ≫ quotientCokernelDesc hf hfg =
      ((ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv
        _ _).symm g :=
  Cofork.IsColimit.π_desc (isColimitCokernelπ _)

/-- Composed with `y ↦ [1 ⊗ y]`, the map induced by `g` is `g`. -/
private theorem quotientCokernelπ_comp_quotientCokernelDesc (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) :
    quotientCokernelπ (ofInjective f hf (smul_mem_range_of_exact hfg)) ≫
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map
        (quotientCokernelDesc hf hfg) = g := by
  -- The class of `y` is the image of `1 ⊗ y`, on which the adjoint of `g` takes the value `g y`.
  ext y
  exact (ConcreteCategory.congr_hom (cokernelπ_quotientCokernelDesc hf hfg) _).trans
    (congrArg (fun k ↦ k.hom y)
      (((ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv
        _ _).apply_symm_apply g))

/-- **The cokernel of Eisenbud's matrix factorization.** If `0 → P --f--> Q --g--> M → 0` is a
resolution of an `S/(w)`-module `M` by finitely generated projective `S`-modules, then the
cokernel of the reduction modulo `w` of the matrix factorization `ofInjective f` is `M`. The
isomorphism sends the class of `1 ⊗ y` to `g y`. -/
def quotientCokernelIsoOfExact (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) (hg : Function.Surjective g) :
    (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
      (ofInjective f hf (smul_mem_range_of_exact hfg)))).obj ≅ M :=
  have h := quotientCokernelπ_comp_quotientCokernelDesc hf hfg
  (LinearEquiv.ofBijective (quotientCokernelDesc hf hfg).hom
    ⟨fun a b hab ↦ by
      -- Both classes lift to `Q`, where `g` identifies them modulo the image of `f`.
      obtain ⟨a, rfl⟩ := quotientCokernelπ_surjective (ofInjective f hf _) a
      obtain ⟨b, rfl⟩ := quotientCokernelπ_surjective (ofInjective f hf _) b
      have hab' : g.hom a = g.hom b :=
        (ConcreteCategory.congr_hom h a).symm.trans (hab.trans (ConcreteCategory.congr_hom h b))
      have hπ : quotientCokernelπ (ofInjective f hf (smul_mem_range_of_exact hfg)) (a - b) = 0 :=
        (quotientCokernelπ_eq_zero_iff _ _).2
          ((hfg _).1 ((map_sub g.hom a b).trans (sub_eq_zero.2 hab')))
      rw [map_sub, sub_eq_zero] at hπ
      exact hπ,
    fun m ↦ by
      obtain ⟨y, rfl⟩ := hg m
      exact ⟨_, ConcreteCategory.congr_hom h y⟩⟩).toModuleIso

/-- The isomorphism `quotientCokernelIsoOfExact` sends the class of `1 ⊗ y` to `g y`. -/
theorem quotientCokernelIsoOfExact_hom_quotientCokernelπ (hf : Function.Injective f.hom.hom)
    (hfg : Function.Exact f.hom.hom g.hom) (hg : Function.Surjective g) (y : Q) :
    (quotientCokernelIsoOfExact hf hfg hg).hom.hom
      (quotientCokernelπ (ofInjective f hf (smul_mem_range_of_exact hfg)) y) = g y :=
  ConcreteCategory.congr_hom (quotientCokernelπ_comp_quotientCokernelDesc hf hfg) y

/-- **Eisenbud's modules are Gorenstein-projective.** For a non-zero-divisor `w`, an
`S/(w)`-module with a resolution `0 → P → Q → M → 0` of length one by finitely generated
projective `S`-modules is Gorenstein-projective over `S/(w)`. -/
theorem isGorensteinProjective_of_exact (hw : w ∈ nonZeroDivisors S)
    (hf : Function.Injective f.hom.hom) (hfg : Function.Exact f.hom.hom g.hom)
    (hg : Function.Surjective g) : IsGorensteinProjective (S ⧸ Ideal.span {w}) M :=
  (IsGorensteinProjective _).prop_of_iso (quotientCokernelIsoOfExact hf hfg hg)
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw _)

end Resolution

/-! ### Cokernels of reductions are the modules with resolutions of length one -/

/-- **Cokernels of matrix factorizations.** For a non-zero-divisor `w`, an `S/(w)`-module `M` is
isomorphic to the cokernel of the reduction modulo `w` of a finite-projective matrix factorization
of `w` exactly when it has a resolution `0 → P → Q → M → 0` of length one by finitely generated
projective `S`-modules. -/
theorem exists_quotientCokernel_iso_iff (hw : w ∈ nonZeroDivisors S)
    (M : ModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (∃ X : MatrixFactorization S w, Nonempty
      ((cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
        X)).obj ≅ M)) ↔
      ∃ (P Q : FGModuleCat.{u} S), Module.Projective S P ∧ Module.Projective S Q ∧
        ∃ (f : P ⟶ Q)
          (g : Q.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M),
          Function.Injective f.hom.hom ∧ Function.Exact f.hom.hom g.hom ∧
            Function.Surjective g := by
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    let e' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).mapIso e
    refine ⟨X.obj.X₀, X.obj.X₁, inferInstance, inferInstance, X.obj.d₀,
      quotientCokernelπ X ≫ e'.hom, d₀_injective hw X, ?_, ?_⟩
    · exact (exact_d₀_quotientCokernelπ X).comp_injective _
        ((ConcreteCategory.bijective_of_isIso e'.hom).1) (by simp)
    · exact (ConcreteCategory.bijective_of_isIso e'.hom).2.comp
        (quotientCokernelπ_surjective X)
  · rintro ⟨P, Q, _, _, f, g, hf, hfg, hg⟩
    exact ⟨_, ⟨quotientCokernelIsoOfExact hf hfg hg⟩⟩

/-- **The essential image of the Gorenstein-projective cokernel functor.** For a non-zero-divisor
`w`, a Gorenstein-projective `S/(w)`-module is isomorphic to the cokernel of the reduction of a
finite-projective matrix factorization exactly when it has a resolution of length one by finitely
generated projective `S`-modules. -/
theorem quotientGorensteinProjectiveCokernel_essImage_iff (hw : w ∈ nonZeroDivisors S)
    (M : GorensteinProjectiveModuleCat.{u} (S ⧸ Ideal.span {w})) :
    (quotientGorensteinProjectiveCokernel hw).essImage M ↔
      ∃ (P Q : FGModuleCat.{u} S), Module.Projective S P ∧ Module.Projective S Q ∧
        ∃ (f : P ⟶ Q)
          (g : Q.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M.obj),
          Function.Injective f.hom.hom ∧ Function.Exact f.hom.hom g.hom ∧
            Function.Surjective g := by
  rw [← exists_quotientCokernel_iso_iff hw]
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, ⟨eqToIso (quotientGorensteinProjectiveCokernel_obj_obj hw X).symm ≪≫
      (IsGorensteinProjective _).ι.mapIso e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, ⟨ObjectProperty.isoMk _
      (eqToIso (quotientGorensteinProjectiveCokernel_obj_obj hw X) ≪≫ e)⟩⟩

/-- **Cokernels of matrix factorizations over a Noetherian ring.** For a non-zero-divisor `w` of a
Noetherian ring `S`, a finitely generated `S/(w)`-module is isomorphic to the cokernel of the
reduction modulo `w` of a finite-projective matrix factorization of `w` exactly when its
projective dimension over `S` is at most one. -/
theorem exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE [IsNoetherianRing S]
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    (∃ X : MatrixFactorization S w, Nonempty
      ((cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj
        X)).obj ≅ M)) ↔
      HasProjectiveDimensionLE
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1 := by
  rw [exists_quotientCokernel_iso_iff hw]
  constructor
  · rintro ⟨P, Q, _, _, f, g, hf, hfg, hg⟩
    -- The resolution is a short exact sequence with projective first and second terms.
    have hS : (ShortComplex.mk f.hom g (by ext y; exact hfg.apply_apply_eq_zero y)).ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg
        mono_f := (ModuleCat.mono_iff_injective _).2 hf
        epi_g := (ModuleCat.epi_iff_surjective _).2 hg }
    have : Projective P.obj := (IsProjective.iff_projective P).1 ‹_›
    have : Projective Q.obj := (IsProjective.iff_projective Q).1 ‹_›
    exact hS.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance
  · intro hM
    let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
    have : Module.Finite S M' := ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
      Ideal.Quotient.mk_surjective M).2 ‹_›
    -- Present `M` over `S` by a finite free module; the kernel is finitely generated because
    -- `S` is Noetherian, and projective because `M` has projective dimension at most one.
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' S M'
    have hK : Module.Projective S (LinearMap.ker π) := by
      rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLE_zero]
      exact (π.hasProjectiveDimensionLE_succ_iff_ker hπ 0).1 hM
    refine ⟨FGModuleCat.of S (LinearMap.ker π), FGModuleCat.of S (Fin n → S), hK,
      inferInstanceAs (Module.Projective S (Fin n → S)),
      ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker π).subtype),
      ModuleCat.ofHom (Y := M') π,
      Subtype.val_injective, LinearMap.exact_subtype_ker_map π, hπ⟩

/-- For a non-zero-divisor `w` of a Noetherian ring `S`, a finitely generated `S/(w)`-module of
projective dimension at most one over `S` is Gorenstein-projective over `S/(w)`. -/
theorem isGorensteinProjective_of_hasProjectiveDimensionLE [IsNoetherianRing S]
    (hw : w ∈ nonZeroDivisors S) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M]
    (hM : HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M) 1) :
    IsGorensteinProjective (S ⧸ Ideal.span {w}) M := by
  obtain ⟨X, ⟨e⟩⟩ := (exists_quotientCokernel_iso_iff_hasProjectiveDimensionLE hw M).2 hM
  exact (IsGorensteinProjective _).prop_of_iso e
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw X)

end TauCeti.MatrixFactorization
