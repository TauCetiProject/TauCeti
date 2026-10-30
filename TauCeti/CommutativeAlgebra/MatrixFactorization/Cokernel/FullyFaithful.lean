/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.GorensteinProjective

/-!
# The cokernel functor on matrix factorizations is fully faithful

Let `w` be a non-zero-divisor of a commutative ring `S` and put `R = S/(w)`. Reducing a
finite-projective matrix factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` modulo `w` and taking the
cokernel of `d₀'` gives a finitely generated Gorenstein-projective `R`-module `M_X`
(`TauCeti.MatrixFactorization.quotientGorensteinProjectiveCokernel`). This file shows that the
induced functor `HMF(S,w) ⥤ stable(Gproj-R)` is fully faithful.

Everything rests on the composite `p_X : X₁ → X₁' → M_X`, `y ↦ [1 ⊗ y]`, an `S`-linear surjection
whose kernel is the image of `d₀`: if `1 ⊗ y = d₀' (1 ⊗ x)`, then `y - d₀ x = w y'` for some `y'`,
and `w y' = d₀ (d₁ y')`. The non-zero-divisor hypothesis makes `d₀` injective on the projective
module `X₀` (`TauCeti.MatrixFactorization.d₀_injective`).

* **Fullness.** An `R`-linear map `φ : M_X → M_Y` lifts along `p_Y` to an `S`-linear
  `f₁ : X₁ → Y₁`, since `X₁` is projective. Then `f₁ ∘ d₀` lands in the image of `d₀`, so it
  lifts to `f₀ : X₀ → Y₀` with `d₀ f₀ = f₁ d₀`, and the second square commutes because `d₀` is
  injective. The pair `(f₀, f₁)` is a morphism of factorizations inducing `φ`; already before
  passing to stable categories, the cokernel functor is full
  (`TauCeti.MatrixFactorization.quotientGorensteinProjectiveCokernel_full`).
* **Faithfulness.** Suppose the cokernel of `g : X ⟶ Y` factors through a projective
  `R`-module. Lifting through the projection `Y₁' → M_Y` and then through the reduction
  `Y₁ → Y₁'` gives `h : X₁ → Y₁` such that `g₁ - h` lands in the image of `d₀` and `h ∘ d₀` lands
  in `w Y₁`. Write `g₁ - h = d₀ k` and `h d₀ = w t`. Since `w` is a non-zero-divisor on `Y₁`,
  `h = t d₁`, so `g₁ = t d₁ + d₀ k`, and injectivity of `d₀` gives `g₀ = k d₀ + d₁ t`. Thus `g`
  is the null-homotopic map of the odd map `(t, k)`
  (`quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal_iff`).

No noetherian, local, or regularity hypothesis is used. Essential surjectivity onto the stable
category of maximal Cohen–Macaulay modules needs Eisenbud's hypotheses (`S` regular local) and is
not proved here.

## Main results

In the namespace `TauCeti.MatrixFactorization`:

* `quotientGorensteinProjectiveCokernel_full`: every `R`-linear map between cokernels is induced
  by a morphism of matrix factorizations.
* `quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal_iff`: the cokernel of a
  morphism factors through a projective module exactly when the morphism is null-homotopic.
* `HomotopyCategory.quotientGorensteinProjectiveStableCokernel_full` and
  `HomotopyCategory.quotientGorensteinProjectiveStableCokernel_faithful`: the cokernel functor
  `HMF(S,w) ⥤ stable(Gproj-S/(w))` is full and faithful.
* `HomotopyCategory.fullyFaithfulQuotientGorensteinProjectiveStableCokernel`: the same functor as
  a `Functor.FullyFaithful` structure.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 6: the cokernel functor from
  matrix factorizations to stable maximal Cohen–Macaulay modules.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262** (2021), Section 4.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings

variable {S : Type u} [CommRing S] {w : S}

/-! ### The cokernel of the reduction as a quotient of the odd component -/

/-- The `S`-linear surjection `y ↦ [1 ⊗ y]` from the odd component onto the cokernel of the
reduction modulo `w`, viewed as an `S`-module. -/
private def reducedCokernelπ (X : MatrixFactorization S w) :
    X.obj.X₁.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj
      (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  (ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).unit.app
      X.obj.X₁.obj ≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map
      (cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X))

private theorem reducedCokernelπ_apply (X : MatrixFactorization S w) (y : X.obj.X₁) :
    reducedCokernelπ X y =
      cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)
        ((1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, Ideal.Quotient.mk (Ideal.span {w})] y) :=
  rfl

private theorem reducedCokernelπ_surjective (X : MatrixFactorization S w) :
    Function.Surjective (reducedCokernelπ X) := by
  intro m
  obtain ⟨z, rfl⟩ :=
    cokernelπ_surjective ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X) m
  obtain ⟨y, rfl⟩ := TensorProduct.exists_one_tmul_eq (Ideal.span {w}) z
  exact ⟨y, reducedCokernelπ_apply X y⟩

/-- The kernel of `y ↦ [1 ⊗ y]` is the image of `d₀`: if `1 ⊗ y = d₀' (1 ⊗ x)`, then
`y - d₀ x = w y' = d₀ (d₁ y')`. -/
private theorem reducedCokernelπ_eq_zero_iff (X : MatrixFactorization S w) (y : X.obj.X₁) :
    reducedCokernelπ X y = 0 ↔ y ∈ LinearMap.range X.obj.d₀.hom.hom := by
  rw [reducedCokernelπ_apply]
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

private theorem reducedCokernelπ_naturality_apply {X Y : MatrixFactorization S w} (g : X ⟶ Y)
    (y : X.obj.X₁) :
    (cokernelFunctor.map ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g)).hom
        (reducedCokernelπ X y) = reducedCokernelπ Y (g.hom.f₁.hom y) :=
  cokernelπ_naturality_apply ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g) _

/-! ### Fullness -/

/-- Every map between the cokernels of the reductions of two matrix factorizations is induced by
a morphism of matrix factorizations. -/
private theorem exists_cokernelFunctor_map_eq (hw : w ∈ nonZeroDivisors S)
    {X Y : MatrixFactorization S w}
    (φ : cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X) ⟶
      cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y)) :
    ∃ g : X ⟶ Y,
      cokernelFunctor.map ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g) = φ := by
  have : Epi (reducedCokernelπ Y) :=
    (ModuleCat.epi_iff_surjective _).2 (reducedCokernelπ_surjective Y)
  -- The odd component lifts `φ` along `y ↦ [1 ⊗ y]`.
  let a := reducedCokernelπ X ≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map φ.hom
  let f₁ := Projective.factorThru a (reducedCokernelπ Y)
  have hf₁ (y : X.obj.X₁) : reducedCokernelπ Y (f₁ y) =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map φ.hom
        (reducedCokernelπ X y) :=
    ConcreteCategory.congr_hom (Projective.factorThru_comp a (reducedCokernelπ Y)) y
  -- The even component lifts `f₁ ∘ d₀` along `d₀`.
  have hrange (x : X.obj.X₀) : f₁ (X.obj.d₀.hom x) ∈ LinearMap.range Y.obj.d₀.hom.hom := by
    rw [← reducedCokernelπ_eq_zero_iff, hf₁,
      (reducedCokernelπ_eq_zero_iff X _).2 ⟨x, rfl⟩, map_zero]
  obtain ⟨f₀, hf₀⟩ := Module.projective_lifting_property Y.obj.d₀.hom.hom.rangeRestrict
    ((f₁.hom ∘ₗ X.obj.d₀.hom.hom).codRestrict _ hrange) (LinearMap.surjective_rangeRestrict _)
  have hf₀' (x : X.obj.X₀) : Y.obj.d₀.hom (f₀ x) = f₁ (X.obj.d₀.hom x) :=
    congrArg Subtype.val (LinearMap.congr_fun hf₀ x)
  refine ⟨ObjectProperty.homMk
    { f₀ := ObjectProperty.homMk (ModuleCat.ofHom f₀)
      f₁ := ObjectProperty.homMk f₁
      comm₀ := by
        ext x
        exact hf₀' x
      comm₁ := by
        -- Both sides agree after the injective map `d₀`, where they become `w • f₁ y`.
        ext y
        apply d₀_injective hw Y
        simp only [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
          LinearMap.comp_apply, ObjectProperty.homMk_hom, ModuleCat.hom_ofHom]
        rw [d₁_comp_d₀_apply, hf₀', d₁_comp_d₀_apply, map_smul] }, ?_⟩
  apply ObjectProperty.hom_ext
  ext m
  obtain ⟨y, rfl⟩ := reducedCokernelπ_surjective X m
  exact (reducedCokernelπ_naturality_apply _ y).trans (hf₁ y)

/-- **The cokernel functor is full.** For a non-zero-divisor `w`, every map between the
Gorenstein-projective `S/(w)`-modules attached to two finite-projective matrix factorizations of
`w` is the cokernel of a morphism of matrix factorizations. -/
theorem quotientGorensteinProjectiveCokernel_full (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveCokernel hw).Full := by
  have : (quotientGorensteinProjectiveCokernel hw ⋙
      (IsGorensteinProjective (S ⧸ Ideal.span {w})).ι).Full := by
    rw [quotientGorensteinProjectiveCokernel_comp_ι]
    refine ⟨fun {X Y} φ ↦ ?_⟩
    obtain ⟨g, hg⟩ := exists_cokernelFunctor_map_eq hw
      ((forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w})) (ModuleCat.{u} _)).preimage φ)
    exact ⟨g, by rw [Functor.comp_map, Functor.comp_map, hg, Functor.map_preimage]⟩
  exact Functor.Full.of_comp_faithful _ (IsGorensteinProjective (S ⧸ Ideal.span {w})).ι

/-! ### Faithfulness -/

/-- If the cokernel of the reduction of `g` factors through a projective `S/(w)`-module, then `g`
is null-homotopic. -/
private theorem mem_nullHomotopic_of_cokernelFunctor_map_eq_comp (hw : w ∈ nonZeroDivisors S)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) {Q : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    [Projective Q]
    (i : (cokernelFunctor.obj
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj ⟶ Q)
    (p : Q ⟶ (cokernelFunctor.obj
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y)).obj)
    (hg : (cokernelFunctor.map
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g)).hom = i ≫ p) :
    g ∈ (nullHomotopic (S := S) (w := w)).hom X Y := by
  have hr : IsSMulRegular Y.obj.X₁ w := Module.Flat.isSMulRegular_of_nonZeroDivisors hw
  -- Lift `p` through the cokernel projection of the reduction of `Y`.
  let p' := Projective.factorThru p
    (cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y))
  have hp' := Projective.factorThru_comp p
    (cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y))
  -- Lift the composite `X₁ → M_X → Q → Y₁'` through the reduction `u : Y₁ → Y₁'` to `h`.
  let u : Y.obj.X₁.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.X₁.obj :=
    (ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).unit.app
      Y.obj.X₁.obj
  have : Epi u := (ModuleCat.epi_iff_surjective _).2 fun z ↦ by
    obtain ⟨y, rfl⟩ := TensorProduct.exists_one_tmul_eq (M := Y.obj.X₁) (Ideal.span {w}) z
    exact ⟨y, rfl⟩
  let a := reducedCokernelπ X ≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map (i ≫ p')
  let h := Projective.factorThru a u
  have hh (y : X.obj.X₁) : u (h y) =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map (i ≫ p')
        (reducedCokernelπ X y) :=
    ConcreteCategory.congr_hom (Projective.factorThru_comp a u) y
  -- `g₁ - h` vanishes in the cokernel, so it is `d₀ k`.
  have ha (y : X.obj.X₁) : g.hom.f₁.hom y - h y ∈ LinearMap.range Y.obj.d₀.hom.hom := by
    refine (reducedCokernelπ_eq_zero_iff Y _).1 ?_
    rw [map_sub, sub_eq_zero]
    exact (reducedCokernelπ_naturality_apply g y).symm.trans
      ((ConcreteCategory.congr_hom hg (reducedCokernelπ X y)).trans
        ((ConcreteCategory.congr_hom hp' (i (reducedCokernelπ X y))).symm.trans
          (congrArg (cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y))
            (hh y).symm)))
  obtain ⟨k, hk⟩ := Module.projective_lifting_property Y.obj.d₀.hom.hom.rangeRestrict
    ((g.hom.f₁.hom.hom - h.hom).codRestrict _ ha) (LinearMap.surjective_rangeRestrict _)
  have hk' (y : X.obj.X₁) : Y.obj.d₀.hom (k y) = g.hom.f₁.hom y - h y :=
    congrArg Subtype.val (LinearMap.congr_fun hk y)
  -- `h ∘ d₀` vanishes after reduction, so it is `w • t`.
  have hb (x : X.obj.X₀) : h (X.obj.d₀.hom x) ∈
      LinearMap.range (w • LinearMap.id : Y.obj.X₁ →ₗ[S] Y.obj.X₁) := by
    have : u (h (X.obj.d₀.hom x)) = 0 := by
      rw [hh, (reducedCokernelπ_eq_zero_iff X _).2 ⟨x, rfl⟩, map_zero]
    obtain ⟨y', hy'⟩ := (TensorProduct.one_tmul_eq_zero_iff_exists_smul_eq w _).1 this
    exact ⟨y', hy'⟩
  obtain ⟨t, ht⟩ := Module.projective_lifting_property
    (w • LinearMap.id : Y.obj.X₁ →ₗ[S] Y.obj.X₁).rangeRestrict
    ((h.hom ∘ₗ X.obj.d₀.hom.hom).codRestrict _ hb) (LinearMap.surjective_rangeRestrict _)
  have ht' (x : X.obj.X₀) : w • t x = h (X.obj.d₀.hom x) :=
    congrArg Subtype.val (LinearMap.congr_fun ht x)
  -- Cancelling the non-zero-divisor `w` on `Y₁` gives `h = t ∘ d₁`.
  have hc (y : X.obj.X₁) : h y = t (X.obj.d₁.hom y) := by
    apply hr
    simp only [ht', d₁_comp_d₀_apply, map_smul]
  rw [mem_nullHomotopic_iff]
  refine ⟨ObjectProperty.homMk (ModuleCat.ofHom t), ObjectProperty.homMk (ModuleCat.ofHom k), ?_⟩
  apply CurvedDuplex.hom_ext
  · ext x
    simp only [CurvedDuplex.nullHomotopicMap_f₀, ObjectProperty.add_hom,
      ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_add, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.comp_apply, ObjectProperty.homMk_hom, ModuleCat.hom_ofHom]
    apply d₀_injective hw Y
    rw [map_add, hk', d₁_comp_d₀_apply, ht', comm₀_apply, sub_add_cancel]
  · ext y
    simp only [CurvedDuplex.nullHomotopicMap_f₁, ObjectProperty.add_hom,
      ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_add, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.comp_apply, ObjectProperty.homMk_hom, ModuleCat.hom_ofHom]
    rw [hk', ← hc, add_sub_cancel]

/-- For a non-zero-divisor `w`, the Gorenstein-projective cokernel of a morphism of
finite-projective matrix factorizations factors through a projective `S/(w)`-module exactly when
the morphism is null-homotopic. -/
theorem quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal_iff
    (hw : w ∈ nonZeroDivisors S) {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (quotientGorensteinProjectiveCokernel hw).map g ∈
        (GorensteinProjectiveModuleCat.exactStructure
          (S ⧸ Ideal.span {w})).projectiveStableIdeal.hom _ _ ↔
      g ∈ (nullHomotopic (S := S) (w := w)).hom X Y := by
  refine ⟨fun hg ↦ ?_, quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal hw⟩
  rw [ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff] at hg
  obtain ⟨Q, hQ, i, p, hip⟩ := hg
  have : Projective Q.obj :=
    (GorensteinProjectiveModuleCat.exactStructure_isProjective_iff Q).1 hQ
  -- Transport the factorization along the identification of the cokernel functor, followed by
  -- the inclusion into all modules, with the cokernel of the reduction.
  have hip' : (quotientGorensteinProjectiveCokernel hw ⋙
      (IsGorensteinProjective (S ⧸ Ideal.span {w})).ι).map g = i.hom ≫ p.hom := by
    rw [Functor.comp_map, hip, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom]
  have e := Functor.congr_hom (quotientGorensteinProjectiveCokernel_comp_ι hw).symm g
  rw [hip', Category.assoc, ← Category.assoc] at e
  exact mem_nullHomotopic_of_cokernelFunctor_map_eq_comp hw g _ _ e

namespace HomotopyCategory

/-- **The stable cokernel functor is full.** For a non-zero-divisor `w`, every stable map between
the cokernels of two finite-projective matrix factorizations comes from `HMF(S,w)`. -/
theorem quotientGorensteinProjectiveStableCokernel_full (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveStableCokernel hw).Full := by
  have := quotientGorensteinProjectiveCokernel_full hw
  have : ((nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
      quotientGorensteinProjectiveStableCokernel hw).Full := by
    rw [quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel]
    infer_instance
  exact Functor.full_of_comp_essSurj _ (nullHomotopic (S := S) (w := w)).quotientFunctor
    fun _ _ φ ↦ ⟨(nullHomotopic (S := S) (w := w)).quotientFunctor.map
      (((nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        quotientGorensteinProjectiveStableCokernel hw).preimage φ),
      Functor.map_preimage ((nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        quotientGorensteinProjectiveStableCokernel hw) φ⟩

/-- **The stable cokernel functor is faithful.** For a non-zero-divisor `w`, two morphisms of
`HMF(S,w)` with the same stable cokernel are equal. -/
theorem quotientGorensteinProjectiveStableCokernel_faithful (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveStableCokernel hw).Faithful := by
  refine Functor.faithful_of_comp_essSurj _ (nullHomotopic (S := S) (w := w)).quotientFunctor
    fun X Y f g hfg ↦ ?_
  obtain ⟨f, rfl⟩ := (nullHomotopic (S := S) (w := w)).quotientFunctor.map_surjective f
  obtain ⟨g, rfl⟩ := (nullHomotopic (S := S) (w := w)).quotientFunctor.map_surjective g
  rw [MorphismIdeal.quotientFunctor_map_eq_iff,
    ← quotientGorensteinProjectiveCokernel_map_mem_projectiveStableIdeal_iff hw, Functor.map_sub,
    ← MorphismIdeal.quotientFunctor_map_eq_iff]
  -- The composite with the quotient functor is only propositionally the cokernel followed by
  -- the stable quotient, so generalize it before substituting.
  have key : ∀ Φ : MatrixFactorization S w ⥤ _,
      Φ = (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        quotientGorensteinProjectiveStableCokernel hw → Φ.map f = Φ.map g := by
    rintro _ rfl
    exact hfg
  exact key _ (quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel hw).symm

/-- **The stable cokernel functor is fully faithful.** For a non-zero-divisor `w` of a commutative
ring `S`, the functor `HMF(S,w) ⥤ stable(Gproj-S/(w))` sending a finite-projective matrix
factorization to the cokernel of its reduction modulo `w` is fully faithful. -/
def fullyFaithfulQuotientGorensteinProjectiveStableCokernel (hw : w ∈ nonZeroDivisors S) :
    (quotientGorensteinProjectiveStableCokernel hw).FullyFaithful :=
  haveI := quotientGorensteinProjectiveStableCokernel_full hw
  haveI := quotientGorensteinProjectiveStableCokernel_faithful hw
  .ofFullyFaithful _

end HomotopyCategory

end TauCeti.MatrixFactorization
