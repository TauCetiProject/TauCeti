/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Biproducts
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.GeneratingSections
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.LineBundle.TwistedSections
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Modules.Tensor.AffineSections
public import TauCeti.CategoryTheory.Monoidal.InvertibleObject
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Global generation and quotient presentations via ample line bundles

Let `X` be a quasi-separated scheme carrying an ample line-bundle class `a`, and let `F` be a
quasi-coherent `𝒪_X`-module of finite type. Twisting `F` by sufficiently high powers `aⁿ` produces
finitely many global sections generating `F ⊗ K` for every invertible sheaf `K` of class `aⁿ`
(Grothendieck, *EGA II*, Proposition 4.5.5; Hartshorne, Theorem II.5.17; Stacks, Tag 01Q3). No
Noetherian hypothesis on `X` is needed.

Applying this to the structure sheaf `𝒪_X` shows that all sufficiently high powers of an ample
line bundle on a quasi-separated scheme are globally generated. Tensoring the resulting finite free
presentation `𝒪_X^k ↠ F ⊗ K` on the right with a line bundle `K'` of inverse class `(aⁿ)⁻¹`
exhibits `F` as a quotient of a finite direct sum `⨁_{i : Fin k} K'` of negative ample twists.

The proof upgrades the extension of sections from a nonvanishing locus `X_s` (`TwistedSections`)
from a single exponent to all sufficiently large exponents using the recursive action of
`TauCeti.tensorPowSuccIso` on tensor powers of sections. Covering `X` by finitely many affine
nonvanishing loci `X_{s_i}` of positive powers `a^{d_i}`, Euclidean division `n = d_i * q + r`
separates `n` into a bounded remainder `r < d_i` and a large quotient `q = n / d_i`, allowing finite
generating sets of `Γ(F ⊗ L^r, X_{s_i})` to extend simultaneously to global sections once `q`
exceeds the thresholds for all finitely many pairs `(i, r)`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exists_forall_ge_exists_map_eq_tmulRight_tensorPowSection`:
  for a section `t` of a quasi-coherent module `F` over `X_s`, there exists `n₀` such that `t ⊗ sⁿ`
  extends to `U` for all `n ≥ n₀`.
* `AlgebraicGeometry.Scheme.Modules.generatingSectionsOfSpanEqTop`: global sections of a
  quasi-coherent module whose restrictions span over every member of an affine open cover form a
  `SheafOfModules.GeneratingSections`.
* `AlgebraicGeometry.Scheme.Modules.exists_epi_biproduct_of_generatingSections`: finite global
  generation of `F ⊗ P` with `P ⊗ Q ≅ 𝒪_X` yields an epimorphism `(⨁_{Fin k} Q) ⟶ F`.
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorPowObjIso`: comparison between the underlying
  sheaf of `InvertibleSheaf.tensorPow L n` and `TauCeti.tensorPow L.obj n`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_generatingSections`:
  Serre's global generation theorem for twists of a quasi-coherent module of finite type by all
  sufficiently high powers of an ample line-bundle class.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_isGloballyGenerated`:
  all sufficiently high powers of an ample line-bundle class are globally generated.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_epi_biproduct`:
  every quasi-coherent module of finite type is a quotient of a finite biproduct of copies of any
  sufficiently negative power of an ample line-bundle class.

## References

* A. Grothendieck, *Éléments de géométrie algébrique. II*, Publ. Math. IHÉS **8** (1961), §4.5.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem II.5.17 and
  Corollary II.5.18.
* [The Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace TauCeti

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- The category of `𝒪_X`-modules has finite biproducts. -/
instance instHasFiniteBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  TauCeti.SheafOfModules.hasFiniteBiproducts X.ringCatSheaf

variable {X : Scheme.{u}}

/-! ### Monoidal coherences on tensor powers of sections -/

/-- The associator `(F ⊗ G) ⊗ H ≅ F ⊗ (G ⊗ H)` sends `(a ⊗ b) ⊗ c` to `a ⊗ (b ⊗ c)`. -/
theorem associator_hom_app_tmulRight (F G H : X.Modules) {U : X.Opens}
    (a : Γ(F, U)) (b : Γ(G, U)) (c : Γ(H, U)) :
    (α_ F G H).hom.app U (tmulRight (F ⊗ G) c (tmulRight F b a)) =
      tmulRight F (tmulRight G c b) a := by
  let a' : (sectionsFunctor U).obj F := a
  let b' : (sectionsFunctor U).obj G := b
  let c' : (sectionsFunctor U).obj H := c
  let ab : ↥((sectionsFunctor U).obj F ⊗ (sectionsFunctor U).obj G) := a' ⊗ₜ[Γ(X, U)] b'
  have h := congrArg (fun φ ↦ φ (ab ⊗ₜ[Γ(X, U)] c'))
    (Functor.LaxMonoidal.associativity (sectionsFunctor U) F G H)
  simp only [ab, CategoryTheory.ConcreteCategory.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply, sectionsFunctor_map] at h
  exact (congrArg ((α_ F G H).hom.app U)
    ((tmulRight_apply (F ⊗ G) c (tmulRight F b a)).trans
      (congrArg (fun x ↦ Functor.LaxMonoidal.μ (sectionsFunctor U) (F ⊗ G) H (x ⊗ₜ c'))
        (tmulRight_apply F b a)))).trans
    (h.trans ((tmulRight_apply F (tmulRight G c b) a).trans
      (congrArg (fun y ↦ Functor.LaxMonoidal.μ (sectionsFunctor U) F (G ⊗ H) (a' ⊗ₜ y))
        (tmulRight_apply G c b))).symm)

/-- The left unitor `𝒪_X ⊗ F ≅ F` sends `r ⊗ t` to `r • t`. -/
theorem leftUnitor_hom_app_tmulRight (F : X.Modules) {U : X.Opens}
    (r : Γ(X, U)) (t : Γ(F, U)) :
    (λ_ F).hom.app U (tmulRight (𝟙_ X.Modules) t r) = r • t := by
  let t' : (sectionsFunctor U).obj F := t
  have h := congrArg (fun φ ↦ φ (r ⊗ₜ t'))
    (Functor.LaxMonoidal.left_unitality (sectionsFunctor U) F)
  simp only [sectionsFunctor_ε, CategoryTheory.ConcreteCategory.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply, sectionsFunctor_map] at h
  exact (congrArg ((λ_ F).hom.app U) (tmulRight_apply (𝟙_ X.Modules) t r)).trans h.symm

/-- Appending a factor on the right via `tensorPowSuccIso` carries `eⁿ ⊗ e` to `eⁿ⁺¹`. -/
theorem tensorPowSuccIso_hom_app_tmulRight_tensorPowSection {L : X.Modules} {U : X.Opens}
    (e : Γ(L, U)) (n : ℕ) :
    (tensorPowSuccIso L n).hom.app U (tmulRight (tensorPow L n) e (tensorPowSection e n)) =
      tensorPowSection e (n + 1) := by
  induction n with
  | zero =>
    rw [tensorPowSuccIso_zero_hom, Hom.comp_app, ConcreteCategory.comp_apply,
      tensorPowSection_zero, leftUnitor_hom_app_tmulRight, one_smul,
      rightUnitor_inv_app_eq_tmulRight, ← tensorPowSection_zero e]
    exact (tensorPowSection_succ e 0).symm
  | succ n ih =>
    rw [tensorPowSuccIso_succ_hom, Hom.comp_app, ConcreteCategory.comp_apply,
      tensorPowSection_succ, associator_hom_app_tmulRight, whiskerLeft_app_tmulRight, ih]
    exact (tensorPowSection_succ e (n + 1)).symm

/-- If `t ⊗ sⁿ` extends from `X_s` to `U`, then `t ⊗ sⁿ⁺¹` also extends from `X_s` to `U`. -/
private theorem exists_map_eq_tmulRight_tensorPowSection_succ (F : X.Modules) {L : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]
    {U : X.Opens} (s : Γ(L, U)) (t : Γ(F, L.nonvanishingLocus s)) {n : ℕ}
    {t' : Γ(F ⊗ tensorPow L n, U)}
    (ht' : (F ⊗ tensorPow L n).presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op t' =
      tmulRight F
        (tensorPowSection (L.presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op s) n) t) :
    ∃ t'' : Γ(F ⊗ tensorPow L (n + 1), U),
      (F ⊗ tensorPow L (n + 1)).presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op t'' =
        tmulRight F
          (tensorPowSection (L.presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op s) (n + 1))
          t := by
  let φ : (F ⊗ tensorPow L n) ⊗ L ⟶ F ⊗ tensorPow L (n + 1) :=
    (α_ F (tensorPow L n) L).hom ≫ F ◁ (tensorPowSuccIso L n).hom
  let i : L.nonvanishingLocus s ⟶ U := homOfLE (L.nonvanishingLocus_le s)
  refine ⟨φ.app U (tmulRight (F ⊗ tensorPow L n) s t'), ?_⟩
  have hnat : φ.app (L.nonvanishingLocus s)
      (((F ⊗ tensorPow L n) ⊗ L).presheaf.map i.op (tmulRight (F ⊗ tensorPow L n) s t')) =
      (F ⊗ tensorPow L (n + 1)).presheaf.map i.op (φ.app U (tmulRight (F ⊗ tensorPow L n) s t')) :=
    φ.mapPresheaf.naturality_apply i.op _
  rw [← hnat, map_tmulRight, ht']
  simp only [φ, Hom.comp_app, ConcreteCategory.comp_apply]
  rw [associator_hom_app_tmulRight, whiskerLeft_app_tmulRight,
    tensorPowSuccIso_hom_app_tmulRight_tensorPowSection]

/-- **Uniform extension of sections from a nonvanishing locus**: for quasi-coherent `F`, invertible
`L`, a quasi-compact quasi-separated open `U`, and a section `t` of `F` over `X_s`, there exists
`n₀` such that `t ⊗ sⁿ` extends to a section of `F ⊗ Lⁿ` over `U` for *every* `n ≥ n₀`. -/
theorem exists_forall_ge_exists_map_eq_tmulRight_tensorPowSection (F : X.Modules)
    [F.IsQuasicoherent] {L : X.Modules}
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (s : Γ(L, U))
    (t : Γ(F, L.nonvanishingLocus s)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ t' : Γ(F ⊗ tensorPow L n, U),
      (F ⊗ tensorPow L n).presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op t' =
        tmulRight F
          (tensorPowSection (L.presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op s) n) t := by
  obtain ⟨n₀, t₀, ht₀⟩ := exists_map_eq_tmulRight_tensorPowSection F hU hU' s t
  refine ⟨n₀, fun n hn ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => exact ⟨t₀, ht₀⟩
  | succ k ih =>
    obtain ⟨t', ht'⟩ := ih (Nat.le_add_right n₀ k)
    exact exists_map_eq_tmulRight_tensorPowSection_succ F s t ht'

/-! ### Global generation from affine covers and quotient presentations -/

private theorem isLocallySurjective_freeHomEquiv_symm_of_span_eq_top (E : X.Modules)
    [E.IsQuasicoherent] {ι : Type*} {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i))
    (hcover : ⨆ i, U i = ⊤) {I : Type u} [Finite I] (σ : I → Γ(E, ⊤))
    (hspan : ∀ i, Submodule.span Γ(X, U i)
      (Set.range fun k ↦ E.presheaf.map (U i).leTop.op (σ k)) = ⊤) :
    Sheaf.IsLocallySurjective
      ((TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X).map
        ((SheafOfModules.freeHomEquiv E).symm fun k ↦ E.sectionsEquivTop.symm (σ k))) := by
  cases nonempty_fintype I
  let s : I → E.sections := fun k ↦ E.sectionsEquivTop.symm (σ k)
  refine ⟨fun {W} m x hxW ↦ ?_⟩
  obtain ⟨i, hxU⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top x)
  obtain ⟨f, hfW, hxf⟩ := (hU i).exists_basicOpen_le ⟨x, hxW⟩ hxU
  let D := X.basicOpen f
  let m' : Γ(E, D) := E.presheaf.map (homOfLE hfW).op m
  have := E.isLocalizedModule_basicOpenRestrict (hU i) f
  obtain ⟨⟨y, ⟨_, d, rfl⟩⟩, hy⟩ :=
    IsLocalizedModule.surj (.powers f) (E.basicOpenRestrict f) m'
  rw [basicOpenRestrict_apply] at hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, U i)).mp
    (hspan i ▸ Submodule.mem_top (x := y))
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ d)) := by
    rw [map_pow]; exact (X.toRingedSpace.isUnit_res_basicOpen f).pow d
  let uinv : Γ(X, D) := ↑hu.unit⁻¹
  let a₀ : I → Γ(X, D) := fun k ↦ uinv * X.presheaf.map (homOfLE (X.basicOpen_le f)).op (c k)
  let a : I → X.ringCatSheaf.obj.obj (op D) := a₀
  refine ⟨D, homOfLE hfW, ⟨∑ k, a k •
    (SheafOfModules.freeSection (R := X.ringCatSheaf) k).eval (op D), ?_⟩, hxf⟩
  refine (TauCeti.SheafOfModules.freeHomEquiv_symm_val_app_sum_smul s (op D) a).trans ?_
  have hterm (k : I) : a k • (s k).eval (op D) =
      a₀ k • E.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (E.presheaf.map (U i).leTop.op (σ k)) := by
    rw [PresheafOfModules.sections.eval, sectionsEquivTop_symm_val, ← Functor.map_comp_apply,
      ← op_comp]
    rfl
  have hmap_y : E.presheaf.map (homOfLE (X.basicOpen_le f)).op y =
      ∑ k, X.presheaf.map (homOfLE (X.basicOpen_le f)).op (c k) •
        E.presheaf.map (homOfLE (X.basicOpen_le f)).op (E.presheaf.map (U i).leTop.op (σ k)) := by
    rw [← hc, map_sum]; exact Finset.sum_congr rfl fun k _ ↦ by rw [E.map_smul]
  have hsum : ∑ k, a₀ k • E.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (E.presheaf.map (U i).leTop.op (σ k)) =
      uinv • E.presheaf.map (homOfLE (X.basicOpen_le f)).op y := by
    rw [hmap_y, Finset.smul_sum]; exact Finset.sum_congr rfl fun k _ ↦ mul_smul _ _ _
  have hm : (hu.unit : Γ(X, D)) • m' = E.presheaf.map (homOfLE (X.basicOpen_le f)).op y := by
    rw [IsUnit.unit_spec]; exact hy
  have hgoal : ∑ k, a₀ k • E.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (E.presheaf.map (U i).leTop.op (σ k)) = m' := by
    rw [hsum, ← hm, ← mul_smul, Units.inv_mul, one_smul]
  exact (Finset.sum_congr rfl fun k _ ↦ hterm k).trans hgoal

/-- If a family of global sections of a quasi-coherent module `E` spans `Γ(E, U i)` over every
member `U i` of an affine open cover of `X`, then it defines a `GeneratingSections` of `E`. -/
def generatingSectionsOfSpanEqTop (E : X.Modules) [E.IsQuasicoherent]
    {ι : Type*} {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤)
    {I : Type u} [Finite I] (σ : I → Γ(E, ⊤))
    (hspan : ∀ i, Submodule.span Γ(X, U i)
      (Set.range fun k ↦ E.presheaf.map (U i).leTop.op (σ k)) = ⊤) :
    E.GeneratingSections where
  I := I
  s k := E.sectionsEquivTop.symm (σ k)
  epi := by
    have := isLocallySurjective_freeHomEquiv_symm_of_span_eq_top E hU hcover σ hspan
    exact (TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X).epi_of_epi_map
      (Sheaf.epi_of_isLocallySurjective _)

/-- `generatingSectionsOfSpanEqTop` indexed by a finite type is of finite type. -/
instance isFiniteType_generatingSectionsOfSpanEqTop (E : X.Modules) [E.IsQuasicoherent]
    {ι : Type*} {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤)
    {I : Type u} [Finite I] (σ : I → Γ(E, ⊤))
    (hspan : ∀ i, Submodule.span Γ(X, U i)
      (Set.range fun k ↦ E.presheaf.map (U i).leTop.op (σ k)) = ⊤) :
    (generatingSectionsOfSpanEqTop E hU hcover σ hspan).IsFiniteType where
  finite := ‹Finite I›

/-- If `F ⊗ P` is generated by finitely many global sections and `P ⊗ Q ≅ 𝒪_X`, then `F` is a
quotient of a finite biproduct of copies of `Q`. -/
theorem exists_epi_biproduct_of_generatingSections {F P Q : X.Modules} (e : P ⊗ Q ≅ 𝟙_ X.Modules)
    (G : (F ⊗ P).GeneratingSections) [hG : G.IsFiniteType] :
    ∃ (k : ℕ) (p : (⨁ fun _ : Fin k ↦ Q) ⟶ F), Epi p := by
  have : Finite G.I := hG.finite
  obtain ⟨k, ⟨ek⟩⟩ := Finite.exists_equiv_fin G.I
  let E : X.Modules ≌ X.Modules := tensorRightEquivalenceOfIso (β_ Q P ≪≫ e) e
  have : (tensorRight Q).IsEquivalence := E.isEquivalence_functor
  have : (tensorRight Q).Additive := Functor.additive_of_preserves_binary_products _
  have : Epi G.π := G.epi
  let ι : Fin k → ((𝟙_ X.Modules : X.Modules) ⟶ F ⊗ P) := fun j ↦
    (SheafOfModules.ιFree (ek.symm j) : (𝟙_ X.Modules : X.Modules) ⟶
      (SheafOfModules.free G.I : X.Modules)) ≫ G.π
  let q : (⨁ fun _ : Fin k ↦ (𝟙_ X.Modules : X.Modules)) ⟶ F ⊗ P := biproduct.desc ι
  have hq : Epi q := ⟨fun {N} f₁ f₂ hf ↦ by
    apply (cancel_epi G.π).mp
    let f₁' : (F ⊗ P : SheafOfModules X.ringCatSheaf) ⟶ (N : SheafOfModules X.ringCatSheaf) := f₁
    let f₂' : (F ⊗ P : SheafOfModules X.ringCatSheaf) ⟶ (N : SheafOfModules X.ringCatSheaf) := f₂
    -- `X.Modules` and `SheafOfModules X.ringCatSheaf` share the same morphism type and composition.
    change G.π ≫ f₁' = G.π ≫ f₂'
    refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan G.I) _ _ fun i ↦ ?_
    have hi : biproduct.ι _ (ek i) ≫ q = ι (ek i) := biproduct.ι_desc ι (ek i)
    have hcomp : (biproduct.ι _ (ek i) ≫ q) ≫ f₁ = (biproduct.ι _ (ek i) ≫ q) ≫ f₂ := by
      rw [Category.assoc, Category.assoc, hf]
    rw [hi] at hcomp
    simp only [ι, ek.symm_apply_apply] at hcomp
    exact SheafOfModules.Hom.ext (congrArg SheafOfModules.Hom.val hcomp)⟩
  refine ⟨k,
    (biproduct.mapIso fun _ : Fin k ↦ (λ_ Q).symm).hom ≫
      ((tensorRight Q).mapBiproduct fun _ : Fin k ↦ (𝟙_ X.Modules : X.Modules)).inv ≫
      (tensorRight Q).map q ≫
      (α_ F P Q).hom ≫ F ◁ e.hom ≫ (ρ_ F).hom,
    inferInstance⟩

/-- Tensor powers of a quasi-coherent module are quasi-coherent. -/
instance isQuasicoherent_tensorPow (L : X.Modules) [L.IsQuasicoherent] (n : ℕ) :
    (tensorPow L n).IsQuasicoherent := by
  induction n with
  | zero => exact TauCeti.AlgebraicGeometry.isQuasicoherent_unit X
  | succ n ih => exact inferInstanceAs (L ⊗ tensorPow L n).IsQuasicoherent

/-- Over an affine open `U`, twisting a quasi-coherent module of finite type by any tensor power of
an invertible sheaf preserves finite generation of sections over `Γ(X, U)`. -/
theorem finite_sections_tensor_tensorPow_of_isAffineOpen (F L : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType]
    [hL : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]
    {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ) :
    Module.Finite Γ(X, U) Γ(F ⊗ tensorPow L n, U) := by
  let L' : TauCeti.AlgebraicGeometry.InvertibleSheaf X := ⟨L, hL⟩
  have hLqc : L.IsQuasicoherent := L'.isQuasicoherent_obj
  have hLfp : (L : SheafOfModules X.ringCatSheaf).IsFinitePresentation :=
    L'.property.isFinitePresentation
  have hLft : L.IsFiniteType :=
    inferInstanceAs (L : SheafOfModules X.ringCatSheaf).IsFiniteType
  have hfin_tensor (A B : X.Modules) [A.IsQuasicoherent] [B.IsQuasicoherent]
      (hA : Module.Finite Γ(X, U) Γ(A, U)) (hB : Module.Finite Γ(X, U) Γ(B, U)) :
      Module.Finite Γ(X, U) Γ(A ⊗ B, U) := by
    let M : ModuleCat Γ(X, U) := (sectionsFunctor U).obj A
    let N : ModuleCat Γ(X, U) := (sectionsFunctor U).obj B
    have : Module.Finite Γ(X, U) M := hA
    have : Module.Finite Γ(X, U) N := hB
    have : Module.Finite Γ(X, U) ↑(M ⊗ N) :=
      inferInstanceAs (Module.Finite Γ(X, U) (TensorProduct Γ(X, U) M N))
    exact Module.Finite.of_surjective
      (Functor.LaxMonoidal.μ (sectionsFunctor U) A B).hom
      (bijective_μ_sectionsFunctor A B hU).surjective
  have hLU : Module.Finite Γ(X, U) Γ(L, U) := L.finite_sections_of_isAffineOpen U hU
  have hFU : Module.Finite Γ(X, U) Γ(F, U) := F.finite_sections_of_isAffineOpen U hU
  have hpow (m : ℕ) : Module.Finite Γ(X, U) Γ(tensorPow L m, U) := by
    induction m with
    | zero => exact inferInstanceAs (Module.Finite Γ(X, U) Γ(X, U))
    | succ m ih => exact hfin_tensor L (tensorPow L m) hLU ih
  exact hfin_tensor F (tensorPow L n) hFU (hpow n)

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry

namespace InvertibleSheaf

variable {X : Scheme.{u}}

/-- The underlying sheaf of `InvertibleSheaf.tensorPow L n` is isomorphic in `X.Modules` to the
monoidal tensor power `TauCeti.tensorPow L.obj n`. -/
def tensorPowObjIso (L : InvertibleSheaf X) :
    (n : ℕ) → ((L.tensorPow n).obj : X.Modules) ≅ TauCeti.tensorPow (L.obj : X.Modules) n
  | 0 =>
    eqToIso (congrArg (fun K : InvertibleSheaf X ↦ (K.obj : X.Modules)) L.tensorPow_zero) ≪≫
      trivialObjIsoUnit X
  | n + 1 =>
    eqToIso (congrArg (fun K : InvertibleSheaf X ↦ (K.obj : X.Modules)) (L.tensorPow_succ n)) ≪≫
      tensorProductObjIso (L.tensorPow n) L ≪≫
      whiskerRightIso (tensorPowObjIso L n) (L.obj : X.Modules) ≪≫
      TauCeti.tensorPowSuccIso (L.obj : X.Modules) n

/-- Any line bundle of class `(mk L)ⁿ` has underlying sheaf isomorphic in `X.Modules` to
`TauCeti.tensorPow L.obj n`. -/
theorem nonempty_iso_tensorPow_of_mk_eq {K L : InvertibleSheaf X} {n : ℕ}
    (h : LineBundleClass.mk K = LineBundleClass.mk L ^ n) :
    Nonempty ((K.obj : X.Modules) ≅ TauCeti.tensorPow (L.obj : X.Modules) n) := by
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp (h.trans (LineBundleClass.mk_tensorPow L n).symm)
  exact ⟨_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X e ≪≫ L.tensorPowObjIso n⟩

end InvertibleSheaf

namespace LineBundleClass

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Euclidean division isomorphism `(F ⊗ L^r) ⊗ M^q ≅ F ⊗ L^n` when `mk M = (mk L)^d` and
`d * q + r = n`. -/
private theorem nonempty_tensor_tensorPow_iso (F : X.Modules) (L M : InvertibleSheaf X)
    {d q r n : ℕ} (hM : LineBundleClass.mk M = LineBundleClass.mk L ^ d) (hn : d * q + r = n) :
    Nonempty ((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
      TauCeti.tensorPow (M.obj : X.Modules) q ≅
      F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n) := by
  have hclass :
      LineBundleClass.mk (InvertibleSheaf.tensorProduct (L.tensorPow r) (M.tensorPow q)) =
        LineBundleClass.mk L ^ n := by
    rw [mk_tensorProduct, mk_tensorPow, mk_tensorPow, hM, ← pow_mul, ← pow_add, add_comm, hn]
  obtain ⟨e⟩ := InvertibleSheaf.nonempty_iso_tensorPow_of_mk_eq hclass
  exact ⟨α_ F _ _ ≪≫ whiskerLeftIso F
    (tensorIso (L.tensorPowObjIso r).symm (M.tensorPowObjIso q).symm ≪≫
      (InvertibleSheaf.tensorProductObjIso (L.tensorPow r) (M.tensorPow q)).symm ≪≫ e)⟩

private theorem exists_finite_span_and_forall_ge_map_eq [QuasiSeparatedSpace X] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (L M : InvertibleSheaf X)
    (s : Γ(M.obj, ⊤)) (hU : IsAffineOpen (M.obj.nonvanishingLocus s)) (r : ℕ) :
    ∃ (k : ℕ) (g : Fin k → Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r,
        M.obj.nonvanishingLocus s)) (q₀ : ℕ),
      Submodule.span Γ(X, M.obj.nonvanishingLocus s) (Set.range g) = ⊤ ∧
      ∀ q ≥ q₀, ∀ j : Fin k,
        ∃ t' : Γ((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
          TauCeti.tensorPow (M.obj : X.Modules) q, ⊤),
          ((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
            TauCeti.tensorPow (M.obj : X.Modules) q).presheaf.map
            (homOfLE (M.obj.nonvanishingLocus_le s)).op t' =
            tmulRight (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r)
              (tensorPowSection (M.obj.presheaf.map
                (homOfLE (M.obj.nonvanishingLocus_le s)).op s) q) (g j) := by
  let U := M.obj.nonvanishingLocus s
  have : (L.obj : X.Modules).IsQuasicoherent := L.isQuasicoherent_obj
  have : Module.Finite Γ(X, U) Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r, U) :=
    finite_sections_tensor_tensorPow_of_isAffineOpen F L.obj hU r
  obtain ⟨S, hS⟩ := Module.Finite.fg_top
    (R := Γ(X, U)) (M := Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r, U))
  let eS := S.equivFin.symm
  let g : Fin S.card → Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r, U) := fun j ↦ (eS j).1
  have hg : Submodule.span Γ(X, U) (Set.range g) = ⊤ := by
    have hr : Set.range g = (S : Set _) := by
      ext x
      exact ⟨fun ⟨j, hj⟩ ↦ hj ▸ (eS j).2, fun hx ↦ ⟨eS.symm ⟨x, hx⟩, by simp [g]⟩⟩
    rw [hr, hS]
  have htop_cpt : IsCompact (⊤ : X.Opens).1 := isCompact_univ
  have htop_qs : IsQuasiSeparated (⊤ : X.Opens).1 := isQuasiSeparated_univ
  choose qj hqj using fun j : Fin S.card ↦
    exists_forall_ge_exists_map_eq_tmulRight_tensorPowSection
      (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) htop_cpt htop_qs s (g j)
  exact ⟨S.card, g, Finset.univ.sup qj, hg, fun q hq j ↦
    hqj j q ((Finset.le_sup (f := qj) (Finset.mem_univ j)).trans hq)⟩

/-- Local chart step for Serre's theorem: on an affine nonvanishing locus `U = X_s` of a global
section `s` of `M` with `mk M = (mk L)^d` (`d > 0`), there exist `n₀` and, for every `n ≥ n₀`,
finitely many global sections of `F ⊗ Lⁿ` whose restrictions to `U` span `Γ(F ⊗ Lⁿ, U)`. -/
private theorem exists_forall_ge_finite_global_span [QuasiSeparatedSpace X] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (L M : InvertibleSheaf X)
    {d : ℕ} (hd : 0 < d) (hM : LineBundleClass.mk M = LineBundleClass.mk L ^ d) (s : Γ(M.obj, ⊤))
    (hU : IsAffineOpen (M.obj.nonvanishingLocus s)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (k : ℕ) (σ : Fin k → Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n, ⊤)),
        Submodule.span Γ(X, M.obj.nonvanishingLocus s)
          (Set.range fun j ↦
            (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n).presheaf.map
              (M.obj.nonvanishingLocus s).leTop.op (σ j)) = ⊤ := by
  let U := M.obj.nonvanishingLocus s
  have : (L.obj : X.Modules).IsQuasicoherent := L.isQuasicoherent_obj
  choose k g q₀ hspan hext using fun r : Fin d ↦
    exists_finite_span_and_forall_ge_map_eq F L M s hU r
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let Q := Finset.univ.sup q₀
  refine ⟨d * Q, fun n hn ↦ ?_⟩
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  let q : ℕ := n / d
  have hq : Q ≤ q := (Nat.le_div_iff_mul_le hd).mpr (by linarith)
  have hqr : q₀ r ≤ q := (Finset.le_sup (f := q₀) (Finset.mem_univ r)).trans hq
  obtain ⟨Φ⟩ := nonempty_tensor_tensorPow_iso F L M hM (Nat.div_add_mod n d)
  choose t' ht' using hext r q hqr
  refine ⟨k r, fun j ↦ Φ.hom.app ⊤ (t' j), top_unique fun z _ ↦ ?_⟩
  let e₁ : Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r, U) ≃ₗ[Γ(X, U)]
      Γ((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
        TauCeti.tensorPow (M.obj : X.Modules) q, U) :=
    LinearEquiv.ofBijective
      (tmulRight (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r)
        (tensorPowSection (M.obj.presheaf.map (homOfLE (M.obj.nonvanishingLocus_le s)).op s) q))
      (bijective_tmulRight_tensorPowSection_of_le_nonvanishingLocus
        (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) _
        (by rw [nonvanishingLocus_map]; exact le_inf le_rfl le_rfl) q)
  let e₂ := sectionsLinearEquiv Φ U
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, U)).mp
    (hspan r ▸ Submodule.mem_top (x := e₁.symm (e₂.symm z)))
  refine (Submodule.mem_span_range_iff_exists_fun Γ(X, U)).mpr ⟨c, ?_⟩
  have hz : z = e₂ (e₁ (∑ j, c j • g r j)) := by rw [hc, e₁.apply_symm_apply, e₂.apply_symm_apply]
  rw [hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [LinearEquiv.map_smul, LinearEquiv.map_smul]
  congr 1
  have hle : U.leTop = homOfLE (M.obj.nonvanishingLocus_le s) := rfl
  have hnat : Φ.hom.app U
      (((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
        TauCeti.tensorPow (M.obj : X.Modules) q).presheaf.map U.leTop.op (t' j)) =
      (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n).presheaf.map U.leTop.op
        (Φ.hom.app ⊤ (t' j)) :=
    Φ.hom.mapPresheaf.naturality_apply U.leTop.op (t' j)
  dsimp only
  rw [sectionsLinearEquiv_apply, LinearEquiv.ofBijective_apply, ← ht' j, ← hle, hnat]

/-- **Serre's global generation theorem** (EGA II, Proposition 4.5.5; Stacks, Tag 01Q3): on a
quasi-separated scheme `X`, let `a` be an ample line-bundle class and `F` a quasi-coherent
`𝒪_X`-module of finite type. There exists `n₀ : ℕ` such that for every `n ≥ n₀` and every line
bundle `K` of class `aⁿ`, `F ⊗ K` is generated by finitely many global sections. -/
theorem IsAmple.exists_forall_ge_generatingSections [QuasiSeparatedSpace X]
    {a : LineBundleClass X} (ha : a.IsAmple) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = a ^ n →
      ∃ G : (F ⊗ (K.obj : X.Modules)).GeneratingSections, G.IsFiniteType := by
  have := ha.compactSpace
  obtain ⟨L, rfl⟩ := mk_surjective a
  have hLqc : (L.obj : X.Modules).IsQuasicoherent := L.isQuasicoherent_obj
  choose dx hdx hMx using fun x : X ↦ ha.exists_pos_forall_mk_eq x
  let Mx (x : X) : InvertibleSheaf X := L.tensorPow (dx x)
  choose sx hsx hAffx using fun x : X ↦ hMx x (Mx x) (mk_tensorPow L (dx x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ ((Mx x).obj.nonvanishingLocus (sx x) : Set X))
    (fun x ↦ ((Mx x).obj.nonvanishingLocus (sx x)).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hsx x⟩)
  let U (i : t) : X.Opens := (Mx i).obj.nonvanishingLocus (sx i)
  have hcover : ⨆ i : t, U i = ⊤ := top_unique fun x _ ↦ by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  choose n₀ hn₀ using fun i : t ↦
    exists_forall_ge_finite_global_span F L (Mx i) (hdx i) (mk_tensorPow L (dx i)) (sx i) (hAffx i)
  refine ⟨t.attach.sup n₀, fun n hn K hK ↦ ?_⟩
  choose ki σi hspani using fun i : t ↦
    hn₀ i n ((Finset.le_sup (f := n₀) (Finset.mem_attach t i)).trans hn)
  let σ : (Σ i : t, Fin (ki i)) → Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n, ⊤) :=
    fun p ↦ σi p.1 p.2
  have hspan (i : t) : Submodule.span Γ(X, U i)
      (Set.range fun p : Σ i : t, Fin (ki i) ↦
        (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n).presheaf.map (U i).leTop.op (σ p)) = ⊤ :=
    top_unique (by
      rw [← hspani i]
      refine Submodule.span_mono ?_
      rintro _ ⟨j, rfl⟩
      exact ⟨⟨i, j⟩, rfl⟩)
  let G₀ := generatingSectionsOfSpanEqTop (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n)
    (fun i : t ↦ hAffx i) hcover σ hspan
  have hG₀ : G₀.IsFiniteType := inferInstance
  obtain ⟨e⟩ := InvertibleSheaf.nonempty_iso_tensorPow_of_mk_eq hK
  let e' : (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n : SheafOfModules X.ringCatSheaf) ≅
      (F ⊗ (K.obj : X.Modules) : SheafOfModules X.ringCatSheaf) :=
    { hom := (whiskerLeftIso F e.symm).hom
      inv := (whiskerLeftIso F e.symm).inv
      hom_inv_id := (whiskerLeftIso F e.symm).hom_inv_id
      inv_hom_id := (whiskerLeftIso F e.symm).inv_hom_id }
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e' G₀, { finite := hG₀.finite }⟩

/-- All sufficiently high powers of an ample line-bundle class on a quasi-separated scheme are
globally generated. -/
theorem IsAmple.exists_forall_ge_isGloballyGenerated [QuasiSeparatedSpace X]
    {a : LineBundleClass X} (ha : a.IsAmple) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = a ^ n →
      K.IsGloballyGenerated := by
  have : (𝟙_ X.Modules : X.Modules).IsFinitePresentation :=
    (TauCeti.AlgebraicGeometry.InvertibleSheaf.trivial X).property.isFinitePresentation |>
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
        (TauCeti.AlgebraicGeometry.InvertibleSheaf.trivialObjIsoUnit X)
  obtain ⟨n₀, hn₀⟩ := ha.exists_forall_ge_generatingSections (𝟙_ X.Modules)
  refine ⟨n₀, fun n hn K hK ↦
    InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr ?_⟩
  obtain ⟨G, -⟩ := hn₀ n hn K hK
  let e : ((𝟙_ X.Modules : X.Modules) ⊗ (K.obj : X.Modules) : SheafOfModules X.ringCatSheaf) ≅
      K.obj :=
    { hom := (λ_ (K.obj : X.Modules)).hom
      inv := (λ_ (K.obj : X.Modules)).inv
      hom_inv_id := (λ_ (K.obj : X.Modules)).hom_inv_id
      inv_hom_id := (λ_ (K.obj : X.Modules)).inv_hom_id }
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e G⟩

/-- **Quotient presentation by negative ample twists** (Hartshorne, Corollary II.5.18): on a
quasi-separated scheme `X`, let `a` be an ample line-bundle class and `F` a quasi-coherent
`𝒪_X`-module of finite type. There exists `n₀ : ℕ` such that for every `n ≥ n₀` and every line
bundle `K` of class `(aⁿ)⁻¹`, `F` is a quotient of a finite biproduct of copies of `K`. -/
theorem IsAmple.exists_forall_ge_epi_biproduct [QuasiSeparatedSpace X]
    {a : LineBundleClass X} (ha : a.IsAmple) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = (a ^ n)⁻¹ →
      ∃ (k : ℕ) (p : (⨁ fun _ : Fin k ↦ (K.obj : X.Modules)) ⟶ F), Epi p := by
  obtain ⟨n₀, hn₀⟩ := ha.exists_forall_ge_generatingSections F
  refine ⟨n₀, fun n hn K hK ↦ ?_⟩
  obtain ⟨P, hP⟩ := mk_surjective (a ^ n)
  obtain ⟨G, hG⟩ := hn₀ n hn P hP
  have hPK : LineBundleClass.mk (InvertibleSheaf.tensorProduct P K) = 1 := by
    rw [mk_tensorProduct, hP, hK, mul_inv_cancel]
  obtain ⟨e₀⟩ := mk_eq_one_iff.mp hPK
  exact exists_epi_biproduct_of_generatingSections
    ((InvertibleSheaf.tensorProductObjIso P K).symm ≪≫ isoOfSheafIso X e₀) G

end LineBundleClass

end TauCeti.AlgebraicGeometry

end
