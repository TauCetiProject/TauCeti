/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Opens
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import TauCeti.Algebra.Module.LocalizedModule.Exact
import TauCeti.Algebra.Module.LocalizedModule.Map
import TauCeti.AlgebraicGeometry.Cohomology.Affine
import TauCeti.AlgebraicGeometry.Modules.Localization
import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-!
# Cohomology of quasi-coherent sheaves commutes with localization

Let `M` be a quasi-coherent sheaf on a scheme `X`, let `g` be a global function on `X` and let `U`
be a quasi-compact and quasi-separated open subset of `X`. Then the restriction map
`Hⁿ(U, M) ⟶ Hⁿ(U ∩ D(g), M)` is the localization at the powers of `g`, in every degree `n`
(`Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_inf_basicOpen`), where `Hⁿ(U, M)` is a
module over the global functions on `X` (`Scheme.Modules.cohomologyOnModule`). On a quasi-compact
quasi-separated scheme this says `Hⁿ(X_g, M) = Hⁿ(X, M)_g`
(`Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_basicOpen`).

Applied to the preimages `f⁻¹ V` of the affine opens `V` of the base of a quasi-compact
quasi-separated morphism `f`, this is the statement that the presheaf `V ↦ Hⁿ(f⁻¹ V, M)` is, on the
basic opens of an affine open, the presheaf of a quasi-coherent sheaf: it is the input for the
quasi-coherence of the higher direct images `Rⁿ f_* M` and for their computation over affine opens
of the base.

The proof follows the vanishing argument of Stacks, Section 30.4, with localization in place of
vanishing. In degree zero this is the qcqs lemma for sections of quasi-coherent sheaves,
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`, and in positive
degrees both sides vanish on an affine open `U`. The Mayer-Vietoris sequences of a cover
`U ∪ V` and of `(U ∩ D(g)) ∪ (V ∩ D(g))` form a commutative ladder of modules
(`CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ_naturality_left`), so by the five
lemma for localizations (`IsLocalizedModule.of_exact`) the restriction map of `U ∪ V` is a
localization in degree `n + 1` once those of `U`, `V` and `U ∩ V` are in degrees `n` and `n + 1`
(`Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_sup_succ`). A quasi-compact open of an
affine open is a finite union of basic opens, whose intersections are again basic opens, and a
quasi-compact quasi-separated open is a finite union of affine opens whose intersections are
quasi-compact opens of affine opens; induction on the number of opens concludes.

## Main declarations

* `Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_sup_succ`: the localization property of
  restriction maps propagates along the Mayer-Vietoris sequence, for arbitrary coefficients;
* `Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_inf_basicOpen`: for quasi-coherent `M`
  and a quasi-compact quasi-separated open `U`, `Hⁿ(U ∩ D(g), M)` is the localization of
  `Hⁿ(U, M)` at the powers of `g`;
* `Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_basicOpen`: on a quasi-compact
  quasi-separated scheme, `Hⁿ(X_g, M)` is the localization of `Hⁿ(X, M)` at the powers of `g`;
* `Scheme.Modules.isLocalizedModule_cohomologyOnResLinear_comp_cohomologyOnTopLinearEquiv_symm`:
  the same statement for the cohomology `Scheme.Modules.Cohomology M n` of the scheme.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, proof of Proposition III.8.5.
* The Stacks Project, Section 30.4 (tag 01XH).
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules TauCeti.CategoryTheory

variable {X : Scheme.{u}} (M : X.Modules)

section MayerVietoris

/-- The difference `Hⁿ(U, M) × Hⁿ(V, M) ⟶ Hⁿ(U ⊓ V, M)` of the two restriction maps. -/
private noncomputable abbrev resDiff (U V : X.Opens) (n : ℕ) :
    cohomologyOn M n U × cohomologyOn M n V →ₗ[Γ(X, ⊤)] cohomologyOn M n (U ⊓ V) :=
  (cohomologyOnResLinear M n inf_le_left).coprod (-cohomologyOnResLinear M n inf_le_right)

/-- The pair `Hⁿ(U ⊔ V, M) ⟶ Hⁿ(U, M) × Hⁿ(V, M)` of the two restriction maps. -/
private noncomputable abbrev resPair (U V : X.Opens) (n : ℕ) :
    cohomologyOn M n (U ⊔ V) →ₗ[Γ(X, ⊤)] cohomologyOn M n U × cohomologyOn M n V :=
  (cohomologyOnResLinear M n le_sup_left).prod (cohomologyOnResLinear M n le_sup_right)

private lemma resDiff_apply (U V : X.Opens) (n : ℕ) (p : cohomologyOn M n U × cohomologyOn M n V) :
    resDiff M U V n p = (Opens.mayerVietorisSquare U V).fromBiprod
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n
        ((AddCommGrpCat.biprodIsoProd _ _).inv p) := by
  obtain ⟨a, b⟩ := p
  rw [LinearMap.coprod_apply, LinearMap.neg_apply, cohomologyOnResLinear_apply,
    cohomologyOnResLinear_apply, ← sub_eq_add_neg]
  exact ((Opens.mayerVietorisSquare U V).fromBiprod_biprodIsoProd_inv_apply _ a b).symm

private lemma toBiprod_apply_eq (U V : X.Opens) (n : ℕ) (y : cohomologyOn M n (U ⊔ V)) :
    (Opens.mayerVietorisSquare U V).toBiprod
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n y =
        (AddCommGrpCat.biprodIsoProd _ _).inv (resPair M U V n y) := by
  have hp : resPair M U V n y =
      (cohomologyOnRes M n le_sup_left y, cohomologyOnRes M n le_sup_right y) :=
    Prod.ext (cohomologyOnResLinear_apply M n _ y) (cohomologyOnResLinear_apply M n _ y)
  rw [hp]
  exact (Opens.mayerVietorisSquare U V).toBiprod_apply _ y

/-- Under `AddCommGrpCat.biprodIsoProd`, the Mayer-Vietoris map out of the biproduct is
`resDiff`. -/
private lemma resDiff_comp_biprodIsoProd (U V : X.Opens) (n : ℕ) :
    (resDiff M U V n).toAddMonoidHom.comp
        (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.toAddMonoidHom =
      ((Opens.mayerVietorisSquare U V).fromBiprod
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n).hom :=
  AddMonoidHom.ext fun z ↦ (resDiff_apply M U V n _).trans
    (congrArg _ (Iso.hom_inv_id_apply (AddCommGrpCat.biprodIsoProd _ _) z))

/-- Under `AddCommGrpCat.biprodIsoProd`, the Mayer-Vietoris map into the biproduct is
`resPair`. -/
private lemma biprodIsoProd_comp_toBiprod (U V : X.Opens) (n : ℕ) :
    (resPair M U V n).toAddMonoidHom =
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.toAddMonoidHom.comp
        ((Opens.mayerVietorisSquare U V).toBiprod
          ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) n).hom :=
  AddMonoidHom.ext fun y ↦ (Iso.inv_hom_id_apply (AddCommGrpCat.biprodIsoProd _ _) _).symm.trans
    (congrArg _ (toBiprod_apply_eq M U V n y).symm)

private lemma exact_resDiff_mayerVietorisδLinear (U V : X.Opens) (n : ℕ) :
    Function.Exact (resDiff M U V n) (mayerVietorisδLinear M U V n (n + 1) rfl) :=
  Function.Exact.of_ladder_addEquiv_of_exact
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv (.refl _) (.refl _)
    (g₁₂ := (resDiff M U V n).toAddMonoidHom)
    (g₂₃ := (mayerVietorisδLinear M U V n (n + 1) rfl).toAddMonoidHom)
    (resDiff_comp_biprodIsoProd M U V n)
    (AddMonoidHom.ext fun x ↦ by exact mayerVietorisδLinear_apply M U V n (n + 1) rfl x)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      ((mayerVietorisSequence_exact M U V n (n + 1) rfl).exact' 1 2 3))

private lemma exact_mayerVietorisδLinear_resPair (U V : X.Opens) (n : ℕ) :
    Function.Exact (mayerVietorisδLinear M U V n (n + 1) rfl) (resPair M U V (n + 1)) :=
  Function.Exact.of_ladder_addEquiv_of_exact
    (.refl _) (.refl _) (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv
    (g₁₂ := (mayerVietorisδLinear M U V n (n + 1) rfl).toAddMonoidHom)
    (g₂₃ := (resPair M U V (n + 1)).toAddMonoidHom)
    (AddMonoidHom.ext fun x ↦ by exact mayerVietorisδLinear_apply M U V n (n + 1) rfl x)
    (biprodIsoProd_comp_toBiprod M U V (n + 1))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      ((mayerVietorisSequence_exact M U V n (n + 1) rfl).exact' 2 3 4))

private lemma exact_resPair_resDiff (U V : X.Opens) (n : ℕ) :
    Function.Exact (resPair M U V n) (resDiff M U V n) :=
  Function.Exact.of_ladder_addEquiv_of_exact
    (.refl _) (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv (.refl _)
    (g₁₂ := (resPair M U V n).toAddMonoidHom) (g₂₃ := (resDiff M U V n).toAddMonoidHom)
    -- Elaborating the squares after the equivalences avoids a costly unification.
    (by exact biprodIsoProd_comp_toBiprod M U V n) (by exact resDiff_comp_biprodIsoProd M U V n)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      ((mayerVietorisSequence_exact M U V n (n + 1) rfl).exact' 0 1 2))

private lemma resDiff_comp_prodMap (n : ℕ) {U V U' V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V) :
    resDiff M U' V' n ∘ₗ (cohomologyOnResLinear M n hU).prodMap (cohomologyOnResLinear M n hV) =
      cohomologyOnResLinear M n (inf_le_inf hU hV) ∘ₗ resDiff M U V n := by
  refine LinearMap.ext fun p ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.coprod_apply,
    LinearMap.neg_apply, cohomologyOnResLinear_apply, map_add, map_neg, cohomologyOnRes_comp_apply]

/-- **Localization propagates along the Mayer-Vietoris sequence.** Let `U' ≤ U` and `V' ≤ V` be
open subsets and `S` a submonoid of the global functions. If the restriction maps from `U`, `V`
and `U ⊓ V` to `U'`, `V'` and `U' ⊓ V'` are localizations at `S` in degrees `n` and `n + 1`, then
so is the restriction map `Hⁿ⁺¹(U ⊔ V, M) ⟶ Hⁿ⁺¹(U' ⊔ V', M)`. -/
theorem isLocalizedModule_cohomologyOnResLinear_sup_succ (S : Submonoid Γ(X, ⊤))
    {U V U' V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V) (n : ℕ)
    (hU₀ : IsLocalizedModule S (cohomologyOnResLinear M n hU))
    (hV₀ : IsLocalizedModule S (cohomologyOnResLinear M n hV))
    (hUV₀ : IsLocalizedModule S (cohomologyOnResLinear M n (inf_le_inf hU hV)))
    (hU₁ : IsLocalizedModule S (cohomologyOnResLinear M (n + 1) hU))
    (hV₁ : IsLocalizedModule S (cohomologyOnResLinear M (n + 1) hV))
    (hUV₁ : IsLocalizedModule S (cohomologyOnResLinear M (n + 1) (inf_le_inf hU hV))) :
    IsLocalizedModule S (cohomologyOnResLinear M (n + 1) (sup_le_sup hU hV)) := by
  -- Restriction from the square of `U` and `V` to that of `U'` and `V'`.
  let φ : (Opens.mayerVietorisSquare U' V').toSquare ⟶ (Opens.mayerVietorisSquare U V).toSquare :=
    { τ₁ := homOfLE (inf_le_inf hU hV)
      τ₂ := homOfLE hU
      τ₃ := homOfLE hV
      τ₄ := homOfLE (sup_le_sup hU hV) }
  have hδ := (Opens.mayerVietorisSquare U V).δ_naturality_left
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) φ n (n + 1) rfl
  refine IsLocalizedModule.of_exact S (i₁ := (cohomologyOnResLinear M n hU).prodMap
      (cohomologyOnResLinear M n hV)) (i₄ := (cohomologyOnResLinear M (n + 1) hU).prodMap
      (cohomologyOnResLinear M (n + 1) hV)) (resDiff_comp_prodMap M n hU hV) ?_ ?_
    (resDiff_comp_prodMap M (n + 1) hU hV) (exact_resDiff_mayerVietorisδLinear M U V n)
    (exact_mayerVietorisδLinear_resPair M U V n) (exact_resPair_resDiff M U V (n + 1))
    (exact_resDiff_mayerVietorisδLinear M U' V' n) (exact_mayerVietorisδLinear_resPair M U' V' n)
    (exact_resPair_resDiff M U' V' (n + 1))
  · ext x
    simp only [LinearMap.comp_apply, mayerVietorisδLinear_apply, cohomologyOnResLinear_apply]
    exact (ConcreteCategory.congr_hom hδ x).symm
  · ext x <;> simp

end MayerVietoris

section Localization

variable [M.IsQuasicoherent] (g : Γ(X, ⊤))

/-- In degree zero, the restriction from a quasi-compact quasi-separated open `U` to `U ⊓ D(g)` is
a localization: this is the qcqs lemma for the sections of `M`. -/
private lemma isLocalizedModule_cohomologyOnResLinear_zero {U W : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (h : W ≤ U)
    (hW : W = U ⊓ X.basicOpen g) :
    IsLocalizedModule (.powers g) (cohomologyOnResLinear M 0 h) := by
  let σ : Γ(X, ⊤) →+* Γ(X, U) := (X.presheaf.map U.leTop.op).hom
  obtain rfl : W = X.basicOpen (σ g) := hW.trans (X.basicOpen_res g U.leTop.op).symm
  have : IsLocalizedModule ((Submonoid.powers g).map σ) (M.basicOpenRestrict (σ g)) := by
    rw [Submonoid.map_powers]
    exact M.isLocalizedModule_basicOpenRestrict_of_qcqs hU hU' (σ g)
  -- The target map is semilinear along `σ`, since `Γ(X, U)` acts on sections over
  -- `X.basicOpen (σ g)` through restriction.
  refine IsLocalizedModule.of_bijective_semilinearMap _ _ (M.basicOpenRestrict (σ g))
    (cohomologyOnZeroSemilinearMap M U)
    { toFun := cohomologyOnZeroEquiv M _
      map_add' := map_add _
      map_smul' := fun r x ↦ ?_ }
    (cohomologyOnZeroSemilinearMap_bijective M U) (cohomologyOnZeroEquiv M _).bijective fun x ↦ ?_
  · rw [cohomologyOnZeroEquiv_smul, basicOpen_smul_def, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl
  · simp only [LinearMap.coe_mk, AddHom.coe_mk, cohomologyOnResLinear_apply,
      cohomologyOnZeroSemilinearMap_apply]
    rw [cohomologyOnZeroEquiv_cohomologyOnRes, basicOpenRestrict_apply]

/-- The restriction maps from `U` to `U ⊓ D(g)` are localizations at the powers of `g` in every
degree. -/
private def LocalizesAt (U : X.Opens) : Prop :=
  ∀ (W : X.Opens) (h : W ≤ U), W = U ⊓ X.basicOpen g → ∀ n,
    IsLocalizedModule (.powers g) (cohomologyOnResLinear M n h)

private lemma localizesAt_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) :
    LocalizesAt M g U := by
  rintro W h hW (_ | n)
  · exact isLocalizedModule_cohomologyOnResLinear_zero M g hU.isCompact hU.isQuasiSeparated h hW
  · -- In positive degrees both sides vanish, since `U` and `U ⊓ D(g)` are affine.
    have hW' : IsAffineOpen W := by
      rw [hW, ← X.basicOpen_res g U.leTop.op]
      exact hU.basicOpen _
    have := subsingleton_cohomologyOn_succ_of_isAffineOpen M hU n
    have := subsingleton_cohomologyOn_succ_of_isAffineOpen M hW' n
    exact IsLocalizedModule.of_subsingleton _ _

private lemma localizesAt_sup {U V : X.Opens} (hUV : IsCompact ((U ⊔ V : X.Opens) : Set X))
    (hUV' : IsQuasiSeparated ((U ⊔ V : X.Opens) : Set X)) (hU : LocalizesAt M g U)
    (hV : LocalizesAt M g V) (hUV₀ : LocalizesAt M g (U ⊓ V)) : LocalizesAt M g (U ⊔ V) := by
  rintro W h hW (_ | n)
  · exact isLocalizedModule_cohomologyOnResLinear_zero M g hUV hUV' h hW
  · obtain rfl : W = U ⊓ X.basicOpen g ⊔ V ⊓ X.basicOpen g := hW.trans (inf_sup_right _ _ _)
    have hD : U ⊓ X.basicOpen g ⊓ (V ⊓ X.basicOpen g) = U ⊓ V ⊓ X.basicOpen g := by
      rw [inf_inf_inf_comm, inf_idem]
    exact isLocalizedModule_cohomologyOnResLinear_sup_succ M _ inf_le_left inf_le_left n
      (hU _ _ rfl n) (hV _ _ rfl n) (hUV₀ _ _ hD n) (hU _ _ rfl (n + 1)) (hV _ _ rfl (n + 1))
      (hUV₀ _ _ hD (n + 1))

/-- Finite unions of basic opens of an affine open. -/
private lemma localizesAt_finset_sup {U : X.Opens} (hU : IsAffineOpen U) {ι : Type*}
    (s : Finset ι) (f : ι → Γ(X, U)) :
    IsCompact ((s.sup fun i ↦ X.basicOpen (f i) : X.Opens) : Set X) ∧
      LocalizesAt M g (s.sup fun i ↦ X.basicOpen (f i)) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨isCompact_empty, localizesAt_of_isAffineOpen M g (isAffineOpen_bot X)⟩
  | insert a s _ ih =>
    rw [Finset.sup_insert]
    obtain ⟨hc, hs⟩ := ih f
    have ha := hU.basicOpen (f a)
    have hc' : IsCompact ((X.basicOpen (f a) ⊔ s.sup fun i ↦ X.basicOpen (f i) : X.Opens) :
        Set X) := by
      rw [Opens.coe_sup]
      exact ha.isCompact.union hc
    refine ⟨hc', localizesAt_sup M g hc' (hU.isQuasiSeparated.of_subset ?_)
      (localizesAt_of_isAffineOpen M g ha) hs ?_⟩
    · exact sup_le (X.basicOpen_le _) (Finset.sup_le fun i _ ↦ X.basicOpen_le _)
    · -- `D(f a) ⊓ D(f i) = D(f a * f i)`
      rw [Finset.sup_inf_distrib_left]
      simpa only [Scheme.basicOpen_mul] using (ih fun i ↦ f a * f i).2

/-- Quasi-compact opens of an affine open. -/
private lemma localizesAt_of_le_isAffineOpen {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsCompact (W : Set X)) (hWU : W ≤ U) : LocalizesAt M g W := by
  -- Cover `W` by finitely many basic opens of `U` contained in `W`.
  obtain ⟨s, hsW⟩ := hU.exists_finset_sup_basicOpen_eq hW hWU
  rw [← hsW]
  exact (localizesAt_finset_sup M g hU s fun i ↦ i.1).2

private lemma localizesAt_of_isCompact {U : X.Opens} (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) : LocalizesAt M g U := by
  revert hU'
  refine compact_open_induction_on (P := fun U ↦ IsQuasiSeparated (U : Set X) → LocalizesAt M g U)
    U hU (fun _ ↦ localizesAt_of_isAffineOpen M g (isAffineOpen_bot X))
    fun W hW U ih hWU' ↦ ?_
  have hc : IsCompact ((W ⊔ U.1 : X.Opens) : Set X) := by
    rw [Opens.coe_sup]
    exact hW.union U.2.isCompact
  -- By quasi-separation, `W ⊓ U` is a quasi-compact open of the affine open `U`.
  exact localizesAt_sup M g hc hWU' (ih (hWU'.of_subset Set.subset_union_left))
    (localizesAt_of_isAffineOpen M g U.2) (localizesAt_of_le_isAffineOpen M g U.2
      (hWU' _ _ Set.subset_union_left W.isOpen hW Set.subset_union_right U.1.isOpen
        U.2.isCompact) inf_le_right)

/-- **Cohomology of quasi-coherent sheaves commutes with localization.** Let `M` be a
quasi-coherent sheaf on a scheme `X`, `g` a global function and `U` a quasi-compact and
quasi-separated open subset. Then the restriction map `Hⁿ(U, M) ⟶ Hⁿ(U ⊓ D(g), M)` is the
localization at the powers of `g`, for every `n`. -/
theorem isLocalizedModule_cohomologyOnResLinear_inf_basicOpen {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (n : ℕ) :
    IsLocalizedModule (.powers g)
      (cohomologyOnResLinear M n (inf_le_left : U ⊓ X.basicOpen g ≤ U)) :=
  localizesAt_of_isCompact M g hU hU' _ _ rfl n

/-- **Cohomology of quasi-coherent sheaves commutes with localization.** On a quasi-compact and
quasi-separated scheme `X`, for a quasi-coherent sheaf `M` and a global function `g`, the
restriction map `Hⁿ(X, M) ⟶ Hⁿ(X_g, M)` is the localization at the powers of `g`, for every `n`.
Here `Hⁿ(X, M)` is the cohomology of the open subset `⊤`. -/
theorem isLocalizedModule_cohomologyOnResLinear_basicOpen [CompactSpace X]
    [QuasiSeparatedSpace X] (n : ℕ) :
    IsLocalizedModule (.powers g) (cohomologyOnResLinear M n (le_top : X.basicOpen g ≤ ⊤)) :=
  localizesAt_of_isCompact M g isCompact_univ isQuasiSeparated_univ _ _ (top_inf_eq _).symm n

/-- **Cohomology of quasi-coherent sheaves commutes with localization.** On a quasi-compact and
quasi-separated scheme `X`, for a quasi-coherent sheaf `M` and a global function `g`, the
restriction map `Hⁿ(X, M) ⟶ Hⁿ(X_g, M)` from the cohomology `Scheme.Modules.Cohomology M n` of the
scheme is the localization at the powers of `g`, for every `n`. -/
theorem isLocalizedModule_cohomologyOnResLinear_comp_cohomologyOnTopLinearEquiv_symm
    [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ) :
    IsLocalizedModule (.powers g) (cohomologyOnResLinear M n (le_top : X.basicOpen g ≤ ⊤) ∘ₗ
      (cohomologyOnTopLinearEquiv M n).symm.toLinearMap) :=
  have := isLocalizedModule_cohomologyOnResLinear_basicOpen M g n
  inferInstance

end Localization

end AlgebraicGeometry.Scheme.Modules
