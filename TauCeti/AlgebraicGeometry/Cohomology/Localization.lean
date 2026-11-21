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
import TauCeti.AlgebraicGeometry.Scheme.Induction
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
      (cohomologyOnResLinear M (n + 1) hV)) (mayerVietorisFromProdLinear_comp_prodMap M n hU hV)
    ?_ ?_ (mayerVietorisFromProdLinear_comp_prodMap M (n + 1) hU hV)
    (exact_mayerVietorisFromProdLinear_mayerVietorisδLinear M U V n)
    (exact_mayerVietorisδLinear_mayerVietorisToProdLinear M U V n)
    (exact_mayerVietorisToProdLinear_mayerVietorisFromProdLinear M U V (n + 1))
    (exact_mayerVietorisFromProdLinear_mayerVietorisδLinear M U' V' n)
    (exact_mayerVietorisδLinear_mayerVietorisToProdLinear M U' V' n)
    (exact_mayerVietorisToProdLinear_mayerVietorisFromProdLinear M U' V' (n + 1))
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

private lemma localizesAt_of_isCompact {U : X.Opens} (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) : LocalizesAt M g U := by
  refine Scheme.Opens.induction_on_isCompact_isQuasiSeparated U hU hU'
    (fun _ h ↦ localizesAt_of_isAffineOpen M g h) ?_
  intro V W hV hW hVW hPV hPW hPVW
  exact localizesAt_sup M g (hV.union hW) hVW hPV hPW hPVW

/-- **Cohomology of quasi-coherent sheaves commutes with localization.** Let `M` be a
quasi-coherent sheaf on a scheme `X`, `g` a global function and `U` a quasi-compact and
quasi-separated open subset. Then the restriction map `Hⁿ(U, M) ⟶ Hⁿ(U ⊓ D(g), M)` is the
localization at the powers of `g`, for every `n`. The open `W` is arbitrary up to the equality
`W = U ⊓ D(g)`. -/
theorem isLocalizedModule_cohomologyOnResLinear_inf_basicOpen {U W : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (h : W ≤ U)
    (hW : W = U ⊓ X.basicOpen g) (n : ℕ) :
    IsLocalizedModule (.powers g) (cohomologyOnResLinear M n h) :=
  localizesAt_of_isCompact M g hU hU' W h hW n

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
