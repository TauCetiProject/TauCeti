/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import TauCeti.AlgebraicGeometry.Cohomology.Affine
import TauCeti.AlgebraicGeometry.Cohomology.Module.Opens
import TauCeti.AlgebraicGeometry.Scheme.Induction

/-!
# Cohomology of quasi-coherent modules commutes with filtered colimits

Let `K : J ⥤ X.Modules` be a filtered diagram of quasi-coherent sheaves of modules on a scheme `X`,
with colimit cocone `c`. For every quasi-compact quasi-separated open `U` of `X` and every `n`,
the cohomology `Hⁿ(U, -)` sends `c` to a colimit cocone of abelian groups
(`TauCeti.AlgebraicGeometry.Scheme.Modules.isColimitMapCoconeCohomologyOnFunctor`): the canonical
map `colim_j Hⁿ(U, K_j) ⟶ Hⁿ(U, colim_j K_j)` is an isomorphism. On a quasi-compact
quasi-separated scheme the same holds for `Hⁿ(X, -)`
(`TauCeti.AlgebraicGeometry.Scheme.Modules.isColimitMapCoconeCohomologyFunctor`).

The proof is a Mayer-Vietoris induction on the number of affine opens covering `U`
(`AlgebraicGeometry.Scheme.Opens.induction_on_isCompact_isQuasiSeparated`), as for flat base
change. Since `J` is filtered, a cocone of abelian groups is a colimit exactly when every element
of its point comes from some `K_j`, and an element of some `K_j` that maps to zero already
vanishes in some `K_k`. On an affine open, `H⁰` is the module of sections, which commutes with all
colimits of quasi-coherent sheaves (`TauCeti.AlgebraicGeometry.isColimitMapCoconeSectionsFunctor`),
and the higher cohomology of every quasi-coherent sheaf vanishes. Both conditions then pass from
`U`, `V` and `U ⊓ V` to `U ⊔ V` by a diagram chase in the Mayer-Vietoris sequences, which are
natural in the coefficient sheaf; in degree zero the sheaf condition replaces the missing
connecting map.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.Modules.isColimitMapCoconeCohomologyOnFunctor`: on a
  quasi-compact quasi-separated open, `Hⁿ(U, -)` preserves filtered colimits of quasi-coherent
  sheaves;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.isColimitMapCoconeCohomologyFunctor`: on a
  quasi-compact quasi-separated scheme, `Hⁿ(X, -)` preserves filtered colimits of quasi-coherent
  sheaves.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.2.9 (on a
  Noetherian space, for all abelian sheaves).
* The Stacks Project, Lemma 30.6.1 (tag 07TB), and Lemma 30.4.1 (tag 08DR) for the
  Mayer-Vietoris induction principle.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme.Modules

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section FilteredColimit

variable {J : Type u} [SmallCategory J] [IsFiltered J] {K : J ⥤ X.Modules} {M : X.Modules}
  (ι : ∀ j, K.obj j ⟶ M)

/-- The elementwise form, for a filtered diagram `K` and a compatible family `ι` of morphisms into
`M`, of `Hⁿ(U, M)` being the colimit of the `Hⁿ(U, K_j)`: every class over `U` with coefficients
in `M` comes from some `K_j`, and a class of `K_j` which maps to zero in `M` already vanishes in
some `K_k`. -/
private structure IsColimitOn (n : ℕ) (U : X.Opens) : Prop where
  surj (y : cohomologyOn M n U) : ∃ j x, cohomologyOnMap (ι j) n U x = y
  inj (j : J) (x : cohomologyOn (K.obj j) n U) : cohomologyOnMap (ι j) n U x = 0 →
    ∃ (k : J) (f : j ⟶ k), cohomologyOnMap (K.map f) n U x = 0

variable {ι}

omit [IsFiltered J] in
/-- Mapping a class of `K_j` to `K_k` does not change its image in `M`. -/
private lemma cohomologyOnMap_cohomologyOnMap_map
    (hι : ∀ {j k : J} (f : j ⟶ k), K.map f ≫ ι k = ι j) {j k : J} (f : j ⟶ k) (n : ℕ)
    (U : X.Opens) (x : cohomologyOn (K.obj j) n U) :
    cohomologyOnMap (ι k) n U (cohomologyOnMap (K.map f) n U x) =
      cohomologyOnMap (ι j) n U x := by
  rw [← ConcreteCategory.comp_apply, ← cohomologyOnMap_comp, hι f]

/-- A cocone of abelian groups satisfying the elementwise criterion is a colimit. -/
private def IsColimitOn.isColimit {c : Cocone K} {n : ℕ} {U : X.Opens}
    (h : IsColimitOn (M := c.pt) c.ι.app n U) :
    IsColimit ((cohomologyOnFunctor X n U).mapCocone c) :=
  haveI : ReflectsColimitsOfShape J (forget AddCommGrpCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  isColimitOfReflects (forget AddCommGrpCat)
    (Types.FilteredColimit.isColimitOf' _ _ (fun y ↦ (h.surj y).imp fun _ ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩)
      fun j (x y : cohomologyOn (K.obj j) n U) hxy ↦ by
        obtain ⟨k, f, hf⟩ := h.inj j (x - y) (by
          rw [map_sub, sub_eq_zero]
          exact hxy)
        rw [map_sub, sub_eq_zero] at hf
        exact ⟨k, f, hf⟩)

/-- On an affine open, degree-zero cohomology commutes with colimits of quasi-coherent sheaves,
being the module of sections. -/
private lemma isColimitOn_zero_of_isAffineOpen (hK : ∀ j, (K.obj j).IsQuasicoherent)
    {c : Cocone K} (hc : IsColimit c) {U : X.Opens} (hU : IsAffineOpen U) :
    IsColimitOn (M := c.pt) c.ι.app 0 U := by
  have hs := isColimitOfPreserves (forget (ModuleCat Γ(X, U)))
    (isColimitMapCoconeSectionsFunctor hK hc hU)
  -- The cocone of sections, written with the components `φ.app U` of the morphisms.
  have hι (j : J) (s : Γ(K.obj j, U)) :
      ((forget (ModuleCat Γ(X, U))).mapCocone ((sectionsFunctor U).mapCocone c)).ι.app j s =
        Scheme.Modules.Hom.app (N := c.pt) (c.ι.app j) U s := rfl
  have hmap {j k : J} (f : j ⟶ k) (s : Γ(K.obj j, U)) :
      (K ⋙ sectionsFunctor U ⋙ forget (ModuleCat Γ(X, U))).map f s = (K.map f).app U s := rfl
  refine ⟨fun y ↦ ?_, fun j x hx ↦ ?_⟩
  · obtain ⟨j, (s : Γ(K.obj j, U)), hs⟩ :=
      Types.jointly_surjective_of_isColimit hs (cohomologyOnZeroEquiv c.pt U y)
    refine ⟨j, (cohomologyOnZeroEquiv (K.obj j) U).symm s,
      (cohomologyOnZeroEquiv c.pt U).injective ?_⟩
    rw [cohomologyOnZeroEquiv_naturality, AddEquiv.apply_symm_apply, ← hι, hs]
  · have h0 := congrArg (cohomologyOnZeroEquiv c.pt U) hx
    rw [cohomologyOnZeroEquiv_naturality, map_zero] at h0
    obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hs
      (cohomologyOnZeroEquiv (K.obj j) U x) 0).1
        ((hι j _).trans (h0.trans ((hι j 0).trans (map_zero
          (ConcreteCategory.hom (Scheme.Modules.Hom.app (N := c.pt) (c.ι.app j) U)))).symm))
    refine ⟨k, f, (cohomologyOnZeroEquiv (K.obj k) U).injective ?_⟩
    rw [cohomologyOnZeroEquiv_naturality, map_zero]
    exact (hmap f _).symm.trans (hf.trans ((hmap f 0).trans
      (map_zero (ConcreteCategory.hom ((K.map f).app U)))))

/-- On an affine open, the positive-degree cohomology of quasi-coherent sheaves vanishes, so it
commutes with colimits. -/
private lemma isColimitOn_succ_of_isAffineOpen (hK : ∀ j, (K.obj j).IsQuasicoherent)
    [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (n : ℕ) :
    IsColimitOn ι (n + 1) U := by
  have := subsingleton_cohomologyOn_succ_of_isAffineOpen M hU n
  refine ⟨fun y ↦ ⟨IsFiltered.nonempty.some, 0, Subsingleton.elim _ _⟩, fun j x _ ↦ ?_⟩
  have := hK j
  have := subsingleton_cohomologyOn_succ_of_isAffineOpen (K.obj j) hU n
  exact ⟨j, 𝟙 j, Subsingleton.elim _ _⟩

variable (hι : ∀ {j k : J} (f : j ⟶ k), K.map f ≫ ι k = ι j)
include hι

/-- **Surjectivity propagates along Mayer-Vietoris.** If the classes over `U` and over `V` all
come from the diagram, the classes over `U ⊓ V` that vanish in `M` vanish in the diagram, and the
classes over `U ⊔ V` restricting to zero on `U` and on `V` come from the diagram, then all classes
over `U ⊔ V` come from the diagram. -/
private lemma surj_sup {n : ℕ} {U V : X.Opens}
    (hU : ∀ y : cohomologyOn M n U, ∃ j x, cohomologyOnMap (ι j) n U x = y)
    (hV : ∀ y : cohomologyOn M n V, ∃ j x, cohomologyOnMap (ι j) n V x = y)
    (hUV : ∀ (j : J) (x : cohomologyOn (K.obj j) n (U ⊓ V)),
      cohomologyOnMap (ι j) n (U ⊓ V) x = 0 →
        ∃ (k : J) (f : j ⟶ k), cohomologyOnMap (K.map f) n (U ⊓ V) x = 0)
    (hker : ∀ y : cohomologyOn M n (U ⊔ V), mayerVietorisToProdLinear M U V n y = 0 →
      ∃ j x, cohomologyOnMap (ι j) n (U ⊔ V) x = y)
    (y : cohomologyOn M n (U ⊔ V)) :
    ∃ j x, cohomologyOnMap (ι j) n (U ⊔ V) x = y := by
  -- Lift the two restrictions of `y` to a common stage `k` of the diagram.
  obtain ⟨j₁, a, ha⟩ := hU (cohomologyOnRes M n le_sup_left y)
  obtain ⟨j₂, b, hb⟩ := hV (cohomologyOnRes M n le_sup_right y)
  obtain ⟨k, p, hp⟩ : ∃ (k : J) (p : cohomologyOn (K.obj k) n U × cohomologyOn (K.obj k) n V),
      Prod.map (cohomologyOnMap (ι k) n U) (cohomologyOnMap (ι k) n V) p =
        mayerVietorisToProdLinear M U V n y :=
    ⟨IsFiltered.max j₁ j₂, (cohomologyOnMap (K.map (IsFiltered.leftToMax j₁ j₂)) n U a,
      cohomologyOnMap (K.map (IsFiltered.rightToMax j₁ j₂)) n V b), by
        rw [Prod.map_apply, cohomologyOnMap_cohomologyOnMap_map hι,
          cohomologyOnMap_cohomologyOnMap_map hι, ha, hb, mayerVietorisToProdLinear_apply]⟩
  -- Their difference on `U ⊓ V` vanishes in `M`, hence at a later stage `l`.
  obtain ⟨l, g, hg⟩ := hUV k (mayerVietorisFromProdLinear (K.obj k) U V n p) (by
    rw [← mayerVietorisFromProdLinear_prodMap_cohomologyOnMap, hp,
      (exact_mayerVietorisToProdLinear_mayerVietorisFromProdLinear M U V n).apply_apply_eq_zero])
  -- So the image of `p` at stage `l` glues to a class `z` over `U ⊔ V`.
  obtain ⟨z, hz⟩ := (exact_mayerVietorisToProdLinear_mayerVietorisFromProdLinear (K.obj l) U V n
    (Prod.map (cohomologyOnMap (K.map g) n U) (cohomologyOnMap (K.map g) n V) p)).1 (by
      rw [mayerVietorisFromProdLinear_prodMap_cohomologyOnMap, hg])
  -- The class `y - z` restricts to zero on `U` and on `V`, so it comes from the diagram.
  obtain ⟨m, w, hw⟩ := hker (y - cohomologyOnMap (ι l) n (U ⊔ V) z) (by
    rw [map_sub, mayerVietorisToProdLinear_cohomologyOnMap, hz, ← hp, sub_eq_zero]
    ext <;> simp only [Prod.map_fst, Prod.map_snd, cohomologyOnMap_cohomologyOnMap_map hι])
  refine ⟨IsFiltered.max l m,
    cohomologyOnMap (K.map (IsFiltered.leftToMax l m)) n (U ⊔ V) z +
      cohomologyOnMap (K.map (IsFiltered.rightToMax l m)) n (U ⊔ V) w, ?_⟩
  rw [map_add, cohomologyOnMap_cohomologyOnMap_map hι, cohomologyOnMap_cohomologyOnMap_map hι, hw,
    add_sub_cancel]

/-- **Injectivity propagates along Mayer-Vietoris.** If the classes over `U` and over `V` that
vanish in `M` vanish in the diagram, and so do the classes over `U ⊔ V` restricting to zero on
`U` and on `V`, then so do all classes over `U ⊔ V`. -/
private lemma inj_sup {n : ℕ} {U V : X.Opens}
    (hU : ∀ (j : J) (x : cohomologyOn (K.obj j) n U), cohomologyOnMap (ι j) n U x = 0 →
      ∃ (k : J) (f : j ⟶ k), cohomologyOnMap (K.map f) n U x = 0)
    (hV : ∀ (j : J) (x : cohomologyOn (K.obj j) n V), cohomologyOnMap (ι j) n V x = 0 →
      ∃ (k : J) (f : j ⟶ k), cohomologyOnMap (K.map f) n V x = 0)
    (hker : ∀ (j : J) (x : cohomologyOn (K.obj j) n (U ⊔ V)),
      mayerVietorisToProdLinear (K.obj j) U V n x = 0 → cohomologyOnMap (ι j) n (U ⊔ V) x = 0 →
        ∃ (k : J) (f : j ⟶ k), cohomologyOnMap (K.map f) n (U ⊔ V) x = 0)
    (j : J) (x : cohomologyOn (K.obj j) n (U ⊔ V)) (hx : cohomologyOnMap (ι j) n (U ⊔ V) x = 0) :
    ∃ (k : J) (f : j ⟶ k), cohomologyOnMap (K.map f) n (U ⊔ V) x = 0 := by
  -- The restrictions of `x` to `U` and to `V` vanish at stages `k₁` and `k₂`.
  obtain ⟨k₁, f₁, hf₁⟩ := hU j (cohomologyOnRes _ n le_sup_left x) (by
    rw [cohomologyOnMap_cohomologyOnRes, hx, map_zero])
  obtain ⟨k₂, f₂, hf₂⟩ := hV j (cohomologyOnRes _ n le_sup_right x) (by
    rw [cohomologyOnMap_cohomologyOnRes, hx, map_zero])
  -- Both vanish along a common map `f₁ ≫ g₁ = f₂ ≫ g₂ : j ⟶ k`.
  obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span f₁ f₂
  have h₁ : cohomologyOnRes _ n le_sup_left
      (cohomologyOnMap (K.map (f₁ ≫ g₁)) n (U ⊔ V) x) = 0 := by
    rw [← cohomologyOnMap_cohomologyOnRes, K.map_comp, cohomologyOnMap_comp,
      ConcreteCategory.comp_apply, hf₁, map_zero]
  have h₂ : cohomologyOnRes _ n le_sup_right
      (cohomologyOnMap (K.map (f₁ ≫ g₁)) n (U ⊔ V) x) = 0 := by
    rw [hg, ← cohomologyOnMap_cohomologyOnRes, K.map_comp, cohomologyOnMap_comp,
      ConcreteCategory.comp_apply, hf₂, map_zero]
  obtain ⟨l, g, hg'⟩ := hker k _
    (by rw [mayerVietorisToProdLinear_apply, h₁, h₂, Prod.mk_zero_zero])
    (by rw [cohomologyOnMap_cohomologyOnMap_map hι, hx])
  refine ⟨l, (f₁ ≫ g₁) ≫ g, ?_⟩
  rw [K.map_comp, cohomologyOnMap_comp, ConcreteCategory.comp_apply, hg']

omit [IsFiltered J] hι in
/-- In degree `n + 1`, a class of `M` over `U ⊔ V` restricting to zero on `U` and on `V` is a
Mayer-Vietoris boundary, so it comes from the diagram when the classes over `U ⊓ V` do. -/
private lemma surj_ker_succ {n : ℕ} {U V : X.Opens}
    (hUV : ∀ y : cohomologyOn M n (U ⊓ V), ∃ j x, cohomologyOnMap (ι j) n (U ⊓ V) x = y)
    (y : cohomologyOn M (n + 1) (U ⊔ V)) (hy : mayerVietorisToProdLinear M U V (n + 1) y = 0) :
    ∃ j x, cohomologyOnMap (ι j) (n + 1) (U ⊔ V) x = y := by
  obtain ⟨w, rfl⟩ := (exact_mayerVietorisδLinear_mayerVietorisToProdLinear M U V n y).1 hy
  obtain ⟨j, w', rfl⟩ := hUV w
  exact ⟨j, mayerVietorisδ (K.obj j) U V n (n + 1) rfl w', by
    rw [mayerVietorisδLinear_apply, cohomologyOnMap_mayerVietorisδ]⟩

/-- In degree `n + 1`, a class of `K_j` over `U ⊔ V` restricting to zero on `U` and on `V` and
vanishing in `M` vanishes in some `K_k`, when the classes of `M` over `U` and over `V` come from
the diagram and the classes over `U ⊓ V` vanishing in `M` vanish in the diagram. -/
private lemma inj_ker_succ {n : ℕ} {U V : X.Opens}
    (hU : ∀ y : cohomologyOn M n U, ∃ j x, cohomologyOnMap (ι j) n U x = y)
    (hV : ∀ y : cohomologyOn M n V, ∃ j x, cohomologyOnMap (ι j) n V x = y)
    (hUV : ∀ (j : J) (x : cohomologyOn (K.obj j) n (U ⊓ V)),
      cohomologyOnMap (ι j) n (U ⊓ V) x = 0 →
        ∃ (k : J) (f : j ⟶ k), cohomologyOnMap (K.map f) n (U ⊓ V) x = 0)
    (j : J) (x : cohomologyOn (K.obj j) (n + 1) (U ⊔ V))
    (hx₀ : mayerVietorisToProdLinear (K.obj j) U V (n + 1) x = 0)
    (hx : cohomologyOnMap (ι j) (n + 1) (U ⊔ V) x = 0) :
    ∃ (k : J) (f : j ⟶ k), cohomologyOnMap (K.map f) (n + 1) (U ⊔ V) x = 0 := by
  -- `x` is the boundary of a class `w` over `U ⊓ V`, whose image in `M` is a difference of
  -- restrictions of classes over `U` and over `V`.
  obtain ⟨w, rfl⟩ := (exact_mayerVietorisδLinear_mayerVietorisToProdLinear _ U V n x).1 hx₀
  rw [mayerVietorisδLinear_apply, cohomologyOnMap_mayerVietorisδ] at hx
  obtain ⟨p, hp⟩ := (exact_mayerVietorisFromProdLinear_mayerVietorisδLinear M U V n _).1
    ((mayerVietorisδLinear_apply M U V n (n + 1) rfl _).trans hx)
  obtain ⟨ja, a, ha⟩ := hU p.1
  obtain ⟨jb, b, hb⟩ := hV p.2
  -- At a common stage `l`, the difference of `w` and that of the lifts vanishes in `M`.
  set l := IsFiltered.max₃ j ja jb
  let q := (cohomologyOnMap (K.map (IsFiltered.secondToMax₃ j ja jb)) n U a,
    cohomologyOnMap (K.map (IsFiltered.thirdToMax₃ j ja jb)) n V b)
  have hq : Prod.map (cohomologyOnMap (ι l) n U) (cohomologyOnMap (ι l) n V) q = p := by
    rw [Prod.map_apply, cohomologyOnMap_cohomologyOnMap_map hι,
      cohomologyOnMap_cohomologyOnMap_map hι, ha, hb]
  obtain ⟨m, g, hg⟩ := hUV l (cohomologyOnMap (K.map (IsFiltered.firstToMax₃ j ja jb)) n (U ⊓ V) w -
      mayerVietorisFromProdLinear (K.obj l) U V n q) (by
    rw [map_sub, cohomologyOnMap_cohomologyOnMap_map hι,
      ← mayerVietorisFromProdLinear_prodMap_cohomologyOnMap, hq, ← hp,
      mayerVietorisFromProdLinear_apply, sub_self])
  -- So the image of `w` at stage `m` is a difference of restrictions, with zero boundary.
  rw [map_sub, sub_eq_zero, ← mayerVietorisFromProdLinear_prodMap_cohomologyOnMap] at hg
  refine ⟨m, IsFiltered.firstToMax₃ j ja jb ≫ g, ?_⟩
  rw [mayerVietorisδLinear_apply, cohomologyOnMap_mayerVietorisδ, K.map_comp, cohomologyOnMap_comp,
    ConcreteCategory.comp_apply, hg]
  exact (mayerVietorisδLinear_apply _ U V n (n + 1) rfl _).symm.trans
    ((exact_mayerVietorisFromProdLinear_mayerVietorisδLinear _ U V n).apply_apply_eq_zero _)

end FilteredColimit

section Main

variable {J : Type u} [SmallCategory J] [IsFiltered J] {K : J ⥤ X.Modules}
  (hK : ∀ j, (K.obj j).IsQuasicoherent) {c : Cocone K} (hc : IsColimit c)

include hK hc in
/-- The elementwise criterion holds on every quasi-compact quasi-separated open, by
Mayer-Vietoris induction from the affine opens. -/
private lemma isColimitOn_of_isCompact_of_isQuasiSeparated {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (n : ℕ) :
    IsColimitOn (M := c.pt) c.ι.app n U := by
  have := isQuasicoherent_of_isColimit hK hc
  have hι {j k : J} (f : j ⟶ k) : K.map f ≫ c.ι.app k = c.ι.app j := c.w f
  refine Scheme.Opens.induction_on_isCompact_isQuasiSeparated
    (P := fun U ↦ ∀ n, IsColimitOn (M := c.pt) c.ι.app n U) U hU hU' ?_ ?_ n
  · rintro V hV (_ | n)
    · exact isColimitOn_zero_of_isAffineOpen hK hc hV
    · exact isColimitOn_succ_of_isAffineOpen hK hV n
  · rintro V W - - - hV hW hVW (_ | n)
    · -- In degree zero, a class restricting to zero on `V` and on `W` is zero.
      refine ⟨surj_sup hι (hV 0).surj (hW 0).surj (hVW 0).inj fun y hy ↦ ?_,
        inj_sup hι (hV 0).inj (hW 0).inj fun j x hx _ ↦ ?_⟩
      · exact ⟨IsFiltered.nonempty.some, 0, by
          rw [map_zero,
            (map_eq_zero_iff _ (mayerVietorisToProdLinear_zero_injective _ V W)).1 hy]⟩
      · exact ⟨j, 𝟙 j, by
          rw [(map_eq_zero_iff _ (mayerVietorisToProdLinear_zero_injective _ V W)).1 hx, map_zero]⟩
    · -- In degree `n + 1`, such a class is a Mayer-Vietoris boundary.
      exact ⟨surj_sup hι (hV (n + 1)).surj (hW (n + 1)).surj (hVW (n + 1)).inj
          (surj_ker_succ (hVW n).surj),
        inj_sup hι (hV (n + 1)).inj (hW (n + 1)).inj
          (inj_ker_succ hι (hV n).surj (hW n).surj (hVW n).inj)⟩

/-- **Cohomology commutes with filtered colimits of quasi-coherent sheaves.** For a filtered
diagram `K` of quasi-coherent sheaves of modules on a scheme `X` with colimit cocone `c`, and a
quasi-compact quasi-separated open `U`, the cohomology `Hⁿ(U, -)` sends `c` to a colimit cocone:
`Hⁿ(U, colim_j K_j)` is the colimit of the `Hⁿ(U, K_j)`. -/
def isColimitMapCoconeCohomologyOnFunctor {U : X.Opens} (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (n : ℕ) :
    IsColimit ((cohomologyOnFunctor X n U).mapCocone c) :=
  (isColimitOn_of_isCompact_of_isQuasiSeparated hK hc hU hU' n).isColimit

/-- **Cohomology commutes with filtered colimits of quasi-coherent sheaves.** For a filtered
diagram `K` of quasi-coherent sheaves of modules on a quasi-compact quasi-separated scheme `X`
with colimit cocone `c`, the cohomology `Hⁿ(X, -)` sends `c` to a colimit cocone:
`Hⁿ(X, colim_j K_j)` is the colimit of the `Hⁿ(X, K_j)`. -/
def isColimitMapCoconeCohomologyFunctor [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ) :
    IsColimit ((cohomologyFunctor X n).mapCocone c) :=
  IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
      (Sheaf.cohomologyPresheafEvaluationIsoFunctorH _ n isTerminalTop))
    (isColimitMapCoconeCohomologyOnFunctor hK hc (U := ⊤) isCompact_univ isQuasiSeparated_univ n)

end Main

end TauCeti.AlgebraicGeometry.Scheme.Modules
