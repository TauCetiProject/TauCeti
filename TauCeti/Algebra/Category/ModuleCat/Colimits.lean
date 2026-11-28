/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.CategoryTheory.Preadditive.SequenceDifference.Basic
public import TauCeti.LinearAlgebra.FreeModule.Filtration

import TauCeti.Algebra.Category.ModuleCat.FilteredColimits
import TauCeti.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Colimits of modules

The point of a colimit cocone in `ModuleCat R` is spanned by the images of the legs of the cocone:
the quotient by their span receives the zero morphism from every leg, so it vanishes by the
uniqueness part of the universal property. This lets elementwise properties that are stable under
linear images and finite sums pass to colimits.

Every `R`-module is the cokernel of a morphism between direct sums of copies of `R`. Hence a
natural transformation `α : F ⟶ G` between colimit-preserving functors out of `ModuleCat R` is an
isomorphism as soon as its component at `R` is: its components at direct sums of copies of `R`
are then isomorphisms, and so are its components at their cokernels.

This is the standard way of checking that a comparison map between two right exact
constructions on modules is invertible, for instance that the sheaf associated with a tensor
product of modules is the tensor product of the associated sheaves.

The colimit `M` of a sequence `F₀ → F₁ → F₂ → ⋯` of modules, with transition maps
`φₙ : Fₙ → Fₙ₊₁`, sits in the *telescope* short exact sequence

```text
0 → ⨁ₙ Fₙ → ⨁ₙ Fₙ → M → 0,
```

whose first map sends `x ∈ Fₙ` to `x - φₙ(x) ∈ Fₙ ⊕ Fₙ₊₁` and whose second map is induced by the
legs `Fₙ → M` of the colimit cocone. When the transition maps are injective, so are the legs, and
then `M` is free as soon as `F₀` and every cokernel `Fₙ₊₁ ⧸ φₙ(Fₙ)` are free: the images of
the legs form an exhaustive filtration of `M` by free subquotients. This is how freeness passes to
the homology of a space exhausted by subspaces whose successive relative homology is free.

## Main declarations

* `TauCeti.ModuleCat.iSup_range_eq_top_of_isColimit`: the ranges of the legs of a colimit cocone
  span its point.
* `TauCeti.ModuleCat.finite_coproduct_of_finite_support`: a coproduct of finite modules is finite if
  only finitely many summands are nonzero.
* `TauCeti.ModuleCat.isIso_of_isIso_app_self`: a natural transformation between
  colimit-preserving functors out of `ModuleCat R` whose component at `R` is invertible is an
  isomorphism.
* `TauCeti.ModuleCat.exists_injective_of_iso_sigma`: a module isomorphic to a nonempty coproduct
  of copies of `R` receives an injective linear map from `R`.
* `ModuleCat.telescopeDiff`: the map `⨁ₙ Fₙ → ⨁ₙ Fₙ`, `x ↦ x - φₙ(x)`, which is injective
  (`ModuleCat.telescopeDiff_injective`), and equals `F.sequenceDifference` under
  `coprodIsoDirectSum` (`ModuleCat.ofHom_telescopeDiff`).
* `ModuleCat.telescopeShortComplex`: the telescope sequence of a cocone over `F : ℕ ⥤ ModuleCat R`,
  short exact when the cocone is a colimit (`ModuleCat.shortExact_telescopeShortComplex`).
* `ModuleCat.injective_ι_app_of_isColimit`: the legs of a colimit of a sequence of injections are
  injective.
* `ModuleCat.free_of_isColimit`: a colimit of a sequence of injections with free cokernels,
  starting at a free module, is free.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341 (the telescope
  sequence).
-/

public section

namespace TauCeti

open CategoryTheory Limits DirectSum

universe u v w

namespace ModuleCat

open _root_.ModuleCat

variable {R : Type u} [Ring R] {D : Type v} [Category.{w} D]

-- The codomain `c.pt` is named because the leg `c.ι.app j` is typed with codomain
-- `((Functor.const J).obj c.pt).obj j`, which depends on `j` until it is unfolded.
/-- The ranges of the legs of a colimit cocone in `ModuleCat R` span its point. -/
theorem iSup_range_eq_top_of_isColimit {J : Type*} [Category* J] {F : J ⥤ ModuleCat.{v} R}
    {c : Cocone F} (hc : IsColimit c) :
    ⨆ j, LinearMap.range (Hom.hom (B := c.pt) (c.ι.app j)) = ⊤ := by
  set T : Submodule R c.pt := ⨆ j, LinearMap.range (Hom.hom (B := c.pt) (c.ι.app j))
  -- The projection onto `c.pt ⧸ T` vanishes on every leg, hence is zero.
  have h : ofHom T.mkQ = 0 := hc.hom_ext fun j ↦ by
    ext x
    simpa [Submodule.Quotient.mk_eq_zero] using
      Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self (c.ι.app j).hom x)
  rw [← Submodule.ker_mkQ T, show T.mkQ = 0 from congr_arg Hom.hom h, LinearMap.ker_zero]

/-- A natural transformation between colimit-preserving functors out of `ModuleCat R` is an
isomorphism as soon as its component at `R` is. -/
theorem isIso_of_isIso_app_self {F G : ModuleCat.{u} R ⥤ D}
    [PreservesColimitsOfSize.{u, u} F] [PreservesColimitsOfSize.{u, u} G] (α : F ⟶ G)
    [IsIso (α.app (ModuleCat.of R R))] : IsIso α := by
  classical
  -- The component at a direct sum of copies of `R` is the induced map between coproducts.
  have hfree (ι : Type u) : IsIso (α.app (ModuleCat.of R (⨁ _ : ι, R))) := by
    have (j : Discrete ι) : IsIso ((Functor.whiskerLeft
        (Discrete.functor fun _ : ι ↦ ModuleCat.of R R) α).app j) :=
      inferInstanceAs (IsIso (α.app (ModuleCat.of R R)))
    have : IsIso (Functor.whiskerLeft (Discrete.functor fun _ : ι ↦ ModuleCat.of R R) α) :=
      NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit _ α _
      (coproductCoconeIsColimit fun _ : ι ↦ ModuleCat.of R R)
  have := preservesSmallestColimits_of_preservesColimits F
  have := preservesSmallestColimits_of_preservesColimits G
  have (M : ModuleCat.{u} R) : IsIso (α.app M) := by
    -- `M` is the cokernel of `f`, where `g` sends the basis vector at `m` to `m` and `f` sends
    -- the basis vector at an element of the kernel of `g` to that element.
    let g : ModuleCat.of R (⨁ _ : M, R) ⟶ M :=
      ofHom (toModule R M M fun m ↦ LinearMap.toSpanSingleton R M m)
    let f : ModuleCat.of R (⨁ _ : LinearMap.ker g.hom, R) ⟶ ModuleCat.of R (⨁ _ : M, R) :=
      ofHom (toModule R _ _ fun k ↦ LinearMap.toSpanSingleton R _ k.val)
    have hg (m : M) : g.hom (lof R M (fun _ ↦ R) m 1) = m := by simp [g]
    have hf (k : LinearMap.ker g.hom) : f.hom (lof R _ (fun _ ↦ R) k 1) = k := by simp [f]
    have hgf : g.hom ∘ₗ f.hom = 0 := linearMap_ext R fun k ↦ LinearMap.ext_ring (by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hf]
      exact k.property)
    have hfg : Function.Exact f.hom g.hom :=
      LinearMap.exact_of_comp_eq_zero_of_ker_le_range hgf fun y hy ↦ ⟨_, hf ⟨y, hy⟩⟩
    have hc := isColimitCokernelCofork f g hfg fun m ↦ ⟨_, hg m⟩
    have (j : WalkingParallelPair) :
        IsIso ((Functor.whiskerLeft (parallelPair f 0) α).app j) := by
      cases j <;> exact hfree _
    have : IsIso (Functor.whiskerLeft (parallelPair f 0) α) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit _ α _ hc
  exact NatIso.isIso_of_isIso_app α

/-- A coproduct of finite modules is finite when only finitely many summands are nonzero.
The index type itself need not be finite. -/
theorem finite_coproduct_of_finite_support {ι : Type*} (M : ι → ModuleCat.{v} R)
    [HasCoproduct M] [∀ i, Module.Finite R (M i)]
    (hM : {i | ¬ IsZero (M i)}.Finite) : Module.Finite R (∐ M : ModuleCat.{v} R) := by
  have : Finite {i | ¬ IsZero (M i)} := hM
  -- The inclusions of the nonzero summands already span the coproduct: the others vanish.
  have htop : ⊤ ≤ ⨆ i : {i | ¬ IsZero (M i)}, LinearMap.range (Sigma.ι M i.val).hom := by
    refine (iSup_range_eq_top_of_isColimit (colimit.isColimit (Discrete.functor M))).ge.trans
      (iSup_le fun ⟨i⟩ ↦ ?_)
    by_cases hi : IsZero (M i)
    · simp [hi.eq_of_src (Sigma.ι M i) 0]
    · exact le_iSup_of_le ⟨i, hi⟩ le_rfl
  apply Module.Finite.of_fg_top
  rw [← top_le_iff.1 htop]
  exact Submodule.fg_iSup _ fun i ↦ Submodule.fg_range _

/-- A module isomorphic to a coproduct of copies of `R` indexed by a nonempty type receives an
injective linear map from `R`, through a coproduct inclusion. -/
theorem exists_injective_of_iso_sigma {M : ModuleCat.{u} R} {J : Type u} [Nonempty J]
    (e : M ≅ ∐ fun _ : J ↦ ModuleCat.of R R) : ∃ f : R →ₗ[R] M, Function.Injective f :=
  let g := Sigma.ι (fun _ : J ↦ ModuleCat.of R R) (Classical.arbitrary J) ≫ e.inv
  ⟨g.hom, (ModuleCat.mono_iff_injective g).1 inferInstance⟩

end ModuleCat

end TauCeti

namespace ModuleCat

open CategoryTheory Limits DirectSum

variable {R : Type u} [Ring R]

variable (F : ℕ ⥤ ModuleCat.{v} R)

/-- The difference map of the telescope of a sequence `F₀ → F₁ → ⋯` of modules: the endomorphism
of `⨁ₙ Fₙ` sending `x` in the summand `Fₙ` to `x - φₙ(x)`, where `φₙ(x)` lies in the summand
`Fₙ₊₁`. -/
noncomputable def telescopeDiff : (⨁ n, F.obj n) →ₗ[R] ⨁ n, F.obj n :=
  letI : HasCoproduct F.obj := ⟨⟨⟨_, coproductCoconeIsColimit F.obj⟩⟩⟩
  ((coprodIsoDirectSum F.obj).inv ≫ F.sequenceDifference ≫ (coprodIsoDirectSum F.obj).hom).hom

@[simp]
theorem telescopeDiff_lof (n : ℕ) (x : F.obj n) :
    telescopeDiff F (lof R ℕ (fun n ↦ F.obj n) n x) =
      lof R ℕ (fun n ↦ F.obj n) n x -
        lof R ℕ (fun n ↦ F.obj n) (n + 1) (F.map (homOfLE (n.le_add_right 1)) x) := by
  have : HasCoproduct F.obj := ⟨⟨⟨_, coproductCoconeIsColimit F.obj⟩⟩⟩
  have hcomp : (ofHom (lof R ℕ (fun n ↦ F.obj n) n) ≫ (coprodIsoDirectSum F.obj).inv) ≫
      F.sequenceDifference ≫ (coprodIsoDirectSum F.obj).hom =
      ofHom (lof R ℕ (fun n ↦ F.obj n) n) -
        F.map (homOfLE (n.le_add_right 1)) ≫ ofHom (lof R ℕ (fun n ↦ F.obj n) (n + 1)) := by
    rw [lof_coprodIsoDirectSum_inv]
    simp [Functor.ι_sequenceDifference_assoc, Preadditive.sub_comp]
  exact congrArg (fun φ : F.obj n ⟶ of R (⨁ n, F.obj n) ↦ φ x) hcomp

/-- As a morphism in `ModuleCat R`, `ofHom (telescopeDiff F)` is `F.sequenceDifference`
conjugated by `coprodIsoDirectSum F.obj`, for any `HasCoproduct F.obj` instance. -/
theorem ofHom_telescopeDiff [HasCoproduct F.obj] :
    ofHom (telescopeDiff F) =
      (coprodIsoDirectSum F.obj).inv ≫ F.sequenceDifference ≫
        (coprodIsoDirectSum F.obj).hom := by
  rw [← cancel_epi (coprodIsoDirectSum F.obj).hom, Iso.hom_inv_id_assoc]
  refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_
  rw [← Category.assoc, ι_coprodIsoDirectSum_hom, Functor.ι_sequenceDifference_assoc,
    Preadditive.sub_comp, ι_coprodIsoDirectSum_hom, Category.assoc, ι_coprodIsoDirectSum_hom]
  ext x
  simp

@[simp]
theorem telescopeDiff_apply_zero (a : ⨁ n, F.obj n) : telescopeDiff F a 0 = a 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n x =>
    rw [← lof_eq_of R, telescopeDiff_lof, DFinsupp.sub_apply]
    rcases n with _ | n <;> simp [lof_eq_of, of_eq_of_ne]
  | add a b ha hb => simp [ha, hb]

@[simp]
theorem telescopeDiff_apply_succ (a : ⨁ n, F.obj n) (n : ℕ) :
    telescopeDiff F a (n + 1) = a (n + 1) - F.map (homOfLE (n.le_add_right 1)) (a n) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m x =>
    rw [← lof_eq_of R, telescopeDiff_lof, DFinsupp.sub_apply]
    rcases eq_or_ne m n with rfl | hmn
    · simp [lof_eq_of, of_eq_of_ne]
    · rcases eq_or_ne m (n + 1) with rfl | -
      · simp [lof_eq_of, of_eq_of_ne]
      · simp [lof_eq_of, of_eq_of_ne, Ne.symm hmn]
  | add a b ha hb => simp [ha, hb, sub_add_sub_comm]

/-- The difference map of the telescope is injective: the component of `a` in degree `n` is
recovered from the components of `telescopeDiff F a` in degrees `≤ n`. -/
theorem telescopeDiff_injective : Function.Injective (telescopeDiff F) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ DFinsupp.ext fun n ↦ ?_
  induction n with
  | zero => simpa using congr($ha 0)
  | succ n ih => simpa [ih] using congr($ha (n + 1))

/-- The telescope sequence `⨁ₙ Fₙ → ⨁ₙ Fₙ → c.pt` of a cocone `c` over a sequence of modules
`F`: the first map is `telescopeDiff F`, the second is induced by the legs of `c`. It is short
exact when `c` is a colimit cocone (`ModuleCat.shortExact_telescopeShortComplex`). -/
@[expose]
noncomputable def telescopeShortComplex (c : Cocone F) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ofHom (telescopeDiff F))
    (ConcreteCategory.ofHom (C := ModuleCat R) (X := of R (⨁ n, F.obj n)) (Y := c.pt)
      (toModule R ℕ c.pt fun n ↦ (c.ι.app n).hom)) <| by
    ext : 1
    refine DirectSum.linearMap_ext _ fun n ↦ LinearMap.ext fun x ↦ ?_
    simp

@[simp]
theorem telescopeShortComplex_X₁ (c : Cocone F) :
    (telescopeShortComplex F c).X₁ = of R (⨁ n, F.obj n) := (rfl)

@[simp]
theorem telescopeShortComplex_X₂ (c : Cocone F) :
    (telescopeShortComplex F c).X₂ = of R (⨁ n, F.obj n) := (rfl)

@[simp]
theorem telescopeShortComplex_X₃ (c : Cocone F) : (telescopeShortComplex F c).X₃ = c.pt := (rfl)

@[simp]
theorem telescopeShortComplex_f (c : Cocone F) :
    (telescopeShortComplex F c).f = ofHom (telescopeDiff F) := (rfl)

@[simp]
theorem telescopeShortComplex_g (c : Cocone F) :
    (telescopeShortComplex F c).g =
      ConcreteCategory.ofHom (C := ModuleCat R) (X := of R (⨁ n, F.obj n)) (Y := c.pt)
        (toModule R ℕ c.pt fun n ↦ (c.ι.app n).hom) := (rfl)

/-- The telescope sequence of a colimit cocone over a sequence of modules is short exact. -/
theorem shortExact_telescopeShortComplex {c : Cocone F} (hc : IsColimit c) :
    (telescopeShortComplex F c).ShortExact := by
  have : HasCoproduct F.obj := ⟨⟨⟨_, coproductCoconeIsColimit F.obj⟩⟩⟩
  let S := telescopeShortComplex F c
  let e := coprodIsoDirectSum F.obj
  have hg : e.hom ≫ S.g = Sigma.desc (fun n : ℕ ↦ c.ι.app n) ≫ (Iso.refl c.pt).hom := by
    have hg₀ : e.hom ≫ ConcreteCategory.ofHom (C := ModuleCat R) (X := of R (⨁ n, F.obj n))
        (Y := c.pt) (toModule R ℕ c.pt fun n ↦ (c.ι.app n).hom) =
        Sigma.desc (fun n : ℕ ↦ c.ι.app n) ≫ (Iso.refl c.pt).hom := by
      rw [Iso.refl_hom, Category.comp_id]
      refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_
      rw [← Category.assoc, ι_coprodIsoDirectSum_hom, Sigma.ι_comp_desc]
      ext x
      simp
    exact (congrArg (fun k : of R (⨁ n, F.obj n) ⟶ c.pt ↦ e.hom ≫ k)
      (telescopeShortComplex_g F c)).trans hg₀
  have hf : e.hom ≫ S.f = F.sequenceDifference ≫ e.hom := by
    have hf₀ : e.hom ≫ ofHom (telescopeDiff F) = F.sequenceDifference ≫ e.hom := by
      rw [ofHom_telescopeDiff, Iso.hom_inv_id_assoc]
    exact (congrArg (fun k : of R (⨁ n, F.obj n) ⟶ of R (⨁ n, F.obj n) ↦ e.hom ≫ k)
      (telescopeShortComplex_f F c)).trans hf₀
  have hcok : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    IsCokernel.ofIso _ (F.isColimitCokernelCoforkOfIsColimit hc) _ e e (Iso.refl c.pt) hf hg
  have : Mono S.f := (mono_iff_injective _).2 (telescopeDiff_injective F)
  have : Epi S.g := epi_of_isColimit_cofork hcok
  exact ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel hcok) inferInstance inferInstance

/-- **The legs of a sequential colimit of injections are injective.** If the transition maps
`Fₙ → Fₙ₊₁` of a sequence of modules are injective, so are the legs `Fₙ → c.pt` of a colimit
cocone. -/
theorem injective_ι_app_of_isColimit {c : Cocone F} (hc : IsColimit c)
    (hinj : ∀ n : ℕ, Function.Injective (F.map (homOfLE (n.le_add_right 1))).hom) (n : ℕ) :
    Function.Injective (c.ι.app n).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (CategoryTheory.forget (ModuleCat.{v} R))
  obtain ⟨m, f, hm⟩ := Concrete.exists_map_eq_zero_of_ι_eq_zero F hc hx
  have hinj_le : ∀ {m : ℕ} (hnm : n ≤ m), Function.Injective (F.map (homOfLE hnm)).hom := by
    intro m hnm
    induction m, hnm using Nat.le_induction with
    | base =>
      rw [Subsingleton.elim (homOfLE _) (𝟙 n), F.map_id]
      exact Function.injective_id
    | succ m hnm ih =>
      rw [← homOfLE_comp hnm (m.le_add_right 1), F.map_comp, ModuleCat.hom_comp]
      exact (hinj m).comp ih
  exact (injective_iff_map_eq_zero _).1 (hinj_le (leOfHom f)) x
    (Subsingleton.elim f (homOfLE (leOfHom f)) ▸ hm)

/-- **A sequential colimit of injections with free cokernels is free.** Let `F₀ → F₁ → F₂ → ⋯` be
a sequence of modules with `F₀` free, whose transition maps `φₙ : Fₙ → Fₙ₊₁` are injective with
free cokernels `Fₙ₊₁ ⧸ φₙ(Fₙ)`. Then the colimit of the sequence is free: the images of the legs
filter it, with `F₀` and the cokernels as subquotients. No finiteness is assumed. -/
theorem free_of_isColimit {c : Cocone F} (hc : IsColimit c) (h0 : Module.Free R (F.obj 0))
    (hinj : ∀ n : ℕ, Function.Injective (F.map (homOfLE (n.le_add_right 1))).hom)
    (hfree : ∀ n : ℕ, Module.Free R
      (F.obj (n + 1) ⧸ LinearMap.range (F.map (homOfLE (n.le_add_right 1))).hom)) :
    Module.Free R c.pt := by
  -- Filter the colimit by the images of the legs.
  let N (n : ℕ) : Submodule R c.pt := LinearMap.range (c.ι.app n).hom
  have hN (n : ℕ) (x : F.obj n) :
      (c.ι.app (n + 1)).hom (F.map (homOfLE (n.le_add_right 1)) x) = (c.ι.app n).hom x := by
    rw [← ModuleCat.comp_apply, c.w]
  have hι (n : ℕ) := injective_ι_app_of_isColimit F hc hinj n
  refine Module.Free.of_filtration N (monotone_nat_of_le_succ fun n ↦ ?_)
    (Module.Free.of_equiv (LinearEquiv.ofInjective _ (hι 0)))
    (TauCeti.ModuleCat.iSup_range_eq_top_of_isColimit hc) fun n ↦ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, hN n x⟩
  · -- Each leg carries the image of the preceding transition onto the preceding filtration step.
    have := hfree n
    refine .of_equiv (Submodule.Quotient.equiv
      (LinearMap.range (F.map (homOfLE (n.le_add_right 1))).hom) _
      (LinearEquiv.ofInjective _ (hι (n + 1))) ?_)
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.subtype_apply]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, hx⟩
      exact ⟨x, (hN n x).symm.trans congr(Subtype.val $hx)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, Subtype.ext (hN n x)⟩

end ModuleCat
