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
legs `Fₙ → M` of the colimit cocone.

## Main declarations

* `TauCeti.ModuleCat.iSup_range_eq_top_of_isColimit`: the ranges of the legs of a colimit cocone
  span its point.
* `TauCeti.ModuleCat.isIso_of_isIso_app_self`: a natural transformation between
  colimit-preserving functors out of `ModuleCat R` whose component at `R` is invertible is an
  isomorphism.
* `ModuleCat.telescopeDiff`: the map `⨁ₙ Fₙ → ⨁ₙ Fₙ`, `x ↦ x - φₙ(x)`, which is injective
  (`ModuleCat.telescopeDiff_injective`).
* `ModuleCat.telescopeShortComplex`: the telescope sequence of a cocone over `F : ℕ ⥤ ModuleCat R`,
  short exact when the cocone is a colimit (`ModuleCat.shortExact_telescopeShortComplex`).

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
      ofHom (toModule R _ _ fun k ↦ LinearMap.toSpanSingleton R _ k.1)
    have hg (m : M) : g.hom (lof R M (fun _ ↦ R) m 1) = m := by simp [g]
    have hf (k : LinearMap.ker g.hom) : f.hom (lof R _ (fun _ ↦ R) k 1) = k := by simp [f]
    have hgf : g.hom ∘ₗ f.hom = 0 := linearMap_ext R fun k ↦ LinearMap.ext_ring (by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hf]
      exact k.2)
    have hfg : Function.Exact f.hom g.hom := fun y ↦ ⟨fun hy ↦ ⟨_, hf ⟨y, hy⟩⟩, by
      rintro ⟨x, rfl⟩
      exact LinearMap.congr_fun hgf x⟩
    have hc := isColimitCokernelCofork f g hfg fun m ↦ ⟨_, hg m⟩
    have (j : WalkingParallelPair) :
        IsIso ((Functor.whiskerLeft (parallelPair f 0) α).app j) := by
      cases j <;> exact hfree _
    have : IsIso (Functor.whiskerLeft (parallelPair f 0) α) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit _ α _ hc
  exact NatIso.isIso_of_isIso_app α

end ModuleCat

end TauCeti

namespace ModuleCat

open CategoryTheory Limits DirectSum

variable {R : Type u} [Ring R] (F : ℕ ⥤ ModuleCat.{v} R)

/-- The difference map of the telescope of a sequence `F₀ → F₁ → ⋯` of modules: the endomorphism
of `⨁ₙ Fₙ` sending `x` in the summand `Fₙ` to `x - φₙ(x)`, where `φₙ(x)` lies in the summand
`Fₙ₊₁`. -/
noncomputable def telescopeDiff : (⨁ n, F.obj n) →ₗ[R] ⨁ n, F.obj n :=
  toModule R ℕ _ fun n ↦ lof R ℕ (fun n ↦ F.obj n) n -
    lof R ℕ (fun n ↦ F.obj n) (n + 1) ∘ₗ (F.map (homOfLE (n.le_add_right 1))).hom

@[simp]
theorem telescopeDiff_lof (n : ℕ) (x : F.obj n) :
    telescopeDiff F (lof R ℕ (fun n ↦ F.obj n) n x) =
      lof R ℕ (fun n ↦ F.obj n) n x -
        lof R ℕ (fun n ↦ F.obj n) (n + 1) (F.map (homOfLE (n.le_add_right 1)) x) := by
  simp [telescopeDiff]

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

theorem telescopeShortComplex_f (c : Cocone F) :
    (telescopeShortComplex F c).f = eqToHom (telescopeShortComplex_X₁ F c) ≫
      ofHom (telescopeDiff F) ≫ eqToHom (telescopeShortComplex_X₂ F c).symm := (rfl)

theorem telescopeShortComplex_g (c : Cocone F) :
    (telescopeShortComplex F c).g = eqToHom (telescopeShortComplex_X₂ F c) ≫
      ConcreteCategory.ofHom (C := ModuleCat R) (X := of R (⨁ n, F.obj n)) (Y := c.pt)
        (toModule R ℕ c.pt fun n ↦ (c.ι.app n).hom) ≫
      eqToHom (telescopeShortComplex_X₃ F c).symm := (rfl)

/-- The cocone over `F` with point the cokernel of `telescopeDiff F`, whose legs are the
summand inclusions followed by the quotient map. -/
private noncomputable def telescopeCokernelCocone : Cocone F where
  pt := of R ((⨁ n, F.obj n) ⧸ LinearMap.range (telescopeDiff F))
  ι := NatTrans.ofSequence (fun n ↦ ConcreteCategory.ofHom (C := ModuleCat R) (X := F.obj n)
      (Y := of R ((⨁ n, F.obj n) ⧸ LinearMap.range (telescopeDiff F)))
      ((LinearMap.range (telescopeDiff F)).mkQ ∘ₗ lof R ℕ (fun n ↦ F.obj n) n)) fun n ↦ by
    ext x
    simpa [Submodule.Quotient.eq] using (LinearMap.range (telescopeDiff F)).neg_mem
      (LinearMap.mem_range_self (telescopeDiff F) (lof R ℕ (fun n ↦ F.obj n) n x))

/-- The telescope sequence of a colimit cocone over a sequence of modules is short exact. -/
theorem shortExact_telescopeShortComplex {c : Cocone F} (hc : IsColimit c) :
    (telescopeShortComplex F c).ShortExact := by
  -- The map from the colimit to the cokernel of `telescopeDiff F` restricts to the quotient map,
  -- so every element of `⨁ₙ Fₙ` sent to zero in the colimit lies in the image of the difference.
  have key (a : ⨁ n, F.obj n) : (hc.desc (telescopeCokernelCocone F)).hom
      (toModule R ℕ c.pt (fun n ↦ (c.ι.app n).hom) a) =
        (LinearMap.range (telescopeDiff F)).mkQ a := by
    induction a using DirectSum.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | of n x =>
      rw [← lof_eq_of R, toModule_lof]
      exact congr(Hom.hom $(hc.fac (telescopeCokernelCocone F) n) x)
    | add a b ha hb =>
      -- The two sides carry the module structures of `of R Q` and `Q`, equal by unfolding.
      simp only [map_add, ha, hb]
      rfl
  have hsurj : Function.Surjective (toModule R ℕ c.pt fun n ↦ (c.ι.app n).hom) := by
    rw [← LinearMap.range_eq_top, eq_top_iff,
      ← TauCeti.ModuleCat.iSup_range_eq_top_of_isColimit hc]
    refine iSup_le fun n ↦ ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨lof R ℕ (fun n ↦ F.obj n) n x, by simp⟩
  refine { exact := (ShortComplex.moduleCat_exact_iff _).2 fun a ha ↦ ?_
           mono_f := (mono_iff_injective _).2 (telescopeDiff_injective F)
           epi_g := (epi_iff_surjective _).2 hsurj }
  exact LinearMap.mem_range.1 <| (Submodule.Quotient.mk_eq_zero _).1 <|
    (key a).symm.trans ((congrArg _ ha).trans (map_zero _))

end ModuleCat
