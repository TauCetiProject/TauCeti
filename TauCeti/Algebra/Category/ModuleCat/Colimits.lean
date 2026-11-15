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
public import TauCeti.LinearAlgebra.FreeModule.Filtration

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
  (`ModuleCat.telescopeDiff_injective`).
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

/-- A coproduct of finite modules is finite when only finitely many summands are nonzero.
The index type itself need not be finite. -/
theorem finite_coproduct_of_finite_support {ι : Type*} (M : ι → ModuleCat.{v} R)
    [HasCoproduct M] [∀ i, Module.Finite R (M i)]
    (hM : {i | ¬ IsZero (M i)}.Finite) : Module.Finite R (∐ M : ModuleCat.{v} R) := by
  have : Finite {i | ¬ IsZero (M i)} := hM
  have hrange :
      (⨆ i, LinearMap.range (Sigma.ι M i).hom) =
        ⨆ i : {i | ¬ IsZero (M i)}, LinearMap.range (Sigma.ι M i.1).hom := by
    apply le_antisymm
    · refine iSup_le fun i ↦ ?_
      by_cases hi : IsZero (M i)
      · have hz : Sigma.ι M i = 0 := hi.eq_of_src _ _
        simp [hz]
      · exact le_iSup_of_le ⟨i, hi⟩ le_rfl
    · exact iSup_le fun i ↦
        le_iSup (fun j ↦ LinearMap.range (Sigma.ι M j).hom) i.1
  have htop : (⨆ i, LinearMap.range (Sigma.ι M i).hom) = ⊤ := by
    have h := TauCeti.ModuleCat.iSup_range_eq_top_of_isColimit
      (colimit.isColimit (Discrete.functor M))
    have hsurj : Function.Surjective (Discrete.mk : ι → Discrete ι) :=
      fun ⟨i⟩ ↦ ⟨i, rfl⟩
    exact (hsurj.iSup_comp _).trans h
  apply Module.Finite.of_fg_top
  rw [← htop, hrange]
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

/-- **The legs of a sequential colimit of injections are injective.** If the transition maps
`Fₙ → Fₙ₊₁` of a sequence of modules are injective, so are the legs `Fₙ → c.pt` of a colimit
cocone. -/
theorem injective_ι_app_of_isColimit {c : Cocone F} (hc : IsColimit c)
    (hinj : ∀ n : ℕ, Function.Injective (F.map (homOfLE (n.le_add_right 1))).hom) (n : ℕ) :
    Function.Injective (c.ι.app n).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- Placed in degree `n`, `x` lies in the kernel of the telescope sequence, hence in the image
  -- of the difference map: `x = a n - φ (a (n - 1))` and `a (m + 1) = φ (a m)` in other degrees.
  obtain ⟨a, ha'⟩ : ∃ a : ⨁ n, F.obj n, telescopeDiff F a = lof R ℕ (fun n ↦ F.obj n) n x :=
    (ShortComplex.moduleCat_exact_iff _).1 (shortExact_telescopeShortComplex F hc).exact
      (lof R ℕ (fun n ↦ F.obj n) n x) (by
        -- The second map of the telescope sequence is by definition induced by the legs.
        change toModule R ℕ c.pt (fun n ↦ (c.ι.app n).hom) (lof R ℕ (fun n ↦ F.obj n) n x) = 0
        rw [toModule_lof]
        exact hx)
  have hlt (m : ℕ) (hm : m < n) : a m = 0 := by
    induction m with
    | zero => simpa [lof_eq_of, of_eq_of_ne _ _ _ hm.ne] using congr($ha' 0)
    | succ m ih =>
      simpa [lof_eq_of, of_eq_of_ne _ _ _ hm.ne, ih (by lia)] using congr($ha' (m + 1))
  have hn : a n = x := by
    rcases n with _ | n
    · simpa [lof_eq_of] using congr($ha' 0)
    · simpa [lof_eq_of, hlt n (by lia)] using congr($ha' (n + 1))
  have hsucc (m : ℕ) (hm : n ≤ m) :
      a (m + 1) = F.map (homOfLE (m.le_add_right 1)) (a m) := by
    have := congr($ha' (m + 1))
    simp only [telescopeDiff_apply_succ, lof_eq_of, of_eq_of_ne _ _ _ (by lia : m + 1 ≠ n)] at this
    exact sub_eq_zero.1 this
  -- Far out the component of `a` vanishes, and by injectivity so do all the earlier ones.
  have hzero (m : ℕ) (hm : n ≤ m) (h : a m = 0) : x = 0 := by
    induction m, hm using Nat.le_induction with
    | base => rwa [hn] at h
    | succ m hm ih =>
      exact ih (hinj m (by rw [← hsucc m hm, h, map_zero]))
  classical
  refine hzero (n + (a.support.sup id + 1)) (by lia) (DFinsupp.notMem_support_iff.1 fun h ↦ ?_)
  have := Finset.le_sup (f := id) h
  simp only [id] at this
  lia

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
