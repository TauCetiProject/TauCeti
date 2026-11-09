/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Spf

/-!
# The formal completion of a scheme along a closed subscheme

For a scheme `X` and an ideal sheaf `I` on `X`, the infinitesimal neighbourhoods
`V(I ^ (n + 1))` of the closed subscheme `V(I)` form an adic thickening system
`X.formalCompletion I`, the formal completion `X/V(I)` of `X` along `V(I)`, retained as its
explicit tower of levels (Stacks, Lemma 87.14.2 (0AIZ), Definition 87.14.3 (0AMC)). Its transition
maps are the inclusions `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))`, and the ideal sheaf of `V(I ^ (m + 1))`
in `V(I ^ (n + 1))` is the inverse image of `I ^ (m + 1)`, which is the `(m + 1)`-st power of the
ideal sheaf of `V(I)` in `V(I ^ (n + 1))`.

The levels come with closed immersions `formalCompletion.toScheme X I n : V(I ^ (n + 1)) ⟶ X`
compatible with the transitions. For `I = ⊥` the formal completion is the constant system of `X`
(`formalCompletion.botIso`), and for `I = ⊤` every level is empty. A morphism `f : X ⟶ Y` with
`J.comap f ≤ I`, i.e. carrying `V(I)` into `V(J)` scheme-theoretically, induces a morphism of formal
completions `formalCompletion.map f : X.formalCompletion I ⟶ Y.formalCompletion J`, functorially in
`f`; it is adic when `J.comap f = I`. The formal completion of a locally Noetherian scheme is
locally Noetherian.

For an ideal `J` of a ring `R`, the formal completion of `Spec R` along `V(J)` is the system
`spf J` of the affine schemes `Spec (R ⧸ J ^ (n + 1))` (`formalCompletion.specIso`, Stacks,
Lemma 87.14.6 (0GBA)). When `J` is finitely generated, `R` and its `J`-adic completion `R̂` have the
same reductions, so this is the formal spectrum `Spf R̂` of the adic ring `R̂`
(`formalCompletion.specIsoSpfCompletion`).

## Main definitions

* `AlgebraicGeometry.Scheme.formalCompletion`: the adic thickening system `n ↦ V(I ^ (n + 1))`.
* `AlgebraicGeometry.Scheme.formalCompletion.toScheme`: the closed immersions
  `V(I ^ (n + 1)) ⟶ X`.
* `AlgebraicGeometry.Scheme.formalCompletion.map`: functoriality in pairs `(X, I)`.
* `AlgebraicGeometry.Scheme.formalCompletion.botIso`: the formal completion along `V(⊥)` is the
  constant system of `X`.
* `AlgebraicGeometry.Scheme.formalCompletion.specIso`: the formal completion of `Spec R` along
  `V(J)` is `spf J`.
* `AlgebraicGeometry.Scheme.formalCompletion.specIsoSpfCompletion`: for `J` finitely generated, the
  formal completion of `Spec R` along `V(J)` is `Spf R̂`, the formal spectrum of the `J`-adic
  completion.

## Main results

* `AlgebraicGeometry.Scheme.formalCompletion_transition`: the transition maps are inclusions of
  closed subschemes.
* `AlgebraicGeometry.Scheme.formalCompletion.ker_ι`,
  `AlgebraicGeometry.Scheme.formalCompletion.ker_levelMap`: the ideal sheaves of the transitions
  are inverse images of powers of `I`.
* `AlgebraicGeometry.Scheme.formalCompletion.isLocallyNoetherian`: the formal completion of a
  locally Noetherian scheme is locally Noetherian.
* `AlgebraicGeometry.Scheme.formalCompletion.isAdicHom_map`: `formalCompletion.map f` is adic when
  `J.comap f = I`.

## References

* [Stacks Project, Section 87.14](https://stacks.math.columbia.edu/tag/0AIZ).
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open IdealSheafData

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The level maps of the tower `n ↦ V(I ^ (n + 1))` are the inclusions `V(I) ⟶ V(I ^ (n + 1))`. -/
private lemma levelMap_inclusion_eq (n : ℕ) :
    TauCeti.AlgebraicGeometry.levelMap (fun k ↦ (I ^ (k + 1)).subscheme)
        (fun k ↦ inclusion (pow_le_pow_of_le_one bot_le le_top (Nat.le_add_right (k + 1) 1))) n =
      inclusion (pow_le_pow_of_le_one bot_le le_top (Nat.le_add_left 1 n)) := by
  induction n with
  | zero => rw [TauCeti.AlgebraicGeometry.levelMap_zero, inclusion_id]
  | succ n ih => rw [TauCeti.AlgebraicGeometry.levelMap_succ, ih, inclusion_comp]

/-- The **formal completion** `X/V(I)` of a scheme `X` along the closed subscheme `V(I)` cut out by
an ideal sheaf `I`: the adic thickening system of the infinitesimal neighbourhoods `V(I ^ (n + 1))`
with the inclusions `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))` as transitions.
Stacks, Lemma 87.14.2 (0AIZ) and Definition 87.14.3 (0AMC). -/
-- `@[expose]` is forced by dependent typing of component morphisms: without
-- `(X.formalCompletion I).X n` reducing definitionally to `(I ^ (n + 1)).subscheme`,
-- `formalCompletion_ι`, `formalCompletion_transition`, `formalCompletion_levelMap` and
-- `formalCompletion.toScheme_def` do not typecheck.
@[stacks 0AMC, expose, simps X]
noncomputable def formalCompletion : AdicThickeningSystem.{u} where
  X n := (I ^ (n + 1)).subscheme
  ι n := inclusion (pow_le_pow_of_le_one bot_le le_top (Nat.le_add_right (n + 1) 1))
  isThickening n := by
    have := IsFirstOrderThickening.inclusion_pow_succ
      (pow_le_pow_of_le_one bot_le le_top (Nat.le_add_right (n + 1) 1) :
        I ^ (n + 2) ≤ I ^ (n + 1))
    infer_instance
  adic n := by
    rw [levelMap_inclusion_eq, ker_inclusion, ker_inclusion, pow_one, ← comap_pow]

/-- The transition `V(I ^ (n + 1)) ⟶ V(I ^ (n + 2))` of the formal completion is the inclusion of
closed subschemes. -/
theorem formalCompletion_ι (n : ℕ) :
    (X.formalCompletion I).ι n =
      inclusion (pow_le_pow_of_le_one bot_le le_top (Nat.le_add_right (n + 1) 1)) :=
  (rfl)

/-- The `n`-th reduction of the formal completion is the infinitesimal neighbourhood
`V(I ^ (n + 1))`. -/
theorem formalCompletion_reduction (n : ℕ) :
    (X.formalCompletion I).reduction n = (I ^ (n + 1)).subscheme := by
  rw [AdicThickeningSystem.reduction_eq, formalCompletion_X]

/-- For `m ≤ n`, the composite transition of the formal completion is the inclusion
`V(I ^ (m + 1)) ⟶ V(I ^ (n + 1))`. -/
theorem formalCompletion_transition {m n : ℕ} (h : m ≤ n) :
    (X.formalCompletion I).transition h =
      inclusion (pow_le_pow_of_le_one bot_le le_top (Nat.add_le_add_right h 1)) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact (AdicThickeningSystem.transition_refl _ _).trans (inclusion_id _).symm
  | succ n ih =>
    by_cases h' : m ≤ n
    · rw [AdicThickeningSystem.transition_succ_of_le _ h', ih h', formalCompletion_ι]
      exact inclusion_comp _ _
    · obtain rfl : m = n + 1 := by omega
      exact (AdicThickeningSystem.transition_refl _ _).trans (inclusion_id _).symm

/-- The level map `V(I) ⟶ V(I ^ (n + 1))` of the formal completion is the inclusion of closed
subschemes. -/
theorem formalCompletion_levelMap (n : ℕ) :
    (X.formalCompletion I).levelMap n =
      inclusion (pow_le_pow_of_le_one bot_le le_top (Nat.le_add_left 1 n)) := by
  rw [AdicThickeningSystem.levelMap_eq_transition, formalCompletion_transition]

namespace formalCompletion

/-- The closed immersion `toScheme X I n : V(I ^ (n + 1)) ⟶ X` from the `n`-th level of the formal
completion. -/
noncomputable def toScheme (n : ℕ) : (X.formalCompletion I).X n ⟶ X :=
  (I ^ (n + 1)).subschemeι

theorem toScheme_def (n : ℕ) : toScheme X I n = (I ^ (n + 1)).subschemeι :=
  (rfl)

instance isClosedImmersion_toScheme (n : ℕ) : IsClosedImmersion (toScheme X I n) :=
  inferInstanceAs (IsClosedImmersion (I ^ (n + 1)).subschemeι)

/-- The `n`-th level of the formal completion is the closed subscheme of `X` cut out by
`I ^ (n + 1)`. -/
@[simp]
theorem ker_toScheme (n : ℕ) : (toScheme X I n).ker = I ^ (n + 1) :=
  ker_subschemeι _

@[reassoc (attr := simp)]
theorem ι_toScheme (n : ℕ) :
    (X.formalCompletion I).ι n ≫ toScheme X I (n + 1) = toScheme X I n :=
  inclusion_subschemeι _

/-- The ideal sheaf of `V(I ^ (n + 1))` in `V(I ^ (n + 2))` is the inverse image of `I ^ (n + 1)`
along `V(I ^ (n + 2)) ⟶ X`. -/
@[simp]
theorem ker_ι (n : ℕ) :
    ((X.formalCompletion I).ι n).ker = (I ^ (n + 1)).comap (toScheme X I (n + 1)) :=
  ker_inclusion _

/-- The level `V(I)` of the formal completion is cut out of `V(I ^ (n + 1))` by the inverse image
of `I`. -/
@[simp]
theorem ker_levelMap (n : ℕ) :
    ((X.formalCompletion I).levelMap n).ker = I.comap (toScheme X I n) := by
  rw [formalCompletion_levelMap]
  exact (ker_inclusion _).trans (congrArg (comap · (toScheme X I n)) (pow_one I))

/-- The formal completion of a locally Noetherian scheme along any closed subscheme is locally
Noetherian, since closed subschemes of locally Noetherian schemes are locally Noetherian. -/
instance isLocallyNoetherian [AlgebraicGeometry.IsLocallyNoetherian X] :
    (X.formalCompletion I).IsLocallyNoetherian where
  level n := LocallyOfFiniteType.isLocallyNoetherian (toScheme X I n)

instance isIso_toScheme_bot (n : ℕ) : IsIso (toScheme X ⊥ n) :=
  (isIso_subschemeι_iff_eq_bot _).mpr (by rw [← zero_eq_bot, zero_pow n.succ_ne_zero])

/-- The formal completion along `V(⊥) = X` is the constant system of `X`. -/
noncomputable def botIso : X.formalCompletion ⊥ ≅ AdicThickeningSystem.ofScheme.obj X :=
  AdicThickeningSystem.isoMk (fun n ↦ (asIso (toScheme X ⊥ n) : _ ≅ X)) fun n ↦
    (ι_toScheme X ⊥ n).trans (Category.comp_id _).symm

@[simp]
theorem botIso_hom_app (n : ℕ) : (botIso X).hom.app n = toScheme X ⊥ n :=
  (AdicThickeningSystem.isoMk_hom_app _ _ n).trans (asIso_hom (toScheme X ⊥ n))

/-- The formal completion along the empty closed subscheme `V(⊤)` has empty levels. -/
instance isEmpty_X_top (n : ℕ) : IsEmpty ((X.formalCompletion ⊤).X n) := by
  rw [formalCompletion_X, ← one_eq_top, one_pow, one_eq_top]
  infer_instance

variable {X I} {Y Z : Scheme.{u}} {J : Y.IdealSheafData} {K : Z.IdealSheafData}

/-- A morphism `f : X ⟶ Y` with `J.comap f ≤ I`, i.e. mapping `V(I)` into `V(J)`
scheme-theoretically, restricts to morphisms `V(I ^ (n + 1)) ⟶ V(J ^ (n + 1))` and hence induces a
morphism of formal completions `X/V(I) ⟶ Y/V(J)`. -/
noncomputable def map (f : X ⟶ Y) (hf : J.comap f ≤ I) :
    X.formalCompletion I ⟶ Y.formalCompletion J where
  app n := subschemeMap (I ^ (n + 1)) (J ^ (n + 1)) f (pow_le_map_pow hf (n + 1))
  naturality n := by
    refine (cancel_mono (J ^ (n + 1 + 1)).subschemeι).mp ?_
    dsimp only [formalCompletion]
    simp

/-- The component of `map f` at level `n` is the restriction of `f` to
`V(I ^ (n + 1)) ⟶ V(J ^ (n + 1))`. -/
@[reassoc (attr := simp)]
theorem map_app_toScheme (f : X ⟶ Y) (hf : J.comap f ≤ I) (n : ℕ) :
    (map f hf).app n ≫ toScheme Y J n = toScheme X I n ≫ f :=
  subschemeMap_subschemeι _ _ _ (pow_le_map_pow hf (n + 1))

@[simp]
theorem map_id (h : I.comap (𝟙 X) ≤ I) : map (𝟙 X) h = 𝟙 (X.formalCompletion I) := by
  ext n
  rw [← cancel_mono (toScheme X I n), map_app_toScheme, AdicThickeningSystem.id_app,
    Category.comp_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : J.comap f ≤ I) (hg : K.comap g ≤ J) :
    map f hf ≫ map g hg =
      map (f ≫ g) ((comap_comp K f g).trans_le ((comap_mono f hg).trans hf)) := by
  ext n
  rw [← cancel_mono (toScheme Z K n), map_app_toScheme, AdicThickeningSystem.comp_app,
    Category.assoc, map_app_toScheme, map_app_toScheme_assoc]

/-- If `V(I)` is the scheme-theoretic inverse image of `V(J)` under `f`, i.e. `J.comap f = I`, then
the induced morphism of formal completions is adic: each `V(I ^ (n + 1))` is the inverse image of
`V(J ^ (n + 1))`. -/
theorem isAdicHom_map (f : X ⟶ Y) (hf : J.comap f = I) :
    AdicThickeningSystem.IsAdicHom (map f hf.le) := by
  rw [AdicThickeningSystem.isAdicHom_iff_ker_comap]
  intro n
  rw [ker_ι, ker_ι, ← comap_comp, map_app_toScheme, comap_comp, comap_pow, hf]

end formalCompletion

/-! ### Formal completions of affine schemes -/

namespace formalCompletion

variable {R : Type u} [CommRing R]

/-- The ideal sheaf `J ^ (n + 1) · 𝒪` on `Spec R` is the ideal sheaf of the closed immersion
`Spec (R ⧸ J ^ (n + 1)) ⟶ Spec R`. -/
private lemma ker_toScheme_eq_ker_spec (J : Ideal R) (n : ℕ) :
    (toScheme _ (ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)) n).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))).ker := by
  rw [ker_toScheme, Hom.ker_Spec_map, CommRingCat.hom_ofHom, Ideal.mk_ker, Ideal.map_pow,
    ofIdealTop_pow]

/-- The levelwise identification `Spec (R ⧸ J ^ (n + 1)) ≅ V(J ^ (n + 1))` over `Spec R`. -/
private noncomputable def specLevelIso (J : Ideal R) (n : ℕ) :
    (AdicThickeningSystem.spf J).X n ≅
      ((Spec (CommRingCat.of R)).formalCompletion
        (ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))).X n :=
  @asIso _ _ _ _ (IsClosedImmersion.lift _ _ (ker_toScheme_eq_ker_spec J n).le)
    (@IsClosedImmersion.isIso_lift _ _ _ _ _ _
      (IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective)
      (ker_toScheme_eq_ker_spec J n))

private lemma specLevelIso_hom_toScheme (J : Ideal R) (n : ℕ) :
    (specLevelIso J n).hom ≫ toScheme _ _ n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) :=
  IsClosedImmersion.lift_fac _ _ _

/-- The formal completion of `Spec R` along the closed subscheme `V(J)` is the system `spf J` of
the affine schemes `Spec (R ⧸ J ^ (n + 1))`, compatibly with the morphisms to `Spec R`.
Stacks, Lemma 87.14.6 (0GBA). -/
@[stacks 0GBA]
noncomputable def specIso (J : Ideal R) :
    (Spec (CommRingCat.of R)).formalCompletion
        (ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)) ≅
      AdicThickeningSystem.spf J :=
  (AdicThickeningSystem.isoMk (specLevelIso J) fun n ↦ by
    rw [← cancel_mono (toScheme _ _ (n + 1)), Category.assoc, Category.assoc,
      specLevelIso_hom_toScheme, ι_toScheme, specLevelIso_hom_toScheme]
    have h := (AdicThickeningSystem.spfToSpec J).naturality n
    simp only [AdicThickeningSystem.spfToSpec_app, AdicThickeningSystem.ofScheme_obj_ι] at h
    exact h.trans (Category.comp_id _)).symm

/-- Under `specIso`, the closed immersions `V(J ^ (n + 1)) ⟶ Spec R` are the morphisms
`Spec (R ⧸ J ^ (n + 1)) ⟶ Spec R` of `spfToSpec`. -/
@[reassoc (attr := simp)]
theorem specIso_inv_app_toScheme (J : Ideal R) (n : ℕ) :
    (specIso J).inv.app n ≫ toScheme _ _ n = (AdicThickeningSystem.spfToSpec J).app n := by
  rw [specIso, Iso.symm_inv, AdicThickeningSystem.isoMk_hom_app, specLevelIso_hom_toScheme,
    AdicThickeningSystem.spfToSpec_app]

/-- For a finitely generated ideal `J` of `R`, the formal completion of `Spec R` along `V(J)` is
the formal spectrum of the `J`-adic completion `R̂` of `R`, compatibly with the morphisms to
`Spec R` (`specIsoSpfCompletion_inv_app_toScheme`). Stacks, Lemma 87.14.6 (0GBA). -/
@[stacks 0GBA]
noncomputable def specIsoSpfCompletion (J : Ideal R) (fg : J.FG) :
    (Spec (CommRingCat.of R)).formalCompletion
        (ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)) ≅
      Spf (AdicRing.completion J fg) :=
  specIso J ≪≫ (Spf.completionIso J fg).symm

/-- Under `specIsoSpfCompletion`, the closed immersions `V(J ^ (n + 1)) ⟶ Spec R` are the
morphisms `Spec (R̂ ⧸ (J R̂) ^ (n + 1)) ⟶ Spec R̂ ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem specIsoSpfCompletion_inv_app_toScheme (J : Ideal R) (fg : J.FG) (n : ℕ) :
    (specIsoSpfCompletion J fg).inv.app n ≫ toScheme _ _ n =
      (Spf.toSpec (AdicRing.completion J fg)).app n ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AdicCompletion J R))) := by
  rw [specIsoSpfCompletion, Iso.trans_inv, Iso.symm_inv, AdicThickeningSystem.comp_app,
    Category.assoc, specIso_inv_app_toScheme]
  exact congrArg (·.app n) (Spf.completionIso_hom_spfToSpec J fg)

end formalCompletion

end AlgebraicGeometry.Scheme
