/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth
public import TauCeti.AlgebraicGeometry.Scheme.HomExt
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Lifts along a first-order thickening form a torsor

Let `f : X ⟶ S` be a morphism of schemes, `i : T ⟶ T'` a first-order thickening with ideal sheaf
`I` (so `I ^ 2 = 0`), `h : T' ⟶ S`, and `a : T ⟶ X` with `a ≫ f = i ≫ h`. A *lift* of `a` is a
morphism `b : T' ⟶ X` with `i ≫ b = a` and `b ≫ f = h`. Any two lifts have the same underlying
map, and their maps on sections differ by a derivation of `𝒪_X` over `𝒪_S` into `I`, along `a`;
conversely a lift plus such a derivation is again a lift. So when a lift exists, the lifts form a
torsor under the group of these derivations, `Der_{f⁻¹𝒪_S}(a⁻¹𝒪_X, I)`, which is
`Hom_{𝒪_T}(a^* Ω_{X/S}, I)` by the universal property of differentials (Stacks, Lemmas 37.9.1
(04FG), 37.9.2 (02H5) and 37.9.5 (04FJ), and Remark 37.9.6 (04FK) for this case `Y' = Y`). No
smoothness is needed for this, and `T'` is arbitrary.

A derivation is recorded here concretely, as a compatible family of maps
`Γ(X, V) → Γ(T', U)` for opens `V` of `X` and `U` of `T'` with `i ⁻¹ᵁ U ≤ a ⁻¹ᵁ V`.

For `f` smooth, lifts exist locally on `T'`: each point has an affine open neighbourhood over
which `f` restricts to a smooth morphism of affine schemes, hence formally smooth. For `f`
formally étale, lifts are unique for every `T'`, not only for affine `T'`.

## Main definitions

* `TauCeti.AlgebraicGeometry.ThickeningLift i a f h`: the lifts of `a` along `i` over `h`.
* `TauCeti.AlgebraicGeometry.LiftDerivation i a f`: the additive group of derivations of `𝒪_X`
  over `𝒪_S` into the ideal sheaf of `i`, along `a`.
* `TauCeti.AlgebraicGeometry.addDerivation b hb D`: the morphism `b + D` for a lift `b` and a
  derivation `D`, with `(b + D)^* x = b^* x + D x` on sections.

## Main results

* `TauCeti.AlgebraicGeometry.ThickeningLift.instAddTorsor`: when a lift exists, the lifts form a
  torsor under `LiftDerivation i a f`.
* `TauCeti.AlgebraicGeometry.exists_thickeningLift_restrict`: for `f` smooth, every point of `T'`
  has an open neighbourhood over which `a` lifts.
* `TauCeti.AlgebraicGeometry.ThickeningLift.instSubsingleton`: for `f` formally étale, a lift is
  unique.

The identification of `LiftDerivation i a f` with `Hom_{𝒪_T}(a^* Ω_{X/S}, I)` as a sheaf of
modules, and the obstruction class in `H¹(T, Hom(a^* Ω_{X/S}, I))`, are not formalized here.

## References

* [Stacks Project, Lemma 37.9.1](https://stacks.math.columbia.edu/tag/04FG): two lifts differ by
  a derivation.
* [Stacks Project, Lemma 37.9.2](https://stacks.math.columbia.edu/tag/02H5): a lift plus a
  derivation is a lift.
* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ) and
  [Remark 37.9.6](https://stacks.math.columbia.edu/tag/04FK): the lifts form a torsor.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {T T' X S : Scheme.{u}} (i : T ⟶ T') (a : T ⟶ X) (f : X ⟶ S)

/-- The families of maps on sections underlying a derivation of `𝒪_X` into the ideal of `i`,
along `a`: to an open `V` of `X` and an open `U` of `T'` whose part in `T` maps into `V` they
assign a map `Γ(X, V) → Γ(T', U)`. -/
abbrev LiftDerivationData : Type u :=
  ∀ (V : X.Opens) (U : {U : T'.Opens // i ⁻¹ᵁ U ≤ a ⁻¹ᵁ V}), Γ(X, V) → Γ(T', U.val)

/-- A family of maps `D V U : Γ(X, V) → Γ(T', U)` is a derivation of `𝒪_X` over `𝒪_S` into the
ideal sheaf of `i`, along `a`: each map is additive, takes values in the kernel of
`Γ(T', U) → Γ(T, U)`, is compatible with restriction, kills the sections pulled back from `S`, and
satisfies the Leibniz rule `D (x * y) = x' * D y + y' * D x` for any sections `x'`, `y'` of `T'`
restricting to `a^* x`, `a^* y` on `T`. -/
structure IsLiftDerivation (D : LiftDerivationData i a) : Prop where
  /-- Each `D V U` is additive. -/
  map_add (V U h) (x y : Γ(X, V)) : D V ⟨U, h⟩ (x + y) = D V ⟨U, h⟩ x + D V ⟨U, h⟩ y
  /-- `D` takes values in the ideal sheaf of `i`. -/
  app_apply_eq_zero (V U h) (x : Γ(X, V)) : i.app U (D V ⟨U, h⟩ x) = 0
  /-- `D` is compatible with restriction. -/
  apply_map {V V' : X.Opens} {U U' : T'.Opens} (h h') (hV : V' ≤ V) (hU : U' ≤ U)
    (x : Γ(X, V)) : D V' ⟨U', h'⟩ (X.presheaf.map (homOfLE hV).op x) =
      T'.presheaf.map (homOfLE hU).op (D V ⟨U, h⟩ x)
  /-- The Leibniz rule, with `𝒪_X` acting on the ideal sheaf of `i` through `a`. -/
  leibniz (V U h) (x y : Γ(X, V)) (x' y' : Γ(T', U)) (hx : i.app U x' = a.appLE V _ h x)
    (hy : i.app U y' = a.appLE V _ h y) :
    D V ⟨U, h⟩ (x * y) = x' * D V ⟨U, h⟩ y + y' * D V ⟨U, h⟩ x
  /-- `D` kills the sections pulled back from `S`. -/
  map_appLE (W : S.Opens) (V U h) (e : V ≤ f ⁻¹ᵁ W) (s : Γ(S, W)) :
    D V ⟨U, h⟩ (f.appLE W V e s) = 0

/-- The additive group of derivations of `𝒪_X` over `𝒪_S` into the ideal sheaf of a thickening
`i : T ⟶ T'`, along `a : T ⟶ X`. -/
def liftDerivations : AddSubgroup (LiftDerivationData i a) where
  carrier := {D | IsLiftDerivation i a f D}
  zero_mem' := ⟨by simp, by simp, by simp, by simp, by simp⟩
  add_mem' {D D'} hD hD' :=
    ⟨fun V U h x y ↦ by simp [hD.map_add, hD'.map_add]; abel,
      fun V U h x ↦ by simp [hD.app_apply_eq_zero, hD'.app_apply_eq_zero],
      fun h h' hV hU x ↦ by simp [hD.apply_map h h' hV hU, hD'.apply_map h h' hV hU],
      fun V U h x y x' y' hx hy ↦ by
        simp [hD.leibniz V U h x y x' y' hx hy, hD'.leibniz V U h x y x' y' hx hy]; ring,
      fun W V U h e s ↦ by simp [hD.map_appLE, hD'.map_appLE]⟩
  neg_mem' {D} hD :=
    ⟨fun V U h x y ↦ by simp [hD.map_add]; abel,
      fun V U h x ↦ by simp [hD.app_apply_eq_zero],
      fun h h' hV hU x ↦ by simp [hD.apply_map h h' hV hU],
      fun V U h x y x' y' hx hy ↦ by simp [hD.leibniz V U h x y x' y' hx hy]; ring,
      fun W V U h e s ↦ by simp [hD.map_appLE]⟩

/-- Membership in `liftDerivations` is `IsLiftDerivation`. -/
theorem mem_liftDerivations {D : LiftDerivationData i a} :
    D ∈ liftDerivations i a f ↔ IsLiftDerivation i a f D :=
  Iff.rfl

/-- The derivations of `𝒪_X` over `𝒪_S` into the ideal sheaf `I` of a thickening `i : T ⟶ T'`,
along `a : T ⟶ X`. Mathematically this is `Der_{f⁻¹𝒪_S}(a⁻¹𝒪_X, I)`, that is
`Hom_{𝒪_T}(a^* Ω_{X/S}, I)`. -/
abbrev LiftDerivation : Type u := liftDerivations i a f

variable {i a f}

namespace LiftDerivation

/-- The defining properties of a derivation into the ideal of a thickening. -/
theorem isLiftDerivation (D : LiftDerivation i a f) : IsLiftDerivation i a f D.val :=
  D.property

/-- A derivation vanishes on `1`. -/
@[simp]
theorem map_one_eq_zero (D : LiftDerivation i a f) (V : X.Opens) (U) : D.val V U 1 = 0 := by
  simpa using D.isLiftDerivation.map_appLE ⊤ V U.val U.property le_top 1

end LiftDerivation

section Lift

variable {b : T' ⟶ X} (hb : i ≫ b = a)
include hb

/-- If `b` lifts `a` along `i`, the part in `T` of `b ⁻¹ᵁ V` lies over `V`. -/
theorem preimage_preimage_le_of_comp_eq (V : X.Opens) : i ⁻¹ᵁ (b ⁻¹ᵁ V) ≤ a ⁻¹ᵁ V := by
  subst hb
  exact le_rfl

/-- If `b` lifts `a` along a surjective `i`, an open of `T'` whose part in `T` lies over `V` lies in
`b ⁻¹ᵁ V`. -/
theorem le_preimage_of_preimage_le_of_comp_eq [Surjective i] {V : X.Opens} {U : T'.Opens}
    (h : i ⁻¹ᵁ U ≤ a ⁻¹ᵁ V) : U ≤ b ⁻¹ᵁ V := by
  intro x hx
  obtain ⟨t, rfl⟩ := i.surjective x
  subst hb
  exact h hx

/-- If `b` lifts `a` along `i`, restricting the sections `b^* x` to `T` gives `a^* x`. -/
theorem app_appLE_of_comp_eq {V : X.Opens} {U : T'.Opens} (e : U ≤ b ⁻¹ᵁ V)
    (h : i ⁻¹ᵁ U ≤ a ⁻¹ᵁ V) (x : Γ(X, V)) :
    i.app U (b.appLE V U e x) = a.appLE V _ h x := by
  subst hb
  rw [← CommRingCat.comp_apply, i.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

end Lift

section AddDerivation

variable [IsFirstOrderThickening i] (b : T' ⟶ X) (hb : i ≫ b = a) (D : LiftDerivation i a f)

/-- The map `x ↦ b^* x + D x` on sections over `V` is multiplicative: the cross term
`D x * D y` lies in the square of the ideal of `i`, which vanishes. -/
private theorem app_add_map_mul (V : X.Opens) (x y : Γ(X, V)) :
    b.app V (x * y) + D.val V ⟨_, preimage_preimage_le_of_comp_eq hb V⟩ (x * y) =
      (b.app V x + D.val V ⟨_, preimage_preimage_le_of_comp_eq hb V⟩ x) *
        (b.app V y + D.val V ⟨_, preimage_preimage_le_of_comp_eq hb V⟩ y) := by
  have hle := preimage_preimage_le_of_comp_eq hb V
  have hx := app_appLE_of_comp_eq hb le_rfl hle x
  have hy := app_appLE_of_comp_eq hb le_rfl hle y
  rw [← Scheme.Hom.app_eq_appLE] at hx hy
  rw [map_mul, D.isLiftDerivation.leibniz V _ _ x y _ _ hx hy]
  have := IsFirstOrderThickening.mul_eq_zero_of_app_eq_zero i
    (D.isLiftDerivation.app_apply_eq_zero V _ hle x)
    (D.isLiftDerivation.app_apply_eq_zero V _ hle y)
  linear_combination (-1 : Γ(T', b ⁻¹ᵁ V)) * this

/-- The map on sections `x ↦ b^* x + D x` over `V`, a ring homomorphism. -/
private noncomputable def addDerivationApp (V : X.Opens) : Γ(X, V) ⟶ Γ(T', b ⁻¹ᵁ V) :=
  CommRingCat.ofHom
    { toFun x := b.app V x + D.val V ⟨_, preimage_preimage_le_of_comp_eq hb V⟩ x
      map_one' := by simp
      map_mul' := app_add_map_mul b hb D V
      map_zero' := by simpa using D.isLiftDerivation.map_appLE ⊤ V _ _ le_top 0
      map_add' x y := by rw [map_add, D.isLiftDerivation.map_add]; abel }

/-- The value of `addDerivationApp` on a section. -/
@[simp]
private theorem addDerivationApp_apply (V : X.Opens) (x : Γ(X, V)) :
    addDerivationApp b hb D V x =
      b.app V x + D.val V ⟨_, preimage_preimage_le_of_comp_eq hb V⟩ x := by
  simp [addDerivationApp]

/-- The morphism of structure presheaves `x ↦ b^* x + D x`. -/
private noncomputable def addDerivationC : X.presheaf ⟶ b.base _* T'.presheaf where
  app V := addDerivationApp b hb D V.unop
  naturality V V' g := by
    obtain ⟨V⟩ := V
    obtain ⟨V'⟩ := V'
    have hle : V' ≤ V := g.unop.le
    obtain rfl : g = (homOfLE hle).op := Subsingleton.elim _ _
    ext x
    have h1 := congr($(b.naturality (homOfLE hle).op) x)
    have h2 := D.isLiftDerivation.apply_map (preimage_preimage_le_of_comp_eq hb V)
      (preimage_preimage_le_of_comp_eq hb V') hle ((Opens.map b.base).map (homOfLE hle)).le x
    simp only [CommRingCat.comp_apply, Quiver.Hom.unop_op] at h1 h2 ⊢
    rw [addDerivationApp_apply, addDerivationApp_apply, h1, h2, map_add,
      TopCat.Presheaf.pushforward_obj_map, Quiver.Hom.unop_op]
    -- The two restriction maps agree, since there is at most one morphism between two opens.
    congr 4

/-- The components of `addDerivationC`. -/
@[simp]
private theorem addDerivationC_app (V : X.Opens) :
    (addDerivationC b hb D).app (op V) = addDerivationApp b hb D V := by
  rw [addDerivationC]

/-- After restricting to `T`, the stalk maps of `b + D` and `b` agree. -/
private theorem addDerivationPsh_stalkMap_comp (t : T) :
    (PresheafedSpace.Hom.mk b.base (addDerivationC b hb D)).stalkMap (i t) ≫ i.stalkMap t =
      b.stalkMap (i t) ≫ i.stalkMap t := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hV ↦ ?_
  rw [PresheafedSpace.stalkMap_germ_assoc]
  dsimp only
  rw [Scheme.Hom.germ_stalkMap_assoc]
  -- After `dsimp only`, the membership proof of the germ on the left still mentions the point map
  -- of the `PresheafedSpace.Hom`; restate it with `hV'` so that `Scheme.Hom.germ_stalkMap` applies.
  have hV' : i t ∈ b ⁻¹ᵁ V := hV
  change _ ≫ T'.presheaf.germ (b ⁻¹ᵁ V) (i t) hV' ≫ _ =
    _ ≫ T'.presheaf.germ (b ⁻¹ᵁ V) (i t) hV' ≫ _
  rw [Scheme.Hom.germ_stalkMap, ← Category.assoc, ← Category.assoc]
  congr 1
  ext y
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, addDerivationC_app, addDerivationApp_apply,
    map_add, D.isLiftDerivation.app_apply_eq_zero, add_zero]

/-- **Translating a lift by a derivation.** For `b : T' ⟶ X` lifting `a` along a first-order
thickening `i` and a derivation `D` of `𝒪_X` into the ideal of `i`, the morphism `b + D` with the
same underlying map as `b` and with `(b + D)^* x = b^* x + D x` on sections. -/
noncomputable def addDerivation : T' ⟶ X where
  base := b.base
  c := addDerivationC b hb D
  prop x := by
    obtain ⟨t, rfl⟩ := i.surjective x
    have : IsLocalHom ((i.stalkMap t).hom.comp
        ((PresheafedSpace.Hom.mk b.base (addDerivationC b hb D)).stalkMap (i t)).hom) := by
      rw [← CommRingCat.hom_comp, addDerivationPsh_stalkMap_comp, CommRingCat.hom_comp]
      infer_instance
    exact isLocalHom_of_comp _ (i.stalkMap t).hom

/-- `b + D` has the same underlying map as `b`. -/
@[simp]
theorem addDerivation_base : (addDerivation b hb D).base = b.base := by
  rw [addDerivation]

/-- `b + D` has the same preimages of opens as `b`. -/
theorem preimage_addDerivation (V : X.Opens) : addDerivation b hb D ⁻¹ᵁ V = b ⁻¹ᵁ V := by
  rw [addDerivation_base]

/-- On sections, `(b + D)^* x = b^* x + D x`. -/
theorem addDerivation_appLE {V : X.Opens} {U : T'.Opens} (e : U ≤ b ⁻¹ᵁ V)
    (e' : U ≤ addDerivation b hb D ⁻¹ᵁ V) (x : Γ(X, V)) :
    (addDerivation b hb D).appLE V U e' x =
      b.appLE V U e x +
        D.val V ⟨U, (i.preimage_mono e).trans (preimage_preimage_le_of_comp_eq hb V)⟩ x := by
  have h2 := D.isLiftDerivation.apply_map (preimage_preimage_le_of_comp_eq hb V)
    ((i.preimage_mono e).trans (preimage_preimage_le_of_comp_eq hb V)) le_rfl e x
  -- The map on sections of `addDerivation b hb D` over `V` is `addDerivationApp b hb D V` by
  -- definition. A lemma stating this cannot be written: its two sides have the types
  -- `Γ(T', addDerivation b hb D ⁻¹ᵁ V)` and `Γ(T', b ⁻¹ᵁ V)`, which agree only after unfolding
  -- `addDerivation`.
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  change T'.presheaf.map (homOfLE e).op (addDerivationApp b hb D V x) = _
  rw [addDerivationApp_apply, map_add, ← h2, ← CommRingCat.comp_apply, ← Scheme.Hom.appLE]
  simp

/-- `b + D` still lifts `a` along `i`. -/
theorem comp_addDerivation : i ≫ addDerivation b hb D = a := by
  subst hb
  refine Scheme.Hom.ext_of_appLE (by rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base,
    addDerivation_base]) fun V e x ↦ ?_
  have hz : i.appLE (addDerivation b rfl D ⁻¹ᵁ V) ((i ≫ b) ⁻¹ᵁ V)
      (by rw [preimage_addDerivation]; rfl) (D.val V ⟨addDerivation b rfl D ⁻¹ᵁ V,
        by rw [preimage_addDerivation]; exact preimage_preimage_le_of_comp_eq rfl V⟩ x) = 0 := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, D.isLiftDerivation.app_apply_eq_zero, map_zero]
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    addDerivation_appLE b rfl D (preimage_addDerivation b rfl D V).le, map_add, hz, add_zero]
  exact Scheme.Hom.appLE_appLE_eq_app i b _ e x

/-- `b + D` lies over the same morphism to `S` as `b`. -/
theorem addDerivation_comp : addDerivation b hb D ≫ f = b ≫ f := by
  refine Scheme.Hom.ext_of_appLE (by rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base,
    addDerivation_base]) fun W e x ↦ ?_
  have hz := D.isLiftDerivation.map_appLE W (f ⁻¹ᵁ W) ((b ≫ f) ⁻¹ᵁ W)
    (preimage_preimage_le_of_comp_eq hb (f ⁻¹ᵁ W)) le_rfl x
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  refine (addDerivation_appLE b hb D (le_rfl : (b ≫ f) ⁻¹ᵁ W ≤ b ⁻¹ᵁ (f ⁻¹ᵁ W)) e
    (f.app W x)).trans ?_
  have hf : f.app W x = f.appLE W (f ⁻¹ᵁ W) le_rfl x := by rw [Scheme.Hom.app_eq_appLE]
  rw [hf, hz, add_zero]
  exact Scheme.Hom.appLE_appLE_eq_app b f _ _ x

end AddDerivation

variable (i a f) in
/-- The lifts of `a : T ⟶ X` along `i : T ⟶ T'` over `h : T' ⟶ S`: the morphisms `b : T' ⟶ X`
with `i ≫ b = a` and `b ≫ f = h`. -/
@[ext]
structure ThickeningLift (h : T' ⟶ S) : Type u where
  /-- The lifted morphism. -/
  hom : T' ⟶ X
  /-- The lift restricts to `a` along `i`. -/
  comp_hom : i ≫ hom = a
  /-- The lift lies over `h`. -/
  hom_comp : hom ≫ f = h

namespace ThickeningLift

variable {h : T' ⟶ S}

/-- Any two lifts along a surjective `i` have the same underlying map. -/
theorem hom_base_eq [Surjective i] (b b' : ThickeningLift i a f h) :
    b.hom.base = b'.hom.base := by
  ext x
  obtain ⟨t, rfl⟩ := i.surjective x
  have := congr(($(b.comp_hom.trans b'.comp_hom.symm)).base t)
  simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using this

/-- Any two lifts along a surjective `i` have the same preimages of opens. -/
theorem le_preimage_hom [Surjective i] (c c' : ThickeningLift i a f h) {V : X.Opens}
    {U : T'.Opens} (e : U ≤ c.hom ⁻¹ᵁ V) : U ≤ c'.hom ⁻¹ᵁ V := fun x hx ↦ by
  rw [Scheme.Hom.mem_preimage, ← hom_base_eq c c']
  exact e hx

/-- Restricting a lift to an open subset `U` of `T'`: a lift of `a` restricted to `i ⁻¹ᵁ U` along
`i ∣_ U`, over `h` restricted to `U`. -/
def restrict (b : ThickeningLift i a f h) (U : T'.Opens) :
    ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h) where
  hom := U.ι ≫ b.hom
  comp_hom := by rw [morphismRestrict_ι_assoc, b.comp_hom]
  hom_comp := by rw [Category.assoc, b.hom_comp]

/-- The restriction of a lift `b` to `U` is `U.ι ≫ b`. -/
@[simp]
theorem restrict_hom (b : ThickeningLift i a f h) (U : T'.Opens) :
    (b.restrict U).hom = U.ι ≫ b.hom := by
  rw [restrict]

variable [IsFirstOrderThickening i]

/-- Translating a lift by a derivation. -/
noncomputable instance instVAdd : VAdd (LiftDerivation i a f) (ThickeningLift i a f h) where
  vadd D b := ⟨addDerivation b.hom b.comp_hom D, comp_addDerivation b.hom b.comp_hom D,
    (addDerivation_comp b.hom b.comp_hom D).trans b.hom_comp⟩

/-- The morphism underlying `D +ᵥ b` is `b + D`. -/
@[simp]
theorem hom_vadd (D : LiftDerivation i a f) (b : ThickeningLift i a f h) :
    (D +ᵥ b).hom = addDerivation b.hom b.comp_hom D :=
  rfl

/-- The difference of two lifts on sections, `b^* x - b'^* x`. -/
private noncomputable def vsubData (b b' : ThickeningLift i a f h) : LiftDerivationData i a :=
  fun V U x ↦
    b.hom.appLE V U.val (le_preimage_of_preimage_le_of_comp_eq b.comp_hom U.property) x -
      b'.hom.appLE V U.val (le_preimage_of_preimage_le_of_comp_eq b'.comp_hom U.property) x

/-- The value of `vsubData` on a section. -/
private theorem vsubData_apply (b b' : ThickeningLift i a f h) (V : X.Opens) (U) (x : Γ(X, V)) :
    vsubData b b' V U x =
      b.hom.appLE V U.val (le_preimage_of_preimage_le_of_comp_eq b.comp_hom U.property) x -
        b'.hom.appLE V U.val (le_preimage_of_preimage_le_of_comp_eq b'.comp_hom U.property) x := by
  rw [vsubData]

/-- The difference of two lifts is a derivation into the ideal of `i`. -/
private theorem isLiftDerivation_vsubData (b b' : ThickeningLift i a f h) :
    IsLiftDerivation i a f (vsubData b b') := by
  have hi : ∀ (c : ThickeningLift i a f h) {V U} (hU : i ⁻¹ᵁ U ≤ a ⁻¹ᵁ V) (x : Γ(X, V)),
      i.app U (c.hom.appLE V U (le_preimage_of_preimage_le_of_comp_eq c.comp_hom hU) x) =
        a.appLE V _ hU x :=
    fun c _ _ hU x ↦ app_appLE_of_comp_eq c.comp_hom _ hU x
  constructor
  · intro V U hU x y
    simp only [vsubData_apply, map_add]
    abel
  · intro V U hU x
    rw [vsubData_apply, map_sub, hi b hU, hi b' hU, sub_self]
  · intro V V' U U' hU hU' hV hUU' x
    simp only [vsubData_apply, map_sub, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_map]
  · intro V U hU x y x' y' hx hy
    -- Two sections of `T'` restricting to the same section of `T` differ by a section of the
    -- ideal of `i`; the product of two such differences vanishes.
    have hI {s s' : Γ(T', U)} {z : Γ(X, V)} (hs : i.app U s = a.appLE V _ hU z)
        (hs' : i.app U s' = a.appLE V _ hU z) : i.app U (s - s') = 0 := by
      rw [map_sub, hs, hs', sub_self]
    have h1 := IsFirstOrderThickening.mul_eq_zero_of_app_eq_zero i (hI hx (hi b hU x))
      (hI (hi b hU y) (hi b' hU y))
    have h2 := IsFirstOrderThickening.mul_eq_zero_of_app_eq_zero i (hI hy (hi b' hU y))
      (hI (hi b hU x) (hi b' hU x))
    simp only [vsubData_apply, map_mul]
    linear_combination -h1 - h2
  · intro W V U hU e s
    have hle : U ≤ h ⁻¹ᵁ W := by
      rw [← b.hom_comp]
      exact (le_preimage_of_preimage_le_of_comp_eq b.comp_hom hU).trans (b.hom.preimage_mono e)
    have hf : ∀ c : ThickeningLift i a f h,
        c.hom.appLE V U (le_preimage_of_preimage_le_of_comp_eq c.comp_hom hU) (f.appLE W V e s) =
          h.appLE W U hle s := fun c ↦ by
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      exact congr($(Scheme.Hom.congr_appLE _ c.hom_comp _ _ _ _) s)
    rw [vsubData_apply, hf, hf, sub_self]

/-- The difference of two lifts is a derivation. Its body is not exposed: use `coe_vsub_apply`. -/
@[no_expose]
noncomputable instance instVSub : VSub (LiftDerivation i a f) (ThickeningLift i a f h) where
  vsub b b' := ⟨vsubData b b', isLiftDerivation_vsubData b b'⟩

/-- On sections, `(b -ᵥ b') x = b^* x - b'^* x`. -/
@[simp]
theorem coe_vsub_apply (b b' : ThickeningLift i a f h) (V : X.Opens) (U) (x : Γ(X, V)) :
    (b -ᵥ b' : LiftDerivation i a f).val V U x =
      b.hom.appLE V U.val (le_preimage_of_preimage_le_of_comp_eq b.comp_hom U.property) x -
        b'.hom.appLE V U.val (le_preimage_of_preimage_le_of_comp_eq b'.comp_hom U.property) x :=
  vsubData_apply b b' V U x

/-- On sections, `(D +ᵥ b)^* x = b^* x + D x`. -/
theorem hom_vadd_appLE (D : LiftDerivation i a f) (b : ThickeningLift i a f h) {V : X.Opens}
    {U : T'.Opens} (e : U ≤ b.hom ⁻¹ᵁ V) (e' : U ≤ (D +ᵥ b).hom ⁻¹ᵁ V) (x : Γ(X, V)) :
    (D +ᵥ b).hom.appLE V U e' x = b.hom.appLE V U e x +
      D.val V ⟨U, (i.preimage_mono e).trans (preimage_preimage_le_of_comp_eq b.comp_hom V)⟩ x :=
  addDerivation_appLE b.hom b.comp_hom D e e' x

/-- **The lifts form a torsor.** When `a` has a lift along a first-order thickening `i` over
`h`, the lifts form a torsor under the derivations of `𝒪_X` over `𝒪_S` into the ideal of `i`. -/
noncomputable instance instAddTorsor [Nonempty (ThickeningLift i a f h)] :
    AddTorsor (LiftDerivation i a f) (ThickeningLift i a f h) where
  zero_vadd b := ThickeningLift.ext <| Scheme.Hom.ext_of_appLE_eq_appLE (hom_base_eq _ _)
    fun V U e e' x ↦ by rw [hom_vadd_appLE _ _ e' e]; simp
  add_vadd D D' b := ThickeningLift.ext <| Scheme.Hom.ext_of_appLE_eq_appLE (hom_base_eq _ _)
    fun V U e e' x ↦ by
      rw [hom_vadd_appLE _ _ (le_preimage_hom _ b e) e,
        hom_vadd_appLE D (D' +ᵥ b) (le_preimage_hom _ (D' +ᵥ b) e') e',
        hom_vadd_appLE D' b (le_preimage_hom _ b e')]
      simp only [AddSubgroup.coe_add, Pi.add_apply]
      abel
  vsub_vadd' b b' := ThickeningLift.ext <| Scheme.Hom.ext_of_appLE_eq_appLE (hom_base_eq _ _)
    fun V U e e' x ↦ by
      rw [hom_vadd_appLE _ _ (le_preimage_hom _ b' e), coe_vsub_apply]
      simp
  vadd_vsub' D b := by
    ext V U x
    rw [coe_vsub_apply,
      hom_vadd_appLE _ _ (le_preimage_of_preimage_le_of_comp_eq b.comp_hom U.property)]
    simp

/-- **Uniqueness of lifts along a formally étale morphism.** Lifts along a first-order thickening
through a formally étale morphism are unique, for any `T'`: a formally étale morphism is formally
unramified, and first-order thickenings have nilpotent ideal sheaf. -/
instance instSubsingleton [FormallyEtale f] : Subsingleton (ThickeningLift i a f h) :=
  ⟨fun b b' ↦ ThickeningLift.ext <|
    FormallyUnramified.hom_ext i (IsFirstOrderThickening.isNilpotent_ker i) f
      (b.comp_hom.trans b'.comp_hom.symm) (b.hom_comp.trans b'.hom_comp.symm)⟩

end ThickeningLift

/-- **Local existence of lifts.** For `f` smooth, `i : T ⟶ T'` a first-order thickening and
`a : T ⟶ X` lying over `h : T' ⟶ S`, every point of `T'` has an open neighbourhood `U` over which
`a` lifts: there is a lift of `a` restricted to `i ⁻¹ᵁ U` along `i ∣_ U`, over `h` restricted
to `U`. -/
theorem exists_thickeningLift_restrict [Smooth f] [IsFirstOrderThickening i] (h : T' ⟶ S)
    (ha : a ≫ f = i ≫ h) (x : T') :
    ∃ U : T'.Opens, x ∈ U ∧ Nonempty (ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) := by
  obtain ⟨t, rfl⟩ := i.surjective x
  have hht : f (a t) = h (i t) := by
    rw [← Scheme.Hom.comp_apply, ha, Scheme.Hom.comp_apply]
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show h (i t) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, htV, hVW : V ≤ f ⁻¹ᵁ W⟩ := exists_isAffineOpen_mem_and_subset
    (show a t ∈ f ⁻¹ᵁ W by rw [Scheme.Hom.mem_preimage, hht]; exact hxW)
  let U₀ : T'.Opens := ⟨i '' (a ⁻¹ᵁ V),
    (IsUniversalHomeomorphism.isHomeomorph i).isOpenMap _ (a ⁻¹ᵁ V).isOpen⟩
  obtain ⟨U, hU, hxU, hUle⟩ := exists_isAffineOpen_mem_and_subset
    (show i t ∈ U₀ ⊓ h ⁻¹ᵁ W from ⟨⟨t, htV, rfl⟩, hxW⟩)
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : IsAffine W := hW
  have hiU : i ⁻¹ᵁ U ≤ a ⁻¹ᵁ V := fun t' ht' ↦ by
    obtain ⟨t'', ht'', he⟩ := (hUle ht').left
    rwa [← i.isClosedEmbedding.injective he]
  have hg : Set.range ((i ⁻¹ᵁ U).ι ≫ a) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t', rfl⟩
    exact hiU t'.property
  have hh : Set.range (U.ι ≫ h) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x', rfl⟩
    exact (hUle x'.property).right
  let g' : (i ⁻¹ᵁ U).toScheme ⟶ V := IsOpenImmersion.lift V.ι ((i ⁻¹ᵁ U).ι ≫ a) hg
  let h' : U.toScheme ⟶ W := IsOpenImmersion.lift W.ι (U.ι ≫ h) hh
  obtain ⟨l, hl₁, hl₂⟩ := FormallySmooth.exists_lift (f := f.resLE W V hVW) (i ∣_ U) g' h' (by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι]
    simp only [g', h']
    rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac, morphismRestrict_ι_assoc,
      Category.assoc, ha])
  refine ⟨U, hxU, ⟨⟨l ≫ V.ι, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, hl₁]
    exact IsOpenImmersion.lift_fac _ _ _
  · rw [Category.assoc, ← f.resLE_comp_ι hVW, ← Category.assoc, hl₂]
    exact IsOpenImmersion.lift_fac _ _ _

end TauCeti.AlgebraicGeometry
