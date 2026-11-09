/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.Thickening

/-!
# Adic thickening systems

An *adic thickening system* is a sequence of schemes `X n` (`n : ℕ`) equipped with transition
thickenings `ι n : X n ⟶ X (n + 1)` such that each `X n` is cut out inside `X (n + 1)` by the
`(n + 1)`-st power of the ideal sheaf of `X 0` in `X (n + 1)`:
`(ι n).ker = (levelMap X ι (n + 1)).ker ^ (n + 1)` (Stacks, Definition 87.9.9 (0AIF), retained as
an explicit tower of infinitesimal levels rather than a colimit of sheaves).

Because the adic relation at level `n + 1` forces the `(n + 2)`-nd power of the ideal sheaf of
`X 0` in `X (n + 1)` to vanish (`ker_levelMap_pow_succ_eq_bot`), every transition morphism `ι n`
in an adic thickening system is automatically a first-order thickening (`isFirstOrderThickening_ι`),
and more generally the composite transition `X m ⟶ X n` (`m ≤ n`) has ideal sheaf equal to the
`(m + 1)`-st power of the ideal sheaf of `X 0` in `X n` (`ker_transition`).

Morphisms of adic thickening systems are families of scheme morphisms `app n : X n ⟶ Y n`
commuting with the transitions `ι n`. Note that these morphisms are level-preserving; they form a
stricter category than continuous morphisms of formal schemes. A morphism `f` is *adic*
(`IsAdicHom f`) when every transition square is cartesian, equivalently when the ideal sheaf of
`Y n` in `Y (n + 1)` pulls back along `f.app (n + 1)` to that of `X n` in `X (n + 1)`
(`isAdicHom_iff_ker_comap`). Every scheme `S` embeds as a constant system `ofScheme.obj S`, and
this functor is fully faithful with adic image morphisms.

## Main definitions

* `TauCeti.AlgebraicGeometry.levelMap`: the composite `X 0 ⟶ X n` in a tower of schemes.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem`: a tower of thickenings satisfying the adic
  power law `(ι n).ker = (levelMap X ι (n + 1)).ker ^ (n + 1)`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.reduction`: the `n`-th level `X n` of a system.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.transition`: the transition thickening
  `X m ⟶ X n` for `m ≤ n`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.Hom`: level-preserving morphisms of systems,
  making `AdicThickeningSystem` a category.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.IsAdicHom`: morphisms whose transition squares
  are cartesian.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.ofScheme`: the fully faithful functor sending a
  scheme `S` to the constant adic thickening system `(S, 𝟙 S)`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.IsLocallyNoetherian`: systems whose levels are
  all locally Noetherian schemes.

## Main results

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.ker_levelMap_pow_succ_eq_bot`: the ideal sheaf of
  `X 0` in `X n` has `(n + 1)`-st power zero.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.isFirstOrderThickening_ι`: every step transition
  `ι n` in an adic thickening system is a first-order thickening.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.ker_transition`: for `m ≤ n`, the kernel of
  `X m ⟶ X n` is `(levelMap n).ker ^ (m + 1)`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.isAdicHom_iff_ker_comap`: characterization of
  adic morphisms by inverse images of transition ideal sheaves.

## References

* [Stacks Project, Definition 87.9.9](https://stacks.math.columbia.edu/tag/0AIF).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- The level maps `X 0 ⟶ X n` of a tower of schemes `(X, ι)`. -/
def levelMap (X : ℕ → Scheme.{u}) (ι : ∀ n, X n ⟶ X (n + 1)) : ∀ n, X 0 ⟶ X n
  | 0 => 𝟙 _
  | n + 1 => levelMap X ι n ≫ ι n

@[simp]
theorem levelMap_zero (X : ℕ → Scheme.{u}) (ι : ∀ n, X n ⟶ X (n + 1)) :
    levelMap X ι 0 = 𝟙 (X 0) :=
  (rfl)

@[simp]
theorem levelMap_succ (X : ℕ → Scheme.{u}) (ι : ∀ n, X n ⟶ X (n + 1)) (n : ℕ) :
    levelMap X ι (n + 1) = levelMap X ι n ≫ ι n :=
  (rfl)

/-- If every transition of a tower is a thickening, then every level map `X 0 ⟶ X n` is a
thickening. -/
theorem isThickening_levelMap {X : ℕ → Scheme.{u}} {ι : ∀ n, X n ⟶ X (n + 1)}
    (h : ∀ n, IsThickening (ι n)) (n : ℕ) : IsThickening (levelMap X ι n) := by
  induction n with
  | zero =>
    rw [levelMap_zero]
    infer_instance
  | succ n ih =>
    have := h n
    exact IsThickening.comp (levelMap X ι n) (ι n)

/-- A tower of thickenings in which each `X n` is cut out inside `X (n + 1)` by the `(n + 1)`-st
power of the ideal sheaf of `X 0` in `X (n + 1)`.
Stacks, Definition 87.9.9 (0AIF). -/
@[stacks 0AIF]
structure AdicThickeningSystem where
  /-- The `n`-th infinitesimal level `X n` of the system. -/
  X : ℕ → Scheme.{u}
  /-- The step transition morphism `X n ⟶ X (n + 1)`. -/
  ι : ∀ n, X n ⟶ X (n + 1)
  /-- Every step transition is a thickening of schemes. -/
  isThickening : ∀ n, IsThickening (ι n)
  /-- Each `X n` is the `n`-th infinitesimal neighbourhood of `X 0` inside `X (n + 1)`. -/
  adic : ∀ n, (ι n).ker = (levelMap X ι (n + 1)).ker ^ (n + 1)

attribute [instance] AdicThickeningSystem.isThickening

namespace AdicThickeningSystem

section Tower

variable (𝔛 : AdicThickeningSystem.{u})

/-- The `n`-th reduction scheme `X n` of an adic thickening system. -/
def reduction (n : ℕ) : Scheme.{u} :=
  𝔛.X n

@[simp]
theorem reduction_eq (n : ℕ) : 𝔛.reduction n = 𝔛.X n :=
  (rfl)

/-- The canonical thickening `X 0 ⟶ X n` from the initial level to level `n`. -/
def levelMap (n : ℕ) : 𝔛.X 0 ⟶ 𝔛.X n :=
  TauCeti.AlgebraicGeometry.levelMap 𝔛.X 𝔛.ι n

@[simp]
theorem levelMap_zero : 𝔛.levelMap 0 = 𝟙 (𝔛.X 0) :=
  (rfl)

theorem levelMap_succ (n : ℕ) : 𝔛.levelMap (n + 1) = 𝔛.levelMap n ≫ 𝔛.ι n :=
  (rfl)

instance isThickening_levelMap (n : ℕ) : IsThickening (𝔛.levelMap n) :=
  TauCeti.AlgebraicGeometry.isThickening_levelMap 𝔛.isThickening n

/-- In an adic thickening system, the ideal sheaf of `X n` in `X (n + 1)` is the `(n + 1)`-st
power of the ideal sheaf of `X 0` in `X (n + 1)`. -/
theorem ker_ι (n : ℕ) : (𝔛.ι n).ker = (𝔛.levelMap (n + 1)).ker ^ (n + 1) :=
  𝔛.adic n

/-- Pulling the ideal sheaf of `X 0` in `X (n + 1)` back along `ι n` gives the ideal sheaf of
`X 0` in `X n`. -/
@[simp]
theorem ker_levelMap_comap_ι (n : ℕ) :
    (𝔛.levelMap (n + 1)).ker.comap (𝔛.ι n) = (𝔛.levelMap n).ker :=
  Scheme.Hom.comap_ker_comp_of_isClosedImmersion (𝔛.levelMap n) (𝔛.ι n)

/-- The ideal sheaf cutting out `X 0` in `X n` has `(n + 1)`-st power zero: its `(n + 1)`-st power
is the inverse image along `ι n` of `(levelMap (n + 1)).ker ^ (n + 1) = (ι n).ker`, which vanishes
on `X n`. -/
@[simp]
theorem ker_levelMap_pow_succ_eq_bot (n : ℕ) : (𝔛.levelMap n).ker ^ (n + 1) = ⊥ := by
  rw [← 𝔛.ker_levelMap_comap_ι n, ← Scheme.IdealSheafData.comap_pow, ← 𝔛.ker_ι n,
    Scheme.Hom.comap_ker_self]

/-- Every transition `ι n : X n ⟶ X (n + 1)` of an adic thickening system is a first-order
thickening, because `(n + 1) + (n + 1) ≥ n + 2` and `(levelMap (n + 1)).ker ^ (n + 2) = ⊥`. -/
instance isFirstOrderThickening_ι (n : ℕ) : IsFirstOrderThickening (𝔛.ι n) where
  ker_mul_self := by
    rw [𝔛.ker_ι n, ← pow_add]
    refine le_bot_iff.mp
      ((pow_le_pow_of_le_one bot_le le_top (m := n + 2) (by omega)).trans_eq ?_)
    exact 𝔛.ker_levelMap_pow_succ_eq_bot (n + 1)

/-- The composite transition thickening `X m ⟶ X n` for `m ≤ n`. -/
def transition : ∀ {m n : ℕ}, m ≤ n → (𝔛.X m ⟶ 𝔛.X n)
  | _, 0, h => eqToHom (congrArg 𝔛.X (by omega))
  | m, n + 1, h =>
    if h' : m ≤ n then transition h' ≫ 𝔛.ι n else eqToHom (congrArg 𝔛.X (by omega))

@[simp]
theorem transition_refl (m : ℕ) : 𝔛.transition (le_refl m) = 𝟙 (𝔛.X m) := by
  cases m with
  | zero => rfl
  | succ m =>
    have hm : ¬ m + 1 ≤ m := by omega
    simp [transition, hm]

theorem transition_succ_of_le {m n : ℕ} (h : m ≤ n) :
    𝔛.transition (Nat.le_succ_of_le h) = 𝔛.transition h ≫ 𝔛.ι n := by
  rw [transition, dite_eq_left_of_eq_true (eq_true h)]

@[simp]
theorem transition_self_succ (n : ℕ) : 𝔛.transition (Nat.le_succ n) = 𝔛.ι n := by
  rw [𝔛.transition_succ_of_le (le_refl n), 𝔛.transition_refl, Category.id_comp]

@[reassoc (attr := simp)]
theorem transition_comp {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) :
    𝔛.transition h₁ ≫ 𝔛.transition h₂ = 𝔛.transition (h₁.trans h₂) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    by_cases hmn : m ≤ n
    · have h₂' : 𝔛.transition h₂ = 𝔛.transition hmn ≫ 𝔛.ι n := 𝔛.transition_succ_of_le hmn
      rw [h₂', ← Category.assoc, ih hmn, ← 𝔛.transition_succ_of_le (h₁.trans hmn)]
    · obtain rfl : m = n + 1 := by omega
      simp

theorem levelMap_eq_transition (n : ℕ) : 𝔛.levelMap n = 𝔛.transition (Nat.zero_le n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [levelMap_succ, ih, ← 𝔛.transition_succ_of_le (Nat.zero_le n)]

instance isThickening_transition {m n : ℕ} (h : m ≤ n) : IsThickening (𝔛.transition h) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    rw [𝔛.transition_refl]
    infer_instance
  | succ n ih =>
    by_cases h' : m ≤ n
    · have hh : 𝔛.transition h = 𝔛.transition h' ≫ 𝔛.ι n := 𝔛.transition_succ_of_le h'
      rw [hh]
      have := ih h'
      infer_instance
    · obtain rfl : m = n + 1 := by omega
      rw [𝔛.transition_refl]
      infer_instance

/-- For every `m ≤ n`, the ideal sheaf of `X m ⟶ X n` is the `(m + 1)`-st power of the ideal sheaf
of `X 0 ⟶ X n`. At `m = n` both sides are `⊥` by `ker_levelMap_pow_succ_eq_bot`. -/
theorem ker_transition {m n : ℕ} (h : m ≤ n) :
    (𝔛.transition h).ker = (𝔛.levelMap n).ker ^ (m + 1) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    simp
  | succ n ih =>
    by_cases h' : m ≤ n
    · have hh : 𝔛.transition h = 𝔛.transition h' ≫ 𝔛.ι n := 𝔛.transition_succ_of_le h'
      rw [hh, Scheme.Hom.ker_comp, ih h', ← 𝔛.ker_levelMap_comap_ι n,
        ← Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.map_comap_of_isClosedImmersion,
        𝔛.ker_ι n, sup_eq_left.mpr (pow_le_pow_of_le_one bot_le le_top (Nat.succ_le_succ h'))]
    · obtain rfl : m = n + 1 := by omega
      rw [𝔛.transition_refl, Scheme.Hom.ker_eq_bot_of_isIso, 𝔛.ker_levelMap_pow_succ_eq_bot]

/-- Every level of an adic thickening system has the same underlying topological space as level `0`,
via the homeomorphism induced by the thickening `levelMap n`. -/
noncomputable def homeomorphLevel (n : ℕ) : 𝔛.X 0 ≃ₜ 𝔛.X n :=
  (IsUniversalHomeomorphism.isHomeomorph (𝔛.levelMap n)).homeomorph

@[simp]
theorem homeomorphLevel_apply (n : ℕ) (x : 𝔛.X 0) :
    𝔛.homeomorphLevel n x = 𝔛.levelMap n x := by
  simp [homeomorphLevel]

end Tower

/-! ### Category of adic thickening systems and adic morphisms -/

/-- A level-preserving morphism of adic thickening systems is a family of scheme morphisms
`app n : 𝔛.X n ⟶ 𝔜.X n` commuting with the transition thickenings `ι n`. -/
@[ext]
structure Hom (𝔛 𝔜 : AdicThickeningSystem.{u}) where
  /-- The component morphism at level `n`. -/
  app : ∀ n, 𝔛.X n ⟶ 𝔜.X n
  /-- Compatibility of the components with the step transitions `ι n`. -/
  naturality : ∀ n, 𝔛.ι n ≫ app (n + 1) = app n ≫ 𝔜.ι n := by cat_disch

attribute [reassoc (attr := simp)] Hom.naturality

instance : Category AdicThickeningSystem.{u} where
  Hom := Hom
  id 𝔛 :=
    { app n := 𝟙 (𝔛.X n) }
  comp f g :=
    { app n := f.app n ≫ g.app n
      naturality n := by rw [← Category.assoc, f.naturality, Category.assoc, g.naturality,
        Category.assoc] }

@[ext]
theorem hom_ext {𝔛 𝔜 : AdicThickeningSystem.{u}} {f g : 𝔛 ⟶ 𝔜}
    (h : ∀ n, f.app n = g.app n) : f = g :=
  Hom.ext (funext h)

@[simp]
theorem id_app (𝔛 : AdicThickeningSystem.{u}) (n : ℕ) :
    (𝟙 𝔛 : 𝔛 ⟶ 𝔛).app n = 𝟙 (𝔛.X n) :=
  (rfl)

@[reassoc, simp]
theorem comp_app {𝔛 𝔜 𝔚 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) (g : 𝔜 ⟶ 𝔚) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n :=
  (rfl)

@[reassoc]
theorem Hom.transition_app {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜)
    {m n : ℕ} (h : m ≤ n) :
    𝔛.transition h ≫ f.app n = f.app m ≫ 𝔜.transition h := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    simp
  | succ n ih =>
    by_cases h' : m ≤ n
    · rw [𝔛.transition_succ_of_le h', 𝔜.transition_succ_of_le h', Category.assoc, f.naturality,
        ← Category.assoc, ih h', Category.assoc]
    · obtain rfl : m = n + 1 := by omega
      simp

@[reassoc (attr := simp)]
theorem Hom.levelMap_app {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) (n : ℕ) :
    𝔛.levelMap n ≫ f.app n = f.app 0 ≫ 𝔜.levelMap n := by
  rw [𝔛.levelMap_eq_transition, 𝔜.levelMap_eq_transition, f.transition_app]

/-- Construct an isomorphism of adic thickening systems from compatible levelwise scheme
isomorphisms. -/
def isoMk {𝔛 𝔜 : AdicThickeningSystem.{u}} (e : ∀ n, 𝔛.X n ≅ 𝔜.X n)
    (h : ∀ n, 𝔛.ι n ≫ (e (n + 1)).hom = (e n).hom ≫ 𝔜.ι n := by cat_disch) : 𝔛 ≅ 𝔜 where
  hom :=
    { app n := (e n).hom
      naturality := h }
  inv :=
    { app n := (e n).inv
      naturality n := by
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, h n] }

@[simp]
theorem isoMk_hom_app {𝔛 𝔜 : AdicThickeningSystem.{u}} (e : ∀ n, 𝔛.X n ≅ 𝔜.X n)
    (h : ∀ n, 𝔛.ι n ≫ (e (n + 1)).hom = (e n).hom ≫ 𝔜.ι n) (n : ℕ) :
    (isoMk e h).hom.app n = (e n).hom :=
  (rfl)

@[simp]
theorem isoMk_inv_app {𝔛 𝔜 : AdicThickeningSystem.{u}} (e : ∀ n, 𝔛.X n ≅ 𝔜.X n)
    (h : ∀ n, 𝔛.ι n ≫ (e (n + 1)).hom = (e n).hom ≫ 𝔜.ι n) (n : ℕ) :
    (isoMk e h).inv.app n = (e n).inv :=
  (rfl)

/-- The component isomorphism at level `n` induced by an isomorphism of adic thickening systems. -/
def appIso {𝔛 𝔜 : AdicThickeningSystem.{u}} (e : 𝔛 ≅ 𝔜) (n : ℕ) : 𝔛.X n ≅ 𝔜.X n where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := by rw [← comp_app, e.hom_inv_id, id_app]
  inv_hom_id := by rw [← comp_app, e.inv_hom_id, id_app]

@[simp]
theorem appIso_hom {𝔛 𝔜 : AdicThickeningSystem.{u}} (e : 𝔛 ≅ 𝔜) (n : ℕ) :
    (appIso e n).hom = e.hom.app n :=
  (rfl)

@[simp]
theorem appIso_inv {𝔛 𝔜 : AdicThickeningSystem.{u}} (e : 𝔛 ≅ 𝔜) (n : ℕ) :
    (appIso e n).inv = e.inv.app n :=
  (rfl)

instance isIso_app_of_isIso {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) [IsIso f] (n : ℕ) :
    IsIso (f.app n) :=
  (appIso (asIso f) n).isIso_hom

/-- A morphism of adic thickening systems is an isomorphism if and only if each levelwise component
is an isomorphism of schemes. -/
theorem isIso_iff_forall_isIso_app {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) :
    IsIso f ↔ ∀ n, IsIso (f.app n) :=
  ⟨fun _ n ↦ inferInstance, fun h ↦
    ⟨(isoMk (fun n ↦ @asIso _ _ _ _ (f.app n) (h n)) f.naturality).inv, by ext; simp, by ext; simp⟩⟩

/-- A morphism `f : 𝔛 ⟶ 𝔜` of adic thickening systems is *adic* if every step transition square is
cartesian, so that `𝔛.X n` is the pullback of `𝔜.X n` along `f.app (n + 1)`. -/
@[mk_iff]
class IsAdicHom {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) : Prop where
  /-- Each transition square of `f` is a pullback square of schemes. -/
  isPullback : ∀ n, IsPullback (𝔛.ι n) (f.app n) (f.app (n + 1)) (𝔜.ι n)

/-- A morphism of adic thickening systems is adic if and only if at each level `n` the ideal sheaf
of `𝔜.ι n` pulls back along `f.app (n + 1)` to the ideal sheaf of `𝔛.ι n`. -/
theorem isAdicHom_iff_ker_comap {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) :
    IsAdicHom f ↔ ∀ n, (𝔜.ι n).ker.comap (f.app (n + 1)) = (𝔛.ι n).ker := by
  rw [isAdicHom_iff]
  refine forall_congr' fun n ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (Scheme.IdealSheafData.ker_eq_comap_of_isPullback (𝔜.ι n) h).symm
  · exact isPullback_of_isClosedImmersion (𝔛.ι n) (𝔜.ι n) (f.app n) (f.app (n + 1))
      (f.naturality n) h

namespace IsAdicHom

/-- For an adic morphism `f`, all composite transition squares (`m ≤ n`) are cartesian. -/
theorem isPullback_transition {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) [IsAdicHom f]
    {m n : ℕ} (h : m ≤ n) :
    IsPullback (𝔛.transition h) (f.app m) (f.app n) (𝔜.transition h) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    rw [𝔛.transition_refl, 𝔜.transition_refl]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  | succ n ih =>
    by_cases h' : m ≤ n
    · rw [𝔛.transition_succ_of_le h', 𝔜.transition_succ_of_le h']
      exact (ih h').paste_horiz (IsAdicHom.isPullback n)
    · obtain rfl : m = n + 1 := by omega
      rw [𝔛.transition_refl, 𝔜.transition_refl]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- For an adic morphism `f`, the level-map square between level `0` and level `n` is cartesian. -/
theorem isPullback_levelMap {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) [IsAdicHom f] (n : ℕ) :
    IsPullback (𝔛.levelMap n) (f.app 0) (f.app n) (𝔜.levelMap n) := by
  rw [𝔛.levelMap_eq_transition, 𝔜.levelMap_eq_transition]
  exact isPullback_transition f (Nat.zero_le n)

instance id (𝔛 : AdicThickeningSystem.{u}) : IsAdicHom (𝟙 𝔛) where
  isPullback _ := (IsPullback.of_horiz_isIso (fst := 𝟙 _) (g := 𝟙 _) ⟨by simp⟩).flip

instance comp {𝔛 𝔜 𝔚 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) (g : 𝔜 ⟶ 𝔚)
    [IsAdicHom f] [IsAdicHom g] : IsAdicHom (f ≫ g) where
  isPullback n := (IsAdicHom.isPullback (f := f) n).paste_vert (IsAdicHom.isPullback (f := g) n)

instance (priority := 100) of_isIso {𝔛 𝔜 : AdicThickeningSystem.{u}} (f : 𝔛 ⟶ 𝔜) [IsIso f] :
    IsAdicHom f where
  isPullback n := (IsPullback.of_horiz_isIso (fst := f.app n) (g := f.app (n + 1))
    ⟨(f.naturality n).symm⟩).flip

end IsAdicHom

/-! ### Constant systems from schemes and locally Noetherian systems -/

/-- A scheme `S` viewed as the constant adic thickening system with `X n = S` and `ι n = 𝟙 S`,
functorially in `S`. -/
-- `@[expose]` is forced by dependent typing of component morphisms: without `(ofScheme.obj S).X n`
-- reducing definitionally to `S`, `ofScheme_obj_ι`, `ofScheme_map_app`,
-- `ofSchemeFullyFaithful_preimage`, and `spfToSpec_app` do not typecheck.
@[expose, simps]
def ofScheme : Scheme.{u} ⥤ AdicThickeningSystem.{u} where
  obj S :=
    { X _ := S
      ι _ := 𝟙 S
      isThickening _ := inferInstance
      adic n := by
        have hlev (m : ℕ) :
            TauCeti.AlgebraicGeometry.levelMap (fun _ ↦ S) (fun _ ↦ 𝟙 S) m = 𝟙 S := by
          induction m with
          | zero => rfl
          | succ m ih => simp [ih]
        rw [hlev (n + 1), Scheme.Hom.ker_eq_bot_of_isIso,
          ← Scheme.IdealSheafData.zero_eq_bot, zero_pow (Nat.succ_ne_zero n)] }
  map g :=
    { app _ := g }

/-- Every morphism between constant adic thickening systems induced by a morphism of schemes is
adic, since all horizontal transitions are identities. -/
instance isAdicHom_ofScheme_map {S T : Scheme.{u}} (g : S ⟶ T) :
    IsAdicHom (ofScheme.map g) where
  isPullback _ := IsPullback.of_horiz_isIso (fst := 𝟙 S) (g := 𝟙 T) ⟨by simp⟩

/-- The constant-system functor `ofScheme` is fully faithful: a compatible family of morphisms
between constant systems is constant across all levels. -/
def ofSchemeFullyFaithful : ofScheme.{u}.FullyFaithful where
  preimage f := f.app 0
  map_preimage f := by
    ext n
    induction n with
    | zero => rfl
    | succ n ih =>
      have h : 𝟙 _ ≫ f.app (n + 1) = f.app n ≫ 𝟙 _ := f.naturality n
      rw [Category.id_comp, Category.comp_id] at h
      exact ih.trans h.symm
  preimage_map _ := rfl

@[simp]
theorem ofSchemeFullyFaithful_preimage {S T : Scheme.{u}}
    (f : ofScheme.obj S ⟶ ofScheme.obj T) :
    ofSchemeFullyFaithful.preimage f = f.app 0 :=
  (rfl)

instance : ofScheme.{u}.Full := ofSchemeFullyFaithful.full
instance : ofScheme.{u}.Faithful := ofSchemeFullyFaithful.faithful

/-- An adic thickening system is *locally Noetherian* if every level `X n` is a locally Noetherian
scheme. -/
@[mk_iff]
class IsLocallyNoetherian (𝔛 : AdicThickeningSystem.{u}) : Prop where
  /-- Each level `X n` is locally Noetherian. -/
  level : ∀ n, AlgebraicGeometry.IsLocallyNoetherian (𝔛.X n)

attribute [instance] IsLocallyNoetherian.level

/-- Locally Noetherian adic thickening systems are invariant under isomorphism. -/
theorem IsLocallyNoetherian.of_iso {𝔛 𝔜 : AdicThickeningSystem.{u}} (e : 𝔛 ≅ 𝔜)
    [𝔛.IsLocallyNoetherian] : 𝔜.IsLocallyNoetherian where
  level n := by
    have : LocallyOfFiniteType (e.inv.app n) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (e.inv.app n)

@[simp]
theorem isLocallyNoetherian_ofScheme_iff (S : Scheme.{u}) :
    (ofScheme.obj S).IsLocallyNoetherian ↔ AlgebraicGeometry.IsLocallyNoetherian S :=
  ⟨fun h ↦ h.level 0, fun h ↦ ⟨fun _ ↦ h⟩⟩

instance isLocallyNoetherian_ofScheme (S : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian S] :
    (ofScheme.obj S).IsLocallyNoetherian :=
  (isLocallyNoetherian_ofScheme_iff S).mpr inferInstance

end AdicThickeningSystem

end TauCeti.AlgebraicGeometry
