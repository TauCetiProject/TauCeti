/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The nonabelian `lim¹` of a tower of groups

A tower of groups `G₀ ← G₁ ← G₂ ← ⋯` is given by its transition homomorphisms
`rₙ : Gₙ₊₁ →* Gₙ` (`TauCeti.GroupTower`). The product `∏ₙ Gₙ` acts on the set `∏ₙ Gₙ` by
`(g • h)ₙ = gₙ hₙ rₙ(gₙ₊₁)⁻¹`. The stabilizer of the identity family is the subgroup `lim G` of
compatible families, and the orbit set of this action is the *nonabelian* `lim¹ G` of Bousfield
and Kan. It is only a pointed set, pointed by the orbit of the identity family, and it vanishes
exactly when the action is transitive, for instance when every transition map is surjective.

These are the terms of the Milnor sequence for the components of a homotopy limit of a tower of
spaces, such as the mapping space out of a CW complex along its skeleta: there `Gₙ` is the
fundamental group of the `n`-th stage at a chosen compatible family of base points.

Algebraically, the orbit of an arbitrary family of group elements `x : ∀ n, G n` (with no
compatibility condition) may serve as the reference orbit instead of that of `1`. Changing the
reference to `x` replaces the transition maps by their conjugates `gₙ₊₁ ↦ xₙ rₙ(gₙ₊₁) xₙ⁻¹`
(`TauCeti.GroupTower.conj`); right translation by `x⁻¹` identifies the two orbit sets, sending the
orbit of `x` to the base point (`TauCeti.GroupTower.limOneEquivConj`), and the stabilizer of `x`
is the limit of the conjugated tower (`TauCeti.GroupTower.stabilizer_eq_lim_conj`).

When the groups are abelian this orbit set is the cokernel of the shift map
`gₙ ↦ gₙ rₙ(gₙ₊₁)⁻¹`; for towers of modules this comparison with `TauCeti.ModuleTower.limOne` is
`TauCeti.ModuleTower.groupTowerLimOneEquiv`.

## Main definitions

* `TauCeti.GroupTower`: a tower of groups, given by its transition homomorphisms.
* `TauCeti.GroupTower.Twisted`: the product `∏ₙ Gₙ` with the twisted action of `∏ₙ Gₙ`.
* `TauCeti.GroupTower.lim`: the subgroup of compatible families.
* `TauCeti.GroupTower.limOne`: the orbit set of the twisted action, pointed by the orbit of `1`.
* `TauCeti.GroupTower.Hom`: morphisms of towers, with the induced maps `Hom.limMap` and
  `Hom.limOneMap`.
* `TauCeti.GroupTower.conj`: the tower conjugated by a family of elements.

## Main statements

* `TauCeti.GroupTower.stabilizer_one`: the stabilizer of the identity family is `lim G`.
* `TauCeti.GroupTower.limOne_mk_eq_mk_iff`: two families have the same class in `lim¹ G` exactly
  when the action of some `g` carries one to the other.
* `TauCeti.GroupTower.isPretransitive_of_surjective`: if every transition map is surjective, the
  twisted action is transitive.
* `TauCeti.GroupTower.subsingleton_limOne_of_surjective`: towers with surjective transition maps
  have trivial `lim¹`.
* `TauCeti.GroupTower.limOneEquivConj`: change of the reference family.

## References

* A. K. Bousfield and D. M. Kan, *Homotopy limits, completions and localizations*, Lecture Notes
  in Mathematics 304, Springer, 1972, Chapter IX, §2.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section VI.2.
-/

public section

namespace TauCeti

universe u v w

/-- A tower of groups `G₀ ← G₁ ← G₂ ← ⋯`, given by its transition homomorphisms
`Gₙ₊₁ →* Gₙ`. -/
abbrev GroupTower (G : ℕ → Type u) [∀ n, Group (G n)] : Type u :=
  ∀ n, G (n + 1) →* G n

namespace GroupTower

variable {G : ℕ → Type u} [∀ n, Group (G n)] (r : GroupTower G)

/-! ### The twisted action and `lim¹` -/

/-- The product `∏ₙ Gₙ` of the groups of a tower `r`, regarded as the set on which `∏ₙ Gₙ` acts
by `(g • h)ₙ = gₙ hₙ rₙ(gₙ₊₁)⁻¹`. -/
@[ext]
structure Twisted (r : GroupTower G) where
  /-- A family of elements of the groups of the tower, as a point of the twisted action. -/
  mk ::
  /-- The family of elements underlying a point of the twisted action. -/
  val : ∀ n, G n

/-- The twisted action `(g • h)ₙ = gₙ hₙ rₙ(gₙ₊₁)⁻¹` of `∏ₙ Gₙ` on `∏ₙ Gₙ`. -/
instance : SMul (∀ n, G n) r.Twisted where
  smul g x := ⟨fun n ↦ g n * x.val n * (r n (g (n + 1)))⁻¹⟩

@[simp]
lemma val_smul (g : ∀ n, G n) (x : r.Twisted) (n : ℕ) :
    (g • x).val n = g n * x.val n * (r n (g (n + 1)))⁻¹ :=
  (rfl)

instance : MulAction (∀ n, G n) r.Twisted where
  one_smul x := by ext n; simp
  mul_smul g g' x := by ext n; simp [mul_assoc]

/-- The limit `lim G` of a tower: the subgroup of families `(gₙ)` with `rₙ(gₙ₊₁) = gₙ` for
every `n`. -/
def lim : Subgroup (∀ n, G n) where
  carrier := {g | ∀ n, r n (g (n + 1)) = g n}
  mul_mem' hg hg' n := by simp [hg n, hg' n]
  one_mem' n := by simp
  inv_mem' hg n := by simp [hg n]

@[simp]
lemma mem_lim {g : ∀ n, G n} : g ∈ r.lim ↔ ∀ n, r n (g (n + 1)) = g n :=
  Iff.rfl

/-- The nonabelian `lim¹` of a tower of groups: the orbit set of the twisted action of `∏ₙ Gₙ`
on `∏ₙ Gₙ`. It is a pointed set, pointed by the orbit of the identity family. -/
abbrev limOne : Type u :=
  MulAction.orbitRel.Quotient (∀ n, G n) r.Twisted

/-- `lim¹` is pointed by the orbit of the identity family. -/
instance : One r.limOne :=
  ⟨Quotient.mk'' ⟨1⟩⟩

lemma one_def : (1 : r.limOne) = Quotient.mk'' ⟨1⟩ :=
  (rfl)

/-- Two families have the same class in `lim¹` exactly when the twisted action of some family
carries the second to the first. -/
theorem limOne_mk_eq_mk_iff {x y : ∀ n, G n} :
    (Quotient.mk'' ⟨x⟩ : r.limOne) = Quotient.mk'' ⟨y⟩ ↔
      ∃ g : ∀ n, G n, ∀ n, g n * y n * (r n (g (n + 1)))⁻¹ = x n := by
  simp [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Twisted.ext_iff,
    funext_iff]

/-- If every transition map is surjective then the twisted action is transitive: every family
lies in the orbit of the identity family. -/
theorem isPretransitive_of_surjective (h : ∀ n, Function.Surjective (r n)) :
    MulAction.IsPretransitive (∀ n, G n) r.Twisted := by
  -- `x` is carried to the identity family by the family `g` defined recursively by `g₀ = 1`
  -- and a choice of preimage `gₙ₊₁` of `gₙ xₙ`.
  have key (x : r.Twisted) : ∃ g : ∀ n, G n, g • x = ⟨1⟩ := by
    let g : ∀ n, G n := fun n ↦
      Nat.rec (motive := fun n ↦ G n) 1 (fun n gn ↦ Function.surjInv (h n) (gn * x.val n)) n
    have hg (n : ℕ) : r n (g (n + 1)) = g n * x.val n := Function.surjInv_eq (h n) _
    exact ⟨g, by ext n; simp [hg]⟩
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨g, hg⟩ := key x
  obtain ⟨g', hg'⟩ := key y
  exact ⟨g'⁻¹ * g, by rw [mul_smul, hg, ← hg', inv_smul_smul]⟩

/-- Towers with surjective transition maps have trivial `lim¹`. -/
theorem subsingleton_limOne_of_surjective (h : ∀ n, Function.Surjective (r n)) :
    Subsingleton r.limOne :=
  have := r.isPretransitive_of_surjective h
  (MulAction.pretransitive_iff_subsingleton_quotient _ _).1 this

/-! ### Change of the reference family -/

/-- The tower `r` conjugated by a family `x`, with transition maps
`gₙ₊₁ ↦ xₙ rₙ(gₙ₊₁) xₙ⁻¹`. -/
def conj (x : ∀ n, G n) : GroupTower G :=
  fun n ↦ (MulAut.conj (x n)).toMonoidHom.comp (r n)

@[simp]
lemma conj_apply (x : ∀ n, G n) (n : ℕ) (g : G (n + 1)) :
    r.conj x n g = x n * r n g * (x n)⁻¹ :=
  (rfl)

@[simp]
lemma conj_one : r.conj 1 = r := by
  ext n g
  simp

/-- Right translation by `x⁻¹` carries the twisted action of `r` to that of the conjugated tower
`r.conj x`, and the family `x` to the identity family. -/
def twistedEquivConj (x : ∀ n, G n) : r.Twisted ≃ (r.conj x).Twisted where
  toFun y := ⟨y.val * x⁻¹⟩
  invFun y := ⟨y.val * x⟩
  left_inv y := by ext n; simp
  right_inv y := by ext n; simp

@[simp]
lemma val_twistedEquivConj (x : ∀ n, G n) (y : r.Twisted) :
    (r.twistedEquivConj x y).val = y.val * x⁻¹ :=
  (rfl)

@[simp]
lemma val_twistedEquivConj_symm (x : ∀ n, G n) (y : (r.conj x).Twisted) :
    ((r.twistedEquivConj x).symm y).val = y.val * x :=
  (rfl)

lemma twistedEquivConj_smul (x g : ∀ n, G n) (y : r.Twisted) :
    r.twistedEquivConj x (g • y) = g • r.twistedEquivConj x y := by
  ext n
  simp [mul_assoc]

/-- The stabilizer of a family `x` under the twisted action of `r` is the limit of the tower
conjugated by `x`. -/
theorem stabilizer_eq_lim_conj (x : ∀ n, G n) :
    MulAction.stabilizer (∀ n, G n) (⟨x⟩ : r.Twisted) = (r.conj x).lim := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, Twisted.ext_iff, val_smul, funext_iff, mem_lim,
    conj_apply]
  refine forall_congr' fun n ↦ ?_
  rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, eq_comm]

/-- The limit of a tower is the stabilizer of the identity family under the twisted action. -/
theorem stabilizer_one : MulAction.stabilizer (∀ n, G n) (⟨1⟩ : r.Twisted) = r.lim := by
  rw [stabilizer_eq_lim_conj, conj_one]

/-- Changing the reference family: right translation by `x⁻¹` identifies `lim¹` of `r` with
`lim¹` of the conjugated tower `r.conj x`, carrying the class of `x` to the base point. -/
def limOneEquivConj (x : ∀ n, G n) : r.limOne ≃ (r.conj x).limOne :=
  Quotient.congr (r.twistedEquivConj x) fun y z ↦ by
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, ← twistedEquivConj_smul]
    exact exists_congr fun g ↦ (r.twistedEquivConj x).apply_eq_iff_eq.symm

@[simp]
lemma limOneEquivConj_mk (x : ∀ n, G n) (y : r.Twisted) :
    r.limOneEquivConj x (Quotient.mk'' y) = Quotient.mk'' (r.twistedEquivConj x y) :=
  (rfl)

-- Higher priority than `limOneEquivConj_mk`, so that the class of `x` normalizes to the base
-- point instead of to the class of the translated family.
@[simp high]
lemma limOneEquivConj_mk_self (x : ∀ n, G n) :
    r.limOneEquivConj x (Quotient.mk'' ⟨x⟩) = 1 := by
  rw [limOneEquivConj_mk, one_def]
  congr 1
  ext n
  simp

/-! ### Functoriality -/

variable {H : ℕ → Type v} [∀ n, Group (H n)] {K : ℕ → Type w} [∀ n, Group (K n)]

/-- A morphism of towers of groups: homomorphisms `Gₙ →* Hₙ` commuting with the transition
maps. -/
@[ext]
structure Hom (r : GroupTower G) (s : GroupTower H) where
  /-- The homomorphism between the `n`-th groups of the towers. -/
  app (n : ℕ) : G n →* H n
  /-- The homomorphisms commute with the transition maps. -/
  comm (n : ℕ) (g : G (n + 1)) : s n (app (n + 1) g) = app n (r n g)

attribute [simp] Hom.comm

/-- The identity morphism of a tower. -/
def Hom.id : Hom r r where
  app n := MonoidHom.id (G n)
  comm _ _ := rfl

@[simp]
lemma Hom.id_app (n : ℕ) : (Hom.id r).app n = MonoidHom.id (G n) :=
  (rfl)

variable {r} {s : GroupTower H} {t : GroupTower K}

/-- The composite of two morphisms of towers. -/
def Hom.comp (f : Hom r s) (f' : Hom s t) : Hom r t where
  app n := (f'.app n).comp (f.app n)
  comm n g := by simp

@[simp]
lemma Hom.comp_app (f : Hom r s) (f' : Hom s t) (n : ℕ) :
    (f.comp f').app n = (f'.app n).comp (f.app n) :=
  (rfl)

/-- The homomorphism `lim G →* lim H` induced by a morphism of towers. -/
def Hom.limMap (f : Hom r s) : r.lim →* s.lim :=
  ((MonoidHom.piMap f.app).comp r.lim.subtype).codRestrict s.lim fun g n ↦ by
    simp [r.mem_lim.1 g.2 n]

@[simp]
lemma Hom.coe_limMap_apply (f : Hom r s) (g : r.lim) (n : ℕ) :
    (f.limMap g : ∀ n, H n) n = f.app n ((g : ∀ n, G n) n) :=
  (rfl)

@[simp]
lemma Hom.limMap_id : (Hom.id r).limMap = MonoidHom.id r.lim :=
  (rfl)

lemma Hom.limMap_comp (f : Hom r s) (f' : Hom s t) :
    (f.comp f').limMap = f'.limMap.comp f.limMap :=
  (rfl)

/-- The map `∏ₙ Gₙ → ∏ₙ Hₙ` of twisted products given levelwise by a morphism of towers. -/
def Hom.twistedMap (f : Hom r s) (x : r.Twisted) : s.Twisted :=
  ⟨fun n ↦ f.app n (x.val n)⟩

@[simp]
lemma Hom.val_twistedMap (f : Hom r s) (x : r.Twisted) (n : ℕ) :
    (f.twistedMap x).val n = f.app n (x.val n) :=
  (rfl)

/-- A morphism of towers is equivariant for the twisted actions. -/
lemma Hom.twistedMap_smul (f : Hom r s) (g : ∀ n, G n) (x : r.Twisted) :
    f.twistedMap (g • x) = MonoidHom.piMap f.app g • f.twistedMap x := by
  ext n
  simp

/-- The map of pointed sets `lim¹ G → lim¹ H` induced by a morphism of towers. -/
def Hom.limOneMap (f : Hom r s) : r.limOne → s.limOne :=
  Quotient.map' f.twistedMap fun x y h ↦ by
    obtain ⟨g, rfl⟩ := MulAction.orbitRel_apply.1 h
    exact MulAction.orbitRel_apply.2 ⟨MonoidHom.piMap f.app g, (f.twistedMap_smul g y).symm⟩

@[simp]
lemma Hom.limOneMap_mk (f : Hom r s) (x : r.Twisted) :
    f.limOneMap (Quotient.mk'' x) = Quotient.mk'' (f.twistedMap x) :=
  (rfl)

@[simp]
lemma Hom.limOneMap_one (f : Hom r s) : f.limOneMap 1 = 1 := by
  rw [one_def, one_def, limOneMap_mk]
  congr 1
  ext n
  simp

@[simp]
lemma Hom.limOneMap_id : (Hom.id r).limOneMap = _root_.id := by
  ext x
  induction x using Quotient.inductionOn'
  rfl

lemma Hom.limOneMap_comp (f : Hom r s) (f' : Hom s t) :
    (f.comp f').limOneMap = f'.limOneMap ∘ f.limOneMap := by
  ext x
  induction x using Quotient.inductionOn'
  rfl

end GroupTower

end TauCeti
