/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# `lim` and `lim¹` of towers of modules

A *tower* of modules over a ring `R` is a functor `ℕᵒᵖ ⥤ ModuleCat R`, that is, a sequence of
modules `A₀ ← A₁ ← A₂ ← ⋯` with transition maps `φₙ : Aₙ₊₁ → Aₙ`. On the product `∏ₙ Aₙ` the
*shift* `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)` is `R`-linear; its kernel `lim A` is the module of compatible
families and its cokernel is `lim¹ A`. This file shows that `lim A`, with its projections, is a
limit of the tower in `ModuleCat R`, that `lim¹ A` vanishes if and only if the shift is surjective,
and hence that `lim¹ A` vanishes when every transition map is surjective. By Stacks, Tag 07KW,
`lim` and `lim¹` are the derived functors `R⁰lim` and `R¹lim` on `ℕ`-indexed towers, whose higher
derived limits vanish; that identification is not formalized here.
The shift presentation is the input to the six-term sequence of a short exact sequence of towers,
to Milnor sequences for towers of complexes, and to derived limits of towers of modules.

The ring `R` is only assumed associative and unital, so towers of left modules over a
noncommutative ring are allowed.

## Main declarations

* `TauCeti.ModuleTower`: towers of `R`-modules, the functor category `ℕᵒᵖ ⥤ ModuleCat R`.
* `TauCeti.ModuleTower.transitionOfLE`: the composite transition maps `Aₖ → Aₙ`, `n ≤ k`.
* `TauCeti.ModuleTower.shift`: the shift map `δ` on the product of the terms.
* `TauCeti.ModuleTower.lim`, `TauCeti.ModuleTower.limOne`: its kernel and cokernel.
* `TauCeti.ModuleTower.mem_lim`: `lim` consists of the families compatible with the transitions.
* `TauCeti.ModuleTower.isLimitLimCone`: `lim`, with its projections, is a limit of the tower.
* `TauCeti.ModuleTower.limπ_surjective`: if the transitions are surjective, so are the
  projections `lim A → Aₙ`.
* `TauCeti.ModuleTower.limMap`, `TauCeti.ModuleTower.limOneMap`: the linear maps induced by a
  morphism of towers, with their identity, composition, zero and addition laws.
* `TauCeti.ModuleTower.limMap_injective`, `TauCeti.ModuleTower.limOneMap_surjective`: levelwise
  injective (surjective) morphisms induce injective (surjective) maps on `lim` (`lim¹`).
* `TauCeti.ModuleTower.subsingleton_limOne_iff`: `lim¹` vanishes if and only if the shift map is
  surjective.
* `TauCeti.ModuleTower.mem_range_shift_of_le_map`: a family of submodules `Bₙ ⊆ φₙ(Bₙ₊₁)` has
  `∏ₙ Bₙ` inside the image of the shift map.
* `TauCeti.ModuleTower.subsingleton_limOne_of_surjective`: towers with surjective transitions
  have vanishing `lim¹`.

## References

* [Stacks: More on Algebra, Lemma 15.88.1, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
* C. A. Weibel, *An introduction to homological algebra*, §3.5.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Opposite

universe v u

/-- A tower of `R`-modules: a functor `ℕᵒᵖ ⥤ ModuleCat R`, given by modules `Aₙ` and transition
maps `Aₙ₊₁ → Aₙ`. Morphisms of towers are natural transformations. -/
abbrev ModuleTower (R : Type u) [Ring R] := ℕᵒᵖ ⥤ ModuleCat.{v} R

namespace ModuleTower

variable {R : Type u} [Ring R]

section Basic

variable (F : ModuleTower.{v} R)

/-- The product `∏ₙ Aₙ` of the terms of a tower. -/
abbrev Product := ∀ n : ℕ, F.obj (op n)

/-- The transition map `Aₙ₊₁ → Aₙ` of a tower. -/
def transition (n : ℕ) : F.obj (op (n + 1)) →ₗ[R] F.obj (op n) :=
  (F.map (homOfLE (Nat.le_succ n)).op).hom

theorem transition_def (n : ℕ) : F.transition n = (F.map (homOfLE (Nat.le_succ n)).op).hom :=
  (rfl)

/-- The composite transition map `Aₖ → Aₙ` of a tower, for `n ≤ k`. -/
def transitionOfLE {n k : ℕ} (h : n ≤ k) : F.obj (op k) →ₗ[R] F.obj (op n) :=
  (F.map (homOfLE h).op).hom

theorem transitionOfLE_def {n k : ℕ} (h : n ≤ k) :
    F.transitionOfLE h = (F.map (homOfLE h).op).hom :=
  (rfl)

/-- Every map `F.map f : Aₖ → Aₙ` of a tower is the composite transition `transitionOfLE`. -/
@[simp]
theorem map_hom_eq_transitionOfLE {n k : ℕ} (f : op k ⟶ op n) :
    (F.map f).hom = F.transitionOfLE (leOfHom f.unop) := by
  rw [transitionOfLE_def, Subsingleton.elim (homOfLE _).op f]

@[simp]
theorem transitionOfLE_succ (n : ℕ) : F.transitionOfLE (Nat.le_succ n) = F.transition n :=
  (rfl)

@[simp]
theorem transitionOfLE_refl (n : ℕ) : F.transitionOfLE (le_refl n) = LinearMap.id := by
  simp [transitionOfLE_def]

@[simp]
theorem transitionOfLE_comp_transitionOfLE {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    F.transitionOfLE hmn ∘ₗ F.transitionOfLE hnk = F.transitionOfLE (hmn.trans hnk) := by
  simp only [transitionOfLE_def, ← ModuleCat.hom_comp, ← F.map_comp, ← op_comp, homOfLE_comp]

@[simp]
theorem transitionOfLE_transitionOfLE {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : F.obj (op k)) :
    F.transitionOfLE hmn (F.transitionOfLE hnk x) = F.transitionOfLE (hmn.trans hnk) x :=
  LinearMap.congr_fun (F.transitionOfLE_comp_transitionOfLE hmn hnk) x

@[simp]
theorem transition_transitionOfLE {n k : ℕ} (h : n + 1 ≤ k) (x : F.obj (op k)) :
    F.transition n (F.transitionOfLE h x) = F.transitionOfLE ((Nat.le_succ n).trans h) x :=
  F.transitionOfLE_transitionOfLE (Nat.le_succ n) h x

@[simp]
theorem transitionOfLE_transition {n k : ℕ} (h : n ≤ k) (x : F.obj (op (k + 1))) :
    F.transitionOfLE h (F.transition k x) = F.transitionOfLE (h.trans (Nat.le_succ k)) x :=
  F.transitionOfLE_transitionOfLE h (Nat.le_succ k) x

/-- The images of the composite transitions into a fixed term `Aₙ` decrease as the source
index grows. -/
theorem range_transitionOfLE_le {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    LinearMap.range (F.transitionOfLE (hmn.trans hnk)) ≤
      LinearMap.range (F.transitionOfLE hmn) := by
  rw [← F.transitionOfLE_comp_transitionOfLE hmn hnk]
  exact LinearMap.range_comp_le_range _ _

/-- If every transition map of a tower is surjective, then so is every composite transition. -/
theorem transitionOfLE_surjective (h : ∀ n, Function.Surjective (F.transition n)) {n k : ℕ}
    (hnk : n ≤ k) : Function.Surjective (F.transitionOfLE hnk) := by
  induction k, hnk using Nat.le_induction with
  | base => simpa using Function.surjective_id
  | succ k hnk ih =>
    rw [← F.transitionOfLE_comp_transitionOfLE hnk (Nat.le_succ k), transitionOfLE_succ,
      LinearMap.coe_comp]
    exact ih.comp (h k)

/-- The shift map `δ : ∏ₙ Aₙ → ∏ₙ Aₙ`, `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)`. -/
def shift : F.Product →ₗ[R] F.Product :=
  LinearMap.id - LinearMap.pi fun n ↦ F.transition n ∘ₗ LinearMap.proj (n + 1)

@[simp]
theorem shift_apply (x : F.Product) (n : ℕ) :
    F.shift x n = x n - F.transition n (x (n + 1)) :=
  (rfl)

/-- The limit `lim A` of a tower, the kernel of the shift map: the families `(xₙ)` with
`φₙ(xₙ₊₁) = xₙ` for every `n`. -/
def lim : Submodule R F.Product :=
  LinearMap.ker F.shift

/-- The first derived limit `lim¹ A` of a tower, the cokernel of the shift map. -/
abbrev limOne : Type _ :=
  F.Product ⧸ LinearMap.range F.shift

theorem lim_eq_ker : F.lim = LinearMap.ker F.shift :=
  (rfl)

/-- `x ∈ lim A` if and only if `φₙ(xₙ₊₁) = xₙ` for every `n`: `lim A` is exactly the module of
compatible families. -/
@[simp]
theorem mem_lim {x : F.Product} : x ∈ F.lim ↔ ∀ n, F.transition n (x (n + 1)) = x n := by
  rw [lim_eq_ker, LinearMap.mem_ker, funext_iff]
  simp only [shift_apply, Pi.zero_apply, sub_eq_zero]
  exact forall_congr' fun n ↦ eq_comm

/-- The projection `lim A → Aₙ`. -/
def limπ (n : ℕ) : F.lim →ₗ[R] F.obj (op n) :=
  LinearMap.proj n ∘ₗ F.lim.subtype

@[simp]
theorem limπ_apply (n : ℕ) (x : F.lim) : F.limπ n x = (x : F.Product) n :=
  (rfl)

/-- An element of `lim A` is compatible with the transition `Aₙ₊₁ → Aₙ`. -/
@[simp]
theorem transition_coe_lim_succ (x : F.lim) (n : ℕ) :
    F.transition n ((x : F.Product) (n + 1)) = (x : F.Product) n :=
  F.mem_lim.1 x.2 n

@[simp]
theorem transition_comp_limπ (n : ℕ) : F.transition n ∘ₗ F.limπ (n + 1) = F.limπ n := by
  ext x
  exact F.mem_lim.1 x.2 n

@[ext]
theorem lim_hom_ext {P : Type*} [AddCommGroup P] [Module R P] {f g : P →ₗ[R] F.lim}
    (h : ∀ n, F.limπ n ∘ₗ f = F.limπ n ∘ₗ g) : f = g := by
  ext p : 1
  exact Subtype.ext <| funext fun n ↦ LinearMap.congr_fun (h n) p

/-- The universal property of `lim A`: a family of linear maps `P → Aₙ` compatible with the
transitions factors through `lim A`. -/
def limLift {P : Type*} [AddCommGroup P] [Module R P] (f : ∀ n, P →ₗ[R] F.obj (op n))
    (hf : ∀ n, F.transition n ∘ₗ f (n + 1) = f n) : P →ₗ[R] F.lim :=
  LinearMap.codRestrict F.lim (LinearMap.pi f) fun p ↦
    F.mem_lim.2 fun n ↦ LinearMap.congr_fun (hf n) p

@[simp]
theorem coe_limLift_apply {P : Type*} [AddCommGroup P] [Module R P]
    (f : ∀ n, P →ₗ[R] F.obj (op n)) (hf : ∀ n, F.transition n ∘ₗ f (n + 1) = f n) (p : P)
    (n : ℕ) : (F.limLift f hf p : F.Product) n = f n p :=
  (rfl)

@[simp]
theorem limπ_comp_limLift {P : Type*} [AddCommGroup P] [Module R P]
    (f : ∀ n, P →ₗ[R] F.obj (op n)) (hf : ∀ n, F.transition n ∘ₗ f (n + 1) = f n) (n : ℕ) :
    F.limπ n ∘ₗ F.limLift f hf = f n :=
  (rfl)

/-- The cone over a tower with vertex `lim A` and the projections `lim A → Aₙ`. -/
@[expose]
def limCone : Limits.Cone F where
  pt := ModuleCat.of R F.lim
  π := NatTrans.ofOpSequence (fun n ↦ ModuleCat.ofHom (F.limπ n)) fun n ↦ by
    ext x
    exact (F.mem_lim.1 x.2 n).symm

@[simp]
theorem limCone_pt : F.limCone.pt = ModuleCat.of R F.lim :=
  (rfl)

@[simp]
theorem limCone_π_app (n : ℕ) : (F.limCone.π.app (op n)).hom = F.limπ n :=
  (rfl)

/-- An element of `lim A` is compatible with every composite transition `Aₙ → Aₘ`, `m ≤ n`. -/
theorem map_apply_of_mem_lim {x : F.Product} (hx : x ∈ F.lim) {m n : ℕ} (f : op n ⟶ op m) :
    (F.map f).hom (x n) = x m :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (F.limCone.π.naturality f)) ⟨x, hx⟩).symm

/-- An element of `lim A` is compatible with the composite transition `Aₖ → Aₙ`, `n ≤ k`. -/
theorem transitionOfLE_apply_of_mem_lim {x : F.Product} (hx : x ∈ F.lim) {n k : ℕ}
    (h : n ≤ k) : F.transitionOfLE h (x k) = x n :=
  F.map_apply_of_mem_lim hx (homOfLE h).op

/-- An element of `lim A` is compatible with the composite transition `Aₖ → Aₙ`, `n ≤ k`. -/
@[simp]
theorem transitionOfLE_coe_lim (x : F.lim) {n k : ℕ} (h : n ≤ k) :
    F.transitionOfLE h ((x : F.Product) k) = (x : F.Product) n :=
  F.transitionOfLE_apply_of_mem_lim x.2 h

@[simp]
theorem transitionOfLE_comp_limπ {n k : ℕ} (h : n ≤ k) :
    F.transitionOfLE h ∘ₗ F.limπ k = F.limπ n := by
  ext x
  exact F.transitionOfLE_coe_lim x h

/-- `lim A`, with its projections, is a limit of the tower `A` in `ModuleCat R`. -/
def isLimitLimCone : Limits.IsLimit F.limCone where
  lift s := ModuleCat.ofHom <| F.limLift (fun n ↦ (s.π.app (op n)).hom) fun n ↦ by
    rw [transition_def, ← ModuleCat.hom_comp, s.w]
  fac s n := by
    ext x
    rfl
  uniq s g hg := by
    ext x : 2
    exact Subtype.ext <| funext fun n ↦
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hg (op n))) x

/-- `lim¹ A` vanishes if and only if the shift map is surjective. -/
theorem subsingleton_limOne_iff : Subsingleton F.limOne ↔ Function.Surjective F.shift := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]

/-- If submodules `Bₙ ⊆ Aₙ` satisfy `Bₙ ⊆ φₙ(Bₙ₊₁)`, then every family `(cₙ)` with `cₙ ∈ Bₙ`
lies in the image of the shift map. -/
theorem mem_range_shift_of_le_map (B : ∀ n, Submodule R (F.obj (op n)))
    (hB : ∀ n, B n ≤ (B (n + 1)).map (F.transition n)) {c : F.Product} (hc : ∀ n, c n ∈ B n) :
    c ∈ LinearMap.range F.shift := by
  -- The equations `xₙ - φₙ(xₙ₊₁) = cₙ` are solved inside the `Bₙ` by choosing `x₀ = 0` and
  -- `xₙ₊₁ ∈ Bₙ₊₁` a preimage of `xₙ - cₙ ∈ Bₙ`.
  have hlift (n : ℕ) (y : B n) : ∃ z : B (n + 1), F.transition n z = y := by
    obtain ⟨z, hz, h⟩ := hB n y.2
    exact ⟨⟨z, hz⟩, h⟩
  choose s hs using hlift
  let x : ∀ n, B n := fun n ↦
    Nat.rec (motive := fun n ↦ B n) 0 (fun n xn ↦ s n (xn - ⟨c n, hc n⟩)) n
  -- The recursion step defining `x` computes definitionally.
  have hx (n : ℕ) : x (n + 1) = s n (x n - ⟨c n, hc n⟩) := rfl
  refine ⟨fun n ↦ (x n).1, funext fun n ↦ ?_⟩
  rw [shift_apply, hx, hs, Submodule.coe_sub, sub_sub_cancel]

/-- If every transition map of a tower is surjective, then so is its shift map. -/
theorem shift_surjective (h : ∀ n, Function.Surjective (F.transition n)) :
    Function.Surjective F.shift := fun b ↦
  F.mem_range_shift_of_le_map (fun _ ↦ ⊤)
    (fun n ↦ by rw [Submodule.map_top, LinearMap.range_eq_top.2 (h n)]) (fun _ ↦ trivial)

/-- **Towers with surjective transitions have vanishing `lim¹`** (Stacks, Tag 07KW). -/
theorem subsingleton_limOne_of_surjective (h : ∀ n, Function.Surjective (F.transition n)) :
    Subsingleton F.limOne :=
  F.subsingleton_limOne_iff.2 (F.shift_surjective h)

/-- If every transition map of a tower is surjective, then so is every projection
`lim A → Aₙ`: an element of `Aₙ` lifts step by step to a compatible family. -/
theorem limπ_surjective (h : ∀ n, Function.Surjective (F.transition n)) (n : ℕ) :
    Function.Surjective (F.limπ n) := by
  intro y
  -- Lifts `g j ∈ A_{n + j}` of `y`, each chosen as a preimage of the previous one.
  let g : ∀ j, F.obj (op (n + j)) := fun j ↦
    Nat.rec (motive := fun j ↦ F.obj (op (n + j))) y (fun j x ↦ (h (n + j) x).choose) j
  have hg (j : ℕ) : F.transition (n + j) (g (j + 1)) = g j := (h (n + j) (g j)).choose_spec
  have hgy (j : ℕ) : F.transitionOfLE (Nat.le_add_right n j) (g j) = y := by
    induction j with
    | zero => exact LinearMap.congr_fun (F.transitionOfLE_refl n) y
    | succ j ih => rwa [← hg j, transitionOfLE_transition] at ih
  refine ⟨⟨fun k ↦ F.transitionOfLE (Nat.le_add_left k n) (g k), F.mem_lim.2 fun k ↦ ?_⟩, hgy n⟩
  rw [transition_transitionOfLE, ← hg k, transitionOfLE_transition]

end Basic

section Functoriality

variable {F G H : ModuleTower.{v} R}

/-- The linear map `∏ₙ Aₙ → ∏ₙ Bₙ` induced levelwise by a morphism of towers. -/
def productMap (f : F ⟶ G) : F.Product →ₗ[R] G.Product :=
  LinearMap.piMap fun n ↦ (f.app (op n)).hom

@[simp]
theorem productMap_apply (f : F ⟶ G) (x : F.Product) (n : ℕ) :
    productMap f x n = (f.app (op n)).hom (x n) :=
  (rfl)

@[simp]
theorem productMap_id : productMap (𝟙 F) = LinearMap.id :=
  (rfl)

@[simp]
theorem productMap_comp (f : F ⟶ G) (g : G ⟶ H) :
    productMap (f ≫ g) = productMap g ∘ₗ productMap f :=
  (rfl)

/-- The composition law `productMap_comp`, applied to a family. -/
theorem productMap_comp_apply (f : F ⟶ G) (g : G ⟶ H) (x : F.Product) :
    productMap (f ≫ g) x = productMap g (productMap f x) :=
  (rfl)

@[simp]
theorem productMap_zero : productMap (0 : F ⟶ G) = 0 :=
  (rfl)

@[simp]
theorem productMap_add (f g : F ⟶ G) : productMap (f + g) = productMap f + productMap g :=
  (rfl)

/-- The product map of a morphism of towers is the componentwise map `Pi.map`. -/
theorem coe_productMap (f : F ⟶ G) : ⇑(productMap f) = Pi.map fun n ↦ (f.app (op n)).hom :=
  funext fun x ↦ funext fun n ↦ productMap_apply f x n

/-- A levelwise injective morphism of towers is injective on products. -/
theorem productMap_injective {f : F ⟶ G} (hf : ∀ n, Function.Injective (f.app (op n)).hom) :
    Function.Injective (productMap f) := by
  rw [coe_productMap]
  exact Function.Injective.piMap hf

/-- A levelwise surjective morphism of towers is surjective on products. -/
theorem productMap_surjective {g : G ⟶ H} (hg : ∀ n, Function.Surjective (g.app (op n)).hom) :
    Function.Surjective (productMap g) := by
  rw [coe_productMap]
  exact Function.Surjective.piMap hg

/-- A morphism of towers commutes with the transition maps. -/
theorem app_comp_transition (f : F ⟶ G) (n : ℕ) :
    (f.app (op n)).hom ∘ₗ F.transition n = G.transition n ∘ₗ (f.app (op (n + 1))).hom := by
  rw [transition_def, transition_def, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, f.naturality]

/-- A morphism of towers commutes with the composite transition maps. -/
theorem app_comp_transitionOfLE (f : F ⟶ G) {n k : ℕ} (h : n ≤ k) :
    (f.app (op n)).hom ∘ₗ F.transitionOfLE h = G.transitionOfLE h ∘ₗ (f.app (op k)).hom := by
  rw [transitionOfLE_def, transitionOfLE_def, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
    f.naturality]

/-- The product map of a morphism of towers commutes with the shift maps. -/
theorem shift_natural (f : F ⟶ G) : G.shift ∘ₗ productMap f = productMap f ∘ₗ F.shift := by
  ext x n : 2
  simp only [LinearMap.comp_apply, shift_apply, productMap_apply, map_sub]
  rw [← LinearMap.comp_apply (f.app (op n)).hom, app_comp_transition, LinearMap.comp_apply]

/-- The naturality square `shift_natural`, applied to a family. -/
theorem shift_natural_apply (f : F ⟶ G) (x : F.Product) :
    G.shift (productMap f x) = productMap f (F.shift x) :=
  LinearMap.congr_fun (shift_natural f) x

/-- The linear map `lim A → lim B` induced by a morphism of towers. -/
def limMap (f : F ⟶ G) : F.lim →ₗ[R] G.lim :=
  (productMap f).restrict fun x hx ↦ by
    rw [lim_eq_ker, LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, shift_natural, LinearMap.comp_apply, hx, map_zero]

@[simp]
theorem coe_limMap_apply (f : F ⟶ G) (x : F.lim) :
    (limMap f x : G.Product) = productMap f x :=
  (rfl)

@[simp]
theorem limπ_comp_limMap (f : F ⟶ G) (n : ℕ) :
    G.limπ n ∘ₗ limMap f = (f.app (op n)).hom ∘ₗ F.limπ n :=
  (rfl)

@[simp]
theorem limMap_id : limMap (𝟙 F) = LinearMap.id :=
  (rfl)

@[simp]
theorem limMap_comp (f : F ⟶ G) (g : G ⟶ H) : limMap (f ≫ g) = limMap g ∘ₗ limMap f :=
  (rfl)

@[simp]
theorem limMap_zero : limMap (0 : F ⟶ G) = 0 :=
  (rfl)

@[simp]
theorem limMap_add (f g : F ⟶ G) : limMap (f + g) = limMap f + limMap g :=
  (rfl)

/-- The first map of the six-term sequence: `lim A → lim B` is injective when every `Aₙ → Bₙ`
is. -/
theorem limMap_injective {f : F ⟶ G} (hf : ∀ n, Function.Injective (f.app (op n)).hom) :
    Function.Injective (limMap f) := fun x y hxy ↦
  Subtype.ext <| productMap_injective hf <| by
    rw [← coe_limMap_apply, ← coe_limMap_apply, hxy]

/-- A morphism of towers maps the image of the shift map into the image of the shift map. -/
theorem range_shift_le_comap (f : F ⟶ G) :
    LinearMap.range F.shift ≤ (LinearMap.range G.shift).comap (productMap f) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨productMap f x, by rw [← LinearMap.comp_apply, shift_natural, LinearMap.comp_apply]⟩

/-- The linear map `lim¹ A → lim¹ B` induced by a morphism of towers. -/
def limOneMap (f : F ⟶ G) : F.limOne →ₗ[R] G.limOne :=
  (LinearMap.range F.shift).mapQ (LinearMap.range G.shift) (productMap f) (range_shift_le_comap f)

@[simp]
theorem limOneMap_mk (f : F ⟶ G) (x : F.Product) :
    limOneMap f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (productMap f x) :=
  (rfl)

@[simp]
theorem limOneMap_id : limOneMap (𝟙 F) = LinearMap.id := by
  ext x
  rfl

@[simp]
theorem limOneMap_comp (f : F ⟶ G) (g : G ⟶ H) :
    limOneMap (f ≫ g) = limOneMap g ∘ₗ limOneMap f := by
  ext x
  rfl

@[simp]
theorem limOneMap_zero : limOneMap (0 : F ⟶ G) = 0 := by
  ext x
  rfl

@[simp]
theorem limOneMap_add (f g : F ⟶ G) : limOneMap (f + g) = limOneMap f + limOneMap g := by
  ext x
  rfl

/-- The last map of the six-term sequence: `lim¹ B → lim¹ C` is surjective when every
`Bₙ → Cₙ` is. -/
theorem limOneMap_surjective {g : G ⟶ H} (hg : ∀ n, Function.Surjective (g.app (op n)).hom) :
    Function.Surjective (limOneMap g) := by
  intro z
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨y, rfl⟩ := productMap_surjective hg z
  exact ⟨Submodule.Quotient.mk y, limOneMap_mk g y⟩

end Functoriality

end ModuleTower

end TauCeti
