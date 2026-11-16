/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.Algebra.Homology.DerivedCategory.Linear
public import TauCeti.Algebra.Homology.DerivedCategory.TStructure
public import TauCeti.CategoryTheory.Linear.Conj
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Preadditive.Endomorphism
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.ZMod.Basic
import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Homology.DerivedCategory.SingleTriangle
import TauCeti.CategoryTheory.Preadditive.NSMul

/-!
# Cohomology actions, ghost ideals, ghost nilpotence, and derived endomorphism images

This file develops the comparison between endomorphism algebras in the derived category and their
actions on cohomology, together with ghost nilpotence, annihilator bounds, and chain/homotopy/
derived endomorphism comparisons, following Allen–Calegari–Caraiani–Gee–Helm–Le Hung–Newton–
Scholze–Taylor–Thorne (ACC, §2.2.3 and Lemma 2.2.4):

* **Cohomology action and ghost ideal**:
  * `DerivedCategory.cohomologyActionRingHom` and `DerivedCategory.cohomologyAction`: for an
    object `X : DerivedCategory C`, the ring homomorphism (and, in a linear setting, `R`-algebra
    homomorphism) `End X → ∀ i : ℤ, End ((homologyFunctor C i).obj X)` sending `f` to `(H^i(f))_i`.
  * `DerivedCategory.IsGhost`: predicate asserting that an endomorphism `f : End X` induces zero on
    every `H^i(X)`.
  * `DerivedCategory.ghostIdeal`: the two-sided ideal of ghosts in `End X`, defined via
    `TwoSidedIdeal.ker (cohomologyActionRingHom X)` independently of any coefficient ring `R`.
* **Ghost nilpotence and annihilator bounds**:
  * `DerivedCategory.exists_comp_truncLEι_mul` and
    `DerivedCategory.exists_comp_truncLEι_list_prod_of_isLE`: an ordered product of endomorphisms
    acting by zero on the top `l.length` degrees below `b` factors through `τ_{≤ b - l.length} X`.
  * `DerivedCategory.list_prod_eq_zero_of_isGE_of_isLE` and
    `DerivedCategory.list_ofFn_prod_eq_zero_of_isGE_of_isLE`: if `X` is concentrated in `[a, b]`,
    every ordered product of more than `b - a` ghosts in `End X` vanishes (in particular, any
    ordered product of `(b - a).toNat + 1` ghosts vanishes).
  * `DerivedCategory.actionGhostKer`, `DerivedCategory.exists_comp_truncLEι_of_mem_pow_of_isLE`,
    and `DerivedCategory.pow_le_ker_of_le_actionGhostKer`: for any ring homomorphism
    `α : H →+* End X` and ideal `I ≤ actionGhostKer α`, `I ^ n ≤ RingHom.ker α` whenever
    `b < a + n`.
  * `DerivedCategory.imageGhostIdeal`, `DerivedCategory.imageGhostIdeal_pow_eq_bot`,
    `DerivedCategory.ghostIdeal_asIdeal_pow_eq_bot`, and
    `DerivedCategory.cohomologyImageQuotientEquiv`: the kernel of cohomology on `α.range` is
    nilpotent of exponent at most `(b - a).toNat + 1`, and its quotient is isomorphic as an
    `R`-algebra to `((cohomologyAction R X).comp α).range`.
* **Chain, homotopy, and derived comparisons**:
  * `DerivedCategory.conjAlgEquiv_comp_Qh_mapEndAlgHom_comp_quotient`: descending chain
    endomorphisms via `HomotopyCategory.quotient` and `DerivedCategory.Qh` agrees with
    `DerivedCategory.Q` up to conjugation by `quotientCompQhIso`.
  * `DerivedCategory.Qh_mapEndAlgHom_bijective_of_isKProjective`,
    `DerivedCategory.homotopyToDerivedEndEquivOfIsKProjective`,
    `DerivedCategory.homotopyToDerivedEndEquivQOfIsKProjective`, and
    `DerivedCategory.Q_mapEndAlgHom_surjective_of_isKProjective`: for a K-projective complex `K`,
    `Qh` and `Q` induce `R`-algebra equivalences between homotopy and derived endomorphism algebras.
-/

public section

open CategoryTheory Limits Pretriangulated Triangulated

universe t' t w v u

namespace DerivedCategory

section CohomologyAction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The ring homomorphism `End X →+* ∀ i : ℤ, End ((homologyFunctor C i).obj X)` sending a derived
endomorphism `f` to its induced family of cohomology endomorphisms `(H^i(f))_i`. -/
noncomputable def cohomologyActionRingHom (X : DerivedCategory C) :
    End X →+* ∀ i : ℤ, End ((homologyFunctor C i).obj X) :=
  RingHom.pi fun i ↦ (homologyFunctor C i).mapEndRingHom X

/-- Applying `cohomologyActionRingHom` at degree `i` gives `(homologyFunctor C i).map f.asHom`. -/
@[simp]
theorem cohomologyActionRingHom_apply_asHom (X : DerivedCategory C) (f : End X) (i : ℤ) :
    (cohomologyActionRingHom X f i).asHom = (homologyFunctor C i).map f.asHom := by
  simp [cohomologyActionRingHom]

/-- An endomorphism `f : End X` in `DerivedCategory C` is a ghost if it induces zero on every
cohomology object `H^i(X)`. -/
def IsGhost {X : DerivedCategory C} (f : End X) : Prop :=
  ∀ i : ℤ, (homologyFunctor C i).map f.asHom = 0

/-- Characterization of `IsGhost`. -/
theorem isGhost_iff {X : DerivedCategory C} {f : End X} :
    IsGhost f ↔ ∀ i : ℤ, (homologyFunctor C i).map f.asHom = 0 :=
  Iff.rfl

/-- An endomorphism is a ghost if and only if it lies in the kernel of
`cohomologyActionRingHom`. -/
theorem isGhost_iff_cohomologyActionRingHom_eq_zero {X : DerivedCategory C} {f : End X} :
    IsGhost f ↔ cohomologyActionRingHom X f = 0 := by
  constructor
  · intro hf
    ext i
    simpa [cohomologyActionRingHom_apply_asHom] using hf i
  · intro hf i
    simpa [cohomologyActionRingHom_apply_asHom] using congrArg (fun g ↦ (g i).asHom) hf

/-- The two-sided ideal of ghost endomorphisms of `X : DerivedCategory C`. -/
noncomputable def ghostIdeal (X : DerivedCategory C) : TwoSidedIdeal (End X) :=
  TwoSidedIdeal.ker (cohomologyActionRingHom X)

/-- An endomorphism belongs to `ghostIdeal X` if and only if it is a ghost. -/
@[simp]
theorem mem_ghostIdeal_iff {X : DerivedCategory C} {f : End X} :
    f ∈ ghostIdeal X ↔ IsGhost f := by
  rw [ghostIdeal, TwoSidedIdeal.mem_ker, isGhost_iff_cohomologyActionRingHom_eq_zero]

/-- The zero endomorphism is a ghost. -/
@[simp]
theorem isGhost_zero (X : DerivedCategory C) : IsGhost (0 : End X) := by
  rw [← mem_ghostIdeal_iff]
  exact (ghostIdeal X).zero_mem

section Linear

variable (R : Type t) [CommSemiring R] [Linear R C] [Linear R (DerivedCategory C)]
  [∀ i : ℤ, (homologyFunctor C i).Linear R]

/-- The `R`-algebra homomorphism `End X →ₐ[R] ∀ i : ℤ, End ((homologyFunctor C i).obj X)` sending
a derived endomorphism `f` to its induced family of cohomology endomorphisms `(H^i(f))_i`. -/
noncomputable def cohomologyAction (X : DerivedCategory C) :
    End X →ₐ[R] ∀ i : ℤ, End ((homologyFunctor C i).obj X) :=
  AlgHom.pi fun i ↦ (homologyFunctor C i).mapEndAlgHom R X

/-- Applying `cohomologyAction` at degree `i` gives `(homologyFunctor C i).map f.asHom`. -/
@[simp]
theorem cohomologyAction_apply_asHom (X : DerivedCategory C) (f : End X) (i : ℤ) :
    (cohomologyAction R X f i).asHom = (homologyFunctor C i).map f.asHom := by
  simp [cohomologyAction]

/-- The underlying ring homomorphism of `cohomologyAction R X` is `cohomologyActionRingHom X`. -/
@[simp]
theorem cohomologyAction_toRingHom (X : DerivedCategory C) :
    (cohomologyAction R X : End X →+* ∀ i : ℤ, End ((homologyFunctor C i).obj X)) =
      cohomologyActionRingHom X := by
  ext f i
  simp

/-- An endomorphism is a ghost if and only if it lies in the kernel of `cohomologyAction`. -/
theorem isGhost_iff_cohomologyAction_eq_zero {X : DerivedCategory C} {f : End X} :
    IsGhost f ↔ cohomologyAction R X f = 0 := by
  rw [isGhost_iff_cohomologyActionRingHom_eq_zero, ← cohomologyAction_toRingHom R X]
  rfl

/-- The two-sided kernel of `cohomologyAction R X` is `ghostIdeal X`, independently of `R`. -/
theorem twoSidedIdeal_ker_cohomologyAction (X : DerivedCategory C) :
    TwoSidedIdeal.ker (cohomologyAction R X).toRingHom = ghostIdeal X := by
  rw [AlgHom.toRingHom_eq_coe, cohomologyAction_toRingHom, ghostIdeal]

/-- Membership in `RingHom.ker (cohomologyAction R X)` is equivalent to `IsGhost`. -/
theorem mem_ringHom_ker_cohomologyAction_iff {X : DerivedCategory C} {f : End X} :
    f ∈ RingHom.ker (cohomologyAction R X) ↔ IsGhost f := by
  rw [RingHom.mem_ker, isGhost_iff_cohomologyAction_eq_zero R]

end Linear

end CohomologyAction

section GhostNilpotence

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If `e : End X` factors through `τ_{≤ b} X ⟶ X` and `f : End X` induces zero on `H^b(X)`,
then `f * e` factors through `τ_{≤ b - 1} X ⟶ X`. -/
theorem exists_comp_truncLEι_mul {X : DerivedCategory C} (b : ℤ) {f e : End X}
    (hf : (homologyFunctor C b).map f.asHom = 0)
    (he : ∃ g : X ⟶ (TStructure.t.truncLE b).obj X,
      g ≫ (TStructure.t.truncLEι b).app X = e.asHom) :
    ∃ g : X ⟶ (TStructure.t.truncLE (b - 1)).obj X,
      g ≫ (TStructure.t.truncLEι (b - 1)).app X = (f * e).asHom := by
  obtain ⟨g, hg⟩ := he
  have hcomp : (homologyFunctor C b).map ((TStructure.t.truncLEι b).app X ≫ f.asHom) = 0 := by
    rw [Functor.map_comp, hf, comp_zero]
  obtain ⟨u, hu⟩ := exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero
    ((TStructure.t.truncLEι b).app X ≫ f.asHom) b hcomp
  refine ⟨g ≫ u, ?_⟩
  rw [Category.assoc, hu, ← Category.assoc, hg, End.mul_asHom]

/-- If `X` is concentrated in degrees `≤ b` and every `f ∈ l` induces zero on `H^i(X)` for
`b - l.length < i ≤ b`, then the ordered product `l.prod` factors through
`τ_{≤ b - l.length} X ⟶ X`. -/
theorem exists_comp_truncLEι_list_prod_of_isLE {X : DerivedCategory C} (b : ℤ) [X.IsLE b]
    (l : List (End X))
    (hl : ∀ f ∈ l, ∀ i : ℤ, b - l.length < i → i ≤ b → (homologyFunctor C i).map f.asHom = 0) :
    ∃ g : X ⟶ (TStructure.t.truncLE (b - l.length)).obj X,
      g ≫ (TStructure.t.truncLEι (b - l.length)).app X = l.prod.asHom := by
  induction l with
  | nil =>
    rw [List.length_nil, Nat.cast_zero, sub_zero, List.prod_nil, End.one_asHom]
    exact ⟨TStructure.t.liftTruncLE (𝟙 X) b, TStructure.t.liftTruncLE_ι (𝟙 X) b⟩
  | cons f l ih =>
    have hl' : ∀ f' ∈ l, ∀ i : ℤ, b - l.length < i → i ≤ b →
        (homologyFunctor C i).map f'.asHom = 0 :=
      fun f' hf' i hi₁ hi₂ ↦ hl f' (List.mem_cons_of_mem f hf') i (by simp; omega) hi₂
    have hf : (homologyFunctor C (b - l.length)).map f.asHom = 0 :=
      hl f List.mem_cons_self (b - l.length) (by simp) (by omega)
    have hdeg : b - ↑(f :: l).length = b - ↑l.length - 1 := by simp; omega
    rw [hdeg, List.prod_cons]
    exact exists_comp_truncLEι_mul (b - l.length) hf (ih hl')

/-- Ghost nilpotence for arbitrary ordered lists: if `X` is concentrated in `[a, b]` and every
`f ∈ l` acts by zero on `H^i(X)` for `a ≤ i ≤ b`, then `l.prod = 0` whenever `b < a + l.length`. -/
theorem list_prod_eq_zero_of_isGE_of_isLE {X : DerivedCategory C} (a b : ℤ) [X.IsGE a] [X.IsLE b]
    (l : List (End X))
    (hl : ∀ f ∈ l, ∀ i : ℤ, a ≤ i → i ≤ b → (homologyFunctor C i).map f.asHom = 0)
    (hlen : b < a + l.length) :
    l.prod = 0 := by
  have hl' : ∀ f ∈ l, ∀ i : ℤ, b - l.length < i → i ≤ b →
      (homologyFunctor C i).map f.asHom = 0 := by
    intro f hf i _ hib
    by_cases hia : a ≤ i
    · exact hl f hf i hia hib
    · exact (isZero_of_isGE X a i (by omega)).eq_of_src _ _
  obtain ⟨g, hg⟩ := exists_comp_truncLEι_list_prod_of_isLE b l hl'
  have hz : IsZero ((TStructure.t.truncLE (b - l.length)).obj X) :=
    TStructure.t.isZero ((TStructure.t.truncLE (b - l.length)).obj X) (b - l.length) a (by omega)
  apply End.ext
  rw [← hg, hz.eq_of_tgt g 0, zero_comp, End.zero_asHom]

/-- Ghost nilpotence (ACC, Lemma 2.2.4): if `X` is concentrated in `[a, b]`, then every ordered
product of `(b - a).toNat + 1` ghost endomorphisms of `X` vanishes. -/
theorem list_ofFn_prod_eq_zero_of_isGE_of_isLE {X : DerivedCategory C} (a b : ℤ)
    [X.IsGE a] [X.IsLE b] (fs : Fin ((b - a).toNat + 1) → End X) (hfs : ∀ j, IsGhost (fs j)) :
    (List.ofFn fs).prod = 0 := by
  refine list_prod_eq_zero_of_isGE_of_isLE a b (List.ofFn fs) (fun f hf i _ _ ↦ ?_) (by simp; omega)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  exact hfs j i

/-- The action ghost kernel of a ring homomorphism `α : H →+* End X`, consisting of all `h : H`
whose image `α h` acts by zero on every cohomology object `H^i(X)`. -/
noncomputable def actionGhostKer {H : Type t} [Semiring H] {X : DerivedCategory C}
    (α : H →+* End X) : Ideal H :=
  RingHom.ker ((cohomologyActionRingHom X).comp α)

/-- An element belongs to `actionGhostKer α` if and only if its image under `α` is a ghost. -/
@[simp]
theorem mem_actionGhostKer_iff {H : Type t} [Semiring H] {X : DerivedCategory C} {α : H →+* End X}
    {h : H} :
    h ∈ actionGhostKer α ↔ IsGhost (α h) := by
  rw [actionGhostKer, RingHom.mem_ker, RingHom.comp_apply,
    isGhost_iff_cohomologyActionRingHom_eq_zero]

/-- The action ghost kernel of `α` is a two-sided ideal of `H`. -/
instance actionGhostKer_isTwoSided {H : Type t} [Semiring H] {X : DerivedCategory C}
    (α : H →+* End X) :
    (actionGhostKer α).IsTwoSided := by
  unfold actionGhostKer
  infer_instance

/-- The kernel of `α` is contained in the action ghost kernel of `α`. -/
theorem ker_le_actionGhostKer {H : Type t} [Semiring H] {X : DerivedCategory C}
    (α : H →+* End X) :
    RingHom.ker α ≤ actionGhostKer α := by
  intro h hh
  rw [mem_actionGhostKer_iff, RingHom.mem_ker.mp hh]
  exact isGhost_zero X

/-- If `X` is concentrated in degrees `≤ b` and `I ≤ actionGhostKer α`, then every `x ∈ I ^ n`
acts via a morphism factoring through `τ_{≤ b - n} X ⟶ X`. -/
theorem exists_comp_truncLEι_of_mem_pow_of_isLE {H : Type t} [Semiring H] {X : DerivedCategory C}
    (α : H →+* End X) (I : Ideal H) (b : ℤ) [X.IsLE b] (hI : I ≤ actionGhostKer α) :
    ∀ (n : ℕ) {x : H}, x ∈ I ^ n →
      ∃ g : X ⟶ (TStructure.t.truncLE (b - n)).obj X,
        g ≫ (TStructure.t.truncLEι (b - n)).app X = (α x).asHom := by
  intro n
  induction n with
  | zero =>
    intro x _
    rw [Nat.cast_zero, sub_zero]
    exact ⟨TStructure.t.liftTruncLE (α x).asHom b, TStructure.t.liftTruncLE_ι (α x).asHom b⟩
  | succ n ih =>
    intro x hx
    have hdeg : b - ((n + 1 : ℕ) : ℤ) = (b - (n : ℤ)) - 1 := by omega
    rw [hdeg]
    cases n with
    | zero =>
      rw [Submodule.pow_one] at hx
      rw [Nat.cast_zero, sub_zero]
      have hghost : IsGhost (α x) := mem_actionGhostKer_iff.mp (hI hx)
      exact exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero (α x).asHom b (hghost b)
    | succ n =>
      rw [Submodule.pow_succ' _ (Nat.succ_ne_zero n)] at hx
      refine Submodule.mul_induction_on hx (fun r hr a ha ↦ ?_) (fun y z hy hz ↦ ?_)
      · have hr' : (homologyFunctor C (b - ((n + 1 : ℕ) : ℤ))).map (α r).asHom = 0 :=
          mem_actionGhostKer_iff.mp (hI hr) _
        rw [map_mul]
        exact exists_comp_truncLEι_mul (b - ((n + 1 : ℕ) : ℤ)) hr' (ih ha)
      · obtain ⟨g₁, hg₁⟩ := hy
        obtain ⟨g₂, hg₂⟩ := hz
        refine ⟨g₁ + g₂, ?_⟩
        rw [Preadditive.add_comp, hg₁, hg₂, map_add, End.add_asHom]

/-- Action-annihilator bound (ACC, Lemma 2.2.4): if `X` is concentrated in `[a, b]` and
`I ≤ actionGhostKer α`, then `I ^ n ≤ RingHom.ker α` whenever `b < a + n`. -/
theorem pow_le_ker_of_le_actionGhostKer {H : Type t} [Semiring H] {X : DerivedCategory C}
    (α : H →+* End X) (I : Ideal H) (a b : ℤ) [X.IsGE a] [X.IsLE b] (n : ℕ)
    (hI : I ≤ actionGhostKer α) (hn : b < a + n) :
    I ^ n ≤ RingHom.ker α := by
  intro x hx
  obtain ⟨g, hg⟩ := exists_comp_truncLEι_of_mem_pow_of_isLE α I b hI n hx
  have hz : IsZero ((TStructure.t.truncLE (b - n)).obj X) :=
    TStructure.t.isZero ((TStructure.t.truncLE (b - n)).obj X) (b - n) a (by omega)
  rw [RingHom.mem_ker]
  apply End.ext
  rw [← hg, hz.eq_of_tgt g 0, zero_comp, End.zero_asHom]

/-- If `X` is concentrated in `[a, b]` and `b < a + n`, then `(ghostIdeal X).asIdeal ^ n = ⊥`. -/
theorem ghostIdeal_asIdeal_pow_eq_bot {X : DerivedCategory C} (a b : ℤ) [X.IsGE a] [X.IsLE b]
    (n : ℕ) (hn : b < a + n) :
    (ghostIdeal X).asIdeal ^ n = ⊥ := by
  refine le_bot_iff.mp <|
    (pow_le_ker_of_le_actionGhostKer (RingHom.id (End X)) (ghostIdeal X).asIdeal a b n ?_ hn).trans
      (fun x hx ↦ hx)
  intro x hx
  rw [mem_actionGhostKer_iff, RingHom.id_apply, ← mem_ghostIdeal_iff]
  exact TwoSidedIdeal.mem_asIdeal.mp hx

end GhostNilpotence

section ImageGhost

variable (R : Type t) [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [Linear R C] [Linear R (DerivedCategory C)]
  [∀ i : ℤ, (homologyFunctor C i).Linear R]

/-- The image ghost ideal of an `R`-algebra action `α : H →ₐ[R] End X`, defined as the kernel of
the cohomology action restricted to `α.range`. -/
noncomputable def imageGhostIdeal {H : Type t'} [Semiring H] [Algebra R H] {X : DerivedCategory C}
    (α : H →ₐ[R] End X) : Ideal α.range :=
  RingHom.ker ((cohomologyAction R X).comp α.range.val)

/-- An element of `α.range` belongs to `imageGhostIdeal R α` if and only if it is a ghost. -/
@[simp]
theorem mem_imageGhostIdeal_iff {H : Type t'} [Semiring H] [Algebra R H] {X : DerivedCategory C}
    {α : H →ₐ[R] End X} {x : α.range} :
    x ∈ imageGhostIdeal R α ↔ IsGhost x.1 := by
  rw [imageGhostIdeal, RingHom.mem_ker, AlgHom.comp_apply, Subalgebra.coe_val,
    isGhost_iff_cohomologyAction_eq_zero R]

/-- The image ghost ideal of `α` is a two-sided ideal of `α.range`. -/
instance imageGhostIdeal_isTwoSided {H : Type t'} [Semiring H] [Algebra R H] {X : DerivedCategory C}
    (α : H →ₐ[R] End X) :
    (imageGhostIdeal R α).IsTwoSided := by
  unfold imageGhostIdeal
  infer_instance

/-- If `X` is concentrated in `[a, b]` and `b < a + n`, then `(imageGhostIdeal R α) ^ n = ⊥`. -/
theorem imageGhostIdeal_pow_eq_bot {H : Type t'} [Semiring H] [Algebra R H] {X : DerivedCategory C}
    (α : H →ₐ[R] End X) (a b : ℤ) [X.IsGE a] [X.IsLE b] (n : ℕ) (hn : b < a + n) :
    (imageGhostIdeal R α) ^ n = ⊥ := by
  refine le_bot_iff.mp <|
    (pow_le_ker_of_le_actionGhostKer α.range.val.toRingHom (imageGhostIdeal R α) a b n ?_ hn).trans
      (fun x hx ↦ Subtype.ext hx)
  intro x hx
  rw [mem_actionGhostKer_iff]
  exact (mem_imageGhostIdeal_iff R).mp hx

end ImageGhost

section CohomologyImageQuotient

variable (R : Type t) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [Linear R C] [Linear R (DerivedCategory C)]
  [∀ i : ℤ, (homologyFunctor C i).Linear R]

/-- The cohomology image quotient equivalence: the quotient of the derived image `α.range` by its
image ghost ideal is isomorphic as an `R`-algebra to the cohomology image
`((cohomologyAction R X).comp α).range`. -/
noncomputable def cohomologyImageQuotientEquiv {H : Type t'} [Semiring H] [Algebra R H]
    {X : DerivedCategory C} (α : H →ₐ[R] End X) :
    (α.range ⧸ imageGhostIdeal R α) ≃ₐ[R] ((cohomologyAction R X).comp α).range :=
  (Ideal.quotientKerEquivRange ((cohomologyAction R X).comp α.range.val)).trans <|
    Subalgebra.equivOfEq _ _ (by rw [Subalgebra.range_comp_val, ← AlgHom.range_comp])

/-- Applying `cohomologyImageQuotientEquiv` to the class of `x : α.range` gives
`cohomologyAction R X x.1`. -/
@[simp]
theorem cohomologyImageQuotientEquiv_mk_val {H : Type t'} [Semiring H] [Algebra R H]
    {X : DerivedCategory C} (α : H →ₐ[R] End X) (x : α.range) :
    (cohomologyImageQuotientEquiv R α (Ideal.Quotient.mk (imageGhostIdeal R α) x)).1 =
      cohomologyAction R X x.1 :=
  (rfl)

end CohomologyImageQuotient

section ChainHomotopyDerived

variable (R : Type t) [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C] [Linear R (DerivedCategory C)]

/-- Descending a chain-level endomorphism through `HomotopyCategory.quotient` and then
`DerivedCategory.Qh` agrees with descending directly through `DerivedCategory.Q`, up to conjugation
by `quotientCompQhIso`. -/
theorem conjAlgEquiv_comp_Qh_mapEndAlgHom_comp_quotient [(Qh (C := C)).Linear R]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) :
    (((quotientCompQhIso C).app K).conjAlgEquiv R).toAlgHom.comp
      ((Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)).comp
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K)) =
      Q.mapEndAlgHom R K := by
  ext f
  simp [Iso.conjAlgEquiv_apply, quotientCompQhIso_hom_naturality]

/-- For a K-projective cochain complex `K`, the functor `Qh` induces a bijective `R`-algebra
homomorphism on endomorphisms. -/
theorem Qh_mapEndAlgHom_bijective_of_isKProjective [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    Function.Bijective
      (Qh.mapEndAlgHom R ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :=
  Qh.mapEndAlgHom_bijective R _
    (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))

/-- For a K-projective cochain complex `K`, `Qh` induces an `R`-algebra equivalence between
homotopy endomorphisms and derived endomorphisms of `Qh.obj (quotient.obj K)`. -/
noncomputable def homotopyToDerivedEndEquivOfIsKProjective [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≃ₐ[R]
      End (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :=
  AlgEquiv.ofBijective _ (Qh_mapEndAlgHom_bijective_of_isKProjective R K)

/-- Applying `homotopyToDerivedEndEquivOfIsKProjective` acts by `Qh.map`. -/
@[simp]
theorem homotopyToDerivedEndEquivOfIsKProjective_asHom [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective]
    (f : End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) :
    (homotopyToDerivedEndEquivOfIsKProjective R K f).asHom = Qh.map f.asHom := by
  simp [homotopyToDerivedEndEquivOfIsKProjective]

/-- For a K-projective cochain complex `K`, homotopy endomorphisms of `K` are isomorphic as an
`R`-algebra to derived endomorphisms of `Q.obj K`. -/
noncomputable def homotopyToDerivedEndEquivQOfIsKProjective [(Qh (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≃ₐ[R] End (Q.obj K) :=
  (homotopyToDerivedEndEquivOfIsKProjective R K).trans
    (((quotientCompQhIso C).app K).conjAlgEquiv R)

/-- Applying `homotopyToDerivedEndEquivQOfIsKProjective` to the homotopy class of a chain
endomorphism `f : End K` gives `Q.mapEndAlgHom R K f`. -/
@[simp]
theorem homotopyToDerivedEndEquivQOfIsKProjective_quotient [(Qh (C := C)).Linear R]
    [(Q (C := C)).Linear R] (K : CochainComplex C ℤ) [K.IsKProjective] (f : End K) :
    homotopyToDerivedEndEquivQOfIsKProjective R K
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapEndAlgHom R K f) =
      Q.mapEndAlgHom R K f := by
  apply End.ext
  simp [homotopyToDerivedEndEquivQOfIsKProjective, Iso.conjAlgEquiv_apply,
    quotientCompQhIso_hom_naturality]

/-- For a K-projective cochain complex `K`, `Q` induces a surjective `R`-algebra homomorphism
from chain endomorphisms to derived endomorphisms. -/
theorem Q_mapEndAlgHom_surjective_of_isKProjective [(Q (C := C)).Linear R]
    (K : CochainComplex C ℤ) [K.IsKProjective] :
    Function.Surjective (Q.mapEndAlgHom R K) := by
  intro g
  obtain ⟨f, hf⟩ := CochainComplex.IsKProjective.Q_map_surjective K K g.asHom
  exact ⟨End.of f, End.ext (by simpa using hf)⟩

end ChainHomotopyDerived

section Examples

open ZeroObject

attribute [local instance] HasDerivedCategory.standard

private example {A : Type u} [CommRing A] {C : Type v} [Category.{w} C] [Abelian C] [Linear A C]
    [HasDerivedCategory.{t} C] {H : Type t'} [Semiring H] [Algebra A H]
    (X : DerivedCategory C) (α : H →ₐ[A] End X) (K : CochainComplex C ℤ) [K.IsKProjective] :
    Nonempty ((α.range ⧸ imageGhostIdeal A α) ≃ₐ[A] ((cohomologyAction A X).comp α).range) ∧
    Nonempty (End ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≃ₐ[A] End (Q.obj K)) :=
  ⟨⟨cohomologyImageQuotientEquiv A α⟩, ⟨homotopyToDerivedEndEquivQOfIsKProjective A K⟩⟩

private example :
    let X : DerivedCategory (ModuleCat.{0} ℤ) := 0
    let α : ℤ →ₐ[ℤ] End X := Algebra.ofId ℤ (End X)
    cohomologyAction ℤ X (algebraMap ℤ (End X) 7) = 0 ∧
    ghostIdeal X = ⊥ ∧
    actionGhostKer α.toRingHom = ⊤ ∧
    imageGhostIdeal ℤ α = ⊤ ∧
    cohomologyImageQuotientEquiv ℤ α (Ideal.Quotient.mk _ (α.rangeRestrict 7)) = 0 := by
  intro X α
  have hX : IsZero X := isZero_zero _
  have hEnd : Subsingleton (End X) :=
    ⟨fun f g ↦ End.ext ((hX.eq_of_src f.asHom 0).trans (hX.eq_of_src g.asHom 0).symm)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    apply End.ext
    exact ((homologyFunctor (ModuleCat.{0} ℤ) i).map_isZero hX).eq_of_src _ _
  · ext f
    simp [Subsingleton.elim f 0]
  · ext r
    simp only [mem_actionGhostKer_iff, Submodule.mem_top, iff_true]
    rw [Subsingleton.elim (α.toRingHom r) 0]
    exact isGhost_zero X
  · ext x
    simp [Subsingleton.elim x.1 0]
  · apply Subtype.ext
    funext i
    apply End.ext
    exact ((homologyFunctor (ModuleCat.{0} ℤ) i).map_isZero hX).eq_of_src _ _

private example :
    let X := (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)
    let α : ℤ →ₐ[ℤ] End X := Algebra.ofId ℤ (End X)
    let e : (homologyFunctor (ModuleCat.{0} ℤ) 0).obj X ≅ ModuleCat.of ℤ ℤ :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (ModuleCat.of ℤ ℤ)
    e.hom ((cohomologyAction ℤ X (algebraMap ℤ (End X) 2) 0).asHom (e.inv 3)) = (6 : ℤ) ∧
    ghostIdeal X = ⊥ ∧
    actionGhostKer α.toRingHom = ⊥ ∧
    imageGhostIdeal ℤ α = ⊥ ∧
    e.hom (((cohomologyImageQuotientEquiv ℤ α
      (Ideal.Quotient.mk _ (α.rangeRestrict 2))).1 0).asHom (e.inv 3)) = (6 : ℤ) := by
  intro X α e
  have hscalar : ∀ n : ℤ,
      e.hom ((cohomologyAction ℤ X (algebraMap ℤ (End X) n) 0).asHom (e.inv 3)) = n * 3 := by
    intro n
    have h1 : (cohomologyAction ℤ X (algebraMap ℤ (End X) n) 0).asHom =
        n • 𝟙 ((homologyFunctor (ModuleCat.{0} ℤ) 0).obj X) := by
      rw [cohomologyAction_apply_asHom, End.algebraMap_asHom, Functor.map_zsmul,
        CategoryTheory.Functor.map_id]
    rw [h1]
    simp [Iso.inv_hom_id_apply]
  have hghost0 : ∀ f : End X, IsGhost f → f = 0 := fun f hf ↦
    End.ext <| (homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE f.asHom 0).mp (hf 0)
  have halg_inj : Function.Injective (algebraMap ℤ (End X)) := by
    intro a b hab
    have h := congrArg (fun g ↦ e.hom ((cohomologyAction ℤ X g 0).asHom (e.inv 3))) hab
    have h' : a * 3 = b * 3 := by simpa only [hscalar] using h
    omega
  refine ⟨(hscalar 2).trans (by decide), ?_, ?_, ?_, ?_⟩
  · ext f
    simp only [mem_ghostIdeal_iff, TwoSidedIdeal.mem_bot]
    exact ⟨hghost0 f, fun h ↦ by simp [h]⟩
  · ext n
    simp only [mem_actionGhostKer_iff, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Ideal.mem_bot]
    exact ⟨fun h ↦ halg_inj (by simpa [α] using hghost0 _ h), fun h ↦ by simp [h]⟩
  · ext x
    simp only [mem_imageGhostIdeal_iff, Ideal.mem_bot]
    exact ⟨fun h ↦ Subtype.ext (hghost0 x.1 h), fun h ↦ by simp [h]⟩
  · rw [cohomologyImageQuotientEquiv_mk_val]
    exact (hscalar 2).trans (by decide)

private example :
    let X := (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ)
    let α : Polynomial ℤ →ₐ[ℤ] End X :=
      (Algebra.ofId ℤ (End X)).comp (Polynomial.aeval (0 : ℤ))
    actionGhostKer α.toRingHom = Ideal.span {Polynomial.X} ∧ imageGhostIdeal ℤ α = ⊥ := by
  intro X α
  have hghost0 : ∀ f : End X, IsGhost f → f = 0 := fun f hf ↦
    End.ext <| (homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE f.asHom 0).mp (hf 0)
  have hscalar : ∀ n : ℤ, algebraMap ℤ (End X) n = 0 → n = 0 := by
    intro n hn
    let e : (homologyFunctor (ModuleCat.{0} ℤ) 0).obj X ≅ ModuleCat.of ℤ ℤ :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app (ModuleCat.of ℤ ℤ)
    have h1 : (cohomologyAction ℤ X (algebraMap ℤ (End X) n) 0).asHom = 0 := by simp [hn]
    rw [cohomologyAction_apply_asHom, End.algebraMap_asHom, Functor.map_zsmul,
      CategoryTheory.Functor.map_id] at h1
    have h3 : e.hom ((n • 𝟙 ((homologyFunctor (ModuleCat.{0} ℤ) 0).obj X)).hom (e.inv 1)) = 0 := by
      simp [h1]
    simpa [Iso.inv_hom_id_apply] using h3
  have hαp : ∀ p : Polynomial ℤ, α p = algebraMap ℤ (End X) (p.coeff 0) := by
    intro p
    simp [α, Polynomial.coeff_zero_eq_eval_zero]
  constructor
  · ext p
    rw [mem_actionGhostKer_iff, Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    constructor
    · intro hp
      exact hscalar (p.coeff 0) (by rw [← hαp p]; exact hghost0 _ hp)
    · intro hp
      have h0 : α.toRingHom p = 0 := by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hαp p, hp,
        map_zero]
      rw [h0]
      exact isGhost_zero X
  · ext x
    simp only [mem_imageGhostIdeal_iff, Ideal.mem_bot]
    exact ⟨fun h ↦ Subtype.ext (hghost0 x.1 h), fun h ↦ by simp [h]⟩

private noncomputable def contractibleTwoTerm : CochainComplex (ModuleCat.{0} ℤ) ℤ where
  X i := if i = 0 ∨ i = 1 then ModuleCat.of ℤ ℤ else 0
  d i j := if h : i = 0 ∧ j = 1 then
    eqToHom (by simp [h.1]) ≫ 𝟙 (ModuleCat.of ℤ ℤ) ≫ eqToHom (by simp [h.2]) else 0
  shape i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    exact dite_eq_right_iff.mpr fun h ↦ absurd (by omega) hij
  d_comp_d' i j k _ _ := by
    by_cases h₁ : i = 0 ∧ j = 1
    · by_cases h₂ : j = 0 ∧ k = 1
      · omega
      · simp [h₂]
    · simp [h₁]

private noncomputable def contractibleTwoTermHomotopy :
    Homotopy (𝟙 contractibleTwoTerm) 0 where
  hom i j := if h : i = 1 ∧ j = 0 then
    eqToHom (by simp [contractibleTwoTerm, h.1]) ≫ 𝟙 (ModuleCat.of ℤ ℤ) ≫
      eqToHom (by simp [contractibleTwoTerm, h.2]) else 0
  zero i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    exact dite_eq_right_iff.mpr fun h ↦ absurd (by omega) hij
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    by_cases hi0 : i = 0
    · subst hi0
      have hd : contractibleTwoTerm.d (0 - 1) 0 = 0 :=
        (show IsZero (contractibleTwoTerm.X (0 - 1)) by
          simp [contractibleTwoTerm, isZero_zero]).eq_of_src _ _
      rw [hd, comp_zero, add_zero, HomologicalComplex.zero_f_apply, add_zero,
        HomologicalComplex.id_f]
      simp [contractibleTwoTerm]
    · by_cases hi1 : i = 1
      · subst hi1
        have hd : contractibleTwoTerm.d 1 (1 + 1) = 0 :=
          (show IsZero (contractibleTwoTerm.X (1 + 1)) by
            simp [contractibleTwoTerm, isZero_zero]).eq_of_tgt _ _
        rw [hd, zero_comp, zero_add, HomologicalComplex.zero_f_apply, add_zero,
          HomologicalComplex.id_f]
        simp only [Int.reduceSub, sub_self, and_self, ↓reduceDIte, Category.id_comp, eqToHom_trans]
        exact (eqToHom_refl (ModuleCat.of ℤ ℤ) rfl).symm
      · have hX0 : IsZero (contractibleTwoTerm.X i) := by
          simp [contractibleTwoTerm, show ¬ (i = 0 ∨ i = 1) by omega, isZero_zero]
        exact hX0.eq_of_src _ _

private example :
    (𝟙 contractibleTwoTerm ≠ 0) ∧
    (HomotopyCategory.quotient (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)).map
      (𝟙 contractibleTwoTerm) = 0 ∧
    Q.map (𝟙 contractibleTwoTerm) = 0 := by
  have hne : 𝟙 contractibleTwoTerm ≠ 0 := by
    intro h
    let e : ModuleCat.of ℤ ℤ ⟶ contractibleTwoTerm.X 0 := eqToHom (by simp [contractibleTwoTerm])
    let e' : contractibleTwoTerm.X 0 ⟶ ModuleCat.of ℤ ℤ := eqToHom (by simp [contractibleTwoTerm])
    have h0 := congrArg (fun f : contractibleTwoTerm ⟶ contractibleTwoTerm ↦ e' ((f.f 0) (e 1))) h
    have h1 : (1 : ℤ) = 0 := by
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply] at h0
      simp [e, e'] at h0
    exact one_ne_zero h1
  have hK : (HomotopyCategory.quotient (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)).map
      (𝟙 contractibleTwoTerm) = 0 := by
    rw [← Functor.map_zero (HomotopyCategory.quotient _ _)]
    exact HomotopyCategory.eq_of_homotopy _ _ contractibleTwoTermHomotopy
  have hD : Q.map (𝟙 contractibleTwoTerm) = 0 := by
    rw [← cancel_epi ((quotientCompQhIso (ModuleCat.{0} ℤ)).hom.app contractibleTwoTerm),
      ← quotientCompQhIso_hom_naturality, hK]
    simp
  exact ⟨hne, hK, hD⟩

private example :
    let V := ModuleCat.of ℤ (ℤ × ℤ)
    let X := (singleFunctor (ModuleCat.{0} ℤ) 0).obj V
    let e : (homologyFunctor (ModuleCat.{0} ℤ) 0).obj X ≅ V :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app V
    let f₀₁ : V ⟶ V := ModuleCat.ofHom
      { toFun := fun p ↦ (p.2, 0), map_add' := fun _ _ ↦ by simp, map_smul' := fun _ _ ↦ by simp }
    let f₁₀ : V ⟶ V := ModuleCat.ofHom
      { toFun := fun p ↦ (0, p.1), map_add' := fun _ _ ↦ by simp, map_smul' := fun _ _ ↦ by simp }
    let E₀₁ : End X := End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map f₀₁)
    let E₁₀ : End X := End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map f₁₀)
    e.hom ((cohomologyAction ℤ X (E₀₁ * E₁₀) 0).asHom (e.inv (2, 3))) = (2, 0) ∧
    e.hom ((cohomologyAction ℤ X (E₁₀ * E₀₁) 0).asHom (e.inv (2, 3))) = (0, 3) := by
  intro V X e f₀₁ f₁₀ E₀₁ E₁₀
  have hnat : ∀ f : V ⟶ V,
      e.hom ((cohomologyAction ℤ X (End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map f)) 0).asHom
        (e.inv (2, 3))) = f (2, 3) := by
    intro f
    have h : (homologyFunctor (ModuleCat.{0} ℤ) 0).map ((singleFunctor (ModuleCat.{0} ℤ) 0).map f) ≫
        e.hom = e.hom ≫ f :=
      (singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).hom.naturality f
    have h' : e.inv ≫ (homologyFunctor (ModuleCat.{0} ℤ) 0).map
        ((singleFunctor (ModuleCat.{0} ℤ) 0).map f) ≫ e.hom = f := by
      rw [h, Iso.inv_hom_id_assoc]
    have hval := congrArg (fun g : V ⟶ V ↦ g (2, 3)) h'
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hval
    simpa [cohomologyAction_apply_asHom] using hval
  constructor
  · have hmul : E₀₁ * E₁₀ = End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map (f₁₀ ≫ f₀₁)) := by
      simp [E₀₁, E₁₀]
    rw [hmul, hnat]
    rfl
  · have hmul : E₁₀ * E₀₁ = End.of ((singleFunctor (ModuleCat.{0} ℤ) 0).map (f₀₁ ≫ f₁₀)) := by
      simp [E₀₁, E₁₀]
    rw [hmul, hnat]
    rfl

private abbrev zmod2MulTwo : ZMod 2 →+ ZMod 4 where
  toFun x := (2 * x.val : ZMod 4)
  map_zero' := by decide
  map_add' a b := by fin_cases a <;> fin_cases b <;> decide

private abbrev zmod2ShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk
    (ModuleCat.ofHom zmod2MulTwo.toIntLinearMap)
    (ModuleCat.ofHom (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toIntLinearMap)
    (by
      ext x
      fin_cases x <;> decide)

private theorem zmod2ShortComplex_shortExact : zmod2ShortComplex.ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x : ZMod 4) hx
    fin_cases x
    · exact ⟨(0 : ZMod 2), rfl⟩
    · exact absurd hx (by decide)
    · exact ⟨(1 : ZMod 2), rfl⟩
    · exact absurd hx (by decide)
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    intro (a : ZMod 2) (b : ZMod 2) h
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    intro (y : ZMod 2)
    fin_cases y
    · exact ⟨(0 : ZMod 4), rfl⟩
    · exact ⟨(1 : ZMod 4), rfl⟩

private theorem zmod2ShortComplex_not_isSplitEpi : ¬ IsSplitEpi zmod2ShortComplex.g := by
  rintro ⟨⟨s, hs⟩⟩
  have h1 : zmod2ShortComplex.g (s (1 : ZMod 2)) = (1 : ZMod 2) := by
    have h := congrArg (fun f : ModuleCat.of ℤ (ZMod 2) ⟶ ModuleCat.of ℤ (ZMod 2) ↦ f 1) hs
    simpa [ModuleCat.comp_apply] using h
  have h2 : (2 : ℤ) • (s (1 : ZMod 2) : ZMod 4) = 0 := by
    have hsmul : s.hom ((2 : ℤ) • (1 : ZMod 2)) = (2 : ℤ) • s.hom (1 : ZMod 2) :=
      map_zsmul s.hom (2 : ℤ) (1 : ZMod 2)
    rw [← hsmul, show (2 : ℤ) • (1 : ZMod 2) = 0 by decide, map_zero]
  generalize hx : (s (1 : ZMod 2) : ZMod 4) = x at h1 h2
  fin_cases x
  · exact (by decide : (0 : ZMod 2) ≠ 1) h1
  · exact (by decide : (2 : ℤ) • (1 : ZMod 4) ≠ 0) h2
  · exact (by decide : (0 : ZMod 2) ≠ 1) h1
  · exact (by decide : (2 : ℤ) • (3 : ZMod 4) ≠ 0) h2

private noncomputable def zmod2Ext1Map :
    (singleFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ZMod 2)) ⟶
      (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)) :=
  ((singleFunctors (ModuleCat.{0} ℤ)).shiftIso (-1) 1 0 (by omega)).inv.app _ ≫
    zmod2ShortComplex_shortExact.singleδ⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{0} ℤ)) (1 : ℤ) (-1 : ℤ) (by omega)).hom.app
      ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)))

private theorem zmod2Ext1Map_ne_zero : zmod2Ext1Map ≠ 0 := by
  intro h0
  have hδ₀ : zmod2ShortComplex_shortExact.singleδ ≠ 0 := by
    rw [ne_eq, ShortComplex.ShortExact.singleδ_eq_zero_iff]
    exact zmod2ShortComplex_not_isSplitEpi
  apply hδ₀
  apply (shiftFunctor (DerivedCategory (ModuleCat.{0} ℤ)) (-1 : ℤ)).map_injective
  rw [Functor.map_zero]
  have h1 : zmod2ShortComplex_shortExact.singleδ⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{0} ℤ)) (1 : ℤ) (-1 : ℤ)
        (by omega)).hom.app ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) =
      0 := by
    rw [← cancel_epi (((singleFunctors (ModuleCat.{0} ℤ)).shiftIso (-1) 1 0 (by omega)).inv.app _)]
    simpa [zmod2Ext1Map, Category.assoc] using h0
  exact (cancel_mono ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{0} ℤ)) (1 : ℤ) (-1 : ℤ)
    (by omega)).hom.app _)).mp (by rw [zero_comp]; exact h1)

private theorem polynomial_decomp_deg_two (p : Polynomial ℤ) :
    ∃ q : Polynomial ℤ,
      p = Polynomial.C (p.coeff 0) + Polynomial.C (p.coeff 1) * Polynomial.X +
        Polynomial.X ^ 2 * q := by
  refine ⟨p.divX.divX, ?_⟩
  have h1 : Polynomial.X * p.divX + Polynomial.C (p.coeff 0) = p := Polynomial.X_mul_divX_add p
  have h2 : Polynomial.X * p.divX.divX + Polynomial.C (p.divX.coeff 0) = p.divX :=
    Polynomial.X_mul_divX_add p.divX
  have hc : p.divX.coeff 0 = p.coeff 1 := by simp [Polynomial.coeff_divX]
  rw [hc] at h2
  calc
    p = Polynomial.X * p.divX + Polynomial.C (p.coeff 0) := h1.symm
    _ = Polynomial.X * (Polynomial.X * p.divX.divX + Polynomial.C (p.coeff 1)) +
          Polynomial.C (p.coeff 0) :=
      congrArg (fun u ↦ Polynomial.X * u + Polynomial.C (p.coeff 0)) h2.symm
    _ = Polynomial.C (p.coeff 0) + Polynomial.C (p.coeff 1) * Polynomial.X +
          Polynomial.X ^ 2 * p.divX.divX := by ring

private noncomputable abbrev zmod2M : DerivedCategory (ModuleCat.{0} ℤ) :=
  (singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)) ⊞
    (singleFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ZMod 2))

private noncomputable abbrev zmod2Ghost : End zmod2M :=
  End.of (biprod.snd ≫ zmod2Ext1Map ≫ biprod.inl)

private noncomputable abbrev zmod2Action : Polynomial ℤ →ₐ[ℤ] End zmod2M :=
  Polynomial.aeval zmod2Ghost

private theorem zmod2_biprod_isGE_isLE : zmod2M.IsGE 0 ∧ zmod2M.IsLE 1 := by
  have hzero : ∀ i : ℤ,
      IsZero ((homologyFunctor (ModuleCat.{0} ℤ) i).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)))) →
      IsZero ((homologyFunctor (ModuleCat.{0} ℤ) i).obj
        ((singleFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ZMod 2)))) →
      IsZero ((homologyFunctor (ModuleCat.{0} ℤ) i).obj zmod2M) := by
    intro i h0 h1
    rw [IsZero.iff_id_eq_zero, ← (homologyFunctor (ModuleCat.{0} ℤ) i).map_id, ← biprod.total,
      Functor.map_add, Functor.map_comp, Functor.map_comp,
      h0.eq_of_tgt ((homologyFunctor (ModuleCat.{0} ℤ) i).map biprod.fst) 0,
      h1.eq_of_tgt ((homologyFunctor (ModuleCat.{0} ℤ) i).map biprod.snd) 0]
    simp
  exact ⟨(isGE_iff zmod2M 0).mpr fun i hi ↦
      hzero i (isZero_of_isGE _ 0 i hi) (isZero_of_isGE _ 1 i (by omega)),
    (isLE_iff zmod2M 1).mpr fun i hi ↦
      hzero i (isZero_of_isLE _ 0 i (by omega)) (isZero_of_isLE _ 1 i hi)⟩

private theorem zmod2_two_smul_id_eq_zero :
    (2 : ℤ) • (1 : End zmod2M) = 0 ∧ (2 : ℤ) • zmod2Ext1Map = 0 ∧
      (2 : ℤ) • 𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) = 0 ∧
      𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) ≠ 0 := by
  have h2F₂ : (2 : ℤ) • 𝟙 (ModuleCat.of ℤ (ZMod 2)) = 0 := by
    ext (a : ZMod 2); fin_cases a <;> decide
  have h2s0 : (2 : ℤ) • 𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) =
      0 := by
    rw [← (singleFunctor (ModuleCat.{0} ℤ) 0).map_id,
      ← (singleFunctor (ModuleCat.{0} ℤ) 0).map_zsmul, h2F₂, Functor.map_zero]
  have h2s1 : (2 : ℤ) • 𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ZMod 2))) =
      0 := by
    rw [← (singleFunctor (ModuleCat.{0} ℤ) 1).map_id,
      ← (singleFunctor (ModuleCat.{0} ℤ) 1).map_zsmul, h2F₂, Functor.map_zero]
  refine ⟨?_, ?_, h2s0, ?_⟩
  · apply End.ext
    rw [End.smul_asHom, End.one_asHom, End.zero_asHom]
    apply biprod.hom_ext'
    · rw [Preadditive.comp_zsmul, Category.comp_id, ← Category.id_comp biprod.inl,
        ← Preadditive.zsmul_comp, h2s0, zero_comp, comp_zero]
    · rw [Preadditive.comp_zsmul, Category.comp_id, ← Category.id_comp biprod.inr,
        ← Preadditive.zsmul_comp, h2s1, zero_comp, comp_zero]
  · rw [← Category.comp_id zmod2Ext1Map, ← Preadditive.comp_zsmul, h2s0, comp_zero]
  · intro h
    have hF₂ : 𝟙 (ModuleCat.of ℤ (ZMod 2)) = 0 :=
      (singleFunctor (ModuleCat.{0} ℤ) 0).map_injective (by simpa using h)
    exact (by decide : (1 : ZMod 2) ≠ 0) (congrArg (fun f : ModuleCat.of ℤ (ZMod 2) ⟶ _ ↦ f 1) hF₂)

private theorem zmod2_odd_smul_ne_zero {G : Type*} [AddCommGroup G] {g : G}
    (hg : g ≠ 0) (h2 : (2 : ℤ) • g = 0) {n : ℤ} (hn : n • g = 0) : (2 : ℤ) ∣ n := by
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k, by omega⟩
  · exfalso
    apply hg
    have : (2 * k + 1) • g = k • ((2 : ℤ) • g) + g := by
      rw [add_zsmul, mul_comm, mul_zsmul, one_zsmul]
    rw [this, h2, smul_zero, zero_add] at hn
    exact hn

private theorem zmod2_ghost_sq : zmod2Ghost ^ 2 = 0 :=
  End.ext (by simp [sq, Category.assoc])

private theorem zmod2_ghost_ker :
    RingHom.ker zmod2Action = Ideal.span {(2 : Polynomial ℤ), Polynomial.X ^ 2} := by
  have ⟨h2M, h2δ, h2s0, hid0⟩ := zmod2_two_smul_id_eq_zero
  refine le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨q, hq⟩ := polynomial_decomp_deg_two p
    have hp0 : (p.coeff 0 : ℤ) • (1 : End zmod2M) + (p.coeff 1 : ℤ) • zmod2Ghost = 0 := by
      have hα : zmod2Action p = (p.coeff 0 : ℤ) • 1 + (p.coeff 1 : ℤ) • zmod2Ghost := by
        conv_lhs => rw [hq]
        simp [zmod2_ghost_sq]
      simpa [hα] using hp
    obtain ⟨k₀, hk₀⟩ : (2 : ℤ) ∣ p.coeff 0 := by
      refine zmod2_odd_smul_ne_zero hid0 h2s0 ?_
      have := congrArg (fun g : End zmod2M ↦ biprod.inl ≫ g.asHom ≫ biprod.fst) hp0
      simpa [End.intCast_asHom, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
        Category.assoc] using this
    obtain ⟨k₁, hk₁⟩ : (2 : ℤ) ∣ p.coeff 1 := by
      refine zmod2_odd_smul_ne_zero zmod2Ext1Map_ne_zero h2δ ?_
      have := congrArg (fun g : End zmod2M ↦ biprod.inr ≫ g.asHom ≫ biprod.fst) hp0
      simpa [End.intCast_asHom, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
        Category.assoc] using this
    rw [hq, hk₀, hk₁]
    have h2mem : (2 : Polynomial ℤ) ∈ Ideal.span {(2 : Polynomial ℤ), Polynomial.X ^ 2} :=
      Ideal.subset_span (by simp)
    have hX2mem : Polynomial.X ^ 2 ∈ Ideal.span {(2 : Polynomial ℤ), Polynomial.X ^ 2} :=
      Ideal.subset_span (by simp)
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) (Ideal.mul_mem_right q _ hX2mem)
    · rw [show Polynomial.C (2 * k₀) = Polynomial.C k₀ * 2 by simp [mul_comm]]
      exact Ideal.mul_mem_left _ _ h2mem
    · rw [show Polynomial.C (2 * k₁) * Polynomial.X = (Polynomial.C k₁ * Polynomial.X) * 2 by
        simp only [map_mul, map_ofNat]; ring]
      exact Ideal.mul_mem_left _ _ h2mem
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_ofNat]
      simpa [zsmul_one] using h2M
    · simp [RingHom.mem_ker, zmod2_ghost_sq]

private theorem zmod2_action_ghost_ker :
    IsGhost zmod2Ghost ∧
      actionGhostKer zmod2Action.toRingHom = Ideal.span {(2 : Polynomial ℤ), Polynomial.X} := by
  have ⟨h2M, _, h2s0, hid0⟩ := zmod2_two_smul_id_eq_zero
  have hghostx : IsGhost zmod2Ghost := by
    intro i
    have hδi : (homologyFunctor (ModuleCat.{0} ℤ) i).map zmod2Ext1Map = 0 := by
      rcases lt_or_ge i 1 with hlt | hge'
      · exact (isZero_of_isGE _ 1 i hlt).eq_of_src _ _
      · exact (isZero_of_isLE _ 0 i (by omega)).eq_of_tgt _ _
    simp [hδi]
  refine ⟨hghostx, le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)⟩
  · have hp0 : cohomologyAction ℤ zmod2M (zmod2Action p) = 0 :=
      (isGhost_iff_cohomologyAction_eq_zero ℤ).mp (mem_actionGhostKer_iff.mp hp)
    have hcohx : cohomologyAction ℤ zmod2M zmod2Ghost = 0 :=
      (isGhost_iff_cohomologyAction_eq_zero ℤ).mp hghostx
    obtain ⟨q, hq⟩ := polynomial_decomp_deg_two p
    have hα : zmod2Action p = (p.coeff 0 : ℤ) • 1 + (p.coeff 1 : ℤ) • zmod2Ghost := by
      conv_lhs => rw [hq]
      simp [zmod2_ghost_sq]
    have h0 : (p.coeff 0 : ℤ) •
        𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))) = 0 := by
      have hcomp := congrArg (fun g ↦ (homologyFunctor (ModuleCat.{0} ℤ) 0).map biprod.inl ≫
        (g 0).asHom ≫ (homologyFunctor (ModuleCat.{0} ℤ) 0).map biprod.fst) hp0
      rw [hα, map_add, map_zsmul, map_zsmul, hcohx, smul_zero, add_zero] at hcomp
      rw [← homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ 0]
      simpa [End.intCast_asHom, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
        Functor.map_zsmul, ← Functor.map_comp] using hcomp
    obtain ⟨k₀, hk₀⟩ := zmod2_odd_smul_ne_zero hid0 h2s0 h0
    have hpX : p = Polynomial.C (2 * k₀) + Polynomial.X * p.divX := by
      rw [← hk₀, add_comm]; exact (Polynomial.X_mul_divX_add p).symm
    rw [hpX]
    have h2mem : (2 : Polynomial ℤ) ∈ Ideal.span {(2 : Polynomial ℤ), Polynomial.X} :=
      Ideal.subset_span (by simp)
    have hXmem : Polynomial.X ∈ Ideal.span {(2 : Polynomial ℤ), Polynomial.X} :=
      Ideal.subset_span (by simp)
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right p.divX _ hXmem)
    rw [show Polynomial.C (2 * k₀) = Polynomial.C k₀ * 2 by simp [mul_comm]]
    exact Ideal.mul_mem_left _ _ h2mem
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · rw [SetLike.mem_coe, mem_actionGhostKer_iff]
      have h2 : zmod2Action.toRingHom 2 = 0 := by rw [map_ofNat]; simpa [zsmul_one] using h2M
      rw [h2]
      exact isGhost_zero zmod2M
    · simpa [mem_actionGhostKer_iff] using hghostx

private example :
    zmod2Ghost ≠ 0 ∧ zmod2Ghost ^ 2 = 0 ∧
    biprod.inr ≫ zmod2Ghost.asHom ≫ biprod.fst = zmod2Ext1Map ∧
    biprod.inl ≫ zmod2Ghost.asHom ≫ biprod.snd = 0 ∧
    cohomologyAction ℤ zmod2M zmod2Ghost = 0 ∧ zmod2Ghost ∈ ghostIdeal zmod2M ∧
    RingHom.ker zmod2Action = Ideal.span {(2 : Polynomial ℤ), Polynomial.X ^ 2} ∧
    actionGhostKer zmod2Action.toRingHom = Ideal.span {(2 : Polynomial ℤ), Polynomial.X} ∧
    zmod2Action.rangeRestrict Polynomial.X ∈ imageGhostIdeal ℤ zmod2Action ∧
    zmod2Action.rangeRestrict Polynomial.X ≠ 0 ∧ (imageGhostIdeal ℤ zmod2Action) ^ 2 = ⊥ ∧
    cohomologyImageQuotientEquiv ℤ zmod2Action
      (Ideal.Quotient.mk _ (zmod2Action.rangeRestrict Polynomial.X)) = 0 ∧
    cohomologyImageQuotientEquiv ℤ zmod2Action
      (Ideal.Quotient.mk _ (zmod2Action.rangeRestrict 1)) ≠ 0 := by
  have ⟨hge, hle⟩ := zmod2_biprod_isGE_isLE
  have ⟨_, _, _, hid0⟩ := zmod2_two_smul_id_eq_zero
  have ⟨hghostx, hghostker⟩ := zmod2_action_ghost_ker
  have hUR : biprod.inr ≫ zmod2Ghost.asHom ≫ biprod.fst = zmod2Ext1Map := by
    simp [Category.assoc]
  have hLL : biprod.inl ≫ zmod2Ghost.asHom ≫ biprod.snd = 0 := by simp [Category.assoc]
  have hxne : zmod2Ghost ≠ 0 := fun h ↦ zmod2Ext1Map_ne_zero (by rw [← hUR, h]; simp)
  have hcohx : cohomologyAction ℤ zmod2M zmod2Ghost = 0 :=
    (isGhost_iff_cohomologyAction_eq_zero ℤ).mp hghostx
  have h1ne : cohomologyImageQuotientEquiv ℤ zmod2Action
      (Ideal.Quotient.mk _ (zmod2Action.rangeRestrict 1)) ≠ 0 := by
    intro h0
    have h1g : IsGhost (1 : End zmod2M) := (isGhost_iff_cohomologyAction_eq_zero ℤ).mpr
      (by simpa [cohomologyImageQuotientEquiv_mk_val] using congrArg Subtype.val h0)
    have hidH : (homologyFunctor (ModuleCat.{0} ℤ) 0).map
        (𝟙 ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2)))) = 0 := by
      have := congrArg (fun f ↦ (homologyFunctor (ModuleCat.{0} ℤ) 0).map biprod.inl ≫ f ≫
        (homologyFunctor (ModuleCat.{0} ℤ) 0).map biprod.fst) (h1g 0)
      simpa [Category.id_comp, ← Functor.map_comp] using this
    exact hid0 ((homologyFunctor_map_eq_zero_iff_of_isLE_of_isGE _ 0).mp hidH)
  refine ⟨hxne, zmod2_ghost_sq, hUR, hLL, hcohx, mem_ghostIdeal_iff.mpr hghostx, zmod2_ghost_ker,
    hghostker, by simpa using hghostx,
    fun h ↦ hxne (by simpa using congrArg Subtype.val h),
    imageGhostIdeal_pow_eq_bot ℤ zmod2Action 0 1 2 (by omega),
    Subtype.ext (by simpa using hcohx), h1ne⟩

end Examples

end DerivedCategory
