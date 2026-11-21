/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.Algebra.Homology.DerivedCategory.Linear
public import TauCeti.Algebra.Homology.DerivedCategory.TStructure
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Preadditive.Endomorphism

/-!
# Cohomology actions, ghost ideals, ghost nilpotence, and derived endomorphism images

In a derived category `DerivedCategory C`, an endomorphism `f : End X` can induce zero on every
cohomology object `H^i(X)` while remaining nonzero, because of non-split extensions between
different cohomology degrees; such endomorphisms are called ghosts. For an object `X` with
cohomology concentrated in a bounded interval `[a, b]`, any product of more than `b - a` ghosts
vanishes. Consequently, the image of an algebra action `α : H →ₐ[R] End X` differs from its image
on cohomology by a nilpotent two-sided ideal of exponent at most `(b - a).toNat + 1`.

When `R` is a ring and `C` is `R`-linear, this module's public import of
`TauCeti.Algebra.Homology.DerivedCategory.Linear` (which publicly imports
`Mathlib.Algebra.Homology.DerivedCategory.Linear`) automatically supplies the
`Linear R (DerivedCategory C)` and `(homologyFunctor C i).Linear R` instances needed by the
`R`-algebra API below.

Main declarations:

* **Cohomology action and ghost ideal**:
  * `DerivedCategory.cohomologyActionRingHom` and `DerivedCategory.cohomologyAction`: for an
    object `X : DerivedCategory C`, the ring homomorphism (and, in a linear setting, `R`-algebra
    homomorphism) `End X → ∀ i : ℤ, End ((homologyFunctor C i).obj X)` sending `f` to `(H^i(f))_i`.
  * `CategoryTheory.End.IsGhost`: predicate asserting that an endomorphism `f : End X` induces
    zero on every `H^i(X)`.
  * `DerivedCategory.ghostIdeal`: the two-sided ideal of ghosts in `End X`, defined via
    `TwoSidedIdeal.ker X.cohomologyActionRingHom` independently of any coefficient ring `R`.
* **Ghost nilpotence and annihilator bounds**:
  * `TauCeti.DerivedCategory.exists_comp_truncLEι_mul_of_homologyFunctor_map_eq_zero` and
    `TauCeti.DerivedCategory.exists_comp_truncLEι_list_prod_of_isLE_of_homologyFunctor_map_eq_zero`:
    for `X` concentrated in degrees `≤ b` (`X.IsLE b`), an ordered product `l.prod` of
    endomorphisms acting by zero on `H^i(X)` for `a < i ≤ b` (`a + l.length = b`) factors through
    `τ_{≤ a} X ⟶ X`.
  * `TauCeti.DerivedCategory.list_prod_eq_zero_of_isGE_of_isLE_of_homologyFunctor_map_eq_zero` and
    `TauCeti.DerivedCategory.list_prod_ofFn_eq_zero_of_isGE_of_isLE_of_isGhost`: if `X` is
    concentrated in `[a, b]`, every ordered product of more than `b - a` ghosts in `End X`
    vanishes (in particular, any ordered product of `(b - a).toNat + 1` ghosts vanishes).
  * `TauCeti.DerivedCategory.actionGhostKer`,
    `TauCeti.DerivedCategory.exists_comp_truncLEι_of_isLE_of_le_actionGhostKer_of_mem_pow`, and
    `TauCeti.DerivedCategory.pow_le_ker_of_le_actionGhostKer`: for any ring homomorphism
    `α : F` (`[RingHomClass F H (End X)]`) and ideal `I ≤ actionGhostKer α`, `I ^ n ≤ RingHom.ker α`
    whenever `b < a + n`.
  * `TauCeti.DerivedCategory.ghostIdeal_asIdeal_pow_eq_bot`,
    `AlgHom.imageGhostIdeal`, `AlgHom.imageGhostIdeal_pow_eq_bot`,
    and `AlgHom.imageGhostIdealQuotientEquivCohomologyImage`: the ghost ideal on `α.range` is
    nilpotent of exponent at most `(b - a).toNat + 1`, and its quotient is isomorphic as an
    `R`-algebra to `((X.cohomologyAction R).comp α).range`.

## References

* P. B. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. V. Le Hung, J. Newton, P. Scholze,
  R. Taylor, and J. A. Thorne, *Potential automorphy over CM fields*, Ann. of Math. (2) 197 (2023),
  897–1113, §2.2.3 and Lemma 2.2.4, pp. 920–921.
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
    (X.cohomologyActionRingHom f i).asHom = (homologyFunctor C i).map f.asHom := by
  simp [cohomologyActionRingHom]

/-- The two-sided ideal of ghost endomorphisms of `X : DerivedCategory C`. -/
noncomputable def ghostIdeal (X : DerivedCategory C) : TwoSidedIdeal (End X) :=
  TwoSidedIdeal.ker X.cohomologyActionRingHom

section Linear

variable (X : DerivedCategory C) (R : Type t) [CommSemiring R] [Linear R C]
  [Linear R (DerivedCategory C)] [∀ i : ℤ, (homologyFunctor C i).Linear R]

/-- The `R`-algebra homomorphism `End X →ₐ[R] ∀ i : ℤ, End ((homologyFunctor C i).obj X)` sending
a derived endomorphism `f` to its induced family of cohomology endomorphisms `(H^i(f))_i`. -/
noncomputable def cohomologyAction :
    End X →ₐ[R] ∀ i : ℤ, End ((homologyFunctor C i).obj X) :=
  AlgHom.pi fun i ↦ (homologyFunctor C i).mapEndAlgHom R X

/-- Applying `cohomologyAction` at degree `i` gives `(homologyFunctor C i).map f.asHom`. -/
@[simp]
theorem cohomologyAction_apply_asHom (f : End X) (i : ℤ) :
    (X.cohomologyAction R f i).asHom = (homologyFunctor C i).map f.asHom := by
  simp [cohomologyAction]

/-- The underlying ring homomorphism of `X.cohomologyAction R` is `X.cohomologyActionRingHom`. -/
@[simp]
theorem cohomologyAction_toRingHom :
    (X.cohomologyAction R : End X →+* ∀ i : ℤ, End ((homologyFunctor C i).obj X)) =
      X.cohomologyActionRingHom := by
  ext f i
  simp

/-- The two-sided kernel of `X.cohomologyAction R` is `X.ghostIdeal`, independently of `R`. -/
theorem twoSidedIdeal_ker_cohomologyAction :
    TwoSidedIdeal.ker (X.cohomologyAction R).toRingHom = X.ghostIdeal := by
  rw [AlgHom.toRingHom_eq_coe, cohomologyAction_toRingHom, ghostIdeal]

end Linear

end CohomologyAction

end DerivedCategory

namespace CategoryTheory.End

open DerivedCategory

section Ghost

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An endomorphism `f : End X` in `DerivedCategory C` is a ghost if it induces zero on every
cohomology object `H^i(X)`. -/
def IsGhost {X : DerivedCategory C} (f : End X) : Prop :=
  ∀ i : ℤ, (homologyFunctor C i).map f.asHom = 0

/-- Characterization of `End.IsGhost`. -/
theorem isGhost_iff {X : DerivedCategory C} {f : End X} :
    f.IsGhost ↔ ∀ i : ℤ, (homologyFunctor C i).map f.asHom = 0 :=
  Iff.rfl

/-- An endomorphism is a ghost if and only if it lies in the kernel of
`DerivedCategory.cohomologyActionRingHom`. -/
theorem isGhost_iff_cohomologyActionRingHom_eq_zero {X : DerivedCategory C} {f : End X} :
    f.IsGhost ↔ X.cohomologyActionRingHom f = 0 := by
  constructor
  · intro hf
    ext i
    simpa [DerivedCategory.cohomologyActionRingHom_apply_asHom] using hf i
  · intro hf i
    simpa [DerivedCategory.cohomologyActionRingHom_apply_asHom] using
      congrArg (fun g ↦ (g i).asHom) hf

/-- The zero endomorphism is a ghost. -/
@[simp]
theorem isGhost_zero {X : DerivedCategory C} : (0 : End X).IsGhost := by
  intro i
  simp

section Linear

variable (R : Type t) [CommSemiring R] [Linear R C] [Linear R (DerivedCategory C)]
  [∀ i : ℤ, (homologyFunctor C i).Linear R]

/-- An endomorphism is a ghost if and only if it lies in the kernel of `cohomologyAction`. -/
theorem isGhost_iff_cohomologyAction_eq_zero {X : DerivedCategory C} {f : End X} :
    f.IsGhost ↔ X.cohomologyAction R f = 0 := by
  rw [isGhost_iff_cohomologyActionRingHom_eq_zero, ← X.cohomologyAction_toRingHom R,
    AlgHom.coe_toRingHom]

end Linear

end Ghost

end CategoryTheory.End

namespace TauCeti.DerivedCategory

open _root_.DerivedCategory

section GhostMembership

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An endomorphism belongs to `X.ghostIdeal` if and only if it is a ghost. -/
@[simp]
theorem mem_ghostIdeal_iff {X : _root_.DerivedCategory C} {f : End X} :
    f ∈ X.ghostIdeal ↔ f.IsGhost := by
  rw [ghostIdeal, TwoSidedIdeal.mem_ker, End.isGhost_iff_cohomologyActionRingHom_eq_zero]

section Linear

variable (R : Type t) [CommSemiring R] [Linear R C] [Linear R (_root_.DerivedCategory C)]
  [∀ i : ℤ, (homologyFunctor C i).Linear R]

/-- Membership in `RingHom.ker (X.cohomologyAction R)` is equivalent to `End.IsGhost`. -/
theorem mem_ringHom_ker_cohomologyAction_iff {X : _root_.DerivedCategory C} {f : End X} :
    f ∈ RingHom.ker (X.cohomologyAction R) ↔ f.IsGhost := by
  rw [RingHom.mem_ker, End.isGhost_iff_cohomologyAction_eq_zero R]

end Linear

end GhostMembership

section GhostNilpotence

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If `e : End X` factors through `τ_{≤ b₁} X ⟶ X` and `f : End X` induces zero on `H^{b₁}(X)`,
then `f * e` factors through `τ_{≤ b₀} X ⟶ X` whenever `b₀ + 1 = b₁`. -/
theorem exists_comp_truncLEι_mul_of_homologyFunctor_map_eq_zero {X : _root_.DerivedCategory C}
    (b₀ b₁ : ℤ) {f e : End X} (hf : (homologyFunctor C b₁).map f.asHom = 0)
    (he : ∃ g : X ⟶ (TStructure.t.truncLE b₁).obj X,
      g ≫ (TStructure.t.truncLEι b₁).app X = e.asHom)
    (hb : b₀ + 1 = b₁ := by lia) :
    ∃ g : X ⟶ (TStructure.t.truncLE b₀).obj X,
      g ≫ (TStructure.t.truncLEι b₀).app X = (f * e).asHom := by
  obtain ⟨g, hg⟩ := he
  have hcomp : (homologyFunctor C b₁).map ((TStructure.t.truncLEι b₁).app X ≫ f.asHom) = 0 := by
    rw [Functor.map_comp, hf, comp_zero]
  obtain ⟨u, hu⟩ := exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero
    ((TStructure.t.truncLEι b₁).app X ≫ f.asHom) b₀ b₁ hcomp hb
  refine ⟨g ≫ u, ?_⟩
  rw [Category.assoc, hu, ← Category.assoc, hg, End.mul_asHom]

/-- If `X` is concentrated in degrees `≤ b` and every `f ∈ l` induces zero on `H^i(X)` for
`a < i ≤ b` (where `a + l.length = b`), then the ordered product `l.prod` factors through
`τ_{≤ a} X ⟶ X`. -/
theorem exists_comp_truncLEι_list_prod_of_isLE_of_homologyFunctor_map_eq_zero
    {X : _root_.DerivedCategory C} (a b : ℤ) [X.IsLE b] (l : List (End X))
    (hl : ∀ f ∈ l, ∀ i : ℤ, a < i → i ≤ b → (homologyFunctor C i).map f.asHom = 0)
    (hab : a + l.length = b := by lia) :
    ∃ g : X ⟶ (TStructure.t.truncLE a).obj X,
      g ≫ (TStructure.t.truncLEι a).app X = l.prod.asHom := by
  induction l generalizing a with
  | nil =>
    obtain rfl : a = b := by simp at hab; lia
    rw [List.prod_nil, End.one_asHom]
    exact ⟨TStructure.t.liftTruncLE (𝟙 X) a, TStructure.t.liftTruncLE_ι (𝟙 X) a⟩
  | cons f l ih =>
    have hab' : (a + 1) + l.length = b := by simp at hab; lia
    have hl' : ∀ f' ∈ l, ∀ i : ℤ, a + 1 < i → i ≤ b →
        (homologyFunctor C i).map f'.asHom = 0 :=
      fun f' hf' i hi₁ hi₂ ↦ hl f' (List.mem_cons_of_mem f hf') i (by lia) hi₂
    have hf : (homologyFunctor C (a + 1)).map f.asHom = 0 :=
      hl f List.mem_cons_self (a + 1) (by lia) (by lia)
    rw [List.prod_cons]
    exact exists_comp_truncLEι_mul_of_homologyFunctor_map_eq_zero a (a + 1) hf (ih (a + 1) hl' hab')

/-- Ghost nilpotence for arbitrary ordered lists: if `X` is concentrated in `[a, b]` and every
`f ∈ l` acts by zero on `H^i(X)` for `a ≤ i ≤ b`, then `l.prod = 0` whenever `b < a + l.length`. -/
theorem list_prod_eq_zero_of_isGE_of_isLE_of_homologyFunctor_map_eq_zero
    {X : _root_.DerivedCategory C} (a b : ℤ) [X.IsGE a] [X.IsLE b] (l : List (End X))
    (hl : ∀ f ∈ l, ∀ i : ℤ, a ≤ i → i ≤ b → (homologyFunctor C i).map f.asHom = 0)
    (hlen : b < a + l.length) :
    l.prod = 0 := by
  have hl' : ∀ f ∈ l, ∀ i : ℤ, b - l.length < i → i ≤ b →
      (homologyFunctor C i).map f.asHom = 0 := by
    intro f hf i _ hib
    by_cases hia : a ≤ i
    · exact hl f hf i hia hib
    · exact (isZero_of_isGE X a i (by omega)).eq_of_src _ _
  obtain ⟨g, hg⟩ :=
    exists_comp_truncLEι_list_prod_of_isLE_of_homologyFunctor_map_eq_zero (b - l.length) b l hl'
  have hz : IsZero ((TStructure.t.truncLE (b - l.length)).obj X) :=
    TStructure.t.isZero ((TStructure.t.truncLE (b - l.length)).obj X) (b - l.length) a (by omega)
  apply End.ext
  rw [← hg, hz.eq_of_tgt g 0, zero_comp, End.zero_asHom]

/-- Ghost nilpotence (Allen et al., Lemma 2.2.4): if `X` is concentrated in `[a, b]`, then every
ordered product of `(b - a).toNat + 1` ghost endomorphisms of `X` vanishes. -/
theorem list_prod_ofFn_eq_zero_of_isGE_of_isLE_of_isGhost {X : _root_.DerivedCategory C}
    (a b : ℤ) [X.IsGE a] [X.IsLE b] (fs : Fin ((b - a).toNat + 1) → End X)
    (hfs : ∀ j, (fs j).IsGhost) :
    (List.ofFn fs).prod = 0 := by
  refine list_prod_eq_zero_of_isGE_of_isLE_of_homologyFunctor_map_eq_zero a b (List.ofFn fs)
    (fun f hf i _ _ ↦ ?_) (by simp; omega)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  exact hfs j i

/-- The action ghost kernel of a ring homomorphism `α : F` (`[RingHomClass F H (End X)]`),
consisting of all `h : H` whose image `α h` acts by zero on every cohomology object `H^i(X)`. -/
noncomputable def actionGhostKer {H : Type t} [Semiring H] {X : _root_.DerivedCategory C}
    {F : Type*} [FunLike F H (End X)] [RingHomClass F H (End X)] (α : F) : Ideal H :=
  Ideal.comap α X.ghostIdeal.asIdeal

/-- An element belongs to `actionGhostKer α` if and only if its image under `α` is a ghost. -/
@[simp]
theorem mem_actionGhostKer_iff {H : Type t} [Semiring H] {X : _root_.DerivedCategory C}
    {F : Type*} [FunLike F H (End X)] [RingHomClass F H (End X)] {α : F} {h : H} :
    h ∈ actionGhostKer α ↔ (α h).IsGhost := by
  rw [actionGhostKer, Ideal.mem_comap, TwoSidedIdeal.mem_asIdeal, mem_ghostIdeal_iff]

/-- The action ghost kernel of `α` is a two-sided ideal of `H`. -/
instance actionGhostKer_isTwoSided {H : Type t} [Semiring H] {X : _root_.DerivedCategory C}
    {F : Type*} [FunLike F H (End X)] [RingHomClass F H (End X)] (α : F) :
    (actionGhostKer α).IsTwoSided := by
  unfold actionGhostKer
  infer_instance

/-- The kernel of `α` is contained in the action ghost kernel of `α`. -/
theorem ker_le_actionGhostKer {H : Type t} [Semiring H] {X : _root_.DerivedCategory C}
    {F : Type*} [FunLike F H (End X)] [RingHomClass F H (End X)] (α : F) :
    RingHom.ker α ≤ actionGhostKer α := by
  intro h hh
  rw [mem_actionGhostKer_iff, RingHom.mem_ker.mp hh]
  exact End.isGhost_zero

/-- If `X` is concentrated in degrees `≤ b` and `I ≤ actionGhostKer α`, then every `x ∈ I ^ n`
acts via a morphism factoring through `τ_{≤ a} X ⟶ X` whenever `a + n = b`. -/
theorem exists_comp_truncLEι_of_isLE_of_le_actionGhostKer_of_mem_pow {H : Type t} [Semiring H]
    {X : _root_.DerivedCategory C} {F : Type*} [FunLike F H (End X)] [RingHomClass F H (End X)]
    (α : F) (I : Ideal H) (a b : ℤ) [X.IsLE b] (hI : I ≤ actionGhostKer α) (n : ℕ) {x : H}
    (hx : x ∈ I ^ n) (hab : a + n = b := by lia) :
    ∃ g : X ⟶ (TStructure.t.truncLE a).obj X,
      g ≫ (TStructure.t.truncLEι a).app X = (α x).asHom := by
  induction n generalizing a x with
  | zero =>
    obtain rfl : a = b := by lia
    exact ⟨TStructure.t.liftTruncLE (α x).asHom a, TStructure.t.liftTruncLE_ι (α x).asHom a⟩
  | succ n ih =>
    cases n with
    | zero =>
      rw [Submodule.pow_one] at hx
      have hghost : (α x).IsGhost := mem_actionGhostKer_iff.mp (hI hx)
      exact exists_comp_truncLEι_of_isLE_of_homologyFunctor_map_eq_zero (α x).asHom a b
        (hghost b) (by lia)
    | succ n =>
      rw [Submodule.pow_succ' _ (Nat.succ_ne_zero n)] at hx
      refine Submodule.mul_induction_on hx (fun r hr y hy ↦ ?_) (fun y z hy hz ↦ ?_)
      · have hr' : (homologyFunctor C (a + 1)).map (α r).asHom = 0 :=
          mem_actionGhostKer_iff.mp (hI hr) (a + 1)
        rw [map_mul]
        exact exists_comp_truncLEι_mul_of_homologyFunctor_map_eq_zero a (a + 1) hr'
          (ih (a + 1) hy (by lia))
      · obtain ⟨g₁, hg₁⟩ := hy
        obtain ⟨g₂, hg₂⟩ := hz
        refine ⟨g₁ + g₂, ?_⟩
        rw [Preadditive.add_comp, hg₁, hg₂, map_add, End.add_asHom]

/-- Action-annihilator bound (Allen et al., Lemma 2.2.4): if `X` is concentrated in `[a, b]` and
`I ≤ actionGhostKer α`, then `I ^ n ≤ RingHom.ker α` whenever `b < a + n`. -/
theorem pow_le_ker_of_le_actionGhostKer {H : Type t} [Semiring H] {X : _root_.DerivedCategory C}
    {F : Type*} [FunLike F H (End X)] [RingHomClass F H (End X)] (α : F) (I : Ideal H)
    (a b : ℤ) [X.IsGE a] [X.IsLE b] (n : ℕ) (hI : I ≤ actionGhostKer α) (hn : b < a + n) :
    I ^ n ≤ RingHom.ker α := by
  intro x hx
  obtain ⟨g, hg⟩ :=
    exists_comp_truncLEι_of_isLE_of_le_actionGhostKer_of_mem_pow α I (b - n) b hI n hx
  have hz : IsZero ((TStructure.t.truncLE (b - n)).obj X) :=
    TStructure.t.isZero ((TStructure.t.truncLE (b - n)).obj X) (b - n) a (by omega)
  rw [RingHom.mem_ker]
  apply End.ext
  rw [← hg, hz.eq_of_tgt g 0, zero_comp, End.zero_asHom]

/-- If `X` is concentrated in `[a, b]` and `b < a + n`, then `X.ghostIdeal.asIdeal ^ n = ⊥`. -/
theorem ghostIdeal_asIdeal_pow_eq_bot {X : _root_.DerivedCategory C} (a b : ℤ) [X.IsGE a] [X.IsLE b]
    (n : ℕ) (hn : b < a + n) :
    X.ghostIdeal.asIdeal ^ n = ⊥ := by
  refine le_bot_iff.mp <|
    (pow_le_ker_of_le_actionGhostKer (RingHom.id (End X)) X.ghostIdeal.asIdeal a b n ?_ hn).trans
      fun _ hx ↦ Ideal.mem_bot.mpr (by simpa using RingHom.mem_ker.mp hx)
  intro x hx
  rw [mem_actionGhostKer_iff, RingHom.id_apply, ← mem_ghostIdeal_iff]
  exact TwoSidedIdeal.mem_asIdeal.mp hx

end GhostNilpotence

end TauCeti.DerivedCategory

namespace AlgHom

open _root_.DerivedCategory TauCeti.DerivedCategory

section ImageGhost

variable {R : Type t} [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [Linear R (_root_.DerivedCategory C)]

/-- The image ghost ideal of an `R`-algebra action `α : H →ₐ[R] CategoryTheory.End X`, consisting
of all elements of `α.range` that act by zero on every cohomology object `H^i(X)`. -/
noncomputable def imageGhostIdeal {H : Type t'} [Semiring H] [Algebra R H]
    {X : _root_.DerivedCategory C} (α : H →ₐ[R] CategoryTheory.End X) : Ideal α.range :=
  actionGhostKer α.range.val

/-- An element of `α.range` belongs to `α.imageGhostIdeal` if and only if it is a ghost. -/
@[simp]
theorem mem_imageGhostIdeal_iff {H : Type t'} [Semiring H] [Algebra R H]
    {X : _root_.DerivedCategory C} {α : H →ₐ[R] CategoryTheory.End X} {x : α.range} :
    x ∈ α.imageGhostIdeal ↔ x.1.IsGhost := by
  rw [imageGhostIdeal, mem_actionGhostKer_iff, Subalgebra.coe_val]

/-- The image ghost ideal of `α` is a two-sided ideal of `α.range`. -/
instance imageGhostIdeal_isTwoSided {H : Type t'} [Semiring H] [Algebra R H]
    {X : _root_.DerivedCategory C} (α : H →ₐ[R] CategoryTheory.End X) :
    α.imageGhostIdeal.IsTwoSided := by
  unfold imageGhostIdeal
  infer_instance

/-- If `X` is concentrated in `[a, b]` and `b < a + n`, then `α.imageGhostIdeal ^ n = ⊥`. -/
theorem imageGhostIdeal_pow_eq_bot {H : Type t'} [Semiring H] [Algebra R H]
    {X : _root_.DerivedCategory C} (α : H →ₐ[R] CategoryTheory.End X) (a b : ℤ) [X.IsGE a]
    [X.IsLE b] (n : ℕ) (hn : b < a + n) :
    α.imageGhostIdeal ^ n = ⊥ :=
  le_bot_iff.mp <|
    (pow_le_ker_of_le_actionGhostKer α.range.val α.imageGhostIdeal a b n le_rfl hn).trans
      fun _ hx ↦ Ideal.mem_bot.mpr (Subtype.ext (by simpa using RingHom.mem_ker.mp hx))

end ImageGhost

section CohomologyImageQuotient

variable {R : Type t} [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [Linear R C] [Linear R (_root_.DerivedCategory C)]
  [∀ i : ℤ, (homologyFunctor C i).Linear R]

/-- The cohomology image quotient equivalence: the quotient of the derived image `α.range` by its
image ghost ideal is isomorphic as an `R`-algebra to the cohomology image
`((X.cohomologyAction R).comp α).range`. -/
noncomputable def imageGhostIdealQuotientEquivCohomologyImage {H : Type t'} [Semiring H]
    [Algebra R H] {X : _root_.DerivedCategory C} (α : H →ₐ[R] CategoryTheory.End X) :
    (α.range ⧸ α.imageGhostIdeal) ≃ₐ[R] ((X.cohomologyAction R).comp α).range :=
  (Ideal.quotientEquivAlgOfEq R (show α.imageGhostIdeal =
      RingHom.ker ((X.cohomologyAction R).comp α.range.val) by
    ext x
    simp [mem_imageGhostIdeal_iff,
      CategoryTheory.End.isGhost_iff_cohomologyAction_eq_zero R])).trans <|
  (Ideal.quotientKerEquivRange ((X.cohomologyAction R).comp α.range.val)).trans <|
    Subalgebra.equivOfEq _ _ (by rw [Subalgebra.range_comp_val, ← AlgHom.range_comp])

/-- Applying `α.imageGhostIdealQuotientEquivCohomologyImage` to the class of `x : α.range` gives
`X.cohomologyAction R x.1`. -/
@[simp]
theorem imageGhostIdealQuotientEquivCohomologyImage_mk_val {H : Type t'} [Semiring H]
    [Algebra R H] {X : _root_.DerivedCategory C} (α : H →ₐ[R] CategoryTheory.End X)
    (x : α.range) :
    (α.imageGhostIdealQuotientEquivCohomologyImage
      (Ideal.Quotient.mk α.imageGhostIdeal x)).1 = X.cohomologyAction R x.1 := by
  simp [imageGhostIdealQuotientEquivCohomologyImage, Ideal.quotientKerEquivRange]

end CohomologyImageQuotient

end AlgHom
