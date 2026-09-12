/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import TauCeti.RepresentationTheory.Induction.Permutation
public import TauCeti.RepresentationTheory.Rep.OfMulAction

/-!
# Coinduction and induction from the trivial subgroup

For a group `G` and a `k`-module `X`, the representation coinduced from the trivial subgroup,
`coindBot k G X = Coind_⊥^G X`, is the module of functions `G → X` with `G` acting by right
translation, and the representation induced from the trivial subgroup, `indBot k G X = Ind_⊥^G X`,
is `k[G] ⊗ X`. Every representation `A` embeds into `coindBot k G A.V` (by `a ↦ (g ↦ g • a)`) and
is a quotient of `indBot k G A.V`; these are the two maps used for dimension shifting in
`TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift`.

By Shapiro's lemma, `Coind_⊥^G X` has vanishing positive-degree cohomology and `Ind_⊥^G X` has
vanishing positive-degree homology; the same holds after restriction to any subgroup, since the
restriction of a module (co)induced from the trivial subgroup is again (co)induced from the
trivial subgroup. For a finite group the two constructions agree and all Tate cohomology
vanishes (Milne, *Class Field Theory*, II 1.11, 1.12, 3.1).

The constructions follow `ClassFieldTheory/Cohomology/IndCoind/Finite.lean` and
`IndCoind/TrivialCohomology.lean` in `kbuzzard/ClassFieldTheory`, commit
`ccc3323c6750abca25b49b35106f54eb3a398509`, adapted to Mathlib's `Rep.coind` and `Rep.ind`.

## Main definitions

* `Rep.coindBot`, `Rep.coindBotFunctor`: coinduction from the trivial subgroup.
* `Rep.coindBotUnit`: the monomorphism `A ⟶ coindBot k G A.V`.
* `Rep.indBot`, `Rep.indBotFunctor`: induction from the trivial subgroup.
* `Rep.indBotCounit`: the epimorphism `indBot k G A.V ⟶ A`.
* `Rep.indBotIsoCoindBot`: for a finite group, `indBot k G X ≅ coindBot k G X`.
* `Rep.resCoindBotIso`: restriction to a subgroup `S` of a module coinduced from the trivial
  subgroup is coinduced from the trivial subgroup of `S`.
* `Rep.leftRegularIsoCoindBot`: for a finite group, `k[G] ≅ coindBot k G k`.

## Main statements

* `groupCohomology.isZero_coindBot_succ`, `groupCohomology.isZero_res_coindBot_succ`:
  `Hⁿ⁺¹(S, Coind_⊥^G X) = 0` for every subgroup `S ≤ G`.
* `groupHomology.isZero_indBot_succ`: `Hₙ₊₁(G, Ind_⊥^G X) = 0`.
* `TauCeti.TateCohomology.isZero_coindBot`, `TauCeti.TateCohomology.isZero_res_coindBot`:
  for a finite group, `Ĥⁿ(S, Coind_⊥^G X) = 0` for all `n : ℤ` (Milne II 3.1).
* `TauCeti.TateCohomology.isZero_indBot`, `TauCeti.TateCohomology.isZero_res_indBot`: the same
  for `Ind_⊥^G X`.
* `TauCeti.TateCohomology.isZero_res_leftRegular`: for a finite group, `Ĥⁿ(S, k[G]) = 0`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1 and §3.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §5 and §6.
-/

public noncomputable section

universe u

open CategoryTheory Limits

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- The restriction of a representation to the trivial subgroup is the trivial representation on
its underlying module. -/
def resBotIsoTrivial (A : Rep k G) :
    res (⊥ : Subgroup G).subtype A ≅ trivial k (⊥ : Subgroup G) A.V :=
  mkIso <| .mk (LinearEquiv.refl k A.V) fun s ↦ by
    obtain rfl : s = 1 := Subsingleton.elim s 1
    ext
    simp

variable (k G) in
/-- The representation of `G` coinduced from the trivial subgroup on a `k`-module `X`: the
functions `G → X`, with `G` acting by right translation, `(g • f) h = f (h * g)`. -/
abbrev coindBot (X : Type u) [AddCommGroup X] [Module k X] : Rep k G :=
  coind (⊥ : Subgroup G).subtype (trivial k (⊥ : Subgroup G) X)

variable (k G) in
/-- Coinduction from the trivial subgroup, as a functor `ModuleCat k ⥤ Rep k G`. -/
@[expose] def coindBotFunctor : ModuleCat.{u} k ⥤ Rep k G :=
  trivialFunctor k (⊥ : Subgroup G) ⋙ coindFunctor k (⊥ : Subgroup G).subtype

/-- Evaluating the coinduction functor from the trivial subgroup gives `coindBot`. -/
@[simp]
theorem coindBotFunctor_obj (X : ModuleCat.{u} k) : (coindBotFunctor k G).obj X = coindBot k G X :=
  rfl

/-- The canonical embedding of a representation `A` into the representation coinduced from the
trivial subgroup on its underlying module, `a ↦ (g ↦ A.ρ g a)`. -/
def coindBotUnit (A : Rep k G) : A ⟶ coindBot k G A.V :=
  resCoindToHom (⊥ : Subgroup G).subtype A (trivial k (⊥ : Subgroup G) A.V)
    (resBotIsoTrivial A).hom

/-- The embedding into the coinduced representation sends `a` to the function `g ↦ A.ρ g a`. -/
@[simp]
theorem coindBotUnit_hom_apply_coe (A : Rep k G) (a : A) (g : G) :
    ((coindBotUnit A).hom a).1 g = A.ρ g a := by
  rfl

/-- The embedding into the coinduced representation is a monomorphism. -/
instance coindBotUnit_mono (A : Rep k G) : Mono (coindBotUnit A) :=
  (mono_iff_injective _).2 fun x y h ↦ by
    have h1 : A.ρ 1 x = A.ρ 1 y := congrArg (fun f ↦ f.1 1) h
    simpa using h1

variable (k G) in
/-- The representation of `G` induced from the trivial subgroup on a `k`-module `X`, namely
`k[G] ⊗[k] X` with `G` acting on `k[G]`. -/
abbrev indBot (X : Type u) [AddCommGroup X] [Module k X] : Rep k G :=
  ind (⊥ : Subgroup G).subtype (trivial k (⊥ : Subgroup G) X)

variable (k G) in
/-- Induction from the trivial subgroup, as a functor `ModuleCat k ⥤ Rep k G`. -/
@[expose] def indBotFunctor : ModuleCat.{u} k ⥤ Rep k G :=
  trivialFunctor k (⊥ : Subgroup G) ⋙ indFunctor k (⊥ : Subgroup G).subtype

/-- Evaluating the induction functor from the trivial subgroup gives `indBot`. -/
@[simp]
theorem indBotFunctor_obj (X : ModuleCat.{u} k) : (indBotFunctor k G).obj X = indBot k G X :=
  rfl

/-- The canonical projection from the representation induced from the trivial subgroup on the
underlying module of `A` onto `A`, `⟦g ⊗ₜ a⟧ ↦ A.ρ g⁻¹ a`. -/
def indBotCounit (A : Rep k G) : indBot k G A.V ⟶ A :=
  (indResHomEquiv (⊥ : Subgroup G).subtype (trivial k (⊥ : Subgroup G) A.V) A).symm
    (resBotIsoTrivial A).inv

/-- The projection from the induced representation is an epimorphism. -/
instance indBotCounit_epi (A : Rep k G) : Epi (indBotCounit A) :=
  (epi_iff_surjective _).2 fun a ↦
    ⟨Representation.IndV.mk (⊥ : Subgroup G).subtype (trivial k (⊥ : Subgroup G) A.V).ρ 1 a,
      by simp [indBotCounit, resBotIsoTrivial]⟩

section Finite

variable [Finite G]

-- Mathlib's `indCoindIso` is stated with a decidability hypothesis on the right coset relation;
-- for the trivial subgroup we supply it classically.
attribute [local instance] Classical.decRel

/-- For a finite group, induction and coinduction from the trivial subgroup agree. -/
def indBotIsoCoindBot (X : Type u) [AddCommGroup X] [Module k X] : indBot k G X ≅ coindBot k G X :=
  indCoindIso (trivial k (⊥ : Subgroup G) X)

end Finite

section Restriction

variable (k G) in
/-- The underlying module of the representation coinduced from the trivial subgroup is the module
of all functions `G → X`. -/
def coindBotEquivPi (X : Type u) [AddCommGroup X] [Module k X] :
    (coindBot k G X : Type u) ≃ₗ[k] (G → X) where
  toFun f := f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f, fun g h ↦ by
    obtain rfl : g = 1 := Subsingleton.elim g 1
    simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of the coinduced module with functions is the underlying function. -/
@[simp]
theorem coindBotEquivPi_apply (X : Type u) [AddCommGroup X] [Module k X] (f : coindBot k G X) :
    coindBotEquivPi k G X f = f.1 := by
  rfl

/-- The inverse identification of functions with the coinduced module is the underlying
function. -/
@[simp]
theorem coindBotEquivPi_symm_apply_coe (X : Type u) [AddCommGroup X] [Module k X] (f : G → X) :
    ((coindBotEquivPi k G X).symm f).1 = f := by
  rfl

variable (S : Subgroup G)

/-- The bijection `S × G ⧸ S ≃ G` sending `(s, y)` to `y.out * s`, for a fixed choice of left
coset representatives. It is the factor-swap of Mathlib's `Subgroup.groupEquivQuotientProdSubgroup`,
but that equivalence carries no `apply`/`symm_apply` lemma and is built from a `cast`-laden calc, so
we spell out this variant to expose the defeq action `(s, y) ↦ y.out * s` that `resCoindBotIso`
needs. -/
def prodQuotientEquiv : S × (G ⧸ S) ≃ G :=
  Equiv.ofBijective (fun p ↦ p.2.out * p.1) ⟨fun ⟨s₁, y₁⟩ ⟨s₂, y₂⟩ h ↦ by
    obtain rfl : y₁ = y₂ := by
      simpa using congrArg (QuotientGroup.mk (s := S)) h
    simpa using h, fun g ↦
    ⟨(⟨(QuotientGroup.mk g : G ⧸ S).out⁻¹ * g,
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g))⟩, QuotientGroup.mk g),
      by simp⟩⟩

/-- The bijection `S × G ⧸ S ≃ G` sends `(s, y)` to `y.out * s`. -/
@[simp]
theorem prodQuotientEquiv_apply (p : S × (G ⧸ S)) : prodQuotientEquiv S p = p.2.out * p.1 := by
  rfl

/-- The restriction to a subgroup `S` of a representation coinduced from the trivial subgroup of
`G` is coinduced from the trivial subgroup of `S`, on `[G : S]` copies of the coefficients:
`f ↦ (s ↦ (y ↦ f (y.out * s)))`. -/
def resCoindBotIso (X : Type u) [AddCommGroup X] [Module k X] :
    res S.subtype (coindBot k G X) ≅ coindBot k S (G ⧸ S → X) :=
  mkIso <| .mk (coindBotEquivPi k G X ≪≫ₗ LinearEquiv.funCongrLeft k X (prodQuotientEquiv S) ≪≫ₗ
    LinearEquiv.curry k X S (G ⧸ S) ≪≫ₗ (coindBotEquivPi k S (G ⧸ S → X)).symm) fun s ↦ by
    ext f h y
    change f.1 (prodQuotientEquiv S (h, y) * s) = f.1 (prodQuotientEquiv S (h * s, y))
    simp [mul_assoc]

end Restriction

/-- For a finite group, the left regular representation `k[G]` is coinduced from the trivial
subgroup. It is the representation induced from the trivial subgroup, via `k[G] ≅ k[G ⧸ ⊥]`
(`quotientBotIsoLeftRegular`) and `Ind_⊥^G k ≅ k[G ⧸ ⊥]` (`indTrivialIso`), and for a finite group
induction and coinduction from the trivial subgroup agree (`indBotIsoCoindBot`). -/
def leftRegularIsoCoindBot [Finite G] : leftRegular k G ≅ coindBot k G k :=
  (TauCeti.indTrivialIso k (⊥ : Subgroup G) ≪≫ TauCeti.quotientBotIsoLeftRegular k).symm ≪≫
    indBotIsoCoindBot k

end Rep

namespace groupCohomology

open Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- Positive-degree cohomology of a representation coinduced from the trivial subgroup vanishes
(Shapiro's lemma, Milne II 1.11). -/
theorem isZero_coindBot_succ (X : Type u) [AddCommGroup X] [Module k X] (n : ℕ) :
    IsZero (groupCohomology (coindBot k G X) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton (trivial k (⊥ : Subgroup G) X) n).of_iso
    (coindIso (trivial k (⊥ : Subgroup G) X) (n + 1))

/-- Positive-degree cohomology of the restriction to a subgroup of a representation coinduced
from the trivial subgroup vanishes. -/
theorem isZero_res_coindBot_succ (S : Subgroup G) (X : Type u) [AddCommGroup X] [Module k X]
    (n : ℕ) : IsZero (groupCohomology (res S.subtype (coindBot k G X)) (n + 1)) :=
  (isZero_coindBot_succ (G := S) (G ⧸ S → X) n).of_iso
    ((functor k S (n + 1)).mapIso (resCoindBotIso S X))

end groupCohomology

namespace groupHomology

open Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- Positive-degree homology of a representation induced from the trivial subgroup vanishes
(Shapiro's lemma). -/
theorem isZero_indBot_succ (X : Type u) [AddCommGroup X] [Module k X] (n : ℕ) :
    IsZero (groupHomology (indBot k G X) (n + 1)) := by
  classical
  exact (isZero_groupHomology_succ_of_subsingleton (trivial k (⊥ : Subgroup G) X) n).of_iso
    (indIso (⊥ : Subgroup G) (trivial k (⊥ : Subgroup G) X) (n + 1))

end groupHomology

namespace TauCeti.TateCohomology

open Rep

variable {k G : Type u} [CommRing k] [Group G]

section Fintype

variable [Fintype G] (X : Type u) [AddCommGroup X] [Module k X]

/-- Degree-zero Tate cohomology of a representation coinduced from the trivial subgroup vanishes:
every invariant function `G → X` is constant, hence the norm of the function supported at `1`
(Milne II 3.1, case `r = 0`). -/
theorem isZero_coindBot_zero : IsZero (tateCohomology (coindBot k G X) 0) := by
  classical
  have : Subsingleton (tateCohomology (coindBot k G X) 0) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    induction x using H0_induction_on with
    | h y =>
      rw [H0π_eq_zero_iff, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.mem_range]
      -- An invariant function is constant, with value `c := y 1`.
      have hconst : ∀ h : G, (y.1).1 h = (y.1).1 1 := fun h ↦ by
        have h1 : (((coindBot k G X).ρ h) y.1).1 1 = (y.1).1 (1 * h) := rfl
        rw [y.2 h, one_mul] at h1
        exact h1.symm
      -- The function supported at `1` with value `c` has norm the constant function `c`.
      refine ⟨(coindBotEquivPi k G X).symm fun h ↦ if h = 1 then (y.1).1 1 else 0, ?_⟩
      refine Subtype.ext (funext fun h ↦ ?_)
      have hval : ∀ g : G, (((coindBot k G X).ρ g)
          ((coindBotEquivPi k G X).symm fun h ↦ if h = 1 then (y.1).1 1 else 0)).1 h =
            if h * g = 1 then (y.1).1 1 else 0 := fun g ↦ rfl
      rw [hconst h]
      simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
        hval]
      rw [Finset.sum_eq_single h⁻¹
        (fun g _ hg ↦ ite_eq_right fun H ↦ hg (mul_eq_one_iff_inv_eq.1 H).symm)
        (fun H ↦ (H (Finset.mem_univ _)).elim)]
      simp
  exact ModuleCat.isZero_of_subsingleton _

/-- Degree `-1` Tate cohomology of a representation coinduced from the trivial subgroup vanishes:
a function `G → X` with vanishing norm, i.e. `∑ g, f g = 0`, lies in the augmentation submodule
(Milne II 3.1, case `r = -1`). -/
theorem isZero_coindBot_negOne : IsZero (tateCohomology (coindBot k G X) (-1)) := by
  classical
  have : Subsingleton (tateCohomology (coindBot k G X) (-1)) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    induction x using HNegOne_induction_on with
    | h y =>
      rw [HNegOneπ_eq_zero_iff, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.subtype_apply]
      -- The point function at `1` with value `x`; `ρ g⁻¹` moves it to the point function at `g`.
      set δ : X → coindBot k G X :=
        fun x ↦ (coindBotEquivPi k G X).symm fun h ↦ if h = 1 then x else 0 with hδ
      clear_value δ
      have hδval : ∀ (h : G) (x : X), (δ x).1 h = if h = 1 then x else 0 := fun h x ↦ by
        rw [hδ]
        rfl
      have hδ_apply : ∀ (g h : G) (x : X), (((coindBot k G X).ρ g) (δ x)).1 h =
          if h * g = 1 then x else 0 := fun g h x ↦ by
        rw [hδ]
        rfl
      -- The norm of `y` vanishes, so the values of `y` sum to zero.
      have hsum : ∑ g : G, (y.1).1 g = 0 := by
        have hval : ∀ c : G, (((coindBot k G X).ρ c) y.1).1 1 = (y.1).1 c := fun c ↦ by
          change (y.1).1 (1 * c) = _
          rw [one_mul]
        have h0 := congrArg (fun f : coindBot k G X ↦ f.1 1) y.2
        simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
          hval, ZeroMemClass.coe_zero, Pi.zero_apply] at h0
        exact h0
      -- `y` is the sum over `g` of `ρ g⁻¹ (δ (y g)) - δ (y g)`, each a generator of the
      -- augmentation submodule.
      have hdecomp : y.1 =
          ∑ g : G, (((coindBot k G X).ρ g⁻¹) (δ ((y.1).1 g)) - δ ((y.1).1 g)) := by
        refine Subtype.ext (funext fun h ↦ ?_)
        simp only [Submodule.coe_sum, Submodule.coe_sub, Finset.sum_apply, Pi.sub_apply,
          hδ_apply, hδval, Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single h (fun g _ hg ↦ ite_eq_right fun H ↦ hg (by
          simpa [eq_comm] using mul_inv_eq_one.1 H)) (fun H ↦ (H (Finset.mem_univ _)).elim)]
        by_cases hh : h = 1
        · subst hh
          simp [hsum]
        · simp [hh]
      rw [hdecomp]
      exact Submodule.sum_mem _ fun g _ ↦ Representation.Coinvariants.sub_mem_ker _ _
  exact ModuleCat.isZero_of_subsingleton _

/-- For a finite group, all Tate cohomology of a representation coinduced from the trivial
subgroup vanishes (Milne II 3.1). -/
theorem isZero_coindBot (n : ℤ) : IsZero (tateCohomology (coindBot k G X) n) :=
  match n with
  | .ofNat (n + 1) =>
    (groupCohomology.isZero_coindBot_succ X n).of_iso
      ((_root_.TateCohomology.isoGroupCohomology (n + 1)).app (coindBot k G X))
  | 0 => isZero_coindBot_zero X
  | .negSucc 0 => isZero_coindBot_negOne X
  | .negSucc (n + 1) =>
    ((groupHomology.isZero_indBot_succ X n).of_iso
      ((groupHomology.functor k G (n + 1)).mapIso (indBotIsoCoindBot X).symm)).of_iso
      ((_root_.TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1) rfl).app
        (coindBot k G X))

/-- For a finite group, all Tate cohomology of a representation induced from the trivial
subgroup vanishes (Milne II 3.1). -/
theorem isZero_indBot (n : ℤ) : IsZero (tateCohomology (indBot k G X) n) :=
  (isZero_coindBot X n).of_iso ((tateCohomologyFunctor n).mapIso (indBotIsoCoindBot X))

end Fintype

/-- For a finite subgroup `S` of a group `G`, all Tate cohomology of the restriction to `S` of a
representation coinduced from the trivial subgroup of `G` vanishes. -/
theorem isZero_res_coindBot (S : Subgroup G) [Fintype S] (X : Type u) [AddCommGroup X]
    [Module k X] (n : ℤ) : IsZero (tateCohomology (res S.subtype (coindBot k G X)) n) :=
  (isZero_coindBot (G := S) (G ⧸ S → X) n).of_iso
    ((tateCohomologyFunctor n).mapIso (resCoindBotIso S X))

/-- For a subgroup `S` of a finite group `G`, all Tate cohomology of the restriction to `S` of a
representation induced from the trivial subgroup of `G` vanishes. -/
theorem isZero_res_indBot [Finite G] (S : Subgroup G) [Fintype S] (X : Type u) [AddCommGroup X]
    [Module k X] (n : ℤ) : IsZero (tateCohomology (res S.subtype (indBot k G X)) n) :=
  (isZero_res_coindBot S X n).of_iso
    ((tateCohomologyFunctor n).mapIso ((resFunctor S.subtype).mapIso (indBotIsoCoindBot X)))

/-- For a subgroup `S` of a finite group `G`, all Tate cohomology of the restriction to `S` of the
left regular representation `k[G]` vanishes. -/
theorem isZero_res_leftRegular [Finite G] (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype (leftRegular k G)) n) :=
  (isZero_res_coindBot S k n).of_iso
    ((tateCohomologyFunctor n).mapIso ((resFunctor S.subtype).mapIso leftRegularIsoCoindBot))

end TauCeti.TateCohomology
