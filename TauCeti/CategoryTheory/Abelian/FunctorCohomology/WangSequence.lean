/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Line
import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory
import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Basic

/-!
# The Wang sequence and a criterion for lines

Let `Y` be a functor on `C × Bℕ`, where `Bℕ = SingleObj (Multiplicative ℕ)`, with restriction `Y₀`
to `C` and with `γ : Y₀ ⟶ Y₀` the action of `1 ∈ ℕ` (`CategoryTheory.Functor.actionOne`). The
*Wang sequence* (`CategoryTheory.Functor.wangSequence`)

`0 ⟶ ℤ[Y₀ × ℕ] ⟶ ℤ[Y₀ × ℕ] ⟶ ℤ[Y] ⟶ 0`,

with maps `(x, k) ↦ (γ x, k) - (x, k + 1)` and `(x, k) ↦ γᵏ x`, is short exact
(`CategoryTheory.Functor.wangSequence_shortExact`): at every object it splits, by an explicit
contracting homotopy. As the projection `Y₀ × ℕ ⟶ Y₀` is a line
(`CategoryTheory.isLineFor_prodNatFst`), its long exact sequence computes the cohomology of `Y` on
`C × Bℕ` from that of `Y₀` on `C` and the action of `γ`, as a two-term Koszul complex computes the
continuous cohomology of `ℤ_p`.

This gives a criterion for lines (`CategoryTheory.IsLineFor.of_koszulExact`). Suppose that `Y₀` is
`Hom(E, ψ -)` for a functor `ψ : C ⥤ C'`, that `γ` is precomposition with `g : E ⟶ E`, and that
`q : Y ⟶ Hom(A, -)` is induced by `i : ψ A ⟶ E`. If `F'` is acyclic at `E` along `ψ` and `F'(i)`,
`F'(g)` are *Koszul-exact* (`Function.KoszulExact`: `F'(i)` is injective, the fixed points of
`F'(g)` lie in its range, and `F'(g) - 1` is onto), then `ℤ[Y]` has the cohomology of `Hom(A, -)`
with coefficients `F' ∘ ψ`, namely `F'(ψ A)` in degree `0` and nothing above, and `q` is a line.

## Main definitions

* `Function.KoszulExact i g`: `i` and `g` are Koszul-exact.
* `CategoryTheory.Functor.actionOne Y`: the action `γ` of `1 ∈ ℕ` on the restriction of `Y` to `C`;
  `CategoryTheory.Functor.prodNatShift X` and `CategoryTheory.Functor.prodNatAct Y`: the
  translation of `X × ℕ` and the map `(x, k) ↦ γᵏ x`.
* `CategoryTheory.Functor.wangSequence Y`: the Wang sequence of `Y`.

## Main results

* `CategoryTheory.Functor.wangSequence_shortExact`: the Wang sequence is short exact.
* `CategoryTheory.IsLineFor.of_koszulExact`: the criterion for lines.

## References

* G. Faltings, *p-adic Hodge theory*, J. Amer. Math. Soc. 1 (1988); P. Scholze, *p-adic Hodge
  theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), Lemmas 4.5 and 5.5; B. Bhatt,
  M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Publ. Math. IHÉS 128 (2018), Lemma 7.3;
  the Stacks Project, Tag 0EBS: Koszul complexes computing the continuous cohomology of `ℤ_p^d`,
  which the Wang sequence replaces here one coordinate and one endomorphism at a time.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicComparison/ToricTower.lean` (declarations
  `New.Variety.TimesBNat.shortExact_wangComplex`, `New.Variety.KoszulExact`,
  `New.Variety.IsLine.of_acyclic`); Apache 2.0, Copyright 2026 Anthropic, PBC. The statements are
  adapted from these declarations, and the proof of the criterion follows the same route.
-/

public section

open CategoryTheory Limits Abelian
open scoped CategoryTheory.Prod

universe t t' t'' w v u v' u'

local notation "Bℕ" => SingleObj (Multiplicative ℕ)
local notation "⋆" => SingleObj.star (Multiplicative ℕ)

/-- A map `i : X₁ → X₂` and a self-map `g` of the additive group `X₂` are *Koszul-exact* if `i` is
injective, every fixed point of `g` lies in the range of `i`, and `z ↦ g z - z` is onto. When the
range of `i` consists of fixed points of `g`, this says that the sequence
`0 → X₁ → X₂ → X₂ → 0` with maps `i` and `g - 1` is exact. -/
structure Function.KoszulExact {X₁ X₂ : Type*} [AddGroup X₂] (i : X₁ → X₂) (g : X₂ → X₂) :
    Prop where
  injective : Function.Injective i
  mem_range_of_apply_eq {z : X₂} : g z = z → z ∈ Set.range i
  surjective_sub : Function.Surjective fun z ↦ g z - z

namespace CategoryTheory

/-! ### The objectwise Wang sequence -/

section Objectwise

/-! Throughout, `γ : Z → Z` is a map and `act k : Z → Z` stands for its `k`-th iterate, in the form
in which a functor on `C × Bℕ` gives it. -/

variable {Z : Type*} (γ : Z → Z) (act : ℕ → Z → Z)

/-- Up to sign, the contracting homotopy of the Wang sequence of `γ`: it sends the generator of
`(x, k)` to `Σ_{j < k} (γʲ x, k - 1 - j)`. -/
private noncomputable def wangHomotopyAux : ℕ → Z → FreeAddCommGroup (Z × ℕ)
  | 0, _ => 0
  | k + 1, x => FreeAddCommGroup.of (x, k) + wangHomotopyAux k (γ x)

/-- The contracting homotopy of the Wang sequence, as a group homomorphism. -/
private noncomputable def wangHomotopy : FreeAddCommGroup (Z × ℕ) →+ FreeAddCommGroup (Z × ℕ) :=
  FreeAddCommGroup.lift fun p ↦ wangHomotopyAux γ p.2 p.1

/-- The differential `(x, k) ↦ (γ x, k) - (x, k + 1)` of the Wang sequence. -/
private noncomputable def wangDiff : FreeAddCommGroup (Z × ℕ) →+ FreeAddCommGroup (Z × ℕ) :=
  FreeAddCommGroup.map (fun p ↦ (γ p.1, p.2)) - FreeAddCommGroup.map (fun p ↦ (p.1, p.2 + 1))

/-- The map `(x, k) ↦ γᵏ x` of the Wang sequence. -/
private noncomputable def wangAct : FreeAddCommGroup (Z × ℕ) →+ FreeAddCommGroup Z :=
  FreeAddCommGroup.map fun p ↦ act p.2 p.1

private lemma wangHomotopy_of (x : Z) (k : ℕ) :
    wangHomotopy γ (FreeAddCommGroup.of (x, k)) = wangHomotopyAux γ k x :=
  FreeAddCommGroup.lift_apply_of _ _

private lemma wangDiff_of (x : Z) (k : ℕ) :
    wangDiff γ (FreeAddCommGroup.of (x, k)) =
      FreeAddCommGroup.of (γ x, k) - FreeAddCommGroup.of (x, k + 1) := by
  simp [wangDiff]

private lemma wangAct_of (x : Z) (k : ℕ) :
    wangAct act (FreeAddCommGroup.of (x, k)) = FreeAddCommGroup.of (act k x) :=
  FreeAddCommGroup.map_of_apply _

private lemma wangHomotopy_wangDiff (z : FreeAddCommGroup (Z × ℕ)) :
    wangHomotopy γ (wangDiff γ z) = -z := by
  have h : (wangHomotopy γ).comp (wangDiff γ) = -AddMonoidHom.id _ := by
    ext ⟨x, k⟩
    simp [wangDiff_of, wangHomotopy_of, wangHomotopyAux]
  exact congr($h z)

variable {γ act}

private lemma wangDiff_wangHomotopy (h₀ : ∀ x, act 0 x = x)
    (hs : ∀ k x, act (k + 1) x = act k (γ x)) (z : FreeAddCommGroup (Z × ℕ)) :
    wangDiff γ (wangHomotopy γ z) =
      FreeAddCommGroup.map (fun x ↦ (x, 0)) (wangAct act z) - z := by
  have h : (wangDiff γ).comp (wangHomotopy γ) =
      (FreeAddCommGroup.map fun x ↦ (x, 0)).comp (wangAct act) - AddMonoidHom.id _ := by
    ext ⟨x, k⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, wangHomotopy_of, wangAct_of,
      AddMonoidHom.sub_apply, AddMonoidHom.id_apply, FreeAddCommGroup.map_of_apply]
    induction k generalizing x with
    | zero => simp [wangHomotopyAux, h₀]
    | succ k ih => rw [wangHomotopyAux, map_add, ih, wangDiff_of, hs]; abel
  exact congr($h z)

private lemma wangAct_wangDiff (hs : ∀ k x, act (k + 1) x = act k (γ x))
    (z : FreeAddCommGroup (Z × ℕ)) : wangAct act (wangDiff γ z) = 0 := by
  have h : (wangAct act).comp (wangDiff γ) = 0 := by
    ext ⟨x, k⟩
    simp [wangDiff_of, wangAct_of, hs]
  exact congr($h z)

/-- The objectwise Wang sequence: the differential is injective. -/
private lemma wangDiff_injective : Function.Injective (wangDiff γ) :=
  (injective_iff_map_eq_zero _).2 fun z hz ↦ by
    simpa [hz] using (wangHomotopy_wangDiff γ z).symm

/-- The objectwise Wang sequence is exact in the middle. -/
private lemma wangDiff_exact (h₀ : ∀ x, act 0 x = x) (hs : ∀ k x, act (k + 1) x = act k (γ x)) :
    Function.Exact (wangDiff γ) (wangAct act) := fun z ↦
  ⟨fun hz ↦ ⟨-wangHomotopy γ z, by simp [wangDiff_wangHomotopy h₀ hs, hz]⟩,
    by rintro ⟨y, rfl⟩; exact wangAct_wangDiff hs y⟩

/-- The objectwise Wang sequence: the map `(x, k) ↦ γᵏ x` is onto. -/
private lemma wangAct_surjective (h₀ : ∀ x, act 0 x = x) : Function.Surjective (wangAct act) := by
  have h : (wangAct act).comp (FreeAddCommGroup.map fun z ↦ (z, 0)) = AddMonoidHom.id _ := by
    ext x
    simp [wangAct_of, h₀]
  exact fun z ↦ ⟨_, congr($h z)⟩

end Objectwise

/-! ### The Wang sequence of a functor on `C × Bℕ` -/

variable {C : Type u} [Category.{v} C]

/-- The action of `1 ∈ ℕ` on a functor `Y` on `C × Bℕ`, as an endomorphism `γ` of the restriction
of `Y` to `C`. -/
@[expose, simps]
def Functor.actionOne {D : Type*} [Category* D] (Y : C × Bℕ ⥤ D) :
    Prod.sectL C ⋆ ⋙ Y ⟶ Prod.sectL C ⋆ ⋙ Y where
  app c := Y.map (𝟙 c ×ₘ Multiplicative.ofAdd 1)
  naturality c d f := by
    have h : (f ×ₘ 𝟙 ⋆) ≫ (𝟙 d ×ₘ (Multiplicative.ofAdd 1 : ⋆ ⟶ ⋆)) =
        (𝟙 c ×ₘ (Multiplicative.ofAdd 1 : ⋆ ⟶ ⋆)) ≫ (f ×ₘ 𝟙 ⋆) :=
      Prod.hom_ext (by simp) (by simp)
    exact (Y.map_comp _ _).symm.trans ((congrArg Y.map h).trans (Y.map_comp _ _))

/-- The translation `(x, k) ↦ (x, k + 1)` of `X × ℕ`. -/
@[expose]
def Functor.prodNatShift (X : C ⥤ Type w) : (prodNat C).obj X ⟶ (prodNat C).obj X where
  app _ := ↾fun p ↦ (p.1, p.2 + 1)
  naturality c d f := by
    ext ⟨x, k⟩
    exact Prod.ext rfl (add_right_comm k _ 1)

/-- The translation sends `(x, k)` to `(x, k + 1)`. -/
lemma Functor.prodNatShift_app_apply (X : C ⥤ Type w) (c : C × Bℕ) (x : X.obj c.1) (k : ℕ) :
    X.prodNatShift.app c ((x, k) : ((prodNat C).obj X).obj c) =
      ((x, k + 1) : ((prodNat C).obj X).obj c) :=
  rfl

/-- `γᵏ` is the action of `k ∈ ℕ`: `γᵏ⁺¹ x = γᵏ (γ x)`. -/
private lemma map_ofAdd_succ_apply (Y : C × Bℕ ⥤ Type w) (c : C) (a : Bℕ) (k : ℕ)
    (x : Y.obj (c, ⋆)) :
    Y.map (𝟙 c ×ₘ Multiplicative.ofAdd (k + 1) : (c, ⋆) ⟶ (c, a)) x =
      Y.map (𝟙 c ×ₘ Multiplicative.ofAdd k : (c, ⋆) ⟶ (c, a))
        (Y.map (𝟙 c ×ₘ Multiplicative.ofAdd 1 : (c, ⋆) ⟶ (c, ⋆)) x) := by
  rw [← Functor.map_comp_apply]
  -- In `Bℕ`, composition is multiplication in `Multiplicative ℕ`, in the opposite order.
  exact congrArg (fun g ↦ Y.map g x) (Prod.hom_ext (by simp) (ofAdd_add k 1))

/-- For `Y` on `C × Bℕ` with restriction `Y₀` to `C`, the map `Y₀ × ℕ ⟶ Y`, `(x, k) ↦ γᵏ x`. -/
@[expose]
def Functor.prodNatAct (Y : C × Bℕ ⥤ Type w) :
    (prodNat C).obj (Prod.sectL C ⋆ ⋙ Y) ⟶ Y where
  app c := ↾fun p ↦ Y.map (𝟙 c.1 ×ₘ (Multiplicative.ofAdd p.2 : ⋆ ⟶ c.2)) p.1
  naturality c d f := by
    ext ⟨x, k⟩
    -- In `Bℕ`, composition is multiplication in `Multiplicative ℕ`, in the opposite order.
    have h : (f.1 ×ₘ 𝟙 ⋆) ≫ (𝟙 d.1 ×ₘ
        (Multiplicative.ofAdd (k + Multiplicative.toAdd f.2) : ⋆ ⟶ d.2)) =
        (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2)) ≫ f :=
      Prod.hom_ext (by simp) ((mul_one _).trans ((ofAdd_add _ _).trans (mul_comm _ _)))
    exact (Functor.map_comp_apply Y _ _ x).symm.trans
      ((congrArg (fun g ↦ Y.map g x) h).trans (Functor.map_comp_apply Y _ _ x))

/-- The action map sends `(x, k)` to `γᵏ x`. -/
lemma Functor.prodNatAct_app_apply (Y : C × Bℕ ⥤ Type w) (c : C × Bℕ)
    (x : Y.obj (c.1, ⋆)) (k : ℕ) :
    Y.prodNatAct.app c
        ((x, k) : ((prodNat C).obj (Prod.sectL C ⋆ ⋙ Y)).obj c) =
      Y.map (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2)) x :=
  rfl

/-- `γ` followed by the action map is the translation followed by the action map:
`γᵏ (γ x) = γᵏ⁺¹ x`. -/
lemma Functor.prodNat_map_actionOne_comp_prodNatAct (Y : C × Bℕ ⥤ Type w) :
    (prodNat C).map Y.actionOne ≫ Y.prodNatAct = Functor.prodNatShift _ ≫ Y.prodNatAct := by
  ext c ⟨x, k⟩
  exact (map_ofAdd_succ_apply Y c.1 c.2 k x).symm

/-- The **Wang sequence** `0 ⟶ ℤ[Y₀ × ℕ] ⟶ ℤ[Y₀ × ℕ] ⟶ ℤ[Y] ⟶ 0` of a functor `Y` on `C × Bℕ`
with restriction `Y₀` to `C`: the first map sends `(x, k)` to `(γ x, k) - (x, k + 1)` and the
second sends `(x, k)` to `γᵏ x`. It is short exact (`Functor.wangSequence_shortExact`). -/
@[expose, simps]
noncomputable def Functor.wangSequence (Y : C × Bℕ ⥤ Type w) :
    ShortComplex (C × Bℕ ⥤ AddCommGrpCat.{w}) where
  X₁ := (prodNat C).obj (Prod.sectL C ⋆ ⋙ Y) ⋙ AddCommGrpCat.free
  X₂ := (prodNat C).obj (Prod.sectL C ⋆ ⋙ Y) ⋙ AddCommGrpCat.free
  X₃ := Y ⋙ AddCommGrpCat.free
  f := Functor.whiskerRight ((prodNat C).map Y.actionOne) AddCommGrpCat.free -
    Functor.whiskerRight (Functor.prodNatShift _) AddCommGrpCat.free
  g := Functor.whiskerRight Y.prodNatAct AddCommGrpCat.free
  zero := by
    rw [Preadditive.sub_comp, ← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp,
      Functor.prodNat_map_actionOne_comp_prodNatAct, sub_self]

/-- **The Wang sequence is short exact.** At every object it splits, by an explicit contracting
homotopy. -/
theorem Functor.wangSequence_shortExact (Y : C × Bℕ ⥤ Type w) : Y.wangSequence.ShortExact := by
  have h₀ (c : C) (x : Y.obj (c, ⋆)) :
      Y.map (𝟙 c ×ₘ Multiplicative.ofAdd 0 : (c, ⋆) ⟶ (c, ⋆)) x = x :=
    Functor.map_id_apply Y (c, ⋆) x
  refine ShortComplex.shortExact_of_forall_function_exact (fun ⟨c, ⟨⟩⟩ ↦ ?_)
    (fun ⟨c, ⟨⟩⟩ ↦ ?_) (fun ⟨c, ⟨⟩⟩ ↦ ?_)
  · exact wangDiff_injective
      (γ := fun x ↦ Y.map (𝟙 c ×ₘ Multiplicative.ofAdd 1 : (c, ⋆) ⟶ (c, ⋆)) x)
  · exact wangDiff_exact (γ := fun x ↦ Y.map (𝟙 c ×ₘ Multiplicative.ofAdd 1 : (c, ⋆) ⟶ (c, ⋆)) x)
      (act := fun k x ↦ Y.map (𝟙 c ×ₘ Multiplicative.ofAdd k : (c, ⋆) ⟶ (c, ⋆)) x)
      (h₀ c) (map_ofAdd_succ_apply Y c _)
  · exact wangAct_surjective
      (act := fun k x ↦ Y.map (𝟙 c ×ₘ Multiplicative.ofAdd k : (c, ⋆) ⟶ (c, ⋆)) x) (h₀ c)

/-! ### A criterion for lines -/

section Criterion

variable {C' : Type u'} [Category.{v'} C']

/-- The endomorphism of a functor `R` corepresented by `E` induced by `g : E ⟶ E`: precomposition
with `g`. -/
private def corepEndo {R : C' ⥤ Type w} {E : C'} (hR : R.CorepresentableBy E) (g : E ⟶ E) :
    R ⟶ R where
  app _ := ↾fun r ↦ hR.homEquiv (g ≫ hR.homEquiv.symm r)
  naturality X X' f := by
    ext r
    exact (congrArg hR.homEquiv ((congrArg (g ≫ ·) (hR.homEquiv_symm_comp r f).symm).trans
      (Category.assoc _ _ _).symm)).trans (hR.homEquiv_comp f _)

private lemma corepEndo_app_apply {R : C' ⥤ Type w} {E : C'} (hR : R.CorepresentableBy E)
    (g : E ⟶ E) (X : C') (r : R.obj X) :
    (corepEndo hR g).app X r = hR.homEquiv (g ≫ hR.homEquiv.symm r) :=
  rfl

/-- Under the additive Yoneda lemma, precomposition with `ℤ[corepEndo hR g]` is `F'.map g`. -/
private lemma freeHomAddEquiv_corepEndo {R : C' ⥤ Type w} {E : C'} (hR : R.CorepresentableBy E)
    (g : E ⟶ E) (F' : C' ⥤ AddCommGrpCat.{w}) (χ : R ⋙ AddCommGrpCat.free ⟶ F') :
    hR.freeHomAddEquiv F' (Functor.whiskerRight (corepEndo hR g) AddCommGrpCat.free ≫ χ) =
      F'.map g (hR.freeHomAddEquiv F' χ) := by
  rw [Functor.CorepresentableBy.freeHomAddEquiv_apply,
    Functor.CorepresentableBy.freeHomAddEquiv_apply]
  -- Both sides evaluate `χ` at the generator of `g`, seen as an element of `R E`.
  have h : (corepEndo hR g).app E (hR.homEquiv (𝟙 E)) = R.map g (hR.homEquiv (𝟙 E)) := by
    rw [corepEndo_app_apply, ← hR.homEquiv_comp, Equiv.symm_apply_apply, Category.comp_id,
      Category.id_comp]
  exact (congrArg (χ.app E) ((FreeAddCommGroup.map_of_apply _).trans
    ((congrArg FreeAddCommGroup.of h).trans (FreeAddCommGroup.map_of_apply _).symm))).trans
    (NatTrans.naturality_apply χ g _)

variable [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C × Bℕ ⥤ AddCommGrpCat.{w})]
  [HasExt.{t''} (C' ⥤ AddCommGrpCat.{w})] {ψ : C ⥤ C'} {F' : C' ⥤ AddCommGrpCat.{w}}
  {R : C' ⥤ Type w} {Y : C × Bℕ ⥤ Type w}

variable (ψ F') in
/-- Restriction along `ψ`, `Extⁿ(ℤ[R], F') ⟶ Extⁿ(ℤ[R ∘ ψ], F' ∘ ψ)`. -/
private noncomputable abbrev wangRes (R : C' ⥤ Type w) (n : ℕ)
    (y : Ext.{t''} (R ⋙ AddCommGrpCat.free) F' n) :
    Ext.{t} (ψ ⋙ R ⋙ AddCommGrpCat.free) (ψ ⋙ F') n :=
  y.mapExactFunctor ((Functor.whiskeringLeft C C' AddCommGrpCat.{w}).obj ψ)

omit [HasExt.{t'} (C × Bℕ ⥤ AddCommGrpCat.{w})] in
/-- Restriction along `ψ` is the comparison map of `(ψ, 𝟙)` along `𝟙`. -/
private lemma extComparison_id_id_eq_wangRes (R : C' ⥤ Type w) (n : ℕ) :
    ⇑(Functor.extComparison.{t'', t} (N := R ⋙ AddCommGrpCat.free) ψ (𝟙 (ψ ⋙ F'))
      (𝟙 (ψ ⋙ R ⋙ AddCommGrpCat.free)) n) = wangRes ψ F' R n := by
  ext y
  rw [Functor.extComparison_apply]
  exact (Ext.mk₀_id_comp _).trans (Ext.comp_mk₀_id _)

variable (ψ F') in
/-- The line `Y₀ × ℕ ⟶ Y₀`: `Extⁿ(ℤ[Y₀], F' ∘ ψ) ⟶ Extⁿ(ℤ[Y₀ × ℕ], F' ∘ ψ ∘ pr)`. -/
private noncomputable abbrev wangLine (Y : C × Bℕ ⥤ Type w) (n : ℕ) :=
  Functor.extComparison.{t, t'} (N := Prod.sectL C ⋆ ⋙ Y ⋙ AddCommGrpCat.free)
    (Prod.fst C Bℕ) (𝟙 (Prod.fst C Bℕ ⋙ ψ ⋙ F'))
    (Functor.whiskerRight (Prod.sectL C ⋆ ⋙ Y).prodNatFst AddCommGrpCat.free) n

/-- The composite `Extⁿ(ℤ[R], F') ⟶ Extⁿ(ℤ[Y₀ × ℕ], F' ∘ ψ ∘ pr)` of restriction along `ψ`,
pull-back along `e : Y₀ ≅ R ∘ ψ` and the line `Y₀ × ℕ ⟶ Y₀`. -/
private noncomputable def wangTheta (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (n : ℕ) :
    Ext.{t''} (R ⋙ AddCommGrpCat.free) F' n →+
      Ext.{t'} ((prodNat C).obj (Prod.sectL C ⋆ ⋙ Y) ⋙ AddCommGrpCat.free)
        (Prod.fst C Bℕ ⋙ ψ ⋙ F') n :=
  (wangLine ψ F' Y n).comp
    (((Ext.mk₀ (Functor.whiskerRight e.hom AddCommGrpCat.free)).precomp (ψ ⋙ F')
      (zero_add n)).comp
        (((Functor.whiskeringLeft C C' AddCommGrpCat.{w}).obj ψ).mapExtAddHom _ _ n))

private lemma wangTheta_apply (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (n : ℕ)
    (y : Ext.{t''} (R ⋙ AddCommGrpCat.free) F' n) :
    wangTheta e n y = wangLine ψ F' Y n
      ((Ext.mk₀ (Functor.whiskerRight e.hom AddCommGrpCat.free)).comp (wangRes ψ F' R n y)
        (zero_add n)) :=
  rfl

private lemma wangTheta_bijective (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R)
    (hF' : Functor.IsExtComparisonBijective.{t'', t} (N := R ⋙ AddCommGrpCat.free) ψ
      (𝟙 (ψ ⋙ F')) (𝟙 (ψ ⋙ R ⋙ AddCommGrpCat.free))) (n : ℕ) :
    Function.Bijective (wangTheta (F' := F') e n) := by
  rw [show ⇑(wangTheta (F' := F') e n) = _ from funext (wangTheta_apply e n)]
  have he : Function.Bijective fun y : Ext.{t} (ψ ⋙ R ⋙ AddCommGrpCat.free) (ψ ⋙ F') n ↦
      (Ext.mk₀ (Functor.whiskerRight e.hom AddCommGrpCat.free)).comp y (zero_add n) :=
    Function.bijective_iff_has_inverse.2
      ⟨fun y ↦ (Ext.mk₀ (Functor.whiskerRight e.inv AddCommGrpCat.free)).comp y (zero_add n),
        fun y ↦ by simp [Ext.mk₀_comp_mk₀_assoc, ← Functor.whiskerRight_comp],
        fun y ↦ by simp [Ext.mk₀_comp_mk₀_assoc, ← Functor.whiskerRight_comp]⟩
  have hres := (Functor.isExtComparisonBijective_iff _ _ _).1 hF' n
  rw [extComparison_id_id_eq_wangRes] at hres
  exact ((isLineFor_iff _ _).1 (isLineFor_prodNatFst _ _) n).comp (he.comp hres)

omit [HasExt.{t''} (C' ⥤ AddCommGrpCat.{w})] in
/-- The translation of `Y₀ × ℕ` acts trivially through the line `Y₀ × ℕ ⟶ Y₀`. -/
private lemma mk₀_prodNatShift_comp_wangLine {n : ℕ}
    (w : Ext.{t} (Prod.sectL C ⋆ ⋙ Y ⋙ AddCommGrpCat.free) (ψ ⋙ F') n) :
    (Ext.mk₀ (Functor.whiskerRight (Functor.prodNatShift (Prod.sectL C ⋆ ⋙ Y))
      AddCommGrpCat.free)).comp (wangLine ψ F' Y n w) (zero_add n) = wangLine ψ F' Y n w := by
  have h : Functor.prodNatShift (Prod.sectL C ⋆ ⋙ Y) ≫ (Prod.sectL C ⋆ ⋙ Y).prodNatFst =
      (Prod.sectL C ⋆ ⋙ Y).prodNatFst :=
    NatTrans.ext (funext fun _ ↦ rfl)
  rw [Functor.mk₀_comp_extComparison (γ := 𝟙 (Prod.sectL C ⋆ ⋙ Y ⋙ AddCommGrpCat.free))
    (b := Functor.whiskerRight (Prod.sectL C ⋆ ⋙ Y).prodNatFst AddCommGrpCat.free),
    Ext.mk₀_id_comp]
  rw [← Functor.whiskerRight_comp, h, Functor.whiskerLeft_id']
  exact (Category.comp_id _).symm

omit [HasExt.{t''} (C' ⥤ AddCommGrpCat.{w})] in
/-- The action of `1 ∈ ℕ` on `Y₀ × ℕ` corresponds, through the line `Y₀ × ℕ ⟶ Y₀`, to `γ`. -/
private lemma mk₀_map_actionOne_comp_wangLine {n : ℕ}
    (w : Ext.{t} (Prod.sectL C ⋆ ⋙ Y ⋙ AddCommGrpCat.free) (ψ ⋙ F') n) :
    (Ext.mk₀ (Functor.whiskerRight ((prodNat C).map Y.actionOne) AddCommGrpCat.free)).comp
        (wangLine ψ F' Y n w) (zero_add n) =
      wangLine ψ F' Y n
        ((Ext.mk₀ (Functor.whiskerRight Y.actionOne AddCommGrpCat.free)).comp w (zero_add n)) := by
  have h : (prodNat C).map Y.actionOne ≫ (Prod.sectL C ⋆ ⋙ Y).prodNatFst =
      (Prod.sectL C ⋆ ⋙ Y).prodNatFst ≫ (Prod.fst C Bℕ).whiskerLeft Y.actionOne :=
    NatTrans.ext (funext fun _ ↦ rfl)
  refine Functor.mk₀_comp_extComparison _ _ ?_ w
  rw [← Functor.whiskerRight_comp, h, Functor.whiskerRight_comp]
  rfl

omit [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C × Bℕ ⥤ AddCommGrpCat.{w})]
  [HasExt.{t''} (C' ⥤ AddCommGrpCat.{w})] in
/-- Under `e`, the action `γ` of `1 ∈ ℕ` is precomposition with `g`. -/
private lemma actionOne_comp_hom {E : C'} (hR : R.CorepresentableBy E)
    (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (g : E ⟶ E)
    (hg : ∀ (c : C) (y : Y.obj (c, ⋆)), hR.homEquiv.symm (e.hom.app c (Y.actionOne.app c y)) =
      g ≫ hR.homEquiv.symm (e.hom.app c y)) :
    Y.actionOne ≫ e.hom = e.hom ≫ ψ.whiskerLeft (corepEndo hR g) := by
  ext c y
  exact hR.homEquiv.symm_apply_eq.1 (hg c y)

omit [HasExt.{t'} (C × Bℕ ⥤ AddCommGrpCat.{w})] in
/-- Pull-back along `γ` after restriction along `ψ` and pull-back along `e` is restriction along
`ψ` and pull-back along `e` after pull-back along `corepEndo hR g`. -/
private lemma mk₀_actionOne_comp_wangRes {E : C'} (hR : R.CorepresentableBy E)
    (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (g : E ⟶ E)
    (hg : ∀ (c : C) (y : Y.obj (c, ⋆)), hR.homEquiv.symm (e.hom.app c (Y.actionOne.app c y)) =
      g ≫ hR.homEquiv.symm (e.hom.app c y)) {n : ℕ}
    (y : Ext.{t''} (R ⋙ AddCommGrpCat.free) F' n) :
    (Ext.mk₀ (Functor.whiskerRight Y.actionOne AddCommGrpCat.free)).comp
        ((Ext.mk₀ (Functor.whiskerRight e.hom AddCommGrpCat.free)).comp (wangRes ψ F' R n y)
          (zero_add n)) (zero_add n) =
      (Ext.mk₀ (Functor.whiskerRight e.hom AddCommGrpCat.free)).comp
        (wangRes ψ F' R n ((Ext.mk₀ (Functor.whiskerRight (corepEndo hR g)
          AddCommGrpCat.free)).comp y (zero_add n))) (zero_add n) := by
  rw [Ext.mk₀_comp_mk₀_assoc, ← Functor.whiskerRight_comp, actionOne_comp_hom hR e g hg,
    Functor.whiskerRight_comp, ← Ext.mk₀_comp_mk₀_assoc, wangRes, wangRes,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  -- `ℤ[ψ.whiskerLeft ρ]` and `ψ.whiskerLeft ℤ[ρ]` agree by definition.
  rfl

/-- **Pull-back along the Wang differential.** Through `wangTheta`, pull-back along the
differential of the Wang sequence is pull-back along `corepEndo hR g` minus the identity. -/
private lemma mk₀_wangSequence_f_comp_wangTheta {E : C'} (hR : R.CorepresentableBy E)
    (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (g : E ⟶ E)
    (hg : ∀ (c : C) (y : Y.obj (c, ⋆)), hR.homEquiv.symm (e.hom.app c (Y.actionOne.app c y)) =
      g ≫ hR.homEquiv.symm (e.hom.app c y)) {n : ℕ}
    (y : Ext.{t''} (R ⋙ AddCommGrpCat.free) F' n) :
    (Ext.mk₀ Y.wangSequence.f).comp (wangTheta e n y) (zero_add n) =
      wangTheta e n ((Ext.mk₀ (Functor.whiskerRight (corepEndo hR g) AddCommGrpCat.free)).comp y
        (zero_add n)) - wangTheta e n y := by
  -- Unfold the Wang differential, writing out the objects of the Wang sequence.
  change (Ext.mk₀ (Functor.whiskerRight ((prodNat C).map Y.actionOne) AddCommGrpCat.free -
      Functor.whiskerRight (Functor.prodNatShift (Prod.sectL C ⋆ ⋙ Y)) AddCommGrpCat.free)).comp
        (wangTheta e n y) (zero_add n) = _
  rw [Ext.mk₀_sub, Ext.sub_comp, wangTheta_apply, wangTheta_apply, mk₀_prodNatShift_comp_wangLine,
    mk₀_map_actionOne_comp_wangLine, mk₀_actionOne_comp_wangRes hR e g hg]

/-- The restriction `Y₀ ⟶ Q` to `C × {⋆}` of a map `q : Y ⟶ Q` to a functor `Q` on `C`, read on
`C × Bℕ` with `ℕ` acting trivially. -/
private def restrictStar {Q : C ⥤ Type w} (q : Y ⟶ Prod.fst C Bℕ ⋙ Q) :
    Prod.sectL C ⋆ ⋙ Y ⟶ Q where
  app c := q.app (c, ⋆)
  naturality _ _ f := q.naturality (f ×ₘ 𝟙 ⋆)

omit [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C × Bℕ ⥤ AddCommGrpCat.{w})]
  [HasExt.{t''} (C' ⥤ AddCommGrpCat.{w})] in
/-- The map `(x, k) ↦ q (γᵏ x)` from `Y₀ × ℕ` is `(x, k) ↦ q x`: `ℕ` acts trivially on `Q`. -/
private lemma prodNatAct_comp {Q : C ⥤ Type w} (q : Y ⟶ Prod.fst C Bℕ ⋙ Q) :
    Y.prodNatAct ≫ q =
      (Prod.sectL C ⋆ ⋙ Y).prodNatFst ≫ (Prod.fst C Bℕ).whiskerLeft (restrictStar q) := by
  ext c ⟨y, k⟩
  exact (NatTrans.naturality_apply q (𝟙 c.1 ×ₘ (Multiplicative.ofAdd k : ⋆ ⟶ c.2)) y).trans
    (Functor.map_id_apply Q c.1 (q.app (c.1, ⋆) y))

omit [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C × Bℕ ⥤ AddCommGrpCat.{w})]
  [HasExt.{t''} (C' ⥤ AddCommGrpCat.{w})] in
/-- In degree `0`: the element `a` of `F'(ψ A)`, pulled back along `q`, is the element `F'(i) a`
of `F'(E)`, restricted along `ψ` and pulled back along `e`. -/
private lemma whiskerRight_restrictStar_comp {A : C} {E : C'} (hR : R.CorepresentableBy E)
    {Q : C ⥤ Type w} (hQ : Q.CorepresentableBy A) (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R)
    (i : ψ.obj A ⟶ E) (q : Y ⟶ Prod.fst C Bℕ ⋙ Q)
    (hq : ∀ (c : C) (y : Y.obj (c, ⋆)),
      ψ.map (hQ.homEquiv.symm (q.app (c, ⋆) y)) = i ≫ hR.homEquiv.symm (e.hom.app c y))
    (a : F'.obj (ψ.obj A)) :
    Functor.whiskerRight (restrictStar q) AddCommGrpCat.free ≫
        (hQ.freeHomAddEquiv (ψ ⋙ F')).symm a =
      Functor.whiskerRight e.hom AddCommGrpCat.free ≫
        ψ.whiskerLeft ((hR.freeHomAddEquiv F').symm (F'.map i a)) := by
  refine free_hom_ext fun c y ↦ ?_
  calc _ = ((hQ.freeHomAddEquiv (ψ ⋙ F')).symm a).app c
        (FreeAddCommGroup.of (q.app (c, ⋆) y)) :=
        congrArg (((hQ.freeHomAddEquiv (ψ ⋙ F')).symm a).app c)
          (whiskerRight_free_app_of (restrictStar q) c y)
    _ = F'.map (ψ.map (hQ.homEquiv.symm (q.app (c, ⋆) y))) a :=
        hQ.freeHomAddEquiv_symm_apply_app_of (ψ ⋙ F') a (q.app (c, ⋆) y)
    _ = F'.map (i ≫ hR.homEquiv.symm (e.hom.app c y)) a :=
        congrArg (fun f ↦ F'.map f a) (hq c y)
    _ = F'.map (hR.homEquiv.symm (e.hom.app c y)) (F'.map i a) :=
        Functor.map_comp_apply F' i _ a
    _ = ((hR.freeHomAddEquiv F').symm (F'.map i a)).app (ψ.obj c)
          (FreeAddCommGroup.of (e.hom.app c y)) :=
        (hR.freeHomAddEquiv_symm_apply_app_of F' (F'.map i a) (e.hom.app c y)).symm
    _ = _ := (congrArg (((hR.freeHomAddEquiv F').symm (F'.map i a)).app (ψ.obj c))
        (whiskerRight_free_app_of e.hom c y)).symm

/-- The additive Yoneda lemma in degree `0`: `Ext⁰(ℤ[R], F') ≃ F'(E)` for `R` corepresented by
`E`. -/
private noncomputable abbrev extYoneda {E : C'} (hR : R.CorepresentableBy E)
    (F' : C' ⥤ AddCommGrpCat.{w}) : Ext.{t''} (R ⋙ AddCommGrpCat.free) F' 0 ≃+ F'.obj E :=
  Ext.addEquiv₀.trans (hR.freeHomAddEquiv F')

omit [HasExt.{t} (C ⥤ AddCommGrpCat.{w})] [HasExt.{t'} (C × Bℕ ⥤ AddCommGrpCat.{w})] in
private lemma extYoneda_corepEndo {E : C'} (hR : R.CorepresentableBy E) (g : E ⟶ E)
    (y : Ext.{t''} (R ⋙ AddCommGrpCat.free) F' 0) :
    extYoneda hR F' ((Ext.mk₀ (Functor.whiskerRight (corepEndo hR g) AddCommGrpCat.free)).comp y
      (zero_add 0)) = F'.map g (extYoneda hR F' y) := by
  simp only [extYoneda, AddEquiv.trans_apply, TauCeti.ext_addEquiv₀_mk₀_comp,
    freeHomAddEquiv_corepEndo]

/-- `ℤ[Y₀ × ℕ]` has no cohomology in positive degrees. -/
private lemma ext_wangSequence_X₂_eq_zero {E : C'} (hR : R.CorepresentableBy E)
    (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R)
    (hF' : Functor.IsExtComparisonBijective.{t'', t} (N := R ⋙ AddCommGrpCat.free) ψ
      (𝟙 (ψ ⋙ F')) (𝟙 (ψ ⋙ R ⋙ AddCommGrpCat.free))) {n : ℕ}
    (z : Ext.{t'} Y.wangSequence.X₂ (Prod.fst C Bℕ ⋙ ψ ⋙ F') (n + 1)) : z = 0 := by
  have := hR.isCorepresentable
  obtain ⟨y, rfl⟩ := (wangTheta_bijective e hF' (n + 1)).2 z
  exact (congrArg (wangTheta e (n + 1)) (Ext.eq_zero_of_projective y)).trans (map_zero _)

/-- In degree `0`, pull-back along the Wang differential is onto. -/
private lemma exists_mk₀_wangSequence_f_comp_eq {E : C'} (hR : R.CorepresentableBy E)
    (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (g : E ⟶ E)
    (hg : ∀ (c : C) (y : Y.obj (c, ⋆)), hR.homEquiv.symm (e.hom.app c (Y.actionOne.app c y)) =
      g ≫ hR.homEquiv.symm (e.hom.app c y))
    (hF' : Functor.IsExtComparisonBijective.{t'', t} (N := R ⋙ AddCommGrpCat.free) ψ
      (𝟙 (ψ ⋙ F')) (𝟙 (ψ ⋙ R ⋙ AddCommGrpCat.free)))
    (hK : Function.Surjective fun z ↦ F'.map g z - z)
    (z : Ext.{t'} Y.wangSequence.X₁ (Prod.fst C Bℕ ⋙ ψ ⋙ F') 0) :
    ∃ w : Ext.{t'} Y.wangSequence.X₂ (Prod.fst C Bℕ ⋙ ψ ⋙ F') 0,
      (Ext.mk₀ Y.wangSequence.f).comp w (zero_add 0) = z := by
  obtain ⟨y, rfl⟩ := (wangTheta_bijective e hF' 0).2 z
  obtain ⟨b, hb⟩ := hK (extYoneda hR F' y)
  refine ⟨wangTheta e 0 ((extYoneda hR F').symm b), ?_⟩
  rw [mk₀_wangSequence_f_comp_wangTheta hR e g hg, ← map_sub]
  congr 1
  apply (extYoneda hR F').injective
  rw [map_sub, extYoneda_corepEndo, AddEquiv.apply_symm_apply]
  exact hb

/-- `ℤ[Y]` has no cohomology in positive degrees: by the Wang sequence, its cohomology in degree
`n + 1` is cut out of that of `ℤ[Y₀ × ℕ]` in degree `n + 1` and the cokernel of pull-back along the
Wang differential in degree `n`. -/
private lemma ext_wangSequence_X₃_eq_zero {E : C'} (hR : R.CorepresentableBy E)
    (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (g : E ⟶ E)
    (hg : ∀ (c : C) (y : Y.obj (c, ⋆)), hR.homEquiv.symm (e.hom.app c (Y.actionOne.app c y)) =
      g ≫ hR.homEquiv.symm (e.hom.app c y))
    (hF' : Functor.IsExtComparisonBijective.{t'', t} (N := R ⋙ AddCommGrpCat.free) ψ
      (𝟙 (ψ ⋙ F')) (𝟙 (ψ ⋙ R ⋙ AddCommGrpCat.free)))
    (hK : Function.Surjective fun z ↦ F'.map g z - z) {n : ℕ}
    (z : Ext.{t'} Y.wangSequence.X₃ (Prod.fst C Bℕ ⋙ ψ ⋙ F') (n + 1)) : z = 0 := by
  obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ Y.wangSequence_shortExact _ z
    (ext_wangSequence_X₂_eq_zero hR e hF' _) (add_comm 1 n)
  cases n with
  | zero =>
    obtain ⟨w, rfl⟩ := exists_mk₀_wangSequence_f_comp_eq hR e g hg hF' hK x
    exact Y.wangSequence_shortExact.extClass_comp_assoc w
  | succ n => rw [show x = 0 from ext_wangSequence_X₂_eq_zero hR e hF' x, Ext.comp_zero]

/-- In degree `0`, the line map of `q` followed by pull-back along `ℤ[Y₀ × ℕ] ⟶ ℤ[Y]` is `F'(i)`,
read through `wangTheta` and the additive Yoneda lemma for `R` and for `Q`. -/
private lemma mk₀_wangSequence_g_comp_extComparison {A : C} {E : C'}
    (hR : R.CorepresentableBy E) {Q : C ⥤ Type w} (hQ : Q.CorepresentableBy A)
    (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (i : ψ.obj A ⟶ E) (q : Y ⟶ Prod.fst C Bℕ ⋙ Q)
    (hq : ∀ (c : C) (y : Y.obj (c, ⋆)),
      ψ.map (hQ.homEquiv.symm (q.app (c, ⋆) y)) = i ≫ hR.homEquiv.symm (e.hom.app c y))
    (a : F'.obj (ψ.obj A)) :
    (Ext.mk₀ Y.wangSequence.g).comp (Functor.extComparison (N := Q ⋙ AddCommGrpCat.free)
      (Prod.fst C Bℕ) (𝟙 _) (Functor.whiskerRight q AddCommGrpCat.free) 0
        (Ext.mk₀ ((hQ.freeHomAddEquiv (ψ ⋙ F')).symm a))) (zero_add 0) =
      wangTheta e 0 (Ext.mk₀ ((hR.freeHomAddEquiv F').symm (F'.map i a))) := by
  have hcond : Y.wangSequence.g ≫ Functor.whiskerRight q AddCommGrpCat.free =
      Functor.whiskerRight (Prod.sectL C ⋆ ⋙ Y).prodNatFst AddCommGrpCat.free ≫
        (Prod.fst C Bℕ).whiskerLeft (Functor.whiskerRight (restrictStar q) AddCommGrpCat.free) :=
    (Functor.whiskerRight_comp Y.prodNatAct q AddCommGrpCat.free).symm.trans
      ((congrArg (Functor.whiskerRight · AddCommGrpCat.free) (prodNatAct_comp q)).trans
        (Functor.whiskerRight_comp _ _ _))
  refine (Functor.mk₀_comp_extComparison _ _ hcond _).trans ?_
  rw [wangTheta_apply, wangRes, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  exact congrArg _ (congrArg Ext.mk₀ (whiskerRight_restrictStar_comp hR hQ e i q hq a))

/-- The pull-back to `ℤ[Y₀ × ℕ]` of a class of `ℤ[Y]` in degree `0` is fixed by `F'(g)`, read
through `wangTheta` and the additive Yoneda lemma: the Wang differential kills it. -/
private lemma map_extYoneda_eq_of_wangTheta_eq {E : C'} (hR : R.CorepresentableBy E)
    (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (g : E ⟶ E)
    (hg : ∀ (c : C) (y : Y.obj (c, ⋆)), hR.homEquiv.symm (e.hom.app c (Y.actionOne.app c y)) =
      g ≫ hR.homEquiv.symm (e.hom.app c y))
    (hF' : Functor.IsExtComparisonBijective.{t'', t} (N := R ⋙ AddCommGrpCat.free) ψ
      (𝟙 (ψ ⋙ F')) (𝟙 (ψ ⋙ R ⋙ AddCommGrpCat.free)))
    (z : Ext.{t'} Y.wangSequence.X₃ (Prod.fst C Bℕ ⋙ ψ ⋙ F') 0)
    (y : Ext.{t''} (R ⋙ AddCommGrpCat.free) F' 0)
    (hy : wangTheta e 0 y = (Ext.mk₀ Y.wangSequence.g).comp z (zero_add 0)) :
    F'.map g (extYoneda hR F' y) = extYoneda hR F' y := by
  rw [← extYoneda_corepEndo]
  congr 1
  refine (wangTheta_bijective e hF' 0).1 (sub_eq_zero.1 ?_)
  rw [← mk₀_wangSequence_f_comp_wangTheta hR e g hg, hy]
  refine (Ext.mk₀_comp_mk₀_assoc _ _ z).trans ?_
  have h0 : (Ext.mk₀ (0 : Y.wangSequence.X₁ ⟶ Y.wangSequence.X₃)).comp z (zero_add 0) = 0 := by
    rw [Ext.mk₀_zero]
    exact Ext.zero_comp Y.wangSequence.X₁ 0 z 0 (zero_add 0)
  exact (congrArg (fun f ↦ (Ext.mk₀ f).comp z (zero_add 0)) Y.wangSequence.zero).trans h0

/-- **A criterion for lines.** Let `ψ : C ⥤ C'`, `A : C`, `E : C'`, `F' : C' ⥤ AddCommGrpCat`, and
let `R` and `Q` be corepresented by `E` and `A`. Let `Y` be a functor on `C × Bℕ` whose restriction
to `C` is identified by `e` with `R ∘ ψ = Hom(E, ψ -)`, the action `γ` of `1 ∈ ℕ` becoming
precomposition with `g : E ⟶ E`, and let `q : Y ⟶ Q` be induced by `i : ψ A ⟶ E`, in the sense
that `ψ (q y) = i ≫ y` for `y : E ⟶ ψ c`. If `F'` is acyclic at `E` along `ψ` (restriction along
`ψ` is bijective on `Extⁿ(ℤ[R], F')` for every `n`) and `F'(i)`, `F'(g)` are Koszul-exact, then `q`
is a line for `F' ∘ ψ`. -/
theorem IsLineFor.of_koszulExact {A : C} {E : C'} (hR : R.CorepresentableBy E) {Q : C ⥤ Type w}
    (hQ : Q.CorepresentableBy A) (e : Prod.sectL C ⋆ ⋙ Y ≅ ψ ⋙ R) (g : E ⟶ E)
    (i : ψ.obj A ⟶ E)
    (hg : ∀ (c : C) (y : Y.obj (c, ⋆)), hR.homEquiv.symm (e.hom.app c (Y.actionOne.app c y)) =
      g ≫ hR.homEquiv.symm (e.hom.app c y))
    (q : Y ⟶ Prod.fst C Bℕ ⋙ Q)
    (hq : ∀ (c : C) (y : Y.obj (c, ⋆)),
      ψ.map (hQ.homEquiv.symm (q.app (c, ⋆) y)) = i ≫ hR.homEquiv.symm (e.hom.app c y))
    (hF' : Functor.IsExtComparisonBijective.{t'', t} (N := R ⋙ AddCommGrpCat.free) ψ
      (𝟙 (ψ ⋙ F')) (𝟙 (ψ ⋙ R ⋙ AddCommGrpCat.free)))
    (hK : Function.KoszulExact (F'.map i) (F'.map g)) :
    IsLineFor.{t, t'} (ψ ⋙ F') q := by
  have hΘ := wangTheta_bijective e hF' 0
  have := hQ.isCorepresentable
  have := Y.wangSequence_shortExact.epi_g
  -- Through the additive Yoneda lemma for `Q`, in degree `0` the line map of `q` followed by the
  -- injective pull-back along `ℤ[Y₀ × ℕ] ⟶ ℤ[Y]` is `wangTheta` after `F'(i)`.
  let Υ' : F'.obj (ψ.obj A) ≃+ Ext.{t} (Q ⋙ AddCommGrpCat.free) (ψ ⋙ F') 0 :=
    (Ext.addEquiv₀.trans (hQ.freeHomAddEquiv (ψ ⋙ F'))).symm
  have hp₀ : Function.Injective fun z : Ext.{t'} Y.wangSequence.X₃ (Prod.fst C Bℕ ⋙ ψ ⋙ F') 0 ↦
      (Ext.mk₀ Y.wangSequence.g).comp z (zero_add 0) :=
    Ext.precomp_mk₀_injective_of_epi _ _
  refine (isLineFor_iff _ _).2 fun n ↦ ?_
  cases n with
  | zero =>
    refine ⟨fun x x' hxx' ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨a, rfl⟩ := Υ'.surjective x
      obtain ⟨a', rfl⟩ := Υ'.surjective x'
      have h := congrArg (fun z ↦ (Ext.mk₀ Y.wangSequence.g).comp z (zero_add 0)) hxx'
      simp only [Υ', AddEquiv.symm_trans_apply, Ext.addEquiv₀_symm_apply,
        mk₀_wangSequence_g_comp_extComparison hR hQ e i q hq] at h
      rw [hK.injective ((hR.freeHomAddEquiv F').symm.injective (Ext.mk₀_bijective _ _ |>.1
        (hΘ.1 h)))]
    · obtain ⟨y, hy⟩ := hΘ.2 ((Ext.mk₀ Y.wangSequence.g).comp z (zero_add 0))
      -- `y` is fixed by `F'(g)`, hence comes from `F'(ψ A)`.
      obtain ⟨a, ha⟩ := hK.mem_range_of_apply_eq
        (map_extYoneda_eq_of_wangTheta_eq hR e g hg hF' z y hy)
      refine ⟨Υ' a, hp₀ ?_⟩
      simp only [Υ', AddEquiv.symm_trans_apply, Ext.addEquiv₀_symm_apply,
        mk₀_wangSequence_g_comp_extComparison hR hQ e i q hq, ha]
      rw [← hy]
      congr 1
      exact (extYoneda hR F').symm_apply_apply y
  | succ n =>
    exact ⟨fun x x' _ ↦ (Ext.eq_zero_of_projective x).trans (Ext.eq_zero_of_projective x').symm,
      fun z ↦ ⟨0, (map_zero _).trans
        (ext_wangSequence_X₃_eq_zero hR e g hg hF' hK.surjective_sub z).symm⟩⟩

end Criterion

end CategoryTheory
