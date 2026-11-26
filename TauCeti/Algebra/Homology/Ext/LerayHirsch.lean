/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Total
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.FiveLemma
import TauCeti.Algebra.Homology.Ext.Coproduct
import TauCeti.CategoryTheory.Abelian.Devissage

/-!
# The Leray–Hirsch map

Let `Φ : 𝒜 ⥤ ℬ` be an exact functor between abelian categories, `G` an object of `𝒜`, `F` an object
of `ℬ`, and `θᵢ ∈ Ext^{dᵢ}(Φ G, F)` a family of classes indexed by a type `I`. For an object `S` of
`𝒜`, the *Leray–Hirsch map* (`CategoryTheory.Functor.lerayHirsch`)

`⨁ᵢ H*(S, G) ⟶ H*(Φ S, F)`, `(wᵢ) ↦ ∑ᵢ Φ(wᵢ) · θᵢ`,

with `H*` the total Ext groups of `TauCeti.Algebra.Homology.Ext.Total` and `·` the Yoneda product,
is natural in `S` (`CategoryTheory.Functor.mk₀_comp_lerayHirsch`). The classes `θᵢ` form a
*Leray–Hirsch basis at* `S` (`CategoryTheory.Functor.IsLerayHirschBasis`) if this map is bijective.
The main example is restriction `Φ = φ*` from functors `A ⥤ AddCommGrpCat` to functors
`C ⥤ AddCommGrpCat` along a functor `φ : C ⥤ A`. There a Leray–Hirsch basis at `S` says that
`H*(φ ⋙ S, F)` is the direct sum of copies of `H*(S, G)`, shifted by the degrees `dᵢ`, through the
classes `θᵢ`; the projective bundle formula is of this shape.

## Main results

* `CategoryTheory.Functor.isLerayHirschBasis_of_forall_exists_epi`: if every object is a quotient
  of an object at which the `θᵢ` form a Leray–Hirsch basis, they form one at every object.
* `CategoryTheory.Functor.isLerayHirschBasis_of_isColimit`: for finite `I`, Leray–Hirsch bases
  pass to coproducts that `Φ` preserves.

The first is the dévissage `TauCeti.bijective_of_forall_exists_epi` applied to the parts of the
Leray–Hirsch map of each total degree: the summands `Extᵐ(S, G)` of the `i`-th copy with
`m + dᵢ = n` map to `Extⁿ(Φ S, F)`, and the long exact sequences of `Ext(-, G)` and `Ext(Φ -, F)`
along a short exact sequence, which these parts respect, supply the four-lemma steps. The second
holds because both sides are products over the summands in each degree (`Ext.coproductAddEquiv`),
and the direct sum over a finite `I` commutes with these products.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4D.1 (the
  Leray–Hirsch theorem).
* *Cohomologie `ℓ`-adique et fonctions `L`* (SGA 5), Lecture Notes in Math. 589, Springer, 1977,
  Exposé VII (the projective bundle formula).
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/LerayHirsch.lean` (declarations `New.Variety.lerayHirsch`,
  `New.Variety.IsLerayHirschBasis`, `New.Variety.isLerayHirschBasis_of_reprBy`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The definitions are adapted from these declarations and stated for
  an exact functor between abelian categories.
-/

public section

open CategoryTheory Limits Abelian DirectSum Function

universe t t' v u v' u'

namespace CategoryTheory.Functor

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasExt.{t} 𝒜]
  {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ] [HasExt.{t'} ℬ]
  (Φ : 𝒜 ⥤ ℬ) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {G : 𝒜} {F : ℬ} {I : Type*} {d : I → ℕ}

section LerayHirsch

variable [DecidableEq I]

/-- The *Leray–Hirsch map* `⨁ᵢ H*(S, G) ⟶ H*(Φ S, F)` of classes `θᵢ ∈ Ext^{dᵢ}(Φ G, F)`, for an
exact functor `Φ`: it sends a family `(wᵢ)` of total Ext classes to `∑ᵢ Φ(wᵢ) · θᵢ`, the Yoneda
product being written in diagram order. -/
noncomputable def lerayHirsch (θ : ∀ i, Ext.{t'} (Φ.obj G) F (d i)) (S : 𝒜) :
    (⨁ _ : I, TotalExt.{t} S G) →+ TotalExt.{t'} (Φ.obj S) F :=
  toAddMonoid fun i ↦ (TotalExt.comp.flip (of _ (d i) (θ i))).comp (TotalExt.map Φ)

variable (θ : ∀ i, Ext.{t'} (Φ.obj G) F (d i))

/-- On the summand of `i`, the Leray–Hirsch map is the action of `Φ` followed by the product with
`θᵢ`. -/
@[simp]
lemma lerayHirsch_of (S : 𝒜) (i : I) (x : TotalExt.{t} S G) :
    Φ.lerayHirsch θ S (of _ i x) = TotalExt.comp (TotalExt.map Φ x) (of _ (d i) (θ i)) := by
  simp [lerayHirsch]

/-- On a homogeneous class of degree `m` in the summand of `i`, the Leray–Hirsch map is the image
of the class under `Φ` composed with `θᵢ`, a class of degree `m + dᵢ`. -/
lemma lerayHirsch_of_of (S : 𝒜) (i : I) {m : ℕ} (x : Ext.{t} S G m) :
    Φ.lerayHirsch θ S (of _ i (of _ m x)) =
      of _ (m + d i) ((x.mapExactFunctor Φ).comp (θ i) rfl) := by
  rw [lerayHirsch_of, TotalExt.map_of, TotalExt.comp_of_of]

/-- The Leray–Hirsch map is natural in `S`: for `α : S' ⟶ S`, pulling back along `Φ α` after the
map at `S` is the map at `S'` after pulling back each summand along `α`. -/
lemma mk₀_comp_lerayHirsch {S S' : 𝒜} (α : S' ⟶ S) (x : ⨁ _ : I, TotalExt.{t} S G) :
    TotalExt.comp (TotalExt.mk₀ (Φ.map α)) (Φ.lerayHirsch θ S x) =
      Φ.lerayHirsch θ S' (DirectSum.map (fun _ ↦ TotalExt.comp (TotalExt.mk₀ α)) x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp_all
  | of i x =>
    rw [lerayHirsch_of, DirectSum.map_of, lerayHirsch_of, TotalExt.map_comp, TotalExt.map_mk₀,
      ← TotalExt.comp_assoc]

/-- The classes `θᵢ` form a *Leray–Hirsch basis at* `S` if the Leray–Hirsch map
`⨁ᵢ H*(S, G) ⟶ H*(Φ S, F)` is bijective. -/
def IsLerayHirschBasis (S : 𝒜) : Prop :=
  Bijective (Φ.lerayHirsch θ S)

/-- The classes `θᵢ` form a Leray–Hirsch basis at `S` exactly when the Leray–Hirsch map at `S` is
bijective. -/
lemma isLerayHirschBasis_iff (S : 𝒜) :
    Φ.IsLerayHirschBasis θ S ↔ Bijective (Φ.lerayHirsch θ S) :=
  Iff.rfl

end LerayHirsch

/-! ### The Leray–Hirsch map degree by degree -/

section Degree

variable [DecidableEq I] (θ : ∀ i, Ext.{t'} (Φ.obj G) F (d i))

/-- The pairs `(i, m)` with `m + dᵢ = n`, which index the summands of total degree `n` of the
source of the Leray–Hirsch map. -/
private abbrev Deg (d : I → ℕ) (n : ℕ) : Type _ := {q : (_ : I) × ℕ // q.snd + d q.fst = n}

/-- The summand `(i, m + 1)` of total degree `n + 1` above the summand `(i, m)` of total degree
`n`. -/
private abbrev Deg.shift {n : ℕ} (p : Deg d n) : Deg d (n + 1) :=
  ⟨⟨p.val.fst, p.val.snd + 1⟩, by have := p.property; lia⟩

omit [DecidableEq I] in
private lemma Deg.shift_injective (n : ℕ) : Function.Injective (Deg.shift (d := d) (n := n)) := by
  rintro ⟨⟨i, m⟩, hp⟩ ⟨⟨i', m'⟩, hp'⟩ h
  simp only [Deg.shift, Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq,
    Nat.add_right_cancel_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- The degree-`n` part of the Leray–Hirsch map, on the summands `(i, m)` with `m + dᵢ = n`. -/
private noncomputable def lhDeg (S : 𝒜) (n : ℕ) :
    (⨁ p : Deg d n, Ext.{t} S G p.val.snd) →+ Ext.{t'} (Φ.obj S) F n :=
  toAddMonoid fun p ↦ ((θ p.val.fst).postcomp (Φ.obj S) p.property).comp
    (Φ.mapExtAddHom S G p.val.snd)

private lemma lhDeg_of (S : 𝒜) (n : ℕ) (p : Deg d n) (x : Ext.{t} S G p.val.snd) :
    lhDeg Φ θ S n (of _ p x) = (x.mapExactFunctor Φ).comp (θ p.val.fst) p.property := by
  simp [lhDeg]

/-- Pull-back along `α : X ⟶ Y`, summand by summand. -/
private noncomputable def pull (d : I → ℕ) {X Y : 𝒜} (α : X ⟶ Y) (n : ℕ) :
    (⨁ p : Deg d n, Ext.{t} Y G p.val.snd) →+ ⨁ p : Deg d n, Ext.{t} X G p.val.snd :=
  DirectSum.map fun p ↦ (Ext.mk₀ α).precomp G (zero_add p.val.snd)

omit [DecidableEq I] in
private lemma pull_apply (d : I → ℕ) {X Y : 𝒜} (α : X ⟶ Y) (n : ℕ)
    (a : ⨁ p : Deg d n, Ext.{t} Y G p.val.snd) (p : Deg d n) :
    pull d α n a p = (Ext.mk₀ α).comp (a p) (zero_add _) :=
  DirectSum.map_apply _ _ _

omit [DecidableEq I] in
private lemma pull_eq_zero_iff {X Y : 𝒜} (α : X ⟶ Y) (n : ℕ)
    (a : ⨁ p : Deg d n, Ext.{t} Y G p.val.snd) :
    pull d α n a = 0 ↔ ∀ p, (Ext.mk₀ α).comp (a p) (zero_add _) = 0 := by
  simp [DirectSum.ext_iff, pull_apply]

omit [DecidableEq I] in
private lemma mem_range_pull_iff {X Y : 𝒜} (α : X ⟶ Y) (n : ℕ)
    (a : ⨁ p : Deg d n, Ext.{t} X G p.val.snd) :
    a ∈ Set.range (pull d α n) ↔ ∀ p, ∃ x, (Ext.mk₀ α).comp x (zero_add _) = a p := by
  rw [← AddMonoidHom.coe_range, SetLike.mem_coe, pull, DirectSum.range_map]
  simp [AddSubgroup.mem_pi, Ext.bilinearComp_apply_apply]

/-- The degree-`n` part of the Leray–Hirsch map is natural in `S`. -/
private lemma lhDeg_pull {X Y : 𝒜} (α : X ⟶ Y) (n : ℕ) (a : ⨁ p : Deg d n, Ext.{t} Y G p.val.snd) :
    lhDeg Φ θ X n (pull d α n a) = (Ext.mk₀ (Φ.map α)).comp (lhDeg Φ θ Y n a) (zero_add n) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb, Ext.comp_add]
  | of p x =>
    rw [pull, DirectSum.map_of, lhDeg_of, lhDeg_of, Ext.bilinearComp_apply_apply,
      Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc _ _ _ (zero_add _) p.property (by lia)]

/-- The connecting map `Extᵐ(X₁, G) ⟶ Extᵐ⁺¹(X₃, G)` of a short exact sequence, from the summands
of total degree `n` to those of total degree `n + 1`. -/
private noncomputable def connecting {S : ShortComplex 𝒜} (hS : S.ShortExact) (d : I → ℕ)
    (n : ℕ) :
    (⨁ p : Deg d n, Ext.{t} S.X₁ G p.val.snd) →+ ⨁ p : Deg d (n + 1), Ext.{t} S.X₃ G p.val.snd :=
  toAddMonoid fun p ↦ (of (fun p : Deg d (n + 1) ↦ Ext.{t} S.X₃ G p.val.snd) p.shift).comp
    (hS.extClass.precomp G (add_comm 1 p.val.snd))

private lemma connecting_of {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ) (p : Deg d n)
    (x : Ext.{t} S.X₁ G p.val.snd) :
    connecting hS d n (of _ p x) = of _ p.shift (hS.extClass.comp x (add_comm 1 p.val.snd)) := by
  simp [connecting, Ext.bilinearComp_apply_apply]

private lemma connecting_apply_shift {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ)
    (a : ⨁ p : Deg d n, Ext.{t} S.X₁ G p.val.snd) (p : Deg d n) :
    connecting hS d n a p.shift = hS.extClass.comp (a p) (add_comm 1 p.val.snd) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb, Ext.comp_add]
  | of p' x =>
    rw [connecting_of]
    by_cases h : p' = p
    · subst h
      simp
    · rw [of_eq_of_ne _ _ _ ((Deg.shift_injective n).ne (Ne.symm h)), of_eq_of_ne _ _ _ (Ne.symm h),
        Ext.comp_zero]

private lemma connecting_apply_zero {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ)
    (a : ⨁ p : Deg d n, Ext.{t} S.X₁ G p.val.snd) (i : I) (h : 0 + d i = n + 1) :
    connecting hS d n a ⟨⟨i, 0⟩, h⟩ = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | of p' x =>
    rw [connecting_of, of_eq_of_ne]
    intro h'
    have := congrArg (fun q : Deg d (n + 1) ↦ q.val.snd) h'
    simp at this

/-- The degree-`n` part of the Leray–Hirsch map commutes with the connecting maps. -/
private lemma lhDeg_connecting {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ)
    (a : ⨁ p : Deg d n, Ext.{t} S.X₁ G p.val.snd) :
    lhDeg Φ θ S.X₃ (n + 1) (connecting hS d n a) =
      (hS.map_of_exact Φ).extClass.comp (lhDeg Φ θ S.X₁ n a) (add_comm 1 n) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb, Ext.comp_add]
  | of p x =>
    rw [connecting_of, lhDeg_of, lhDeg_of, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      Ext.comp_assoc _ _ _ (add_comm 1 p.val.snd) p.property (by have := p.property; lia)]

omit [DecidableEq I] in
/-- Exactness of `Ext(S.X₃, -) ⟶ Ext(S.X₂, -) ⟶ Ext(S.X₁, -)` on the summands of total degree
`n`. -/
private lemma exact_pull_pull {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (pull (G := G) d S.g n) (pull d S.f n) := by
  intro y
  rw [pull_eq_zero_iff, mem_range_pull_iff]
  refine ⟨fun hy p ↦ Ext.contravariant_sequence_exact₂ hS G (y p) (hy p), fun h p ↦ ?_⟩
  obtain ⟨x, hx⟩ := h p
  rw [← hx, Ext.mk₀_comp_mk₀_assoc, S.zero, Ext.mk₀_zero, Ext.zero_comp]

/-- Exactness of the long exact sequence at `Ext(S.X₁, -)`, on the summands of total degree `n`. -/
private lemma exact_pull_connecting {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (pull (G := G) d S.f n) (connecting hS d n) := by
  intro y
  rw [DirectSum.ext_iff, mem_range_pull_iff]
  simp only [DirectSum.zero_apply]
  refine ⟨fun hy p ↦ ?_, fun h p' ↦ ?_⟩
  · have := hy p.shift
    rw [connecting_apply_shift] at this
    exact Ext.contravariant_sequence_exact₁ hS G (y p) _ this
  · obtain ⟨⟨i, _ | m⟩, hp⟩ := p'
    · exact connecting_apply_zero hS n y i hp
    · obtain ⟨x, hx⟩ := h ⟨⟨i, m⟩, by simp only at hp; lia⟩
      exact (connecting_apply_shift hS n y ⟨⟨i, m⟩, _⟩).trans (by rw [← hx, hS.extClass_comp_assoc])

/-- Exactness of the long exact sequence at `Ext(S.X₃, -)`, on the summands of total degree
`n + 1`. -/
private lemma exact_connecting_pull {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (connecting (G := G) hS d n) (pull d S.g (n + 1)) := by
  have := hS.epi_g
  intro y
  rw [pull_eq_zero_iff]
  refine ⟨fun hy ↦ ?_, ?_⟩
  · -- The components of positive degree of `y` come from the connecting map, and those of
    -- degree `0` vanish.
    obtain ⟨x, hx⟩ : DFinsupp.comapDomain _ (Deg.shift_injective n) y ∈
        (DirectSum.map fun p : Deg d n ↦ hS.extClass.precomp G (add_comm 1 p.val.snd)).range := by
      rw [DirectSum.range_map]
      exact fun p _ ↦ Ext.contravariant_sequence_exact₃ hS G _ (hy p.shift) (add_comm 1 _)
    refine ⟨x, ?_⟩
    ext ⟨⟨i, _ | m⟩, hp⟩
    · rw [connecting_apply_zero]
      exact (Ext.precomp_mk₀_injective_of_epi G S.g
        ((hy ⟨⟨i, 0⟩, hp⟩).trans (Ext.comp_zero (Ext.mk₀ S.g) G 0 0 (zero_add 0)).symm)).symm
    · have := DFunLike.congr_fun hx ⟨⟨i, m⟩, by simp only at hp; lia⟩
      rw [DirectSum.map_apply, DFinsupp.comapDomain_apply, Ext.bilinearComp_apply_apply] at this
      exact (connecting_apply_shift hS n x _).trans this
  · rintro ⟨x, rfl⟩ ⟨⟨i, _ | m⟩, hp⟩
    · rw [connecting_apply_zero]
      exact Ext.comp_zero _ _ _ _ (zero_add 0)
    · rw [connecting_apply_shift hS n x ⟨⟨i, m⟩, by simp only at hp; lia⟩,
        hS.comp_extClass_assoc]

omit [DecidableEq I] in
/-- In total degree `0`, pull-back along the epimorphism of a short exact sequence is injective. -/
private lemma pull_injective_zero {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Function.Injective (pull (G := G) d S.g 0) := by
  have := hS.epi_g
  refine (DirectSum.map_injective _).2 fun p ↦ ?_
  obtain ⟨⟨i, m⟩, hp⟩ := p
  obtain rfl : m = 0 := by simp only at hp; lia
  exact Ext.precomp_mk₀_injective_of_epi G S.g

/-- The step of dévissage for injectivity: in a short exact sequence, if the degree-`m` parts of
the Leray–Hirsch map are bijective at `S.X₁` and `S.X₂` for `m < n` and the degree-`n` part is
injective at `S.X₂`, then it is injective at `S.X₃`, by the four lemma. -/
private lemma lhDeg_injective_X₃ {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ)
    (h₁ : ∀ m < n, Bijective (lhDeg Φ θ S.X₁ m)) (h₂ : ∀ m < n, Bijective (lhDeg Φ θ S.X₂ m))
    (hi : Function.Injective (lhDeg Φ θ S.X₂ n)) : Function.Injective (lhDeg Φ θ S.X₃ n) := by
  cases n with
  | zero =>
    have hc : (Ext.mk₀ (Φ.map S.g)).precomp F (zero_add 0) ∘ lhDeg Φ θ S.X₃ 0 =
        lhDeg Φ θ S.X₂ 0 ∘ pull d S.g 0 :=
      funext fun a ↦ (lhDeg_pull Φ θ S.g 0 a).symm
    exact Function.Injective.of_comp (hc ▸ hi.comp (pull_injective_zero hS))
  | succ n =>
    exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
      (pull d S.f n) (connecting hS d n) (pull d S.g (n + 1))
      ((Ext.mk₀ (Φ.map S.f)).precomp F (zero_add n))
      ((hS.map_of_exact Φ).extClass.precomp F (add_comm 1 n))
      ((Ext.mk₀ (Φ.map S.g)).precomp F (zero_add (n + 1)))
      (lhDeg Φ θ S.X₂ n) (lhDeg Φ θ S.X₁ n) (lhDeg Φ θ S.X₃ (n + 1)) (lhDeg Φ θ S.X₂ (n + 1))
      (AddMonoidHom.ext fun a ↦ (lhDeg_pull Φ θ S.f n a).symm)
      (AddMonoidHom.ext fun a ↦ (lhDeg_connecting Φ θ hS n a).symm)
      (AddMonoidHom.ext fun a ↦ (lhDeg_pull Φ θ S.g (n + 1) a).symm)
      (exact_pull_connecting hS n) (exact_connecting_pull hS n)
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' (hS.map_of_exact Φ) F n (n + 1) (add_comm 1 n)))
      (h₂ n (by lia)).2 (h₁ n (by lia)).1 hi

/-- The step of dévissage for surjectivity: in a short exact sequence, if the degree-`m` parts of
the Leray–Hirsch map are bijective at `S.X₁` for `m < n` and at `S.X₂` for `m ≤ n`, and the
degree-`n` part is injective at `S.X₁`, then it is surjective at `S.X₃`, by the four lemma. -/
private lemma lhDeg_surjective_X₃ {S : ShortComplex 𝒜} (hS : S.ShortExact) (n : ℕ)
    (h₁ : ∀ m < n, Bijective (lhDeg Φ θ S.X₁ m)) (hi : Function.Injective (lhDeg Φ θ S.X₁ n))
    (h₂ : ∀ m ≤ n, Bijective (lhDeg Φ θ S.X₂ m)) : Surjective (lhDeg Φ θ S.X₃ n) := by
  cases n with
  | zero =>
    have : Epi (Φ.map S.g) := (hS.map_of_exact Φ).epi_g
    intro y
    obtain ⟨a, ha⟩ := (h₂ 0 le_rfl).2 ((Ext.mk₀ (Φ.map S.g)).comp y (zero_add 0))
    have hf : pull d S.f 0 a = 0 := hi (by
      rw [lhDeg_pull, ha, Ext.mk₀_comp_mk₀_assoc, ← Φ.map_comp, S.zero, Φ.map_zero, Ext.mk₀_zero,
        Ext.zero_comp, map_zero])
    obtain ⟨b, rfl⟩ := (exact_pull_pull hS 0 a).1 hf
    exact ⟨b, Ext.precomp_mk₀_injective_of_epi F (Φ.map S.g)
      ((lhDeg_pull Φ θ S.g 0 b).symm.trans ha)⟩
  | succ n =>
    exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
      (connecting hS d n) (pull d S.g (n + 1)) (pull d S.f (n + 1))
      ((hS.map_of_exact Φ).extClass.precomp F (add_comm 1 n))
      ((Ext.mk₀ (Φ.map S.g)).precomp F (zero_add (n + 1)))
      ((Ext.mk₀ (Φ.map S.f)).precomp F (zero_add (n + 1)))
      (lhDeg Φ θ S.X₁ n) (lhDeg Φ θ S.X₃ (n + 1)) (lhDeg Φ θ S.X₂ (n + 1)) (lhDeg Φ θ S.X₁ (n + 1))
      (AddMonoidHom.ext fun a ↦ (lhDeg_connecting Φ θ hS n a).symm)
      (AddMonoidHom.ext fun a ↦ (lhDeg_pull Φ θ S.g (n + 1) a).symm)
      (AddMonoidHom.ext fun a ↦ (lhDeg_pull Φ θ S.f (n + 1) a).symm)
      (exact_pull_pull hS (n + 1))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₃' (hS.map_of_exact Φ) F n (n + 1) (add_comm 1 n)))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₂' (hS.map_of_exact Φ) F (n + 1)))
      (h₁ n (by lia)).2 (h₂ (n + 1) le_rfl).2 hi

/-- The regrouping of `⨁ᵢ ⨁ₘ Extᵐ(S, G)` by total degree `m + dᵢ`. -/
private noncomputable def regroup (d : I → ℕ) (S : 𝒜) :
    (⨁ _ : I, TotalExt.{t} S G) ≃+ ⨁ (n : ℕ) (p : Deg d n), Ext.{t} S G p.val.snd :=
  (sigmaCurryEquiv (δ := fun (_ : I) (m : ℕ) ↦ Ext.{t} S G m)).symm.trans
    ((equivCongrLeft (Equiv.sigmaFiberEquiv fun q : (_ : I) × ℕ ↦ q.snd + d q.fst).symm).trans
      (sigmaCurryEquiv (δ := fun (n : ℕ) (p : Deg d n) ↦ Ext.{t} S G p.val.snd)))

private lemma regroup_apply (S : 𝒜) (y : ⨁ _ : I, TotalExt.{t} S G) :
    regroup d S y = sigmaCurry (δ := fun (n : ℕ) (p : Deg d n) ↦ Ext.{t} S G p.val.snd)
      (equivCongrLeft (Equiv.sigmaFiberEquiv fun q : (_ : I) × ℕ ↦ q.snd + d q.fst).symm
        ((sigmaCurryEquiv (δ := fun (_ : I) (m : ℕ) ↦ Ext.{t} S G m)).symm y)) :=
  rfl

private lemma regroup_of_of (S : 𝒜) (i : I) (m : ℕ) (x : Ext.{t} S G m) :
    regroup d S (of _ i (of _ m x)) = of _ (m + d i) (of _ ⟨⟨i, m⟩, rfl⟩ x) := by
  let e := Equiv.sigmaFiberEquiv fun q : (_ : I) × ℕ ↦ q.snd + d q.fst
  let k : (n : ℕ) × Deg d n := ⟨m + d i, ⟨⟨i, m⟩, rfl⟩⟩
  have h₁ : (sigmaCurryEquiv (δ := fun (_ : I) (m : ℕ) ↦ Ext.{t} S G m)).symm (of _ i (of _ m x)) =
      of (fun q : (_ : I) × ℕ ↦ Ext.{t} S G q.snd) (e k) x := by
    rw [AddEquiv.symm_apply_eq]
    exact (sigmaCurry_of (δ := fun (_ : I) (m : ℕ) ↦ Ext.{t} S G m) ⟨i, m⟩ x).symm
  rw [regroup_apply, h₁]
  have h₂ := equivCongrLeft_of (β := fun q : (_ : I) × ℕ ↦ Ext.{t} S G q.snd) (h := e.symm) k x
  have h₃ := sigmaCurry_of (δ := fun (n : ℕ) (p : Deg d n) ↦ Ext.{t} S G p.val.snd) k x
  exact (congrArg (sigmaCurry (δ := fun (n : ℕ) (p : Deg d n) ↦ Ext.{t} S G p.val.snd)) h₂).trans h₃

/-- The Leray–Hirsch map is the sum of its parts of each total degree. -/
private lemma lerayHirsch_eq_map_lhDeg (S : 𝒜) :
    Φ.lerayHirsch θ S = (DirectSum.map (lhDeg Φ θ S)).comp (regroup d S).toAddMonoidHom := by
  ext i m x
  simp [regroup_of_of, lhDeg]

/-- The classes `θᵢ` form a Leray–Hirsch basis at `S` exactly when every degree-`n` part of the
Leray–Hirsch map is bijective. -/
private lemma isLerayHirschBasis_iff_forall_bijective_lhDeg (S : 𝒜) :
    Φ.IsLerayHirschBasis θ S ↔ ∀ n, Bijective (lhDeg Φ θ S n) := by
  rw [isLerayHirschBasis_iff, lerayHirsch_eq_map_lhDeg, AddMonoidHom.coe_comp,
    AddEquiv.coe_toAddMonoidHom, Bijective.of_comp_iff _ (regroup d S).bijective]
  simp only [Bijective, DirectSum.map_injective, DirectSum.map_surjective, forall_and]

end Degree

/-! ### Leray–Hirsch bases from presenting objects -/

section Basis

variable [DecidableEq I] (θ : ∀ i, Ext.{t'} (Φ.obj G) F (d i))

/-- **Leray–Hirsch dévissage.** If every object of `𝒜` is a quotient of an object at which the
classes `θᵢ ∈ Ext^{dᵢ}(Φ G, F)` form a Leray–Hirsch basis, then they form a Leray–Hirsch basis at
every object. -/
theorem isLerayHirschBasis_of_forall_exists_epi
    (h : ∀ X : 𝒜, ∃ (Q : 𝒜) (p : Q ⟶ X), Epi p ∧ Φ.IsLerayHirschBasis θ Q) (S : 𝒜) :
    Φ.IsLerayHirschBasis θ S := by
  rw [isLerayHirschBasis_iff_forall_bijective_lhDeg]
  exact TauCeti.bijective_of_forall_exists_epi (f := fun X n ↦ lhDeg Φ θ X n)
    (fun _ hS n h₁ h₂ hi ↦ lhDeg_injective_X₃ Φ θ hS n h₁ h₂ hi)
    (fun _ hS n h₁ hi h₂ ↦ lhDeg_surjective_X₃ Φ θ hS n h₁ hi h₂)
    (fun X ↦ by
      obtain ⟨Q, p, hp, hQ⟩ := h X
      exact ⟨Q, p, hp, (isLerayHirschBasis_iff_forall_bijective_lhDeg Φ θ Q).1 hQ⟩) S

/-- For finitely many classes `θᵢ`, Leray–Hirsch bases pass to coproducts preserved by `Φ`: if
the `θᵢ` form a Leray–Hirsch basis at every `Xⱼ`, they form one at `∐ⱼ Xⱼ`. In each degree both
sides of the Leray–Hirsch map are products over `j`, and the finiteness of `I` lets the direct sum
over `I` commute with these products. -/
theorem isLerayHirschBasis_of_isColimit [Finite I] [EnoughInjectives 𝒜] [EnoughInjectives ℬ]
    {J : Type*} {X : J → 𝒜} {c : Cofan X} (hc : IsColimit c)
    [PreservesColimit (Discrete.functor X) Φ] (h : ∀ j, Φ.IsLerayHirschBasis θ (X j)) :
    Φ.IsLerayHirschBasis θ c.pt := by
  have hX := fun j ↦ (isLerayHirschBasis_iff_forall_bijective_lhDeg Φ θ (X j)).1 (h j)
  rw [isLerayHirschBasis_iff_forall_bijective_lhDeg]
  intro n
  -- In degree `n`, restriction to the summands identifies both sides of the degree-`n` part of
  -- the Leray–Hirsch map at `∐ⱼ Xⱼ` with products over `j`, compatibly with the maps at the `Xⱼ`.
  let eB := Ext.coproductAddEquiv (isColimitCofanMkObjOfIsColimit Φ X c.inj hc) F n
  let R : (⨁ p : Deg d n, Ext.{t} c.pt G p.val.snd) →
      ∀ j, ⨁ p : Deg d n, Ext.{t} (X j) G p.val.snd := fun a j ↦ pull d (c.inj j) n a
  have hcomm : eB ∘ lhDeg Φ θ c.pt n = (fun b j ↦ lhDeg Φ θ (X j) n (b j)) ∘ R := by
    funext a j
    simp only [Function.comp_apply, eB, R, Ext.coproductAddEquiv_apply, cofan_mk_inj, lhDeg_pull]
  have hR : Bijective R := by
    refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
    · ext p
      refine (Ext.coproductAddEquiv hc G _).injective (funext fun j ↦ ?_)
      have := DFunLike.congr_fun (congrFun hab j) p
      rwa [pull_apply, pull_apply, ← Ext.coproductAddEquiv_apply hc,
        ← Ext.coproductAddEquiv_apply hc] at this
    · -- The finiteness of `I` makes the direct sum over the summands of degree `n` a product.
      have : Finite (Deg d n) := Finite.of_injective (fun p : Deg d n ↦ p.val.fst) fun p p' h ↦ by
        obtain ⟨⟨i, m⟩, hp⟩ := p
        obtain ⟨⟨i', m'⟩, hp'⟩ := p'
        obtain rfl : i = i' := h
        obtain rfl : m = m' := by simp only at hp hp'; lia
        rfl
      have := Fintype.ofFinite (Deg d n)
      refine ⟨(addEquivProd fun p : Deg d n ↦ Ext.{t} c.pt G p.val.snd).symm
        fun p ↦ (Ext.coproductAddEquiv hc G _).symm fun j ↦ b j p, funext fun j ↦ ?_⟩
      ext p
      exact Ext.mk₀_comp_coproductAddEquiv_symm hc G _ (fun j ↦ b j p) j
  refine (Bijective.of_comp_iff' eB.bijective _).1 ?_
  rw [hcomm]
  exact (Bijective.piMap fun j ↦ hX j n).comp hR

end Basis

end CategoryTheory.Functor
