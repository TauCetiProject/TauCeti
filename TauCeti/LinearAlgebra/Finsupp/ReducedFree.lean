/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Reduced free modules on pointed types

For a type `α` with a chosen point `a`, the reduced free `R`-module `ReducedFreeModule R a` is the
free module `α →₀ R` modulo the line spanned by the generator of `a`. It is spanned by the
generators `ReducedFreeModule.mk R x` of the points `x : α`, and the generator of the basepoint
is zero (`ReducedFreeModule.mk_self`). Applied degreewise to a pointed simplicial set `X`, it gives
the simplicial module `Ã[X]` whose underlying pointed simplicial set is the reduced free
construction used to build Eilenberg–MacLane spectra.

A based map `f : α → β` induces the linear map `ReducedFreeModule.map R f`, sending generators to
generators, and a ring homomorphism `φ : R →+* S` induces the `φ`-semilinear map
`ReducedFreeModule.mapRing φ`, changing coefficients on generators. For a commutative ring `R` and
a function `p : α → β → γ` sending the two axes `{a} × β` and `α × {b}` to the basepoint `c`, such
as the quotient map onto a smash product, `ReducedFreeModule.map₂ R p` is the bilinear map sending
the generators of `x` and `y` to the generator of `p x y`. This is the external product of reduced
free modules.

## Main definitions

* `ReducedFreeModule R a`: the reduced free module on the pointed type `(α, a)`.
* `ReducedFreeModule.mk R x`: the generator of a point `x`.
* `ReducedFreeModule.lift R f`: the linear map extending a function `f` that vanishes at the
  basepoint.
* `ReducedFreeModule.map R f`: the linear map induced by a based map `f`.
* `ReducedFreeModule.mapRing φ`: the `φ`-semilinear change-of-rings map along `φ : R →+* S`.
* `ReducedFreeModule.map₂ R p`: the bilinear map induced by a function `p` of two variables sending
  the axes to the basepoint.

## Main statements

* `ReducedFreeModule.induction_on`: induction on elements through sums of multiples of
  generators, `ReducedFreeModule.linearMap_ext`: semilinear maps out of a reduced free module are
  determined by their values on generators, and `ReducedFreeModule.linearMap_ext₂`: likewise for
  curried semilinear maps out of two reduced free modules.
* `ReducedFreeModule.lift_mk`, `ReducedFreeModule.lift_unique`: the universal property of the
  reduced free module.
* `ReducedFreeModule.mapRing_map`, `ReducedFreeModule.mapRing_map₂`: compatibility of `mapRing`
  with based maps and external products.
* `ReducedFreeModule.map_map₂`, `ReducedFreeModule.map₂_map_left`,
  `ReducedFreeModule.map₂_map_right`: naturality of `map₂`.
* `ReducedFreeModule.map₂_assoc`, `ReducedFreeModule.map₂_swap`, `ReducedFreeModule.map₂_mk_left`,
  `ReducedFreeModule.map₂_mk_right`: associativity, symmetry and unitality of `map₂`, for functions
  of two variables satisfying the corresponding laws.
-/

public section

universe u v w

open Finsupp

namespace TauCeti

noncomputable section

/-- The reduced free `R`-module on a type `α` with a chosen point `a`: the free module `α →₀ R`
modulo the submodule spanned by the generator of `a`. -/
abbrev ReducedFreeModule (R : Type*) [Ring R] {α : Type*} (a : α) : Type _ :=
  (α →₀ R) ⧸ R ∙ Finsupp.single a (1 : R)

namespace ReducedFreeModule

section Ring

variable (R : Type*) [Ring R] {α : Type u} {β : Type v} {γ : Type w} {a : α} {b : β} {c : γ}

/-- The generator of a point `x` in the reduced free module. -/
def mk (x : α) : ReducedFreeModule R a :=
  Submodule.Quotient.mk (Finsupp.single x 1)

/-- The generator of the basepoint is zero. -/
@[simp]
lemma mk_self : mk R a = (0 : ReducedFreeModule R a) :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)

/-- Induction on the elements of a reduced free module: it suffices to treat zero, sums and
multiples of generators. -/
@[elab_as_elim]
lemma induction_on {motive : ReducedFreeModule R a → Prop} (v : ReducedFreeModule R a)
    (zero : motive 0) (add : ∀ v w, motive v → motive w → motive (v + w))
    (smul_mk : ∀ (r : R) (x : α), motive (r • mk R x)) : motive v := by
  induction v using Submodule.Quotient.induction_on with | H f
  induction f using Finsupp.induction_linear with
  | zero => exact zero
  | add f g hf hg => exact add _ _ hf hg
  | single x r =>
    have h := smul_mk r x
    rwa [mk, ← Submodule.Quotient.mk_smul, smul_single_one] at h

variable {R}

/-- Semilinear maps out of a reduced free module are determined by their values on generators. -/
@[ext high]
lemma linearMap_ext {S : Type*} [Semiring S] {σ : R →+* S} {M : Type*} [AddCommMonoid M]
    [Module S M] {f g : ReducedFreeModule R a →ₛₗ[σ] M} (h : ∀ x, f (mk R x) = g (mk R x)) :
    f = g := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using induction_on with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | smul_mk r x => simp [h]

/-- Curried semilinear maps out of two reduced free modules are determined by their values on
pairs of generators. -/
lemma linearMap_ext₂ {R₂ S₁ S₂ : Type*} [Ring R₂] [Semiring S₁] [Semiring S₂] {σ₁ : R →+* S₁}
    {σ₂ : R₂ →+* S₂} {M : Type*} [AddCommMonoid M] [Module S₁ M] [Module S₂ M]
    [SMulCommClass S₂ S₁ M] {f g : ReducedFreeModule R a →ₛₗ[σ₁] ReducedFreeModule R₂ b →ₛₗ[σ₂] M}
    (h : ∀ x y, f (mk R x) (mk R₂ y) = g (mk R x) (mk R₂ y)) : f = g :=
  linearMap_ext fun x ↦ linearMap_ext fun y ↦ h x y

variable (R)

/-- The linear map out of the reduced free module extending a function `f` that vanishes at the
basepoint, sending the generator of `x` to `f x`. -/
def lift {M : Type*} [AddCommGroup M] [Module R M] (f : α → M) (hf : f a = 0) :
    ReducedFreeModule R a →ₗ[R] M :=
  Submodule.liftQ _ (Finsupp.linearCombination R f) <|
    (Submodule.span_singleton_le_iff_mem _ _).2 <| LinearMap.mem_ker.2 <| by simp [hf]

@[simp]
lemma lift_mk {M : Type*} [AddCommGroup M] [Module R M] (f : α → M) (hf : f a = 0) (x : α) :
    lift R f hf (mk R x) = f x := by
  simp [lift, mk]

/-- A linear map out of the reduced free module is the lift of its values on generators. -/
lemma lift_unique {M : Type*} [AddCommGroup M] [Module R M] (f : α → M) (hf : f a = 0)
    (g : ReducedFreeModule R a →ₗ[R] M) (h : ∀ x, g (mk R x) = f x) : g = lift R f hf :=
  linearMap_ext fun x ↦ by simp [h]

/-- The linear map of reduced free modules induced by a based map `f`, sending the generator of
`x` to the generator of `f x`. -/
def map (f : α → β) (hf : f a = b) : ReducedFreeModule R a →ₗ[R] ReducedFreeModule R b :=
  Submodule.mapQ _ _ (Finsupp.lmapDomain R R f) <| (Submodule.span_singleton_le_iff_mem _ _).2 <|
    Submodule.mem_comap.2 <| by simp [hf]

@[simp]
lemma map_mk (f : α → β) (hf : f a = b) (x : α) : map R f hf (mk R x) = mk R (f x) := by
  simp [map, mk]

@[simp]
lemma map_id : map R (fun x : α ↦ x) rfl = LinearMap.id (M := ReducedFreeModule R a) :=
  linearMap_ext fun _ ↦ by simp

lemma map_comp (f : α → β) (g : β → γ) (hf : f a = b) (hg : g b = c) :
    map R (g ∘ f) (by simp [hf, hg]) = map R g hg ∘ₗ map R f hf :=
  linearMap_ext fun _ ↦ by simp

@[simp]
lemma map_map (f : α → β) (g : β → γ) (hf : f a = b) (hg : g b = c) (v : ReducedFreeModule R a) :
    map R g hg (map R f hf v) = map R (fun x ↦ g (f x)) (by simp [hf, hg]) v := by
  induction v using induction_on <;> simp_all

section MapRing

variable {R} {S T : Type*} [Ring S] [Ring T]

/-- The `φ`-semilinear map of reduced free modules induced by a ring homomorphism `φ : R →+* S`,
sending the generator of `x` over `R` to the generator of `x` over `S`. -/
def mapRing (φ : R →+* S) : ReducedFreeModule R a →ₛₗ[φ] ReducedFreeModule S a :=
  Submodule.mapQ _ _ (Finsupp.mapRange.linearMap φ.toSemilinearMap) <|
    (Submodule.span_singleton_le_iff_mem _ _).2 <| Submodule.mem_comap.2 <| by
      simp [Submodule.mem_span_singleton_self]

@[simp]
lemma mapRing_mk (φ : R →+* S) (x : α) : mapRing φ (mk R (a := a) x) = mk S x := by
  simp [mapRing, mk]

@[simp]
lemma mapRing_id : mapRing (a := a) (RingHom.id R) = LinearMap.id :=
  linearMap_ext fun _ ↦ by simp

lemma mapRing_comp {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} [RingHomCompTriple φ ψ χ] :
    mapRing (a := a) χ = (mapRing ψ).comp (mapRing φ) :=
  linearMap_ext fun _ ↦ by simp

@[simp]
lemma mapRing_mapRing (φ : R →+* S) (ψ : S →+* T) (v : ReducedFreeModule R a) :
    mapRing ψ (mapRing φ v) = mapRing (ψ.comp φ) v := by
  induction v using induction_on <;> simp_all

lemma mapRing_comp_map (φ : R →+* S) (f : α → β) (hf : f a = b) :
    (mapRing (a := b) φ).comp (map R f hf) = (map S f hf).comp (mapRing (a := a) φ) :=
  linearMap_ext fun _ ↦ by simp

lemma mapRing_map (φ : R →+* S) (f : α → β) (hf : f a = b) (v : ReducedFreeModule R a) :
    mapRing φ (map R f hf v) = map S f hf (mapRing φ v) :=
  LinearMap.congr_fun (mapRing_comp_map φ f hf) v

end MapRing

end Ring

section CommRing

variable (R : Type*) [CommRing R] {α : Type u} {β : Type v} {γ : Type w} {a : α} {b : β} {c : γ}

/-- The bilinear map out of the free modules on `α` and `β` sending the pair of generators of `x`
and `y` to the generator of `p x y`. -/
private def map₂Aux (p : α → β → γ) :
    (α →₀ R) →ₗ[R] (β →₀ R) →ₗ[R] ReducedFreeModule R c :=
  Finsupp.linearCombination R fun x ↦ Finsupp.linearCombination R fun y ↦ mk R (p x y)

@[simp]
private lemma map₂Aux_single_single (p : α → β → γ) (x : α) (y : β) :
    map₂Aux R (c := c) p (Finsupp.single x 1) (Finsupp.single y 1) = mk R (p x y) := by
  simp [map₂Aux]

/-- The bilinear map of reduced free modules induced by a function `p` of two variables sending
the axes `{a} × β` and `α × {b}` to the basepoint `c`: it sends the generators of `x` and `y` to
the generator of `p x y`. -/
def map₂ (p : α → β → γ) (hl : ∀ y, p a y = c) (hr : ∀ x, p x b = c) :
    ReducedFreeModule R a →ₗ[R] ReducedFreeModule R b →ₗ[R] ReducedFreeModule R c :=
  LinearMap.liftQ₂ _ _ (map₂Aux R p)
    ((Submodule.span_singleton_le_iff_mem _ _).2 <| LinearMap.mem_ker.2 <|
      Finsupp.lhom_ext' fun y ↦ LinearMap.ext_ring <| by simp [hl])
    ((Submodule.span_singleton_le_iff_mem _ _).2 <| LinearMap.mem_ker.2 <|
      Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring <| by simp [hr])

lemma map₂_mk_mk (p : α → β → γ) (hl : ∀ y, p a y = c) (hr : ∀ x, p x b = c) (x : α) (y : β) :
    map₂ R p hl hr (mk R x) (mk R y) = mk R (p x y) := by
  simp [map₂, mk]

/-- The external product with a generator in the first variable is the based map `p x`. -/
@[simp]
lemma map₂_mk_left (p : α → β → γ) (hl : ∀ y, p a y = c) (hr : ∀ x, p x b = c) (x : α)
    (w : ReducedFreeModule R b) :
    map₂ R p hl hr (mk R x) w = map R (p x) (hr x) w := by
  induction w using induction_on with
  | zero => simp
  | add w w' hw hw' => simp_all
  | smul_mk s y => simp [map₂_mk_mk]

/-- The external product with a generator in the second variable is the based map `(p · y)`. -/
@[simp]
lemma map₂_mk_right (p : α → β → γ) (hl : ∀ y, p a y = c) (hr : ∀ x, p x b = c)
    (v : ReducedFreeModule R a) (y : β) :
    map₂ R p hl hr v (mk R y) = map R (p · y) (hl y) v := by
  induction v using induction_on with
  | zero => simp
  | add v v' hv hv' => simp_all
  | smul_mk r x => simp

/-- Applying a based map after the external product `map₂` composes it into the function of two
variables. -/
lemma map_map₂ {δ : Type*} {d : δ} (p : α → β → γ) (hl : ∀ y, p a y = c) (hr : ∀ x, p x b = c)
    (f : γ → δ) (hf : f c = d) (v : ReducedFreeModule R a) (w : ReducedFreeModule R b) :
    map R f hf (map₂ R p hl hr v w) =
      map₂ R (fun x y ↦ f (p x y)) (by simp [hl, hf]) (by simp [hr, hf]) v w :=
  LinearMap.congr_fun₂ (f := (map₂ R p hl hr).compr₂ (map R f hf))
    (linearMap_ext₂ fun x y ↦ by simp) v w

/-- Applying a based map to the first variable of the external product `map₂` composes it into the
function of two variables. -/
lemma map₂_map_left {α' : Type*} {a' : α'} (p : α → β → γ) (hl : ∀ y, p a y = c)
    (hr : ∀ x, p x b = c) (f : α' → α) (hf : f a' = a) (v : ReducedFreeModule R a')
    (w : ReducedFreeModule R b) :
    map₂ R p hl hr (map R f hf v) w =
      map₂ R (fun x y ↦ p (f x) y) (by simp [hf, hl]) (by simp [hr]) v w :=
  LinearMap.congr_fun₂ (f := (map₂ R p hl hr).comp (map R f hf))
    (linearMap_ext₂ fun x y ↦ by simp) v w

/-- Applying a based map to the second variable of the external product `map₂` composes it into
the function of two variables. -/
lemma map₂_map_right {β' : Type*} {b' : β'} (p : α → β → γ) (hl : ∀ y, p a y = c)
    (hr : ∀ x, p x b = c) (g : β' → β) (hg : g b' = b) (v : ReducedFreeModule R a)
    (w : ReducedFreeModule R b') :
    map₂ R p hl hr v (map R g hg w) =
      map₂ R (fun x y ↦ p x (g y)) (by simp [hl]) (by simp [hg, hr]) v w :=
  LinearMap.congr_fun₂ (f := (map₂ R p hl hr).compl₂ (map R g hg))
    (linearMap_ext₂ fun x y ↦ by simp) v w

/-- Associativity of the external product `map₂`, for functions of two variables satisfying the
corresponding associativity law. -/
lemma map₂_assoc {δ ε ζ : Type*} {d : δ} {e : ε} {z : ζ} (p : α → β → γ) (hpl : ∀ y, p a y = c)
    (hpr : ∀ x, p x b = c) (q : γ → δ → ε) (hql : ∀ w, q c w = e) (hqr : ∀ v, q v d = e)
    (p' : β → δ → ζ) (hpl' : ∀ w, p' b w = z) (hpr' : ∀ y, p' y d = z) (q' : α → ζ → ε)
    (hql' : ∀ t, q' a t = e) (hqr' : ∀ x, q' x z = e)
    (h : ∀ x y w, q (p x y) w = q' x (p' y w)) (u : ReducedFreeModule R a)
    (v : ReducedFreeModule R b) (w : ReducedFreeModule R d) :
    map₂ R q hql hqr (map₂ R p hpl hpr u v) w =
      map₂ R q' hql' hqr' u (map₂ R p' hpl' hpr' v w) := by
  refine LinearMap.congr_fun₂ (f := (map₂ R p hpl hpr).compr₂ ((map₂ R q hql hqr).flip w))
    (g := (map₂ R q' hql' hqr').compl₂ ((map₂ R p' hpl' hpr').flip w))
    (linearMap_ext₂ fun x y ↦ ?_) u v
  simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.flip_apply, map₂_mk_left,
    map_map]
  congr 1
  ext t
  simp [h]

/-- Exchanging the two variables of the external product `map₂`. -/
lemma map₂_swap (p : α → β → γ) (hl : ∀ y, p a y = c) (hr : ∀ x, p x b = c)
    (v : ReducedFreeModule R a) (w : ReducedFreeModule R b) :
    map₂ R p hl hr v w = map₂ R (fun y x ↦ p x y) hr hl w v :=
  LinearMap.congr_fun₂ (g := (map₂ R (fun y x ↦ p x y) hr hl).flip)
    (linearMap_ext₂ fun x y ↦ by simp) v w

variable {R} in
/-- Changing coefficients along `φ : R →+* S` commutes with the external product `map₂`. -/
lemma mapRing_map₂ {S : Type*} [CommRing S] (φ : R →+* S) (p : α → β → γ)
    (hl : ∀ y, p a y = c) (hr : ∀ x, p x b = c)
    (v : ReducedFreeModule R a) (w : ReducedFreeModule R b) :
    mapRing φ (map₂ R p hl hr v w) = map₂ S p hl hr (mapRing φ v) (mapRing φ w) := by
  induction v using induction_on with
  | zero => simp
  | add v v' hv hv' => simp [hv, hv']
  | smul_mk r x => simp [mapRing_map]

end CommRing

end ReducedFreeModule

end

end TauCeti
