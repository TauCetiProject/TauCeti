/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration.MappingPath

/-!
# Homotopy pullbacks of topological spaces

Given a cospan `A --f--> B <--g-- C` of continuous maps, the **homotopy pullback**
`TauCeti.HomotopyPullback f g` is the double mapping-path space

$$A \times_B^h C =
  \{(a, c, \gamma) \in A \times C \times C(I, B) \mid \gamma(0) = f(a),\ \gamma(1) = g(c)\}$$

equipped with the subspace topology from `A × C × C(I, B)`, where `C(I, B)` carries the
compact-open topology. No compact-generation, connectedness, nonemptiness, or base-point hypothesis
is imposed, and `A`, `B`, `C` may live in independent universes.

It comes with continuous projections `fst : C(HomotopyPullback f g, A)` and
`snd : C(HomotopyPullback f g, C)` and a universal homotopy
`homotopy f g : (f.comp (fst f g)).Homotopy (g.comp (snd f g))`. Continuous maps
`X → HomotopyPullback f g` correspond bijectively (`HomotopyPullback.liftEquiv`) to triples
`(α : C(X, A), β : C(X, C), H : (f.comp α).Homotopy (g.comp β))`. In particular, the strict
pullback `f.Pullback g` maps into `HomotopyPullback f g` by constant paths
(`HomotopyPullback.ofPullback`).

Factoring through the mapping-path replacement identifies `HomotopyPullback f g` over `C` with the
strict pullback of the Hurewicz fibration `MappingPathSpace.endpoint f` along `g`
(`HomotopyPullback.pullbackEndpointLeftHomeomorph`). Consequently:

* both projections `fst` and `snd` are Hurewicz fibrations in every lifting universe
  (`HomotopyPullback.isHurewiczFibration_fst`, `HomotopyPullback.isHurewiczFibration_snd`);
* the strict fibre of `snd f g` over `c : C` is homeomorphic to `MappingPathFiber f (g c)`
  (`HomotopyPullback.sndFiberHomeomorph`), and symmetrically for `fst f g`;
* when `p` is a Hurewicz fibration, the constant-path inclusion `ofPullback p g` from the strict
  pullback `p.Pullback g` to `HomotopyPullback p g` is a fibre homotopy equivalence over `C`
  (`IsHurewiczFibration.pullbackHomotopyPullbackLeftFiberHomotopyEquiv`), and symmetrically when the
  right leg is a Hurewicz fibration.

Specializing `f` or `g` recovers `MappingPathSpace`, `MappingPathFiber`, `Path b₀ b₁`, and `Ω B b`
up to canonical homeomorphism.

## Main definitions and results

* `TauCeti.HomotopyPullback f g`: the homotopy pullback of `f : C(A, B)` and `g : C(C, B)`, with
  `fst`, `snd`, `pathMap`, `path`, and universal `homotopy`.
* `TauCeti.HomotopyPullback.lift`, `TauCeti.HomotopyPullback.liftEquiv`,
  `TauCeti.HomotopyPullback.liftStrict`, `TauCeti.HomotopyPullback.ofPullback`: universal property
  and constant-path comparison from the strict pullback.
* `TauCeti.HomotopyPullback.swapHomeomorph`: symmetry `HomotopyPullback f g ≃ₜ HomotopyPullback g f`
  reversing paths.
* `TauCeti.HomotopyPullback.pullbackEndpointLeftHomeomorph`,
  `TauCeti.HomotopyPullback.isHurewiczFibration_snd`,
  `TauCeti.HomotopyPullback.isHurewiczFibration_fst`,
  `TauCeti.HomotopyPullback.sndFiberHomeomorph`, `TauCeti.HomotopyPullback.fstFiberHomeomorph`:
  pullback-of-replacement factorization, Hurewicz fibration projections, and strict fibres.
* `TauCeti.HomotopyPullback.idRightHomeomorph`, `TauCeti.HomotopyPullback.idLeftHomeomorph`,
  `TauCeti.HomotopyPullback.constRightProdHomeomorph`,
  `TauCeti.HomotopyPullback.constRightHomeomorphOfUnique`,
  `TauCeti.HomotopyPullback.constLeftHomeomorphOfUnique`,
  `TauCeti.HomotopyPullback.constHomeomorphPath`,
  `TauCeti.HomotopyPullback.constHomeomorphLoopSpace`: canonical homeomorphisms for identity and
  constant legs.
* `TauCeti.HomotopyPullback.map`: functoriality in strictly commuting morphisms of cospans.
* `TauCeti.IsHurewiczFibration.pullbackHomotopyPullbackLeftFiberHomotopyEquiv`,
  `TauCeti.IsHurewiczFibration.pullbackHomotopyPullbackRightFiberHomotopyEquiv`: `ofPullback` is a
  fibre homotopy equivalence when one leg is a Hurewicz fibration.

## References

* D. Quillen, *Higher Algebraic K-Theory: I*, Lecture Notes in Mathematics 341, Springer, 1973, §1.
* M. Mather, *Pull-backs in homotopy theory*, Canad. J. Math. **28** (1976), 225–263.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public section

open Topology Topology.Homotopy unitInterval

universe u v w u' v' w'

namespace TauCeti

/-- The **homotopy pullback** of `f : C(A, B)` and `g : C(C, B)`: triples `(a, c, γ)` in
`A × C × C(I, B)` where `γ` is a path in `B` from `f a` to `g c`, with the subspace compact-open
topology. -/
abbrev HomotopyPullback {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(C, B)) :=
  {p : A × C × C(I, B) // p.2.2 0 = f p.1 ∧ p.2.2 1 = g p.2.1}

namespace HomotopyPullback

section Basic

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  (f : C(A, B)) (g : C(C, B))

/-- Construct a point of `HomotopyPullback f g` from points `a : A`, `c : C`, and a path
`γ : Path (f a) (g c)`. -/
def mk' {f : C(A, B)} {g : C(C, B)} (a : A) (c : C) (γ : Path (f a) (g c)) :
    HomotopyPullback f g :=
  ⟨(a, c, γ.toContinuousMap), γ.source, γ.target⟩

@[simp]
theorem mk'_val {f : C(A, B)} {g : C(C, B)} (a : A) (c : C) (γ : Path (f a) (g c)) :
    (mk' a c γ : HomotopyPullback f g).val = (a, c, γ.toContinuousMap) :=
  (rfl)

/-- Projection `HomotopyPullback f g → A` to the first leg. -/
def fst : C(HomotopyPullback f g, A) :=
  ⟨fun p ↦ p.val.1, continuous_subtype_val.fst⟩

/-- Projection `HomotopyPullback f g → C` to the second leg. -/
def snd : C(HomotopyPullback f g, C) :=
  ⟨fun p ↦ p.val.2.1, continuous_subtype_val.snd.fst⟩

/-- Projection `HomotopyPullback f g → C(I, B)` forgetting the endpoints and keeping the path. -/
def pathMap : C(HomotopyPullback f g, C(I, B)) :=
  ⟨fun p ↦ p.val.2.2, continuous_subtype_val.snd.snd⟩

@[simp]
theorem fst_apply (p : HomotopyPullback f g) : fst f g p = p.val.1 := (rfl)

@[simp]
theorem snd_apply (p : HomotopyPullback f g) : snd f g p = p.val.2.1 := (rfl)

@[simp]
theorem pathMap_apply (p : HomotopyPullback f g) : pathMap f g p = p.val.2.2 := (rfl)

theorem pathMap_zero (p : HomotopyPullback f g) : pathMap f g p 0 = f (fst f g p) := p.property.1

theorem pathMap_one (p : HomotopyPullback f g) : pathMap f g p 1 = g (snd f g p) := p.property.2

/-- Two points of `HomotopyPullback f g` are equal iff their `fst`, `snd`, and path evaluations
agree. -/
@[ext]
theorem ext {f : C(A, B)} {g : C(C, B)} {p q : HomotopyPullback f g}
    (h₁ : fst f g p = fst f g q) (h₂ : snd f g p = snd f g q)
    (h₃ : ∀ t : I, pathMap f g p t = pathMap f g q t) : p = q :=
  Subtype.ext <| Prod.ext h₁ <| Prod.ext h₂ <| ContinuousMap.ext h₃

/-- The path component of a point `p : HomotopyPullback f g` as a `Path` from `f p.val.1` to
`g p.val.2.1`. -/
def path {f : C(A, B)} {g : C(C, B)} (p : HomotopyPullback f g) :
    Path (f p.val.1) (g p.val.2.1) :=
  ⟨p.val.2.2, p.property.1, p.property.2⟩

@[simp]
theorem path_apply {f : C(A, B)} {g : C(C, B)} (p : HomotopyPullback f g) (t : I) :
    path p t = pathMap f g p t :=
  (rfl)

@[simp]
theorem toContinuousMap_path {f : C(A, B)} {g : C(C, B)} (p : HomotopyPullback f g) :
    (path p).toContinuousMap = pathMap f g p :=
  (rfl)

/-- The universal homotopy from `f ∘ fst` to `g ∘ snd` on `HomotopyPullback f g`. -/
def homotopy : (f.comp (fst f g)).Homotopy (g.comp (snd f g)) where
  toFun q := q.2.val.2.2 q.1
  continuous_toFun := continuous_subtype_val.snd.snd.comp continuous_snd |>.eval continuous_fst
  map_zero_left p := p.property.1
  map_one_left p := p.property.2

@[simp]
theorem homotopy_apply (t : I) (p : HomotopyPullback f g) :
    homotopy f g (t, p) = pathMap f g p t :=
  (rfl)

end Basic

/-! ### Universal property and comparison from the strict pullback -/

section UniversalProperty

variable {A : Type u} {B : Type v} {C : Type w} {X : Type u'}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace X]
  {f : C(A, B)} {g : C(C, B)}

/-- **Universal property of the homotopy pullback.** A pair of continuous maps `α : C(X, A)`,
`β : C(X, C)` together with a homotopy `H : (f.comp α).Homotopy (g.comp β)` induces a continuous
map `lift α β H : C(X, HomotopyPullback f g)`. -/
def lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    C(X, HomotopyPullback f g) where
  toFun x := ⟨(α x, β x, (H.evalAt x).toContinuousMap), H.apply_zero x, H.apply_one x⟩
  continuous_toFun := by
    refine (α.continuous.prodMk <| β.continuous.prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact H.continuous.comp (continuous_snd.prodMk continuous_fst)

@[simp]
theorem lift_val (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) (x : X) :
    (lift α β H x).val = (α x, β x, (H.evalAt x).toContinuousMap) :=
  (rfl)

@[simp]
theorem fst_comp_lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    (fst f g).comp (lift α β H) = α := by
  ext : 1; rfl

@[simp]
theorem snd_comp_lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    (snd f g).comp (lift α β H) = β := by
  ext : 1; rfl

@[simp]
theorem homotopy_comp_lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    ((homotopy f g).compContinuousMap (lift α β H)).cast
      (congrArg f.comp (fst_comp_lift α β H)) (congrArg g.comp (snd_comp_lift α β H)) = H := by
  ext ⟨t, x⟩ : 1
  rfl

/-- Any continuous map `φ : C(X, HomotopyPullback f g)` is uniquely reconstructed as `lift` from
its two projections and the pulled-back universal homotopy. -/
theorem eq_lift (φ : C(X, HomotopyPullback f g)) :
    φ = lift ((fst f g).comp φ) ((snd f g).comp φ)
      (((homotopy f g).compContinuousMap φ).cast rfl rfl) := by
  ext x : 1
  exact ext rfl rfl fun _ ↦ rfl

private theorem liftEquiv_right_inv
    (t : Σ (α : C(X, A)) (β : C(X, C)), (f.comp α).Homotopy (g.comp β)) :
    (⟨(fst f g).comp (lift t.1 t.2.1 t.2.2), (snd f g).comp (lift t.1 t.2.1 t.2.2),
      ((homotopy f g).compContinuousMap (lift t.1 t.2.1 t.2.2)).cast rfl rfl⟩ :
      Σ (α : C(X, A)) (β : C(X, C)), (f.comp α).Homotopy (g.comp β)) = t := by
  rcases t with ⟨α, β, H⟩
  have hα : (fst f g).comp (lift α β H) = α := fst_comp_lift α β H
  have hβ : (snd f g).comp (lift α β H) = β := snd_comp_lift α β H
  refine Sigma.ext hα ?_
  cases hα
  refine heq_of_eq (Sigma.ext hβ ?_)
  cases hβ
  refine heq_of_eq ?_
  ext ⟨s, x⟩ : 1
  rfl

/-- Continuous maps `X → HomotopyPullback f g` correspond bijectively to homotopy-commutative cones
`(α : C(X, A), β : C(X, C), H : (f.comp α).Homotopy (g.comp β))`. -/
def liftEquiv (X : Type u') [TopologicalSpace X] (f : C(A, B)) (g : C(C, B)) :
    C(X, HomotopyPullback f g) ≃
      Σ (α : C(X, A)) (β : C(X, C)), (f.comp α).Homotopy (g.comp β) where
  toFun φ := ⟨(fst f g).comp φ, (snd f g).comp φ,
    ((homotopy f g).compContinuousMap φ).cast rfl rfl⟩
  invFun t := lift t.1 t.2.1 t.2.2
  left_inv φ := (eq_lift φ).symm
  right_inv := liftEquiv_right_inv

@[simp]
theorem liftEquiv_apply (φ : C(X, HomotopyPullback f g)) :
    liftEquiv X f g φ =
      ⟨(fst f g).comp φ, (snd f g).comp φ, ((homotopy f g).compContinuousMap φ).cast rfl rfl⟩ :=
  (rfl)

@[simp]
theorem liftEquiv_symm_apply
    (t : Σ (α : C(X, A)) (β : C(X, C)), (f.comp α).Homotopy (g.comp β)) :
    (liftEquiv X f g).symm t = lift t.1 t.2.1 t.2.2 :=
  (rfl)

/-- Lift a strictly commuting cone `f ∘ α = g ∘ β` to `HomotopyPullback f g` using constant
paths. -/
def liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    C(X, HomotopyPullback f g) :=
  lift α β ((ContinuousMap.Homotopy.refl (f.comp α)).cast rfl h)

@[simp]
theorem liftStrict_val {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) (x : X) :
    (liftStrict h x).val = (α x, β x, ContinuousMap.const I (f (α x))) :=
  Prod.ext rfl (Prod.ext rfl (ContinuousMap.ext fun _ ↦ rfl))

@[simp]
theorem fst_comp_liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    (fst f g).comp (liftStrict h) = α :=
  fst_comp_lift _ _ _

@[simp]
theorem snd_comp_liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    (snd f g).comp (liftStrict h) = β :=
  snd_comp_lift _ _ _

/-- Precomposing `liftStrict` with a cone morphism `φ` yields `liftStrict` on the pulled-back
strictly commuting cone. -/
theorem liftStrict_comp {Y : Type v'} [TopologicalSpace Y] {α : C(X, A)} {β : C(X, C)}
    (h : f.comp α = g.comp β) {α' : C(Y, A)} {β' : C(Y, C)} (h' : f.comp α' = g.comp β')
    (φ : C(Y, X)) (hα : α.comp φ = α') (hβ : β.comp φ = β') :
    (liftStrict h).comp φ = liftStrict h' := by
  ext y : 1
  have hαy : α (φ y) = α' y := ContinuousMap.congr_fun hα y
  have hβy : β (φ y) = β' y := ContinuousMap.congr_fun hβ y
  exact ext (by simpa using hαy) (by simpa using hβy) fun _ ↦ by simpa using congrArg f hαy

/-- The canonical comparison map from the strict pullback `f.Pullback g` to `HomotopyPullback f g`
sending `(a, c)` with `f a = g c` to `(a, c, const I (f a))`. -/
def ofPullback (f : C(A, B)) (g : C(C, B)) :
    C((⇑f).Pullback ⇑g, HomotopyPullback f g) :=
  liftStrict (α := ContinuousMap.pullbackFst ⇑f ⇑g) (β := ContinuousMap.pullbackSnd ⇑f ⇑g)
    (ContinuousMap.ext fun x ↦ by
      simpa [Function.Pullback.fst, Function.Pullback.snd] using x.2)

@[simp]
theorem ofPullback_val (f : C(A, B)) (g : C(C, B)) (x : (⇑f).Pullback ⇑g) :
    (ofPullback f g x).val = (x.1.1, x.1.2, ContinuousMap.const I (f x.1.1)) := by
  simp [ofPullback, Function.Pullback.fst, Function.Pullback.snd]

@[simp]
theorem fst_comp_ofPullback (f : C(A, B)) (g : C(C, B)) :
    (fst f g).comp (ofPullback f g) = ContinuousMap.pullbackFst ⇑f ⇑g :=
  fst_comp_liftStrict _

@[simp]
theorem snd_comp_ofPullback (f : C(A, B)) (g : C(C, B)) :
    (snd f g).comp (ofPullback f g) = ContinuousMap.pullbackSnd ⇑f ⇑g :=
  snd_comp_liftStrict _

theorem pathMap_ofPullback_apply (f : C(A, B)) (g : C(C, B)) (x : (⇑f).Pullback ⇑g) (t : I) :
    pathMap f g (ofPullback f g x) t = f x.1.1 := by
  simp

end UniversalProperty

/-! ### Symmetry -/

section Symmetry

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- Swap the two factors of `HomotopyPullback f g` by reversing the path in `B`. -/
def swap (f : C(A, B)) (g : C(C, B)) :
    C(HomotopyPullback f g, HomotopyPullback g f) where
  toFun p := ⟨(p.val.2.1, p.val.1, p.val.2.2.comp ⟨σ, continuous_symm⟩),
    (congrArg p.val.2.2 symm_zero).trans p.property.2,
    (congrArg p.val.2.2 symm_one).trans p.property.1⟩
  continuous_toFun :=
    (continuous_subtype_val.snd.fst.prodMk <|
      continuous_subtype_val.fst.prodMk <|
        (ContinuousMap.continuous_precomp ⟨σ, continuous_symm⟩).comp
          continuous_subtype_val.snd.snd).subtype_mk _

@[simp]
theorem swap_val (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    (swap f g p).val = (p.val.2.1, p.val.1, p.val.2.2.comp ⟨σ, continuous_symm⟩) :=
  (rfl)

theorem fst_swap (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    fst g f (swap f g p) = snd f g p :=
  (rfl)

theorem snd_swap (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    snd g f (swap f g p) = fst f g p :=
  (rfl)

@[simp]
theorem fst_comp_swap (f : C(A, B)) (g : C(C, B)) :
    (fst g f).comp (swap f g) = snd f g := by
  ext : 1; rfl

@[simp]
theorem snd_comp_swap (f : C(A, B)) (g : C(C, B)) :
    (snd g f).comp (swap f g) = fst f g := by
  ext : 1; rfl

theorem pathMap_swap_apply (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) (t : I) :
    pathMap g f (swap f g p) t = pathMap f g p (σ t) :=
  (rfl)

@[simp]
theorem swap_comp_swap (f : C(A, B)) (g : C(C, B)) :
    (swap g f).comp (swap f g) = .id (HomotopyPullback f g) := by
  ext p : 1
  exact ext rfl rfl fun t ↦ congrArg (pathMap f g p) (symm_symm t)

@[simp]
theorem swap_swap (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    swap g f (swap f g p) = p :=
  ContinuousMap.congr_fun (swap_comp_swap f g) p

/-- **Symmetry of homotopy pullbacks.** Swapping the two legs and reversing the path is a
homeomorphism `HomotopyPullback f g ≃ₜ HomotopyPullback g f`. -/
def swapHomeomorph (f : C(A, B)) (g : C(C, B)) :
    HomotopyPullback f g ≃ₜ HomotopyPullback g f where
  toFun := swap f g
  invFun := swap g f
  left_inv := swap_swap f g
  right_inv := swap_swap g f
  continuous_toFun := (swap f g).continuous
  continuous_invFun := (swap g f).continuous

@[simp]
theorem coe_swapHomeomorph (f : C(A, B)) (g : C(C, B)) :
    (swapHomeomorph f g : C(HomotopyPullback f g, HomotopyPullback g f)) = swap f g :=
  (rfl)

@[simp]
theorem swapHomeomorph_apply (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    swapHomeomorph f g p = swap f g p :=
  (rfl)

@[simp]
theorem swapHomeomorph_symm (f : C(A, B)) (g : C(C, B)) :
    (swapHomeomorph f g).symm = swapHomeomorph g f :=
  (rfl)

@[simp]
theorem swapHomeomorph_trans_swapHomeomorph (f : C(A, B)) (g : C(C, B)) :
    (swapHomeomorph f g).trans (swapHomeomorph g f) =
      Homeomorph.refl (HomotopyPullback f g) := by
  ext : 1; exact swap_swap f g _

@[simp]
theorem swap_comp_lift {X : Type u'} [TopologicalSpace X] {f : C(A, B)} {g : C(C, B)}
    (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    (swap f g).comp (lift α β H) = lift β α H.symm := by
  ext x : 1
  exact ext rfl rfl fun _ ↦ rfl

end Symmetry

/-! ### Pullback-of-replacement factorization, fibrations, and fibres -/

section Fibration

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- `HomotopyPullback f g` is homeomorphic over `C` to the strict pullback along `g` of the
mapping-path endpoint fibration `MappingPathSpace.endpoint f`. -/
def pullbackEndpointLeftHomeomorph (f : C(A, B)) (g : C(C, B)) :
    HomotopyPullback f g ≃ₜ (⇑g).Pullback ⇑(MappingPathSpace.endpoint f) where
  toFun p := ⟨(p.val.2.1, ⟨(p.val.1, p.val.2.2), p.property.1⟩),
    p.property.2.symm.trans
      (MappingPathSpace.endpoint_apply f ⟨(p.val.1, p.val.2.2), p.property.1⟩).symm⟩
  invFun q := ⟨(q.1.2.val.1, q.1.1, q.1.2.val.2), q.1.2.property,
    (MappingPathSpace.endpoint_apply f q.1.2).symm.trans q.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.snd.fst.prodMk <|
      (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.snd).subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.snd.subtype_val.fst.prodMk <|
      continuous_subtype_val.fst.prodMk
        continuous_subtype_val.snd.subtype_val.snd).subtype_mk _

@[simp]
theorem pullbackEndpointLeftHomeomorph_fst (f : C(A, B)) (g : C(C, B))
    (p : HomotopyPullback f g) :
    (pullbackEndpointLeftHomeomorph f g p).1.1 = snd f g p :=
  (rfl)

@[simp]
theorem pullbackEndpointLeftHomeomorph_snd_val (f : C(A, B)) (g : C(C, B))
    (p : HomotopyPullback f g) :
    (pullbackEndpointLeftHomeomorph f g p).1.2.val = (fst f g p, pathMap f g p) :=
  (rfl)

@[simp]
theorem pullbackEndpointLeftHomeomorph_symm_val (f : C(A, B)) (g : C(C, B))
    (q : (⇑g).Pullback ⇑(MappingPathSpace.endpoint f)) :
    ((pullbackEndpointLeftHomeomorph f g).symm q).val = (q.1.2.val.1, q.1.1, q.1.2.val.2) :=
  (rfl)

@[simp]
theorem pullbackFst_comp_pullbackEndpointLeftHomeomorph (f : C(A, B)) (g : C(C, B)) :
    (ContinuousMap.pullbackFst (⇑g) ⇑(MappingPathSpace.endpoint f)).comp
      (pullbackEndpointLeftHomeomorph f g :
        C(HomotopyPullback f g, (⇑g).Pullback ⇑(MappingPathSpace.endpoint f))) = snd f g := by
  ext p : 1
  simp [Function.Pullback.fst]

/-- **The second projection of any homotopy pullback is a Hurewicz fibration** in every lifting
universe, as the pullback along `g` of `MappingPathSpace.endpoint f` precomposed with
`pullbackEndpointLeftHomeomorph f g`. -/
theorem isHurewiczFibration_snd (f : C(A, B)) (g : C(C, B)) :
    IsHurewiczFibration.{u'} (snd f g) := by
  convert ((MappingPathSpace.isHurewiczFibration_endpoint f).pullback g).comp_homeomorph
    (pullbackEndpointLeftHomeomorph f g) using 1
  ext p
  rfl

/-- **The first projection of any homotopy pullback is a Hurewicz fibration** in every lifting
universe. -/
theorem isHurewiczFibration_fst (f : C(A, B)) (g : C(C, B)) :
    IsHurewiczFibration.{u'} (fst f g) := by
  convert (isHurewiczFibration_snd g f).comp_homeomorph (swapHomeomorph f g) using 1
  ext p
  rfl

/-- The strict fibre of `snd f g` over `c : C` is canonically homeomorphic to
`MappingPathFiber f (g c)`. -/
def sndFiberHomeomorph (f : C(A, B)) (g : C(C, B)) (c : C) :
    (snd f g) ⁻¹' {c} ≃ₜ MappingPathFiber f (g c) where
  toFun x := ⟨(x.1.val.1, x.1.val.2.2), x.1.property.1,
    x.1.property.2.trans (congrArg g x.2)⟩
  invFun p := ⟨⟨(p.val.1, c, p.val.2), p.property.1, p.property.2⟩, rfl⟩
  left_inv x := Subtype.ext <| ext rfl x.2.symm fun _ ↦ rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).fst.prodMk
      (continuous_subtype_val.comp continuous_subtype_val).snd.snd).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.fst.prodMk
      (continuous_const.prodMk continuous_subtype_val.snd)).subtype_mk _).subtype_mk _

@[simp]
theorem sndFiberHomeomorph_val (f : C(A, B)) (g : C(C, B)) (c : C) (x : (snd f g) ⁻¹' {c}) :
    (sndFiberHomeomorph f g c x).val = (fst f g x.1, pathMap f g x.1) :=
  (rfl)

@[simp]
theorem sndFiberHomeomorph_symm_val (f : C(A, B)) (g : C(C, B)) (c : C)
    (p : MappingPathFiber f (g c)) :
    (((sndFiberHomeomorph f g c).symm p).1 : HomotopyPullback f g).val =
      (p.val.1, c, p.val.2) :=
  (rfl)

/-- The strict fibre of `fst f g` over `a : A` is canonically homeomorphic to
`MappingPathFiber g (f a)` by reversing paths. -/
def fstFiberHomeomorph (f : C(A, B)) (g : C(C, B)) (a : A) :
    (fst f g) ⁻¹' {a} ≃ₜ MappingPathFiber g (f a) :=
  ((swapHomeomorph f g).sets rfl).trans (sndFiberHomeomorph g f a)

@[simp]
theorem fstFiberHomeomorph_val_fst (f : C(A, B)) (g : C(C, B)) (a : A) (x : (fst f g) ⁻¹' {a}) :
    (fstFiberHomeomorph f g a x).val.1 = snd f g x.1 :=
  (rfl)

@[simp]
theorem fstFiberHomeomorph_val_snd_apply (f : C(A, B)) (g : C(C, B)) (a : A)
    (x : (fst f g) ⁻¹' {a}) (t : I) :
    (fstFiberHomeomorph f g a x).val.2 t = pathMap f g x.1 (σ t) :=
  (rfl)

@[simp]
theorem fstFiberHomeomorph_symm_val (f : C(A, B)) (g : C(C, B)) (a : A)
    (p : MappingPathFiber g (f a)) :
    (((fstFiberHomeomorph f g a).symm p).1 : HomotopyPullback f g).val =
      (a, p.val.1, p.val.2.comp ⟨σ, continuous_symm⟩) :=
  (rfl)

end Fibration

/-! ### Special cases: identity and constant legs -/

section SpecialCases

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- `HomotopyPullback f (.id B)` is homeomorphic to `MappingPathSpace f`, since `c = γ 1` is
uniquely determined by the path. -/
def idRightHomeomorph (f : C(A, B)) :
    HomotopyPullback f (.id B) ≃ₜ MappingPathSpace f where
  toFun p := ⟨(p.val.1, p.val.2.2), p.property.1⟩
  invFun q := ⟨(q.val.1, MappingPathSpace.endpoint f q, q.val.2), q.property,
    (MappingPathSpace.endpoint_apply f q).symm⟩
  left_inv p := ext rfl ((MappingPathSpace.endpoint_apply f _).trans p.property.2) fun _ ↦ rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.snd).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.fst.prodMk <|
      (MappingPathSpace.endpoint f).continuous.prodMk continuous_subtype_val.snd).subtype_mk _

@[simp]
theorem idRightHomeomorph_val (f : C(A, B)) (p : HomotopyPullback f (.id B)) :
    (idRightHomeomorph f p).val = (fst f (.id B) p, pathMap f (.id B) p) :=
  (rfl)

@[simp]
theorem idRightHomeomorph_symm_val (f : C(A, B)) (q : MappingPathSpace f) :
    ((idRightHomeomorph f).symm q).val =
      (q.val.1, MappingPathSpace.endpoint f q, q.val.2) :=
  (rfl)

/-- `HomotopyPullback (.id B) g` is homeomorphic to `MappingPathSpace g` via path reversal. -/
def idLeftHomeomorph (g : C(C, B)) :
    HomotopyPullback (.id B) g ≃ₜ MappingPathSpace g :=
  (swapHomeomorph (.id B) g).trans (idRightHomeomorph g)

@[simp]
theorem idLeftHomeomorph_val (g : C(C, B)) (p : HomotopyPullback (.id B) g) :
    (idLeftHomeomorph g p).val =
      (snd (.id B) g p, (pathMap (.id B) g p).comp ⟨σ, continuous_symm⟩) :=
  (rfl)

@[simp]
theorem idLeftHomeomorph_symm_val (g : C(C, B)) (q : MappingPathSpace g) :
    ((idLeftHomeomorph g).symm q).val =
      (MappingPathSpace.endpoint g q, q.val.1, q.val.2.comp ⟨σ, continuous_symm⟩) :=
  (rfl)

/-- `HomotopyPullback f (.const C b)` splits as `MappingPathFiber f b × C`, since the path endpoint
condition `γ 1 = b` is independent of `c : C`. -/
def constRightProdHomeomorph (f : C(A, B)) (b : B) :
    HomotopyPullback f (.const C b) ≃ₜ MappingPathFiber f b × C where
  toFun p := (⟨(p.val.1, p.val.2.2), p.property.1, p.property.2⟩, p.val.2.1)
  invFun q := ⟨(q.1.val.1, q.2, q.1.val.2), q.1.property.1, q.1.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.snd).subtype_mk _).prodMk
      continuous_subtype_val.snd.fst
  continuous_invFun :=
    ((continuous_subtype_val.fst.comp continuous_fst).prodMk <|
      continuous_snd.prodMk (continuous_subtype_val.snd.comp continuous_fst)).subtype_mk _

@[simp]
theorem constRightProdHomeomorph_fst_val (f : C(A, B)) (b : B)
    (p : HomotopyPullback f (.const C b)) :
    (constRightProdHomeomorph f b p).1.val = (fst f (.const C b) p, pathMap f (.const C b) p) :=
  (rfl)

@[simp]
theorem constRightProdHomeomorph_snd (f : C(A, B)) (b : B)
    (p : HomotopyPullback f (.const C b)) :
    (constRightProdHomeomorph f b p).2 = snd f (.const C b) p :=
  (rfl)

@[simp]
theorem constRightProdHomeomorph_symm_val (f : C(A, B)) (b : B)
    (q : MappingPathFiber f b × C) :
    ((constRightProdHomeomorph f b).symm q).val = (q.1.val.1, q.2, q.1.val.2) :=
  (rfl)

/-- Over a one-point corner `C`, `HomotopyPullback f (.const C b)` is canonically homeomorphic to
`MappingPathFiber f b`. -/
def constRightHomeomorphOfUnique [Unique C] (f : C(A, B)) (b : B) :
    HomotopyPullback f (.const C b) ≃ₜ MappingPathFiber f b :=
  (constRightProdHomeomorph f b).trans (Homeomorph.prodUnique (MappingPathFiber f b) C)

@[simp]
theorem constRightHomeomorphOfUnique_val [Unique C] (f : C(A, B)) (b : B)
    (p : HomotopyPullback f (.const C b)) :
    (constRightHomeomorphOfUnique f b p).val = (fst f (.const C b) p, pathMap f (.const C b) p) :=
  (rfl)

@[simp]
theorem constRightHomeomorphOfUnique_symm_val [Unique C] (f : C(A, B)) (b : B)
    (q : MappingPathFiber f b) :
    ((constRightHomeomorphOfUnique (C := C) f b).symm q).val =
      (q.val.1, default, q.val.2) :=
  (rfl)

/-- Over a one-point left corner `A`, `HomotopyPullback (.const A b) g` is canonically homeomorphic
to `MappingPathFiber g b` via path reversal. -/
def constLeftHomeomorphOfUnique [Unique A] (b : B) (g : C(C, B)) :
    HomotopyPullback (.const A b) g ≃ₜ MappingPathFiber g b :=
  (swapHomeomorph (.const A b) g).trans (constRightHomeomorphOfUnique g b)

@[simp]
theorem constLeftHomeomorphOfUnique_val [Unique A] (b : B) (g : C(C, B))
    (p : HomotopyPullback (.const A b) g) :
    (constLeftHomeomorphOfUnique (A := A) b g p).val =
      (snd (.const A b) g p, (pathMap (.const A b) g p).comp ⟨σ, continuous_symm⟩) :=
  (rfl)

@[simp]
theorem constLeftHomeomorphOfUnique_symm_val [Unique A] (b : B) (g : C(C, B))
    (q : MappingPathFiber g b) :
    ((constLeftHomeomorphOfUnique (A := A) b g).symm q).val =
      (default, q.val.1, q.val.2.comp ⟨σ, continuous_symm⟩) :=
  (rfl)

/-- The homotopy pullback of two point inclusions `Unit → B` at `b₀` and `b₁` is homeomorphic to
`Path b₀ b₁`. -/
def constHomeomorphPath (b₀ b₁ : B) :
    HomotopyPullback (.const Unit b₀) (.const Unit b₁) ≃ₜ Path b₀ b₁ :=
  (constRightHomeomorphOfUnique (.const Unit b₀) b₁).trans
    (mappingPathFiberConstHomeomorphPath b₀ b₁)

@[simp]
theorem constHomeomorphPath_apply (b₀ b₁ : B)
    (p : HomotopyPullback (.const Unit b₀) (.const Unit b₁)) :
    constHomeomorphPath b₀ b₁ p = path p :=
  Path.ext <| funext fun t ↦ mappingPathFiberConstHomeomorphPath_apply b₀ b₁ _ t

@[simp]
theorem constHomeomorphPath_symm_apply (b₀ b₁ : B) (γ : Path b₀ b₁) :
    (constHomeomorphPath b₀ b₁).symm γ = mk' () () γ :=
  (constHomeomorphPath b₀ b₁).symm_apply_eq.mpr <|
    Eq.symm <| (constHomeomorphPath_apply b₀ b₁ _).trans (Path.ext rfl)

/-- The homotopy pullback of a point inclusion `Unit → B` at `b` with itself is homeomorphic to the
based loop space `Ω B b`. -/
abbrev constHomeomorphLoopSpace (b : B) :
    HomotopyPullback (.const Unit b) (.const Unit b) ≃ₜ Ω B b :=
  constHomeomorphPath b b

end SpecialCases

/-! ### Functoriality in maps of cospans -/

section Functoriality

variable {A : Type u} {B : Type v} {C : Type w}
  {A' : Type u'} {B' : Type v'} {C' : Type w'}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace A'] [TopologicalSpace B'] [TopologicalSpace C']
  {f : C(A, B)} {g : C(C, B)} {f' : C(A', B')} {g' : C(C', B')}

/-- A strictly commuting morphism `(a, b, c)` of cospans induces a continuous map on homotopy
pullbacks by acting on the corner points and postcomposing the path with `b`. -/
def map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) :
    C(HomotopyPullback f g, HomotopyPullback f' g') where
  toFun p := ⟨(a p.val.1, c p.val.2.1, b.comp p.val.2.2),
    (congrArg b p.property.1).trans (ContinuousMap.congr_fun hf p.val.1),
    (congrArg b p.property.2).trans (ContinuousMap.congr_fun hg p.val.2.1)⟩
  continuous_toFun :=
    ((a.continuous.comp continuous_subtype_val.fst).prodMk <|
      (c.continuous.comp continuous_subtype_val.snd.fst).prodMk <|
        (ContinuousMap.continuous_postcomp b).comp continuous_subtype_val.snd.snd).subtype_mk _

@[simp]
theorem map_val (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) (p : HomotopyPullback f g) :
    (map a b c hf hg p).val = (a p.val.1, c p.val.2.1, b.comp p.val.2.2) :=
  (rfl)

@[simp]
theorem fst_comp_map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) :
    (fst f' g').comp (map a b c hf hg) = a.comp (fst f g) := by
  ext : 1; rfl

@[simp]
theorem snd_comp_map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) :
    (snd f' g').comp (map a b c hf hg) = c.comp (snd f g) := by
  ext : 1; rfl

@[simp]
theorem map_id (f : C(A, B)) (g : C(C, B)) :
    map (.id A) (.id B) (.id C) ((ContinuousMap.id_comp f).trans (ContinuousMap.comp_id f).symm)
      ((ContinuousMap.id_comp g).trans (ContinuousMap.comp_id g).symm) =
      .id (HomotopyPullback f g) := by
  ext p : 1
  exact ext rfl rfl fun _ ↦ rfl

theorem map_comp {A'' B'' C'' : Type*} [TopologicalSpace A''] [TopologicalSpace B'']
    [TopologicalSpace C''] {f'' : C(A'', B'')} {g'' : C(C'', B'')}
    (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c)
    (a' : C(A', A'')) (b' : C(B', B'')) (c' : C(C', C''))
    (hf' : b'.comp f' = f''.comp a') (hg' : b'.comp g' = g''.comp c') :
    (map a' b' c' hf' hg').comp (map a b c hf hg) =
      map (a'.comp a) (b'.comp b) (c'.comp c)
        (by rw [ContinuousMap.comp_assoc, hf, ← ContinuousMap.comp_assoc, hf',
          ContinuousMap.comp_assoc])
        (by rw [ContinuousMap.comp_assoc, hg, ← ContinuousMap.comp_assoc, hg',
          ContinuousMap.comp_assoc]) := by
  ext p : 1
  exact ext rfl rfl fun _ ↦ rfl

end Functoriality

end HomotopyPullback

/-! ### Comparison with the strict pullback along a Hurewicz fibration -/

namespace IsHurewiczFibration

/-- **Strict vs. homotopy pullback along a Hurewicz fibration (left leg).** When `p : C(A, B)` is
a Hurewicz fibration, the constant-path inclusion `HomotopyPullback.ofPullback p g` from the strict
pullback `p.Pullback g` to `HomotopyPullback p g` is part of a fibre homotopy equivalence over `C`.
-/
noncomputable def pullbackHomotopyPullbackLeftFiberHomotopyEquiv
    {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {p : C(A, B)} (hp : IsHurewiczFibration.{max u v} p) (g : C(C, B)) :
    FiberHomotopyEquiv (ContinuousMap.pullbackSnd ⇑p ⇑g) (HomotopyPullback.snd p g) :=
  let Λ := hp.nonempty_liftingFunction.some
  (FiberHomotopyEquiv.ofHomeomorph (Homeomorph.pullbackComm ⇑p ⇑g)
      (ContinuousMap.pullbackFst_comp_pullbackComm ⇑p ⇑g)).trans
    ((FiberHomotopyEquiv.pullback g Λ.mappingPathFiberHomotopyEquiv).trans
      (FiberHomotopyEquiv.ofHomeomorph
        (HomotopyPullback.pullbackEndpointLeftHomeomorph p g)
        (HomotopyPullback.pullbackFst_comp_pullbackEndpointLeftHomeomorph p g)).symm)

@[simp]
theorem pullbackHomotopyPullbackLeftFiberHomotopyEquiv_toFun
    {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {p : C(A, B)} (hp : IsHurewiczFibration.{max u v} p) (g : C(C, B)) :
    (hp.pullbackHomotopyPullbackLeftFiberHomotopyEquiv g).toFun =
      HomotopyPullback.ofPullback p g := by
  rw [pullbackHomotopyPullbackLeftFiberHomotopyEquiv, FiberHomotopyEquiv.trans_toFun,
    FiberHomotopyEquiv.trans_toFun, FiberHomotopyEquiv.ofHomeomorph_toFun,
    FiberHomotopyEquiv.symm_toFun, FiberHomotopyEquiv.ofHomeomorph_invFun]
  ext x : 1
  exact HomotopyPullback.ext (by simp) (by simp) fun _ ↦ by simp

/-- **Strict vs. homotopy pullback along a Hurewicz fibration (right leg).** When `q : C(C, B)` is
a Hurewicz fibration, `HomotopyPullback.ofPullback f q` is part of a fibre homotopy equivalence
from `f.Pullback q` to `HomotopyPullback f q` over `A`. -/
noncomputable def pullbackHomotopyPullbackRightFiberHomotopyEquiv
    {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) {q : C(C, B)} (hq : IsHurewiczFibration.{max w v} q) :
    FiberHomotopyEquiv (ContinuousMap.pullbackFst ⇑f ⇑q) (HomotopyPullback.fst f q) :=
  (FiberHomotopyEquiv.ofHomeomorph (Homeomorph.pullbackComm ⇑f ⇑q)
      (ContinuousMap.pullbackSnd_comp_pullbackComm ⇑f ⇑q)).trans
    ((hq.pullbackHomotopyPullbackLeftFiberHomotopyEquiv f).trans
      (FiberHomotopyEquiv.ofHomeomorph (p := HomotopyPullback.fst f q)
        (HomotopyPullback.swapHomeomorph f q) (ContinuousMap.ext fun _ ↦ rfl)).symm)

@[simp]
theorem pullbackHomotopyPullbackRightFiberHomotopyEquiv_toFun
    {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) {q : C(C, B)} (hq : IsHurewiczFibration.{max w v} q) :
    (hq.pullbackHomotopyPullbackRightFiberHomotopyEquiv f).toFun =
      HomotopyPullback.ofPullback f q := by
  rw [pullbackHomotopyPullbackRightFiberHomotopyEquiv, FiberHomotopyEquiv.trans_toFun,
    FiberHomotopyEquiv.trans_toFun, FiberHomotopyEquiv.ofHomeomorph_toFun,
    FiberHomotopyEquiv.symm_toFun, FiberHomotopyEquiv.ofHomeomorph_invFun,
    hq.pullbackHomotopyPullbackLeftFiberHomotopyEquiv_toFun f]
  ext x : 1
  exact HomotopyPullback.ext (by simp) (by simp) fun _ ↦ by simp [x.2.symm]

end IsHurewiczFibration

end TauCeti
