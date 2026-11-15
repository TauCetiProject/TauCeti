/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration.MappingPath
public import TauCeti.Topology.Homotopy.MappingPath.Homotopy

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
  (`IsHurewiczFibration.pullbackHomotopyPullbackLeftEquiv`), and symmetrically when the right leg
  is a Hurewicz fibration;
* replacing either leg by a homotopic map induces a fibre homotopy equivalence over `A × C`, hence
  over both `A` and `C` (`ContinuousMap.Homotopy.homotopyPullbackLeftEquiv`,
  `ContinuousMap.Homotopy.homotopyPullbackRightEquiv`).

Specializing `f` or `g` recovers `MappingPathSpace`, `MappingPathFiber`, `Path b₀ b₁`, and `Ω B b`
up to canonical homeomorphism.

## Main definitions and results

* `TauCeti.HomotopyPullback f g`: the homotopy pullback of `f : C(A, B)` and `g : C(C, B)`, with
  `fst`, `snd`, `pathMap`, `path`, and universal `homotopy`.
* `TauCeti.HomotopyPullback.lift`, `TauCeti.HomotopyPullback.liftEquiv`,
  `TauCeti.HomotopyPullback.ofPullback`: universal property and constant-path comparison from the
  strict pullback.
* `TauCeti.HomotopyPullback.swapHomeomorph`: symmetry `HomotopyPullback f g ≃ₜ HomotopyPullback g f`
  reversing paths.
* `TauCeti.HomotopyPullback.pullbackEndpointLeftHomeomorph`,
  `TauCeti.HomotopyPullback.isHurewiczFibration_snd`,
  `TauCeti.HomotopyPullback.isHurewiczFibration_fst`,
  `TauCeti.HomotopyPullback.sndFiberHomeomorph`, `TauCeti.HomotopyPullback.fstFiberHomeomorph`:
  pullback-of-replacement factorization, Hurewicz fibration projections, and strict fibres.
* `TauCeti.IsHurewiczFibration.pullbackHomotopyPullbackLeftEquiv`,
  `TauCeti.IsHurewiczFibration.pullbackHomotopyPullbackRightEquiv`: `ofPullback` is a fibre
  homotopy equivalence when one leg is a Hurewicz fibration.
* `TauCeti.HomotopyPullback.idRightHomeomorph`, `TauCeti.HomotopyPullback.constRightProdHomeomorph`,
  `TauCeti.HomotopyPullback.constHomeomorphPath`,
  `TauCeti.HomotopyPullback.constHomeomorphLoopSpace`: canonical homeomorphisms for identity and
  constant legs.
* `TauCeti.HomotopyPullback.map`, `ContinuousMap.Homotopy.homotopyPullbackLeftEquiv`,
  `ContinuousMap.Homotopy.homotopyPullbackRightEquiv`: functoriality and homotopy invariance in both
  legs.

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

theorem fst_mk' {f : C(A, B)} {g : C(C, B)} (a : A) (c : C) (γ : Path (f a) (g c)) :
    fst f g (mk' a c γ) = a :=
  (rfl)

theorem snd_mk' {f : C(A, B)} {g : C(C, B)} (a : A) (c : C) (γ : Path (f a) (g c)) :
    snd f g (mk' a c γ) = c :=
  (rfl)

theorem pathMap_mk'_apply {f : C(A, B)} {g : C(C, B)} (a : A) (c : C) (γ : Path (f a) (g c))
    (t : I) :
    pathMap f g (mk' a c γ) t = γ t :=
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

theorem fst_lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) (x : X) :
    fst f g (lift α β H x) = α x :=
  (rfl)

theorem snd_lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) (x : X) :
    snd f g (lift α β H x) = β x :=
  (rfl)

theorem pathMap_lift_apply (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β))
    (x : X) (t : I) :
    pathMap f g (lift α β H x) t = H (t, x) :=
  (rfl)

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

/-- Lift a strictly commuting cone `f ∘ α = g ∘ β` to `HomotopyPullback f g` using constant
paths. -/
def liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    C(X, HomotopyPullback f g) :=
  lift α β ((ContinuousMap.Homotopy.refl (f.comp α)).cast rfl h)

@[simp]
theorem liftStrict_val {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) (x : X) :
    (liftStrict h x).val = (α x, β x, ContinuousMap.const I (f (α x))) := by
  ext : 1
  · rfl
  · ext : 1
    · rfl
    · ext t : 1
      rfl

@[simp]
theorem fst_comp_liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    (fst f g).comp (liftStrict h) = α :=
  fst_comp_lift _ _ _

@[simp]
theorem snd_comp_liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    (snd f g).comp (liftStrict h) = β :=
  snd_comp_lift _ _ _

theorem fst_liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) (x : X) :
    fst f g (liftStrict h x) = α x :=
  (rfl)

theorem snd_liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) (x : X) :
    snd f g (liftStrict h x) = β x :=
  (rfl)

theorem pathMap_liftStrict_apply {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β)
    (x : X) (t : I) :
    pathMap f g (liftStrict h x) t = f (α x) :=
  (rfl)

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

theorem fst_ofPullback (f : C(A, B)) (g : C(C, B)) (x : (⇑f).Pullback ⇑g) :
    fst f g (ofPullback f g x) = x.1.1 :=
  (ContinuousMap.congr_fun (fst_comp_ofPullback f g) x).trans
    (by simp [Function.Pullback.fst])

theorem snd_ofPullback (f : C(A, B)) (g : C(C, B)) (x : (⇑f).Pullback ⇑g) :
    snd f g (ofPullback f g x) = x.1.2 :=
  (ContinuousMap.congr_fun (snd_comp_ofPullback f g) x).trans
    (by simp [Function.Pullback.snd])

theorem pathMap_ofPullback_apply (f : C(A, B)) (g : C(C, B)) (x : (⇑f).Pullback ⇑g) (t : I) :
    pathMap f g (ofPullback f g x) t = f x.1.1 := by
  change f (ContinuousMap.pullbackFst (⇑f) (⇑g) x) = f x.1.1
  simp [Function.Pullback.fst]

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

theorem fst_pullbackEndpointLeftHomeomorph_symm (f : C(A, B)) (g : C(C, B))
    (q : (⇑g).Pullback ⇑(MappingPathSpace.endpoint f)) :
    fst f g ((pullbackEndpointLeftHomeomorph f g).symm q) = q.1.2.val.1 :=
  (rfl)

theorem snd_pullbackEndpointLeftHomeomorph_symm (f : C(A, B)) (g : C(C, B))
    (q : (⇑g).Pullback ⇑(MappingPathSpace.endpoint f)) :
    snd f g ((pullbackEndpointLeftHomeomorph f g).symm q) = q.1.1 :=
  (rfl)

@[simp]
theorem pullbackEndpointLeftHomeomorph_symm_val (f : C(A, B)) (g : C(C, B))
    (q : (⇑g).Pullback ⇑(MappingPathSpace.endpoint f)) :
    ((pullbackEndpointLeftHomeomorph f g).symm q).val = (q.1.2.val.1, q.1.1, q.1.2.val.2) :=
  (rfl)

theorem pathMap_pullbackEndpointLeftHomeomorph_symm (f : C(A, B)) (g : C(C, B))
    (q : (⇑g).Pullback ⇑(MappingPathSpace.endpoint f)) :
    pathMap f g ((pullbackEndpointLeftHomeomorph f g).symm q) = q.1.2.val.2 :=
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

theorem fst_sndFiberHomeomorph_symm (f : C(A, B)) (g : C(C, B)) (c : C)
    (p : MappingPathFiber f (g c)) :
    fst f g ((sndFiberHomeomorph f g c).symm p).1 = p.val.1 :=
  (rfl)

theorem snd_sndFiberHomeomorph_symm (f : C(A, B)) (g : C(C, B)) (c : C)
    (p : MappingPathFiber f (g c)) :
    snd f g ((sndFiberHomeomorph f g c).symm p).1 = c :=
  (rfl)

theorem pathMap_sndFiberHomeomorph_symm (f : C(A, B)) (g : C(C, B)) (c : C)
    (p : MappingPathFiber f (g c)) :
    pathMap f g ((sndFiberHomeomorph f g c).symm p).1 = p.val.2 :=
  (rfl)

/-- The strict fibre of `fst f g` over `a : A` is canonically homeomorphic to
`MappingPathFiber g (f a)` by reversing paths. -/
def fstFiberHomeomorph (f : C(A, B)) (g : C(C, B)) (a : A) :
    (fst f g) ⁻¹' {a} ≃ₜ MappingPathFiber g (f a) where
  toFun x := sndFiberHomeomorph g f a ⟨swap f g x.1, x.2⟩
  invFun p := ⟨swap g f ((sndFiberHomeomorph g f a).symm p).1, rfl⟩
  left_inv x := Subtype.ext <|
    (congrArg (swap g f) (congrArg Subtype.val
      ((sndFiberHomeomorph g f a).left_inv ⟨swap f g x.1, x.2⟩))).trans (swap_swap f g x.1)
  right_inv p := by
    change sndFiberHomeomorph g f a ⟨swap f g (swap g f ((sndFiberHomeomorph g f a).symm p).1), rfl⟩
      = p
    have h : (⟨swap f g (swap g f ((sndFiberHomeomorph g f a).symm p).1), rfl⟩ :
        (snd g f) ⁻¹' {a}) = (sndFiberHomeomorph g f a).symm p :=
      Subtype.ext (swap_swap g f _)
    rw [h]
    exact (sndFiberHomeomorph g f a).right_inv p
  continuous_toFun := (sndFiberHomeomorph g f a).continuous.comp
    (((swap f g).continuous.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (((swap g f).continuous.comp
    (continuous_subtype_val.comp (sndFiberHomeomorph g f a).symm.continuous)).subtype_mk _)

@[simp]
theorem fstFiberHomeomorph_val_fst (f : C(A, B)) (g : C(C, B)) (a : A) (x : (fst f g) ⁻¹' {a}) :
    (fstFiberHomeomorph f g a x).val.1 = snd f g x.1 :=
  (rfl)

@[simp]
theorem fstFiberHomeomorph_val_snd_apply (f : C(A, B)) (g : C(C, B)) (a : A)
    (x : (fst f g) ⁻¹' {a}) (t : I) :
    (fstFiberHomeomorph f g a x).val.2 t = pathMap f g x.1 (σ t) :=
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

theorem fst_idRightHomeomorph_symm (f : C(A, B)) (q : MappingPathSpace f) :
    fst f (.id B) ((idRightHomeomorph f).symm q) = q.val.1 :=
  (rfl)

theorem snd_idRightHomeomorph_symm (f : C(A, B)) (q : MappingPathSpace f) :
    snd f (.id B) ((idRightHomeomorph f).symm q) = MappingPathSpace.endpoint f q :=
  (rfl)

/-- `HomotopyPullback (.id B) g` is homeomorphic to `MappingPathSpace g` via path reversal. -/
def idLeftHomeomorph (g : C(C, B)) :
    HomotopyPullback (.id B) g ≃ₜ MappingPathSpace g :=
  (swapHomeomorph (.id B) g).trans (idRightHomeomorph g)

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

theorem fst_constRightProdHomeomorph_symm (f : C(A, B)) (b : B)
    (q : MappingPathFiber f b × C) :
    fst f (.const C b) ((constRightProdHomeomorph f b).symm q) = q.1.val.1 :=
  (rfl)

theorem snd_constRightProdHomeomorph_symm (f : C(A, B)) (b : B)
    (q : MappingPathFiber f b × C) :
    snd f (.const C b) ((constRightProdHomeomorph f b).symm q) = q.2 :=
  (rfl)

theorem pathMap_constRightProdHomeomorph_symm (f : C(A, B)) (b : B)
    (q : MappingPathFiber f b × C) :
    pathMap f (.const C b) ((constRightProdHomeomorph f b).symm q) = q.1.val.2 :=
  (rfl)

/-- Over a one-point corner `C`, `HomotopyPullback f (.const C b)` is canonically homeomorphic to
`MappingPathFiber f b`. -/
def constRightHomeomorphOfUnique [Unique C] (f : C(A, B)) (b : B) :
    HomotopyPullback f (.const C b) ≃ₜ MappingPathFiber f b :=
  (constRightProdHomeomorph f b).trans (Homeomorph.prodUnique (MappingPathFiber f b) C)

/-- Over a one-point left corner `A`, `HomotopyPullback (.const A b) g` is canonically homeomorphic
to `MappingPathFiber g b` via path reversal. -/
def constLeftHomeomorphOfUnique [Unique A] (b : B) (g : C(C, B)) :
    HomotopyPullback (.const A b) g ≃ₜ MappingPathFiber g b :=
  (swapHomeomorph (.const A b) g).trans (constRightHomeomorphOfUnique g b)

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
    (constHomeomorphPath b₀ b₁).symm γ = mk' () () γ := by
  refine ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) fun t ↦ ?_
  change (((mappingPathFiberConstHomeomorphPath b₀ b₁).symm γ).val.2) t = γ t
  rw [mappingPathFiberConstHomeomorphPath_symm_val]
  rfl

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

theorem fst_map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) (p : HomotopyPullback f g) :
    fst f' g' (map a b c hf hg p) = a (fst f g p) :=
  (rfl)

theorem snd_map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) (p : HomotopyPullback f g) :
    snd f' g' (map a b c hf hg p) = c (snd f g p) :=
  (rfl)

theorem pathMap_map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) (p : HomotopyPullback f g) :
    pathMap f' g' (map a b c hf hg p) = b.comp (pathMap f g p) :=
  (rfl)

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
noncomputable def pullbackHomotopyPullbackLeftEquiv {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {p : C(A, B)} (hp : IsHurewiczFibration.{max u v} p) (g : C(C, B)) :
    FiberHomotopyEquiv (ContinuousMap.pullbackSnd ⇑p ⇑g) (HomotopyPullback.snd p g) := by
  let Λ := hp.nonempty_liftingFunction.some
  let eDom : (⇑p).Pullback ⇑g ≃ₜ (⇑g).Pullback ⇑p :=
    { toFun x := ⟨(x.1.2, x.1.1), x.2.symm⟩
      invFun y := ⟨(y.1.2, y.1.1), y.2.symm⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        ((continuous_subtype_val.snd).prodMk continuous_subtype_val.fst).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.snd).prodMk continuous_subtype_val.fst).subtype_mk _ }
  have heDom : (ContinuousMap.pullbackFst ⇑g ⇑p).comp (eDom : C(_, _)) =
      ContinuousMap.pullbackSnd ⇑p ⇑g := by
    ext x : 1
    simp [eDom, Function.Pullback.fst, Function.Pullback.snd]
  exact (FiberHomotopyEquiv.ofHomeomorph eDom heDom).trans
    ((FiberHomotopyEquiv.pullback g Λ.mappingPathFiberHomotopyEquiv).trans
      (FiberHomotopyEquiv.ofHomeomorph
        (HomotopyPullback.pullbackEndpointLeftHomeomorph p g)
        (HomotopyPullback.pullbackFst_comp_pullbackEndpointLeftHomeomorph p g)).symm)

@[simp]
theorem pullbackHomotopyPullbackLeftEquiv_toFun {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {p : C(A, B)} (hp : IsHurewiczFibration.{max u v} p) (g : C(C, B)) :
    (hp.pullbackHomotopyPullbackLeftEquiv g).toFun = HomotopyPullback.ofPullback p g := by
  rw [pullbackHomotopyPullbackLeftEquiv, FiberHomotopyEquiv.trans_toFun,
    FiberHomotopyEquiv.trans_toFun, FiberHomotopyEquiv.ofHomeomorph_toFun,
    FiberHomotopyEquiv.symm_toFun, FiberHomotopyEquiv.ofHomeomorph_invFun]
  ext x : 1
  refine HomotopyPullback.ext ?_ ?_ fun t ↦ ?_
  · simp
  · simp
  · simp

/-- **Strict vs. homotopy pullback along a Hurewicz fibration (right leg).** When `q : C(C, B)` is
a Hurewicz fibration, `HomotopyPullback.ofPullback f q` is part of a fibre homotopy equivalence
from `f.Pullback q` to `HomotopyPullback f q` over `A`. -/
noncomputable def pullbackHomotopyPullbackRightEquiv {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) {q : C(C, B)} (hq : IsHurewiczFibration.{max w v} q) :
    FiberHomotopyEquiv (ContinuousMap.pullbackFst ⇑f ⇑q) (HomotopyPullback.fst f q) := by
  let eDom : (⇑f).Pullback ⇑q ≃ₜ (⇑q).Pullback ⇑f :=
    { toFun x := ⟨(x.1.2, x.1.1), x.2.symm⟩
      invFun y := ⟨(y.1.2, y.1.1), y.2.symm⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        ((continuous_subtype_val.snd).prodMk continuous_subtype_val.fst).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.snd).prodMk continuous_subtype_val.fst).subtype_mk _ }
  have heDom : (ContinuousMap.pullbackSnd ⇑q ⇑f).comp (eDom : C(_, _)) =
      ContinuousMap.pullbackFst ⇑f ⇑q := by
    ext x : 1
    simp [eDom, Function.Pullback.fst, Function.Pullback.snd]
  exact (FiberHomotopyEquiv.ofHomeomorph eDom heDom).trans
    ((hq.pullbackHomotopyPullbackLeftEquiv f).trans
      (FiberHomotopyEquiv.ofHomeomorph (p := HomotopyPullback.fst f q)
        (HomotopyPullback.swapHomeomorph f q) (ContinuousMap.ext fun _ ↦ rfl)).symm)

@[simp]
theorem pullbackHomotopyPullbackRightEquiv_toFun {A : Type u} {B : Type v} {C : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) {q : C(C, B)} (hq : IsHurewiczFibration.{max w v} q) :
    (hq.pullbackHomotopyPullbackRightEquiv f).toFun = HomotopyPullback.ofPullback f q := by
  rw [pullbackHomotopyPullbackRightEquiv, FiberHomotopyEquiv.trans_toFun,
    FiberHomotopyEquiv.trans_toFun, FiberHomotopyEquiv.ofHomeomorph_toFun,
    FiberHomotopyEquiv.symm_toFun, FiberHomotopyEquiv.ofHomeomorph_invFun,
    hq.pullbackHomotopyPullbackLeftEquiv_toFun f]
  ext x : 1
  refine HomotopyPullback.ext (by simp) (by simp) fun t ↦ ?_
  change HomotopyPullback.pathMap q f
      (HomotopyPullback.ofPullback q f ⟨(x.1.2, x.1.1), x.2.symm⟩) (σ t) =
    HomotopyPullback.pathMap f q (HomotopyPullback.ofPullback f q x) t
  rw [HomotopyPullback.pathMap_ofPullback_apply, HomotopyPullback.pathMap_ofPullback_apply]
  exact x.2.symm

end IsHurewiczFibration

end TauCeti

/-! ### Homotopy invariance in both legs -/

namespace ContinuousMap.Homotopy

open TauCeti

section Left

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  {f f' : C(A, B)} (H : f.Homotopy f') (g : C(C, B))

/-- Prepend the reversed track of `H : f.Homotopy f'` to the path of a point in
`HomotopyPullback f g`, keeping both corner coordinates fixed. -/
noncomputable def homotopyPullbackLeftMap :
    C(HomotopyPullback f g, HomotopyPullback f' g) where
  toFun p := ⟨(p.val.1, p.val.2.1,
    ((H.evalAt p.val.1).symm.trans (HomotopyPullback.path p)).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    refine (continuous_subtype_val.fst.prodMk <|
      continuous_subtype_val.snd.fst.prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.trans_continuous_family
      (fun p : HomotopyPullback f g ↦ (H.evalAt p.val.1).symm)
      (H.continuous.comp ((continuous_symm.comp continuous_snd).prodMk
        (continuous_subtype_val.fst.comp continuous_fst)))
      (fun p ↦ HomotopyPullback.path p)
      ((continuous_subtype_val.snd.snd.comp continuous_fst).eval continuous_snd)

@[simp]
theorem homotopyPullbackLeftMap_val (p : HomotopyPullback f g) :
    (H.homotopyPullbackLeftMap g p).val =
      (p.val.1, p.val.2.1,
        ((H.evalAt p.val.1).symm.trans (HomotopyPullback.path p)).toContinuousMap) :=
  (rfl)

theorem fst_homotopyPullbackLeftMap (p : HomotopyPullback f g) :
    HomotopyPullback.fst f' g (H.homotopyPullbackLeftMap g p) = HomotopyPullback.fst f g p :=
  (rfl)

theorem snd_homotopyPullbackLeftMap (p : HomotopyPullback f g) :
    HomotopyPullback.snd f' g (H.homotopyPullbackLeftMap g p) = HomotopyPullback.snd f g p :=
  (rfl)

theorem pathMap_homotopyPullbackLeftMap_apply (p : HomotopyPullback f g) (t : I) :
    HomotopyPullback.pathMap f' g (H.homotopyPullbackLeftMap g p) t =
      ((H.evalAt p.val.1).symm.trans (HomotopyPullback.path p)) t :=
  (rfl)

@[simp]
theorem prodMk_comp_homotopyPullbackLeftMap :
    ((HomotopyPullback.fst f' g).prodMk (HomotopyPullback.snd f' g)).comp
      (H.homotopyPullbackLeftMap g) =
      (HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g) := by
  ext : 1; rfl

/-- Remove the constant initial path continuously on `HomotopyPullback f g`, preserving both corner
coordinates throughout. -/
private noncomputable def reflLeftHomotopy (f : C(A, B)) (g : C(C, B)) :
    ContinuousMap.HomotopyWith ((Homotopy.refl f).homotopyPullbackLeftMap g)
      (.id (HomotopyPullback f g))
      (fun φ ↦ ((HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g)).comp φ =
        (HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g)) where
  toFun q := ⟨(q.2.val.1, q.2.val.2.1,
    (Path.delayReflLeft q.1 (HomotopyPullback.path q.2)).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    refine ((continuous_subtype_val.fst.comp continuous_snd).prodMk <|
      (continuous_subtype_val.snd.fst.comp continuous_snd).prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.delayReflLeft_continuous_family
      (fun q : I × HomotopyPullback f g ↦ HomotopyPullback.path q.2)
      (((continuous_subtype_val.snd.snd.comp continuous_snd).comp continuous_fst).eval
        continuous_snd)
      ContinuousMap.fst
  map_zero_left p := Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <|
    congrArg Path.toContinuousMap (Path.delayReflLeft_zero _)
  map_one_left p := Subtype.ext <| Prod.ext rfl <| Prod.ext rfl <|
    congrArg Path.toContinuousMap (Path.delayReflLeft_one _)
  prop' _ := by ext : 1; rfl

/-- Shrink `α` followed by `α.symm` on `HomotopyPullback f g` while fixing both corner points. -/
private noncomputable def backtrackLeftHomotopy :
    ContinuousMap.HomotopyWith
      (((Homotopy.refl f).homotopyPullbackLeftMap g).comp
        ((Homotopy.refl f).homotopyPullbackLeftMap g))
      ((H.symm.homotopyPullbackLeftMap g).comp (H.homotopyPullbackLeftMap g))
      (fun φ ↦ ((HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g)).comp φ =
        (HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g)) := by
  let α (s : I) (a : A) : Path (f a) (H (s, a)) :=
    ((H.evalAt a).subpath 0 s).cast (H.apply_zero a).symm rfl
  refine
    { toFun q := ⟨(q.2.val.1, q.2.val.2.1,
        ((α q.1 q.2.val.1).trans
          ((α q.1 q.2.val.1).symm.trans (HomotopyPullback.path q.2))).toContinuousMap),
        Path.source _, Path.target _⟩
      continuous_toFun := ?_
      map_zero_left p := ?_
      map_one_left p := ?_
      prop' _ := by ext : 1; rfl }
  · refine ((continuous_subtype_val.fst.comp continuous_snd).prodMk <|
      (continuous_subtype_val.snd.fst.comp continuous_snd).prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hα : Continuous ↿fun q : I × HomotopyPullback f g ↦ α q.1 q.2.val.1 :=
      H.continuous.comp
        ((by fun_prop : Continuous fun q : (I × HomotopyPullback f g) × I ↦
            Set.Icc.convexComb 0 q.1.1 q.2).prodMk
          (continuous_subtype_val.fst.comp (continuous_snd.comp continuous_fst)))
    have hγ : Continuous ↿fun q : I × HomotopyPullback f g ↦ HomotopyPullback.path q.2 :=
      ((continuous_subtype_val.snd.snd.comp continuous_snd).comp continuous_fst).eval
        continuous_snd
    have hβ := Path.trans_continuous_family
      (fun q : I × HomotopyPullback f g ↦ (α q.1 q.2.val.1).symm)
      (Path.symm_continuous_family _ hα) (fun q ↦ HomotopyPullback.path q.2) hγ
    exact Path.trans_continuous_family
      (fun q : I × HomotopyPullback f g ↦ α q.1 q.2.val.1) hα
      (fun q ↦ (α q.1 q.2.val.1).symm.trans (HomotopyPullback.path q.2)) hβ
  · refine HomotopyPullback.ext rfl rfl fun t ↦ ?_
    simp [α, Path.cast, Path.trans_apply, HomotopyPullback.path]
  · refine HomotopyPullback.ext rfl rfl fun t ↦ ?_
    simp [α, Path.subpath_zero_one, Path.cast, Path.trans_apply, HomotopyPullback.path,
      -Path.coe_subpath]

private theorem homotopyPullbackLeftMap_symm_comp_homotopicWith :
    ((H.symm.homotopyPullbackLeftMap g).comp (H.homotopyPullbackLeftMap g)).HomotopicWith
      (.id (HomotopyPullback f g))
      (fun φ ↦ ((HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g)).comp φ =
        (HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g)) := by
  let h := (reflLeftHomotopy f g).toHomotopy.compContinuousMap
    ((Homotopy.refl f).homotopyPullbackLeftMap g)
  have h' : (((Homotopy.refl f).homotopyPullbackLeftMap g).comp
      ((Homotopy.refl f).homotopyPullbackLeftMap g)).HomotopicWith
      ((Homotopy.refl f).homotopyPullbackLeftMap g)
      (fun φ ↦ ((HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g)).comp φ =
        (HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g)) := by
    refine ⟨⟨h.cast rfl (ContinuousMap.id_comp _), ?_⟩⟩
    intro s
    ext p : 1
    exact ContinuousMap.congr_fun ((reflLeftHomotopy f g).prop' s)
      ((Homotopy.refl f).homotopyPullbackLeftMap g p)
  exact ⟨(backtrackLeftHomotopy H g).symm.trans (h'.some.trans (reflLeftHomotopy f g))⟩

/-- **Homotopy invariance of the homotopy pullback in the first leg.** A homotopy
`H : f.Homotopy f'` induces a fibre homotopy equivalence over `A × C` between
`HomotopyPullback f g` and `HomotopyPullback f' g`. -/
noncomputable def homotopyPullbackLeftEquiv :
    FiberHomotopyEquiv ((HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g))
      ((HomotopyPullback.fst f' g).prodMk (HomotopyPullback.snd f' g)) where
  toFun := H.homotopyPullbackLeftMap g
  invFun := H.symm.homotopyPullbackLeftMap g
  comp_toFun := H.prodMk_comp_homotopyPullbackLeftMap g
  comp_invFun := H.symm.prodMk_comp_homotopyPullbackLeftMap g
  left_inv := H.homotopyPullbackLeftMap_symm_comp_homotopicWith g
  right_inv := by simpa using H.symm.homotopyPullbackLeftMap_symm_comp_homotopicWith g

@[simp]
theorem homotopyPullbackLeftEquiv_toFun :
    (H.homotopyPullbackLeftEquiv g).toFun = H.homotopyPullbackLeftMap g :=
  (rfl)

@[simp]
theorem homotopyPullbackLeftEquiv_invFun :
    (H.homotopyPullbackLeftEquiv g).invFun = H.symm.homotopyPullbackLeftMap g :=
  (rfl)

/-- `H : f.Homotopy f'` induces a fibre homotopy equivalence over `C` between
`HomotopyPullback f g` and `HomotopyPullback f' g`. -/
noncomputable def homotopyPullbackLeftSndEquiv :
    FiberHomotopyEquiv (HomotopyPullback.snd f g) (HomotopyPullback.snd f' g) :=
  (H.homotopyPullbackLeftEquiv g).compBase ContinuousMap.snd

/-- `H : f.Homotopy f'` induces a fibre homotopy equivalence over `A` between
`HomotopyPullback f g` and `HomotopyPullback f' g`. -/
noncomputable def homotopyPullbackLeftFstEquiv :
    FiberHomotopyEquiv (HomotopyPullback.fst f g) (HomotopyPullback.fst f' g) :=
  (H.homotopyPullbackLeftEquiv g).compBase ContinuousMap.fst

/-- `H : f.Homotopy f'` induces a homotopy equivalence
`HomotopyPullback f g ≃ₕ HomotopyPullback f' g`. -/
noncomputable def homotopyPullbackLeftHomotopyEquiv :
    HomotopyPullback f g ≃ₕ HomotopyPullback f' g :=
  (H.homotopyPullbackLeftEquiv g).toHomotopyEquiv

@[simp]
theorem homotopyPullbackLeftHomotopyEquiv_apply (p : HomotopyPullback f g) :
    homotopyPullbackLeftHomotopyEquiv H g p = H.homotopyPullbackLeftMap g p :=
  FiberHomotopyEquiv.toHomotopyEquiv_apply _ p

@[simp]
theorem homotopyPullbackLeftHomotopyEquiv_symm_apply (p : HomotopyPullback f' g) :
    (homotopyPullbackLeftHomotopyEquiv H g).symm p = H.symm.homotopyPullbackLeftMap g p :=
  FiberHomotopyEquiv.toHomotopyEquiv_symm_apply _ p

end Left

section Right

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  {g g' : C(C, B)} (K : g.Homotopy g') (f : C(A, B))

/-- Conjugate `K.homotopyPullbackLeftMap f` by `swapHomeomorph` to vary the right leg `g ~ g'` while
fixing both corner coordinates. -/
noncomputable def homotopyPullbackRightMap :
    C(HomotopyPullback f g, HomotopyPullback f g') :=
  (HomotopyPullback.swap g' f).comp ((K.homotopyPullbackLeftMap f).comp (HomotopyPullback.swap f g))

theorem fst_homotopyPullbackRightMap (p : HomotopyPullback f g) :
    HomotopyPullback.fst f g' (K.homotopyPullbackRightMap f p) = HomotopyPullback.fst f g p :=
  (rfl)

theorem snd_homotopyPullbackRightMap (p : HomotopyPullback f g) :
    HomotopyPullback.snd f g' (K.homotopyPullbackRightMap f p) = HomotopyPullback.snd f g p :=
  (rfl)

theorem pathMap_homotopyPullbackRightMap_apply (p : HomotopyPullback f g) (t : I) :
    HomotopyPullback.pathMap f g' (K.homotopyPullbackRightMap f p) t =
      ((HomotopyPullback.path p).trans (K.evalAt p.val.2.1)) t := by
  change ((K.evalAt p.val.2.1).symm.trans (HomotopyPullback.path p).symm) (σ t) = _
  rw [← Path.trans_symm, Path.symm_apply, Function.comp_apply, unitInterval.symm_symm]

/-- **Homotopy invariance of the homotopy pullback in the second leg.** A homotopy
`K : g.Homotopy g'` induces a fibre homotopy equivalence over `A × C` between
`HomotopyPullback f g` and `HomotopyPullback f g'`. -/
noncomputable def homotopyPullbackRightEquiv :
    FiberHomotopyEquiv ((HomotopyPullback.fst f g).prodMk (HomotopyPullback.snd f g))
      ((HomotopyPullback.fst f g').prodMk (HomotopyPullback.snd f g')) :=
  ((FiberHomotopyEquiv.ofHomeomorph (HomotopyPullback.swapHomeomorph f g) rfl).trans
    ((K.homotopyPullbackLeftEquiv f).trans
      (FiberHomotopyEquiv.ofHomeomorph (HomotopyPullback.swapHomeomorph f g') rfl).symm)).compBase
    (ContinuousMap.snd.prodMk ContinuousMap.fst)

@[simp]
theorem homotopyPullbackRightEquiv_toFun :
    (K.homotopyPullbackRightEquiv f).toFun = K.homotopyPullbackRightMap f := by
  ext p : 1
  simp [homotopyPullbackRightEquiv, homotopyPullbackRightMap]

@[simp]
theorem homotopyPullbackRightEquiv_invFun :
    (K.homotopyPullbackRightEquiv f).invFun = K.symm.homotopyPullbackRightMap f := by
  ext p : 1
  simp [homotopyPullbackRightEquiv, homotopyPullbackRightMap]

/-- `K : g.Homotopy g'` induces a fibre homotopy equivalence over `A` between
`HomotopyPullback f g` and `HomotopyPullback f g'`. -/
noncomputable def homotopyPullbackRightFstEquiv :
    FiberHomotopyEquiv (HomotopyPullback.fst f g) (HomotopyPullback.fst f g') :=
  (K.homotopyPullbackRightEquiv f).compBase ContinuousMap.fst

/-- `K : g.Homotopy g'` induces a fibre homotopy equivalence over `C` between
`HomotopyPullback f g` and `HomotopyPullback f g'`. -/
noncomputable def homotopyPullbackRightSndEquiv :
    FiberHomotopyEquiv (HomotopyPullback.snd f g) (HomotopyPullback.snd f g') :=
  (K.homotopyPullbackRightEquiv f).compBase ContinuousMap.snd

/-- `K : g.Homotopy g'` induces a homotopy equivalence
`HomotopyPullback f g ≃ₕ HomotopyPullback f g'`. -/
noncomputable def homotopyPullbackRightHomotopyEquiv :
    HomotopyPullback f g ≃ₕ HomotopyPullback f g' :=
  (K.homotopyPullbackRightEquiv f).toHomotopyEquiv

@[simp]
theorem homotopyPullbackRightHomotopyEquiv_apply (p : HomotopyPullback f g) :
    homotopyPullbackRightHomotopyEquiv K f p = K.homotopyPullbackRightMap f p := by
  rw [homotopyPullbackRightHomotopyEquiv, FiberHomotopyEquiv.toHomotopyEquiv_apply,
    homotopyPullbackRightEquiv_toFun]

@[simp]
theorem homotopyPullbackRightHomotopyEquiv_symm_apply (p : HomotopyPullback f g') :
    (homotopyPullbackRightHomotopyEquiv K f).symm p = K.symm.homotopyPullbackRightMap f p := by
  rw [homotopyPullbackRightHomotopyEquiv, FiberHomotopyEquiv.toHomotopyEquiv_symm_apply,
    homotopyPullbackRightEquiv_invFun]

end Right

end ContinuousMap.Homotopy
