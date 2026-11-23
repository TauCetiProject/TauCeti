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
with the subspace topology from `A × C × C(I, B)` (`C(I, B)` carrying the compact-open topology),
across arbitrary universes and without compact-generation or base-point assumptions.

Continuous maps `X → HomotopyPullback f g` correspond bijectively (`liftEquiv`) to homotopy cones
`(α : C(X, A), β : C(X, C), H : (f.comp α).Homotopy (g.comp β))`, and the strict pullback maps in
by constant paths (`ofPullback`). Identifying `HomotopyPullback f g` over `C` with the pullback of
`MappingPathSpace.endpoint f` along `g` (`pullbackEndpointLeftHomeomorph`) shows that both
projections `fst` and `snd` are Hurewicz fibrations in every lifting universe, identifies their
fibres with `MappingPathFiber`, and makes `ofPullback` a fibre homotopy equivalence when either leg
is a Hurewicz fibration.

## Main definitions and results

* `TauCeti.HomotopyPullback`: homotopy pullback with `fst`, `snd`, `pathMap`, `path`, `homotopy`.
* `TauCeti.HomotopyPullback.lift`, `liftEquiv`, `liftStrict`, `ofPullback`: universal property and
  strict-pullback comparison.
* `TauCeti.HomotopyPullback.swapHomeomorph`, `map`: symmetry and functoriality in cospan morphisms.
* `TauCeti.HomotopyPullback.pullbackEndpointLeftHomeomorph`, `isHurewiczFibration_snd`,
  `isHurewiczFibration_fst`, `sndFiberHomeomorph`, `fstFiberHomeomorph`: fibration structure and
  strict fibres.
* `TauCeti.HomotopyPullback.idRightHomeomorph`, `idLeftHomeomorph`, `constRightProdHomeomorph`,
  `uniqueRightHomeomorph`, `uniqueLeftHomeomorph`, `homeomorphPathOfUnique`,
  `homeomorphLoopSpaceOfUnique`: canonical homeomorphisms for identity, constant, and one-point
  legs.
* `TauCeti.IsHurewiczFibration.pullbackHomotopyPullbackLeftFiberHomotopyEquiv`,
  `pullbackHomotopyPullbackRightFiberHomotopyEquiv`: fibre homotopy equivalence from `f.Pullback g`.

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

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

section Basic

variable (f : C(A, B)) (g : C(C, B))

/-- Construct a point of `HomotopyPullback f g` from points `a : A`, `c : C`, and a path
`γ : Path (f a) (g c)`. -/
def mk' {f : C(A, B)} {g : C(C, B)} (a : A) (c : C) (γ : Path (f a) (g c)) : HomotopyPullback f g :=
  ⟨(a, c, γ.toContinuousMap), γ.source, γ.target⟩

@[simp] theorem mk'_val {f : C(A, B)} {g : C(C, B)} (a : A) (c : C) (γ : Path (f a) (g c)) :
    (mk' a c γ : HomotopyPullback f g).val = (a, c, γ.toContinuousMap) := (rfl)

/-- Projection `HomotopyPullback f g → A` to the first leg. -/
def fst : C(HomotopyPullback f g, A) := ⟨fun p ↦ p.val.1, continuous_subtypeVal.fst⟩

/-- Projection `HomotopyPullback f g → C` to the second leg. -/
def snd : C(HomotopyPullback f g, C) := ⟨fun p ↦ p.val.2.1, continuous_subtypeVal.snd.fst⟩

/-- Projection `HomotopyPullback f g → C(I, B)` forgetting the endpoints and keeping the path. -/
def pathMap : C(HomotopyPullback f g, C(I, B)) :=
  ⟨fun p ↦ p.val.2.2, continuous_subtypeVal.snd.snd⟩

@[simp] theorem fst_apply (p : HomotopyPullback f g) : fst f g p = p.val.1 := (rfl)

@[simp] theorem snd_apply (p : HomotopyPullback f g) : snd f g p = p.val.2.1 := (rfl)

@[simp] theorem pathMap_apply (p : HomotopyPullback f g) : pathMap f g p = p.val.2.2 := (rfl)

theorem pathMap_zero (p : HomotopyPullback f g) : pathMap f g p 0 = f (fst f g p) := p.property.1

theorem pathMap_one (p : HomotopyPullback f g) : pathMap f g p 1 = g (snd f g p) := p.property.2

/-- Two points of `HomotopyPullback f g` are equal iff their `fst`, `snd`, and path evaluations
agree. -/
@[ext] theorem ext {f : C(A, B)} {g : C(C, B)} {p q : HomotopyPullback f g}
    (h₁ : fst f g p = fst f g q) (h₂ : snd f g p = snd f g q)
    (h₃ : ∀ t : I, pathMap f g p t = pathMap f g q t) : p = q :=
  Subtype.ext <| Prod.ext h₁ <| Prod.ext h₂ <| ContinuousMap.ext h₃

/-- The path component of a point `p : HomotopyPullback f g` as a `Path` from `f (fst f g p)` to
`g (snd f g p)`. -/
def path {f : C(A, B)} {g : C(C, B)} (p : HomotopyPullback f g) :
    Path (f (fst f g p)) (g (snd f g p)) :=
  ⟨pathMap f g p, pathMap_zero f g p, pathMap_one f g p⟩

@[simp] theorem path_apply {f : C(A, B)} {g : C(C, B)} (p : HomotopyPullback f g) (t : I) :
    path p t = pathMap f g p t := (rfl)

@[simp] theorem toContinuousMap_path {f : C(A, B)} {g : C(C, B)} (p : HomotopyPullback f g) :
    (path p).toContinuousMap = pathMap f g p := (rfl)

@[simp] theorem mk'_fst_snd_path {f : C(A, B)} {g : C(C, B)} (p : HomotopyPullback f g) :
    mk' (fst f g p) (snd f g p) (path p) = p := ext rfl rfl fun _ ↦ rfl

/-- The universal homotopy from `f ∘ fst` to `g ∘ snd` on `HomotopyPullback f g`. -/
def homotopy : (f.comp (fst f g)).Homotopy (g.comp (snd f g)) where
  toFun q := q.2.val.2.2 q.1
  continuous_toFun := continuous_subtypeVal.snd.snd.comp continuous_snd |>.eval continuous_fst
  map_zero_left p := p.property.1
  map_one_left p := p.property.2

@[simp] theorem homotopy_apply (t : I) (p : HomotopyPullback f g) :
    homotopy f g (t, p) = pathMap f g p t := (rfl)

@[simp] theorem evalAt_homotopy (p : HomotopyPullback f g) :
    (homotopy f g).evalAt p = path p := by ext _; rfl

end Basic

/-! ### Universal property and comparison from the strict pullback -/

section UniversalProperty

variable {X : Type u'} [TopologicalSpace X] {f : C(A, B)} {g : C(C, B)}

/-- **Universal property of the homotopy pullback.** A pair of continuous maps `α : C(X, A)`,
`β : C(X, C)` together with a homotopy `H : (f.comp α).Homotopy (g.comp β)` induces a continuous
map `lift α β H : C(X, HomotopyPullback f g)`. -/
def lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    C(X, HomotopyPullback f g) where
  toFun x := ⟨(α x, β x, (H.evalAt x).toContinuousMap), H.apply_zero x, H.apply_one x⟩
  continuous_toFun := by
    refine (α.continuous.prodMk (β.continuous.prodMk ?_)).subtype_mk _
    exact ContinuousMap.continuous_of_continuous_uncurry _ <|
      H.continuous.comp (continuous_snd.prodMk continuous_fst)

@[simp] theorem lift_val (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) (x : X) :
    (lift α β H x).val = (α x, β x, (H.evalAt x).toContinuousMap) := (rfl)

@[simp] theorem fst_comp_lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    (fst f g).comp (lift α β H) = α := by ext : 1; rfl

@[simp] theorem snd_comp_lift (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    (snd f g).comp (lift α β H) = β := by ext : 1; rfl

@[simp] theorem homotopy_comp_lift (α : C(X, A)) (β : C(X, C))
    (H : (f.comp α).Homotopy (g.comp β)) :
    ((homotopy f g).compContinuousMap (lift α β H)).cast
      (congrArg f.comp (fst_comp_lift α β H)) (congrArg g.comp (snd_comp_lift α β H)) = H := by
  ext ⟨_, _⟩ : 1; rfl

/-- Any continuous map `φ : C(X, HomotopyPullback f g)` is uniquely reconstructed as `lift` from
its two projections and the pulled-back universal homotopy. -/
theorem eq_lift (φ : C(X, HomotopyPullback f g)) :
    φ = lift ((fst f g).comp φ) ((snd f g).comp φ)
      (((homotopy f g).compContinuousMap φ).cast rfl rfl) := by
  ext x : 1; exact ext rfl rfl fun _ ↦ rfl

/-- Continuous maps `X → HomotopyPullback f g` correspond bijectively to homotopy-commutative cones
`(α : C(X, A), β : C(X, C), H : (f.comp α).Homotopy (g.comp β))`. -/
def liftEquiv (X : Type u') [TopologicalSpace X] (f : C(A, B)) (g : C(C, B)) :
    C(X, HomotopyPullback f g) ≃
      Σ (α : C(X, A)) (β : C(X, C)), (f.comp α).Homotopy (g.comp β) where
  toFun φ := ⟨(fst f g).comp φ, (snd f g).comp φ,
    ((homotopy f g).compContinuousMap φ).cast rfl rfl⟩
  invFun t := lift t.1 t.2.1 t.2.2
  left_inv φ := (eq_lift φ).symm
  right_inv := fun ⟨α, β, H⟩ ↦ by
    have hα := fst_comp_lift α β H; have hβ := snd_comp_lift α β H
    refine Sigma.ext hα ?_; cases hα
    refine heq_of_eq (Sigma.ext hβ ?_); cases hβ
    exact heq_of_eq (by ext ⟨_, _⟩ : 1; rfl)

@[simp] theorem liftEquiv_apply (φ : C(X, HomotopyPullback f g)) :
    liftEquiv X f g φ = ⟨(fst f g).comp φ, (snd f g).comp φ,
      ((homotopy f g).compContinuousMap φ).cast rfl rfl⟩ := (rfl)

@[simp] theorem liftEquiv_symm_apply
    (t : Σ (α : C(X, A)) (β : C(X, C)), (f.comp α).Homotopy (g.comp β)) :
    (liftEquiv X f g).symm t = lift t.1 t.2.1 t.2.2 := (rfl)

/-- Lift a strictly commuting cone `f ∘ α = g ∘ β` to `HomotopyPullback f g` using constant
paths. -/
def liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) : C(X, HomotopyPullback f g) :=
  lift α β ((ContinuousMap.Homotopy.refl (f.comp α)).cast rfl h)

theorem liftStrict_def {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    liftStrict h = lift α β ((ContinuousMap.Homotopy.refl (f.comp α)).cast rfl h) := (rfl)

@[simp] theorem liftStrict_val {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) (x : X) :
    (liftStrict h x).val = (α x, β x, ContinuousMap.const I (f (α x))) :=
  Prod.ext rfl (Prod.ext rfl (ContinuousMap.ext fun _ ↦ rfl))

@[simp] theorem fst_comp_liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    (fst f g).comp (liftStrict h) = α := fst_comp_lift _ _ _

@[simp] theorem snd_comp_liftStrict {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    (snd f g).comp (liftStrict h) = β := snd_comp_lift _ _ _

/-- Precomposing `liftStrict` with a cone morphism `φ` yields `liftStrict` on the pulled-back
strictly commuting cone. -/
theorem liftStrict_comp {Y : Type v'} [TopologicalSpace Y] {α : C(X, A)} {β : C(X, C)}
    (h : f.comp α = g.comp β) {α' : C(Y, A)} {β' : C(Y, C)} (h' : f.comp α' = g.comp β')
    (φ : C(Y, X)) (hα : α.comp φ = α') (hβ : β.comp φ = β') :
    (liftStrict h).comp φ = liftStrict h' := by
  ext y : 1; have hαy : α (φ y) = α' y := ContinuousMap.congr_fun hα y
  exact ext (by simpa using hαy) (by simpa using ContinuousMap.congr_fun hβ y)
    fun _ ↦ by simpa using congrArg f hαy

/-- The canonical comparison map from the strict pullback `f.Pullback g` to `HomotopyPullback f g`
sending `(a, c)` with `f a = g c` to `(a, c, const I (f a))`. -/
def ofPullback (f : C(A, B)) (g : C(C, B)) : C((⇑f).Pullback ⇑g, HomotopyPullback f g) :=
  liftStrict (α := ContinuousMap.pullbackFst ⇑f ⇑g) (β := ContinuousMap.pullbackSnd ⇑f ⇑g)
    (ContinuousMap.ext fun x ↦ by
        simpa [Function.Pullback.fst, Function.Pullback.snd] using x.property)

@[simp] theorem ofPullback_val (f : C(A, B)) (g : C(C, B)) (x : (⇑f).Pullback ⇑g) :
    (ofPullback f g x).val = (x.val.1, x.val.2, ContinuousMap.const I (f x.val.1)) := by
  simp [ofPullback, Function.Pullback.fst, Function.Pullback.snd]

@[simp] theorem fst_comp_ofPullback (f : C(A, B)) (g : C(C, B)) :
    (fst f g).comp (ofPullback f g) = ContinuousMap.pullbackFst ⇑f ⇑g := fst_comp_liftStrict _

@[simp] theorem snd_comp_ofPullback (f : C(A, B)) (g : C(C, B)) :
    (snd f g).comp (ofPullback f g) = ContinuousMap.pullbackSnd ⇑f ⇑g := snd_comp_liftStrict _

theorem pathMap_ofPullback_apply (f : C(A, B)) (g : C(C, B)) (x : (⇑f).Pullback ⇑g) (t : I) :
    pathMap f g (ofPullback f g x) t = f x.val.1 := by simp

end UniversalProperty

/-! ### Symmetry -/

/-- Swap the two factors of `HomotopyPullback f g` by reversing the path in `B`. -/
def swap (f : C(A, B)) (g : C(C, B)) : C(HomotopyPullback f g, HomotopyPullback g f) where
  toFun p := ⟨(p.val.2.1, p.val.1, p.val.2.2.comp ⟨σ, continuous_symm⟩),
    (congrArg p.val.2.2 symm_zero).trans p.property.2,
    (congrArg p.val.2.2 symm_one).trans p.property.1⟩
  continuous_toFun :=
    (continuous_subtypeVal.snd.fst.prodMk <| continuous_subtypeVal.fst.prodMk <|
      (ContinuousMap.continuous_precomp ⟨σ, continuous_symm⟩).comp
        continuous_subtypeVal.snd.snd).subtype_mk _

@[simp] theorem swap_val (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    (swap f g p).val = (p.val.2.1, p.val.1, p.val.2.2.comp ⟨σ, continuous_symm⟩) := (rfl)

theorem fst_swap (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    fst g f (swap f g p) = snd f g p := (rfl)

theorem snd_swap (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    snd g f (swap f g p) = fst f g p := (rfl)

@[simp] theorem fst_comp_swap (f : C(A, B)) (g : C(C, B)) :
    (fst g f).comp (swap f g) = snd f g := by ext : 1; rfl

@[simp] theorem snd_comp_swap (f : C(A, B)) (g : C(C, B)) :
    (snd g f).comp (swap f g) = fst f g := by ext : 1; rfl

theorem pathMap_swap_apply (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) (t : I) :
    pathMap g f (swap f g p) t = pathMap f g p (σ t) := (rfl)

@[simp] theorem swap_comp_swap (f : C(A, B)) (g : C(C, B)) :
    (swap g f).comp (swap f g) = .id (HomotopyPullback f g) := by
  ext p : 1; exact ext rfl rfl fun t ↦ congrArg (pathMap f g p) (symm_symm t)

@[simp] theorem swap_swap (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    swap g f (swap f g p) = p := ContinuousMap.congr_fun (swap_comp_swap f g) p

/-- **Symmetry of homotopy pullbacks.** Swapping the two legs and reversing the path is a
homeomorphism `HomotopyPullback f g ≃ₜ HomotopyPullback g f`. -/
def swapHomeomorph (f : C(A, B)) (g : C(C, B)) : HomotopyPullback f g ≃ₜ HomotopyPullback g f where
  toFun := swap f g
  invFun := swap g f
  left_inv := swap_swap f g
  right_inv := swap_swap g f
  continuous_toFun := (swap f g).continuous
  continuous_invFun := (swap g f).continuous

@[simp] theorem coe_swapHomeomorph (f : C(A, B)) (g : C(C, B)) :
    (swapHomeomorph f g : C(HomotopyPullback f g, HomotopyPullback g f)) = swap f g := (rfl)

@[simp] theorem swapHomeomorph_apply (f : C(A, B)) (g : C(C, B)) (p : HomotopyPullback f g) :
    swapHomeomorph f g p = swap f g p := (rfl)

@[simp] theorem swapHomeomorph_symm (f : C(A, B)) (g : C(C, B)) :
    (swapHomeomorph f g).symm = swapHomeomorph g f := (rfl)

@[simp] theorem swapHomeomorph_trans_swapHomeomorph (f : C(A, B)) (g : C(C, B)) :
    (swapHomeomorph f g).trans (swapHomeomorph g f) = .refl (HomotopyPullback f g) := by
  ext : 1; exact swap_swap f g _

@[simp] theorem swap_comp_lift {X : Type u'} [TopologicalSpace X] {f : C(A, B)} {g : C(C, B)}
    (α : C(X, A)) (β : C(X, C)) (H : (f.comp α).Homotopy (g.comp β)) :
    (swap f g).comp (lift α β H) = lift β α H.symm := by
  ext x : 1; exact ext rfl rfl fun _ ↦ rfl

@[simp] theorem swap_comp_liftStrict {X : Type u'} [TopologicalSpace X] {f : C(A, B)} {g : C(C, B)}
    {α : C(X, A)} {β : C(X, C)} (h : f.comp α = g.comp β) :
    (swap f g).comp (liftStrict h) = liftStrict h.symm := by
  ext x : 1; exact ext (by simp) (by simp) fun _ ↦ by simpa using ContinuousMap.congr_fun h x

@[simp] theorem swap_comp_ofPullback (f : C(A, B)) (g : C(C, B)) :
    (swap f g).comp (ofPullback f g) =
      (ofPullback g f).comp (Homeomorph.pullbackComm ⇑f ⇑g : C(_, _)) := by
  ext x : 1; exact ext (by simp) (by simp) fun _ ↦ by simpa using x.property

@[simp] theorem swap_comp_ofPullback_comp_pullbackComm (f : C(A, B)) (g : C(C, B)) :
    (swap g f).comp ((ofPullback g f).comp (Homeomorph.pullbackComm ⇑f ⇑g : C(_, _))) =
      ofPullback f g := by
  rw [← ContinuousMap.comp_assoc, swap_comp_ofPullback, ContinuousMap.comp_assoc,
    ContinuousMap.pullbackComm_comp_pullbackComm, ContinuousMap.comp_id]

/-! ### Pullback-of-replacement factorization, fibrations, and fibres -/

/-- `HomotopyPullback f g` is homeomorphic over `C` to the strict pullback along `g` of the
mapping-path endpoint fibration `MappingPathSpace.endpoint f`. -/
def pullbackEndpointLeftHomeomorph (f : C(A, B)) (g : C(C, B)) :
    HomotopyPullback f g ≃ₜ (⇑g).Pullback ⇑(MappingPathSpace.endpoint f) where
  toFun p := ⟨(p.val.2.1, ⟨(p.val.1, p.val.2.2), p.property.1⟩), p.property.2.symm.trans
    (MappingPathSpace.endpoint_apply f ⟨(p.val.1, p.val.2.2), p.property.1⟩).symm⟩
  invFun q := ⟨(q.val.2.val.1, q.val.1, q.val.2.val.2), q.val.2.property,
    (MappingPathSpace.endpoint_apply f q.val.2).symm.trans q.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem pullbackEndpointLeftHomeomorph_fst (f : C(A, B)) (g : C(C, B))
    (p : HomotopyPullback f g) : (pullbackEndpointLeftHomeomorph f g p).val.1 = snd f g p := (rfl)

@[simp] theorem pullbackEndpointLeftHomeomorph_snd_val (f : C(A, B)) (g : C(C, B))
    (p : HomotopyPullback f g) :
    (pullbackEndpointLeftHomeomorph f g p).val.2.val = (fst f g p, pathMap f g p) := (rfl)

@[simp] theorem pullbackEndpointLeftHomeomorph_symm_val (f : C(A, B)) (g : C(C, B))
    (q : (⇑g).Pullback ⇑(MappingPathSpace.endpoint f)) :
    ((pullbackEndpointLeftHomeomorph f g).symm q).val = (q.val.2.val.1, q.val.1, q.val.2.val.2) :=
        (rfl)

@[simp] theorem pullbackFst_comp_pullbackEndpointLeftHomeomorph (f : C(A, B)) (g : C(C, B)) :
    (ContinuousMap.pullbackFst (⇑g) ⇑(MappingPathSpace.endpoint f)).comp
      (pullbackEndpointLeftHomeomorph f g :
        C(HomotopyPullback f g, (⇑g).Pullback ⇑(MappingPathSpace.endpoint f))) = snd f g := by
  ext p : 1; simp [Function.Pullback.fst]

/-- **The second projection of any homotopy pullback is a Hurewicz fibration** in every lifting
universe, as the pullback along `g` of `MappingPathSpace.endpoint f` precomposed with
`pullbackEndpointLeftHomeomorph f g`. -/
theorem isHurewiczFibration_snd (f : C(A, B)) (g : C(C, B)) :
    IsHurewiczFibration.{u'} (snd f g) := by
  convert ((MappingPathSpace.isHurewiczFibration_endpoint f).pullback g).comp_homeomorph
    (pullbackEndpointLeftHomeomorph f g) using 1
  ext; rfl

/-- **The first projection of any homotopy pullback is a Hurewicz fibration** in every lifting
universe. -/
theorem isHurewiczFibration_fst (f : C(A, B)) (g : C(C, B)) :
    IsHurewiczFibration.{u'} (fst f g) := by
  convert (isHurewiczFibration_snd g f).comp_homeomorph (swapHomeomorph f g) using 1
  ext; rfl

/-- The strict fibre of `snd f g` over `c : C` is canonically homeomorphic to
`MappingPathFiber f (g c)`. -/
def sndFiberHomeomorph (f : C(A, B)) (g : C(C, B)) (c : C) :
    (snd f g) ⁻¹' {c} ≃ₜ MappingPathFiber f (g c) where
  toFun x := ⟨(x.val.val.1, x.val.val.2.2), x.val.property.1, x.val.property.2.trans
      (congrArg g x.property)⟩
  invFun p := ⟨⟨(p.val.1, c, p.val.2), p.property.1, p.property.2⟩, rfl⟩
  left_inv x := Subtype.ext <| ext rfl x.property.symm fun _ ↦ rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem sndFiberHomeomorph_val (f : C(A, B)) (g : C(C, B)) (c : C) (x : (snd f g) ⁻¹' {c}) :
    (sndFiberHomeomorph f g c x).val = (fst f g x.val, pathMap f g x.val) := (rfl)

@[simp] theorem sndFiberHomeomorph_symm_val (f : C(A, B)) (g : C(C, B)) (c : C)
    (p : MappingPathFiber f (g c)) :
    (((sndFiberHomeomorph f g c).symm p).val : HomotopyPullback f g).val = (p.val.1, c, p.val.2) :=
  (rfl)

/-- The strict fibre of `fst f g` over `a : A` is canonically homeomorphic to
`MappingPathFiber g (f a)` by reversing paths. -/
def fstFiberHomeomorph (f : C(A, B)) (g : C(C, B)) (a : A) :
    (fst f g) ⁻¹' {a} ≃ₜ MappingPathFiber g (f a) :=
  ((swapHomeomorph f g).sets rfl).trans (sndFiberHomeomorph g f a)

@[simp] theorem fstFiberHomeomorph_val_fst (f : C(A, B)) (g : C(C, B)) (a : A)
    (x : (fst f g) ⁻¹' {a}) : (fstFiberHomeomorph f g a x).val.1 = snd f g x.val := (rfl)

@[simp] theorem fstFiberHomeomorph_val_snd_apply (f : C(A, B)) (g : C(C, B)) (a : A)
    (x : (fst f g) ⁻¹' {a}) (t : I) :
    (fstFiberHomeomorph f g a x).val.2 t = pathMap f g x.val (σ t) := (rfl)

@[simp] theorem fstFiberHomeomorph_symm_val (f : C(A, B)) (g : C(C, B)) (a : A)
    (p : MappingPathFiber g (f a)) :
    (((fstFiberHomeomorph f g a).symm p).val : HomotopyPullback f g).val =
      (a, p.val.1, p.val.2.comp ⟨σ, continuous_symm⟩) := (rfl)

/-! ### Special cases: identity and constant legs -/

/-- `HomotopyPullback f (.id B)` is homeomorphic to `MappingPathSpace f`, since `c = γ 1` is
uniquely determined by the path. -/
def idRightHomeomorph (f : C(A, B)) : HomotopyPullback f (.id B) ≃ₜ MappingPathSpace f where
  toFun p := ⟨(p.val.1, p.val.2.2), p.property.1⟩
  invFun q := ⟨(q.val.1, MappingPathSpace.endpoint f q, q.val.2), q.property,
    (MappingPathSpace.endpoint_apply f q).symm⟩
  left_inv p := ext rfl ((MappingPathSpace.endpoint_apply f _).trans p.property.2) fun _ ↦ rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem idRightHomeomorph_val (f : C(A, B)) (p : HomotopyPullback f (.id B)) :
    (idRightHomeomorph f p).val = (fst f (.id B) p, pathMap f (.id B) p) := (rfl)

@[simp] theorem idRightHomeomorph_symm_val (f : C(A, B)) (q : MappingPathSpace f) :
    ((idRightHomeomorph f).symm q).val = (q.val.1, MappingPathSpace.endpoint f q, q.val.2) := (rfl)

/-- For any map `f : C(A, B)`, the strict comparison of the horizontal-identity square
`f ∘ id = id ∘ f` identifies under `idRightHomeomorph f` with `MappingPathSpace.incl f`. -/
@[simp] theorem idRightHomeomorph_comp_liftStrict_id (f : C(A, B)) :
    (idRightHomeomorph f : C(_, _)).comp (liftStrict (f.comp_id.trans f.id_comp.symm)) =
      MappingPathSpace.incl f := by
  ext x : 1; apply Subtype.ext
  rw [ContinuousMap.comp_apply, ContinuousMap.coe_apply, idRightHomeomorph_val]; simp

/-- `HomotopyPullback (.id B) g` is homeomorphic to `MappingPathSpace g` via path reversal. -/
def idLeftHomeomorph (g : C(C, B)) : HomotopyPullback (.id B) g ≃ₜ MappingPathSpace g :=
  (swapHomeomorph (.id B) g).trans (idRightHomeomorph g)

@[simp] theorem idLeftHomeomorph_val (g : C(C, B)) (p : HomotopyPullback (.id B) g) :
    (idLeftHomeomorph g p).val =
      (snd (.id B) g p, (pathMap (.id B) g p).comp ⟨σ, continuous_symm⟩) := (rfl)

@[simp] theorem idLeftHomeomorph_symm_val (g : C(C, B)) (q : MappingPathSpace g) :
    ((idLeftHomeomorph g).symm q).val =
      (MappingPathSpace.endpoint g q, q.val.1, q.val.2.comp ⟨σ, continuous_symm⟩) := (rfl)

/-- `HomotopyPullback f (.const C b)` splits as `MappingPathFiber f b × C`, since the path endpoint
condition `γ 1 = b` is independent of `c : C`. -/
def constRightProdHomeomorph (f : C(A, B)) (b : B) :
    HomotopyPullback f (.const C b) ≃ₜ MappingPathFiber f b × C where
  toFun p := (⟨(p.val.1, p.val.2.2), p.property.1, p.property.2⟩, p.val.2.1)
  invFun q := ⟨(q.1.val.1, q.2, q.1.val.2), q.1.property.1, q.1.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem constRightProdHomeomorph_fst_val (f : C(A, B)) (b : B)
    (p : HomotopyPullback f (.const C b)) :
    (constRightProdHomeomorph f b p).1.val = (fst f (.const C b) p, pathMap f (.const C b) p) :=
  (rfl)

@[simp] theorem constRightProdHomeomorph_snd (f : C(A, B)) (b : B)
    (p : HomotopyPullback f (.const C b)) :
    (constRightProdHomeomorph f b p).2 = snd f (.const C b) p := (rfl)

@[simp] theorem constRightProdHomeomorph_symm_val (f : C(A, B)) (b : B)
    (q : MappingPathFiber f b × C) :
    ((constRightProdHomeomorph f b).symm q).val = (q.1.val.1, q.2, q.1.val.2) := (rfl)

/-- Over a one-point right corner `C`, `HomotopyPullback f g` is canonically homeomorphic to
`MappingPathFiber f (g default)`. -/
def uniqueRightHomeomorph [Unique C] (f : C(A, B)) (g : C(C, B)) :
    HomotopyPullback f g ≃ₜ MappingPathFiber f (g default) where
  toFun p := ⟨(p.val.1, p.val.2.2), p.property.1,
    p.property.2.trans (congrArg g (Unique.eq_default p.val.2.1))⟩
  invFun q := ⟨(q.val.1, default, q.val.2), q.property.1, q.property.2⟩
  left_inv _ := ext rfl (Unique.eq_default _).symm fun _ ↦ rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem uniqueRightHomeomorph_val [Unique C] (f : C(A, B)) (g : C(C, B))
    (p : HomotopyPullback f g) :
    (uniqueRightHomeomorph f g p).val = (fst f g p, pathMap f g p) := (rfl)

@[simp] theorem uniqueRightHomeomorph_symm_val [Unique C] (f : C(A, B)) (g : C(C, B))
    (q : MappingPathFiber f (g default)) :
    ((uniqueRightHomeomorph f g).symm q).val = (q.val.1, default, q.val.2) := (rfl)

/-- Under `uniqueRightHomeomorph f g`, the strict-square comparison of any commuting square from
the strict fibre `f ⁻¹' {g default}` over a one-point space `C` is the constant-path fibre
inclusion `MappingPathFiber.ofFiber f (g default)`. -/
@[simp] theorem uniqueRightHomeomorph_comp_liftStrict_eq_ofFiber [Unique C]
    {f : C(A, B)} {g : C(C, B)} {p' : C(↥(f ⁻¹' {g default}), C)}
    (hcomm : f.comp ⟨Subtype.val, continuous_subtypeVal⟩ = g.comp p') :
    (uniqueRightHomeomorph f g : C(_, _)).comp (liftStrict hcomm) =
      MappingPathFiber.ofFiber f (g default) := by
  ext x : 1; apply Subtype.ext
  rw [ContinuousMap.comp_apply, ContinuousMap.coe_apply, uniqueRightHomeomorph_val]
  simp [Set.mem_singleton_iff.mp x.property]

/-- Over a one-point left corner `A`, `HomotopyPullback f g` is canonically homeomorphic to
`MappingPathFiber g (f default)` via path reversal. -/
def uniqueLeftHomeomorph [Unique A] (f : C(A, B)) (g : C(C, B)) :
    HomotopyPullback f g ≃ₜ MappingPathFiber g (f default) :=
  (swapHomeomorph f g).trans (uniqueRightHomeomorph g f)

@[simp] theorem uniqueLeftHomeomorph_val [Unique A] (f : C(A, B)) (g : C(C, B))
    (p : HomotopyPullback f g) :
    (uniqueLeftHomeomorph f g p).val = (snd f g p, (pathMap f g p).comp ⟨σ, continuous_symm⟩) :=
  (rfl)

@[simp] theorem uniqueLeftHomeomorph_symm_val [Unique A] (f : C(A, B)) (g : C(C, B))
    (q : MappingPathFiber g (f default)) :
    ((uniqueLeftHomeomorph f g).symm q).val =
      (default, q.val.1, q.val.2.comp ⟨σ, continuous_symm⟩) := (rfl)

/-- The homotopy pullback of two maps out of one-point spaces `A` and `C` is canonically
homeomorphic to `Path (f default) (g default)`. -/
def homeomorphPathOfUnique [Unique A] [Unique C] (f : C(A, B)) (g : C(C, B)) :
    HomotopyPullback f g ≃ₜ Path (f default) (g default) where
  toFun p := ⟨p.val.2.2, p.property.1.trans (congrArg f (Unique.eq_default _)),
    p.property.2.trans (congrArg g (Unique.eq_default _))⟩
  invFun γ := mk' default default γ
  left_inv p := ext (Unique.eq_default _).symm (Unique.eq_default _).symm fun _ ↦ rfl
  right_inv _ := by ext _; rfl
  continuous_toFun := continuous_induced_rng.2 continuous_subtypeVal.snd.snd
  continuous_invFun :=
    (continuous_const.prodMk (continuous_const.prodMk continuous_induced_dom)).subtype_mk _

@[simp] theorem homeomorphPathOfUnique_apply [Unique A] [Unique C] (f : C(A, B)) (g : C(C, B))
    (p : HomotopyPullback f g) (t : I) : homeomorphPathOfUnique f g p t = pathMap f g p t := (rfl)

@[simp] theorem homeomorphPathOfUnique_symm_apply [Unique A] [Unique C] (f : C(A, B)) (g : C(C, B))
    (γ : Path (f default) (g default)) :
    (homeomorphPathOfUnique f g).symm γ = mk' default default γ := (rfl)

/-- The homotopy pullback of a map out of a one-point space `A` with itself is homeomorphic to the
based loop space `Ω B (f default)`. -/
abbrev homeomorphLoopSpaceOfUnique [Unique A] (f : C(A, B)) :
    HomotopyPullback f f ≃ₜ Ω B (f default) := homeomorphPathOfUnique f f

/-! ### Functoriality in maps of cospans -/

section Functoriality

variable {A' : Type u'} {B' : Type v'} {C' : Type w'}
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
    ((a.continuous.comp continuous_subtypeVal.fst).prodMk <|
      (c.continuous.comp continuous_subtypeVal.snd.fst).prodMk <|
        (ContinuousMap.continuous_postcomp b).comp continuous_subtypeVal.snd.snd).subtype_mk _

@[simp] theorem map_val (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) (p : HomotopyPullback f g) :
    (map a b c hf hg p).val = (a p.val.1, c p.val.2.1, b.comp p.val.2.2) := (rfl)

@[simp] theorem fst_comp_map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) :
    (fst f' g').comp (map a b c hf hg) = a.comp (fst f g) := by ext : 1; rfl

@[simp] theorem snd_comp_map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) :
    (snd f' g').comp (map a b c hf hg) = c.comp (snd f g) := by ext : 1; rfl

@[simp] theorem swap_comp_map (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) :
    (swap f' g').comp (map a b c hf hg) = (map c b a hg hf).comp (swap f g) := by
  ext p : 1; exact ext rfl rfl fun _ ↦ rfl

@[simp] theorem map_comp_ofPullback (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c) :
    (map a b c hf hg).comp (ofPullback f g) =
      (ofPullback f' g').comp (ContinuousMap.mapPullback (f₁ := ⇑f) (g₁ := ⇑g) (f₂ := ⇑f')
        (g₂ := ⇑g') a b c (congrArg DFunLike.coe hf.symm) (congrArg DFunLike.coe hg.symm)) := by
  ext x : 1
  exact ext (by simp) (by simp) fun _ ↦ by simpa using ContinuousMap.congr_fun hf x.val.1

@[simp] theorem map_id (f : C(A, B)) (g : C(C, B)) :
    map (.id A) (.id B) (.id C) ((ContinuousMap.id_comp f).trans (ContinuousMap.comp_id f).symm)
      ((ContinuousMap.id_comp g).trans (ContinuousMap.comp_id g).symm) =
      .id (HomotopyPullback f g) := by ext p : 1; exact ext rfl rfl fun _ ↦ rfl

theorem map_comp {A'' B'' C'' : Type*} [TopologicalSpace A''] [TopologicalSpace B'']
    [TopologicalSpace C''] {f'' : C(A'', B'')} {g'' : C(C'', B'')}
    (a : C(A, A')) (b : C(B, B')) (c : C(C, C'))
    (hf : b.comp f = f'.comp a) (hg : b.comp g = g'.comp c)
    (a' : C(A', A'')) (b' : C(B', B'')) (c' : C(C', C''))
    (hf' : b'.comp f' = f''.comp a') (hg' : b'.comp g' = g''.comp c') :
    (map a' b' c' hf' hg').comp (map a b c hf hg) = map (a'.comp a) (b'.comp b) (c'.comp c)
      (by rw [ContinuousMap.comp_assoc, hf, ← ContinuousMap.comp_assoc, hf',
        ContinuousMap.comp_assoc])
      (by rw [ContinuousMap.comp_assoc, hg, ← ContinuousMap.comp_assoc, hg',
        ContinuousMap.comp_assoc]) := by ext p : 1; exact ext rfl rfl fun _ ↦ rfl

end Functoriality

end HomotopyPullback

/-! ### Comparison with the strict pullback along a Hurewicz fibration -/

namespace IsHurewiczFibration

variable {A : Type u} {B : Type v} {C : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- **Strict vs. homotopy pullback along a Hurewicz fibration (left leg).** When `p : C(A, B)` is
a Hurewicz fibration, the constant-path inclusion `HomotopyPullback.ofPullback p g` from the strict
pullback `p.Pullback g` to `HomotopyPullback p g` is part of a fibre homotopy equivalence over
`C`. -/
noncomputable def pullbackHomotopyPullbackLeftFiberHomotopyEquiv
    {p : C(A, B)} (hp : IsHurewiczFibration.{max u v} p) (g : C(C, B)) :
    FiberHomotopyEquiv (ContinuousMap.pullbackSnd ⇑p ⇑g) (HomotopyPullback.snd p g) :=
  let Λ := hp.nonempty_liftingFunction.some
  (FiberHomotopyEquiv.ofHomeomorph (Homeomorph.pullbackComm ⇑p ⇑g)
      (ContinuousMap.pullbackFst_comp_pullbackComm ⇑p ⇑g)).trans
    ((FiberHomotopyEquiv.pullback (⇑g) Λ.mappingPathFiberHomotopyEquiv).trans
      (FiberHomotopyEquiv.ofHomeomorph (HomotopyPullback.pullbackEndpointLeftHomeomorph p g)
        (HomotopyPullback.pullbackFst_comp_pullbackEndpointLeftHomeomorph p g)).symm)

@[simp] theorem pullbackHomotopyPullbackLeftFiberHomotopyEquiv_toFun
    {p : C(A, B)} (hp : IsHurewiczFibration.{max u v} p) (g : C(C, B)) :
    (hp.pullbackHomotopyPullbackLeftFiberHomotopyEquiv g).toFun =
      HomotopyPullback.ofPullback p g := by
  ext x : 1; exact HomotopyPullback.ext
    (by simp [pullbackHomotopyPullbackLeftFiberHomotopyEquiv])
    (by simp [pullbackHomotopyPullbackLeftFiberHomotopyEquiv])
    fun _ ↦ by simp [pullbackHomotopyPullbackLeftFiberHomotopyEquiv]

/-- **Strict vs. homotopy pullback along a Hurewicz fibration (right leg).** When `q : C(C, B)` is
a Hurewicz fibration, `HomotopyPullback.ofPullback f q` is part of a fibre homotopy equivalence
from `f.Pullback q` to `HomotopyPullback f q` over `A`. -/
noncomputable def pullbackHomotopyPullbackRightFiberHomotopyEquiv
    (f : C(A, B)) {q : C(C, B)} (hq : IsHurewiczFibration.{max w v} q) :
    FiberHomotopyEquiv (ContinuousMap.pullbackFst ⇑f ⇑q) (HomotopyPullback.fst f q) :=
  (FiberHomotopyEquiv.ofHomeomorph (Homeomorph.pullbackComm ⇑f ⇑q)
      (ContinuousMap.pullbackSnd_comp_pullbackComm ⇑f ⇑q)).trans
    ((hq.pullbackHomotopyPullbackLeftFiberHomotopyEquiv f).trans
      (FiberHomotopyEquiv.ofHomeomorph (p := HomotopyPullback.fst f q)
        (HomotopyPullback.swapHomeomorph f q)
        (by rw [HomotopyPullback.coe_swapHomeomorph, HomotopyPullback.snd_comp_swap])).symm)

@[simp] theorem pullbackHomotopyPullbackRightFiberHomotopyEquiv_toFun
    (f : C(A, B)) {q : C(C, B)} (hq : IsHurewiczFibration.{max w v} q) :
    (hq.pullbackHomotopyPullbackRightFiberHomotopyEquiv f).toFun =
      HomotopyPullback.ofPullback f q := by
  simp [pullbackHomotopyPullbackRightFiberHomotopyEquiv, ContinuousMap.comp_assoc]

end IsHurewiczFibration

end TauCeti
