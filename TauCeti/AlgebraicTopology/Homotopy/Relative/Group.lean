/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
public import TauCeti.Topology.Homotopy.HomotopicWith
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homotopy

/-!
# The group structure on relative homotopy groups

Let `X = (X, A, a₀)` be a based pair and let `n` be the cardinality of the index type `N`. This
file makes the relative homotopy set `π_{n+1}(X, A, a₀) = TauCeti.RelHomotopyGroup N X` a group
when `N` is nonempty, that is in degrees at least two, and a commutative group when `N` is
nontrivial, that is in degrees at least three. It then proves that the induced maps, the boundary
map `π_{n+1}(X, A, a₀) → π_n(A, a₀)` and the map `π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀)` of the long
exact sequence are homomorphisms. For `N` empty, `π_1(X, A, a₀)` remains a pointed set, and
`π_2(X, A, a₀)` receives no commutative structure.

The group structure is transported from Mathlib's `HomotopyGroup`. Let `P` be the space
`TauCeti.BasedTopPair.pathSpace X` of paths in `X` from a point of `A` to `a₀`, with the
compact-open topology, pointed by the constant path `c` at `a₀`. Currying a relative cube
`p : I × I^N → X` in its distinguished first coordinate gives the generalized loop
`t ↦ (s ↦ p (s, t))` in `P`, and this is a homeomorphism
`TauCeti.RelGenLoop.pathSpaceHomeo : RelGenLoop N X ≃ₜ Ω^ N P c`. Homotopy through relative cubes
is path connectedness in the space of relative cubes (`TauCeti.RelGenLoop.homotopic_iff_joined`),
and homotopy of generalized loops is path connectedness in `Ω^ N P c`
(`GenLoop.homotopic_iff_joined`), so the homeomorphism descends to a bijection
`π_{n+1}(X, A, a₀) ≃ π_n(P, c)`. The group axioms, the independence of the direction of
concatenation and the Eckmann–Hilton argument are therefore inherited from Mathlib.

Concretely, the product of two classes is the class of the concatenation of representatives in
any direction `i : N` of the cube `I^N` (`TauCeti.RelHomotopyGroup.mul_spec`), never in the
distinguished direction, and in the order of Mathlib's `HomotopyGroup.mul_spec`.

## Main declarations

* `TauCeti.BasedTopPair.pathSpace`: the space of paths from `A` to `a₀`.
* `TauCeti.RelGenLoop.pathSpaceHomeo`: relative cubes are generalized loops in the path space.
* `TauCeti.RelGenLoop.transAt`, `TauCeti.RelGenLoop.symmAt`: concatenation and reversal of
  relative cubes along a direction of `I^N`.
* `TauCeti.RelHomotopyGroup.pathSpaceEquiv`, `TauCeti.RelHomotopyGroup.pathSpaceMulEquiv`:
  `π_{n+1}(X, A, a₀) ≅ π_n(P, c)`.
* `TauCeti.RelHomotopyGroup.group`, `TauCeti.RelHomotopyGroup.commGroup`: the group structures,
  characterised by `TauCeti.RelHomotopyGroup.one_def`, `TauCeti.RelHomotopyGroup.mul_spec` and
  `TauCeti.RelHomotopyGroup.inv_spec`.
* `TauCeti.RelHomotopyGroup.mapHom`, `TauCeti.RelHomotopyGroup.boundaryHom`,
  `TauCeti.RelHomotopyGroup.ofHomotopyGroupHom`: the maps of the long exact sequence as
  homomorphisms.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.1, for relative homotopy groups and their group
  structure, and Section 4.3, where the space of paths from the subspace to the basepoint appears
  as the homotopy fibre of the inclusion.
-/

public section

noncomputable section

universe u v

open CategoryTheory
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

namespace BasedTopPair

variable (X : BasedTopPair.{u})

/-- The space of paths in the based pair `X = (X, A, a₀)` that start in `A` and end at `a₀`, as a
subspace of `C(I, X)` with the compact-open topology. Its homotopy groups at the constant path are
the relative homotopy groups of `X`, shifted down by one degree. -/
def pathSpace : Set C(I, X.pair.fst) :=
  {γ | γ 0 ∈ Set.range X.pair.map ∧ γ 1 = X.pair.map X.basepoint}

theorem mem_pathSpace_iff {γ : C(I, X.pair.fst)} :
    γ ∈ X.pathSpace ↔ γ 0 ∈ Set.range X.pair.map ∧ γ 1 = X.pair.map X.basepoint :=
  Iff.rfl

/-- The constant path at `a₀`, the basepoint of the path space. -/
def pathSpaceBase : X.pathSpace :=
  ⟨ContinuousMap.const _ (X.pair.map X.basepoint), ⟨X.basepoint, rfl⟩, rfl⟩

@[simp]
theorem coe_pathSpaceBase :
    (X.pathSpaceBase : C(I, X.pair.fst)) = ContinuousMap.const _ (X.pair.map X.basepoint) :=
  (rfl)

end BasedTopPair

namespace RelGenLoop

variable {N : Type v} {X Y : BasedTopPair.{u}}

/-- The path `s ↦ p (s, t)` in the distinguished direction of a relative cube `p`. -/
private def toPathSpace (p : RelGenLoop N X) (t : I^N) : X.pathSpace :=
  ⟨⟨fun s => p (s, t),
      (map_continuous (p : C(I × (I^N), X.pair.fst))).comp (Continuous.prodMk_left t)⟩,
    apply_zero_mem_range p t, apply_one p t⟩

private theorem continuous_toPathSpace (p : RelGenLoop N X) : Continuous (toPathSpace p) := by
  refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
  exact (map_continuous (p : C(I × (I^N), X.pair.fst))).comp continuous_swap

/-- Currying a relative cube `p : I × I^N → X` in its distinguished first coordinate identifies it
with the generalized loop `t ↦ (s ↦ p (s, t))` in the space of paths from `A` to `a₀`. -/
def pathSpaceHomeo : RelGenLoop N X ≃ₜ Ω^ N X.pathSpace X.pathSpaceBase where
  toFun p := ⟨⟨toPathSpace p, continuous_toPathSpace p⟩, fun t ht => Subtype.ext <|
    ContinuousMap.ext fun s => apply_of_mem_boundary p s ht⟩
  invFun γ := mk ⟨fun y => (γ y.2).1 y.1, by
      have := (continuous_subtype_val.comp (map_continuous (γ : C(I^N, X.pathSpace))))
      exact continuous_eval.comp ((this.comp continuous_snd).prodMk continuous_fst)⟩
    (fun t => (γ t).2.1) fun s t h => by
      rcases h with rfl | ht
      · exact (γ t).2.2
      · exact congrArg (fun c : X.pathSpace => c.1 s) (GenLoop.boundary γ t ht)
  left_inv p := by ext y; exact mk_apply _ _ _ y
  right_inv γ := by ext t s; exact mk_apply _ _ _ (s, t)
  continuous_toFun := by
    refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
    refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
    exact continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  continuous_invFun := by
    refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
    simp only [coe_mk]
    have hγ :
        Continuous fun z : Ω^ N X.pathSpace X.pathSpaceBase × (I × (I^N)) => (z.1 z.2.2).1 :=
      continuous_subtype_val.comp
        (continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    exact continuous_eval.comp (hγ.prodMk (continuous_fst.comp continuous_snd))

@[simp]
theorem pathSpaceHomeo_apply_apply (p : RelGenLoop N X) (t : I^N) (s : I) :
    (pathSpaceHomeo p t).1 s = p (s, t) :=
  (rfl)

@[simp]
theorem pathSpaceHomeo_symm_apply (γ : Ω^ N X.pathSpace X.pathSpaceBase) (y : I × (I^N)) :
    pathSpaceHomeo.symm γ y = (γ y.2).1 y.1 :=
  mk_apply _ _ _ y

@[simp]
theorem pathSpaceHomeo_const :
    pathSpaceHomeo (const : RelGenLoop N X) = GenLoop.const :=
  GenLoop.ext _ _ fun _ => Subtype.ext <| ContinuousMap.ext fun _ => const_apply _

/-- Homotopy through relative cubes is path connectedness in the space of relative cubes. -/
theorem homotopic_iff_joined {p q : RelGenLoop N X} : Homotopic p q ↔ Joined p q :=
  homotopic_iff.trans (ContinuousMap.homotopicWith_iff_joined p.2 q.2)

/-- Currying relative cubes into generalized loops in the path space preserves and reflects
homotopy. -/
@[simp]
theorem homotopic_pathSpaceHomeo_iff {p q : RelGenLoop N X} :
    GenLoop.Homotopic (pathSpaceHomeo p) (pathSpaceHomeo q) ↔ Homotopic p q := by
  rw [GenLoop.homotopic_iff_joined, homotopic_iff_joined]
  refine ⟨fun h => ?_, fun h => h.map pathSpaceHomeo.continuous⟩
  simpa using h.map pathSpaceHomeo.symm.continuous

variable [DecidableEq N]

/-- Concatenation of two relative cubes along a direction `i : N` of the cube `I^N`: the first on
the half `t i ≤ 1 / 2` and the second on the other half, both reparametrised. -/
def transAt (i : N) (p q : RelGenLoop N X) : RelGenLoop N X :=
  pathSpaceHomeo.symm (GenLoop.transAt i (pathSpaceHomeo p) (pathSpaceHomeo q))

theorem transAt_apply (i : N) (p q : RelGenLoop N X) (s : I) (t : I^N) :
    transAt i p q (s, t) = if (t i : ℝ) ≤ 1 / 2
      then p (s, Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i))
      else q (s, Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i - 1)) := by
  rw [transAt, pathSpaceHomeo_symm_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> exact pathSpaceHomeo_apply_apply _ _ _

/-- Reversal of a relative cube along a direction `i : N` of the cube `I^N`, by `t i ↦ 1 - t i`. -/
def symmAt (i : N) (p : RelGenLoop N X) : RelGenLoop N X :=
  pathSpaceHomeo.symm (GenLoop.symmAt i (pathSpaceHomeo p))

theorem symmAt_apply (i : N) (p : RelGenLoop N X) (s : I) (t : I^N) :
    symmAt i p (s, t) = p (s, fun j => if j = i then σ (t i) else t j) := by
  rw [symmAt, pathSpaceHomeo_symm_apply, GenLoop.symmAt, GenLoop.coe_copy]
  exact pathSpaceHomeo_apply_apply _ _ _

@[simp]
theorem pathSpaceHomeo_transAt (i : N) (p q : RelGenLoop N X) :
    pathSpaceHomeo (transAt i p q) =
      GenLoop.transAt i (pathSpaceHomeo p) (pathSpaceHomeo q) :=
  pathSpaceHomeo.apply_symm_apply _

@[simp]
theorem pathSpaceHomeo_symmAt (i : N) (p : RelGenLoop N X) :
    pathSpaceHomeo (symmAt i p) = GenLoop.symmAt i (pathSpaceHomeo p) :=
  pathSpaceHomeo.apply_symm_apply _

/-- Concatenation commutes with the action of morphisms of based pairs. -/
theorem map_transAt (f : X ⟶ Y) (i : N) (p q : RelGenLoop N X) :
    map f (transAt i p q) = transAt i (map f p) (map f q) := by
  ext ⟨s, t⟩
  simp only [map_apply, transAt_apply]
  exact apply_ite _ _ _ _

/-- The face in the subspace of a concatenation is the concatenation of the faces. -/
theorem boundary_transAt (i : N) (p q : RelGenLoop N X) :
    boundary (transAt i p q) = GenLoop.transAt i (boundary p) (boundary q) := by
  ext t
  rw [boundary_apply_eq_iff, transAt_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> exact (map_boundary_apply _ _).symm

/-- Regarding absolute cubes as relative cubes carries a concatenation in the direction `some i`
of `I^(Option N)` to a concatenation in the direction `i`. -/
theorem ofGenLoop_transAt (i : N) (γ δ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    ofGenLoop (GenLoop.transAt (some i) γ δ) = transAt i (ofGenLoop γ) (ofGenLoop δ) := by
  ext ⟨s, t⟩
  rw [ofGenLoop_apply, transAt_apply, ofGenLoop_apply, ofGenLoop_apply, GenLoop.transAt,
    GenLoop.coe_copy]
  have hupd (v : I) :
      Function.update ((piOptionEquivProdHomeomorph fun _ => I).symm (s, t)) (some i) v =
        (piOptionEquivProdHomeomorph fun _ => I).symm (s, Function.update t i v) := by
    funext o
    cases o <;> simp [Function.update_apply]
  simp only [piOptionEquivProdHomeomorph_symm_apply_some, hupd]

end RelGenLoop

namespace RelHomotopyGroup

variable {N : Type v} {X Y : BasedTopPair.{u}}

/-- The relative homotopy set `π_{n+1}(X, A, a₀)` is the homotopy set `π_n(P, c)` of the space `P`
of paths from `A` to `a₀`, based at the constant path `c`. -/
def pathSpaceEquiv : RelHomotopyGroup N X ≃ HomotopyGroup N X.pathSpace X.pathSpaceBase where
  toFun := lift (β := Quotient (GenLoop.Homotopic.setoid N X.pathSpaceBase))
    (fun p => ⟦RelGenLoop.pathSpaceHomeo p⟧) fun _ _ h =>
    Quotient.sound (RelGenLoop.homotopic_pathSpaceHomeo_iff.2 h)
  invFun := Quotient.lift (fun γ => mk (RelGenLoop.pathSpaceHomeo.symm γ)) fun γ δ h =>
    mk_eq_mk.2 (RelGenLoop.homotopic_pathSpaceHomeo_iff.1 (by
      rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
      exact h))
  left_inv a := by
    obtain ⟨p, rfl⟩ := mk_surjective a
    rw [lift_mk]
    exact congrArg mk (RelGenLoop.pathSpaceHomeo.symm_apply_apply p)
  right_inv b := by
    induction b using Quotient.inductionOn with | h γ => ?_
    rw [Quotient.lift_mk, lift_mk]
    exact congrArg (fun γ => (⟦γ⟧ : HomotopyGroup N X.pathSpace X.pathSpaceBase))
      (RelGenLoop.pathSpaceHomeo.apply_symm_apply γ)

@[simp]
theorem pathSpaceEquiv_mk (p : RelGenLoop N X) :
    pathSpaceEquiv (mk p) = ⟦RelGenLoop.pathSpaceHomeo p⟧ :=
  lift_mk _ _ p

@[simp]
theorem pathSpaceEquiv_symm_mk (γ : Ω^ N X.pathSpace X.pathSpaceBase) :
    pathSpaceEquiv.symm ⟦γ⟧ = mk (RelGenLoop.pathSpaceHomeo.symm γ) :=
  (rfl)

variable [DecidableEq N]

/-- The group structure on `π_{n+1}(X, A, a₀)` for `n ≥ 1`, transported from `π_n(P, c)`. Its
product is concatenation of relative cubes in any direction of `I^N`, by `mul_spec`. -/
instance group [Nonempty N] : Group (RelHomotopyGroup N X) :=
  pathSpaceEquiv.group

/-- The group isomorphism `π_{n+1}(X, A, a₀) ≃* π_n(P, c)`, for `n ≥ 1`. -/
def pathSpaceMulEquiv [Nonempty N] :
    RelHomotopyGroup N X ≃* HomotopyGroup N X.pathSpace X.pathSpaceBase :=
  pathSpaceEquiv.mulEquiv

@[simp]
theorem pathSpaceMulEquiv_apply [Nonempty N] (a : RelHomotopyGroup N X) :
    pathSpaceMulEquiv a = pathSpaceEquiv a :=
  (rfl)

@[simp]
theorem pathSpaceMulEquiv_symm_apply [Nonempty N]
    (b : HomotopyGroup N X.pathSpace X.pathSpaceBase) :
    pathSpaceMulEquiv.symm b = pathSpaceEquiv.symm b :=
  (rfl)

/-- `π_{n+1}(X, A, a₀)` is commutative for `n ≥ 2`. -/
instance commGroup [Nontrivial N] : CommGroup (RelHomotopyGroup N X) where
  mul_comm a b := pathSpaceMulEquiv.injective <| by rw [map_mul, map_mul, mul_comm]

/-- The identity of `π_{n+1}(X, A, a₀)` is the class of the constant cube. -/
theorem one_def [Nonempty N] : (1 : RelHomotopyGroup N X) = mk RelGenLoop.const := by
  apply pathSpaceMulEquiv.injective
  rw [map_one, pathSpaceMulEquiv_apply, pathSpaceEquiv_mk, RelGenLoop.pathSpaceHomeo_const]
  exact HomotopyGroup.one_def

/-- The identity of `π_{n+1}(X, A, a₀)` is its distinguished point. -/
theorem one_eq_default [Nonempty N] : (1 : RelHomotopyGroup N X) = default :=
  one_def

/-- The product of two relative homotopy classes is represented by the concatenation of
representatives along any direction `i` of `I^N`, in the order of `HomotopyGroup.mul_spec`. -/
theorem mul_spec [Nonempty N] {i : N} {p q : RelGenLoop N X} :
    mk p * mk q = mk (RelGenLoop.transAt i q p) := by
  apply pathSpaceMulEquiv.injective
  simp only [map_mul, pathSpaceMulEquiv_apply, pathSpaceEquiv_mk,
    RelGenLoop.pathSpaceHomeo_transAt]
  exact HomotopyGroup.mul_spec

/-- The inverse of a relative homotopy class is represented by the reversal of a representative
along any direction `i` of `I^N`. -/
theorem inv_spec [Nonempty N] {i : N} {p : RelGenLoop N X} :
    (mk p)⁻¹ = mk (RelGenLoop.symmAt i p) := by
  apply pathSpaceMulEquiv.injective
  simp only [map_inv, pathSpaceMulEquiv_apply, pathSpaceEquiv_mk,
    RelGenLoop.pathSpaceHomeo_symmAt]
  exact HomotopyGroup.inv_spec

/-! ### Homomorphisms -/

/-- The homomorphism `π_{n+1}(X, A, a₀) →* π_{n+1}(Y, B, b₀)` induced by a morphism of based
pairs. -/
def mapHom [Nonempty N] (f : X ⟶ Y) : RelHomotopyGroup N X →* RelHomotopyGroup N Y where
  toFun := map f
  map_one' := by rw [one_eq_default, map_default, one_eq_default]
  map_mul' a b := by
    obtain ⟨p, rfl⟩ := mk_surjective a
    obtain ⟨q, rfl⟩ := mk_surjective b
    rw [mul_spec (i := Classical.arbitrary N), map_mk, map_mk, map_mk, RelGenLoop.map_transAt,
      mul_spec (i := Classical.arbitrary N)]

@[simp]
theorem mapHom_apply [Nonempty N] (f : X ⟶ Y) (a : RelHomotopyGroup N X) :
    mapHom f a = map f a :=
  (rfl)

@[simp]
theorem mapHom_id [Nonempty N] : mapHom (𝟙 X) = MonoidHom.id (RelHomotopyGroup N X) :=
  MonoidHom.ext fun a => by rw [mapHom_apply, map_id, id_eq, MonoidHom.id_apply]

@[simp]
theorem mapHom_comp [Nonempty N] {Z : BasedTopPair.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (mapHom g).comp (mapHom f) = mapHom (N := N) (f ≫ g) :=
  MonoidHom.ext fun a => by
    rw [MonoidHom.comp_apply, mapHom_apply, mapHom_apply, mapHom_apply, map_map]

@[simp]
theorem map_mul [Nonempty N] (f : X ⟶ Y) (a b : RelHomotopyGroup N X) :
    map f (a * b) = map f a * map f b :=
  (mapHom f).map_mul a b

@[simp]
theorem map_one [Nonempty N] (f : X ⟶ Y) : map f (1 : RelHomotopyGroup N X) = 1 :=
  (mapHom f).map_one

/-- The boundary map `π_{n+1}(X, A, a₀) →* π_n(A, a₀)` as a homomorphism. -/
def boundaryHom [Nonempty N] : RelHomotopyGroup N X →* HomotopyGroup N X.pair.snd X.basepoint where
  toFun := boundary
  map_one' := by rw [one_def, boundary_mk, RelGenLoop.boundary_const, HomotopyGroup.one_def]
  map_mul' a b := by
    obtain ⟨p, rfl⟩ := mk_surjective a
    obtain ⟨q, rfl⟩ := mk_surjective b
    rw [mul_spec (i := Classical.arbitrary N), boundary_mk, boundary_mk, boundary_mk,
      RelGenLoop.boundary_transAt]
    exact HomotopyGroup.mul_spec.symm

@[simp]
theorem boundaryHom_apply [Nonempty N] (a : RelHomotopyGroup N X) :
    boundaryHom a = boundary a :=
  (rfl)

@[simp]
theorem boundary_mul [Nonempty N] (a b : RelHomotopyGroup N X) :
    boundary (a * b) = boundary a * boundary b :=
  boundaryHom.map_mul a b

@[simp]
theorem boundary_one [Nonempty N] :
    boundary (1 : RelHomotopyGroup N X) = 1 :=
  boundaryHom.map_one

/-- The boundary homomorphism `π_{n+1}(X, A, a₀) →* π_n(A, a₀)` is natural in the based pair. -/
theorem boundaryHom_comp_mapHom [Nonempty N] (f : X ⟶ Y) :
    boundaryHom.comp (mapHom (N := N) f) =
      (HomotopyGroup.mapHom (TopPair.Hom.snd f.toTopPairHom).hom f.map_basepoint).comp
        boundaryHom :=
  MonoidHom.ext fun a => by simp [boundary_map]

/-- The map `π_{n+1}(X, a₀) →* π_{n+1}(X, A, a₀)` as a homomorphism, where `π_{n+1}(X, a₀)` is
modelled on the cube `I^(Option N)`. -/
def ofHomotopyGroupHom [Nonempty N] :
    HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint) →* RelHomotopyGroup N X where
  toFun := ofHomotopyGroup
  map_one' := by rw [ofHomotopyGroup_one, one_eq_default]
  map_mul' a b := by
    induction a, b using Quotient.inductionOn₂ with | h γ δ => ?_
    simp only [HomotopyGroup.mul_spec (i := some (Classical.arbitrary N)), ofHomotopyGroup_mk,
      RelGenLoop.ofGenLoop_transAt, mul_spec (i := Classical.arbitrary N)]

@[simp]
theorem ofHomotopyGroupHom_apply [Nonempty N]
    (a : HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    ofHomotopyGroupHom a = ofHomotopyGroup a :=
  (rfl)

@[simp]
theorem ofHomotopyGroup_mul [Nonempty N]
    (a b : HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    (ofHomotopyGroup (a * b) : RelHomotopyGroup N X) = ofHomotopyGroup a * ofHomotopyGroup b :=
  ofHomotopyGroupHom.map_mul a b

end RelHomotopyGroup

end TauCeti
