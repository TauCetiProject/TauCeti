/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Group
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# The relative Hurewicz map

For a based pair `X = (X, A, a₀)` and a coefficient object `R` of an abelian category with
coproducts, this file constructs the relative Hurewicz map

`TauCeti.RelHomotopyGroup.hurewicz R n : π_{n+1}(X, A, a₀) → (R ⟶ Hₙ₊₁(X, A; R))`

on the relative homotopy sets `TauCeti.RelHomotopyGroup (Fin n) X`, in every degree `n + 1 ≥ 1`.
A relative cube `p : I × Iⁿ → X` sends the face `{0} × Iⁿ` into `A` and the rest of the boundary
to `a₀ ∈ A`. Read on `Iⁿ⁺¹` through `z ↦ (z 0, Fin.tail z)`, so that the first coordinate is the
distinguished direction, it is therefore a map of pairs `(Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, A)`
(`TauCeti.RelGenLoop.toCubeBoundaryPairHom`). The relative Hurewicz class of `p` is the image under
this map of the generator of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R) ≅ R`
(`TauCeti.singularHomologyCubeBoundaryPairIso`), the generator that also defines the absolute
Hurewicz map `HomotopyGroup.hurewicz`. With `C = ModuleCat ℤ` and `R = ℤ`, evaluating at `1` gives
the classical map `π_{n+1}(X, A, a₀) → Hₙ₊₁(X, A; ℤ)`, `[p] ↦ p_*[Iⁿ⁺¹]`.

A homotopy through relative cubes is a homotopy of maps of pairs, so the class only depends on the
relative homotopy class. The map is natural in morphisms of based pairs and sends the distinguished
class to zero. It extends the absolute Hurewicz map: regarding an absolute class of
`π_{n+1}(X, a₀)` as a relative class and then applying the relative Hurewicz map agrees with
applying the absolute Hurewicz map and then the quotient map `Hₙ₊₁(X; R) ⟶ Hₙ₊₁(X, A; R)`
(`TauCeti.RelHomotopyGroup.hurewicz_ofHomotopyGroup`). The absolute Hurewicz map is defined on
classes modelled on `I^(Fin (n + 1))`, while `TauCeti.RelHomotopyGroup.ofHomotopyGroup` takes
classes modelled on `I^(Option (Fin n))`; the two are matched by `finSuccEquiv n`, which sends the
first coordinate to the distinguished coordinate `none`.

In degrees `n + 2 ≥ 2`, where `π_{n+2}(X, A, a₀)` is a group, the relative Hurewicz map is a
homomorphism (`TauCeti.RelHomotopyGroup.hurewicz_mul`). The product `[q] * [p]` is represented by
a concatenation of `p` and `q` along a direction of `Iⁿ⁺¹` other than the distinguished one, with
a slab between them sent to `a₀`, and the pinch identity
`TauCeti.singularHomologyMap_cubeBoundaryPair_eq_add`, which also gives additivity of the absolute
Hurewicz map, splits its relative Hurewicz class into those of `p` and `q`.

## Main declarations

* `TauCeti.RelGenLoop.toCubeBoundaryPairHom`: a relative cube as a map of pairs
  `(Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, A)`.
* `TauCeti.RelGenLoop.hurewicz`: the relative Hurewicz class of a relative cube.
* `TauCeti.RelHomotopyGroup.hurewicz`: the relative Hurewicz map on relative homotopy classes,
  natural by `TauCeti.RelHomotopyGroup.hurewicz_map`.
* `TauCeti.RelHomotopyGroup.hurewicz_ofHomotopyGroup`: compatibility with the absolute Hurewicz
  map.
* `TauCeti.RelHomotopyGroup.hurewicz_mul`, `TauCeti.RelHomotopyGroup.hurewiczHom`: the relative
  Hurewicz map is a homomorphism from `π_{n+2}(X, A, a₀)`, written additively, to the group of
  morphisms `R ⟶ Hₙ₊₂(X, A; R)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, the Hurewicz maps `πₙ(X, x₀) → Hₙ(X)` and `πₙ(X, A, x₀) → Hₙ(X, A)`, defined by
  pushing forward a generator of `Hₙ(Dⁿ, ∂Dⁿ)`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped unitInterval Topology Topology.Homotopy

universe w v u

namespace TauCeti

namespace RelGenLoop

variable {n : ℕ} {X Y : BasedTopPair.{w}}

/-- Split a point of `Iⁿ⁺¹` into its first coordinate and the remaining ones. -/
private def cubeSplit (n : ℕ) : C(ULift.{w} (I^(Fin (n + 1))), I × (I^(Fin n))) :=
  ⟨fun z ↦ (z.down 0, Fin.tail z.down), by fun_prop⟩

/-- A relative cube sends the boundary of the cube into the subspace. -/
theorem apply_mem_range_of_mem_boundary (p : RelGenLoop (Fin n) X) {z : I^(Fin (n + 1))}
    (hz : z ∈ Cube.boundary (Fin (n + 1))) : p (z 0, Fin.tail z) ∈ Set.range X.pair.map := by
  rcases Cube.boundary_fin_succ_iff.1 hz with (h | h) | h
  · rw [h]
    exact apply_zero_mem_range p _
  · rw [h, apply_one]
    exact Set.mem_range_self _
  · rw [apply_of_mem_boundary p _ h]
    exact Set.mem_range_self _

/-- The ambient map of `toCubeBoundaryPairHom`. -/
private def cubeMap (p : RelGenLoop (Fin n) X) : C(ULift.{w} (I^(Fin (n + 1))), X.pair.fst) :=
  (p : C(I × (I^(Fin n)), X.pair.fst)).comp (cubeSplit n)

/-- A relative cube `p : I × Iⁿ → X`, read on `Iⁿ⁺¹` with the first coordinate as the distinguished
direction, as a map of pairs `(Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, A)`. -/
def toCubeBoundaryPairHom (p : RelGenLoop (Fin n) X) : cubeBoundaryPair.{w} (n + 1) ⟶ X.pair :=
  TopPair.ofHom (TopCat.ofHom (cubeMap p))
    (TopCat.ofHom (X.pair.liftSnd ((cubeMap p).comp ⟨Subtype.val, continuous_subtype_val⟩)
      fun z ↦ apply_mem_range_of_mem_boundary p z.2))
    (by ext z; exact TopPair.map_liftSnd _ _ z)

@[simp]
lemma toCubeBoundaryPairHom_fst_apply (p : RelGenLoop (Fin n) X)
    (z : (cubeBoundaryPair.{w} (n + 1)).fst) :
    TopPair.Hom.fst (toCubeBoundaryPairHom p) z = p (z.down 0, Fin.tail z.down) :=
  (rfl)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- **Homotopic relative cubes induce the same map on relative homology**: a homotopy through
relative cubes is a homotopy of the maps of pairs `(Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, A)`. -/
theorem singularHomologyMap_toCubeBoundaryPairHom_eq {p q : RelGenLoop (Fin n) X}
    (h : Homotopic p q) (k : ℕ) :
    TopPair.singularHomologyMap (toCubeBoundaryPairHom p) R k =
      TopPair.singularHomologyMap (toCubeBoundaryPairHom q) R k := by
  obtain ⟨F⟩ := homotopic_iff.1 h
  let G : C(I × (cubeBoundaryPair.{w} (n + 1)).snd, X.pair.fst) :=
    ⟨fun x ↦ F (x.1, cubeSplit n x.2.1), by fun_prop⟩
  have hG (x : I × (cubeBoundaryPair.{w} (n + 1)).snd) : G x ∈ Set.range X.pair.map :=
    apply_mem_range_of_mem_boundary ⟨_, F.prop x.1⟩ x.2.2
  exact TopPair.Homotopy.congr_singularHomologyMap
    { fst := F.toHomotopy.compContinuousMap (cubeSplit n)
      snd :=
        { toContinuousMap := X.pair.liftSnd G hG
          map_zero_left z := X.pair.isEmbedding_map.injective <| by
            rw [ContinuousMap.toFun_eq_coe, TopPair.map_liftSnd, TopPair.Hom.w_apply]
            exact F.apply_zero _
          map_one_left z := X.pair.isEmbedding_map.injective <| by
            rw [ContinuousMap.toFun_eq_coe, TopPair.map_liftSnd, TopPair.Hom.w_apply]
            exact F.apply_one _ }
      w := by
        ext x
        exact (TopPair.map_liftSnd G hG (TopCat.I.homeomorph x.2, x.1)).symm } R k

/-- Postcomposing a relative cube with a morphism of based pairs postcomposes its map of pairs. -/
lemma toCubeBoundaryPairHom_map (f : X ⟶ Y) (p : RelGenLoop (Fin n) X) :
    toCubeBoundaryPairHom (map f p) = toCubeBoundaryPairHom p ≫ f.toTopPairHom :=
  TopPair.hom_ext_of_fst _ (by ext z; simp [TopPair.Hom.fst_comp, map_apply])

/-- **The relative Hurewicz class of a relative cube** `p : I × Iⁿ → X`: the image of the generator
`TauCeti.singularHomologyCubeBoundaryPairIso` of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R)` under the map of pairs
`p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, A)`. -/
def hurewicz (p : RelGenLoop (Fin n) X) : R ⟶ X.pair.singularHomology R (n + 1) :=
  (singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
    TopPair.singularHomologyMap (toCubeBoundaryPairHom p) R (n + 1)

lemma hurewicz_def (p : RelGenLoop (Fin n) X) :
    hurewicz R p = (singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
      TopPair.singularHomologyMap (toCubeBoundaryPairHom p) R (n + 1) :=
  (rfl)

/-- Homotopic relative cubes have the same relative Hurewicz class. -/
theorem hurewicz_eq_of_homotopic {p q : RelGenLoop (Fin n) X} (h : Homotopic p q) :
    hurewicz R p = hurewicz R q := by
  rw [hurewicz_def, hurewicz_def, singularHomologyMap_toCubeBoundaryPairHom_eq R h]

/-- **Naturality of the relative Hurewicz class**: for a morphism of based pairs `f`, the relative
Hurewicz class of `f ∘ p` is the image of that of `p` under
`f_* : Hₙ₊₁(X, A; R) ⟶ Hₙ₊₁(Y, B; R)`. -/
theorem hurewicz_map (f : X ⟶ Y) (p : RelGenLoop (Fin n) X) :
    hurewicz R (map f p) =
      hurewicz R p ≫ TopPair.singularHomologyMap f.toTopPairHom R (n + 1) := by
  rw [hurewicz_def, hurewicz_def, toCubeBoundaryPairHom_map, TopPair.singularHomologyMap_comp,
    Category.assoc]

/-- The relative Hurewicz class of a relative cube with values in the subspace is zero. -/
theorem hurewicz_eq_zero_of_mem_range (p : RelGenLoop (Fin n) X)
    (hp : ∀ y, p y ∈ Set.range X.pair.map) : hurewicz R p = 0 := by
  rw [hurewicz_def, TopPair.singularHomologyMap_eq_zero_of_fac _ R
    (TopCat.ofHom (X.pair.liftSnd (cubeMap p) fun z ↦ hp _))
    (by ext z; exact TopPair.map_liftSnd _ _ z), comp_zero]

/-! ### Additivity -/

/-- The concatenation of `p`, the constant cube and `q` along the direction `i` of `Iⁿ`: `p` is run
on `tᵢ ≤ 1/4`, the slab `1/4 ≤ tᵢ ≤ 1/2` goes to the base point, and `q` is run on `tᵢ ≥ 1/2`. It
represents the product `[q] * [p]`. -/
private def fatTrans (i : Fin n) (p q : RelGenLoop (Fin n) X) : RelGenLoop (Fin n) X :=
  transAt i (transAt i p const) q

/-- The fat concatenation sends the slab `1/4 ≤ tᵢ ≤ 1/2` to the base point. -/
private lemma fatTrans_apply_of_le_of_le (i : Fin n) (p q : RelGenLoop (Fin n) X) (s : I)
    {t : I^(Fin n)} (h₁ : (1 / 4 : ℝ) ≤ t i) (h₂ : (t i : ℝ) ≤ 1 / 2) :
    fatTrans i p q (s, t) = X.pair.map X.basepoint := by
  have h₂' : (Set.projIcc 0 1 zero_le_one (2 * (t i : ℝ)) : ℝ) = 2 * t i :=
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨by linarith, by linarith⟩)
  rw [fatTrans, transAt_apply, ite_eq_left h₂, transAt_apply, Function.update_self, h₂']
  split_ifs with h
  · -- On the face `tᵢ = 1/4`, the cube `p` is evaluated on the face `tᵢ = 1` of `Iⁿ`.
    refine apply_of_mem_boundary p s ⟨i, Or.inr ?_⟩
    rw [Function.update_self, show 2 * (2 * (t i : ℝ)) = 1 by linarith]
    exact Set.projIcc_right (h := zero_le_one' ℝ)
  · exact const_apply _

/-- On the first quarter, reparametrised by `tᵢ ↦ tᵢ / 4`, the fat concatenation is `p`. -/
private lemma fatTrans_apply_quarter (i : Fin n) (p q : RelGenLoop (Fin n) X) (s : I)
    (t : I^(Fin n)) :
    fatTrans i p q (s, Function.update t i (Set.projIcc 0 1 zero_le_one (t i / 4))) =
      p (s, t) := by
  have ht := (t i).2
  -- The arithmetic: both reparametrisations stay in `[0, 1/2]` and compose to the identity.
  have h₁ : (t i / 4 : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h₂ : (2 * (t i / 4) : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h₃ : (2 * (2 * (t i / 4)) : ℝ) = t i := by ring
  have hc₁ : (t i / 4 : ℝ) ≤ 1 / 2 := by linarith [ht.2]
  have hc₂ : (2 * (t i / 4) : ℝ) ≤ 1 / 2 := by linarith [ht.2]
  -- Both concatenations take their first branch, and the coordinate updates collapse.
  simp only [fatTrans, transAt_apply, Function.update_self, Function.update_idem,
    Set.projIcc_of_mem _ h₁, Set.projIcc_of_mem _ h₂, h₃, Set.projIcc_val,
    Function.update_eq_self, hc₁, hc₂, ↓reduceIte]

/-- On the upper half, reparametrised by `tᵢ ↦ (tᵢ + 1) / 2`, the fat concatenation is `q`. -/
private lemma fatTrans_apply_upperHalf (i : Fin n) (p q : RelGenLoop (Fin n) X) (s : I)
    (t : I^(Fin n)) :
    fatTrans i p q (s, Function.update t i (Set.projIcc 0 1 zero_le_one ((t i + 1) / 2))) =
      q (s, t) := by
  have ht := (t i).2
  -- The arithmetic: `tᵢ ↦ (tᵢ + 1) / 2` stays in `[0, 1]` and `tᵢ ↦ 2 tᵢ - 1` inverts it.
  have h₁ : ((t i + 1) / 2 : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h₂ : (2 * ((t i + 1) / 2) : ℝ) = t i + 1 := by ring
  simp only [fatTrans, transAt_apply, Function.update_self, Function.update_idem,
    Set.projIcc_of_mem _ h₁, h₂, add_sub_cancel_right, Set.projIcc_val, Function.update_eq_self]
  rcases ht.1.eq_or_lt with h₀ | h₀
  · -- On the face `tᵢ = 0`, both sides are the base point.
    have hz : t i = 0 := Subtype.ext h₀.symm
    have hc : ¬(1 : ℝ) ≤ 1 / 2 := by norm_num
    simp only [hz, Set.Icc.coe_zero, zero_add, Set.projIcc_right, le_refl, hc,
      ↓reduceIte, apply_of_mem_boundary q s ⟨i, Or.inl hz⟩]
    exact const_apply _
  · -- Otherwise the outer concatenation takes its second branch.
    have hc : ¬((t i + 1) / 2 : ℝ) ≤ 1 / 2 := by linarith
    simp only [hc, ↓reduceIte]

/-- The relative Hurewicz class of the fat concatenation of `p` and `q` is the sum of their
relative Hurewicz classes, by the pinch identity
`TauCeti.singularHomologyMap_cubeBoundaryPair_eq_add` along the direction of `Iⁿ⁺¹` that
corresponds to `i`. -/
private lemma hurewicz_fatTrans (i : Fin n) (p q : RelGenLoop (Fin n) X) :
    hurewicz R (fatTrans i p q) = hurewicz R p + hurewicz R q := by
  have hupd (z : I^(Fin (n + 1))) (v : I) :
      (Function.update z i.succ v 0, Fin.tail (Function.update z i.succ v)) =
        (z 0, Function.update (Fin.tail z) i v) := by
    rw [Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.tail_update_succ]
  have h := singularHomologyMap_cubeBoundaryPair_eq_add R i.succ
    (f := toCubeBoundaryPairHom (fatTrans i p q)) (g := toCubeBoundaryPairHom p)
    (h := toCubeBoundaryPairHom q)
    (fun z h₁ h₂ ↦ by
      rw [toCubeBoundaryPairHom_fst_apply, fatTrans_apply_of_le_of_le i p q _ h₁ h₂]
      exact Set.mem_range_self _)
    (fun z ↦ by
      have e := toCubeBoundaryPairHom_fst_apply (fatTrans i p q) (⟨Function.update z.down i.succ
        (Set.projIcc 0 1 zero_le_one (z.down i.succ / 4))⟩ : (cubeBoundaryPair.{w} (n + 1)).fst)
      dsimp only at e
      rw [toCubeBoundaryPairHom_fst_apply, e, hupd]
      exact (fatTrans_apply_quarter i p q _ _).symm)
    (fun z ↦ by
      have e := toCubeBoundaryPairHom_fst_apply (fatTrans i p q) (⟨Function.update z.down i.succ
        (Set.projIcc 0 1 zero_le_one ((z.down i.succ + 1) / 2))⟩ :
          (cubeBoundaryPair.{w} (n + 1)).fst)
      dsimp only at e
      rw [toCubeBoundaryPairHom_fst_apply, e, hupd]
      exact (fatTrans_apply_upperHalf i p q _ _).symm)
    (n + 1)
  rw [hurewicz_def, hurewicz_def, hurewicz_def, h, Preadditive.comp_add]

end RelGenLoop

namespace RelHomotopyGroup

variable {X Y : BasedTopPair.{w}}
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)

/-- **The relative Hurewicz map** `π_{n+1}(X, A, a₀) → (R ⟶ Hₙ₊₁(X, A; R))`, sending the class of a
relative cube `p` to its relative Hurewicz class `TauCeti.RelGenLoop.hurewicz R p`: the image of
the generator of `Hₙ₊₁(Iⁿ⁺¹, ∂Iⁿ⁺¹; R) ≅ R` under `p : (Iⁿ⁺¹, ∂Iⁿ⁺¹) ⟶ (X, A)`. -/
def hurewicz : RelHomotopyGroup (Fin n) X → (R ⟶ X.pair.singularHomology R (n + 1)) :=
  lift (RelGenLoop.hurewicz R) fun _ _ h ↦ RelGenLoop.hurewicz_eq_of_homotopic R h

@[simp]
lemma hurewicz_mk (p : RelGenLoop (Fin n) X) : hurewicz R n (mk p) = RelGenLoop.hurewicz R p :=
  lift_mk _ _ p

/-- **Naturality of the relative Hurewicz map** in morphisms of based pairs. -/
theorem hurewicz_map (f : X ⟶ Y) (a : RelHomotopyGroup (Fin n) X) :
    hurewicz R n (map f a) =
      hurewicz R n a ≫ TopPair.singularHomologyMap f.toTopPairHom R (n + 1) := by
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [map_mk, hurewicz_mk, hurewicz_mk, RelGenLoop.hurewicz_map]

/-- The relative Hurewicz map sends the distinguished class to zero. -/
@[simp]
theorem hurewicz_default : hurewicz R n (default : RelHomotopyGroup (Fin n) X) = 0 := by
  rw [default_eq, hurewicz_mk]
  refine RelGenLoop.hurewicz_eq_zero_of_mem_range R _ fun y ↦ ?_
  rw [RelGenLoop.const_apply]
  exact Set.mem_range_self _

/-- The relative Hurewicz map sends the identity class to zero. -/
@[simp]
theorem hurewicz_one : hurewicz R (n + 1) (1 : RelHomotopyGroup (Fin (n + 1)) X) = 0 := by
  rw [one_eq_default, hurewicz_default]

/-- **The relative Hurewicz map is additive** in degrees at least two: it sends a product of
relative homotopy classes to the sum of their relative Hurewicz classes. -/
@[simp]
theorem hurewicz_mul (a b : RelHomotopyGroup (Fin (n + 1)) X) :
    hurewicz R (n + 1) (a * b) = hurewicz R (n + 1) a + hurewicz R (n + 1) b := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  obtain ⟨p, rfl⟩ := mk_surjective b
  -- `[q] * [p]` is the class of the fat concatenation, which runs `p` and then `q`.
  have hp : mk (RelGenLoop.transAt 0 p RelGenLoop.const) = mk p := by
    rw [← mul_spec, ← one_def, one_mul]
  rw [hurewicz_mk, hurewicz_mk, add_comm (RelGenLoop.hurewicz R q),
    ← RelGenLoop.hurewicz_fatTrans R 0, ← hurewicz_mk, RelGenLoop.fatTrans, ← mul_spec, hp]

/-- The relative Hurewicz map sends the inverse of a class to the negative of its relative
Hurewicz class. -/
@[simp]
theorem hurewicz_inv (a : RelHomotopyGroup (Fin (n + 1)) X) :
    hurewicz R (n + 1) a⁻¹ = -hurewicz R (n + 1) a :=
  eq_neg_of_add_eq_zero_left (by rw [← hurewicz_mul, inv_mul_cancel, hurewicz_one])

/-- **The relative Hurewicz homomorphism** `π_{n+2}(X, A, a₀) → (R ⟶ Hₙ₊₂(X, A; R))`, from the
relative homotopy group, written additively, to the group of morphisms from `R` to relative
singular homology. -/
def hurewiczHom :
    Additive (RelHomotopyGroup (Fin (n + 1)) X) →+ (R ⟶ X.pair.singularHomology R (n + 2)) where
  toFun a := hurewicz R (n + 1) a.toMul
  map_zero' := hurewicz_one R n
  map_add' a b := hurewicz_mul R n a.toMul b.toMul

@[simp]
lemma hurewiczHom_apply (a : Additive (RelHomotopyGroup (Fin (n + 1)) X)) :
    hurewiczHom R n a = hurewicz R (n + 1) a.toMul :=
  (rfl)

/-- The inclusion of pairs `(X, {a₀}) ⟶ (X, A)` of a based pair. -/
private def basepointPairHom (X : BasedTopPair.{w}) :
    TopPair.ofSubset ({X.pair.map X.basepoint} : Set (TopCat.of X.pair.fst)) ⟶ X.pair :=
  TopPair.ofHom (𝟙 _) (TopCat.ofHom (ContinuousMap.const _ X.basepoint))
    (by ext z; exact z.2.symm)

/-- The quotient map `Hₖ(X) ⟶ Hₖ(X, A)` factors through `Hₖ(X, {a₀})`. -/
private lemma singularHomologyπ_comp_basepointPairHom (X : BasedTopPair.{w}) (k : ℕ) :
    (TopPair.ofSubset ({X.pair.map X.basepoint} : Set (TopCat.of X.pair.fst))).singularHomologyπ
        R k ≫ TopPair.singularHomologyMap (basepointPairHom X) R k =
      X.pair.singularHomologyπ R k := by
  have h := SSetPair.homologyπ_naturality (TopPair.toSSetPair.map (basepointPairHom X)) R k
  -- The ambient component of `basepointPairHom X` is the identity of `X`.
  have h₁ : SSet.homologyMap (TopPair.toSSetPair.map (basepointPairHom X)).right R k = 𝟙 _ :=
    (congrArg (SSet.homologyMap · R k) ((TopPair.toSSetPair_map_right _).trans
      (TopCat.toSSet.map_id X.pair.fst))).trans (SSet.homologyMap_id _ R k)
  rw [h₁] at h
  exact h.symm.trans (Category.id_comp _)

/-- Read on `Iⁿ⁺¹`, an absolute cube regarded as a relative cube is the absolute cube followed by
the inclusion `(X, {a₀}) ⟶ (X, A)`. -/
private lemma toCubeBoundaryPairHom_ofGenLoop
    (γ : Ω^ (Option (Fin n)) X.pair.fst (X.pair.map X.basepoint)) :
    RelGenLoop.toCubeBoundaryPairHom (RelGenLoop.ofGenLoop γ) =
      GenLoop.toCubeBoundaryPairHom (GenLoop.congr _ (finSuccEquiv n).symm γ) ≫
        basepointPairHom X := by
  refine TopPair.hom_ext_of_fst _ ?_
  ext z
  rw [RelGenLoop.toCubeBoundaryPairHom_fst_apply, RelGenLoop.ofGenLoop_apply,
    TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, GenLoop.toCubeBoundaryPairHom_fst_apply]
  -- The ambient component of `basepointPairHom X` is the identity, so the right side is `γ` at
  -- the point `o ↦ z ((finSuccEquiv n).symm o)` of `I^(Option (Fin n))`, by `GenLoop.congr_apply`.
  refine congrArg γ (funext fun o ↦ ?_)
  cases o <;> simp [Fin.tail]

/-- **The relative Hurewicz map extends the absolute one**: the relative Hurewicz class of an
absolute class `a ∈ π_{n+1}(X, a₀)`, regarded as a relative class, is the image of the Hurewicz
class of `a` under `Hₙ₊₁(X; R) ⟶ Hₙ₊₁(X, A; R)`.  The absolute class is modelled on `Iⁿ⁺¹` and
the relative class on `I × Iⁿ`, matched by `finSuccEquiv n : Fin (n + 1) ≃ Option (Fin n)`. -/
theorem hurewicz_ofHomotopyGroup
    (a : HomotopyGroup (Option (Fin n)) X.pair.fst (X.pair.map X.basepoint)) :
    hurewicz R n (ofHomotopyGroup a) =
      HomotopyGroup.hurewicz R n ((HomotopyGroup.congrEquiv (finSuccEquiv n)).symm a) ≫
        X.pair.singularHomologyπ R (n + 1) := by
  induction a using Quotient.inductionOn with | h γ => ?_
  rw [HomotopyGroup.congrEquiv_symm_mk, ofHomotopyGroup_mk, hurewicz_mk, HomotopyGroup.hurewicz_mk]
  set γ' := GenLoop.congr _ (finSuccEquiv n).symm γ
  calc RelGenLoop.hurewicz R (RelGenLoop.ofGenLoop γ)
      = ((singularHomologyCubeBoundaryPairIso R (n + 1)).inv ≫
          TopPair.singularHomologyMap (GenLoop.toCubeBoundaryPairHom γ') R (n + 1)) ≫
          TopPair.singularHomologyMap (basepointPairHom X) R (n + 1) := by
        -- The relative cube factors through `basepointPairHom X`.
        rw [RelGenLoop.hurewicz_def, toCubeBoundaryPairHom_ofGenLoop,
          TopPair.singularHomologyMap_comp, Category.assoc]
    _ = (GenLoop.hurewicz R γ' ≫ (singularHomologyIsoOfSubsetSingleton R n _).hom) ≫
          TopPair.singularHomologyMap (basepointPairHom X) R (n + 1) := by
        rw [GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom]
    _ = GenLoop.hurewicz R γ' ≫ X.pair.singularHomologyπ R (n + 1) := by
        -- The quotient map to `(X, A)` factors through `(X, {a₀})`.
        rw [← singularHomologyπ_comp_basepointPairHom, ← singularHomologyIsoOfSubsetSingleton_hom]
        exact Category.assoc _ _ _

end RelHomotopyGroup

end TauCeti
