/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.LowDimTopology.Heegaard.CurveHomology
import TauCeti.Data.ZMod.Units
import TauCeti.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The genus-one Heegaard diagrams of lens spaces

Fix `p ≥ 1` and a unit `q` of `ZMod p`. On the torus `ℝ² / ℤ²` let `α` be the circle `y = 0`,
oriented by increasing `x`, and let `β` be the closed curve `t ↦ (q t, p t)` of homology class
`(q, p)`, oriented by increasing `t`. Attaching disks along `α` and `β` gives the lens space
`L(p, q)`: the meridian `β` of the second solid torus is glued to `p λ + q μ`, where `μ = α`.
The two curves meet transversally in the `p` points `x_j = (j / p, 0)`, `j ∈ ZMod p`. Going along
`α` the point after `x_j` is `x_{j+1}`; going along `β` it is `x_{j+q}`. Cutting the torus along
`α` leaves an annulus that the `p` arcs of `β` cut into `p` parallelograms; the region `R_j` is
the one whose bottom edge is the `α`-arc from `x_j` to `x_{j+1}`, its top edge is the `α`-arc from
`x_{j-q}` to `x_{j-q+1}`, and its two sides are the `β`-arcs starting at `x_j` and `x_{j+1}`.

`TauCeti.HeegaardRegionSystem.lensSpace p q r` records this incidence data, with points and
regions both indexed by `ZMod p` and the basepoint in the region `R_r`. Each point is a generator
(`TauCeti.HeegaardRegionSystem.lensSpaceGenerator`), and every generator is of this form.

The group `CurveHomology` in which the classes `ε(x, y)` live is identified with
`H₁(L(p, q)) = ℤ/p` (`TauCeti.HeegaardRegionSystem.lensSpaceCurveHomologyEquiv`): a cycle of
`α ∪ β` whose `β`-part has total coefficient `s` winds `s` times around the `y`-direction, and the
equivalence sends its class to `-q s`. Under this identification `ε(x_a, x_b) = b - a`. So the
`p` generators lie in the `p` distinct classes, and no domain joins two distinct generators. Since
`s_z(x) - s_z(y)` is Poincaré dual to `ε(x, y)`, this puts one generator in each of the `p` spin^c
structures of `L(p, q)`. The diagram has no nonzero periodic domain, so it is weakly admissible.
These are the combinatorial inputs to the computation `HF̂(L(p, q)) ≅ 𝔽₂^p`: the hat differential
only counts disks whose domains join two generators, so it vanishes on this diagram. The Floer
complex itself is not constructed here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.lensSpace`: the genus-one diagram of `L(p, q)`, with its basepoint
  in a given region.
* `TauCeti.HeegaardRegionSystem.lensSpaceGenerator`: the generator at the intersection point
  `x_a`.
* `TauCeti.HeegaardRegionSystem.lensSpaceCurveHomologyEquiv`: `CurveHomology ≃+ ZMod p`.

## Main results

* `TauCeti.HeegaardRegionSystem.lensSpaceCurveHomologyEquiv_epsilon`: the identification sends
  `ε(x_a, x_b)` to `b - a`.
* `TauCeti.HeegaardRegionSystem.epsilon_lensSpace_eq_zero_iff`: `ε(x, y) = 0` exactly when
  `x = y`, and `TauCeti.HeegaardRegionSystem.exists_isDomainBetween_lensSpace_iff`: a domain joins
  `x` to `y` exactly when `x = y`.
* `TauCeti.HeegaardRegionSystem.epsilon_lensSpace_bijective`: `y ↦ ε(x, y)` is a bijection from
  the generators onto `CurveHomology`.
* `TauCeti.HeegaardRegionSystem.addOrderOf_epsilon_lensSpace`: `ε(x_a, x_{a+1})` has order `p`.
* `TauCeti.HeegaardRegionSystem.periodicDomains_lensSpace` and
  `TauCeti.HeegaardRegionSystem.weaklyAdmissible_lensSpace`: the only periodic domain is zero, so
  the diagram is weakly admissible.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.4 for `ε(x, y)` and periodic
  domains; their §3 uses these genus-one diagrams of lens spaces.
* D. Rolfsen, *Knots and Links*, Chapter 9.B, for the lens space `L(p, q)` as the union of two
  solid tori glued along the slope `p λ + q μ`.
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

variable (p : ℕ) [NeZero p] (q : (ZMod p)ˣ)

/-- The genus-one Heegaard diagram of the lens space `L(p, q)`, with its basepoint in the region
`r`. The point `x_j` and the region `R_j` are both indexed by `j : ZMod p`; the point after `x_j`
is `x_{j+1}` along `α` and `x_{j+q}` along `β`. The `α`-arc starting at `x_j` has `R_j` on its
left and `R_{j-q}` on its right, and the `β`-arc starting at `x_j` has `R_{j-1}` on its left and
`R_j` on its right. -/
def lensSpace (r : ZMod p) : HeegaardRegionSystem 1 (ZMod p) (ZMod p) Unit where
  pointFintype := inferInstance
  alpha _ := 0
  beta _ := 0
  alphaNext := Equiv.addRight 1
  alphaNext_isCycleOn i :=
    Set.eq_univ_of_forall (s := {_j : ZMod p | (0 : Fin 1) = i}) (fun _ => Subsingleton.elim _ _) ▸
      Equiv.isCycleOn_addRight_univ_iff.mpr (ZMod.zmultiples_coe_unit_eq_top 1)
  betaNext := Equiv.addRight (q : ZMod p)
  betaNext_isCycleOn i :=
    Set.eq_univ_of_forall (s := {_j : ZMod p | (0 : Fin 1) = i}) (fun _ => Subsingleton.elim _ _) ▸
      Equiv.isCycleOn_addRight_univ_iff.mpr (ZMod.zmultiples_coe_unit_eq_top q)
  alphaLeft j := j
  alphaRight j := j - q
  betaLeft j := j - 1
  betaRight j := j
  regionNonempty := inferInstance
  crossingCompatible j := Or.inl ⟨by simp [sub_eq_add_neg],
    by simp [sub_eq_add_neg, add_right_comm], rfl, by simp [sub_eq_add_neg]⟩
  regionCovered s := Or.inl ⟨s, Or.inl rfl⟩
  basepoint _ := r

variable {p q} {r : ZMod p}

@[simp]
theorem lensSpace_alphaNext_apply (j : ZMod p) : (lensSpace p q r).alphaNext j = j + 1 :=
  (rfl)

@[simp]
theorem lensSpace_betaNext_apply (j : ZMod p) : (lensSpace p q r).betaNext j = j + q :=
  (rfl)

@[simp]
theorem lensSpace_alphaNext_symm_apply (j : ZMod p) :
    (lensSpace p q r).alphaNext.symm j = j - 1 := by
  simp [lensSpace, sub_eq_add_neg]

@[simp]
theorem lensSpace_betaNext_symm_apply (j : ZMod p) :
    (lensSpace p q r).betaNext.symm j = j - q := by
  simp [lensSpace, sub_eq_add_neg]

@[simp]
theorem lensSpace_basepoint (z : Unit) : (lensSpace p q r).basepoint z = r :=
  (rfl)

@[simp]
theorem lensSpace_alphaLeft (j : ZMod p) : (lensSpace p q r).alphaLeft j = j :=
  (rfl)

@[simp]
theorem lensSpace_alphaRight (j : ZMod p) : (lensSpace p q r).alphaRight j = j - q :=
  (rfl)

@[simp]
theorem lensSpace_betaLeft (j : ZMod p) : (lensSpace p q r).betaLeft j = j - 1 :=
  (rfl)

@[simp]
theorem lensSpace_betaRight (j : ZMod p) : (lensSpace p q r).betaRight j = j :=
  (rfl)

variable (p q r) in
/-- The generator of `lensSpace p q r` at the intersection point `x_a`. -/
def lensSpaceGenerator (a : ZMod p) : (lensSpace p q r).Generator :=
  (lensSpace p q r).generatorOf 1 (fun _ => a) (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)

@[simp]
theorem coe_lensSpaceGenerator_snd (a : ZMod p) (i : Fin 1) :
    ((lensSpaceGenerator p q r a).2 i : ZMod p) = a := by
  simp [lensSpaceGenerator]

/-- Every generator of `lensSpace p q r` is the generator at its intersection point. -/
@[simp]
theorem lensSpaceGenerator_point (x : (lensSpace p q r).Generator) :
    lensSpaceGenerator p q r (x.2 0) = x := by
  refine HeegaardIntersectionSystem.point_injective _ (funext fun i => ?_)
  simp [Subsingleton.elim i 0]

/-- The generators of `lensSpace p q r` are indexed by the intersection points. -/
theorem lensSpaceGenerator_bijective : Function.Bijective (lensSpaceGenerator p q r) :=
  Function.bijective_iff_has_inverse.mpr ⟨fun x => x.2 0,
    fun _ => by simp, lensSpaceGenerator_point⟩

/-- The `0`-chain of the generator at `x_a` is the point `x_a`. -/
@[simp]
theorem generatorChain_lensSpaceGenerator (a : ZMod p) :
    (lensSpace p q r).generatorChain (lensSpaceGenerator p q r a) = Pi.single a 1 := by
  funext j
  simp [HeegaardIntersectionSystem.generatorChain_apply, Pi.single_apply, eq_comm]

/-- Weight each point `x_j` by `j ∈ ZMod p`. The boundary of a `1`-chain `c` on the `β`-arcs
has weighted sum `q` times the total coefficient of `c`, since the arc starting at `x_j` has
boundary `x_{j+q} - x_j`. -/
private theorem sum_betaArcBoundary_mul (c : ZMod p → ℤ) :
    ∑ j, ((lensSpace p q r).betaArcBoundary c j : ZMod p) * j = q * ∑ j, (c j : ZMod p) := by
  have h : ∑ j, (c (j - q) : ZMod p) * j = ∑ j, (c j : ZMod p) * (j + q) :=
    Fintype.sum_equiv (Equiv.subRight (q : ZMod p)) _ _ fun j => by simp
  simp only [betaArcBoundary_apply, lensSpace_betaNext_symm_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib, h]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

variable (p q) in
/-- The total coefficient of the `β`-part of a `1`-chain, multiplied by `-q`, in `ZMod p`. On a
cycle of `α ∪ β` with `β`-part of total coefficient `s`, the cycle winds `s` times in the direction
transverse to `α`; this is its class in `H₁(L(p, q)) = ℤ/p`, normalized so that `ε(x_a, x_b)`
goes to `b - a`. -/
private def betaWinding : (ZMod p → ℤ) × (ZMod p → ℤ) →+ ZMod p :=
  AddMonoidHom.mk' (fun c => -(q * ∑ j, (c.2 j : ZMod p))) fun c d => by
    simp only [Prod.snd_add, Pi.add_apply, Int.cast_add, Finset.sum_add_distrib]
    ring

private theorem betaWinding_apply (c : (ZMod p → ℤ) × (ZMod p → ℤ)) :
    betaWinding p q c = -(q * ∑ j, (c.2 j : ZMod p)) :=
  (rfl)

/-- The winding vanishes on the relations: boundaries of domains and whole curves. -/
private theorem betaWinding_eq_zero_of_mem_arcRelations {c : (ZMod p → ℤ) × (ZMod p → ℤ)}
    (hc : c ∈ (lensSpace p q r).arcRelations) : betaWinding p q c = 0 := by
  obtain ⟨D, hD⟩ := mem_arcRelations_iff.mp hc
  obtain ⟨-, b, hb⟩ := mem_curveCycles_iff_exists.mp hD
  have h : ∀ j, c.2 j = D (j - 1) - D j + b 0 := fun j => by
    have := hb j
    simp only [Prod.snd_sub, Pi.sub_apply, domainBoundary_apply, betaBoundary_apply,
      lensSpace_betaLeft, lensSpace_betaRight,
      Subsingleton.elim ((lensSpace p q r).beta j) 0] at this
    omega
  have hD : ∑ j, (D (j - 1) : ZMod p) = ∑ j, (D j : ZMod p) :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ fun _ => rfl
  simp only [betaWinding_apply, h, Int.cast_add, Int.cast_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hD, sub_self, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, ZMod.natCast_self, zero_mul, zero_add, mul_zero, neg_zero]

variable (p q r) in
/-- The class map `CurveHomology → ZMod p` induced by `betaWinding`. -/
private def windingHom : (lensSpace p q r).CurveHomology →+ ZMod p :=
  CurveHomology.lift _ ((betaWinding p q).comp (lensSpace p q r).arcCycles.subtype)
    fun _ hc => betaWinding_eq_zero_of_mem_arcRelations hc

private theorem windingHom_mk (c : (lensSpace p q r).arcCycles) :
    windingHom p q r (CurveHomology.mk _ c) = -(q * ∑ j, ((c : (ZMod p → ℤ) × (ZMod p → ℤ)).2 j :
      ZMod p)) := by
  simp [windingHom, betaWinding_apply]

private theorem windingHom_epsilon (a b : ZMod p) :
    windingHom p q r ((lensSpace p q r).epsilon (lensSpaceGenerator p q r a)
      (lensSpaceGenerator p q r b)) = b - a := by
  obtain ⟨c, hc⟩ := (lensSpace p q r).exists_isConnectingChain (lensSpaceGenerator p q r a)
    (lensSpaceGenerator p q r b)
  have h := sum_betaArcBoundary_mul (q := q) (r := r) c.2
  rw [(isConnectingChain_iff.mp hc).2, generatorChain_lensSpaceGenerator,
    generatorChain_lensSpaceGenerator] at h
  simp only [Pi.sub_apply, Pi.single_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib,
    Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  rw [hc.epsilon_eq, windingHom_mk, ← h]
  ring

/-- A cycle of `α ∪ β` of winding zero is a relation. Its `β`-part `c₂` has total coefficient
`p m`, so `j ↦ c₂ j - m` is the `β`-boundary of a domain `D`; then `c - ∂D` has constant
`β`-part `m`, and its `α`-part is a cycle, so `c - ∂D` is a combination of whole curves. -/
private theorem mem_arcRelations_of_betaWinding_eq_zero {c : (ZMod p → ℤ) × (ZMod p → ℤ)}
    (hc : c ∈ (lensSpace p q r).arcCycles) (h0 : betaWinding p q c = 0) :
    c ∈ (lensSpace p q r).arcRelations := by
  rw [betaWinding_apply, neg_eq_zero, Units.mul_right_eq_zero, ← Int.cast_sum,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  obtain ⟨m, hm⟩ := h0
  obtain ⟨D, hD⟩ := Equiv.Perm.exists_comp_symm_sub_eq_sum (σ := Equiv.addRight (1 : ZMod p))
    (u := fun _ => 0) (v := id)
    (fun i => (Equiv.isCycleOn_addRight_univ_iff.mpr (ZMod.zmultiples_coe_unit_eq_top 1)).2
      (Set.mem_univ _) (Set.mem_univ _))
    (fun j => c.2 j - m)
  have hβD : ∀ j, (lensSpace p q r).betaBoundary D j = c.2 j - m := fun j => by
    have := congrFun hD j
    rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_apply] at this
    simp only [Pi.single_apply, id, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_sub_distrib, hm, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, sub_self, ite_self, sub_zero, Equiv.addRight_symm,
      Equiv.coe_addRight, ← sub_eq_add_neg] at this
    rw [betaBoundary_apply, lensSpace_betaLeft, lensSpace_betaRight, this]
  have hβ : (lensSpace p q r).betaArcBoundary (c - (lensSpace p q r).domainBoundary D).2 = 0 :=
    ((lensSpace p q r).betaArcBoundary_eq_zero_iff _).mpr
      ⟨fun _ => m, fun j => by simp [hβD]⟩
  refine mem_arcRelations_iff.mpr ⟨D, mem_curveCycles_iff.mpr ⟨?_, hβ⟩⟩
  have hcyc := mem_arcCycles_iff.mp hc
  have hbd := (lensSpace p q r).boundary_boundary_eq_zero D
  simp only [Prod.fst_sub, Prod.snd_sub, domainBoundary_apply, map_sub] at hβ ⊢
  linear_combination hcyc - hbd - hβ

variable (p q r) in
/-- The group `CurveHomology` of the lens space diagram is `H₁(L(p, q)) = ℤ/p`: the class of a
cycle of `α ∪ β` whose `β`-part has total coefficient `s` goes to `-q s`. Under this
identification `ε(x_a, x_b) = b - a` (`lensSpaceCurveHomologyEquiv_epsilon`). -/
noncomputable def lensSpaceCurveHomologyEquiv : (lensSpace p q r).CurveHomology ≃+ ZMod p :=
  AddEquiv.ofBijective (windingHom p q r)
    ⟨(injective_iff_map_eq_zero _).mpr fun x hx => by
      obtain ⟨c, rfl⟩ := CurveHomology.mk_surjective _ x
      exact (CurveHomology.mk_eq_zero_iff _).mpr
        (mem_arcRelations_of_betaWinding_eq_zero c.2
          (by rwa [windingHom_mk, ← betaWinding_apply] at hx)),
    fun a => ⟨_, (windingHom_epsilon 0 a).trans (sub_zero a)⟩⟩

/-- The class of a cycle `c` of `α ∪ β` is `-q` times the total coefficient of its `β`-part. -/
theorem lensSpaceCurveHomologyEquiv_mk (c : (lensSpace p q r).arcCycles) :
    lensSpaceCurveHomologyEquiv p q r (CurveHomology.mk _ c) =
      -(q * ∑ j, ((c : (ZMod p → ℤ) × (ZMod p → ℤ)).2 j : ZMod p)) :=
  windingHom_mk c

/-- The class `ε(x, y)` of two generators is the difference of their intersection points. -/
theorem lensSpaceCurveHomologyEquiv_epsilon (x y : (lensSpace p q r).Generator) :
    lensSpaceCurveHomologyEquiv p q r ((lensSpace p q r).epsilon x y) =
      (lensSpace p q r).point y 0 - (lensSpace p q r).point x 0 := by
  obtain ⟨a, rfl⟩ := lensSpaceGenerator_bijective.2 x
  obtain ⟨b, rfl⟩ := lensSpaceGenerator_bijective.2 y
  simp only [HeegaardIntersectionSystem.point_apply, coe_lensSpaceGenerator_snd]
  exact windingHom_epsilon a b

/-- In the lens space diagram `ε(x, y)` vanishes only when `x = y`: distinct generators lie in
distinct spin^c structures. -/
theorem epsilon_lensSpace_eq_zero_iff {x y : (lensSpace p q r).Generator} :
    (lensSpace p q r).epsilon x y = 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ epsilon_self x⟩
  have := lensSpaceCurveHomologyEquiv_epsilon x y
  rw [h, map_zero, eq_comm, sub_eq_zero, HeegaardIntersectionSystem.point_apply,
    HeegaardIntersectionSystem.point_apply] at this
  rw [← lensSpaceGenerator_point x, ← lensSpaceGenerator_point y, this]

/-- In the lens space diagram a domain joins `x` to `y` only when `x = y`. -/
theorem exists_isDomainBetween_lensSpace_iff {x y : (lensSpace p q r).Generator} :
    (∃ D, (lensSpace p q r).IsDomainBetween x y D) ↔ x = y :=
  epsilon_eq_zero_iff.symm.trans epsilon_lensSpace_eq_zero_iff

/-- The generators of the lens space diagram are in bijection with `CurveHomology`, and so with
the spin^c structures of `L(p, q)`, through `y ↦ ε(x, y)`. -/
theorem epsilon_lensSpace_bijective (x : (lensSpace p q r).Generator) :
    Function.Bijective ((lensSpace p q r).epsilon x) := by
  refine ⟨fun y y' h => ?_, fun c => ?_⟩
  · rw [← epsilon_lensSpace_eq_zero_iff, ← epsilon_add_epsilon y x y', ← neg_epsilon, h,
      neg_add_cancel]
  · refine ⟨lensSpaceGenerator p q r (lensSpaceCurveHomologyEquiv p q r c +
      (lensSpace p q r).point x 0), (lensSpaceCurveHomologyEquiv p q r).injective ?_⟩
    simp [lensSpaceCurveHomologyEquiv_epsilon]

/-- The class `ε(x_a, x_{a+1})` of two consecutive generators has order `p`, as a generator of
`H₁(L(p, q)) = ℤ/p` should. -/
theorem addOrderOf_epsilon_lensSpace (a : ZMod p) :
    addOrderOf ((lensSpace p q r).epsilon (lensSpaceGenerator p q r a)
      (lensSpaceGenerator p q r (a + 1))) = p := by
  rw [← AddEquiv.addOrderOf_eq (lensSpaceCurveHomologyEquiv p q r),
    lensSpaceCurveHomologyEquiv_epsilon]
  simp [ZMod.addOrderOf_one]

/-- The lens space diagram has no nonzero periodic domain: a domain whose boundary is a
combination of whole `α`- and `β`-curves and whose multiplicity at the basepoint region `R_r` is
zero must vanish. Hence the diagram is weakly admissible (`weaklyAdmissible_lensSpace`) for every
basepoint, and for each pair of generators there is at most one domain joining them. -/
@[simp]
theorem periodicDomains_lensSpace : (lensSpace p q r).periodicDomains = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun P hP => ?_
  obtain ⟨hz, -, hβ⟩ := mem_periodicDomains_iff.mp hP
  obtain ⟨b, hb⟩ := ((lensSpace p q r).betaArcBoundary_eq_zero_iff _).mp hβ
  have hb' : ∀ j, P (j - 1) - P j = b 0 := fun j => by
    have := hb j
    rwa [betaBoundary_apply, lensSpace_betaLeft, lensSpace_betaRight,
      Subsingleton.elim ((lensSpace p q r).beta j) 0] at this
  have hb0 : b 0 = 0 := by
    have hsum : ∑ j, (P (j - 1) - P j) = 0 := by
      rw [Finset.sum_sub_distrib, sub_eq_zero]
      exact Fintype.sum_equiv (Equiv.subRight 1) _ _ fun _ => rfl
    simp only [hb', Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left (Int.natCast_ne_zero.mpr (NeZero.ne p))
  funext j
  have hconst : P j = P r := Equiv.Perm.SameCycle.apply_eq_of_apply_eq
    ((Equiv.isCycleOn_addRight_univ_iff.mpr (ZMod.zmultiples_coe_unit_eq_top 1)).2
      (Set.mem_univ j) (Set.mem_univ r)) fun z => by
      have := hb' (z + 1)
      rw [hb0, add_sub_cancel_right, sub_eq_zero] at this
      simpa using this.symm
  simpa [hconst] using hz ()

/-- The lens space diagram is weakly admissible. -/
theorem weaklyAdmissible_lensSpace : (lensSpace p q r).WeaklyAdmissible :=
  weaklyAdmissible_iff.mpr fun P hP _ => by simpa using hP

end HeegaardRegionSystem

end TauCeti
